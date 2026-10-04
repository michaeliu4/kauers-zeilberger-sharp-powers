import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.IntermediateValue

/-!
# Propagation of nonnegative analytic coefficients

A real analytic function with nonnegative derivatives at the left endpoint
has nonnegative derivatives throughout an interval where it remains analytic.
The proof preserves a common convergence radius for all derivative orders,
then applies continuous induction to the closed set of nonnegative jets.
-/

namespace Results.SharpPowersKz.AnalyticPropagation

open Set Filter
open scoped Topology

private theorem iteratedDeriv_comp_order (f : ℝ → ℝ) (k n : ℕ) :
    iteratedDeriv k (iteratedDeriv n f) = iteratedDeriv (k + n) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- Every derivative has an analytic expansion on the original ball, with the
same radius. This uniformity in the order is essential for continuation. -/
private theorem exists_series_iteratedDeriv
    {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ} {a : ℝ} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p a r) (n : ℕ) :
    ∃ q : FormalMultilinearSeries ℝ ℝ ℝ,
      HasFPowerSeriesOnBall (iteratedDeriv n f) q a r := by
  induction n with
  | zero => exact ⟨p, by simpa only [iteratedDeriv_zero] using hp⟩
  | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨(ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
        q.derivSeries, ?_⟩
      rw [iteratedDeriv_succ]
      exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp_hasFPowerSeriesOnBall hq.fderiv

/-- A nonnegative jet stays nonnegative to the right throughout the common
analytic ball. The proof uses the Taylor expansion of each derivative. -/
private theorem nonnegative_jet_add
    {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ} {a d : ℝ} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p a r)
    (hjet : ∀ n : ℕ, 0 ≤ iteratedDeriv n f a)
    (hd : 0 ≤ d) (hdr : d ∈ Metric.eball (0 : ℝ) r) :
    ∀ n : ℕ, 0 ≤ iteratedDeriv n f (a + d) := by
  intro n
  obtain ⟨q, hq⟩ := exists_series_iteratedDeriv hp n
  apply (hq.hasSum_iteratedFDeriv hdr).nonneg
  intro k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply mul_nonneg (pow_nonneg hd k)
  rw [iteratedDeriv_comp_order]
  exact hjet (k + n)

/-- Local right stability of the set of points with nonnegative full jet. -/
private theorem nonnegative_jet_mem_nhdsGT {f : ℝ → ℝ} {a : ℝ}
    (ha : AnalyticAt ℝ f a) (hjet : ∀ n : ℕ, 0 ≤ iteratedDeriv n f a) :
    {y : ℝ | ∀ n : ℕ, 0 ≤ iteratedDeriv n f y} ∈ 𝓝[>] a := by
  obtain ⟨p, r, hp⟩ := ha
  have hsub : ContinuousAt (fun y : ℝ => y - a) a :=
    continuousAt_id.sub continuousAt_const
  have hball : {y : ℝ | y - a ∈ Metric.eball (0 : ℝ) r} ∈ 𝓝 a :=
    hsub.preimage_mem_nhds (by simpa only [sub_self] using Metric.eball_mem_nhds 0 hp.r_pos)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hball,
    (self_mem_nhdsWithin : Ioi a ∈ 𝓝[>] a)] with y hyr hy
  have hyjet := nonnegative_jet_add hp hjet (sub_nonneg.mpr (le_of_lt hy)) hyr
  rw [add_comm a (y - a), sub_add_cancel] at hyjet
  exact hyjet

/-- If a real function is analytic at every point of a closed interval, and
all its derivatives at the left endpoint are nonnegative, then all derivatives
are nonnegative throughout that interval. There is no hypothesis about the
paper's particular polynomial or about nonnegative derivatives away from the
initial endpoint. -/
theorem nonnegative_jet_on_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hana : ∀ x ∈ Icc a b, AnalyticAt ℝ f x)
    (hjet : ∀ n : ℕ, 0 ≤ iteratedDeriv n f a) :
    ∀ x ∈ Icc a b, ∀ n : ℕ, 0 ≤ iteratedDeriv n f x := by
  let s : Set ℝ := {x | ∀ n : ℕ, 0 ≤ iteratedDeriv n f x}
  have hs : IsClosed (s ∩ Icc a b) := by
    have heq : s ∩ Icc a b =
        ⋂ n : ℕ, Icc a b ∩ (iteratedDeriv n f) ⁻¹' Ici (0 : ℝ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro hx n
        exact ⟨hx.2, hx.1 n⟩
      · intro hx
        exact ⟨fun n => (hx n).2, (hx 0).1⟩
    rw [heq]
    apply isClosed_iInter
    intro n
    apply ContinuousOn.preimage_isClosed_of_isClosed _ isClosed_Icc isClosed_Ici
    intro x hx
    have hn := (hana x hx).iterated_deriv n
    rw [← iteratedDeriv_eq_iterate] at hn
    exact hn.continuousAt.continuousWithinAt
  apply hs.Icc_subset_of_forall_mem_nhdsWithin hjet
  intro x hx
  exact nonnegative_jet_mem_nhdsGT (hana x ⟨hx.2.1, le_of_lt hx.2.2⟩) hx.1

/-- Positivity of the actual coefficients of an analytic expansion gives
positivity of the derivative jet at its center. -/
theorem nonnegative_jet_of_series {f : ℝ → ℝ}
    {p : FormalMultilinearSeries ℝ ℝ ℝ} {a : ℝ}
    (hp : HasFPowerSeriesAt f p a)
    (hcoeff : ∀ n : ℕ, 0 ≤ p n (fun _ => 1)) :
    ∀ n : ℕ, 0 ≤ iteratedDeriv n f a := by
  obtain ⟨r, hr⟩ := hp
  intro n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hr.factorial_smul (1 : ℝ) n]
  exact nsmul_nonneg (hcoeff n) _

/-- A negative derivative later on a real analytic interval forces a negative
coefficient in every analytic expansion at the left endpoint. -/
theorem exists_negative_coefficient_of_deriv_neg {f : ℝ → ℝ}
    {p : FormalMultilinearSeries ℝ ℝ ℝ} {a b : ℝ}
    (hab : a ≤ b) (hana : ∀ x ∈ Icc a b, AnalyticAt ℝ f x)
    (hp : HasFPowerSeriesAt f p a) (hneg : deriv f b < 0) :
    ∃ n : ℕ, p n (fun _ => 1) < 0 := by
  by_contra h
  have hcoeff : ∀ n : ℕ, 0 ≤ p n (fun _ => 1) := by
    intro n
    by_contra hn
    exact h ⟨n, lt_of_not_ge hn⟩
  have hb := nonnegative_jet_on_Icc hana (nonnegative_jet_of_series hp hcoeff)
    b ⟨hab, le_rfl⟩ 1
  rw [iteratedDeriv_one] at hb
  exact (not_le_of_gt hneg) hb

end Results.SharpPowersKz.AnalyticPropagation
