import Results.SharpPowersKz.Solution.CoefficientJets
import Results.SharpPowersKz.ScottSokalDefs
import Results.SharpPowersKz.Solution.AnalyticPropagation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
Coordinate words agree with the corresponding Frechet jets for analytic
functions. Nonnegative word jets at the origin propagate through a positive
rectangle by successive one-coordinate restrictions. These generic lemmas
use the actual derivative definitions from ScottSokalDefs.
-/

noncomputable section
namespace Results.SharpPowersKz.CoefficientJets

open NumeratorCalculus
open scoped Topology

abbrev Point := Fin 4 → ℝ

def wordDirections : (w : List (Fin 4)) → Fin w.length → Point
  | [] => Fin.elim0
  | i :: w => Fin.cons (Pi.single i 1) (wordDirections w)

theorem coordinateDeriv_eq_fderiv (i : Fin 4) (f : Point → ℝ) (x : Point)
    (hf : DifferentiableAt ℝ f x) :
    coordinateDeriv i f x = fderiv ℝ f x (Pi.single i 1) := by
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x i)
    (hasDerivAt_update x i (x i)) (by simp)
  exact h.deriv

theorem wordDeriv_eq_iteratedFDeriv (w : List (Fin 4)) (f : Point → ℝ)
    (x : Point) (hf : AnalyticAt ℝ f x) :
    wordDeriv w f x = iteratedFDeriv ℝ w.length f x (wordDirections w) := by
  induction w generalizing x with
  | nil => simp [wordDirections, wordDeriv]
  | cons i w ih =>
    have heq : wordDeriv w f =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ w.length f y (wordDirections w)) :=
      hf.eventually_analyticAt.mono fun y hy => ih y hy
    have hpath := (hasDerivAt_update x i (x i)).continuousAt
    have heqpath := heq.comp_tendsto (by simpa using hpath.tendsto)
    simp only [Function.comp_def] at heqpath
    have hfd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) x :=
      (hf.contDiffAt : ContDiffAt ℝ ⊤ f x).differentiableAt_iteratedFDeriv (by simp)
    rw [wordDeriv, coordinateDeriv, heqpath.deriv_eq]
    change coordinateDeriv i
      (fun y => iteratedFDeriv ℝ w.length f y (wordDirections w)) x = _
    rw [coordinateDeriv_eq_fderiv _ _ _ (hfd.continuousMultilinear_apply_const _)]
    simpa [wordDirections] using
      (hfd.iteratedFDeriv_succ_apply_left' (m := wordDirections (i :: w))).symm

theorem iteratedDeriv_coordinate_restriction (n : ℕ) (w : List (Fin 4))
    (f : Point → ℝ) (x : Point) (i : Fin 4) (t : ℝ) :
    iteratedDeriv n (fun u => wordDeriv w f (Function.update x i u)) t =
      wordDeriv (List.replicate n i ++ w) f (Function.update x i t) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun u => wordDeriv w f (Function.update x i u)) =
        (fun u => wordDeriv (List.replicate n i ++ w) f (Function.update x i u)) :=
      funext ih
    rw [heq]
    simp [List.replicate_succ, wordDeriv, coordinateDeriv, Function.update_idem]

theorem analyticAt_update (x : Point) (i : Fin 4) (t : ℝ) :
    AnalyticAt ℝ (Function.update x i) t := by
  apply AnalyticAt.pi
  intro j
  by_cases hji : j = i
  · subst j
    have heq : (fun u : ℝ => Function.update x i u i) = id := by funext u; simp
    rw [heq]
    exact analyticAt_id
  · simpa [Function.update_of_ne hji] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => x j) t)

theorem wordDeriv_nonneg_coordinate (f : Point → ℝ) (x : Point) (i : Fin 4)
    (b : ℝ) (hb : x i ≤ b)
    (hana : ∀ w t, t ∈ Set.Icc (x i) b →
      AnalyticAt ℝ (wordDeriv w f) (Function.update x i t))
    (hjet : ∀ w, 0 ≤ wordDeriv w f x) :
    ∀ w, 0 ≤ wordDeriv w f (Function.update x i b) := by
  intro w
  let g : ℝ → ℝ := fun t => wordDeriv w f (Function.update x i t)
  have hga (t : ℝ) (ht : t ∈ Set.Icc (x i) b) : AnalyticAt ℝ g t :=
    (hana w t ht).comp (analyticAt_update x i t)
  have hgj (n : ℕ) : 0 ≤ iteratedDeriv n g (x i) := by
    rw [show g = (fun t => wordDeriv w f (Function.update x i t)) from rfl,
      iteratedDeriv_coordinate_restriction]
    simpa using hjet (List.replicate n i ++ w)
  have h := AnalyticPropagation.nonnegative_jet_on_Icc hga hgj b ⟨hb, le_rfl⟩ 0
  simpa [g] using h

/-- Coordinate-by-coordinate analytic propagation requires no interchange of
mixed derivatives and no expansion of a directional derivative. -/
theorem wordDeriv_nonneg_box (f : Point → ℝ) (y : Point)
    (hy : ∀ i, 0 ≤ y i)
    (hana : ∀ w x, (∀ i, x i ∈ Set.Icc 0 (y i)) → AnalyticAt ℝ (wordDeriv w f) x)
    (hjet : ∀ w, 0 ≤ wordDeriv w f 0) : ∀ w, 0 ≤ wordDeriv w f y := by
  classical
  let point (s : Finset (Fin 4)) : Point := fun j => if j ∈ s then y j else 0
  have hpoint (s : Finset (Fin 4)) (j : Fin 4) : point s j ∈ Set.Icc 0 (y j) := by
    simp only [point]
    split_ifs
    · exact ⟨hy j, le_rfl⟩
    · exact ⟨le_rfl, hy j⟩
  have hs (s : Finset (Fin 4)) : ∀ w, 0 ≤ wordDeriv w f (point s) := by
    induction s using Finset.induction_on with
    | empty =>
      have hp0 : point ∅ = 0 := by funext j; simp [point]
      rw [hp0]
      exact hjet
    | @insert i s hi ih =>
      have hzero : point s i = 0 := by simp [point, hi]
      have heq : point (insert i s) = Function.update (point s) i (y i) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [point]
        · simp [point, hji]
      rw [heq]
      apply wordDeriv_nonneg_coordinate f (point s) i (y i)
        (by simpa only [hzero] using hy i) _ ih
      intro w t ht
      apply hana w _
      intro j
      by_cases hji : j = i
      · subst j; simpa [hzero] using ht
      · simpa [Function.update_of_ne hji] using hpoint s j
  simpa [point] using hs Finset.univ

end Results.SharpPowersKz.CoefficientJets
