import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Analytic jets agree with finite formal substitution

The outer series can be truncated at degree n because every composition of
n has at most n blocks; the resulting composition is a finite polynomial.
-/

namespace Results.SharpPowersKz.AnalyticCoefficients

private theorem polynomial_analytic (Q : Polynomial ℝ) (x : ℝ) :
    AnalyticAt ℝ (fun t => Q.eval t) x := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.fun_add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial, Pi.pow_apply, id_eq] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => a) x).fun_mul
          ((analyticAt_id : AnalyticAt ℝ (fun t : ℝ => t) x).pow n)

private theorem iteratedDeriv_polynomial (Q : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => Q.eval t) =
      fun t => (Polynomial.derivative^[n] Q).eval t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext t
      simp only [Polynomial.deriv, Function.iterate_succ_apply']

private theorem iteratedDeriv_polynomial_zero (Q : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => Q.eval t) 0 =
      (n.factorial : ℝ) * Q.coeff n := by
  rw [iteratedDeriv_polynomial]
  change (Polynomial.derivative^[n] Q).eval 0 = (n.factorial : ℝ) * Q.coeff n
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self, nsmul_eq_mul]

private theorem series_derivative_at_zero
    {g : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt g p 0) (k : ℕ) :
    iteratedDeriv k g 0 = (k.factorial : ℝ) * p.coeff k := by
  obtain ⟨r, hr⟩ := hp
  have hone : (1 : Fin k → ℝ) = (fun _ => 1) := by ext i; rfl
  rw [FormalMultilinearSeries.coeff, hone]
  simpa only [nsmul_eq_mul,
    iteratedDeriv_eq_iteratedFDeriv] using (hr.factorial_smul (1 : ℝ) k).symm

private theorem polynomial_series_coeff
    {Q : Polynomial ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt (fun t => Q.eval t) p 0) (k : ℕ) :
    p.coeff k = Q.coeff k := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k) :
    (k.factorial : ℝ) ≠ 0)
  rw [← series_derivative_at_zero hp k, iteratedDeriv_polynomial_zero]

/-- The finite polynomial with the first n+1 scalar series coefficients. -/
noncomputable def truncatedPolynomial (a : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (a k) * Polynomial.X ^ k

private theorem truncatedPolynomial_coeff {a : ℕ → ℝ} {n k : ℕ} (hk : k ≤ n) :
    (truncatedPolynomial a n).coeff k = a k := by
  simp [truncatedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Nat.lt_succ_of_le hk]

/-- Composing an analytic scalar germ with any analytic scalar-valued inner
function preserves its nth Fréchet derivative when the outer series is
truncated after degree n. The inner function must vanish at the base point.
The inner space may be multidimensional. -/
theorem iteratedFDeriv_comp_eq_outer_truncation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℝ a) 0)
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (hfx : f x = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => g (f y)) x =
      iteratedFDeriv ℝ n (fun y => (truncatedPolynomial a n).eval (f y)) x := by
  classical
  obtain ⟨p, hpf⟩ := hf
  obtain ⟨q, hq⟩ := polynomial_analytic (truncatedPolynomial a n) 0
  have hgx : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℝ a)
      (f x) := by simpa only [hfx] using hp
  have hqx : HasFPowerSeriesAt (fun u => (truncatedPolynomial a n).eval u) q (f x) := by
    simpa only [hfx] using hq
  have houter : ∀ k ≤ n, (FormalMultilinearSeries.ofScalars ℝ a) k = q k := by
    intro k hk
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars]
    rw [polynomial_series_coeff hq k, truncatedPolynomial_coeff hk]
  have hcomp : ((FormalMultilinearSeries.ofScalars ℝ a).comp p) n =
      (q.comp p) n := by
    simp only [FormalMultilinearSeries.comp]
    apply Finset.sum_congr rfl
    intro c hc
    unfold FormalMultilinearSeries.compAlongComposition
    rw [houter c.length c.length_le]
  obtain ⟨rg, hgball⟩ := hgx.comp hpf
  obtain ⟨rq, hqball⟩ := hqx.comp hpf
  apply ContinuousMultilinearMap.ext
  intro v
  change iteratedFDeriv ℝ n (g ∘ f) x v =
    iteratedFDeriv ℝ n ((fun u => (truncatedPolynomial a n).eval u) ∘ f) x v
  rw [hgball.iteratedFDeriv_eq_sum_of_completeSpace v,
    hqball.iteratedFDeriv_eq_sum_of_completeSpace v]
  simp only [hcomp]

/-- The actual Taylor jet of an analytic scalar series composed with a
polynomial of zero constant term is its finite formal substitution. -/
theorem iteratedDeriv_comp_polynomial_zero
    {g : ℝ → ℝ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℝ a) 0)
    (T : Polynomial ℝ) (hT : T.eval 0 = 0) (n : ℕ) :
    iteratedDeriv n (fun t => g (T.eval t)) 0 =
      (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1), a k * (T ^ k).coeff n := by
  have hjets := iteratedFDeriv_comp_eq_outer_truncation hp (polynomial_analytic T 0) hT n
  have hjets' := congrArg (fun D => D (fun _ => (1 : ℝ))) hjets
  change iteratedDeriv n (fun t => g (T.eval t)) 0 =
    iteratedDeriv n (fun t => (truncatedPolynomial a n).eval (T.eval t)) 0 at hjets'
  calc
    iteratedDeriv n (fun t => g (T.eval t)) 0 =
        iteratedDeriv n (fun t => ((truncatedPolynomial a n).comp T).eval t) 0 := by
      simpa only [Polynomial.eval_comp] using hjets'
    _ = (n.factorial : ℝ) * ((truncatedPolynomial a n).comp T).coeff n :=
      iteratedDeriv_polynomial_zero ((truncatedPolynomial a n).comp T) n
    _ = (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1), a k * (T ^ k).coeff n := by
      simp [truncatedPolynomial, Polynomial.finsetSum_coeff]

end Results.SharpPowersKz.AnalyticCoefficients
