import Results.SharpPowersKz.Solution.CoordinateJets
import Results.SharpPowersKz.Solution.NumeratorAnalytic
import Results.SharpPowersKz.Solution.AnalyticCoefficients
import Results.SharpPowersKz.Solution.BinomialGerm

noncomputable section
namespace Results.SharpPowersKz.CoefficientJets
open MvPolynomial NumeratorCalculus

theorem wordDeriv_eval (w : List (Fin 4)) (p : MvPolynomial (Fin 4) ℝ) :
    wordDeriv w (fun x => p.eval x) = fun x => (wordPDeriv w p).eval x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    rw [wordDeriv_cons, ih]
    exact (hasDerivAt_evalAlong (wordPDeriv w p) x i).deriv

theorem binomialTruncation_word_deriv_zero (β : ℝ) (w : List (Fin 4)) :
    wordDeriv w (fun x => (binomialTruncation β w.length).eval x) 0 =
      (wordFactor w 0 : ℝ) * powerCoeff 4 β (wordIndex w) := by
  rw [wordDeriv_eval]
  change (MvPolynomial.eval 0) (wordPDeriv w (binomialTruncation β w.length)) = _
  rw [MvPolynomial.eval_zero]
  change (wordPDeriv w (binomialTruncation β w.length)).coeff 0 = _
  exact binomialTruncation_word_coeff_zero β w

theorem truncatedPolynomial_eval (β : ℝ) (N : ℕ) (x : Point) :
    (AnalyticCoefficients.truncatedPolynomial (binomialWeight β) N).eval
      ((perturbation (4 : ℝ)).eval x) = (binomialTruncation β N).eval x := by
  simp [AnalyticCoefficients.truncatedPolynomial, binomialTruncation,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow]

/-- The actual analytic coordinate jet is the finite formal binomial coefficient,
with its positive multiplicity factor. No coefficient-jet premise is used. -/
theorem wordDeriv_inverse_zero (β : ℝ) (w : List (Fin 4)) :
    wordDeriv w (fun x => denominator.eval x ^ (-β)) 0 =
      (wordFactor w 0 : ℝ) * powerCoeff 4 β (wordIndex w) := by
  have hp := BinomialGerm.hasFPowerSeriesAt_inverse_one_sub β
  have hq := analyticAt_eval (perturbation (4 : ℝ)) (0 : Point)
  have hq0 : (perturbation (4 : ℝ)).eval (0 : Point) = 0 := by simp [perturbation]
  have hjets := AnalyticCoefficients.iteratedFDeriv_comp_eq_outer_truncation hp hq hq0 w.length
  have hleft : (fun x : Point => (1 - (perturbation (4 : ℝ)).eval x) ^ (-β)) =
      (fun x : Point => denominator.eval x ^ (-β)) := by
    funext x
    simp [denominator]
  have hright :
      (fun x : Point => (AnalyticCoefficients.truncatedPolynomial (binomialWeight β)
        w.length).eval ((perturbation (4 : ℝ)).eval x)) =
      (fun x : Point => (binomialTruncation β w.length).eval x) :=
    funext (truncatedPolynomial_eval β w.length)
  rw [hleft, hright] at hjets
  have hf := analyticAt_eval_neg_rpow denominator β (0 : Point)
    (by rw [denominator_eval_zero]; norm_num)
  have ht := analyticAt_eval (binomialTruncation β w.length) (0 : Point)
  calc
    _ = iteratedFDeriv ℝ w.length (fun x => denominator.eval x ^ (-β)) 0
        (wordDirections w) := wordDeriv_eq_iteratedFDeriv w _ _ hf
    _ = iteratedFDeriv ℝ w.length (fun x => (binomialTruncation β w.length).eval x) 0
        (wordDirections w) := congrArg (fun D => D (wordDirections w)) hjets
    _ = wordDeriv w (fun x => (binomialTruncation β w.length).eval x) 0 :=
      (wordDeriv_eq_iteratedFDeriv w _ _ ht).symm
    _ = _ := binomialTruncation_word_deriv_zero β w

/-- Actual formal coefficient positivity propagates to every derivative
numerator throughout the positive cube. -/
theorem numerator_nonnegative_cube (β : ℝ) (hβ : NonnegativePower 4 β)
    (w : List (Fin 4)) (y : Point) (hy : ∀ i, 0 < y i ∧ y i < Algebra.rho) :
    0 ≤ (DerivativeNumerator.numerator β (1 - perturbation 4) w).eval y := by
  have hjet (v : List (Fin 4)) :
      0 ≤ wordDeriv v (fun x => denominator.eval x ^ (-β)) 0 := by
    rw [wordDeriv_inverse_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (hβ _)
  have hQ (x : Point) (hx : ∀ i, x i ∈ Set.Icc 0 (y i)) :
      0 < denominator.eval x := denominator_pos_cube x fun i =>
    ⟨(hx i).1, lt_of_le_of_lt (hx i).2 (hy i).2⟩
  have hwords := wordDeriv_nonneg_box (fun x => denominator.eval x ^ (-β)) y
    (fun i => (hy i).1.le)
    (fun v x hx => analyticAt_wordDeriv_neg_rpow β denominator v x (hQ x hx)) hjet
  have hQy : 0 < denominator.eval y := denominator_pos_cube y fun i =>
    ⟨(hy i).1.le, (hy i).2⟩
  have h := hwords w
  rw [wordDeriv_neg_rpow β denominator w y hQy] at h
  change 0 ≤ (DerivativeNumerator.numerator β denominator w).eval y
  exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hQy _)).mp h

end Results.SharpPowersKz.CoefficientJets
