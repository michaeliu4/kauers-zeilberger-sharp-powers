import Results.SharpPowersKz.Solution.Truncation
import Results.SharpPowersKz.Solution.Basic
import Results.SharpPowersKz.Solution.Geometry
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Finite polynomial jets of the actual binomial coefficient definition.
The analytic conversion and propagation are proved in CoordinateJets and
CubeJetBridge. -/

noncomputable section

namespace Results.SharpPowersKz.CoefficientJets

open MvPolynomial

def denominator : MvPolynomial (Fin 4) ℝ := 1 - perturbation 4

theorem denominator_eval (x : Fin 4 → ℝ) :
    denominator.eval x = Algebra.pκ 4 (x 0) (x 1) (x 2) (x 3) := by
  simp [denominator, perturbation, Algebra.pκ]
  ring

theorem denominator_eval_zero : denominator.eval 0 = 1 := by
  simp [denominator, perturbation]

theorem denominator_pos_cube (x : Fin 4 → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < Algebra.rho) : 0 < denominator.eval x := by
  rw [denominator_eval]
  exact Algebra.pFour_pos_on_cube (hx 0).1 (hx 1).1 (hx 2).1 (hx 3).1
    (hx 0).2 (hx 1).2 (hx 2).2 (hx 3).2

def wordIndex : List (Fin 4) → MultiIndex
  | [] => 0
  | i :: w => Finsupp.single i 1 + wordIndex w

def wordFactor : List (Fin 4) → MultiIndex → ℕ
  | [], _ => 1
  | i :: w, d => (d i + 1) * wordFactor w (d + Finsupp.single i 1)

def wordPDeriv : List (Fin 4) → MvPolynomial (Fin 4) ℝ → MvPolynomial (Fin 4) ℝ
  | [], p => p
  | i :: w, p => pderiv i (wordPDeriv w p)

theorem wordIndex_degree (w : List (Fin 4)) : degree (wordIndex w) = w.length := by
  induction w with
  | nil => simp [wordIndex]
  | cons i w ih => simp [wordIndex, degree_add, ih, Nat.add_comm]

theorem wordFactor_pos (w : List (Fin 4)) (d : MultiIndex) : 0 < wordFactor w d := by
  induction w generalizing d with
  | nil => simp [wordFactor]
  | cons i w ih => exact Nat.mul_pos (Nat.zero_lt_succ _) (ih _)

theorem coeff_wordPDeriv (w : List (Fin 4)) (p : MvPolynomial (Fin 4) ℝ)
    (d : MultiIndex) :
    (wordPDeriv w p).coeff d = (wordFactor w d : ℝ) * p.coeff (d + wordIndex w) := by
  induction w generalizing d with
  | nil => simp [wordPDeriv, wordFactor, wordIndex]
  | cons i w ih =>
    rw [wordPDeriv, coeff_pderiv, ih]
    simp only [wordFactor, wordIndex, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_assoc]
    ring

def binomialTruncation (β : ℝ) (N : ℕ) : MvPolynomial (Fin 4) ℝ :=
  ∑ k ∈ Finset.range (N + 1), C (binomialWeight β k) * perturbation 4 ^ k

theorem binomialTruncation_coeff (β : ℝ) (N : ℕ) (d : MultiIndex)
    (hd : degree d ≤ N) :
    (binomialTruncation β N).coeff d = powerCoeff 4 β d := by
  rw [powerCoeff_eq_sum_of_degree_le 4 β d N hd]
  simp only [binomialTruncation, coeff_sum, coeff_C_mul]

/-- The exact finite word jet at zero uses the manuscript's coefficient,
multiplied by a strictly positive natural-number factor. -/
theorem binomialTruncation_word_coeff_zero (β : ℝ) (w : List (Fin 4)) :
    (wordPDeriv w (binomialTruncation β w.length)).coeff 0 =
      (wordFactor w 0 : ℝ) * powerCoeff 4 β (wordIndex w) := by
  rw [coeff_wordPDeriv, zero_add, binomialTruncation_coeff β _ _ (wordIndex_degree w).le]

theorem binomialTruncation_word_coeff_zero_nonneg (β : ℝ)
    (hβ : NonnegativePower 4 β) (w : List (Fin 4)) :
    0 ≤ (wordPDeriv w (binomialTruncation β w.length)).coeff 0 := by
  rw [binomialTruncation_word_coeff_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (hβ _)

end Results.SharpPowersKz.CoefficientJets
