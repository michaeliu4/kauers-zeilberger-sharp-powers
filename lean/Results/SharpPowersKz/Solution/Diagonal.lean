import Results.SharpPowersKz.Solution.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Coeff

/-! Exact diagonal contraction of the finite multivariate coefficients. -/

noncomputable section
namespace Results.SharpPowersKz

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def diagonalMap : MvPolynomial (Fin 4) A →ₐ[A] Polynomial A :=
  MvPolynomial.aeval fun _ => Polynomial.X

def diagonalPerturbation (κ : A) : Polynomial A :=
  4 * Polynomial.X - 8 * Polynomial.X ^ 3 - Polynomial.C κ * Polynomial.X ^ 4

omit [Algebra ℚ A] in
theorem diagonalMap_coeff (p : MvPolynomial (Fin 4) A) (n : ℕ) :
    (diagonalMap p).coeff n =
      ∑ d ∈ p.support, if degree d = n then p.coeff d else 0 := by
  classical
  change (p.eval₂ Polynomial.C (fun _ => Polynomial.X)).coeff n = _
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.prod_pow_eq_pow_sum]
  change (Polynomial.C (p.coeff d) * Polynomial.X ^ degree d).coeff n = _
  rw [Polynomial.coeff_C_mul_X_pow]
  simp [eq_comm]

omit [Algebra ℚ A] in
theorem diagonalMap_perturbation (κ : A) :
    diagonalMap (perturbation κ) = diagonalPerturbation κ := by
  simp only [perturbation, diagonalMap, map_sub, map_add, map_mul,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_ofNat, Polynomial.algebraMap_eq]
  change _ = 4 * Polynomial.X - 8 * Polynomial.X ^ 3 -
    Polynomial.C κ * Polynomial.X ^ 4
  ring

def finitePowerPolynomial (κ β : A) (n : ℕ) : MvPolynomial (Fin 4) A :=
  ∑ k ∈ Finset.range (n + 1), MvPolynomial.C (binomialWeight β k) * perturbation κ ^ k

theorem finitePowerPolynomial_coeff (κ β : A) (d : MultiIndex) :
    (finitePowerPolynomial κ β (degree d)).coeff d = powerCoeff κ β d := by
  simp [finitePowerPolynomial, powerCoeff, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]

theorem diagonalMap_finitePowerPolynomial (κ β : A) (n : ℕ) :
    diagonalMap (finitePowerPolynomial κ β n) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (binomialWeight β k) * diagonalPerturbation κ ^ k := by
  simp only [finitePowerPolynomial, map_sum, map_mul, map_pow,
    diagonalMap_perturbation]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp [diagonalMap]

/-- Nonnegative multivariate coefficients imply nonnegative diagonal Taylor
coefficients, expressed by the same finite binomial sum. -/
theorem diagonal_binomial_coefficient_nonneg (κ β : ℝ)
    (h : NonnegativePower κ β) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (n + 1),
      binomialWeight β k * (diagonalPerturbation κ ^ k).coeff n := by
  have heq : (diagonalMap (finitePowerPolynomial κ β n)).coeff n =
      ∑ k ∈ Finset.range (n + 1),
        binomialWeight β k * (diagonalPerturbation κ ^ k).coeff n := by
    rw [diagonalMap_finitePowerPolynomial]
    simp [Polynomial.coeff_C_mul]
  rw [← heq, diagonalMap_coeff]
  apply Finset.sum_nonneg
  intro d hd
  split_ifs with hdeg
  · rw [← hdeg, finitePowerPolynomial_coeff]
    exact h d
  · exact le_refl 0

end Results.SharpPowersKz
