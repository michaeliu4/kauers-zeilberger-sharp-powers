import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic identities for the sharp powers argument

This file checks the polynomial identities used in the proof for the
Kauers--Zeilberger denominator.  The basic identities are stated over an
arbitrary commutative ring; only the specialization involving `sqrt 3` uses
the real numbers.
-/

namespace Results.SharpPowersKz.Algebra

section Ring

variable {R : Type*} [CommRing R]

/-- The elementary symmetric polynomial of degree two in four variables. -/
def e2 (x y z w : R) : R :=
  x * y + x * z + x * w + y * z + y * w + z * w

/-- The elementary symmetric polynomial of degree three in four variables. -/
def e3 (x y z w : R) : R :=
  x * y * z + x * y * w + x * z * w + y * z * w

/-- The elementary symmetric polynomial of degree four in four variables. -/
def e4 (x y z w : R) : R := x * y * z * w

/-- The one-parameter Kauers--Zeilberger denominator
`1 - e₁ + 2 e₃ + κ e₄`. -/
def pκ (κ x y z w : R) : R :=
  1 - x - y - z - w +
    2 * (x * y * z + x * y * w + x * z * w + y * z * w) +
    κ * (x * y * z * w)

/-- The linear term `L` arising from the rank-two dilation. -/
def kzL (x y z w : R) : R :=
  x + y + z + w + (x + y) * (z + w)

/-- The quadratic term `R` arising from the rank-two dilation. -/
def kzR (x y z w : R) : R :=
  (x + y + 2 * x * y) * (z + w + 2 * z * w)

/-- Equation (3.6) of the paper: the original denominator is `1 - L + R`. -/
theorem pFour_eq_one_sub_kzL_add_kzR (x y z w : R) :
    pκ 4 x y z w = 1 - kzL x y z w + kzR x y z w := by
  simp only [pκ, kzL, kzR]
  ring

/-- The same factorization with the quartic parameter left free. -/
theorem pκ_eq_one_sub_kzL_add_kzR_add (κ x y z w : R) :
    pκ κ x y z w =
      1 - kzL x y z w + kzR x y z w + (κ - 4) * e4 x y z w := by
  simp only [pκ, kzL, kzR, e4]
  ring

/-- Equal-variable specialization of the quartic family. -/
theorem pκ_diagonal (κ t : R) :
    pκ κ t t t t = (1 - 2 * t - 2 * t ^ 2) ^ 2 + (κ - 4) * t ^ 4 := by
  simp only [pκ]
  ring

end Ring

section Dilation

open Matrix

/-- The rank-two matrix in equation (3.1) of the paper. -/
def dilationC : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, -Complex.I, 1;
     Complex.I, -1, 1;
     1, 1, 0]

/-- A convenient explicit `3 × 3` diagonal matrix. -/
def diagonalThree (a b c : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![a, 0, 0;
     0, b, 0;
     0, 0, c]

/-- The displayed matrix has vanishing determinant. -/
theorem dilationC_det : dilationC.det = 0 := by
  simp [dilationC, Matrix.det_fin_three, Complex.I_mul_I]

/-- Its upper-left `2 × 2` minor is `-2`, so the displayed matrix is not
of rank at most one.  Together with `dilationC_det`, this certifies the
paper's rank-two assertion without invoking a rank convention. -/
theorem dilationC_upperLeftMinor :
    dilationC 0 0 * dilationC 1 1 - dilationC 0 1 * dilationC 1 0 = -2 := by
  simp [dilationC, Complex.I_mul_I]
  ring

/-- The coefficient `ℒ` in the determinant of the six-variable dilation. -/
def dilationL (x y ξ z w η : ℂ) : ℂ :=
  (x + y) * (z + w) + η * (x + y) + ξ * (z + w)

/-- The coefficient `ℛ` in the determinant of the six-variable dilation. -/
def dilationR (x y ξ z w η : ℂ) : ℂ :=
  (2 * x * y + ξ * (x + y)) * (2 * z * w + η * (z + w))

/-- Specializing the two auxiliary variables to one gives the `L` used for
the Kauers--Zeilberger denominator. -/
theorem dilationL_specialize (x y z w : ℂ) :
    dilationL x y 1 z w 1 = kzL x y z w := by
  simp only [dilationL, kzL, one_mul]
  ring

/-- Specializing the two auxiliary variables to one gives the `R` used for
the Kauers--Zeilberger denominator. -/
theorem dilationR_specialize (x y z w : ℂ) :
    dilationR x y 1 z w 1 = kzR x y z w := by
  simp only [dilationR, kzR, one_mul]
  ring

/-- The matrix product in the dilation, expanded entry by entry. -/
def dilationProduct (x y ξ z w η : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![x * (η + w + z), x * (η + Complex.I * w - Complex.I * z),
        x * (-Complex.I * w + z);
     y * (η - Complex.I * w + Complex.I * z), y * (η + w + z),
        y * (-w + Complex.I * z);
     ξ * (Complex.I * w + z), ξ * (-w - Complex.I * z), ξ * (w + z)]

theorem dilation_matrix_product (x y ξ z w η : ℂ) :
    diagonalThree x y ξ * dilationC * diagonalThree z w η * dilationCᴴ =
      dilationProduct x y ξ z w η := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalThree, dilationC, dilationProduct, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply, Complex.conj_I] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Equation (3.4): the explicit rank-two dilation has determinant
`1 - t ℒ + t² ℛ`. -/
theorem dilation_det_identity (t x y ξ z w η : ℂ) :
    Matrix.det
        (1 - t • (diagonalThree x y ξ * dilationC * diagonalThree z w η * dilationCᴴ)) =
      1 - t * dilationL x y ξ z w η + t ^ 2 * dilationR x y ξ z w η := by
  rw [dilation_matrix_product]
  rw [Matrix.det_fin_three]
  simp [Matrix.sub_apply, smul_eq_mul, dilationProduct, dilationL, dilationR]
  ring_nf
  rw [Complex.I_sq]
  ring

end Dilation

section Tangent

/-- The positive zero of `1 - 2t - 2t²`. -/
noncomputable def rho : ℝ := (Real.sqrt 3 - 1) / 2

/-- The tangent-cone identity, with the square-root relation exposed as a hypothesis.
This form isolates the algebra from facts about the real square root. -/
theorem tangent_identity_of_sq_three (s r ε x y z w : ℝ)
    (hs : s ^ 2 = 3) (hr : r = (s - 1) / 2) :
    pκ 4 (r - ε * x) (r - ε * y) (r - ε * z) (r - ε * w) =
      2 * ε ^ 2 *
        (e2 x y z w - s * ε * e3 x y z w + 2 * ε ^ 2 * e4 x y z w) := by
  subst r
  simp only [pκ, e2, e3, e4]
  let q : ℝ :=
    (4 * ε ^ 2 * w * x + 4 * ε ^ 2 * w * y + 4 * ε ^ 2 * w * z +
      4 * ε ^ 2 * x * y + 4 * ε ^ 2 * x * z + 4 * ε ^ 2 * y * z -
      2 * ε * s * w - 2 * ε * s * x - 2 * ε * s * y - 2 * ε * s * z +
      s ^ 2 - 3) / 4
  calc
    1 - ((s - 1) / 2 - ε * x) - ((s - 1) / 2 - ε * y) -
          ((s - 1) / 2 - ε * z) - ((s - 1) / 2 - ε * w) +
          2 * (((s - 1) / 2 - ε * x) * ((s - 1) / 2 - ε * y) *
              ((s - 1) / 2 - ε * z) +
            ((s - 1) / 2 - ε * x) * ((s - 1) / 2 - ε * y) *
              ((s - 1) / 2 - ε * w) +
            ((s - 1) / 2 - ε * x) * ((s - 1) / 2 - ε * z) *
              ((s - 1) / 2 - ε * w) +
            ((s - 1) / 2 - ε * y) * ((s - 1) / 2 - ε * z) *
              ((s - 1) / 2 - ε * w)) +
          4 * (((s - 1) / 2 - ε * x) * ((s - 1) / 2 - ε * y) *
            ((s - 1) / 2 - ε * z) * ((s - 1) / 2 - ε * w)) =
        2 * ε ^ 2 *
            (x * y + x * z + x * w + y * z + y * w + z * w -
              s * ε * (x * y * z + x * y * w + x * z * w + y * z * w) +
              2 * ε ^ 2 * (x * y * z * w)) + (s ^ 2 - 3) * q := by
      dsimp only [q]
      ring
    _ = 2 * ε ^ 2 *
        (x * y + x * z + x * w + y * z + y * w + z * w -
          s * ε * (x * y * z + x * y * w + x * z * w + y * z * w) +
          2 * ε ^ 2 * (x * y * z * w)) := by rw [hs]; ring

/-- Equation (4.4) of the paper, at `ρ = (√3 - 1)/2`. -/
theorem tangent_identity (ε x y z w : ℝ) :
    pκ 4 (rho - ε * x) (rho - ε * y) (rho - ε * z) (rho - ε * w) =
      2 * ε ^ 2 *
        (e2 x y z w - Real.sqrt 3 * ε * e3 x y z w +
          2 * ε ^ 2 * e4 x y z w) := by
  apply tangent_identity_of_sq_three (s := Real.sqrt 3)
  · exact Real.sq_sqrt (by norm_num)
  · rfl

/-- The defining quadratic vanishes at `rho`. -/
theorem one_sub_two_mul_rho_sub_two_mul_rho_sq :
    1 - 2 * rho - 2 * rho ^ 2 = 0 := by
  unfold rho
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The tangent point is positive. -/
theorem rho_pos : 0 < rho := by
  unfold rho
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith

end Tangent

section Quartic

/-- The equal-variable quartic, in its sum-of-a-square form. -/
def diagonalQuartic (κ t : ℝ) : ℝ :=
  (1 - 2 * t - 2 * t ^ 2) ^ 2 + (κ - 4) * t ^ 4

/-- Its formal first derivative. -/
def diagonalQuarticDeriv (κ t : ℝ) : ℝ :=
  2 * (1 - 2 * t - 2 * t ^ 2) * (-2 - 4 * t) + 4 * (κ - 4) * t ^ 3

/-- For a quartic coefficient above the sharp boundary, the diagonal is
strictly positive on the whole real axis. -/
theorem diagonalQuartic_pos_all {κ t : ℝ} (hκ : 4 < κ) :
    0 < diagonalQuartic κ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num [diagonalQuartic]
  · have ht4 : 0 < t ^ 4 := by
      rw [show t ^ 4 = (t ^ 2) ^ 2 by ring]
      exact pow_pos (sq_pos_of_ne_zero ht) 2
    have hquartic : 0 < (κ - 4) * t ^ 4 :=
      mul_pos (sub_pos.mpr hκ) ht4
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hquartic

/-- The nonnegative-axis form used directly in the paper. -/
theorem diagonalQuartic_pos {κ t : ℝ} (hκ : 4 < κ) (_ht : 0 ≤ t) :
    0 < diagonalQuartic κ t :=
  diagonalQuartic_pos_all hκ

/-- The preceding positivity stated directly for `pκ`. -/
theorem pκ_diagonal_pos {κ t : ℝ} (hκ : 4 < κ) (ht : 0 ≤ t) :
    0 < pκ κ t t t t := by
  rw [pκ_diagonal]
  exact diagonalQuartic_pos hκ ht

/-- The direct `pκ` statement on the whole real axis. -/
theorem pκ_diagonal_pos_all {κ t : ℝ} (hκ : 4 < κ) :
    0 < pκ κ t t t t := by
  rw [pκ_diagonal]
  exact diagonalQuartic_pos_all hκ

/-- At the old double root `rho`, the derivative of the perturbed quartic
is exactly its quartic contribution. -/
theorem diagonalQuarticDeriv_at_rho (κ : ℝ) :
    diagonalQuarticDeriv κ rho = 4 * (κ - 4) * rho ^ 3 := by
  simp only [diagonalQuarticDeriv, one_sub_two_mul_rho_sub_two_mul_rho_sq,
    zero_mul, mul_zero, zero_add]

/-- Above the sharp quartic boundary, that derivative is positive. -/
theorem diagonalQuarticDeriv_at_rho_pos {κ : ℝ} (hκ : 4 < κ) :
    0 < diagonalQuarticDeriv κ rho := by
  rw [diagonalQuarticDeriv_at_rho]
  exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hκ)) (pow_pos rho_pos 3)

end Quartic

end Results.SharpPowersKz.Algebra
