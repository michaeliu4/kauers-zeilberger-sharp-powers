import Results.SharpPowersKz.Solution.MacMahonCopies
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section
open Finset MvPolynomial Matrix
namespace Results.SharpPowersKz.MacMahon
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Splitting variables is exactly repetition of both matrix indices. -/
theorem splitVariables_determinantPoly (H : Matrix n n ℂ) (d : n →₀ ℕ) :
    splitVariables d (determinantPoly H) = determinantPoly (repeatedMatrix H d d) := by
  classical
  let U : Matrix n (RepetitionIndex d) (MvPolynomial (RepetitionIndex d) ℂ) :=
    fun i k => if i = k.1 then 1 else 0
  let V : Matrix (RepetitionIndex d) n (MvPolynomial (RepetitionIndex d) ℂ) :=
    fun k j => X k * C (H k.1 j)
  have hUV : U * V = diagonal (copySum d) * H.map C := by
    apply Matrix.ext
    intro i j
    simp [Matrix.diagonal_apply, Matrix.mul_apply, U, V, Fintype.sum_sigma, copySum, Finset.sum_mul]
  have hVU : V * U = diagonal X * (repeatedMatrix H d d).map C := by
    apply Matrix.ext
    intro i j
    simp [Matrix.diagonal_apply, Matrix.mul_apply, U, V, repeatedMatrix]
  calc
    splitVariables d (determinantPoly H) =
        det (1 - diagonal (copySum d) * H.map C) := by
      rw [determinantPoly, RingHom.map_det]
      congr 1
      apply Matrix.ext
      intro i j
      simp [Matrix.diagonal_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    _ = det (1 - U * V) := by rw [hUV]
    _ = det (1 - V * U) := Matrix.det_one_sub_mul_comm U V
    _ = determinantPoly (repeatedMatrix H d d) := by rw [hVU]; rfl

omit [DecidableEq n] in
theorem reciprocalCoeff_splitVariables_of_coeff (P : MvPolynomial n ℂ) (d : n →₀ ℕ)
    (hc : ∀ Q : MvPolynomial n ℂ,
      (splitVariables d Q).coeff (squarefreeIndex (RepetitionIndex d)) =
        (∏ i, (d i).factorial : ℕ) * Q.coeff d) :
    reciprocalCoeff (splitVariables d P) (squarefreeIndex (RepetitionIndex d)) =
      (∏ i, (d i).factorial : ℕ) * reciprocalCoeff P d := by
  classical
  unfold reciprocalCoeff
  rw [indexDegree_squarefreeIndex, card_repetitionIndex]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := hc ((1 - P) ^ j)
  simpa only [map_pow, map_sub, map_one] using h

theorem reciprocalCoeff_eq_permanent_of_squarefree
    (H : Matrix n n ℂ) (d : n →₀ ℕ)
    (hc : ∀ Q : MvPolynomial n ℂ,
      (splitVariables d Q).coeff (squarefreeIndex (RepetitionIndex d)) =
        (∏ i, (d i).factorial : ℕ) * Q.coeff d)
    (hs : reciprocalCoeff (determinantPoly (repeatedMatrix H d d))
      (squarefreeIndex (RepetitionIndex d)) = (repeatedMatrix H d d).permanent) :
    reciprocalCoeff (determinantPoly H) d =
      (repeatedMatrix H d d).permanent / (∏ i, (d i).factorial : ℕ) := by
  have hf : (∏ i, (d i).factorial : ℕ) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero (d i))
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hf)).2
  have hl := reciprocalCoeff_splitVariables_of_coeff (determinantPoly H) d hc
  rw [splitVariables_determinantPoly, hs] at hl
  simpa only [mul_comm] using hl.symm

end Results.SharpPowersKz.MacMahon
