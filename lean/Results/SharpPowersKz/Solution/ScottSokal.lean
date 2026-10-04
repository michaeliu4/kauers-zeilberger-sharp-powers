import Results.SharpPowersKz.Solution.NumeratorAnalytic
import Results.SharpPowersKz.Solution.TangentTransfer

/-!
Scott--Sokal, Acta Math. 213 (2014), Corollary 1.6. The published theorem
is an explicit proposition parameter, never a new Lean axiom. Its predicate
uses actual iterated coordinate derivatives and smoothness on the entire
positive orthant. No KZ-specific conclusion is included in the proposition.
-/

namespace Results.SharpPowersKz.ScottSokal

open NumeratorCalculus TangentTransfer

theorem e2InversePower_eq (β : ℝ) :
    e2InversePower β = fun x => (e2Poly.eval x) ^ (-β) := by
  funext x
  rw [eval_e2Poly]
  rfl

theorem e2_eval_pos (x : Fin 4 → ℝ) (hx : x ∈ positiveOrthant) :
    0 < e2Poly.eval x := by
  rw [eval_e2Poly]
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  unfold Algebra.e2
  positivity

/-- Proved derivative-numerator semantics supply the actual CM predicate;
the external hypothesis is not used in this bridge. -/
theorem completelyMonotone_of_signed_numerators (β : ℝ)
    (hJ : ∀ (w : List (Fin 4)) (x : Fin 4 → ℝ), x ∈ positiveOrthant →
      0 ≤ (-1 : ℝ) ^ w.length * (DerivativeNumerator.numerator β e2Poly w).eval x) :
    CompletelyMonotone (e2InversePower β) := by
  unfold CompletelyMonotone
  rw [e2InversePower_eq]
  constructor
  · intro x hx
    exact (NumeratorCalculus.analyticAt_eval_neg_rpow e2Poly β x
      (e2_eval_pos x hx)).contDiffAt.contDiffWithinAt
  · intro w x hx
    rw [wordDeriv_neg_rpow β e2Poly w x (e2_eval_pos x hx), ← mul_assoc]
    exact mul_nonneg (hJ w x hx)
      (Real.rpow_nonneg (le_of_lt (e2_eval_pos x hx)) _)

theorem range_of_cube_numerators (hSS : E2InversePowers) (β : ℝ)
    (hJ : ∀ (w : List (Fin 4)) (y : Fin 4 → ℝ),
      (∀ i, 0 < y i ∧ y i < Algebra.rho) →
      0 ≤ (DerivativeNumerator.numerator β pFour w).eval y) :
    β = 0 ∨ 1 ≤ β := by
  apply (hSS β).mp
  apply completelyMonotone_of_signed_numerators
  exact signed_e2_numerator_nonnegative_of_cube β hJ

end Results.SharpPowersKz.ScottSokal
