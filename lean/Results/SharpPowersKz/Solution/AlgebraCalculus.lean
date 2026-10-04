import Results.SharpPowersKz.Solution.Algebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Calculus bridge for the diagonal quartic

The algebraic expression for the derivative lives in `Algebra`; this small
leaf verifies that it is the analytic derivative as well.
-/

namespace Results.SharpPowersKz.Algebra

/-- `diagonalQuarticDeriv` is the derivative of `diagonalQuartic`. -/
theorem hasDerivAt_diagonalQuartic (κ t : ℝ) :
    HasDerivAt (diagonalQuartic κ) (diagonalQuarticDeriv κ t) t := by
  have hinner : HasDerivAt (fun u : ℝ => 1 - 2 * u - 2 * u ^ 2) (-2 - 4 * t) t := by
    have hraw := (((hasDerivAt_id t).const_mul 2).const_sub 1).sub
      (((hasDerivAt_id t).pow 2).const_mul 2)
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun u => by
        simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · dsimp only [id_eq]
      ring
  have hsquare := hinner.pow 2
  have hquartic := ((hasDerivAt_id t).pow 4).const_mul (κ - 4)
  have hsum := hsquare.add hquartic
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall fun u => by
      simp only [diagonalQuartic, Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [diagonalQuarticDeriv, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

end Results.SharpPowersKz.Algebra
