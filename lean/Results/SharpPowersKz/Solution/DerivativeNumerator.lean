import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# Polynomial numerators for derivatives of inverse powers

The recursive polynomials below are the algebraic numerator candidates for
coordinate derivatives of `Q ^ (-β)`. This file proves their homogeneity under
constant scaling of `Q`. It does not assert the analytic derivative identity,
the formal-coefficient/analytic-jet bridge, or a tangent-cone necessity theorem.
-/

namespace Results.SharpPowersKz.DerivativeNumerator

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The head of the word is the final coordinate derivative applied. -/
noncomputable def numerator (β : R) (Q : MvPolynomial σ R) :
    List σ → MvPolynomial σ R
  | [] => 1
  | i :: w =>
      Q * pderiv i (numerator β Q w) -
        C (β + (w.length : R)) * numerator β Q w * pderiv i Q

@[simp]
theorem numerator_nil (β : R) (Q : MvPolynomial σ R) :
    numerator β Q [] = 1 := rfl

theorem numerator_cons (β : R) (Q : MvPolynomial σ R) (i : σ) (w : List σ) :
    numerator β Q (i :: w) =
      Q * pderiv i (numerator β Q w) -
        C (β + (w.length : R)) * numerator β Q w * pderiv i Q := rfl

@[simp]
theorem numerator_singleton (β : R) (Q : MvPolynomial σ R) (i : σ) :
    numerator β Q [i] = -(C β * pderiv i Q) := by
  simp [numerator]

/-- A constant denominator has zero numerator at every positive order. -/
theorem numerator_constant (β a : R) (w : List σ) :
    numerator β (C a : MvPolynomial σ R) w = if w = [] then 1 else 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [numerator_cons, ih]
      cases w <;> simp

/-- Each order-n numerator is homogeneous of degree n in the denominator.
No positivity or nonzero assumption on the scalar is needed. -/
theorem numerator_const_mul (β a : R) (Q : MvPolynomial σ R) (w : List σ) :
    numerator β (C a * Q) w = C (a ^ w.length) * numerator β Q w := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [numerator_cons, ih, pderiv_C_mul,
        List.length_cons, pow_succ, map_mul]
      ring

/-- Forming a derivative numerator commutes with coefficient specialization.
For example the coefficient ring can first be a polynomial ring in a tangent
parameter, and the parameter can then be evaluated at a real number. -/
theorem numerator_map {S : Type*} [CommRing S] (φ : R →+* S)
    (β : R) (Q : MvPolynomial σ R) (w : List σ) :
    numerator (φ β) (MvPolynomial.map φ Q) w =
      MvPolynomial.map φ (numerator β Q w) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [numerator_cons, ih, pderiv_map, map_sub, map_mul,
        MvPolynomial.map_C, map_add, map_natCast]

end Results.SharpPowersKz.DerivativeNumerator
