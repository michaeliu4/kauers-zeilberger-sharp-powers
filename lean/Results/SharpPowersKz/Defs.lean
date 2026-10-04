import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The coefficient definitions use the formal binomial expansion itself, rather
than the positive expansion that the paper must prove. All sums are finite:
`1 - Pκ` has zero constant coefficient, so terms above total degree cannot
contribute. Parameters may lie in ℝ, ℚ[s], or ℚ[s,λ].
-/
noncomputable section

namespace Results.SharpPowersKz

abbrev MultiIndex := Fin 4 →₀ ℕ

def degree (d : MultiIndex) : ℕ := d.sum fun _ n => n

section Coefficients
variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The polynomial `1 - Pκ`, including the sign of the quartic term. -/
def perturbation (κ : A) : MvPolynomial (Fin 4) A :=
  let x := MvPolynomial.X (0 : Fin 4)
  let y := MvPolynomial.X (1 : Fin 4)
  let z := MvPolynomial.X (2 : Fin 4)
  let w := MvPolynomial.X (3 : Fin 4)
  x + y + z + w - 2 * (x*y*z + x*y*w + x*z*w + y*z*w) -
    MvPolynomial.C κ * x*y*z*w

/-- Rising factorial, with empty product equal to one. -/
def rising (β : A) (n : ℕ) : A := ∏ j ∈ Finset.range n, (β + j)

/-- The scalar coefficient `(β)ₙ/n!` in `(1-u)^(-β)`. -/
def binomialWeight (β : A) (n : ℕ) : A :=
  algebraMap ℚ A ((n.factorial : ℚ)⁻¹) * rising β n

/-- Formal coefficient of `Pκ^(-β)` at the specified monomial. -/
def powerCoeff (κ β : A) (d : MultiIndex) : A :=
  ∑ n ∈ Finset.range (degree d + 1),
    binomialWeight β n * (perturbation κ ^ n).coeff d

end Coefficients

/-- Nonnegativity of every formal coefficient, including the constant term. -/
def NonnegativePower (κ β : ℝ) : Prop := ∀ d, 0 ≤ powerCoeff κ β d

/-- Strict positivity of every coefficient. -/
def PositivePower (κ β : ℝ) : Prop := ∀ d, 0 < powerCoeff κ β d

/-- Coefficient polynomial in the shift `s=β-1`. -/
def shiftedCoeff (d : MultiIndex) : Polynomial ℚ :=
  powerCoeff 4 (1 + Polynomial.X) d

/-- Joint polynomial coefficient in `s,λ`, ordered in that order. -/
def jointCoeff (d : MultiIndex) : MvPolynomial (Fin 2) ℚ :=
  powerCoeff (4 - MvPolynomial.X 1) (1 + MvPolynomial.X 0) d

def ShiftNonnegative : Prop := ∀ d j, 0 ≤ (shiftedCoeff d).coeff j

def JointNonnegative : Prop := ∀ d j, 0 ≤ (jointCoeff d).coeff j

/-- The explicit lower bound in Theorem 1.1. -/
def lowerBound (β : ℝ) (d : MultiIndex) : ℝ :=
  binomialWeight β (degree d) *
    ((d 0 + d 1).choose (d 0) : ℝ) * ((d 2 + d 3).choose (d 2) : ℝ)

end Results.SharpPowersKz
