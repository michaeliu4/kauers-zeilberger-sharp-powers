import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic

/-! Neutral statement of the classical MacMahon Master Theorem.

This module contains only definitions and Mathlib imports, so Challenge and Solution
can use the identical theorem statement without importing proof modules.
The proposition is proved in Solution/MacMahonTheorem.lean.
-/

noncomputable section
open scoped Matrix
open Finset

namespace Results.SharpPowersKz

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
variable {R : Type*} [CommSemiring R]

/-- Labeled copies used when repeating rows and columns. -/
abbrev RepetitionIndex (ν : m → ℕ) := Σ i, Fin (ν i)

/-- Repeat row i exactly ν i times and column j exactly μ j times. -/
def repeatedMatrix (B : Matrix m n R) (ν : m → ℕ) (μ : n → ℕ) :
    Matrix (RepetitionIndex ν) (RepetitionIndex μ) R :=
  B.submatrix Sigma.fst Sigma.fst

namespace MacMahon

variable {ι A : Type*} [CommRing A]

def indexDegree (d : ι →₀ ℕ) : ℕ := d.sum fun _ n => n

/-- Literal finite geometric coefficient of an inverse with constant term one. -/
def reciprocalCoeff (P : MvPolynomial ι A) (d : ι →₀ ℕ) : A :=
  ∑ j ∈ Finset.range (indexDegree d + 1), ((1 - P) ^ j).coeff d

/-- The universal diagonal-variable determinant from MacMahon's theorem. -/
def determinantPoly {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) :
    MvPolynomial n ℂ :=
  Matrix.det (1 - Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C)

/-- The beta=1 permanent form of MacMahon's Master Theorem, as explicit
    coefficients. Source: Tuite, JCTA 120 (2013), Theorem 2.1 and Remark 2.2,
    DOI 10.1016/j.jcta.2012.07.007; arXiv:1111.4047, equations (1)--(5).
    This proposition is proved in Solution/MacMahonTheorem.lean; it is not an axiom. -/
def MacMahonMasterTheorem : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (d : n →₀ ℕ),
    reciprocalCoeff (determinantPoly H) d =
      (repeatedMatrix H d d).permanent / (∏ i, (d i).factorial : ℕ)

end MacMahon
end Results.SharpPowersKz
