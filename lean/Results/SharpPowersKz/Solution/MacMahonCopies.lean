import Results.SharpPowersKz.MacMahonDefs
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section

namespace Results.SharpPowersKz.MacMahon

open Finset MvPolynomial

variable {n : Type*}
variable {R : Type*} [CommSemiring R]

/-- The exponent one at every variable, including the empty index type. -/
def squarefreeIndex (n : Type*) [Fintype n] : n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem squarefreeIndex_apply [Fintype n] (i : n) : squarefreeIndex n i = 1 := by
  simp [squarefreeIndex]

/-- Replace one variable by a sum of separately labelled copies. -/
def copySum (d : n →₀ ℕ) (i : n) : MvPolynomial (RepetitionIndex d) R :=
  ∑ j : Fin (d i), X ⟨i, j⟩

def splitVariables (d : n →₀ ℕ) :
    MvPolynomial n R →+* MvPolynomial (RepetitionIndex d) R :=
  eval₂Hom C (copySum d)

@[simp] theorem splitVariables_X (d : n →₀ ℕ) (i : n) :
    splitVariables (R := R) d (X i) = copySum d i := by
  simp [splitVariables]

@[simp] theorem splitVariables_C (d : n →₀ ℕ) (r : R) :
    splitVariables d (C r) = C r := by
  simp [splitVariables]

@[simp] theorem indexDegree_squarefreeIndex (n : Type*) [Fintype n] :
    indexDegree (squarefreeIndex n) = Fintype.card n := by
  classical
  simp [indexDegree, Finsupp.sum_fintype]
@[simp] theorem card_repetitionIndex {n : Type*} [Fintype n] (d : n →₀ ℕ) :
    Fintype.card (RepetitionIndex d) = indexDegree d := by
  classical
  simp [RepetitionIndex, Fintype.card_sigma, indexDegree, Finsupp.sum_fintype]

end Results.SharpPowersKz.MacMahon
