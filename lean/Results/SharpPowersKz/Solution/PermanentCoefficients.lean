import Results.SharpPowersKz.Solution.MacMahonCopies
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Factorial coefficients under splitting variables into labeled copies

Formal differentiation proves the squarefree coefficient identity over every
commutative semiring, with no division or characteristic-zero hypothesis.
-/

noncomputable section

namespace Results.SharpPowersKz.PermanentCoefficients

open MvPolynomial MacMahon

variable {σ τ R : Type*} [CommSemiring R]

/-- Multiplicity index of a word of derivative directions. -/
def wordIndex : List σ → σ →₀ ℕ
  | [] => 0
  | i :: w => Finsupp.single i 1 + wordIndex w

/-- Integer coefficient multiplier for the indicated word of derivatives. -/
def wordFactor : List σ → (σ →₀ ℕ) → ℕ
  | [], _ => 1
  | i :: w, d => (d i + 1) * wordFactor w (d + Finsupp.single i 1)

/-- Iterate formal partial derivatives in a finite word of directions. -/
def wordPDeriv : List σ → MvPolynomial σ R → MvPolynomial σ R
  | [], p => p
  | i :: w, p => pderiv i (wordPDeriv w p)

theorem wordIndex_append (w v : List σ) : wordIndex (w ++ v) = wordIndex w + wordIndex v := by
  induction w with
  | nil => simp [wordIndex]
  | cons i w ih => simp [wordIndex, ih, add_assoc]

theorem wordIndex_map (f : σ → τ) (w : List σ) :
    wordIndex (w.map f) = (wordIndex w).mapDomain f := by
  induction w with
  | nil => simp [wordIndex]
  | cons i w ih => simp [wordIndex, ih, Finsupp.mapDomain_add]

theorem wordFactor_append (w v : List σ) (d : σ →₀ ℕ) :
    wordFactor (w ++ v) d = wordFactor w d * wordFactor v (d + wordIndex w) := by
  induction w generalizing d with
  | nil => simp [wordFactor, wordIndex]
  | cons i w ih => simp [wordFactor, wordIndex, ih, add_assoc, Nat.mul_assoc]

theorem wordIndex_apply [DecidableEq σ] (w : List σ) (i : σ) :
    wordIndex w i = w.count i := by
  induction w with
  | nil => simp [wordIndex]
  | cons j w ih =>
      by_cases h : j = i
      · subst j; simp [wordIndex, ih, Nat.add_comm]
      · simp [wordIndex, ih, h, Ne.symm h]

theorem wordFactor_zero [Fintype σ] (w : List σ) :
    wordFactor w 0 = ∏ i, (wordIndex w i).factorial := by
  classical
  induction w using List.reverseRecOn with
  | nil => simp [wordFactor, wordIndex]
  | append_singleton w i ih =>
      rw [wordFactor_append, ih]
      simp only [wordFactor, wordIndex, zero_add, mul_one, wordIndex_append,
        add_zero]
      have he (j : σ) : ((wordIndex w + Finsupp.single i 1 : σ →₀ ℕ) j).factorial =
          (if j = i then wordIndex w i + 1 else 1) * (wordIndex w j).factorial := by
        by_cases hj : j = i
        · subst j
          simp [Nat.factorial_succ]
        · simp [Finsupp.single_eq_of_ne hj, hj]
      simp_rw [he]
      rw [Finset.prod_mul_distrib]
      simp [Nat.mul_comm]

theorem coeff_wordPDeriv (w : List σ) (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (wordPDeriv w p).coeff d = (wordFactor w d : R) * p.coeff (d + wordIndex w) := by
  induction w generalizing d with
  | nil => simp [wordPDeriv, wordFactor, wordIndex]
  | cons i w ih =>
      rw [wordPDeriv, coeff_pderiv, ih]
      simp only [wordFactor, wordIndex, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_assoc]
      ring

theorem coeff_wordPDeriv_zero [Fintype σ] (w : List σ) (p : MvPolynomial σ R) :
    (wordPDeriv w p).coeff 0 =
      (∏ i, (wordIndex w i).factorial : ℕ) * p.coeff (wordIndex w) := by
  rw [coeff_wordPDeriv, wordFactor_zero, zero_add]

theorem wordIndex_univ [Fintype σ] :
    wordIndex (Finset.univ.toList : List σ) = squarefreeIndex σ := by
  classical
  ext i
  rw [wordIndex_apply, squarefreeIndex_apply]
  exact List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)


/-- Forgetting copy labels recovers the original multiplicity index. -/
theorem mapDomain_squarefreeIndex [Fintype σ] (d : σ →₀ ℕ) :
    (squarefreeIndex (RepetitionIndex d)).mapDomain Sigma.fst = d := by
  classical
  have hs : (squarefreeIndex (RepetitionIndex d)).support = Finset.univ := by
    ext a
    simp [Finsupp.mem_support_iff]
  ext i
  simp only [Finsupp.mapDomain, Finsupp.sum, hs,
    squarefreeIndex_apply]
  rw [Fintype.sum_sigma]
  simp

theorem pderiv_copySum [DecidableEq σ] (d : σ →₀ ℕ) (a : RepetitionIndex d) (i : σ) :
    pderiv a (copySum d i : MvPolynomial (RepetitionIndex d) R) =
      if i = a.1 then 1 else 0 := by
  classical
  rcases a with ⟨a, k⟩
  by_cases hi : i = a
  · subst i
    simp [copySum, map_sum, pderiv_X, Pi.single_apply]
  · have hne (j : Fin (d i)) : (⟨i, j⟩ : RepetitionIndex d) ≠ ⟨a, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h)
    simp [copySum, map_sum, pderiv_X, hi, hne]

theorem pderiv_splitVariables (d : σ →₀ ℕ) (a : RepetitionIndex d)
    (P : MvPolynomial σ R) :
    pderiv a (splitVariables d P) = splitVariables d (pderiv a.1 P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, splitVariables_X, pderiv_mul, hp, map_add]
      rw [pderiv_copySum]
      by_cases hi : i = a.1
      · subst i
        simp
      · simp [hi, pderiv_X_of_ne hi]

theorem wordPDeriv_splitVariables (d : σ →₀ ℕ) (w : List (RepetitionIndex d))
    (P : MvPolynomial σ R) :
    wordPDeriv w (splitVariables d P) =
      splitVariables d (wordPDeriv (w.map Sigma.fst) P) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [wordPDeriv, ih, pderiv_splitVariables, List.map_cons]

theorem constantCoeff_splitVariables (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    constantCoeff (splitVariables d P) = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, copySum]

/-- Splitting each variable into `d i` labeled copies multiplies the coefficient
of exponent `d` by `∏ i, (d i)!` when extracting the squarefree coefficient.
This is valid in arbitrary characteristic; no factorial division is used. -/
theorem coeff_splitVariables [Fintype σ] (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (splitVariables d P).coeff (squarefreeIndex (RepetitionIndex d)) =
      ((∏ i, (d i).factorial : ℕ) : R) * P.coeff d := by
  classical
  let w := (Finset.univ.toList : List (RepetitionIndex d))
  have hw : wordIndex w = squarefreeIndex (RepetitionIndex d) := wordIndex_univ
  have hm : wordIndex (w.map Sigma.fst) = d := by
    rw [wordIndex_map, hw, mapDomain_squarefreeIndex]
  have hleft := coeff_wordPDeriv_zero w (splitVariables d P)
  simp only [hw, squarefreeIndex_apply, Nat.factorial_one, Finset.prod_const_one,
    Nat.cast_one, one_mul] at hleft
  rw [← hleft, wordPDeriv_splitVariables]
  change constantCoeff (splitVariables d (wordPDeriv (w.map Sigma.fst) P)) = _
  rw [constantCoeff_splitVariables]
  change (wordPDeriv (w.map Sigma.fst) P).coeff 0 = _
  rw [coeff_wordPDeriv_zero, hm]

end Results.SharpPowersKz.PermanentCoefficients
