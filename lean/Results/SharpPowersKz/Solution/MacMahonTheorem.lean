import Results.SharpPowersKz.Solution.MacMahonCopies
import Results.SharpPowersKz.Solution.MacMahon
import Mathlib.Algebra.MvPolynomial.Rename
import Results.SharpPowersKz.Solution.MacMahonRecurrence
import Results.SharpPowersKz.Solution.MacMahonRestriction
import Results.SharpPowersKz.Solution.PermanentCoefficients

noncomputable section
open Finset MvPolynomial Equiv
namespace Results.SharpPowersKz.MacMahon
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

omit [DecidableEq n] in
lemma sum_single_eq_squarefree (σ : Equiv.Perm n) :
    (∑ i, Finsupp.single (σ i) 1) = squarefreeIndex n := by
  rw [Equiv.sum_comp σ (fun i : n => Finsupp.single i (1 : ℕ))]
  ext i
  simp

lemma bijective_of_sum_single_eq_squarefree (f : n → n)
    (h : (∑ i, Finsupp.single (f i) 1) = squarefreeIndex n) : Function.Bijective f := by
  apply (Finite.surjective_iff_bijective).mp
  intro j
  by_contra hn
  have hne : ∀ i, f i ≠ j := by simpa only [not_exists] using hn
  have hval := congrArg (fun d : n →₀ ℕ => d j) h
  simp [hne] at hval

lemma squarefree_coeff_linearProduct (A : Matrix n n R) :
    (∏ j, ∑ i, X i * C (A i j)).coeff (squarefreeIndex n) = A.permanent := by
  classical
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, coeff_sum]
  have hprod (f : n → n) : (∏ j, X (f j) * C (A (f j) j)) =
      monomial (∑ j, Finsupp.single (f j) 1) (∏ j, A (f j) j) := by
    rw [MvPolynomial.monomial_sum_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp [X, mul_comm, C_mul_monomial]
  simp_rw [hprod, coeff_monomial]
  calc
    _ = ∑ f : n → n with Function.Bijective f, ∏ j, A (f j) j := by
      rw [← Finset.sum_filter]
      congr 1
      ext f
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨bijective_of_sum_single_eq_squarefree f,
        fun h => sum_single_eq_squarefree (Equiv.ofBijective f h)⟩
    _ = ∑ σ : Equiv.Perm n, ∏ j, A (σ j) j := by
      exact sum_bij (fun p h ↦ Equiv.ofBijective p (mem_filter.1 h).2)
        (fun _ _ ↦ mem_univ _)
        (fun _ _ _ _ h ↦ by injection h)
        (fun b _ ↦ ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩,
          coe_fn_injective rfl⟩) (fun _ _ ↦ rfl)
    _ = _ := rfl


def indexOn (s : Finset n) : n →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1

omit [Fintype n] in
@[simp] lemma indexOn_apply (s : Finset n) (i : n) :
    indexOn s i = if i ∈ s then 1 else 0 := by
  classical
  simp [indexOn, Finsupp.single_apply]

lemma indexOn_compl_add (s : Finset n) : indexOn s + indexOn sᶜ = squarefreeIndex n := by
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

omit [Fintype n] in
lemma indexOn_injective : Function.Injective (indexOn : Finset n → n →₀ ℕ) := by
  intro s t h
  ext i
  have hv := congrArg (fun d : n →₀ ℕ => d i) h
  simp only [indexOn_apply] at hv
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

lemma indexOn_univ : indexOn (Finset.univ : Finset n) = squarefreeIndex n := by
  ext i
  simp

omit [Fintype n] [DecidableEq n] in
lemma mapDomain_squarefree_subtype (s : Finset n) :
    (squarefreeIndex s).mapDomain Subtype.val = indexOn s := by
  rw [← sum_single_eq_squarefree (Equiv.refl s)]
  simp only [Equiv.refl_apply, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  exact (Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => Finsupp.single i 1)).symm

omit [Fintype n] in
lemma killCompl_X_subtype (s : Finset n) (i : n) :
    (X i : MvPolynomial n R).killCompl (Subtype.val_injective (p := fun i => i ∈ s)) =
      if h : i ∈ s then X (⟨i, h⟩ : s) else 0 := by
  classical
  rw [killCompl, aeval_X]
  by_cases hi : i ∈ s
  · have hr : i ∈ Set.range (Subtype.val : s → n) := ⟨⟨i, hi⟩, rfl⟩
    simp only [dif_pos hr, dif_pos hi]
    congr 1
    exact Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, hi⟩
  · have hr : i ∉ Set.range (Subtype.val : s → n) := by simpa using hi
    simp [hi]

lemma killCompl_linearForm (A : Matrix n n R) (s : Finset n) (j : n) :
    (∑ i, X i * C (A i j)).killCompl
      (Subtype.val_injective (p := fun i => i ∈ s)) =
        ∑ i : s, X i * C (A i j) := by
  simp only [map_sum, map_mul, killCompl_C, killCompl_X_subtype]
  simp only [dite_mul, zero_mul]
  let f : n → MvPolynomial s R := fun i =>
    if h : i ∈ s then X (⟨i, h⟩ : s) * C (A i j) else 0
  change (∑ i, f i) = _
  rw [← Finset.sum_subset (Finset.subset_univ s)
    (fun i _ hi => by simp [f, hi])]
  rw [Finset.sum_subtype s (fun _ => Iff.rfl) f]
  apply Finset.sum_congr rfl
  intro i _
  simp [f, i.property]

lemma coeff_indexOn_linearProduct (A : Matrix n n R) (s : Finset n) :
    (∏ j : s, ∑ i, X i * C (A i j)).coeff (indexOn s) =
      (A.submatrix (Subtype.val : s → n) Subtype.val).permanent := by
  rw [← mapDomain_squarefree_subtype, ← coeff_killCompl Subtype.val_injective]
  simp only [map_prod, killCompl_linearForm]
  exact squarefree_coeff_linearProduct _


omit [Fintype n] [DecidableEq n] in
lemma prod_X_subtype_eq_monomial (s : Finset n) :
    (∏ i : s, X (i : n) : MvPolynomial n R) = monomial (indexOn s) 1 := by
  rw [← Finset.prod_subtype s (fun _ => Iff.rfl) (fun i => (X i : MvPolynomial n R))]
  simp only [indexOn, X, monomial_sum_one]

omit [DecidableEq n] in
lemma killCompl_linearForm_pred (A : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (j : n) :
    (∑ i, X i * C (A i j)).killCompl (Subtype.val_injective (p := p)) =
      ∑ i : Subtype p, X i * C (A i j) := by
  have hx (i : n) : (X i : MvPolynomial n R).killCompl
      (Subtype.val_injective (p := p)) = if h : p i then X (⟨i, h⟩ : Subtype p) else 0 := by
    rw [killCompl, aeval_X]
    by_cases hi : p i
    · have hr : i ∈ Set.range (Subtype.val : Subtype p → n) := ⟨⟨i, hi⟩, rfl⟩
      simp only [dif_pos hr, dif_pos hi]
      congr 1
      exact Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, hi⟩
    · simp [hi]
  simp only [map_sum, map_mul, killCompl_C, hx, dite_mul, zero_mul]
  let f : n → MvPolynomial (Subtype p) R := fun i =>
    if h : p i then X (⟨i, h⟩ : Subtype p) * C (A i j) else 0
  change (∑ i, f i) = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter p))
    (fun i _ hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp [f, hi])]
  rw [Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp) f]
  apply Finset.sum_congr rfl
  intro i _
  simp [f, i.property]

lemma coeff_squarefree_monomial_linearProduct (A : Matrix n n R) (s : Finset n) :
    ((∏ i : s, X (i : n)) *
      (∏ j : {j // j ∉ s}, ∑ i, X i * C (A i j))).coeff (squarefreeIndex n) =
      (A.submatrix (Subtype.val : {j // j ∉ s} → n) Subtype.val).permanent := by
  rw [prod_X_subtype_eq_monomial, ← indexOn_compl_add s, coeff_monomial_mul, one_mul]
  have hm : (squarefreeIndex {j // j ∉ s}).mapDomain Subtype.val = indexOn sᶜ := by
    rw [← sum_single_eq_squarefree (Equiv.refl {j // j ∉ s})]
    simp only [Equiv.refl_apply, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
    exact (Finset.sum_subtype (p := fun j => j ∉ s) sᶜ (by simp)
      (fun i => Finsupp.single i 1)).symm
  rw [← hm, ← coeff_killCompl Subtype.val_injective]
  simp only [map_prod, killCompl_linearForm_pred]
  exact squarefree_coeff_linearProduct _

lemma determinant_permanent_convolution [Nonempty n] [IsDomain R] (A : Matrix n n R) :
    ∑ s : Finset n, (-1 : R)^s.card *
      (A.submatrix (Subtype.val : s → n) Subtype.val).det *
      (A.submatrix (Subtype.val : {j // j ∉ s} → n) Subtype.val).permanent = 0 := by
  have h := columnLaplacian_principalMinor_convolution
    (A.map (MvPolynomial.C : R →+* MvPolynomial n R)) MvPolynomial.X
  have hc := congrArg (fun p : MvPolynomial n R => p.coeff (squarefreeIndex n)) h
  rw [coeff_sum, coeff_zero] at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro s _
  have hdet : (A.map (MvPolynomial.C : R →+* MvPolynomial n R)).submatrix
      (Subtype.val : s → n) (Subtype.val : s → n) =
      (A.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).map MvPolynomial.C := rfl
  have hmap : ((A.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).map
      (MvPolynomial.C : R →+* MvPolynomial n R)).det =
      C (A.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det := by
    simpa only [RingHom.mapMatrix_apply] using
      (RingHom.map_det (MvPolynomial.C : R →+* MvPolynomial n R)
        (A.submatrix (Subtype.val : s → n) (Subtype.val : s → n))).symm
  rw [hdet, hmap]
  change _ = (((-1 : MvPolynomial n R)^s.card * (∏ i : s, X (i : n)) *
    C (A.submatrix (Subtype.val : s → n) Subtype.val).det) *
      ∏ j : {j // j ∉ s}, ∑ i, X i * C (A i j)).coeff _
  rw [show (-1 : MvPolynomial n R)^s.card = C ((-1 : R)^s.card) by simp]
  rw [show C ((-1 : R)^s.card) * (∏ i : s, X (i : n)) *
      C (A.submatrix (Subtype.val : s → n) Subtype.val).det =
    C ((-1 : R)^s.card * (A.submatrix (Subtype.val : s → n) Subtype.val).det) *
      (∏ i : s, X (i : n)) by rw [map_mul]; ring]
  simp only [mul_assoc, coeff_C_mul, coeff_squarefree_monomial_linearProduct]


lemma mapDomain_squarefree_compl (s : Finset n) :
    (squarefreeIndex {j // j ∉ s}).mapDomain Subtype.val = indexOn sᶜ := by
  rw [← sum_single_eq_squarefree (Equiv.refl {j // j ∉ s})]
  simp only [Equiv.refl_apply, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  exact (Finset.sum_subtype (p := fun j => j ∉ s) sᶜ (by simp)
    (fun i => Finsupp.single i 1)).symm

lemma permanent_empty_compl (A : Matrix n n R) :
    (A.submatrix (Subtype.val : {j // j ∉ (∅ : Finset n)} → n) Subtype.val).permanent =
      A.permanent := by
  let e : {j // j ∉ (∅ : Finset n)} ≃ n :=
    { toFun := Subtype.val
      invFun := fun j => ⟨j, by simp⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  exact permanent_reindex e A

/-- The squarefree coefficient of the reciprocal determinant is a permanent.
The proof compares the inverse recurrence with the independently proved
column-Laplacian determinant/permanent cancellation. -/
theorem squarefree_reciprocal_det_eq_permanent {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) :
    reciprocalCoeff (determinantPoly H) (squarefreeIndex ι) = H.permanent := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h N IH =>
    cases isEmpty_or_nonempty ι with
    | inl hempty =>
      letI := hempty
      have hi : squarefreeIndex ι = 0 := by ext i; exact isEmptyElim i
      simp [hi, determinantPoly, reciprocalCoeff, Matrix.permanent_isEmpty]
    | inr hnonempty =>
      letI := hnonempty
      have hsquare : squarefreeIndex ι ≠ 0 := by
        intro heq
        obtain ⟨i⟩ := hnonempty
        have := congrArg (fun d : ι →₀ ℕ => d i) heq
        simp at this
      have hrec := squarefree_reciprocalCoeff_principalMinor_recurrence H
      have hper := determinant_permanent_convolution H
      have hrest :
          (∑ s ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
            (-1 : ℂ)^s.card * (H.submatrix (Subtype.val : s → ι) Subtype.val).det *
              reciprocalCoeff (determinantPoly H)
                ((squarefreeIndex {j // j ∉ s}).mapDomain Subtype.val)) =
          ∑ s ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
            (-1 : ℂ)^s.card * (H.submatrix (Subtype.val : s → ι) Subtype.val).det *
              (H.submatrix (Subtype.val : {j // j ∉ s} → ι) Subtype.val).permanent := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsne : s ≠ ∅ := (Finset.mem_erase.mp hs).1
        have hlt : Fintype.card {j // j ∉ s} < N := by
          rw [Fintype.card_subtype_compl, Fintype.card_coe]
          have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hsne)
          have hle := Finset.card_le_univ s
          omega
        have hIH := IH (Fintype.card {j // j ∉ s}) hlt
          (H.submatrix (Subtype.val : {j // j ∉ s} → ι) Subtype.val) rfl
        congr 1
        rw [reciprocalCoeff_determinantPoly_restrict_pred H (fun j => j ∉ s)]
        exact hIH
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset ι))] at hrec hper
      simp only [Finset.card_empty, pow_zero, Matrix.det_isEmpty, one_mul] at hrec hper
      rw [mapDomain_squarefree_compl, Finset.compl_empty, indexOn_univ] at hrec
      rw [permanent_empty_compl] at hper
      have hone : (1 : MvPolynomial ι ℂ).coeff (squarefreeIndex ι) = 0 := by
        simp [coeff_one, Ne.symm hsquare]
      rw [hone, hrest] at hrec
      exact add_left_cancel (hrec.trans hper.symm)

/-- MacMahon's Master Theorem, with the exact finite coefficient and labeled
repetition convention used in the shared statement. -/
theorem macMahon_master_theorem : MacMahonMasterTheorem := by
  intro n _ _ H d
  apply reciprocalCoeff_eq_permanent_of_squarefree H d
  · exact PermanentCoefficients.coeff_splitVariables d
  · exact squarefree_reciprocal_det_eq_permanent _

end Results.SharpPowersKz.MacMahon
