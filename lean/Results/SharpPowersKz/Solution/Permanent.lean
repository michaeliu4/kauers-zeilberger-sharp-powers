import Results.SharpPowersKz.MacMahonDefs
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Generic permanent identities for the bipartite MacMahon specialization. -/
noncomputable section

open Equiv Equiv.Perm Finset Function
open scoped Matrix

namespace Results.SharpPowersKz

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
variable {R : Type*} [CommSemiring R]

/-- Simultaneously relabeling rows and columns preserves the permanent. -/
theorem permanent_reindex (e : m ≃ n) (B : Matrix n n R) :
    (B.submatrix e e).permanent = B.permanent := by
  classical
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp [Matrix.submatrix, Equiv.permCongr_apply]

/-- Permanent analogue of the upper triangular block determinant identity. -/
theorem permanent_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [Matrix.permanent]
  convert!
    Eq.symm <|
      sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
  · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_nbij (fun σ ↦ σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      simp
    · intro σ₁ _ σ₂ _
      dsimp only
      intro h
      have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
        DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
        Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      use σ₁₂
      rw [← hσ₁₂]
      simp
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
        mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · have hn := (not_exists.mp ha) a2
      exact absurd hx.symm hn
    · apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))
      rw [hx, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-- Swapping the column blocks turns the bipartite permanent into a product. -/
theorem permanent_bipartite (B D : Matrix n n R) :
    (Matrix.fromBlocks 0 B D 0).permanent = B.permanent * D.permanent := by
  have h := Matrix.permanent_permute_rows (Equiv.sumComm n n)
    (Matrix.fromBlocks 0 B D 0)
  change ((Matrix.fromBlocks 0 B D 0).submatrix id Sum.swap).permanent = _ at h
  rw [Matrix.fromBlocks_submatrix_sum_swap_right, Matrix.submatrix_id_id] at h
  rw [← h, permanent_fromBlocks_zero₂₁]

/-- An unbalanced bipartite block matrix has zero permanent. -/
theorem permanent_bipartite_eq_zero_of_card_ne (B : Matrix m n R) (D : Matrix n m R)
    (hcard : Fintype.card m ≠ Fintype.card n) :
    (Matrix.fromBlocks 0 B D 0).permanent = 0 := by
  classical
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro σ _
  by_contra ht
  have hl : ∀ a : m, ∃ b : n, σ (Sum.inl a) = Sum.inr b := by
    intro a
    cases h : σ (Sum.inl a) with
    | inl a' =>
      exfalso
      apply ht
      apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))
      rw [h, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    | inr b => exact ⟨b, rfl⟩
  have hr : ∀ b : n, ∃ a : m, σ (Sum.inr b) = Sum.inl a := by
    intro b
    cases h : σ (Sum.inr b) with
    | inl a => exact ⟨a, rfl⟩
    | inr b' =>
      exfalso
      apply ht
      apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inr b))
      rw [h, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  choose f hf using hl
  choose g hg using hr
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Sum.inl_injective
    apply σ.injective
    rw [hf a, hf b, hab]
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply Sum.inr_injective
    apply σ.injective
    rw [hg a, hg b, hab]
  exact hcard (Nat.le_antisymm (Fintype.card_le_of_injective f hf_inj)
    (Fintype.card_le_of_injective g hg_inj))

/-- Complex conjugation commutes with the permanent, including the empty matrix. -/
theorem permanent_conjTranspose [StarRing R] (B : Matrix n n R) :
    Bᴴ.permanent = star B.permanent := by
  rw [Matrix.conjTranspose]
  calc
    (B.transpose.map star).permanent = star B.transpose.permanent := by
      simp only [Matrix.permanent, Matrix.map_apply, star_sum, star_prod]
    _ = star B.permanent := by rw [Matrix.permanent_transpose]

/-- Pure algebra behind the permanent-square coefficients of the bipartite inverse determinant. -/
theorem permanent_bipartite_star [StarRing R] (B : Matrix n n R) :
    (Matrix.fromBlocks 0 B Bᴴ 0).permanent = B.permanent * star B.permanent := by
  rw [permanent_bipartite, permanent_conjTranspose]

/-- Every balanced bipartite permanent is a real nonnegative squared modulus. -/
theorem permanent_bipartite_normSq (B : Matrix n n ℂ) :
    (Matrix.fromBlocks 0 B Bᴴ 0).permanent = (Complex.normSq B.permanent : ℂ) := by
  rw [permanent_bipartite_star]
  exact Complex.mul_conj _

/-- The balanced formula on distinct finite row and column index types. -/
theorem permanent_bipartite_normSq_of_equiv (e : m ≃ n) (B : Matrix m n ℂ) :
    (Matrix.fromBlocks 0 B Bᴴ 0).permanent =
      (Complex.normSq (B.submatrix id e).permanent : ℂ) := by
  let E : m ⊕ m ≃ m ⊕ n := (Equiv.refl m).sumCongr e
  have h : (Matrix.fromBlocks 0 B Bᴴ 0).submatrix E E =
      Matrix.fromBlocks 0 (B.submatrix id e) (B.submatrix id e)ᴴ 0 := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [← permanent_reindex E, h, permanent_bipartite_normSq]

theorem permanent_bipartite_re_nonneg (B : Matrix n n ℂ) :
    0 ≤ (Matrix.fromBlocks 0 B Bᴴ 0).permanent.re := by
  rw [permanent_bipartite_normSq]
  exact Complex.normSq_nonneg _

omit [DecidableEq m] in
@[simp]
theorem card_repetitionIndex (ν : m → ℕ) :
    Fintype.card (RepetitionIndex ν) = ∑ i, ν i := by
  simp [RepetitionIndex]

/-- Repetition of a bipartite matrix is again bipartite after relabeling. -/
theorem repeated_bipartite_permanent (C : Matrix m n ℂ) (ν : m → ℕ) (μ : n → ℕ) :
    (repeatedMatrix (Matrix.fromBlocks 0 C Cᴴ 0) (Sum.elim ν μ) (Sum.elim ν μ)).permanent =
      (Matrix.fromBlocks 0 (repeatedMatrix C ν μ) (repeatedMatrix C ν μ)ᴴ 0).permanent := by
  let e : RepetitionIndex (Sum.elim ν μ) ≃ RepetitionIndex ν ⊕ RepetitionIndex μ :=
    Equiv.sumSigmaDistrib (fun i => Fin (Sum.elim ν μ i))
  rw [← permanent_reindex e.symm]
  congr 1
  ext i j
  cases i <;> cases j <;> rfl

/-- The repeated bipartite permanent vanishes unless the two total degrees agree. -/
theorem repeated_bipartite_permanent_eq_zero_of_sum_ne (C : Matrix m n ℂ)
    (ν : m → ℕ) (μ : n → ℕ) (h : ∑ i, ν i ≠ ∑ j, μ j) :
    (repeatedMatrix (Matrix.fromBlocks 0 C Cᴴ 0)
      (Sum.elim ν μ) (Sum.elim ν μ)).permanent = 0 := by
  rw [repeated_bipartite_permanent]
  apply permanent_bipartite_eq_zero_of_card_ne
  simpa only [card_repetitionIndex] using h

/-- The elementary positivity used after applying the general MacMahon theorem. -/
theorem repeated_bipartite_permanent_re_nonneg (C : Matrix m n ℂ)
    (ν : m → ℕ) (μ : n → ℕ) :
    0 ≤ (repeatedMatrix (Matrix.fromBlocks 0 C Cᴴ 0)
      (Sum.elim ν μ) (Sum.elim ν μ)).permanent.re := by
  classical
  rw [repeated_bipartite_permanent]
  by_cases hcard : Fintype.card (RepetitionIndex ν) = Fintype.card (RepetitionIndex μ)
  · rw [permanent_bipartite_normSq_of_equiv (Fintype.equivOfCardEq hcard)]
    exact Complex.normSq_nonneg _
  · rw [permanent_bipartite_eq_zero_of_card_ne _ _ hcard]
    simp

end Results.SharpPowersKz
