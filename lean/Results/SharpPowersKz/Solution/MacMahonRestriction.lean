import Results.SharpPowersKz.Solution.MacMahonLift
import Mathlib.Algebra.MvPolynomial.Rename
noncomputable section
open Finset MvPolynomial Matrix
namespace Results.SharpPowersKz.MacMahon
variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma killCompl_X_pred (p : n → Prop) [DecidablePred p] (i : n) :
    (X i : MvPolynomial n ℂ).killCompl (Subtype.val_injective (p := p)) =
      if h : p i then X (⟨i, h⟩ : {i // p i}) else 0 := by
  classical
  rw [killCompl, aeval_X]
  by_cases hi : p i
  · have hr : i ∈ Set.range (Subtype.val : {i // p i} → n) := ⟨⟨i, hi⟩, rfl⟩
    simp only [dif_pos hr, dif_pos hi]
    congr 1
    exact Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, hi⟩
  · have hr : i ∉ Set.range (Subtype.val : {i // p i} → n) := by simpa using hi
    simp [hi]

theorem killCompl_determinantPoly_pred (H : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] :
    (determinantPoly H).killCompl (Subtype.val_injective (p := p)) =
      determinantPoly (H.submatrix (Subtype.val : {i // p i} → n) Subtype.val) := by
  classical
  let K := MvPolynomial.killCompl (R := ℂ) (Subtype.val_injective (p := p))
  let U : Matrix n {i // p i} (MvPolynomial {i // p i} ℂ) := fun i k => if i = k then 1 else 0
  let V : Matrix {i // p i} n (MvPolynomial {i // p i} ℂ) := fun k j => X k * C (H k j)
  have hUV : U * V = diagonal (fun i => K (X i)) * H.map C := by
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul]
    by_cases hi : p i
    · have heq : ∀ k : {i // p i}, (i = (k : n)) ↔ k = ⟨i, hi⟩ := by
        intro k
        simp [Subtype.ext_iff, eq_comm]
      simp [Matrix.mul_apply, U, V, K, killCompl_X_pred, hi, heq]
    · have heq : ∀ k : {i // p i}, i ≠ (k : n) := fun k h => hi (h ▸ k.property)
      simp [Matrix.mul_apply, U, V, K, killCompl_X_pred, hi, heq]
  have hVU : V * U = diagonal X * (H.submatrix (Subtype.val : {i // p i} → n) Subtype.val).map C := by
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply, U, V, Matrix.diagonal_apply, Matrix.submatrix]
  calc
    _ = det (1 - diagonal (fun i => K (X i)) * H.map C) := by
      rw [determinantPoly, AlgHom.map_det]
      congr 1
      apply Matrix.ext
      intro i j
      simp [Matrix.diagonal_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply, K]
    _ = det (1 - U * V) := by rw [hUV]
    _ = det (1 - V * U) := Matrix.det_one_sub_mul_comm U V
    _ = _ := by rw [hVU]; rfl

theorem killCompl_determinantPoly (H : Matrix n n ℂ) (s : Finset n) :
    (determinantPoly H).killCompl (Subtype.val_injective (p := fun i => i ∈ s)) =
      determinantPoly (H.submatrix (Subtype.val : s → n) Subtype.val) :=
  by
    have h := killCompl_determinantPoly_pred H (fun i => i ∈ s)
    have hf : (Subtype.fintype fun i => i ∈ s) = Finset.Subtype.fintype s := Subsingleton.elim _ _
    exact h.trans (congrArg (fun inst : Fintype s =>
      @determinantPoly s inst inferInstance (H.submatrix (Subtype.val : s → n) Subtype.val)) hf)

omit [Fintype n] [DecidableEq n] in
theorem reciprocalCoeff_killCompl {m : Type*} (f : m → n) (hf : Function.Injective f)
    (P : MvPolynomial n ℂ) (d : m →₀ ℕ) :
    reciprocalCoeff (P.killCompl hf) d = reciprocalCoeff P (d.mapDomain f) := by
  classical
  have hd : indexDegree (d.mapDomain f) = indexDegree d := by
    unfold indexDegree
    rw [Finsupp.sum_mapDomain_index] <;> intros <;> rfl
  unfold reciprocalCoeff
  rw [hd]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← coeff_killCompl hf]
  congr 1
  simp

theorem reciprocalCoeff_determinantPoly_restrict (H : Matrix n n ℂ) (s : Finset n) :
    reciprocalCoeff (determinantPoly H) ((squarefreeIndex s).mapDomain Subtype.val) =
      reciprocalCoeff (determinantPoly (H.submatrix (Subtype.val : s → n) Subtype.val))
        (squarefreeIndex s) := by
  rw [← reciprocalCoeff_killCompl Subtype.val Subtype.val_injective,
    killCompl_determinantPoly]

theorem reciprocalCoeff_determinantPoly_restrict_pred (H : Matrix n n ℂ)
    (p : n → Prop) [DecidablePred p] :
    reciprocalCoeff (determinantPoly H) ((squarefreeIndex {i // p i}).mapDomain Subtype.val) =
      reciprocalCoeff (determinantPoly (H.submatrix (Subtype.val : {i // p i} → n) Subtype.val))
        (squarefreeIndex {i // p i}) := by
  rw [← reciprocalCoeff_killCompl Subtype.val Subtype.val_injective,
    killCompl_determinantPoly_pred]

end Results.SharpPowersKz.MacMahon
