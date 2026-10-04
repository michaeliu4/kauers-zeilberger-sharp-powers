import Results.SharpPowersKz.Solution.MacMahon
import Results.SharpPowersKz.Solution.MacMahonCopies
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A coefficient recurrence for the finite MacMahon inverse

The literal cutoff in `MacMahon.reciprocalCoeff` is stable once the cutoff
has reached the requested total degree.  Consequently these coefficients
satisfy the ordinary convolution recurrence for the inverse of a polynomial
with constant coefficient one.  This isolates the algebraic half of a proof
of MacMahon's theorem: a proposed permanent formula only has to satisfy the
same recurrence.
-/

noncomputable section

open Finset
open MvPolynomial
open scoped Matrix

namespace Results.SharpPowersKz.MacMahon

variable {ι A : Type*} [CommRing A]

/-- The polynomial used to compute an inverse through total degree `N`. -/
def inverseTruncation (P : MvPolynomial ι A) (N : ℕ) : MvPolynomial ι A :=
  ∑ j ∈ Finset.range (N + 1), (1 - P) ^ j

theorem coeff_inverseTruncation (P : MvPolynomial ι A) (N : ℕ) (d : ι →₀ ℕ) :
    (inverseTruncation P N).coeff d =
      ∑ j ∈ Finset.range (N + 1), ((1 - P) ^ j).coeff d := by
  simp only [inverseTruncation, MvPolynomial.coeff_sum]

/-- Terms beyond the total degree of a monomial do not affect its coefficient
in the geometric inverse. -/
theorem coeff_inverseTruncation_eq_reciprocalCoeff [DecidableEq ι]
    (P : MvPolynomial ι A) (hP : P.coeff 0 = 1) (d : ι →₀ ℕ) (N : ℕ)
    (hN : indexDegree d ≤ N) :
    (inverseTruncation P N).coeff d = reciprocalCoeff P d := by
  have hm : MinDegree (1 - P) 1 := minDegree_one_of_coeff_zero _ (by simp [hP])
  rw [coeff_inverseTruncation, reciprocalCoeff]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
  intro j hjN hjd
  have hj : indexDegree d < j := by
    simp only [Finset.mem_range, not_lt] at hjd
    omega
  exact (hm.pow j).coeff_eq_zero d (by simpa using hj)

/-- The finite coefficient definition obeys the exact convolution equation
`P * P⁻¹ = 1`.  This is the recurrence needed to characterize the permanent
side of MacMahon's theorem. -/
theorem reciprocalCoeff_convolution [DecidableEq ι]
    (P : MvPolynomial ι A) (hP : P.coeff 0 = 1) (d : ι →₀ ℕ) :
    ∑ de ∈ Finset.antidiagonal d,
        P.coeff de.1 * reciprocalCoeff P de.2 =
      (1 : MvPolynomial ι A).coeff d := by
  let N := indexDegree d
  have hfinite :
      (P * inverseTruncation P N).coeff d = (1 : MvPolynomial ι A).coeff d := by
    simpa only [inverseTruncation] using finite_geometric_inverse_coeff P hP d N le_rfl
  rw [MvPolynomial.coeff_mul] at hfinite
  rw [← hfinite]
  apply Finset.sum_congr rfl
  intro de hde
  congr 1
  symm
  apply coeff_inverseTruncation_eq_reciprocalCoeff P hP
  have hadd : de.1 + de.2 = d := Finset.mem_antidiagonal.mp hde
  have hdegree : indexDegree de.1 + indexDegree de.2 = indexDegree d := by
    rw [← indexDegree_add, hadd]
  omega

/-- For a nonconstant monomial, the convolution recurrence can be solved for
the requested inverse coefficient by removing its constant-factor term. -/
theorem reciprocalCoeff_eq_neg_sum_erase [DecidableEq ι]
    (P : MvPolynomial ι A) (hP : P.coeff 0 = 1) (d : ι →₀ ℕ) (hd : d ≠ 0) :
    reciprocalCoeff P d =
      -∑ de ∈ (Finset.antidiagonal d).erase (0, d),
          P.coeff de.1 * reciprocalCoeff P de.2 := by
  have hconv := reciprocalCoeff_convolution P hP d
  have hzero : (1 : MvPolynomial ι A).coeff d = 0 := by
    rw [MvPolynomial.coeff_one, if_neg (Ne.symm hd)]
  rw [hzero] at hconv
  have hmem : (0, d) ∈ Finset.antidiagonal d := by simp
  rw [← Finset.sum_erase_add _ _ hmem] at hconv
  simp only [hP, one_mul] at hconv
  exact eq_neg_of_add_eq_zero_right hconv

section PrincipalMinorExpansion

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A matrix formed from rows of `B` on `s` and diagonal rows off `s`
has determinant equal to the corresponding principal minor times the omitted
diagonal entries. -/
theorem det_piecewise_diagonal_eq_principalMinor
    (B : Matrix n n R) (z : n → R) (s : Finset n) :
    Matrix.det (Matrix.of <| s.piecewise B.row (Matrix.diagonal z).row) =
      Matrix.det (B.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) *
        ∏ i : {i // i ∉ s}, z i := by
  let e := Equiv.sumCompl (fun i => i ∈ s)
  let A : Matrix n n R := Matrix.of <| s.piecewise B.row (Matrix.diagonal z).row
  rw [← Matrix.det_submatrix_equiv_self e A]
  have hblocks : A.submatrix e e =
      Matrix.fromBlocks
        (B.submatrix (Subtype.val : s → n) (Subtype.val : s → n))
        (B.submatrix (Subtype.val : s → n) (Subtype.val : {i // i ∉ s} → n))
        0 (Matrix.diagonal fun i : {i // i ∉ s} => z i) := by
    ext (i | i) (j | j)
    · simp [A, e, i.prop]
    · simp [A, e, i.prop]
    · have hij : (i : n) ≠ (j : n) := fun h => i.prop (h ▸ j.prop)
      simp [A, e, i.prop, hij]
    · simp [A, e, i.prop, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [hblocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]

/-- Principal-minor expansion obtained by multilinearity in the rows:
`det (B + diag z)` chooses the rows of `B` indexed by `s` and diagonal
rows on its complement. -/
theorem det_add_diagonal_eq_sum_principalMinors
    (B : Matrix n n R) (z : n → R) :
    Matrix.det (B + Matrix.diagonal z) =
      ∑ s : Finset n,
        Matrix.det (B.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) *
          ∏ i : {i // i ∉ s}, z i := by
  let D := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  change D (fun i => (B + Matrix.diagonal z) i) = _
  rw [show (fun i => (B + Matrix.diagonal z) i) =
      (fun i => B i) + (fun i => Matrix.diagonal z i) by rfl]
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  exact det_piecewise_diagonal_eq_principalMinor B z s

end PrincipalMinorExpansion

section ColumnLaplacian

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The linear form given by the `j`th column of `H`. -/
def columnLinearForm (H : Matrix n n R) (Y : n → R) (j : n) : R :=
  ∑ i, Y i * H i j

/-- A weighted column Laplacian.  Every column sums to zero. -/
def columnLaplacian (H : Matrix n n R) (Y : n → R) : Matrix n n R :=
  Matrix.diagonal (columnLinearForm H Y) - Matrix.diagonal Y * H

theorem one_vecMul_columnLaplacian (H : Matrix n n R) (Y : n → R) :
    (1 : n → R) ᵥ* columnLaplacian H Y = 0 := by
  ext j
  simp [Matrix.vecMul_apply_eq_sum, columnLaplacian, columnLinearForm,
    Matrix.diagonal_apply, Matrix.diagonal_mul]

/-- The weighted column Laplacian has zero determinant. -/
theorem det_columnLaplacian [Nonempty n] [IsDomain R]
    (H : Matrix n n R) (Y : n → R) :
    Matrix.det (columnLaplacian H Y) = 0 := by
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨1, one_ne_zero, one_vecMul_columnLaplacian H Y⟩

theorem det_neg_diagonal_mul_submatrix
    (H : Matrix n n R) (Y : n → R) (s : Finset n) :
    Matrix.det
        ((-(Matrix.diagonal Y * H)).submatrix
          (Subtype.val : s → n) (Subtype.val : s → n)) =
      (-1 : R) ^ s.card * (∏ i : s, Y i) *
        Matrix.det (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) := by
  let Hs : Matrix s s R :=
    H.submatrix (Subtype.val : s → n) (Subtype.val : s → n)
  change Matrix.det
      ((-(Matrix.diagonal Y * H)).submatrix
        (Subtype.val : s → n) (Subtype.val : s → n)) =
    (-1 : R) ^ s.card * (∏ i : s, Y i) * Matrix.det Hs
  have hmatrix :
      ((-(Matrix.diagonal Y * H)).submatrix
        (Subtype.val : s → n) (Subtype.val : s → n)) =
        -(Matrix.of fun i j : s => Y i * Hs i j) := by
    ext i j
    simp [Hs, Matrix.diagonal_mul]
  rw [hmatrix, Matrix.det_neg, Fintype.card_coe, Matrix.det_mul_column]
  ring

/-- Expanding the zero determinant of the weighted column Laplacian gives
the determinant side of the squarefree MacMahon recurrence. -/
theorem columnLaplacian_principalMinor_convolution [Nonempty n] [IsDomain R]
    (H : Matrix n n R) (Y : n → R) :
    ∑ s : Finset n,
        (-1 : R) ^ s.card * (∏ i : s, Y i) *
          Matrix.det (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) *
          (∏ j : {j // j ∉ s}, columnLinearForm H Y j) = 0 := by
  have hexpand := det_add_diagonal_eq_sum_principalMinors
    (B := -(Matrix.diagonal Y * H)) (columnLinearForm H Y)
  have hlap : -(Matrix.diagonal Y * H) + Matrix.diagonal (columnLinearForm H Y) =
      columnLaplacian H Y := by
    simp only [columnLaplacian]
    abel
  rw [hlap, det_columnLaplacian] at hexpand
  calc
    _ = ∑ s : Finset n,
        Matrix.det ((-(Matrix.diagonal Y * H)).submatrix
          (Subtype.val : s → n) (Subtype.val : s → n)) *
          (∏ j : {j // j ∉ s}, columnLinearForm H Y j) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [det_neg_diagonal_mul_submatrix]
    _ = 0 := hexpand.symm

end ColumnLaplacian

section DeterminantPolynomialExpansion

/-- The multivariate determinant in MacMahon's theorem is the signed
principal-minor polynomial. -/
theorem determinantPoly_eq_sum_principalMinors
    {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) :
    determinantPoly H =
      ∑ s : Finset n,
        MvPolynomial.C
            ((-1 : ℂ) ^ s.card *
              Matrix.det (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n))) *
          ∏ i : s, MvPolynomial.X (i : n) := by
  unfold determinantPoly
  have hmatrix :
      (1 - Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C) =
        -(Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C) +
          Matrix.diagonal (1 : n → MvPolynomial n ℂ) := by
    have hd : Matrix.diagonal (1 : n → MvPolynomial n ℂ) = 1 := by
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [hd]
    abel
  rw [hmatrix, det_add_diagonal_eq_sum_principalMinors]
  apply Finset.sum_congr rfl
  intro s _
  rw [det_neg_diagonal_mul_submatrix]
  simp only [Pi.one_apply, Finset.prod_const_one, map_pow, map_mul, map_neg, map_one]
  let Cn : ℂ →+* MvPolynomial n ℂ := MvPolynomial.C
  have hmap :
      Matrix.det
          ((H.map Cn).submatrix
            (Subtype.val : s → n) (Subtype.val : s → n)) =
        Cn
          (Matrix.det
            (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n))) := by
    calc
      _ = Matrix.det
          ((H.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).map Cn) := by
            congr 1
      _ = _ := (RingHom.map_det Cn _).symm
  rw [hmap]
  ring

end DeterminantPolynomialExpansion

section SquarefreeInverseRecurrence

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem mapDomain_squarefreeIndex_subtype_apply
    (s : Finset n) (i : n) :
    ((squarefreeIndex s).mapDomain (Subtype.val : s → n)) i =
      if i ∈ s then 1 else 0 := by
  classical
  by_cases hi : i ∈ s
  · let a : s := ⟨i, hi⟩
    change ((squarefreeIndex s).mapDomain (Subtype.val : s → n)) (Subtype.val a) = _
    rw [Finsupp.mapDomain_apply Subtype.val_injective]
    simp [hi, a]
  · let e : s ↪ n := ⟨Subtype.val, Subtype.val_injective⟩
    have hnot : i ∉ (((squarefreeIndex s).mapDomain e).support) := by
      rw [Finsupp.support_mapDomain_embedding e]
      simp [squarefreeIndex, hi, e]
    change i ∉ (((squarefreeIndex s).mapDomain (Subtype.val : s → n)).support) at hnot
    rw [Finsupp.notMem_support_iff.mp hnot, if_neg hi]

private theorem mapDomain_squarefreeIndex_compl_apply
    (s : Finset n) (i : n) :
    ((squarefreeIndex {j // j ∉ s}).mapDomain
      (Subtype.val : {j // j ∉ s} → n)) i =
      if i ∉ s then 1 else 0 := by
  classical
  by_cases hi : i ∉ s
  · let a : {j // j ∉ s} := ⟨i, hi⟩
    change ((squarefreeIndex {j // j ∉ s}).mapDomain
      (Subtype.val : {j // j ∉ s} → n)) (Subtype.val a) = _
    rw [Finsupp.mapDomain_apply Subtype.val_injective]
    simp [hi, a]
  · let e : {j // j ∉ s} ↪ n := ⟨Subtype.val, Subtype.val_injective⟩
    have hnot : i ∉ (((squarefreeIndex {j // j ∉ s}).mapDomain e).support) := by
      rw [Finsupp.support_mapDomain_embedding e]
      simp [squarefreeIndex, hi, e]
    change i ∉ (((squarefreeIndex {j // j ∉ s}).mapDomain
      (Subtype.val : {j // j ∉ s} → n)).support) at hnot
    rw [Finsupp.notMem_support_iff.mp hnot, if_neg hi]

private theorem mapDomain_squarefreeIndex_add_compl (s : Finset n) :
    (squarefreeIndex s).mapDomain (Subtype.val : s → n) +
      (squarefreeIndex {j // j ∉ s}).mapDomain
        (Subtype.val : {j // j ∉ s} → n) = squarefreeIndex n := by
  ext i
  by_cases hi : i ∈ s
  · rw [Finsupp.add_apply,
      mapDomain_squarefreeIndex_subtype_apply s i,
      mapDomain_squarefreeIndex_compl_apply s i]
    simp [hi]
  · rw [Finsupp.add_apply,
      mapDomain_squarefreeIndex_subtype_apply s i,
      mapDomain_squarefreeIndex_compl_apply s i]
    simp [hi]

omit [Fintype n] in
private theorem prod_X_subtype_eq_monomial_mapDomain (s : Finset n) :
    (∏ i : s, (MvPolynomial.X (i : n) : MvPolynomial n ℂ)) =
      MvPolynomial.monomial
        ((squarefreeIndex s).mapDomain (Subtype.val : s → n)) 1 := by
  classical
  have hidx :
      (squarefreeIndex s).mapDomain (Subtype.val : s → n) =
        Finsupp.indicator s (fun _ _ => 1) := by
    ext i
    rw [mapDomain_squarefreeIndex_subtype_apply]
    simp only [Finsupp.indicator_apply]
    split <;> rfl
  calc
    _ = ∏ i ∈ s, (MvPolynomial.X i : MvPolynomial n ℂ) :=
      (Finset.prod_subtype s (fun _ => Iff.rfl) fun i =>
        (MvPolynomial.X i : MvPolynomial n ℂ)).symm
    _ = ∏ i ∈ s, (MvPolynomial.X i : MvPolynomial n ℂ) ^ (1 : ℕ) := by simp
    _ = MvPolynomial.monomial (Finsupp.indicator s (fun _ _ => 1)) 1 :=
      MvPolynomial.prod_X_pow (fun _ => 1) s
    _ = _ := by rw [hidx]

/-- The squarefree coefficient of the determinant inverse satisfies the
principal-minor convolution.  The complementary exponent is stated using
only `squarefreeIndex` and `mapDomain`, so it can be consumed independently
of any particular finite-set encoding. -/
theorem squarefree_reciprocalCoeff_principalMinor_recurrence
    (H : Matrix n n ℂ) :
    ∑ s : Finset n,
        (-1 : ℂ) ^ s.card *
          Matrix.det (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) *
          reciprocalCoeff (determinantPoly H)
            ((squarefreeIndex {j // j ∉ s}).mapDomain
              (Subtype.val : {j // j ∉ s} → n)) =
      (1 : MvPolynomial n ℂ).coeff (squarefreeIndex n) := by
  let P := determinantPoly H
  let N := Fintype.card n
  let G := inverseTruncation P N
  have hP : P.coeff 0 = 1 := determinantPoly_coeff_zero H
  have hfinite : (P * G).coeff (squarefreeIndex n) =
      (1 : MvPolynomial n ℂ).coeff (squarefreeIndex n) := by
    apply finite_geometric_inverse_coeff P hP
    simp [N]
  rw [show P = determinantPoly H by rfl, determinantPoly_eq_sum_principalMinors,
    Finset.sum_mul, MvPolynomial.coeff_sum] at hfinite
  rw [← hfinite]
  apply Finset.sum_congr rfl
  intro s _
  let is := (squarefreeIndex s).mapDomain (Subtype.val : s → n)
  let ic := (squarefreeIndex {j // j ∉ s}).mapDomain
    (Subtype.val : {j // j ∉ s} → n)
  have hadd : is + ic = squarefreeIndex n := mapDomain_squarefreeIndex_add_compl s
  have hicDegree : indexDegree ic ≤ N := by
    have hdegree : indexDegree is + indexDegree ic = Fintype.card n := by
      rw [← indexDegree_add, hadd, indexDegree_squarefreeIndex]
    omega
  have hstable : G.coeff ic = reciprocalCoeff P ic := by
    exact coeff_inverseTruncation_eq_reciprocalCoeff P hP ic N hicDegree
  rw [prod_X_subtype_eq_monomial_mapDomain]
  change
    (-1 : ℂ) ^ s.card *
          Matrix.det (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n)) *
          reciprocalCoeff P ic =
      ((MvPolynomial.C
          ((-1 : ℂ) ^ s.card *
            Matrix.det (H.submatrix (Subtype.val : s → n) (Subtype.val : s → n))) *
          MvPolynomial.monomial is 1) * G).coeff (squarefreeIndex n)
  rw [MvPolynomial.C_mul_monomial, mul_one, ← hadd,
    MvPolynomial.coeff_monomial_mul, hstable]

end SquarefreeInverseRecurrence

end Results.SharpPowersKz.MacMahon
