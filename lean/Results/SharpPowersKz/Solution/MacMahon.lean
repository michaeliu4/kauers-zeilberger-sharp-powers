import Results.SharpPowersKz.MacMahonDefs
import Results.SharpPowersKz.Solution.Algebra
import Results.SharpPowersKz.Solution.Permanent
import Results.SharpPowersKz.Solution.Schur
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open scoped Matrix
open Finset
namespace Results.SharpPowersKz.MacMahon

variable {ι A : Type*} [CommRing A]

@[simp] theorem indexDegree_zero : indexDegree (0 : ι →₀ ℕ) = 0 := by simp [indexDegree]

theorem indexDegree_add (d e : ι →₀ ℕ) :
    indexDegree (d + e) = indexDegree d + indexDegree e :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Exact homogeneous degree, expressed directly in monomial support. -/
def FixedDegree (p : MvPolynomial ι A) (n : ℕ) : Prop :=
  ∀ d ∈ p.support, indexDegree d = n

/-- A lower bound on degrees of all supported monomials. -/
def MinDegree (p : MvPolynomial ι A) (n : ℕ) : Prop :=
  ∀ d ∈ p.support, n ≤ indexDegree d

theorem MinDegree.zero (p : MvPolynomial ι A) : MinDegree p 0 := fun _ _ => Nat.zero_le _

theorem MinDegree.mono {p : MvPolynomial ι A} {m n : ℕ}
    (hp : MinDegree p n) (h : m ≤ n) : MinDegree p m :=
  fun d hd => h.trans (hp d hd)

theorem FixedDegree.minDegree {p : MvPolynomial ι A} {n : ℕ}
    (hp : FixedDegree p n) : MinDegree p n := fun d hd => (hp d hd).ge

theorem MinDegree.coeff_eq_zero {p : MvPolynomial ι A} {n : ℕ}
    (hp : MinDegree p n) (d : ι →₀ ℕ) (hd : indexDegree d < n) : p.coeff d = 0 := by
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  exact (Nat.not_le_of_gt hd) (hp d hmem)

theorem FixedDegree.coeff_eq_zero {p : MvPolynomial ι A} {n : ℕ}
    (hp : FixedDegree p n) (d : ι →₀ ℕ) (hd : indexDegree d ≠ n) : p.coeff d = 0 := by
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  exact hd (hp d hmem)

theorem FixedDegree.one [Nontrivial A] : FixedDegree (1 : MvPolynomial ι A) 0 := by
  intro d hd
  have hd0 : d = 0 := by simpa only [MvPolynomial.support_one, Finset.mem_singleton] using hd
  subst d
  exact indexDegree_zero

theorem FixedDegree.add {p q : MvPolynomial ι A} {n : ℕ}
    (hp : FixedDegree p n) (hq : FixedDegree q n) : FixedDegree (p + q) n := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem FixedDegree.C (a : A) : FixedDegree (MvPolynomial.C a : MvPolynomial ι A) 0 := by
  intro d hd
  have hc := MvPolynomial.mem_support_iff.mp hd
  by_cases hd0 : d = 0
  · subst d; exact indexDegree_zero
  · exact (hc (MvPolynomial.coeff_C_of_ne_zero hd0 a)).elim

theorem FixedDegree.X [Nontrivial A] (i : ι) :
    FixedDegree (MvPolynomial.X i : MvPolynomial ι A) 1 := by
  intro d hd
  have hd0 : d = Finsupp.single i 1 := by
    simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hd
  subst d
  simp [indexDegree]

theorem FixedDegree.sub {p q : MvPolynomial ι A} {n : ℕ}
    (hp : FixedDegree p n) (hq : FixedDegree q n) : FixedDegree (p - q) n := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_sub ι p q hd) with h | h
  · exact hp d h
  · exact hq d h

theorem FixedDegree.mul {p q : MvPolynomial ι A} {m n : ℕ}
    (hp : FixedDegree p m) (hq : FixedDegree q n) : FixedDegree (p * q) (m + n) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [indexDegree_add, hp a ha, hq b hb]

theorem MinDegree.sub {p q : MvPolynomial ι A} {n : ℕ}
    (hp : MinDegree p n) (hq : MinDegree q n) : MinDegree (p - q) n := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_sub ι p q hd) with h | h
  · exact hp d h
  · exact hq d h

theorem MinDegree.add {p q : MvPolynomial ι A} {n : ℕ}
    (hp : MinDegree p n) (hq : MinDegree q n) : MinDegree (p + q) n := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem MinDegree.mul {p q : MvPolynomial ι A} {m n : ℕ}
    (hp : MinDegree p m) (hq : MinDegree q n) : MinDegree (p * q) (m + n) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [indexDegree_add]
  exact Nat.add_le_add (hp a ha) (hq b hb)

theorem MinDegree.neg {p : MvPolynomial ι A} {n : ℕ}
    (hp : MinDegree p n) : MinDegree (-p) n := by
  intro d hd
  exact hp d (by simpa using hd)

theorem MinDegree.pow {p : MvPolynomial ι A} {n : ℕ}
    (hp : MinDegree p n) (k : ℕ) : MinDegree (p ^ k) (n * k) := by
  induction k with
  | zero => simpa using MinDegree.zero (1 : MvPolynomial ι A)
  | succ k ih => simpa [pow_succ, Nat.mul_succ] using ih.mul hp

theorem complete_fixedDegree [Nontrivial A] {L R : MvPolynomial ι A}
    (hL : FixedDegree L 2) (hR : FixedDegree R 4) (k : ℕ) :
    FixedDegree (Schur.complete L R k) (2 * k) := by
  induction k using Nat.twoStepInduction with
  | zero => simpa using (FixedDegree.one : FixedDegree (1 : MvPolynomial ι A) 0)
  | one => simpa using hL
  | more k ih₀ ih₁ =>
    rw [Schur.complete_add_two]
    apply FixedDegree.sub
    · convert hL.mul ih₁ using 1; omega
    · convert hR.mul ih₀ using 1; omega

def partialComplete (L R : A) (k : ℕ) : A :=
  ∑ j ∈ Finset.range (k + 1), Schur.complete L R j

theorem partialComplete_identity (L R : A) (k : ℕ) :
    (1 - L + R) * partialComplete L R k =
      1 - Schur.complete L R (k + 1) + R * Schur.complete L R k := by
  induction k with
  | zero => simp [partialComplete]
  | succ k ih =>
    have hs : partialComplete L R (k + 1) =
        partialComplete L R k + Schur.complete L R (k + 1) := by
      simp only [partialComplete, Finset.sum_range_succ]
    rw [hs, mul_add, ih]
    rw [show k + 1 + 1 = k + 2 by omega, Schur.complete_add_two]
    ring

theorem geometric_identity (z : A) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), z ^ j) * (1 - z) = 1 - z ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

/-- The complete recurrence gives exactly the even homogeneous pieces of
    the finite geometric inverse; this is an algebraic theorem, not an assumption. -/
theorem complete_coeff_eq_reciprocalCoeff [Nontrivial A] {L R : MvPolynomial ι A}
    (hL : FixedDegree L 2) (hR : FixedDegree R 4) (k : ℕ) (d : ι →₀ ℕ)
    (hd : indexDegree d = 2 * k) :
    (Schur.complete L R k).coeff d = reciprocalCoeff (1 - L + R) d := by
  classical
  let S := partialComplete L R k
  let G := ∑ j ∈ Finset.range (2 * k + 1), (L - R) ^ j
  have hG : G * (1 - L + R) = 1 - (L - R) ^ (2 * k + 1) := by
    simpa only [show 1 - L + R = 1 - (L - R) by ring] using
      geometric_identity (L - R) (2 * k)
  have hS : (1 - L + R) * S =
      1 - Schur.complete L R (k + 1) + R * Schur.complete L R k :=
    partialComplete_identity L R k
  have hdiff : S - G = -G * Schur.complete L R (k + 1) +
      (G * R) * Schur.complete L R k + (L - R) ^ (2 * k + 1) * S := by
    calc
      S - G = (G * (1 - L + R) + (L - R) ^ (2 * k + 1)) * S - G := by
        rw [hG]; ring
      _ = G * ((1 - L + R) * S) + (L - R) ^ (2 * k + 1) * S - G := by ring
      _ = _ := by rw [hS]; ring
  have hmin : MinDegree (S - G) (2 * k + 1) := by
    rw [hdiff]
    apply MinDegree.add
    · apply MinDegree.add
      · exact ((MinDegree.zero (-G)).mul
          (complete_fixedDegree hL hR (k + 1)).minDegree).mono (by omega)
      · exact (((MinDegree.zero G).mul hR.minDegree).mul
          (complete_fixedDegree hL hR k).minDegree).mono (by omega)
    · exact ((hL.minDegree.sub (hR.minDegree.mono (by omega))).pow (2 * k + 1)
        |>.mul (MinDegree.zero S)).mono (by omega)
  have heq : S.coeff d = G.coeff d := by
    have hz := hmin.coeff_eq_zero d (by omega)
    simpa only [MvPolynomial.coeff_sub, sub_eq_zero] using hz
  have hSc : S.coeff d = (Schur.complete L R k).coeff d := by
    simp only [S, partialComplete, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_single k
    · intro j hj hjk
      exact (complete_fixedDegree hL hR j).coeff_eq_zero d (by omega)
    · simp
  rw [hSc] at heq
  simpa only [reciprocalCoeff, hd, show 1 - (1 - L + R) = L - R by ring,
    G, MvPolynomial.coeff_sum] using heq


/-- Six-variable homogeneous linear coefficient in the rank-two determinant. -/
def dilationLPoly : MvPolynomial (Fin 3 ⊕ Fin 3) A :=
  let x := MvPolynomial.X (Sum.inl (0 : Fin 3))
  let y := MvPolynomial.X (Sum.inl (1 : Fin 3))
  let ξ := MvPolynomial.X (Sum.inl (2 : Fin 3))
  let z := MvPolynomial.X (Sum.inr (0 : Fin 3))
  let w := MvPolynomial.X (Sum.inr (1 : Fin 3))
  let η := MvPolynomial.X (Sum.inr (2 : Fin 3))
  (x + y) * (z + w) + η * (x + y) + ξ * (z + w)

/-- Six-variable homogeneous quadratic coefficient in the rank-two determinant. -/
def dilationRPoly : MvPolynomial (Fin 3 ⊕ Fin 3) A :=
  let x := MvPolynomial.X (Sum.inl (0 : Fin 3))
  let y := MvPolynomial.X (Sum.inl (1 : Fin 3))
  let ξ := MvPolynomial.X (Sum.inl (2 : Fin 3))
  let z := MvPolynomial.X (Sum.inr (0 : Fin 3))
  let w := MvPolynomial.X (Sum.inr (1 : Fin 3))
  let η := MvPolynomial.X (Sum.inr (2 : Fin 3))
  (2 * x * y + ξ * (x + y)) * (2 * z * w + η * (z + w))

theorem dilationLPoly_fixedDegree [Nontrivial A] :
    FixedDegree (dilationLPoly (A := A)) 2 := by
  dsimp only [dilationLPoly]
  exact (((FixedDegree.X _).add (FixedDegree.X _)).mul
    ((FixedDegree.X _).add (FixedDegree.X _))).add
    ((FixedDegree.X _).mul ((FixedDegree.X _).add (FixedDegree.X _))) |>.add
    ((FixedDegree.X _).mul ((FixedDegree.X _).add (FixedDegree.X _)))

theorem dilationRPoly_fixedDegree [Nontrivial A] :
    FixedDegree (dilationRPoly (A := A)) 4 := by
  have htwo : FixedDegree (2 : MvPolynomial (Fin 3 ⊕ Fin 3) A) 0 := by
    simpa only [map_ofNat] using (FixedDegree.C (ι := Fin 3 ⊕ Fin 3) (2 : A))
  dsimp only [dilationRPoly]
  exact (((htwo.mul (FixedDegree.X _)).mul (FixedDegree.X _)).add
    ((FixedDegree.X _).mul ((FixedDegree.X _).add (FixedDegree.X _)))).mul
    (((htwo.mul (FixedDegree.X _)).mul (FixedDegree.X _)).add
    ((FixedDegree.X _).mul ((FixedDegree.X _).add (FixedDegree.X _))))

theorem complete_coeff_re_nonneg_of_reciprocalCoeff {L R : MvPolynomial ι ℂ}
    (hL : FixedDegree L 2) (hR : FixedDegree R 4)
    (hpos : ∀ d, 0 ≤ (reciprocalCoeff (1 - L + R) d).re) (k : ℕ) (d : ι →₀ ℕ) :
    0 ≤ ((Schur.complete L R k).coeff d).re := by
  by_cases hd : indexDegree d = 2 * k
  · rw [complete_coeff_eq_reciprocalCoeff hL hR k d hd]
    exact hpos d
  · rw [(complete_fixedDegree hL hR k).coeff_eq_zero d hd]
    simp

/-- Positivity of the general bipartite inverse coefficients follows from
    the named published theorem and the proved permanent-square algebra. -/
theorem bipartite_reciprocalCoeff_re_nonneg (hMMT : MacMahonMasterTheorem)
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (C : Matrix m n ℂ) (d : (m ⊕ n) →₀ ℕ) :
    0 ≤ (reciprocalCoeff (determinantPoly (Matrix.fromBlocks 0 C Cᴴ 0)) d).re := by
  rw [hMMT]
  have heq : (d : (m ⊕ n) → ℕ) =
      Sum.elim (fun i => d (Sum.inl i)) (fun j => d (Sum.inr j)) := by
    funext i
    cases i <;> rfl
  have hper : 0 ≤ (repeatedMatrix (Matrix.fromBlocks 0 C Cᴴ 0) d d).permanent.re := by
    rw [heq]
    exact repeated_bipartite_permanent_re_nonneg _ _ _
  simpa only [Complex.div_natCast_re] using
    div_nonneg hper (Nat.cast_nonneg (∏ i, (d i).factorial))


/-- Elementary block elimination; no invertibility hypothesis is needed. -/
theorem det_bipartite_block {A m n : Type*} [CommRing A]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (B : Matrix m n A) (D : Matrix n m A) :
    (Matrix.fromBlocks 1 (-B) (-D) 1).det = (1 - B * D).det := by
  have h : Matrix.fromBlocks 1 (-B) (-D) 1 * Matrix.fromBlocks 1 0 D 1 =
      Matrix.fromBlocks (1 - B * D) (-B) 0 1 := by
    simp [Matrix.fromBlocks_multiply, Matrix.neg_mul, sub_eq_add_neg]
  simpa only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, one_mul] using
    congrArg Matrix.det h

theorem determinantPoly_bipartite {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) :
    determinantPoly (Matrix.fromBlocks 0 C Cᴴ 0) =
      Matrix.det (1 - Matrix.diagonal (fun i => MvPolynomial.X (Sum.inl i)) *
        C.map MvPolynomial.C * Matrix.diagonal (fun j => MvPolynomial.X (Sum.inr j)) *
        Cᴴ.map MvPolynomial.C) := by
  have hb : (1 - Matrix.diagonal MvPolynomial.X *
      (Matrix.fromBlocks 0 C Cᴴ 0).map MvPolynomial.C) =
      Matrix.fromBlocks 1
        (-(Matrix.diagonal (fun i => MvPolynomial.X (Sum.inl i)) * C.map MvPolynomial.C))
        (-(Matrix.diagonal (fun j => MvPolynomial.X (Sum.inr j)) * Cᴴ.map MvPolynomial.C)) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
        Matrix.map_apply, Matrix.fromBlocks, Matrix.neg_apply]
  unfold determinantPoly
  rw [hb, det_bipartite_block]
  simp only [Matrix.mul_assoc]

theorem dilation_determinantPoly :
    determinantPoly (Matrix.fromBlocks 0 Algebra.dilationC Algebra.dilationCᴴ 0) =
      1 - dilationLPoly + dilationRPoly := by
  rw [determinantPoly_bipartite, Matrix.det_fin_three]
  simp [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.diagonal, Matrix.map_apply, Algebra.dilationC, Matrix.conjTranspose_apply,
    Complex.conj_I, dilationLPoly, dilationRPoly]
  have hI : (MvPolynomial.C Complex.I : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hI4 : (MvPolynomial.C Complex.I : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) ^ 4 = 1 := by
    calc
      _ = ((MvPolynomial.C Complex.I : MvPolynomial (Fin 3 ⊕ Fin 3) ℂ) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hI]; ring
  ring_nf
  rw [hI, hI4]
  ring

/-- Every coefficient of the actual rank-two dilation H_k has nonnegative
    real part, assuming only the generic published MacMahon theorem. -/
theorem dilation_complete_coeff_re_nonneg (hMMT : MacMahonMasterTheorem)
    (k : ℕ) (d : (Fin 3 ⊕ Fin 3) →₀ ℕ) :
    0 ≤ ((Schur.complete (dilationLPoly (A := ℂ)) dilationRPoly k).coeff d).re := by
  apply complete_coeff_re_nonneg_of_reciprocalCoeff
    dilationLPoly_fixedDegree dilationRPoly_fixedDegree
  intro e
  rw [← dilation_determinantPoly]
  exact bipartite_reciprocalCoeff_re_nonneg hMMT Algebra.dilationC e



theorem indexDegree_eq_zero_iff (d : ι →₀ ℕ) : indexDegree d = 0 ↔ d = 0 := by
  classical
  constructor
  · intro hd
    apply Finsupp.ext
    intro i
    change d i = 0
    by_cases hi : i ∈ d.support
    · exact (Finset.sum_eq_zero_iff.mp hd) i hi
    · exact Finsupp.notMem_support_iff.mp hi
  · rintro rfl; simp

theorem minDegree_one_of_coeff_zero (p : MvPolynomial ι A) (hp : p.coeff 0 = 0) :
    MinDegree p 1 := by
  intro d hd
  apply Nat.one_le_iff_ne_zero.mpr
  intro hz
  have hd0 := (indexDegree_eq_zero_iff d).mp hz
  rw [hd0] at hd
  exact (MvPolynomial.mem_support_iff.mp hd) hp

/-- The cutoff defining reciprocalCoeff really is a finite inverse to every
    requested monomial degree. This justifies the formal-inverse interpretation. -/
theorem finite_geometric_inverse_coeff (P : MvPolynomial ι A) (hP : P.coeff 0 = 1)
    (d : ι →₀ ℕ) (N : ℕ) (hN : indexDegree d ≤ N) :
    (P * ∑ j ∈ Finset.range (N + 1), (1 - P) ^ j).coeff d =
      (1 : MvPolynomial ι A).coeff d := by
  have hm : MinDegree (1 - P) 1 := minDegree_one_of_coeff_zero _ (by simp [hP])
  have hz : ((1 - P) ^ (N + 1)).coeff d = 0 :=
    (hm.pow (N + 1)).coeff_eq_zero d (by omega)
  have hg : P * (∑ j ∈ Finset.range (N + 1), (1 - P) ^ j) =
      1 - (1 - P) ^ (N + 1) := by
    simpa only [sub_sub_cancel, mul_comm P] using geometric_identity (1 - P) N
  rw [hg, MvPolynomial.coeff_sub, hz, sub_zero]

theorem determinantPoly_coeff_zero {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) : (determinantPoly H).coeff 0 = 1 := by
  change MvPolynomial.constantCoeff (determinantPoly H) = 1
  unfold determinantPoly
  rw [RingHom.map_det]
  have hm : (1 - Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C).map
      MvPolynomial.constantCoeff = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.diagonal_mul, h]
  change ((1 - Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C).map
    MvPolynomial.constantCoeff).det = 1
  rw [hm, Matrix.det_one]

theorem permanent_rowScale {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n A) (r : n → A) :
    Matrix.permanent (fun i j => r i * H i j : Matrix n n A) =
      (∏ i, r i) * H.permanent := by
  classical
  simp only [Matrix.permanent, Finset.prod_mul_distrib]
  have he (σ : Equiv.Perm n) : (∏ i, r (σ i)) = ∏ i, r i := Equiv.prod_comp σ r
  simp_rw [he]
  rw [Finset.mul_sum]

theorem repeated_rowScale_permanent {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n A) (r : n → A) (d : n → ℕ) :
    (repeatedMatrix (fun i j => r i * H i j) d d).permanent =
      (∏ i, r i ^ d i) * (repeatedMatrix H d d).permanent := by
  change Matrix.permanent (fun i j => r i.1 * repeatedMatrix H d d i j :
    Matrix (RepetitionIndex d) (RepetitionIndex d) A) = _
  rw [permanent_rowScale]
  congr 1
  simp [RepetitionIndex, Fintype.prod_sigma]

/-- Factoring the row variables from the labeled permanent is the exact
    specialization that turns Tuite's matrix identity into our coefficient form. -/
theorem repeated_diagonal_variables_permanent {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (d : n →₀ ℕ) :
    (repeatedMatrix (Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C) d d).permanent =
      MvPolynomial.monomial d (repeatedMatrix H d d).permanent := by
  classical
  have hdiag : Matrix.diagonal MvPolynomial.X * H.map MvPolynomial.C =
      Matrix.of (fun i j => (MvPolynomial.X i : MvPolynomial n ℂ) * MvPolynomial.C (H i j)) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.diagonal_mul]
    rfl
  have hp : (∏ i, (MvPolynomial.X i : MvPolynomial n ℂ) ^ d i) =
      MvPolynomial.monomial d 1 := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  have hm : (repeatedMatrix (H.map MvPolynomial.C) d d).permanent =
      (MvPolynomial.C (repeatedMatrix H d d).permanent : MvPolynomial n ℂ) := by
    simp only [Matrix.permanent, repeatedMatrix, Matrix.submatrix_apply, Matrix.map_apply, map_sum, map_prod]
  calc
    _ = (∏ i, (MvPolynomial.X i : MvPolynomial n ℂ) ^ d i) *
        (repeatedMatrix (H.map MvPolynomial.C) d d).permanent := by
      rw [hdiag]
      exact repeated_rowScale_permanent (H.map MvPolynomial.C)
        (fun i => (MvPolynomial.X i : MvPolynomial n ℂ)) d
    _ = _ := by
      rw [hp, hm]
      rw [MvPolynomial.C_apply, MvPolynomial.monomial_mul, add_zero, one_mul]

end Results.SharpPowersKz.MacMahon
