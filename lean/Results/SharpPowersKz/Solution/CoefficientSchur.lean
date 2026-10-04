import Results.SharpPowersKz.Solution.WeightedSchur
import Results.SharpPowersKz.Solution.Truncation
import Mathlib.Algebra.Polynomial.Eval.Degree

noncomputable section

namespace Results.SharpPowersKz.CoefficientSchur

open WeightedSchur

variable {A : Type*} [CommRing A] [Algebra ℚ A]

abbrev FourPoly (A : Type*) [CommRing A] := MvPolynomial (Fin 4) A

def raw (L D : FourPoly A) : Polynomial (FourPoly A) :=
  Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2

omit [Algebra ℚ A] in
theorem coeff_mul_pow_zero (L D : FourPoly A) (hL : L.coeff 0 = 0) (hD : D.coeff 0 = 0)
    (a b : ℕ) (d : MultiIndex) (hd : degree d < a + b) :
    (L ^ a * D ^ b).coeff d = 0 := by
  classical
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    Finset.mem_add.mp (MvPolynomial.support_mul (L ^ a) (D ^ b) hmem)
  have hu' := le_degree_of_mem_pow_support L hL a u hu
  have hv' := le_degree_of_mem_pow_support D hD b v hv
  rw [degree_add] at hd
  omega

omit [Algebra ℚ A] in
theorem raw_pow_coeff (L D : FourPoly A) (k n : ℕ) :
    ((raw L D) ^ k).coeff n =
      if k ≤ n then (k.choose (n - k) : FourPoly A) *
        L ^ (k - (n - k)) * (-D) ^ (n - k) else 0 := by
  have he : (raw L D) ^ k =
      Polynomial.X ^ k * (Polynomial.C L + Polynomial.C (-D) * Polynomial.X) ^ k := by
    rw [← mul_pow]
    congr 1
    simp only [raw, map_neg]
    ring
  rw [he, Polynomial.coeff_X_pow_mul', linearPower_coeff]

omit [Algebra ℚ A] in
theorem raw_pow_coeff_coeff_zero (L D : FourPoly A) (hL : L.coeff 0 = 0)
    (hD : D.coeff 0 = 0) (k n : ℕ) (d : MultiIndex) (hd : degree d < k) :
    (((raw L D) ^ k).coeff n).coeff d = 0 := by
  rw [raw_pow_coeff]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    by_cases hnk : n - k ≤ k
    · have he : (k.choose (n - k) : FourPoly A) * L ^ (k - (n - k)) * (-D) ^ (n - k) =
          MvPolynomial.C ((k.choose (n - k) : A) * (-1 : A) ^ (n - k)) *
            (L ^ (k - (n - k)) * D ^ (n - k)) := by
        rw [neg_pow]
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
        ring
      rw [he, MvPolynomial.coeff_C_mul,
        coeff_mul_pow_zero L D hL hD _ _ d (by omega), mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · rw [if_neg hkn]
    simp

omit [Algebra ℚ A] in
theorem raw_natDegree_le (L D : FourPoly A) : (raw L D).natDegree ≤ 2 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simpa using (Polynomial.natDegree_C_mul_X_pow_le L 1).trans (by omega)
  · exact Polynomial.natDegree_C_mul_X_pow_le D 2

omit [Algebra ℚ A] in
theorem raw_pow_sum_coeff (L D : FourPoly A) (k M : ℕ) (hk : k ≤ M) :
    (∑ n ∈ Finset.range (2 * M + 1), ((raw L D) ^ k).coeff n) = (L - D) ^ k := by
  have hdeg : ((raw L D) ^ k).natDegree < 2 * M + 1 := by
    have h := Polynomial.natDegree_pow_le_of_le k (raw_natDegree_le L D)
    omega
  have h := Polynomial.eval_eq_sum_range' hdeg (1 : FourPoly A)
  simpa [raw] using h.symm

theorem schurDegree_coeff_eq_sum (b : A) (L D : FourPoly A) (n M : ℕ)
    (hn : n ≤ M) (d : MultiIndex) :
    (schurDegree (MvPolynomial.C b) L D n).coeff d =
      ∑ k ∈ Finset.range (M + 1),
        binomialWeight b k * (((raw L D) ^ k).coeff n).coeff d := by
  have h := congrArg (fun p : FourPoly A => p.coeff d)
    (finite_binomial_schur (MvPolynomial.C b) L D n).symm
  simp only [MvPolynomial.coeff_sum, ← map_binomialWeight MvPolynomial.C,
    MvPolynomial.coeff_C_mul] at h
  rw [h]
  change (∑ k ∈ Finset.range (n + 1),
      binomialWeight b k * (((raw L D) ^ k).coeff n).coeff d) = _
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
  intro k hk hnot
  have hnk : n < k := by simp only [Finset.mem_range] at hnot; omega
  rw [raw_pow_coeff, if_neg (by omega)]
  simp

/-- Coarse local finiteness uses only that both L and D have zero constant
coefficient. Weighted degrees through `2*M` suffice for monomials of degree M. -/
theorem coefficient_schur (b : A) (L D : FourPoly A) (hL : L.coeff 0 = 0)
    (hD : D.coeff 0 = 0) (d : MultiIndex) (M : ℕ) (hM : degree d ≤ M) :
    (∑ k ∈ Finset.range (M + 1), binomialWeight b k * ((L - D) ^ k).coeff d) =
      ∑ n ∈ Finset.range (2 * M + 1),
        (schurDegree (MvPolynomial.C b) L D n).coeff d := by
  symm
  calc
    _ = ∑ n ∈ Finset.range (2 * M + 1), ∑ k ∈ Finset.range (2 * M + 1),
        binomialWeight b k * (((raw L D) ^ k).coeff n).coeff d := by
      apply Finset.sum_congr rfl
      intro n hn
      apply schurDegree_coeff_eq_sum
      simp only [Finset.mem_range] at hn
      omega
    _ = ∑ k ∈ Finset.range (2 * M + 1), ∑ n ∈ Finset.range (2 * M + 1),
        binomialWeight b k * (((raw L D) ^ k).coeff n).coeff d := Finset.sum_comm
    _ = ∑ k ∈ Finset.range (M + 1), ∑ n ∈ Finset.range (2 * M + 1),
        binomialWeight b k * (((raw L D) ^ k).coeff n).coeff d := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hnot
      apply Finset.sum_eq_zero
      intro n hn
      have hdk : degree d < k := by simp only [Finset.mem_range] at hnot; omega
      rw [raw_pow_coeff_coeff_zero L D hL hD k n d hdk, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkM : k ≤ M := by simp only [Finset.mem_range] at hk; omega
      rw [← Finset.mul_sum, ← MvPolynomial.coeff_sum, raw_pow_sum_coeff L D k M hkM]

def kzL : FourPoly A :=
  let x := MvPolynomial.X (0 : Fin 4)
  let y := MvPolynomial.X (1 : Fin 4)
  let z := MvPolynomial.X (2 : Fin 4)
  let w := MvPolynomial.X (3 : Fin 4)
  x + y + z + w + (x + y) * (z + w)

def kzD : FourPoly A :=
  let x := MvPolynomial.X (0 : Fin 4)
  let y := MvPolynomial.X (1 : Fin 4)
  let z := MvPolynomial.X (2 : Fin 4)
  let w := MvPolynomial.X (3 : Fin 4)
  (x + y + 2 * x * y) * (z + w + 2 * z * w)

omit [Algebra ℚ A] in
theorem perturbation_four : perturbation (4 : A) = kzL - kzD := by
  simp only [perturbation, kzL, kzD, map_ofNat]
  ring

omit [Algebra ℚ A] in
theorem kzL_coeff_zero : (kzL : FourPoly A).coeff 0 = 0 := by
  change MvPolynomial.constantCoeff kzL = 0
  simp [kzL]

omit [Algebra ℚ A] in
theorem kzD_coeff_zero : (kzD : FourPoly A).coeff 0 = 0 := by
  change MvPolynomial.constantCoeff kzD = 0
  simp [kzD]

/-- The finite Schur expansion of the actual KZ inverse-power coefficient.
This identity holds in every rational coefficient algebra, including Q[s]. -/
theorem powerCoeff_schur (b : A) (d : MultiIndex) :
    powerCoeff 4 b d =
      ∑ n ∈ Finset.range (2 * degree d + 1), ∑ q ∈ Finset.range (n / 2 + 1),
        WeightedSchur.weight b (n - q) q *
          (kzD ^ q * Schur.complete kzL kzD (n - 2 * q) : FourPoly A).coeff d := by
  unfold powerCoeff
  rw [perturbation_four]
  rw [coefficient_schur b kzL kzD kzL_coeff_zero kzD_coeff_zero d (degree d) le_rfl]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [schurDegree, MvPolynomial.coeff_sum, ← map_weight MvPolynomial.C,
    MvPolynomial.coeff_C_mul]

/-- Coefficientwise nonnegativity for rational multivariate polynomials. -/
def CoeffNonneg {σ : Type*} (p : MvPolynomial σ ℚ) : Prop := ∀ d, 0 ≤ p.coeff d

theorem coeffNonneg_C {σ : Type*} {a : ℚ} (ha : 0 ≤ a) :
    CoeffNonneg (MvPolynomial.C a : MvPolynomial σ ℚ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_C]
  split_ifs <;> positivity

theorem coeffNonneg_one {σ : Type*} : CoeffNonneg (1 : MvPolynomial σ ℚ) := by
  simpa using coeffNonneg_C (σ := σ) (a := 1) (by norm_num)

theorem coeffNonneg_X {σ : Type*} (i : σ) : CoeffNonneg (MvPolynomial.X i : MvPolynomial σ ℚ) := by
  classical
  intro d
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> norm_num

theorem coeffNonneg_add {σ : Type*} {p q : MvPolynomial σ ℚ}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p + q) := by
  intro d
  rw [MvPolynomial.coeff_add]
  exact add_nonneg (hp d) (hq d)

theorem coeffNonneg_mul {σ : Type*} {p q : MvPolynomial σ ℚ}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p * q) := by
  classical
  intro d
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg fun uv _ => mul_nonneg (hp uv.1) (hq uv.2)

theorem coeffNonneg_pow {σ : Type*} {p : MvPolynomial σ ℚ}
    (hp : CoeffNonneg p) (n : ℕ) : CoeffNonneg (p ^ n) := by
  induction n with
  | zero => simpa using (coeffNonneg_one : CoeffNonneg (1 : MvPolynomial σ ℚ))
  | succ n ih => rw [pow_succ]; exact coeffNonneg_mul ih hp

theorem kzD_nonneg : CoeffNonneg (kzD : FourPoly ℚ) := by
  have htwo : CoeffNonneg (2 : FourPoly ℚ) := by
    rw [show (2 : FourPoly ℚ) = 1 + 1 by norm_num]
    exact coeffNonneg_add coeffNonneg_one coeffNonneg_one
  have hpq {p q : FourPoly ℚ} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
      CoeffNonneg (p + q + 2 * p * q) :=
    coeffNonneg_add (coeffNonneg_add hp hq) (coeffNonneg_mul (coeffNonneg_mul htwo hp) hq)
  exact coeffNonneg_mul (hpq (coeffNonneg_X 0) (coeffNonneg_X 1))
    (hpq (coeffNonneg_X 2) (coeffNonneg_X 3))

theorem kzL_map_polynomial :
    MvPolynomial.map Polynomial.C (kzL : FourPoly ℚ) = (kzL : FourPoly (Polynomial ℚ)) := by
  simp [kzL]

theorem kzD_map_polynomial :
    MvPolynomial.map Polynomial.C (kzD : FourPoly ℚ) = (kzD : FourPoly (Polynomial ℚ)) := by
  simp [kzD]

theorem complete_product_coeff_map (q k : ℕ) (d : MultiIndex) :
    (kzD ^ q * Schur.complete kzL kzD k : FourPoly (Polynomial ℚ)).coeff d =
      Polynomial.C ((kzD ^ q * Schur.complete kzL kzD k : FourPoly ℚ).coeff d) := by
  have hm := congrArg (fun p : FourPoly (Polynomial ℚ) => p.coeff d)
    (show MvPolynomial.map Polynomial.C (kzD ^ q * Schur.complete kzL kzD k : FourPoly ℚ) =
      (kzD ^ q * Schur.complete kzL kzD k : FourPoly (Polynomial ℚ)) by
        rw [map_mul, map_pow, Schur.map_complete, kzL_map_polynomial, kzD_map_polynomial])
  simpa only [MvPolynomial.coeff_map] using hm.symm

/-- The remaining positive-direction input is precisely the coefficientwise
nonnegativity of the actual H_k polynomials. No such input is assumed in the
preceding exact coefficient identities. -/
theorem shiftNonnegative_of_complete_nonnegative
    (hH : ∀ k, CoeffNonneg (Schur.complete kzL kzD k : FourPoly ℚ)) : ShiftNonnegative := by
  intro d j
  unfold shiftedCoeff
  rw [powerCoeff_schur]
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro n hn
  apply Finset.sum_nonneg
  intro q hq
  rw [complete_product_coeff_map, Polynomial.coeff_mul_C]
  apply mul_nonneg
  · apply weight_shifted_nonneg (p := n - q) (q := q) _ j
    simp only [Finset.mem_range] at hq
    omega
  · exact coeffNonneg_mul (coeffNonneg_pow kzD_nonneg q) (hH (n - 2 * q)) d

end Results.SharpPowersKz.CoefficientSchur
