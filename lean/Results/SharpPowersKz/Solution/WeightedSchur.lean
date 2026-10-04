import Results.SharpPowersKz.Solution.Schur
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Tactic.FinCases

/-!
The full weighted Schur identity over any rational algebra, including the
identification with actual finite binomial coefficients. The proof uses
finite Chu--Vandermonde, polynomial coefficient comparison, and injectivity
of elementary-symmetric substitution. No positivity conclusion is assumed.
-/

noncomputable section

namespace Results.SharpPowersKz.WeightedSchur

open Schur

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def factInv (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) : A :=
  algebraMap ℚ A ((n.factorial : ℚ)⁻¹)

theorem factInv_succ (n : ℕ) :
    ((n : A) + 1) * factInv A (n + 1) = factInv A n := by
  have h : ((n : ℚ) + 1) * ((n + 1).factorial : ℚ)⁻¹ = (n.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ]
    push_cast
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  have hm := congrArg (algebraMap ℚ A) h
  simpa only [map_mul, map_add, map_natCast, map_one, factInv] using hm

/-- The same Schur scalar weight over any rational algebra, without requiring
that the coefficient ring be a field or an integral domain. -/
def weight (b : A) (p q : ℕ) : A :=
  ((p : A) - q + 1) * factInv A (p + 1) * factInv A q *
    Results.SharpPowersKz.rising b p * Results.SharpPowersKz.rising (b - 1) q

theorem weight_zero (b : A) (p : ℕ) : weight b p 0 = binomialWeight b p := by
  unfold weight binomialWeight
  simp only [Nat.cast_zero, sub_zero, Results.SharpPowersKz.rising,
    Finset.range_zero, Finset.prod_empty, mul_one, factInv, Nat.factorial_zero,
    Nat.cast_one, inv_one, map_one]
  change ((p : A) + 1) * factInv A (p + 1) * _ = factInv A p * _
  rw [factInv_succ]

theorem weight_succ_eq_minor (b : A) (p q : ℕ) :
    weight b p (q + 1) =
      binomialWeight b p * binomialWeight b (q + 1) -
        binomialWeight b (p + 1) * binomialWeight b q := by
  have hp : factInv A p = ((p : A) + 1) * factInv A (p + 1) :=
    (factInv_succ p).symm
  have hq : factInv A q = ((q : A) + 1) * factInv A (q + 1) :=
    (factInv_succ q).symm
  unfold weight
  push_cast
  change ((p : A) - (q + 1) + 1) * factInv A (p + 1) * factInv A (q + 1) *
      Results.SharpPowersKz.rising b p * Results.SharpPowersKz.rising (b - 1) (q + 1) =
    (factInv A p * Results.SharpPowersKz.rising b p) *
        (factInv A (q + 1) * Results.SharpPowersKz.rising b (q + 1)) -
      (factInv A (p + 1) * Results.SharpPowersKz.rising b (p + 1)) *
        (factInv A q * Results.SharpPowersKz.rising b q)
  simp only [← Schur.rising_eq_product]
  rw [hp, hq]
  calc
    _ = (factInv A (p + 1) * factInv A (q + 1)) *
        (((p : A) - q) * Schur.rising b p * Schur.rising (b - 1) (q + 1)) := by ring
    _ = (factInv A (p + 1) * factInv A (q + 1)) *
        (((p : A) + 1) * Schur.rising b p * Schur.rising b (q + 1) -
          ((q : A) + 1) * Schur.rising b (p + 1) * Schur.rising b q) := by
      rw [Schur.adjacent_minor_numerator]
    _ = _ := by ring

theorem minor_binomial_eq_weight (b : A) (n q : ℕ) :
    Schur.minor (binomialWeight b) n q = weight b (n - q) q := by
  cases q with
  | zero =>
      rw [weight_zero]
      simp [Schur.minor, binomialWeight, Results.SharpPowersKz.rising]
  | succ q =>
      rw [weight_succ_eq_minor]
      simp [Schur.minor]

def schurDegree (b L D : A) (n : ℕ) : A :=
  ∑ q ∈ Finset.range (n / 2 + 1),
    weight b (n - q) q * (D ^ q * Schur.complete L D (n - 2 * q))

theorem schurDegree_roots (b l m : A) (n : ℕ) :
    schurDegree b (l + m) (l * m) n =
      ∑ j ∈ Finset.range (n + 1),
        binomialWeight b j * binomialWeight b (n - j) * m ^ (n - j) * l ^ j := by
  simpa only [schurDegree, minor_binomial_eq_weight] using
    Schur.homogeneous_schur (binomialWeight b) l m n

omit [Algebra ℚ A] in
theorem rising_add_length (b : A) (i j : ℕ) :
    Schur.rising b (i + j) = Schur.rising b i * Schur.rising (b + i) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      simp only [Schur.rising_succ, ← Nat.add_assoc, ih, Nat.cast_add]
      ring

omit [Algebra ℚ A] in
/-- Rising-factorial Chu--Vandermonde, proved directly by the Pascal recurrence. -/
theorem rising_add (r s : A) (n : ℕ) :
    Schur.rising (r + s) n =
      ∑ ij ∈ Finset.antidiagonal n,
        (n.choose ij.1 : A) * (Schur.rising r ij.1 * Schur.rising s ij.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Schur.rising_succ, ih, Finset.sum_mul,
        Finset.sum_antidiagonal_choose_succ_mul
          (fun i j => Schur.rising r i * Schur.rising s j) n,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij hij
      have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
      have hchoose : n.choose ij.2 = n.choose ij.1 :=
        (Nat.choose_symm_of_eq_add hsum.symm).symm
      rw [Schur.rising_succ, Schur.rising_succ, hchoose, ← hsum, Nat.cast_add]
      ring

omit [Algebra ℚ A] in
theorem rising_neg_nat (i k : ℕ) :
    Schur.rising (-(i : A)) k = (-1 : A) ^ k * (i.descFactorial k : A) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Schur.rising_succ, ih, Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      by_cases hk : k ≤ i
      · rw [Nat.cast_sub hk]
        ring
      · have hz : i.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        simp [hz]

omit [Algebra ℚ A] in
/-- Exact finite product identity behind factorization of binomial powers
after `L=l+m`, `D=l*m`. No infinite series are used. -/
theorem rising_mul_expansion (b : A) (i j : ℕ) :
    Schur.rising b i * Schur.rising b j =
      ∑ k ∈ Finset.range (j + 1),
        (-1 : A) ^ k * (j.choose k : A) * (i.descFactorial k : A) *
          Schur.rising b (i + j - k) := by
  have hv := rising_add (-(i : A)) (b + i) j
  rw [show -(i : A) + (b + i) = b by ring,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  rw [hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ j := by simp only [Finset.mem_range] at hk; omega
  rw [rising_neg_nat, Nat.add_sub_assoc hk', rising_add_length]
  ring

theorem factInv_choose_desc {i j k : ℕ} (hki : k ≤ i) (hkj : k ≤ j) :
    factInv A i * factInv A j * (j.choose k : A) * (i.descFactorial k : A) =
      factInv A (i - k) * factInv A (j - k) * factInv A k := by
  have hd : ((i - k).factorial : ℚ) * (i.descFactorial k : ℚ) = i.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hki
  have hc : (j.choose k : ℚ) * (k.factorial : ℚ) * ((j - k).factorial : ℚ) =
      j.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkj
  have hh := congrArg₂ (fun x y : ℚ => x * y) hd hc
  have hr : (i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹ * (j.choose k : ℚ) *
      (i.descFactorial k : ℚ) =
        ((i - k).factorial : ℚ)⁻¹ * ((j - k).factorial : ℚ)⁻¹ * (k.factorial : ℚ)⁻¹ := by
    have hi : (i.factorial : ℚ) ≠ 0 := by positivity
    have hj : (j.factorial : ℚ) ≠ 0 := by positivity
    have hik : ((i - k).factorial : ℚ) ≠ 0 := by positivity
    have hjk : ((j - k).factorial : ℚ) ≠ 0 := by positivity
    have hk : (k.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    nlinarith only [hh]
  have hm := congrArg (algebraMap ℚ A) hr
  simpa only [map_mul, map_natCast, factInv] using hm

theorem binomialWeight_mul_expansion (b : A) (i j : ℕ) :
    binomialWeight b i * binomialWeight b j =
      ∑ k ∈ Finset.range (min i j + 1),
        (-1 : A) ^ k * factInv A (i - k) * factInv A (j - k) * factInv A k *
          Results.SharpPowersKz.rising b (i + j - k) := by
  change (factInv A i * Results.SharpPowersKz.rising b i) *
      (factInv A j * Results.SharpPowersKz.rising b j) = _
  simp only [← Schur.rising_eq_product]
  calc
    _ = (factInv A i * factInv A j) * (Schur.rising b i * Schur.rising b j) := by ring
    _ = ∑ k ∈ Finset.range (j + 1),
        (factInv A i * factInv A j) *
          ((-1 : A) ^ k * (j.choose k : A) * (i.descFactorial k : A) *
            Schur.rising b (i + j - k)) := by rw [rising_mul_expansion, Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (min i j + 1),
        (factInv A i * factInv A j) *
          ((-1 : A) ^ k * (j.choose k : A) * (i.descFactorial k : A) *
            Schur.rising b (i + j - k)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hnot
      have hik : i < k := by simp only [Finset.mem_range] at hk hnot; omega
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hik]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≤ i := by simp only [Finset.mem_range] at hk; omega
      have hkj : k ≤ j := by simp only [Finset.mem_range] at hk; omega
      have h := factInv_choose_desc (A := A) hki hkj
      calc
        _ = (-1 : A) ^ k *
            (factInv A i * factInv A j * (j.choose k : A) * (i.descFactorial k : A)) *
              Schur.rising b (i + j - k) := by ring
        _ = _ := by rw [h]; ring

theorem factInv_mul_choose {n k : ℕ} (hk : k ≤ n) :
    factInv A n * (n.choose k : A) = factInv A k * factInv A (n - k) := by
  have hc : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
      n.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hr : (n.factorial : ℚ)⁻¹ * (n.choose k : ℚ) =
      (k.factorial : ℚ)⁻¹ * ((n - k).factorial : ℚ)⁻¹ := by
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    have hk' : (k.factorial : ℚ) ≠ 0 := by positivity
    have hnk : ((n - k).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    nlinarith only [hc]
  have hm := congrArg (algebraMap ℚ A) hr
  simpa only [map_mul, map_natCast, factInv] using hm

theorem factInv_two_choose {n i k : ℕ} (hki : k ≤ i) (hik : i ≤ n - k)
    (hk : 2 * k ≤ n) :
    factInv A (n - k) * ((n - k).choose k : A) * ((n - 2 * k).choose (i - k) : A) =
      factInv A (i - k) * factInv A (n - i - k) * factInv A k := by
  rw [factInv_mul_choose (by omega), show n - k - k = n - 2 * k by omega]
  rw [mul_assoc, factInv_mul_choose (by omega), show n - 2 * k - (i - k) = n - i - k by omega]
  ring

/-- Weight-n component of the formal binomial expansion in variables of
weights one and two. The k-th summand selects k copies of the quadratic term. -/
def binomialDegree (b L D : A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : A) ^ k * binomialWeight b (n - k) * ((n - k).choose k : A) *
      L ^ (n - 2 * k) * D ^ k

omit [Algebra ℚ A] in
theorem binomial_root_term_coeff (m : A) {n k : ℕ} (hk : 2 * k ≤ n) (i : ℕ) :
    (((Polynomial.X + Polynomial.C m) ^ (n - 2 * k)) *
      (Polynomial.X * Polynomial.C m) ^ k).coeff i =
      if k ≤ i ∧ i ≤ n - k then
        ((n - 2 * k).choose (i - k) : A) * m ^ (n - i) else 0 := by
  have heq : ((Polynomial.X + Polynomial.C m) ^ (n - 2 * k)) *
      (Polynomial.X * Polynomial.C m) ^ k =
        (((Polynomial.X + Polynomial.C m) ^ (n - 2 * k)) * Polynomial.X ^ k) *
          Polynomial.C (m ^ k) := by
    rw [mul_pow, map_pow]
    ring
  rw [heq, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow', Polynomial.coeff_X_add_C_pow]
  by_cases hi : k ≤ i ∧ i ≤ n - k
  · rw [if_pos hi, if_pos hi.1]
    have he : n - 2 * k - (i - k) + k = n - i := by omega
    rw [mul_assoc, mul_comm ((n - 2 * k).choose (i - k) : A), ← mul_assoc, ← pow_add, he]
    ring
  · rw [if_neg hi]
    by_cases hki : k ≤ i
    · rw [if_pos hki, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · rw [if_neg hki, zero_mul]

theorem binomial_root_polynomial (b m : A) (n : ℕ) :
    (∑ k ∈ Finset.range (n / 2 + 1),
      Polynomial.C ((-1 : A) ^ k * binomialWeight b (n - k) * ((n - k).choose k : A)) *
        (((Polynomial.X + Polynomial.C m) ^ (n - 2 * k)) *
          (Polynomial.X * Polynomial.C m) ^ k)) =
      ∑ i ∈ Finset.range (n + 1),
        Polynomial.C (binomialWeight b i * binomialWeight b (n - i) * m ^ (n - i)) *
          Polynomial.X ^ i := by
  apply Polynomial.ext
  intro i
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have ht : (∑ k ∈ Finset.range (n / 2 + 1),
      ((-1 : A) ^ k * binomialWeight b (n - k) * ((n - k).choose k : A)) *
        (((Polynomial.X + Polynomial.C m) ^ (n - 2 * k)) *
          (Polynomial.X * Polynomial.C m) ^ k).coeff i) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        if k ≤ i ∧ i ≤ n - k then
          (-1 : A) ^ k * binomialWeight b (n - k) * ((n - k).choose k : A) *
            (((n - 2 * k).choose (i - k) : A) * m ^ (n - i)) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [binomial_root_term_coeff m (by simp only [Finset.mem_range] at hk; omega), mul_ite,
      mul_zero]
  rw [ht]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hi : i ≤ n
  · rw [if_pos (by omega)]
    have hsub : Finset.range (min i (n - i) + 1) ⊆ Finset.range (n / 2 + 1) := by
      intro k hk
      simp only [Finset.mem_range] at *
      omega
    rw [← Finset.sum_subset hsub (by
      intro k hk hnot
      simp only [Finset.mem_range] at hk hnot
      rw [if_neg (by omega)])]
    rw [binomialWeight_mul_expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≤ i := by simp only [Finset.mem_range] at hk; omega
    have hik : i ≤ n - k := by simp only [Finset.mem_range] at hk; omega
    have hkn : 2 * k ≤ n := by omega
    rw [if_pos ⟨hki, hik⟩, Nat.add_sub_of_le hi]
    change (-1 : A) ^ k * (factInv A (n - k) * Results.SharpPowersKz.rising b (n - k)) *
        ((n - k).choose k : A) * (((n - 2 * k).choose (i - k) : A) * m ^ (n - i)) = _
    have hc := factInv_two_choose (A := A) hki hik hkn
    calc
      _ = (-1 : A) ^ k *
          (factInv A (n - k) * ((n - k).choose k : A) * ((n - 2 * k).choose (i - k) : A)) *
            Results.SharpPowersKz.rising b (n - k) * m ^ (n - i) := by ring
      _ = _ := by rw [hc]; ring
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (by omega)]

theorem binomialDegree_roots (b l m : A) (n : ℕ) :
    binomialDegree b (l + m) (l * m) n =
      ∑ j ∈ Finset.range (n + 1),
        binomialWeight b j * binomialWeight b (n - j) * m ^ (n - j) * l ^ j := by
  have h := congrArg (Polynomial.evalRingHom l) (binomial_root_polynomial b m n)
  simpa only [binomialDegree, map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_mul, mul_assoc]
      using h

theorem weighted_schur_roots (b l m : A) (n : ℕ) :
    binomialDegree b (l + m) (l * m) n = schurDegree b (l + m) (l * m) n := by
  rw [binomialDegree_roots, schurDegree_roots]

omit [Algebra ℚ A] in
theorem linearPower_coeff (a b : A) (n k : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ n).coeff k =
      (n.choose k : A) * a ^ (n - k) * b ^ k := by
  rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
  have ht : (∑ j ∈ Finset.range (n + 1),
      (((Polynomial.C b * Polynomial.X) ^ j) * Polynomial.C a ^ (n - j) *
        (n.choose j : Polynomial A)).coeff k) =
      ∑ j ∈ Finset.range (n + 1),
        if k = j then (n.choose j : A) * a ^ (n - j) * b ^ j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have he : ((Polynomial.C b * Polynomial.X) ^ j) * Polynomial.C a ^ (n - j) *
        (n.choose j : Polynomial A) =
        Polynomial.C ((n.choose j : A) * a ^ (n - j) * b ^ j) * Polynomial.X ^ j := by
      simp only [map_mul, map_pow, map_natCast, mul_pow]
      ring
    rw [he, Polynomial.coeff_C_mul_X_pow]
  rw [ht, Finset.sum_ite_eq]
  by_cases hk : k ≤ n
  · rw [if_pos (by simpa using hk)]
  · rw [if_neg (by simpa using hk), Nat.choose_eq_zero_of_lt (by omega)]
    simp

omit [Algebra ℚ A] in
theorem rawBinomial_coeff_reflect (L D : A) {n q : ℕ} (hq : q ≤ n) :
    ((Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2) ^ (n - q)).coeff n =
      ((n - q).choose q : A) * L ^ (n - 2 * q) * (-D) ^ q := by
  have he : (Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2) ^ (n - q) =
      Polynomial.X ^ (n - q) * (Polynomial.C L + Polynomial.C (-D) * Polynomial.X) ^ (n - q) := by
    rw [← mul_pow]
    congr 1
    simp only [map_neg]
    ring
  rw [he, Polynomial.coeff_X_pow_mul', if_pos (by omega), linearPower_coeff,
    show n - (n - q) = q by omega, show n - q - q = n - 2 * q by omega]

/-- Exact identification of `binomialDegree` with the coefficient of the
finite binomial expansion of `(1-L*t+D*t^2)^(-b)`. -/
theorem binomialDegree_eq_coeff_sum (b L D : A) (n : ℕ) :
    binomialDegree b L D n =
      ∑ k ∈ Finset.range (n + 1), binomialWeight b k *
        ((Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2) ^ k).coeff n := by
  let f : ℕ → A := fun k => binomialWeight b k *
    ((Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2) ^ k).coeff n
  trans ∑ q ∈ Finset.range (n + 1), f (n - q)
  · dsimp only [f]
    symm
    calc
      _ = ∑ q ∈ Finset.range (n / 2 + 1), binomialWeight b (n - q) *
          ((Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2) ^ (n - q)).coeff n := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro q hq hnot
        have hqn : q ≤ n := by simp only [Finset.mem_range] at hq; omega
        rw [rawBinomial_coeff_reflect L D hqn, Nat.choose_eq_zero_of_lt (by
          simp only [Finset.mem_range] at hnot; omega)]
        simp
      _ = _ := by
        unfold binomialDegree
        apply Finset.sum_congr rfl
        intro q hq
        have hqn : q ≤ n := by simp only [Finset.mem_range] at hq; omega
        rw [rawBinomial_coeff_reflect L D hqn, neg_pow]
        ring
  · simpa only [Nat.add_sub_cancel, f] using Finset.sum_range_reflect f (n + 1)

section Maps

variable {B : Type*} [CommRing B] [Algebra ℚ B]

theorem map_factInv (f : A →+* B) (n : ℕ) : f (factInv A n) = factInv B n := by
  simp only [factInv, RingHom.map_rat_algebraMap]

theorem map_defsRising (f : A →+* B) (b : A) (n : ℕ) :
    f (Results.SharpPowersKz.rising b n) = Results.SharpPowersKz.rising (f b) n := by
  simp only [← Schur.rising_eq_product, Schur.map_rising]

theorem map_binomialWeight (f : A →+* B) (b : A) (n : ℕ) :
    f (binomialWeight b n) = binomialWeight (f b) n := by
  simp only [binomialWeight, map_mul, RingHom.map_rat_algebraMap, map_defsRising]

theorem map_weight (f : A →+* B) (b : A) (p q : ℕ) :
    f (weight b p q) = weight (f b) p q := by
  simp only [weight, map_mul, map_add, map_sub, map_natCast, map_one, map_factInv,
    map_defsRising]

theorem map_schurDegree (f : A →+* B) (b L D : A) (n : ℕ) :
    f (schurDegree b L D n) = schurDegree (f b) (f L) (f D) n := by
  simp only [schurDegree, map_sum, map_mul, map_pow, map_weight, Schur.map_complete]

theorem map_binomialDegree (f : A →+* B) (b L D : A) (n : ℕ) :
    f (binomialDegree b L D n) = binomialDegree (f b) (f L) (f D) n := by
  simp only [binomialDegree, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_binomialWeight]

end Maps

def rootMap (A : Type*) [CommRing A] :
    MvPolynomial (Fin 2) A →ₐ[A] MvPolynomial (Fin 2) A :=
  MvPolynomial.aeval fun i =>
    if i = 0 then MvPolynomial.X 0 + MvPolynomial.X 1 else MvPolynomial.X 0 * MvPolynomial.X 1

omit [Algebra ℚ A] in
@[simp] theorem rootMap_C (b : A) : rootMap A (MvPolynomial.C b) = MvPolynomial.C b := by
  simp [rootMap]

omit [Algebra ℚ A] in
@[simp] theorem rootMap_X_zero :
    rootMap A (MvPolynomial.X 0) = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  simp [rootMap]

omit [Algebra ℚ A] in
@[simp] theorem rootMap_X_one :
    rootMap A (MvPolynomial.X 1) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [rootMap]

theorem weighted_schur_of_rootMap_injective (hinj : Function.Injective (rootMap A))
    (b L D : A) (n : ℕ) : binomialDegree b L D n = schurDegree b L D n := by
  have hf : binomialDegree (MvPolynomial.C b : MvPolynomial (Fin 2) A)
      (MvPolynomial.X 0) (MvPolynomial.X 1) n =
      schurDegree (MvPolynomial.C b) (MvPolynomial.X 0) (MvPolynomial.X 1) n := by
    apply hinj
    change (rootMap A).toRingHom _ = (rootMap A).toRingHom _
    rw [map_binomialDegree, map_schurDegree]
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootMap_C, rootMap_X_zero,
      rootMap_X_one] using weighted_schur_roots (MvPolynomial.C b)
        (MvPolynomial.X 0) (MvPolynomial.X 1) n
  let g : MvPolynomial (Fin 2) A →ₐ[A] A :=
    MvPolynomial.aeval fun i => if i = 0 then L else D
  have h := congrArg g.toRingHom hf
  rw [map_binomialDegree, map_schurDegree] at h
  simpa [g] using h

omit [Algebra ℚ A] in
theorem rootMap_injective : Function.Injective (rootMap A) := by
  have he₁ : MvPolynomial.esymm (Fin 2) A 1 =
      MvPolynomial.X 0 + MvPolynomial.X 1 := by
    simp [MvPolynomial.esymm_one, Fin.sum_univ_two]
  have he₂ : MvPolynomial.esymm (Fin 2) A 2 =
      MvPolynomial.X 0 * MvPolynomial.X 1 := by
    have hc : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
    have hp : Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ} := by
      simpa only [hc] using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
    rw [MvPolynomial.esymm, hp, Finset.sum_singleton]
    simp [Fin.prod_univ_two]
  have he : (fun i : Fin 2 => MvPolynomial.esymm (Fin 2) A (i + 1)) =
      (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 + MvPolynomial.X 1 else
        MvPolynomial.X 0 * MvPolynomial.X 1) := by
    funext i
    fin_cases i <;> simp [he₁, he₂]
  intro p q hpq
  apply MvPolynomial.esymmAlgHom_injective (σ := Fin 2) A (n := 2) (by decide)
  apply Subtype.ext
  simpa only [MvPolynomial.esymmAlgHom_apply, he, rootMap] using hpq

/-- The complete weighted Schur identity in any rational algebra. -/
theorem weighted_schur (b L D : A) (n : ℕ) :
    binomialDegree b L D n = schurDegree b L D n :=
  weighted_schur_of_rootMap_injective rootMap_injective b L D n

/-- The Schur expansion equals the actual finite binomial coefficient, before
any specialization to the Kauers--Zeilberger polynomials. -/
theorem finite_binomial_schur (b L D : A) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), binomialWeight b k *
      ((Polynomial.C L * Polynomial.X - Polynomial.C D * Polynomial.X ^ 2) ^ k).coeff n) =
      schurDegree b L D n := by
  rw [← binomialDegree_eq_coeff_sum, weighted_schur]

theorem weight_shifted_eq (p q : ℕ) :
    weight (1 + Polynomial.X : Polynomial ℚ) p q = Schur.shiftedWeight p q := by
  have hc : ((p : ℚ) - q + 1) / ((p + 1).factorial * q.factorial) =
      ((p : ℚ) - q + 1) * ((p + 1).factorial : ℚ)⁻¹ * (q.factorial : ℚ)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold weight factInv Schur.shiftedWeight
  rw [hc]
  simp only [← Schur.rising_eq_product, Polynomial.algebraMap_eq, map_mul, map_sub,
    map_add, map_natCast, map_one]
  rw [show (1 + Polynomial.X : Polynomial ℚ) - 1 = Polynomial.X by ring,
    add_comm (1 : Polynomial ℚ) Polynomial.X]

theorem weight_shifted_nonneg {p q : ℕ} (hqp : q ≤ p) :
    Schur.PolyNonneg (weight (1 + Polynomial.X : Polynomial ℚ) p q) := by
  rw [weight_shifted_eq]
  exact Schur.shiftedWeight_nonneg hqp

end Results.SharpPowersKz.WeightedSchur
