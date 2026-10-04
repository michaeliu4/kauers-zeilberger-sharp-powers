import Results.SharpPowersKz.Solution.Basic
import Results.SharpPowersKz.Solution.Truncation
import Results.SharpPowersKz.Solution.Schur
import Results.SharpPowersKz.Solution.CoefficientSchur
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FinCases

/-!
Exact lowest-degree coefficients of the specialized complete polynomials.
The lower-bound transfer exposes H-polynomial positivity as its sole internal
positivity premise; all finite identities and degree comparisons are proved.
-/

noncomputable section

namespace Results.SharpPowersKz.LowerBound

open MvPolynomial

variable {A : Type*} [CommRing A]

abbrev FourPoly (A : Type*) [CommRing A] := MvPolynomial (Fin 4) A

def MinDegree (n : ℕ) (p : FourPoly A) : Prop :=
  ∀ d : MultiIndex, degree d < n → p.coeff d = 0

theorem minDegree_zero (p : FourPoly A) : MinDegree 0 p := by
  intro d hd
  omega

theorem minDegree_zero_poly (n : ℕ) : MinDegree n (0 : FourPoly A) := by
  intro d hd
  simp

theorem minDegree_mono {m n : ℕ} {p : FourPoly A}
    (hp : MinDegree n p) (hmn : m ≤ n) : MinDegree m p := by
  intro d hd
  exact hp d (lt_of_lt_of_le hd hmn)

theorem minDegree_add {n : ℕ} {p q : FourPoly A}
    (hp : MinDegree n p) (hq : MinDegree n q) : MinDegree n (p + q) := by
  intro d hd
  rw [coeff_add, hp d hd, hq d hd, add_zero]

theorem minDegree_sub {n : ℕ} {p q : FourPoly A}
    (hp : MinDegree n p) (hq : MinDegree n q) : MinDegree n (p - q) := by
  intro d hd
  have he : (p - q).coeff d = p.coeff d - q.coeff d := Finsupp.sub_apply _ _ _
  rw [he, hp d hd, hq d hd, sub_self]

theorem minDegree_mul {m n : ℕ} {p q : FourPoly A}
    (hp : MinDegree m p) (hq : MinDegree n q) : MinDegree (m + n) (p * q) := by
  classical
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro e he
  have heq : e.1 + e.2 = d := Finset.mem_antidiagonal.mp he
  have hdeg : degree e.1 + degree e.2 = degree d := by rw [← degree_add, heq]
  by_cases hleft : degree e.1 < m
  · rw [hp e.1 hleft, zero_mul]
  · rw [hq e.2 (by omega), mul_zero]

theorem minDegree_mul_le {m n k : ℕ} {p q : FourPoly A}
    (hp : MinDegree m p) (hq : MinDegree n q) (hk : k ≤ m + n) :
    MinDegree k (p * q) := minDegree_mono (minDegree_mul hp hq) hk

theorem minDegree_C_mul {n : ℕ} {p : FourPoly A} (c : A)
    (hp : MinDegree n p) : MinDegree n (C c * p) := by
  intro d hd
  rw [coeff_C_mul, hp d hd, mul_zero]

theorem minDegree_monomial (d : MultiIndex) (c : A) :
    MinDegree (degree d) (monomial d c) := by
  classical
  intro e he
  rw [coeff_monomial, if_neg]
  intro h
  subst e
  omega

theorem minDegree_X (i : Fin 4) : MinDegree 1 (X i : FourPoly A) := by
  simpa [X] using minDegree_monomial (Finsupp.single i 1) (1 : A)

theorem complete_minDegree (L D : FourPoly A) (hL : MinDegree 1 L)
    (hD : MinDegree 2 D) (n : ℕ) : MinDegree n (Schur.complete L D n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact minDegree_zero _
  | one => exact hL
  | more n ih₀ ih₁ =>
      rw [Schur.complete_add_two]
      exact minDegree_sub (minDegree_mul_le hL ih₁ (by omega))
        (minDegree_mul_le hD ih₀ (by omega))

/-- Replacing L,D by their leading parts preserves the degree-n coefficients
of the complete polynomial H_n; all differences have degree at least n+1. -/
theorem complete_leading_difference (L D L₀ D₀ : FourPoly A)
    (hL : MinDegree 1 L) (hD : MinDegree 2 D)
    (hL₀ : MinDegree 1 L₀) (hD₀ : MinDegree 2 D₀)
    (hLd : MinDegree 2 (L - L₀)) (hDd : MinDegree 3 (D - D₀)) (n : ℕ) :
    MinDegree (n + 1) (Schur.complete L D n - Schur.complete L₀ D₀ n) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using minDegree_zero_poly (A := A) 1
  | one => exact hLd
  | more n ih₀ ih₁ =>
      rw [Schur.complete_add_two, Schur.complete_add_two]
      have he : L * Schur.complete L D (n + 1) - D * Schur.complete L D n -
          (L₀ * Schur.complete L₀ D₀ (n + 1) - D₀ * Schur.complete L₀ D₀ n) =
          ((L - L₀) * Schur.complete L D (n + 1) +
            L₀ * (Schur.complete L D (n + 1) - Schur.complete L₀ D₀ (n + 1))) -
          ((D - D₀) * Schur.complete L D n +
            D₀ * (Schur.complete L D n - Schur.complete L₀ D₀ n)) := by ring
      rw [he]
      exact minDegree_sub
        (minDegree_add
          (minDegree_mul_le hLd (complete_minDegree L D hL hD (n + 1)) (by omega))
          (minDegree_mul_le hL₀ ih₁ (by omega)))
        (minDegree_add
          (minDegree_mul_le hDd (complete_minDegree L D hL hD n) (by omega))
          (minDegree_mul_le hD₀ ih₀ (by omega)))

def pairLeft : FourPoly A := X 0 + X 1

def pairRight : FourPoly A := X 2 + X 3

theorem pairLeft_minDegree : MinDegree 1 (pairLeft : FourPoly A) :=
  minDegree_add (minDegree_X 0) (minDegree_X 1)

theorem pairRight_minDegree : MinDegree 1 (pairRight : FourPoly A) :=
  minDegree_add (minDegree_X 2) (minDegree_X 3)

def tupleIndex (a b c e : ℕ) : MultiIndex :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c + Finsupp.single 3 e

@[simp] theorem tupleIndex_zero (a b c e : ℕ) : tupleIndex a b c e 0 = a := by
  simp [tupleIndex]
@[simp] theorem tupleIndex_one (a b c e : ℕ) : tupleIndex a b c e 1 = b := by
  simp [tupleIndex]
@[simp] theorem tupleIndex_two (a b c e : ℕ) : tupleIndex a b c e 2 = c := by
  simp [tupleIndex]
@[simp] theorem tupleIndex_three (a b c e : ℕ) : tupleIndex a b c e 3 = e := by
  simp [tupleIndex]

theorem tupleIndex_eta (d : MultiIndex) : tupleIndex (d 0) (d 1) (d 2) (d 3) = d := by
  ext i
  fin_cases i <;> simp

theorem degree_eq_four (d : MultiIndex) : degree d = d 0 + d 1 + d 2 + d 3 := by
  conv_lhs => rw [← tupleIndex_eta d]
  simp [tupleIndex, degree_add]

theorem tupleIndex_eq_iff (a b c e : ℕ) (d : MultiIndex) :
    tupleIndex a b c e = d ↔ a = d 0 ∧ b = d 1 ∧ c = d 2 ∧ e = d 3 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun t => t 0) h,
      by simpa using congrArg (fun t => t 1) h,
      by simpa using congrArg (fun t => t 2) h,
      by simpa using congrArg (fun t => t 3) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact tupleIndex_eta d

theorem pair_powers_expansion (j k : ℕ) :
    (pairLeft : FourPoly A) ^ j * pairRight ^ k =
      ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
        monomial (tupleIndex a (j - a) c (k - c))
          ((j.choose a : A) * (k.choose c : A)) := by
  rw [pairLeft, pairRight, add_pow, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    _ = (C ((j.choose a : A) * (k.choose c : A)) : FourPoly A) *
        (X 0 ^ a * X 1 ^ (j - a) * X 2 ^ c * X 3 ^ (k - c)) := by
      simp only [map_mul, map_natCast]
      ring
    _ = _ := by simp only [X_pow_eq_monomial, monomial_mul, tupleIndex, C_mul_monomial, mul_one]

theorem pair_powers_coeff (j k : ℕ) (d : MultiIndex) :
    ((pairLeft : FourPoly A) ^ j * pairRight ^ k).coeff d =
      if d 0 + d 1 = j ∧ d 2 + d 3 = k then
        (j.choose (d 0) : A) * (k.choose (d 2) : A) else 0 := by
  classical
  rw [pair_powers_expansion, coeff_sum]
  simp only [coeff_sum, coeff_monomial]
  by_cases hd : d 0 + d 1 = j ∧ d 2 + d 3 = k
  · rw [if_pos hd]
    have hindex (a c : ℕ) :
        tupleIndex a (j - a) c (k - c) = d ↔ a = d 0 ∧ c = d 2 := by
      rw [tupleIndex_eq_iff]
      constructor
      · exact fun h => ⟨h.1, h.2.2.1⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, by omega, rfl, by omega⟩
    simp_rw [hindex]
    simp [ite_and, Finset.mem_range,
      show d 0 < j + 1 by omega, show d 2 < k + 1 by omega]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro c hc
    rw [if_neg]
    intro he
    rw [tupleIndex_eq_iff] at he
    simp only [Finset.mem_range] at ha hc
    apply hd
    omega

/-- Complete homogeneous polynomials in the two roots are finite geometric sums. -/
theorem complete_roots_sum (u v : A) (n : ℕ) :
    Schur.complete (u + v) (u * v) n =
      ∑ j ∈ Finset.range (n + 1), u ^ j * v ^ (n - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Schur.complete_roots_succ, ih, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, Nat.sub_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [show n + 1 - (j + 1) = n - j by omega, pow_succ]
      ring

theorem complete_pair_coeff (d : MultiIndex) :
    (Schur.complete ((pairLeft : FourPoly A) + pairRight)
      (pairLeft * pairRight) (degree d)).coeff d =
        ((d 0 + d 1).choose (d 0) : A) * ((d 2 + d 3).choose (d 2) : A) := by
  classical
  rw [complete_roots_sum, coeff_sum]
  simp_rw [pair_powers_coeff]
  have hd := degree_eq_four d
  have hindex (j : ℕ) :
      (d 0 + d 1 = j ∧ d 2 + d 3 = degree d - j) ↔ j = d 0 + d 1 := by omega
  simp_rw [hindex]
  simp [Finset.mem_range, show d 0 + d 1 < degree d + 1 by omega,
    show degree d - (d 0 + d 1) = d 2 + d 3 by omega]

def quadLeft : FourPoly A := C 2 * (X 0 * X 1)
def quadRight : FourPoly A := C 2 * (X 2 * X 3)

theorem quadLeft_minDegree : MinDegree 2 (quadLeft : FourPoly A) :=
  minDegree_C_mul 2 (minDegree_mul (minDegree_X 0) (minDegree_X 1))

theorem quadRight_minDegree : MinDegree 2 (quadRight : FourPoly A) :=
  minDegree_C_mul 2 (minDegree_mul (minDegree_X 2) (minDegree_X 3))

theorem kzL_parts : (CoefficientSchur.kzL : FourPoly A) =
    pairLeft + pairRight + pairLeft * pairRight := by
  simp only [CoefficientSchur.kzL, pairLeft, pairRight]
  ring

theorem kzD_parts : (CoefficientSchur.kzD : FourPoly A) =
    (pairLeft + quadLeft) * (pairRight + quadRight) := by
  simp only [CoefficientSchur.kzD, pairLeft, pairRight, quadLeft, quadRight, map_ofNat]
  ring

theorem kzL_minDegree : MinDegree 1 (CoefficientSchur.kzL : FourPoly A) := by
  rw [kzL_parts]
  exact minDegree_add (minDegree_add pairLeft_minDegree pairRight_minDegree)
    (minDegree_mul_le pairLeft_minDegree pairRight_minDegree (by omega))

theorem kzD_minDegree : MinDegree 2 (CoefficientSchur.kzD : FourPoly A) := by
  rw [kzD_parts]
  exact minDegree_mul
    (minDegree_add pairLeft_minDegree (minDegree_mono quadLeft_minDegree (by omega)))
    (minDegree_add pairRight_minDegree (minDegree_mono quadRight_minDegree (by omega)))

theorem kzL_difference_minDegree : MinDegree 2
    ((CoefficientSchur.kzL : FourPoly A) - (pairLeft + pairRight)) := by
  rw [kzL_parts, add_sub_cancel_left]
  exact minDegree_mul pairLeft_minDegree pairRight_minDegree

theorem kzD_difference_minDegree : MinDegree 3
    ((CoefficientSchur.kzD : FourPoly A) - pairLeft * pairRight) := by
  rw [kzD_parts]
  have he : ((pairLeft : FourPoly A) + quadLeft) * (pairRight + quadRight) -
      pairLeft * pairRight =
      pairLeft * quadRight + quadLeft * pairRight + quadLeft * quadRight := by ring
  rw [he]
  exact minDegree_add
    (minDegree_add (minDegree_mul_le pairLeft_minDegree quadRight_minDegree (by omega))
      (minDegree_mul_le quadLeft_minDegree pairRight_minDegree (by omega)))
    (minDegree_mul_le quadLeft_minDegree quadRight_minDegree (by omega))

/-- The exact leading-degree coefficient used in the sharp lower bound. -/
theorem complete_kz_leading_coeff (d : MultiIndex) :
    (Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD (degree d) : FourPoly A).coeff d =
      ((d 0 + d 1).choose (d 0) : A) * ((d 2 + d 3).choose (d 2) : A) := by
  have h := complete_leading_difference
    (CoefficientSchur.kzL : FourPoly A) CoefficientSchur.kzD
    (pairLeft + pairRight) (pairLeft * pairRight)
    kzL_minDegree kzD_minDegree
    (minDegree_add pairLeft_minDegree pairRight_minDegree)
    (minDegree_mul pairLeft_minDegree pairRight_minDegree)
    kzL_difference_minDegree kzD_difference_minDegree (degree d)
  have hd := h d (Nat.lt_succ_self (degree d))
  have he : (Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD (degree d) -
      Schur.complete (pairLeft + pairRight) (pairLeft * pairRight) (degree d) : FourPoly A).coeff d =
      (Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD (degree d) : FourPoly A).coeff d -
      (Schur.complete (pairLeft + pairRight) (pairLeft * pairRight) (degree d) : FourPoly A).coeff d :=
    Finsupp.sub_apply _ _ _
  rw [he, complete_pair_coeff] at hd
  exact sub_eq_zero.mp hd

/-- The rational H-polynomial coefficients agree with their real images. -/
theorem complete_product_coeff_real (q k : ℕ) (d : MultiIndex) :
    (CoefficientSchur.kzD ^ q * Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD k
      : FourPoly ℝ).coeff d =
      (((CoefficientSchur.kzD ^ q * Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD k
        : FourPoly ℚ).coeff d : ℚ) : ℝ) := by
  have hm := congrArg (fun p : FourPoly ℝ => p.coeff d)
    (show MvPolynomial.map (algebraMap ℚ ℝ)
        (CoefficientSchur.kzD ^ q * Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD k
          : FourPoly ℚ) =
      (CoefficientSchur.kzD ^ q * Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD k
        : FourPoly ℝ) by
      rw [map_mul, map_pow, Schur.map_complete]
      simp [CoefficientSchur.kzL, CoefficientSchur.kzD])
  have hcast (x : ℚ) : (algebraMap ℚ ℝ) x = (x : ℝ) := by
    have hhom : algebraMap ℚ ℝ = Rat.castHom ℝ := Subsingleton.elim _ _
    rw [hhom]
    rfl
  simpa only [MvPolynomial.coeff_map, hcast] using hm.symm

theorem real_weight_nonnegative (β : ℝ) (hβ : 1 ≤ β) (p q : ℕ) (hpq : q ≤ p) :
    0 ≤ WeightedSchur.weight β p q := by
  have hfac (n : ℕ) : 0 ≤ WeightedSchur.factInv ℝ n := by
    change 0 ≤ (((n.factorial : ℚ)⁻¹ : ℚ) : ℝ)
    positivity
  have hr (b : ℝ) (hb : 0 ≤ b) (n : ℕ) : 0 ≤ rising b n := by
    rw [← Schur.rising_eq_product]
    exact Schur.rising_nonneg hb n
  have hpq' : (q : ℝ) ≤ p := by exact_mod_cast hpq
  unfold WeightedSchur.weight
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (hfac (p + 1))) (hfac q))
      (hr β (by linarith) p)) (hr (β - 1) (by linarith) q)

/-- The lower-bound comparison is reduced only to nonnegativity of the actual
H_k coefficients. The finite expansion and its selected coefficient are proved. -/
theorem lowerBound_le_of_complete_nonnegative
    (hH : ∀ k, CoefficientSchur.CoeffNonneg
      (Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD k : FourPoly ℚ))
    (β : ℝ) (hβ : 1 ≤ β) (d : MultiIndex) : lowerBound β d ≤ powerCoeff 4 β d := by
  classical
  let T (n q : ℕ) : ℝ := WeightedSchur.weight β (n - q) q *
    (CoefficientSchur.kzD ^ q *
      Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD (n - 2 * q) : FourPoly ℝ).coeff d
  have hT (n q : ℕ) (hq : q ∈ Finset.range (n / 2 + 1)) : 0 ≤ T n q := by
    have hqp : q ≤ n - q := by simp only [Finset.mem_range] at hq; omega
    apply mul_nonneg (real_weight_nonnegative β hβ (n - q) q hqp)
    rw [complete_product_coeff_real]
    exact_mod_cast CoefficientSchur.coeffNonneg_mul
      (CoefficientSchur.coeffNonneg_pow CoefficientSchur.kzD_nonneg q) (hH (n - 2 * q)) d
  have houter : (∑ q ∈ Finset.range (degree d / 2 + 1), T (degree d) q) ≤
      ∑ n ∈ Finset.range (2 * degree d + 1), ∑ q ∈ Finset.range (n / 2 + 1), T n q := by
    apply Finset.single_le_sum (f := fun n => ∑ q ∈ Finset.range (n / 2 + 1), T n q)
      (a := degree d)
    · intro n hn
      exact Finset.sum_nonneg fun q hq => hT n q hq
    · simp only [Finset.mem_range]
      omega
  have hinner : T (degree d) 0 ≤
      ∑ q ∈ Finset.range (degree d / 2 + 1), T (degree d) q := by
    apply Finset.single_le_sum
    · exact fun q hq => hT (degree d) q hq
    · simp
  have hselected : T (degree d) 0 = lowerBound β d := by
    simp only [T, Nat.sub_zero, mul_zero, pow_zero, one_mul,
      WeightedSchur.weight_zero, complete_kz_leading_coeff]
    unfold lowerBound
    ring
  rw [CoefficientSchur.powerCoeff_schur]
  exact hselected ▸ (hinner.trans houter)

theorem lowerBound_and_strict_of_complete_nonnegative
    (hH : ∀ k, CoefficientSchur.CoeffNonneg
      (Schur.complete CoefficientSchur.kzL CoefficientSchur.kzD k : FourPoly ℚ))
    (β : ℝ) (hβ : 1 ≤ β) (d : MultiIndex) :
    lowerBound β d ≤ powerCoeff 4 β d ∧ 0 < lowerBound β d := by
  exact ⟨lowerBound_le_of_complete_nonnegative hH β hβ d, lowerBound_pos (by linarith) d⟩

end Results.SharpPowersKz.LowerBound
