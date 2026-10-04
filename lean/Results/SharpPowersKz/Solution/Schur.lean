import Results.SharpPowersKz.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary scalar factors in the two-variable Schur expansion

This file proves the rising-factorial algebra and positivity of the scalar
factors.  It does not assert the formal-series Schur expansion or the
nonnegativity of the specialized complete homogeneous polynomials.
-/

noncomputable section

namespace Results.SharpPowersKz.Schur

/-- Rising factorial, with a definition usable in a polynomial coefficient ring. -/
def rising {R : Type*} [CommSemiring R] (b : R) : ℕ → R
  | 0 => 1
  | n + 1 => rising b n * (b + n)

@[simp] theorem rising_zero {R : Type*} [CommSemiring R] (b : R) :
    rising b 0 = 1 := rfl

@[simp] theorem rising_succ {R : Type*} [CommSemiring R] (b : R) (n : ℕ) :
    rising b (n + 1) = rising b n * (b + n) := rfl

theorem rising_eq_product {R : Type*} [CommRing R] [Algebra ℚ R] (b : R) (n : ℕ) :
    rising b n = Results.SharpPowersKz.rising b n := by
  induction n with
  | zero => simp [Results.SharpPowersKz.rising]
  | succ n ih =>
      simpa only [rising_succ, Results.SharpPowersKz.rising, Finset.prod_range_succ]
        using congrArg (fun z => z * (b + n)) ih

theorem map_rising {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (b : R) (n : ℕ) : f (rising b n) = rising (f b) n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [rising_succ, map_mul, map_add, map_natCast, ih]

theorem rising_start_succ {R : Type*} [CommSemiring R] (b : R) (n : ℕ) :
    rising b (n + 1) = b * rising (b + 1) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rising_succ, ih, rising_succ]
      push_cast
      ring

theorem rising_sub_one {R : Type*} [CommRing R] (b : R) (n : ℕ) :
    rising (b - 1) (n + 1) = (b - 1) * rising b n := by
  simpa using rising_start_succ (b - 1) n

/-- The division-free adjacent-minor identity underlying the Schur coefficient.
It is valid polynomially, including at zeros of either rising factorial. -/
theorem adjacent_minor_numerator {R : Type*} [CommRing R] (b : R) (p q : ℕ) :
    ((p : R) + 1) * rising b p * rising b (q + 1) -
        ((q : R) + 1) * rising b (p + 1) * rising b q =
      ((p : R) - q) * rising b p * rising (b - 1) (q + 1) := by
  rw [rising_succ, rising_succ, rising_sub_one]
  ring

/-- Finite telescoping of adjacent minors: the coefficient computation in a
two-variable Schur expansion reduces to this identity. -/
theorem adjacent_sum {R : Type*} [CommRing R] (f : ℕ → R) (m : ℕ) :
    (∑ q ∈ Finset.range (m + 1),
      if q = 0 then f 0 else f q - f (q - 1)) = f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      ring

/-- Adjacent minors in homogeneous degree `n`, with the missing index -1
interpreted as zero. -/
def minor {R : Type*} [CommRing R] (a : ℕ → R) (n q : ℕ) : R :=
  if q = 0 then a n * a 0 else a (n - q) * a q - a (n - q + 1) * a (q - 1)

/-- Every coefficient of the finite homogeneous Schur expansion telescopes
to the corresponding product coefficient. -/
theorem minor_sum {R : Type*} [CommRing R] (a : ℕ → R) {n j : ℕ} (hj : j ≤ n) :
    (∑ q ∈ Finset.range (min j (n - j) + 1), minor a n q) = a j * a (n - j) := by
  calc
    (∑ q ∈ Finset.range (min j (n - j) + 1), minor a n q) =
        ∑ q ∈ Finset.range (min j (n - j) + 1),
          if q = 0 then a (n - 0) * a 0 else
            a (n - q) * a q - a (n - (q - 1)) * a (q - 1) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' : q ≤ n := by simp only [Finset.mem_range] at hq; omega
      unfold minor
      split_ifs with h
      · simp
      · rw [show n - (q - 1) = n - q + 1 by omega]
    _ = a (n - min j (n - j)) * a (min j (n - j)) :=
      adjacent_sum (fun q => a (n - q) * a q) _
    _ = a j * a (n - j) := by
      by_cases h : j ≤ n - j
      · rw [min_eq_left h]
        ring
      · rw [min_eq_right (by omega), show n - (n - j) = j by omega]

/-- Complete homogeneous polynomials in two roots, expressed in their sum
and product. Positivity after the KZ substitution is a separate theorem. -/
def complete {R : Type*} [CommRing R] (L D : R) : ℕ → R
  | 0 => 1
  | 1 => L
  | n + 2 => L * complete L D (n + 1) - D * complete L D n

@[simp] theorem complete_zero {R : Type*} [CommRing R] (L D : R) :
    complete L D 0 = 1 := rfl

@[simp] theorem complete_one {R : Type*} [CommRing R] (L D : R) :
    complete L D 1 = L := rfl

theorem complete_add_two {R : Type*} [CommRing R] (L D : R) (n : ℕ) :
    complete L D (n + 2) = L * complete L D (n + 1) - D * complete L D n := rfl

theorem complete_roots_succ {R : Type*} [CommRing R] (l m : R) (n : ℕ) :
    complete (l + m) (l * m) (n + 1) =
      l * complete (l + m) (l * m) n + m ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, complete_add_two]
      simp only [ih, pow_succ]
      ring

theorem map_complete {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (L D : R) (n : ℕ) :
    f (complete L D n) = complete (f L) (f D) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => simp only [complete_add_two, map_sub, map_mul, ih₀, ih₁]

theorem complete_roots_coeff {R : Type*} [CommRing R] (m : R) (n j : ℕ) :
    (complete (Polynomial.X + Polynomial.C m) (Polynomial.X * Polynomial.C m) n).coeff j =
      if j ≤ n then m ^ (n - j) else 0 := by
  induction n generalizing j with
  | zero =>
      cases j <;> simp [Polynomial.coeff_one]
  | succ n ih =>
      rw [complete_roots_succ, ← Polynomial.C_pow, Polynomial.coeff_add]
      cases j with
      | zero =>
          rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_zero, zero_add]
          simp
      | succ j =>
          rw [Polynomial.coeff_X_mul,
            Polynomial.coeff_C_of_ne_zero (by omega), add_zero]
          simpa using ih j

theorem schur_basis_coeff {R : Type*} [CommRing R] (m : R) {n q : ℕ}
    (hq : 2 * q ≤ n) (j : ℕ) :
    (((Polynomial.X * Polynomial.C m) ^ q) *
      complete (Polynomial.X + Polynomial.C m) (Polynomial.X * Polynomial.C m)
        (n - 2 * q)).coeff j =
      if q ≤ j ∧ j ≤ n - q then m ^ (n - j) else 0 := by
  have heq : ((Polynomial.X * Polynomial.C m) ^ q) *
      complete (Polynomial.X + Polynomial.C m) (Polynomial.X * Polynomial.C m) (n - 2 * q) =
        Polynomial.C (m ^ q) * (Polynomial.X ^ q *
          complete (Polynomial.X + Polynomial.C m) (Polynomial.X * Polynomial.C m)
            (n - 2 * q)) := by
    rw [mul_pow, map_pow]
    ring
  rw [heq, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', complete_roots_coeff]
  by_cases h : q ≤ j ∧ j ≤ n - q
  · rw [if_pos h, if_pos h.1, if_pos (by omega), ← pow_add]
    congr 1
    omega
  · rw [if_neg h]
    by_cases hj : q ≤ j
    · rw [if_pos hj, if_neg (by omega), mul_zero]
    · rw [if_neg hj, mul_zero]

/-- The full homogeneous-degree Schur identity, as a polynomial in the first
root. The second root and all sequence entries belong to an arbitrary ring. -/
theorem homogeneous_schur_polynomial {R : Type*} [CommRing R]
    (a : ℕ → R) (m : R) (n : ℕ) :
    (∑ q ∈ Finset.range (n / 2 + 1),
      Polynomial.C (minor a n q) * ((Polynomial.X * Polynomial.C m) ^ q *
        complete (Polynomial.X + Polynomial.C m) (Polynomial.X * Polynomial.C m)
          (n - 2 * q))) =
      ∑ j ∈ Finset.range (n + 1),
        Polynomial.C (a j * a (n - j) * m ^ (n - j)) * Polynomial.X ^ j := by
  apply Polynomial.ext
  intro j
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hb : (∑ q ∈ Finset.range (n / 2 + 1),
      minor a n q *
        (((Polynomial.X * Polynomial.C m) ^ q) *
          complete (Polynomial.X + Polynomial.C m) (Polynomial.X * Polynomial.C m)
            (n - 2 * q)).coeff j) =
      ∑ q ∈ Finset.range (n / 2 + 1),
        minor a n q * (if q ≤ j ∧ j ≤ n - q then m ^ (n - j) else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [schur_basis_coeff m (by simp only [Finset.mem_range] at hq; omega)]
  rw [hb]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hj : j ≤ n
  · rw [if_pos (by omega)]
    have hsub : Finset.range (min j (n - j) + 1) ⊆ Finset.range (n / 2 + 1) := by
      intro q hq
      simp only [Finset.mem_range] at *
      omega
    rw [← Finset.sum_subset hsub (by
      intro q hq hnot
      simp only [Finset.mem_range] at hq hnot
      rw [if_neg (by omega)])]
    calc
      (∑ q ∈ Finset.range (min j (n - j) + 1),
          if q ≤ j ∧ j ≤ n - q then minor a n q * m ^ (n - j) else 0) =
          ∑ q ∈ Finset.range (min j (n - j) + 1), minor a n q * m ^ (n - j) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [Finset.mem_range] at hq
        rw [if_pos (by omega)]
      _ = a j * a (n - j) * m ^ (n - j) := by
        rw [← Finset.sum_mul, minor_sum a hj]
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg (by omega)]

/-- Finite two-variable Schur expansion in homogeneous degree `n`. This is
an equality in any commutative ring; no convergence or positivity is assumed. -/
theorem homogeneous_schur {R : Type*} [CommRing R]
    (a : ℕ → R) (l m : R) (n : ℕ) :
    (∑ q ∈ Finset.range (n / 2 + 1),
      minor a n q * ((l * m) ^ q * complete (l + m) (l * m) (n - 2 * q))) =
      ∑ j ∈ Finset.range (n + 1), a j * a (n - j) * m ^ (n - j) * l ^ j := by
  have h := congrArg (Polynomial.evalRingHom l) (homogeneous_schur_polynomial a m n)
  simpa only [map_sum, map_mul, map_pow, map_complete, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_mul] using h

/-- The two-variable alternant identity used to extract Schur coefficients. -/
theorem complete_alternant {R : Type*} [CommRing R] (l m : R) (n : ℕ) :
    (l - m) * complete (l + m) (l * m) n = l ^ (n + 1) - m ^ (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp only [complete_one]; ring
  | more n ih₀ ih₁ =>
      calc
        (l - m) * complete (l + m) (l * m) (n + 2) =
            (l + m) * ((l - m) * complete (l + m) (l * m) (n + 1)) -
              (l * m) * ((l - m) * complete (l + m) (l * m) n) := by
                rw [complete_add_two]
                ring
        _ = (l + m) * (l ^ (n + 1 + 1) - m ^ (n + 1 + 1)) -
              (l * m) * (l ^ (n + 1) - m ^ (n + 1)) := by rw [ih₀, ih₁]
        _ = l ^ (n + 2 + 1) - m ^ (n + 2 + 1) := by
              simp only [pow_succ]
              ring

theorem schur_alternant {R : Type*} [CommRing R] (l m : R) {p q : ℕ}
    (hqp : q ≤ p) :
    (l - m) * (l * m) ^ q * complete (l + m) (l * m) (p - q) =
      l ^ (p + 1) * m ^ q - l ^ q * m ^ (p + 1) := by
  have hn : p - q + 1 + q = p + 1 := by omega
  calc
    (l - m) * (l * m) ^ q * complete (l + m) (l * m) (p - q) =
        (l * m) ^ q * ((l - m) * complete (l + m) (l * m) (p - q)) := by ring
    _ = (l * m) ^ q * (l ^ (p - q + 1) - m ^ (p - q + 1)) := by
          rw [complete_alternant]
    _ = l ^ (p - q + 1 + q) * m ^ q - l ^ q * m ^ (p - q + 1 + q) := by
          simp only [mul_pow, pow_add]
          ring
    _ = l ^ (p + 1) * m ^ q - l ^ q * m ^ (p + 1) := by rw [hn]

theorem rising_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 ≤ rising b n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rising_succ]
      exact mul_nonneg ih (add_nonneg hb (Nat.cast_nonneg n))

theorem rising_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < rising b n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rising_succ]
      exact mul_pos ih (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n))

/-- The scalar multiplying `R^q H_(p-q)` in the paper. -/
def weight (b : ℝ) (p q : ℕ) : ℝ :=
  (((p : ℝ) - q + 1) * rising b p * rising (b - 1) q) /
    ((p + 1).factorial * q.factorial)

theorem weight_nonneg {b : ℝ} (hb : 1 ≤ b) {p q : ℕ} (hqp : q ≤ p) :
    0 ≤ weight b p q := by
  unfold weight
  apply div_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · have h : (q : ℝ) ≤ p := by exact_mod_cast hqp
        linarith
      · exact rising_nonneg (by linarith) p
    · exact rising_nonneg (by linarith) q
  · positivity

theorem weight_zero (b : ℝ) (p : ℕ) :
    weight b p 0 = rising b p / p.factorial := by
  unfold weight
  simp only [Nat.cast_zero, sub_zero, rising_zero, mul_one, Nat.factorial_zero,
    Nat.cast_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem weight_succ_eq_adjacent_minor (b : ℝ) (p q : ℕ) :
    weight b p (q + 1) =
      rising b p / (p.factorial : ℝ) *
        (rising b (q + 1) / ((q + 1).factorial : ℝ)) -
      rising b (p + 1) / ((p + 1).factorial : ℝ) *
        (rising b q / (q.factorial : ℝ)) := by
  unfold weight
  rw [rising_sub_one, rising_succ, rising_succ]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem minor_binomial_eq_weight (b : ℝ) (n q : ℕ) :
    minor (fun k => rising b k / (k.factorial : ℝ)) n q = weight b (n - q) q := by
  cases q with
  | zero => simp [minor, weight_zero]
  | succ q =>
      rw [weight_succ_eq_adjacent_minor]
      simp [minor]

/-- The complete finite homogeneous-degree identity for the inverse-power
Schur expansion after the elementary-symmetric substitution. -/
theorem inverse_power_schur_degree (b l m : ℝ) (n : ℕ) :
    (∑ q ∈ Finset.range (n / 2 + 1),
      weight b (n - q) q *
        ((l * m) ^ q * complete (l + m) (l * m) (n - 2 * q))) =
      ∑ j ∈ Finset.range (n + 1),
        (rising b j / (j.factorial : ℝ)) *
        (rising b (n - j) / ((n - j).factorial : ℝ)) * m ^ (n - j) * l ^ j := by
  simpa only [minor_binomial_eq_weight] using
    homogeneous_schur (fun k => rising b k / (k.factorial : ℝ)) l m n

/-- Coefficientwise nonnegativity of a rational polynomial. -/
def PolyNonneg (f : Polynomial ℚ) : Prop := ∀ n, 0 ≤ f.coeff n

theorem polyNonneg_one : PolyNonneg 1 := by
  intro n
  simp only [Polynomial.coeff_one]
  split_ifs <;> norm_num

theorem polyNonneg_add {f g : Polynomial ℚ} (hf : PolyNonneg f) (hg : PolyNonneg g) :
    PolyNonneg (f + g) := by
  intro n
  rw [Polynomial.coeff_add]
  exact add_nonneg (hf n) (hg n)

theorem polyNonneg_mul {f g : Polynomial ℚ} (hf : PolyNonneg f) (hg : PolyNonneg g) :
    PolyNonneg (f * g) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hf a.1) (hg a.2)

theorem polyNonneg_C {c : ℚ} (hc : 0 ≤ c) : PolyNonneg (Polynomial.C c) := by
  intro n
  simp only [Polynomial.coeff_C]
  split_ifs <;> positivity

theorem polyNonneg_X : PolyNonneg Polynomial.X := by
  intro n
  simp only [Polynomial.coeff_X]
  split_ifs <;> norm_num

theorem polyNonneg_natCast (n : ℕ) : PolyNonneg (n : Polynomial ℚ) := by
  simpa using polyNonneg_C (c := (n : ℚ)) (Nat.cast_nonneg n)

theorem polyNonneg_rising {f : Polynomial ℚ} (hf : PolyNonneg f) (n : ℕ) :
    PolyNonneg (rising f n) := by
  induction n with
  | zero => exact polyNonneg_one
  | succ n ih =>
      exact polyNonneg_mul ih (polyNonneg_add hf (polyNonneg_natCast n))

/-- The weight after replacing the exponent by `1+s`, as a rational polynomial. -/
def shiftedWeight (p q : ℕ) : Polynomial ℚ :=
  Polynomial.C (((p : ℚ) - q + 1) / ((p + 1).factorial * q.factorial)) *
    rising (Polynomial.X + 1) p * rising Polynomial.X q

theorem shiftedWeight_nonneg {p q : ℕ} (hqp : q ≤ p) :
    PolyNonneg (shiftedWeight p q) := by
  unfold shiftedWeight
  apply polyNonneg_mul
  · apply polyNonneg_mul
    · apply polyNonneg_C
      apply div_nonneg
      · have h : (q : ℚ) ≤ p := by exact_mod_cast hqp
        linarith
      · positivity
    · exact polyNonneg_rising (polyNonneg_add polyNonneg_X polyNonneg_one) p
  · exact polyNonneg_rising polyNonneg_X q

theorem eval_shiftedWeight (s : ℝ) (p q : ℕ) :
    (shiftedWeight p q).eval₂ (algebraMap ℚ ℝ) s = weight (1 + s) p q := by
  change Polynomial.eval₂RingHom (algebraMap ℚ ℝ) s (shiftedWeight p q) = _
  unfold shiftedWeight weight
  rw [map_mul, map_mul, map_rising, map_rising]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X,
    map_div₀, map_sub, map_add, map_mul, map_natCast, map_one]
  rw [show 1 + s - 1 = s by ring, add_comm s 1]
  ring

end Results.SharpPowersKz.Schur
