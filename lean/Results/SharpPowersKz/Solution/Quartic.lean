import Results.SharpPowersKz.Solution.Basic
import Results.SharpPowersKz.Solution.Truncation
import Results.SharpPowersKz.Solution.WeightedSchur
import Results.SharpPowersKz.Solution.Specialization
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum

/-!
Exact finite coefficient expansion for perturbing the quartic parameter.
The identity is unconditional. Positivity transfers explicitly expose the
base positivity assumptions; they do not assert the unfinished main theorem.
-/

noncomputable section

namespace Results.SharpPowersKz.Quartic

open MvPolynomial

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def fullIndex : MultiIndex :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1

@[simp] theorem fullIndex_degree : degree fullIndex = 4 := by
  simp [fullIndex, degree_add]

theorem degree_nsmul (m : ℕ) (d : MultiIndex) : degree (m • d) = m * degree d := by
  induction m with
  | zero => simp
  | succ m ih => simp [succ_nsmul, degree_add, ih, Nat.succ_mul]

omit [Algebra ℚ A] in
theorem monomial_fullIndex (lam : A) :
    monomial fullIndex lam = C lam * X (0 : Fin 4) * X 1 * X 2 * X 3 := by
  simp [fullIndex, X, C_mul_monomial, monomial_mul]

omit [Algebra ℚ A] in
theorem perturbation_sub (lam : A) :
    perturbation (4 - lam) = monomial fullIndex lam + perturbation (4 : A) := by
  rw [monomial_fullIndex]
  simp only [perturbation, map_sub, map_ofNat]
  ring

theorem binomialWeight_mul_choose (β : A) {n m : ℕ} (hm : m ≤ n) :
    binomialWeight β n * (n.choose m : A) =
      binomialWeight β m * binomialWeight (β + m) (n - m) := by
  have hr := WeightedSchur.rising_add_length β m (n - m)
  rw [Nat.add_sub_of_le hm] at hr
  simp only [Schur.rising_eq_product] at hr
  change (WeightedSchur.factInv A n * rising β n) * _ =
    (WeightedSchur.factInv A m * rising β m) *
      (WeightedSchur.factInv A (n - m) * rising (β + m) (n - m))
  calc
    _ = (WeightedSchur.factInv A n * (n.choose m : A)) * rising β n := by ring
    _ = _ := by rw [WeightedSchur.factInv_mul_choose hm, hr]; ring

omit [Algebra ℚ A] in
theorem coeff_shift_pow (q : MvPolynomial (Fin 4) A) (lam : A)
    (n : ℕ) (d : MultiIndex) :
    ((monomial fullIndex lam + q) ^ n).coeff d =
      ∑ m ∈ Finset.range (n + 1),
        (n.choose m : A) *
          (if m • fullIndex ≤ d then lam ^ m * (q ^ (n - m)).coeff (d - m • fullIndex)
            else 0) := by
  classical
  rw [add_pow, coeff_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [monomial_pow]
  rw [show (monomial (m • fullIndex) (lam ^ m) * q ^ (n - m)) * (n.choose m : MvPolynomial (Fin 4) A) =
      C (n.choose m : A) * (monomial (m • fullIndex) (lam ^ m) * q ^ (n - m)) by
        simp only [map_natCast]; ring]
  rw [coeff_C_mul, coeff_monomial_mul']

theorem powerCoeff_triangular (lam β : A) (d : MultiIndex) :
    powerCoeff (4 - lam) β d =
      ∑ n ∈ Finset.range (degree d + 1), ∑ m ∈ Finset.range (n + 1),
        binomialWeight β m * binomialWeight (β + m) (n - m) *
          (if m • fullIndex ≤ d then
            lam ^ m * (perturbation (4 : A) ^ (n - m)).coeff (d - m • fullIndex)
          else 0) := by
  classical
  unfold powerCoeff
  rw [perturbation_sub]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coeff_shift_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← mul_assoc, binomialWeight_mul_choose β (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm)]

/-- The manuscript's quartic expansion, extracted coefficient by coefficient
from the defining finite binomial sum. Invalid residual indices contribute zero. -/
theorem powerCoeff_quartic_expansion (lam β : A) (d : MultiIndex) :
    powerCoeff (4 - lam) β d =
      ∑ m ∈ Finset.range (degree d + 1),
        if m • fullIndex ≤ d then
          binomialWeight β m * lam ^ m * powerCoeff 4 (β + m) (d - m • fullIndex)
        else 0 := by
  classical
  rw [powerCoeff_triangular, Finset.sum_range_diag_flip (degree d + 1)
    (fun m k => binomialWeight β m * binomialWeight (β + m) k *
      (if m • fullIndex ≤ d then
        lam ^ m * (perturbation (4 : A) ^ k).coeff (d - m • fullIndex) else 0))]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmd : m • fullIndex ≤ d
  · simp only [if_pos hmd]
    have hdegree : degree (d - m • fullIndex) + m * 4 = degree d := by
      have h := congrArg degree (tsub_add_cancel_of_le hmd)
      simpa only [degree_add, degree_nsmul, fullIndex_degree] using h
    have hbound : degree (d - m • fullIndex) ≤ degree d - m := by omega
    have hmN : m ≤ degree d := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
    have hrange : degree d + 1 - m = degree d - m + 1 := by omega
    rw [hrange, powerCoeff_eq_sum_of_degree_le 4 (β + m) (d - m • fullIndex)
      (degree d - m) hbound, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · simp [hmd]

/-- The quartic perturbation can only increase coefficients when all the
integer-shifted base exponents have nonnegative coefficients. -/
theorem powerCoeff_quartic_ge (lam β : ℝ) (hlam : 0 ≤ lam) (hβ : 0 < β)
    (hshift : ∀ m : ℕ, NonnegativePower 4 (β + m)) (d : MultiIndex) :
    powerCoeff 4 β d ≤ powerCoeff (4 - lam) β d := by
  classical
  rw [powerCoeff_quartic_expansion]
  have hterm (m : ℕ) : 0 ≤
      (if m • fullIndex ≤ d then
        binomialWeight β m * lam ^ m * powerCoeff 4 (β + m) (d - m • fullIndex)
      else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg (le_of_lt (binomialWeight_pos hβ m))
        (pow_nonneg hlam m)) (hshift m _)
    · exact le_refl 0
  have h := Finset.single_le_sum (fun m _ => hterm m)
    (Finset.mem_range.mpr (Nat.zero_lt_succ (degree d)))
  simpa using h

abbrev ParamPolynomial := MvPolynomial (Fin 2) ℚ

def ParamNonnegative (p : ParamPolynomial) : Prop := ∀ d, 0 ≤ p.coeff d

theorem param_C_nonnegative (r : ℚ) (hr : 0 ≤ r) : ParamNonnegative (C r) := by
  intro d
  simp only [coeff_C]
  split_ifs <;> positivity

theorem param_natCast_nonnegative (n : ℕ) : ParamNonnegative (n : ParamPolynomial) := by
  simpa only [map_natCast] using param_C_nonnegative (n : ℚ) (Nat.cast_nonneg n)

theorem param_X_nonnegative (i : Fin 2) : ParamNonnegative (X i) := by
  intro d
  simp only [coeff_X]
  split_ifs <;> norm_num

theorem param_add_nonnegative {p q : ParamPolynomial}
    (hp : ParamNonnegative p) (hq : ParamNonnegative q) : ParamNonnegative (p + q) := by
  intro d
  rw [coeff_add]
  exact add_nonneg (hp d) (hq d)

theorem param_mul_nonnegative {p q : ParamPolynomial}
    (hp : ParamNonnegative p) (hq : ParamNonnegative q) : ParamNonnegative (p * q) := by
  intro d
  rw [coeff_mul]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hp e.1) (hq e.2)

theorem param_pow_nonnegative {p : ParamPolynomial} (hp : ParamNonnegative p) (n : ℕ) :
    ParamNonnegative (p ^ n) := by
  induction n with
  | zero => simpa using param_natCast_nonnegative 1
  | succ n ih => rw [pow_succ]; exact param_mul_nonnegative ih hp

theorem param_rising_nonnegative {p : ParamPolynomial} (hp : ParamNonnegative p) (n : ℕ) :
    ParamNonnegative (rising p n) := by
  induction n with
  | zero => simpa using param_natCast_nonnegative 1
  | succ n ih =>
      rw [rising_succ]
      exact param_mul_nonnegative ih (param_add_nonnegative hp (param_natCast_nonnegative n))

theorem param_binomialWeight_nonnegative {p : ParamPolynomial}
    (hp : ParamNonnegative p) (n : ℕ) : ParamNonnegative (binomialWeight p n) := by
  unfold binomialWeight
  apply param_mul_nonnegative
  · change ParamNonnegative (C ((n.factorial : ℚ)⁻¹))
    exact param_C_nonnegative _ (by positivity)
  · exact param_rising_nonnegative hp n

theorem param_aeval_nonnegative (p : Polynomial ℚ) (hp : ∀ n, 0 ≤ p.coeff n)
    (q : ParamPolynomial) (hq : ParamNonnegative q) :
    ParamNonnegative (Polynomial.aeval q p) := by
  rw [Polynomial.aeval_eq_sum_range]
  intro d
  rw [coeff_sum]
  apply Finset.sum_nonneg
  intro n hn
  rw [MvPolynomial.smul_eq_C_mul]
  exact param_mul_nonnegative (param_C_nonnegative _ (hp n))
    (param_pow_nonnegative hq n) d

/-- The already-shifted base coefficient stays coefficientwise nonnegative
under substitution s ↦ s+m. This is explicitly conditional on main_shift. -/
theorem param_shift_nonnegative (hshift : ShiftNonnegative) (m : ℕ) (d : MultiIndex) :
    ParamNonnegative (powerCoeff (4 : ParamPolynomial) (1 + X 0 + (m : ParamPolynomial)) d) := by
  have h := param_aeval_nonnegative (shiftedCoeff d) (hshift d)
    (X 0 + (m : ParamPolynomial))
    (param_add_nonnegative (param_X_nonnegative 0) (param_natCast_nonnegative m))
  unfold shiftedCoeff at h
  rw [powerCoeff_map] at h
  simpa only [map_ofNat, map_add, map_one, Polynomial.aeval_X, add_assoc] using h

/-- Honest transfer theorem: the proved finite quartic expansion makes the
joint positivity conclusion follow from the single-parameter shift theorem.
This does not claim that main_shift has been proved. -/
theorem jointNonnegative_of_shift (hshift : ShiftNonnegative) : JointNonnegative := by
  classical
  intro d j
  unfold jointCoeff
  rw [powerCoeff_quartic_expansion, coeff_sum]
  apply Finset.sum_nonneg
  intro m hm
  by_cases hmd : m • fullIndex ≤ d
  · rw [if_pos hmd]
    exact param_mul_nonnegative
      (param_mul_nonnegative
        (param_binomialWeight_nonnegative
          (param_add_nonnegative (param_natCast_nonnegative 1) (param_X_nonnegative 0)) m)
        (param_pow_nonnegative (param_X_nonnegative 1) m))
      (param_shift_nonnegative hshift m _) j
  · simp [hmd]

end Results.SharpPowersKz.Quartic
