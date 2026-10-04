import Results.SharpPowersKz.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Elementary consequences of the literal finite binomial coefficient definition. -/
namespace Results.SharpPowersKz

section Generic
variable {A : Type*} [CommRing A]

@[simp] theorem rising_zero (β : A) : rising β 0 = 1 := by
  simp [rising]

@[simp] theorem rising_succ (β : A) (n : ℕ) :
    rising β (n + 1) = rising β n * (β + n) := by
  simp [rising, Finset.prod_range_succ]

@[simp] theorem rising_zero_succ (n : ℕ) : rising (0 : A) (n + 1) = 0 := by
  unfold rising
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  simp

variable [Algebra ℚ A]

@[simp] theorem binomialWeight_zero (β : A) : binomialWeight β 0 = 1 := by
  simp [binomialWeight]

@[simp] theorem binomialWeight_one (β : A) : binomialWeight β 1 = β := by
  simp [binomialWeight, rising]

@[simp] theorem binomialWeight_zero_succ (n : ℕ) : binomialWeight (0 : A) (n + 1) = 0 := by
  rw [binomialWeight, rising_zero_succ, mul_zero]

@[simp] theorem degree_zero : degree 0 = 0 := by simp [degree]

@[simp] theorem degree_single (i : Fin 4) (n : ℕ) :
    degree (Finsupp.single i n) = n := by simp [degree]

@[simp] theorem powerCoeff_constant (κ β : A) : powerCoeff κ β 0 = 1 := by
  simp [powerCoeff]

/-- Exponent zero gives the constant series one, for every quartic parameter. -/
theorem powerCoeff_zero_exponent (κ : A) (d : MultiIndex) :
    powerCoeff κ 0 d = if d = 0 then 1 else 0 := by
  classical
  unfold powerCoeff
  rw [Finset.sum_eq_single 0]
  · simp [MvPolynomial.coeff_one, eq_comm]
  · intro b hb hb0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    simp
  · simp

/-- The first coefficient detects every negative exponent. -/
theorem powerCoeff_x (κ β : A) :
    powerCoeff κ β (Finsupp.single 0 1) = β := by
  have hsub (p q : MvPolynomial (Fin 4) A) :
      (p - q).coeff (Finsupp.single 0 1) =
        p.coeff (Finsupp.single 0 1) - q.coeff (Finsupp.single 0 1) :=
    Finsupp.sub_apply _ _ _
  simp [hsub, powerCoeff, Finset.sum_range_succ, perturbation,
    MvPolynomial.coeff_mul_X',
    MvPolynomial.coeff_one, two_mul, eq_comm, Finsupp.single_eq_zero]

end Generic

theorem zero_exponent_nonnegative (κ : ℝ) : NonnegativePower κ 0 := by
  intro d
  rw [powerCoeff_zero_exponent]
  split_ifs <;> norm_num

theorem negative_exponent_not_nonnegative (κ β : ℝ) (hβ : β < 0) :
    ¬ NonnegativePower κ β := by
  intro h
  have hx := h (Finsupp.single 0 1)
  rw [powerCoeff_x] at hx
  exact (not_lt_of_ge hx) hβ

theorem rising_pos {β : ℝ} (hβ : 0 < β) (n : ℕ) : 0 < rising β n := by
  unfold rising
  exact Finset.prod_pos fun i _ => add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg i)

theorem binomialWeight_pos {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    0 < binomialWeight β n := by
  unfold binomialWeight
  have hf : (0 : ℚ) < n.factorial := by positivity
  have hm : (0 : ℝ) < algebraMap ℚ ℝ ((n.factorial : ℚ)⁻¹) := by
    change (0 : ℝ) < (((n.factorial : ℚ)⁻¹ : ℚ) : ℝ)
    exact_mod_cast (inv_pos.mpr hf)
  exact mul_pos hm (rising_pos hβ n)

/-- Strictness of the explicit bound, independently of the hard comparison. -/
theorem lowerBound_pos {β : ℝ} (hβ : 0 < β) (d : MultiIndex) :
    0 < lowerBound β d := by
  unfold lowerBound
  have h01 : 0 < (d 0 + d 1).choose (d 0) := Nat.choose_pos (Nat.le_add_right _ _)
  have h23 : 0 < (d 2 + d 3).choose (d 2) := Nat.choose_pos (Nat.le_add_right _ _)
  exact mul_pos (mul_pos (binomialWeight_pos hβ _) (by exact_mod_cast h01))
    (by exact_mod_cast h23)

end Results.SharpPowersKz
