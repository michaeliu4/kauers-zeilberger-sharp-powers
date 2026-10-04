import Results.SharpPowersKz.Defs

/-!
The finite binomial coefficient definition discards only zero terms.  The
argument uses minimum monomial degree, not a positivity formula for KZ.
-/

namespace Results.SharpPowersKz

theorem degree_add (d e : MultiIndex) : degree (d + e) = degree d + degree e := by
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem degree_eq_zero_iff (d : MultiIndex) : degree d = 0 ↔ d = 0 := by
  classical
  constructor
  · intro hd
    apply Finsupp.ext
    intro i
    change d i = 0
    by_cases hi : i ∈ d.support
    · exact (Finset.sum_eq_zero_iff.mp hd) i hi
    · exact Finsupp.notMem_support_iff.mp hi
  · rintro rfl
    simp [degree]

section General

variable {A : Type*} [CommSemiring A]

/-- A nonconstant monomial in a polynomial with zero constant term has
positive total degree. -/
theorem one_le_degree_of_mem_support (p : MvPolynomial (Fin 4) A)
    (hp : p.coeff 0 = 0) (d : MultiIndex) (hd : d ∈ p.support) :
    1 ≤ degree d := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hdegree
  have hzero : d = 0 := (degree_eq_zero_iff d).mp hdegree
  rw [hzero] at hd
  exact (MvPolynomial.mem_support_iff.mp hd) hp

/-- Every monomial occurring in the `n`th power has degree at least `n`. -/
theorem le_degree_of_mem_pow_support (p : MvPolynomial (Fin 4) A)
    (hp : p.coeff 0 = 0) (n : ℕ) (d : MultiIndex)
    (hd : d ∈ (p ^ n).support) : n ≤ degree d := by
  classical
  induction n generalizing d with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      rw [pow_succ] at hd
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        Finset.mem_add.mp (MvPolynomial.support_mul (p ^ n) p hd)
      rw [degree_add]
      exact Nat.add_le_add (ih a ha) (one_le_degree_of_mem_support p hp b hb)

/-- Coefficients beyond the degree cutoff vanish for any polynomial with
zero constant coefficient. -/
theorem coeff_pow_eq_zero_of_degree_lt (p : MvPolynomial (Fin 4) A)
    (hp : p.coeff 0 = 0) (n : ℕ) (d : MultiIndex) (hd : degree d < n) :
    (p ^ n).coeff d = 0 := by
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  exact (Nat.not_le_of_gt hd) (le_degree_of_mem_pow_support p hp n d hmem)

end General

section Perturbation

variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
@[simp]
theorem perturbation_coeff_zero (κ : A) : (perturbation κ).coeff 0 = 0 := by
  change MvPolynomial.constantCoeff (perturbation κ) = 0
  simp [perturbation]

omit [Algebra ℚ A] in
theorem perturbation_pow_coeff_eq_zero (κ : A) (n : ℕ) (d : MultiIndex)
    (hd : degree d < n) : (perturbation κ ^ n).coeff d = 0 :=
  coeff_pow_eq_zero_of_degree_lt (perturbation κ) (perturbation_coeff_zero κ) n d hd

/-- Increasing the inclusive cutoff past total degree leaves the finite
binomial coefficient unchanged. -/
theorem powerCoeff_eq_sum_of_degree_le (κ β : A) (d : MultiIndex) (M : ℕ)
    (hM : degree d ≤ M) :
    powerCoeff κ β d = ∑ n ∈ Finset.range (M + 1),
      binomialWeight β n * (perturbation κ ^ n).coeff d := by
  classical
  unfold powerCoeff
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hM 1))
  intro n _ hn
  have hlarge : degree d < n := by
    apply Nat.lt_of_lt_of_le (Nat.lt_succ_self (degree d))
    apply Nat.le_of_not_gt
    intro hlt
    exact hn (Finset.mem_range.mpr hlt)
  rw [perturbation_pow_coeff_eq_zero κ n d hlarge, mul_zero]

end Perturbation

end Results.SharpPowersKz
