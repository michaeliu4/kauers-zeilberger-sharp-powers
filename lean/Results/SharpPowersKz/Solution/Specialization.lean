import Results.SharpPowersKz.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Parameter specialization commutes with the actual finite coefficient definition. -/
namespace Results.SharpPowersKz

section Generic
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

theorem rising_map (f : A →ₐ[ℚ] B) (β : A) (n : ℕ) :
    f (rising β n) = rising (f β) n := by
  simp [rising, map_prod]

theorem binomialWeight_map (f : A →ₐ[ℚ] B) (β : A) (n : ℕ) :
    f (binomialWeight β n) = binomialWeight (f β) n := by
  simp [binomialWeight, rising_map]

theorem perturbation_map (f : A →ₐ[ℚ] B) (κ : A) :
    MvPolynomial.map f.toRingHom (perturbation κ) = perturbation (f κ) := by
  simp [perturbation]

theorem powerCoeff_map (f : A →ₐ[ℚ] B) (κ β : A) (d : MultiIndex) :
    f (powerCoeff κ β d) = powerCoeff (f κ) (f β) d := by
  simp only [powerCoeff, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, binomialWeight_map]
  congr 1
  change f.toRingHom ((perturbation κ ^ n).coeff d) = _
  rw [← MvPolynomial.coeff_map f.toRingHom, map_pow, perturbation_map]

end Generic

theorem shiftedCoeff_aeval (s : ℝ) (d : MultiIndex) :
    Polynomial.aeval s (shiftedCoeff d) = powerCoeff 4 (1 + s) d := by
  unfold shiftedCoeff
  rw [powerCoeff_map]
  simp [map_ofNat]

theorem polynomial_aeval_nonneg (p : Polynomial ℚ) (hp : ∀ n, 0 ≤ p.coeff n)
    (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Polynomial.aeval s p := by
  rw [Polynomial.aeval_eq_sum_range]
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · exact_mod_cast hp i
  · exact pow_nonneg hs i

/-- An honest reduction: the polynomial-shift theorem implies real positivity.
The shift theorem is an explicit hypothesis here, not a proved main theorem. -/
theorem nonnegativePower_of_shift (hshift : ShiftNonnegative) (β : ℝ) (hβ : 1 ≤ β) :
    NonnegativePower 4 β := by
  intro d
  have h := polynomial_aeval_nonneg (shiftedCoeff d) (hshift d) (β - 1) (by linarith)
  rw [shiftedCoeff_aeval] at h
  simpa using h

theorem jointCoeff_aeval (s lam : ℝ) (d : MultiIndex) :
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then s else lam) (jointCoeff d) =
      powerCoeff (4 - lam) (1 + s) d := by
  unfold jointCoeff
  rw [powerCoeff_map]
  simp [map_ofNat]

theorem mvPolynomial_aeval_nonneg {σ : Type*} (p : MvPolynomial σ ℚ)
    (hp : ∀ d, 0 ≤ p.coeff d) (v : σ → ℝ) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ MvPolynomial.aeval v p := by
  change 0 ≤ p.eval₂ (algebraMap ℚ ℝ) v
  rw [MvPolynomial.eval₂_eq]
  apply Finset.sum_nonneg
  intro d hd
  apply mul_nonneg
  · change 0 ≤ ((p.coeff d : ℚ) : ℝ)
    exact_mod_cast hp d
  · exact Finset.prod_nonneg fun i hi => pow_nonneg (hv i) _

/-- Specializing a joint coefficient polynomial with nonnegative parameters
preserves nonnegativity. The joint theorem remains an explicit hypothesis. -/
theorem nonnegativePower_of_joint (hjoint : JointNonnegative)
    (κ β : ℝ) (hκ : κ ≤ 4) (hβ : 1 ≤ β) : NonnegativePower κ β := by
  intro d
  have h := mvPolynomial_aeval_nonneg (jointCoeff d) (hjoint d)
    (fun i : Fin 2 => if i = 0 then β - 1 else 4 - κ) (by
      intro i
      split_ifs <;> linarith)
  rw [jointCoeff_aeval] at h
  simpa using h

end Results.SharpPowersKz
