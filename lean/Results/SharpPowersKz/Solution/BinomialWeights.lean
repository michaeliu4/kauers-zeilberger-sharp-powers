import Results.SharpPowersKz.Solution.Basic
import Mathlib.RingTheory.Binomial

/-! Scalar identification with Mathlib's analytic binomial series. -/
namespace Results.SharpPowersKz

theorem smeval_ascPochhammer_eq_rising (β : ℝ) (n : ℕ) :
    (ascPochhammer ℕ n).smeval β = rising β n := by
  induction n with
  | zero => simp [rising]
  | succ n ih =>
    simp only [ascPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_add, Polynomial.smeval_X, Polynomial.smeval_natCast,
      pow_zero, pow_one, nsmul_eq_mul, mul_one, ih, rising_succ]

theorem binomialWeight_eq_multichoose (β : ℝ) (n : ℕ) :
    binomialWeight β n = Ring.multichoose β n := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer β n
  rw [smeval_ascPochhammer_eq_rising, nsmul_eq_mul] at h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  simp [binomialWeight, ← h, hn]

theorem choose_eq_binomialWeight (β : ℝ) (n : ℕ) :
    Ring.choose (β + n - 1) n = binomialWeight β n := by
  rw [binomialWeight_eq_multichoose, Ring.multichoose_eq]

end Results.SharpPowersKz
