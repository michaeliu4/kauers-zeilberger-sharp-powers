import Results.SharpPowersKz.Solution.BinomialWeights
import Mathlib.Analysis.Analytic.Binomial

/-! Exact analytic germ for the literal finite formal binomial weights. -/

namespace Results.SharpPowersKz.BinomialGerm

open Set Filter
open scoped Topology

/-- The inverse real power has exactly the paper's rising-factorial weights
in its actual analytic expansion at zero. -/
theorem hasFPowerSeriesAt_inverse_one_sub (β : ℝ) :
    HasFPowerSeriesAt (fun t : ℝ => (1 - t) ^ (-β))
      (FormalMultilinearSeries.ofScalars ℝ (binomialWeight β)) 0 := by
  have hstock := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero β).hasFPowerSeriesAt
  have hweights : (fun n : ℕ => Ring.choose (β + n - 1) n) = binomialWeight β := by
    funext n
    exact choose_eq_binomialWeight β n
  rw [hweights] at hstock
  refine hstock.congr ?_
  filter_upwards [(Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))] with t ht
  rw [Real.rpow_neg (sub_nonneg.mpr (le_of_lt ht)) β, one_div]

end Results.SharpPowersKz.BinomialGerm
