import Results.SharpPowersKz.Solution.AlgebraRealPower
import Results.SharpPowersKz.Solution.AnalyticCoefficients
import Results.SharpPowersKz.Solution.AnalyticPropagation
import Results.SharpPowersKz.Solution.BinomialGerm
import Results.SharpPowersKz.Solution.Diagonal

namespace Results.SharpPowersKz

open Algebra

theorem not_nonnegativePower_gt_four {κ β : ℝ} (hκ : 4 < κ) (hβ : 0 < β) :
    ¬ NonnegativePower κ β := by
  intro h
  let T := diagonalPerturbation κ
  have hT : T.eval 0 = 0 := by simp [T, diagonalPerturbation]
  have hf : (fun t => (1 - T.eval t) ^ (-β)) =
      (fun t => (diagonalQuartic κ t) ^ (-β)) := by
    funext t
    congr 1
    simp [T, diagonalPerturbation, diagonalQuartic]
    ring
  have hjet : ∀ n, 0 ≤ iteratedDeriv n (fun t => (diagonalQuartic κ t) ^ (-β)) 0 := by
    intro n
    rw [← hf, AnalyticCoefficients.iteratedDeriv_comp_polynomial_zero
      (BinomialGerm.hasFPowerSeriesAt_inverse_one_sub β) T hT]
    exact mul_nonneg (Nat.cast_nonneg _) (diagonal_binomial_coefficient_nonneg κ β h n)
  have hnonneg := AnalyticPropagation.nonnegative_jet_on_Icc
    (fun t _ => analyticAt_diagonalQuartic_neg_rpow_of_gt_four hκ) hjet
    rho ⟨le_of_lt rho_pos, le_rfl⟩ 1
  rw [iteratedDeriv_one] at hnonneg
  exact (not_le_of_gt (deriv_diagonalQuartic_neg_rpow_at_rho_neg hκ hβ)) hnonneg

theorem quartic_obstruction (κ β : ℝ) (hκ : 4 < κ) (hβ : 0 < β) :
    ∃ d, powerCoeff κ β d < 0 := by
  by_contra h
  apply not_nonnegativePower_gt_four hκ hβ
  intro d
  exact le_of_not_gt fun hd => h ⟨d, hd⟩

end Results.SharpPowersKz
