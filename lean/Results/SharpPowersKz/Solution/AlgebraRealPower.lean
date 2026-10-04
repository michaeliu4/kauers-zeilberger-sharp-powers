import Results.SharpPowersKz.Solution.AlgebraCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp

/-!
# The derivative obstruction above the quartic boundary

This leaf combines the algebraic derivative at `rho` with the chain rule for
real powers.
-/

open scoped Topology

namespace Results.SharpPowersKz.Algebra

/-- A negative real power of the diagonal quartic is real analytic at every
point where the quartic is positive. -/
theorem analyticAt_diagonalQuartic_neg_rpow
    (κ β t : ℝ) (ht : 0 < diagonalQuartic κ t) :
    AnalyticAt ℝ (fun u => (diagonalQuartic κ u) ^ (-β)) t := by
  have hpoly : AnalyticAt ℝ (diagonalQuartic κ) t := by
    unfold diagonalQuartic
    fun_prop
  have hpos : ∀ᶠ u in 𝓝 t, 0 < diagonalQuartic κ u :=
    hpoly.continuousAt.eventually_mem (isOpen_Ioi.mem_nhds ht)
  have hexp :
      AnalyticAt ℝ (fun u => Real.exp (Real.log (diagonalQuartic κ u) * (-β))) t :=
    ((hpoly.log ht).mul analyticAt_const).rexp'
  apply hexp.congr
  exact hpos.mono fun u hu => (Real.rpow_def_of_pos hu (-β)).symm

/-- For `κ > 4`, the inverse real power is analytic on the whole real axis. -/
theorem analyticAt_diagonalQuartic_neg_rpow_of_gt_four
    {κ β t : ℝ} (hκ : 4 < κ) :
    AnalyticAt ℝ (fun u => (diagonalQuartic κ u) ^ (-β)) t :=
  analyticAt_diagonalQuartic_neg_rpow κ β t (diagonalQuartic_pos_all hκ)

/-- On this positive quartic, the reciprocal of the `β`-th real power is
globally the real power with exponent `-β`. -/
theorem inv_rpow_diagonalQuartic_eq_neg_rpow
    {κ : ℝ} (hκ : 4 < κ) (β t : ℝ) :
    ((diagonalQuartic κ t) ^ β)⁻¹ = (diagonalQuartic κ t) ^ (-β) := by
  exact (Real.rpow_neg (diagonalQuartic_pos_all hκ).le β).symm

/-- Chain-rule formula for the negative real power of the diagonal quartic
at the old double root. -/
theorem hasDerivAt_diagonalQuartic_neg_rpow_at_rho
    {κ β : ℝ} (hκ : 4 < κ) :
    HasDerivAt (fun t => (diagonalQuartic κ t) ^ (-β))
      (diagonalQuarticDeriv κ rho * (-β) *
        (diagonalQuartic κ rho) ^ (-β - 1)) rho := by
  apply (hasDerivAt_diagonalQuartic κ rho).rpow_const
  left
  exact ne_of_gt (diagonalQuartic_pos hκ rho_pos.le)

/-- If `κ > 4` and `β > 0`, the derivative of the inverse real power of
the diagonal quartic is strictly negative at `rho`. -/
theorem deriv_diagonalQuartic_neg_rpow_at_rho_neg
    {κ β : ℝ} (hκ : 4 < κ) (hβ : 0 < β) :
    deriv (fun t => (diagonalQuartic κ t) ^ (-β)) rho < 0 := by
  rw [(hasDerivAt_diagonalQuartic_neg_rpow_at_rho hκ).deriv]
  have hbase : 0 < diagonalQuartic κ rho := diagonalQuartic_pos hκ rho_pos.le
  have hpow : 0 < (diagonalQuartic κ rho) ^ (-β - 1) :=
    Real.rpow_pos_of_pos hbase _
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (diagonalQuarticDeriv_at_rho_pos hκ) (neg_neg_of_pos hβ)) hpow

end Results.SharpPowersKz.Algebra
