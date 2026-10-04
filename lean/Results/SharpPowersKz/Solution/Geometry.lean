import Results.SharpPowersKz.Solution.Algebra

/-! Positivity of the denominator on the cube used in the tangent argument. -/

namespace Results.SharpPowersKz.Algebra

theorem coordinateSlope_at_rho :
    -1 + 6 * rho ^ 2 + 4 * rho ^ 3 = 0 := by
  have h := one_sub_two_mul_rho_sub_two_mul_rho_sq
  have hm := congrArg (fun t : ℝ => t * rho) h
  nlinarith

theorem coordinateSlope_nonpos {y z w : ℝ}
    (_hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hyr : y ≤ rho) (hzr : z ≤ rho) (hwr : w ≤ rho) :
    -1 + 2 * (y * z + y * w + z * w) + 4 * y * z * w ≤ 0 := by
  have hr := le_of_lt rho_pos
  have hyz : y * z ≤ rho * rho := mul_le_mul hyr hzr hz hr
  have hyw : y * w ≤ rho * rho := mul_le_mul hyr hwr hw hr
  have hzw : z * w ≤ rho * rho := mul_le_mul hzr hwr hw hr
  have hyzw : y * z * w ≤ rho * rho * rho :=
    mul_le_mul hyz hwr hw (mul_nonneg hr hr)
  have h := coordinateSlope_at_rho
  nlinarith

theorem pFour_replace_first {x y z w : ℝ}
    (hx : x ≤ rho) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hyr : y ≤ rho) (hzr : z ≤ rho) (hwr : w ≤ rho) :
    pκ 4 rho y z w ≤ pκ 4 x y z w := by
  have hs := coordinateSlope_nonpos hy hz hw hyr hzr hwr
  have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx) hs
  dsimp [pκ]
  nlinarith

theorem pFour_two_rho (z w : ℝ) :
    pκ 4 rho rho z w = 2 * (rho - z) * (rho - w) := by
  have h := one_sub_two_mul_rho_sub_two_mul_rho_sq
  have hz := congrArg (fun t : ℝ => t * z) h
  have hw := congrArg (fun t : ℝ => t * w) h
  have hzw := congrArg (fun t : ℝ => t * z * w) h
  dsimp [pκ]
  nlinarith

/-- The actual denominator is strictly positive throughout the half-open
positive cube, including its coordinate faces. -/
theorem pFour_pos_on_cube {x y z w : ℝ}
    (_hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hxr : x < rho) (hyr : y < rho) (hzr : z < rho) (hwr : w < rho) :
    0 < pκ 4 x y z w := by
  have h₁ := pFour_replace_first (le_of_lt hxr) hy hz hw
    (le_of_lt hyr) (le_of_lt hzr) (le_of_lt hwr)
  have h₂ := pFour_replace_first (le_of_lt hyr) (le_of_lt rho_pos) hz hw
    (le_refl rho) (le_of_lt hzr) (le_of_lt hwr)
  have hswap : pκ 4 y rho z w = pκ 4 rho y z w := by dsimp [pκ]; ring
  rw [hswap, pFour_two_rho] at h₂
  have hp : 0 < 2 * (rho - z) * (rho - w) := by
    exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hzr)) (sub_pos.mpr hwr)
  exact lt_of_lt_of_le hp (le_trans h₂ h₁)

end Results.SharpPowersKz.Algebra
