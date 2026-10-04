import Results.SharpPowersKz.Solution.SixSpecialization
import Results.SharpPowersKz.Solution.LowerBound
import Results.SharpPowersKz.Solution.Quartic

/-! Positive conclusions with the general MacMahon master theorem exposed as
an explicit hypothesis. All specialized algebraic bridges are proved. -/

namespace Results.SharpPowersKz

theorem main_shift_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem) :
    ShiftNonnegative :=
  SixSpecialization.shiftNonnegative_of_macMahon hMMT

theorem main_lower_bound_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem)
    (β : ℝ) (hβ : 1 ≤ β) (d : MultiIndex) :
    lowerBound β d ≤ powerCoeff 4 β d ∧ 0 < lowerBound β d :=
  LowerBound.lowerBound_and_strict_of_complete_nonnegative
    (SixSpecialization.complete_nonnegative_of_macMahon hMMT) β hβ d

theorem main_positive_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem)
    (β : ℝ) (hβ : 1 ≤ β) : PositivePower 4 β := by
  intro d
  have h := main_lower_bound_of_macMahon hMMT β hβ d
  exact lt_of_lt_of_le h.2 h.1

/-- The sufficient direction of the sharp exponent classification. -/
theorem main_range_reverse_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem)
    (β : ℝ) (hβ : β = 0 ∨ 1 ≤ β) : NonnegativePower 4 β := by
  rcases hβ with rfl | hβ
  · exact zero_exponent_nonnegative 4
  · exact nonnegativePower_of_shift (main_shift_of_macMahon hMMT) β hβ

theorem quartic_joint_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem) :
    JointNonnegative :=
  Quartic.jointNonnegative_of_shift (main_shift_of_macMahon hMMT)

/-- The sufficient direction of the sharp quartic-parameter classification. -/
theorem quartic_range_reverse_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem)
    (κ β : ℝ) (hκ : κ ≤ 4) (hβ : 1 ≤ β) : NonnegativePower κ β :=
  nonnegativePower_of_joint (quartic_joint_of_macMahon hMMT) κ β hκ hβ

theorem quartic_strict_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem)
    (κ β : ℝ) (hκ : κ ≤ 4) (hβ : 1 ≤ β) : PositivePower κ β := by
  have hshift (m : ℕ) : NonnegativePower 4 (β + m) :=
    nonnegativePower_of_shift (main_shift_of_macMahon hMMT) (β + m)
      (le_trans hβ (le_add_of_nonneg_right (Nat.cast_nonneg m)))
  intro d
  have hge := Quartic.powerCoeff_quartic_ge (4 - κ) β (by linarith)
    (by linarith) hshift d
  have hpos := main_positive_of_macMahon hMMT β hβ d
  have h := lt_of_lt_of_le hpos hge
  simpa only [sub_sub_cancel] using h

end Results.SharpPowersKz
