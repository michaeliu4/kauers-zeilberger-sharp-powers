import Results.SharpPowersKz.Solution.MacMahonTheorem
import Results.SharpPowersKz.Solution.PositiveMain
import Results.SharpPowersKz.Solution.ScottSokal
import Results.SharpPowersKz.Solution.CubeJetBridge
import Results.SharpPowersKz.Solution.QuarticObstruction

namespace Results.SharpPowersKz

theorem macMahon_master_theorem : MacMahon.MacMahonMasterTheorem :=
  MacMahon.macMahon_master_theorem

theorem main_range (hSS : ScottSokal.E2InversePowers) (β : ℝ) :
    NonnegativePower 4 β ↔ β = 0 ∨ 1 ≤ β := by
  constructor
  · intro h
    apply ScottSokal.range_of_cube_numerators hSS β
    exact CoefficientJets.numerator_nonnegative_cube β h
  · exact main_range_reverse_of_macMahon macMahon_master_theorem β

theorem main_shift : ShiftNonnegative :=
  main_shift_of_macMahon macMahon_master_theorem

theorem main_lower_bound
    (β : ℝ) (hβ : 1 ≤ β) (d : MultiIndex) :
    lowerBound β d ≤ powerCoeff 4 β d ∧ 0 < lowerBound β d :=
  main_lower_bound_of_macMahon macMahon_master_theorem β hβ d

theorem quartic_range
    (κ β : ℝ) (hβ : 1 ≤ β) : NonnegativePower κ β ↔ κ ≤ 4 := by
  constructor
  · intro h
    by_contra hκ
    obtain ⟨d, hd⟩ := quartic_obstruction κ β (lt_of_not_ge hκ)
      (lt_of_lt_of_le (by norm_num) hβ)
    exact (not_le_of_gt hd) (h d)
  · intro hκ
    exact quartic_range_reverse_of_macMahon macMahon_master_theorem κ β hκ hβ

theorem quartic_strict
    (κ β : ℝ) (hκ : κ ≤ 4) (hβ : 1 ≤ β) : PositivePower κ β :=
  quartic_strict_of_macMahon macMahon_master_theorem κ β hκ hβ

theorem quartic_joint : JointNonnegative :=
  quartic_joint_of_macMahon macMahon_master_theorem

end Results.SharpPowersKz
