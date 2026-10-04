import Results.SharpPowersKz.Solution.CoefficientSchur
import Results.SharpPowersKz.Solution.MacMahon
import Mathlib.Data.Complex.Basic

/-! Coefficientwise positivity under specialization of the auxiliary variables. -/
noncomputable section
set_option maxHeartbeats 1200000

namespace Results.SharpPowersKz.SixSpecialization

open CoefficientSchur

theorem coeffNonneg_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℚ)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∑ i ∈ s, f i) := by
  intro d
  simp only [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg fun i hi => h i hi d

theorem coeffNonneg_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℚ)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (coeffNonneg_one : CoeffNonneg (1 : MvPolynomial σ ℚ))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact coeffNonneg_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem coeffNonneg_eval₂ {σ τ : Type*} (p : MvPolynomial σ ℚ)
    (v : σ → MvPolynomial τ ℚ) (hp : CoeffNonneg p)
    (hv : ∀ i, CoeffNonneg (v i)) : CoeffNonneg (p.eval₂ MvPolynomial.C v) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply coeffNonneg_sum
  intro d hd
  apply coeffNonneg_mul (coeffNonneg_C (hp d))
  exact coeffNonneg_prod _ _ fun i _ => coeffNonneg_pow (hv i) _

theorem coeffNonneg_of_complex {σ : Type*} (p : MvPolynomial σ ℚ)
    (hp : ∀ d, 0 ≤ ((MvPolynomial.map (algebraMap ℚ ℂ) p).coeff d).re) :
    CoeffNonneg p := by
  intro d
  have h := hp d
  rw [MvPolynomial.coeff_map] at h
  change 0 ≤ (((p.coeff d : ℚ) : ℂ)).re at h
  rw [Complex.ratCast_re] at h
  exact_mod_cast h

/-- The left third and right third variables are specialized to one. -/
def auxiliaryValue : Fin 3 ⊕ Fin 3 → FourPoly ℚ
  | .inl i => if i = 0 then MvPolynomial.X 0 else if i = 1 then MvPolynomial.X 1 else 1
  | .inr i => if i = 0 then MvPolynomial.X 2 else if i = 1 then MvPolynomial.X 3 else 1

theorem auxiliaryValue_nonneg (i : Fin 3 ⊕ Fin 3) : CoeffNonneg (auxiliaryValue i) := by
  rcases i with i | i
  · dsimp only [auxiliaryValue]
    split_ifs
    · exact coeffNonneg_X 0
    · exact coeffNonneg_X 1
    · exact coeffNonneg_one
  · dsimp only [auxiliaryValue]
    split_ifs
    · exact coeffNonneg_X 2
    · exact coeffNonneg_X 3
    · exact coeffNonneg_one

def specialize : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ →+* FourPoly ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C auxiliaryValue

theorem specialize_nonneg (p : MvPolynomial (Fin 3 ⊕ Fin 3) ℚ)
    (hp : CoeffNonneg p) : CoeffNonneg (specialize p) :=
  coeffNonneg_eval₂ p auxiliaryValue hp auxiliaryValue_nonneg

theorem specialize_L : specialize (MacMahon.dilationLPoly (A := ℚ)) = kzL := by
  simp [specialize, MacMahon.dilationLPoly, auxiliaryValue, kzL]
  ring

theorem specialize_R : specialize (MacMahon.dilationRPoly (A := ℚ)) = kzD := by
  simp [specialize, MacMahon.dilationRPoly, auxiliaryValue, kzD]
  ring

theorem complex_map_L :
    MvPolynomial.map (algebraMap ℚ ℂ) (MacMahon.dilationLPoly (A := ℚ)) =
      MacMahon.dilationLPoly (A := ℂ) := by
  simp [MacMahon.dilationLPoly]

theorem complex_map_R :
    MvPolynomial.map (algebraMap ℚ ℂ) (MacMahon.dilationRPoly (A := ℚ)) =
      MacMahon.dilationRPoly (A := ℂ) := by
  simp [MacMahon.dilationRPoly]

theorem complete_nonnegative_of_dilation (k : ℕ)
    (h : ∀ d, 0 ≤ ((Schur.complete (MacMahon.dilationLPoly (A := ℂ))
      MacMahon.dilationRPoly k).coeff d).re) :
    CoeffNonneg (Schur.complete kzL kzD k : FourPoly ℚ) := by
  have hq : CoeffNonneg (Schur.complete (MacMahon.dilationLPoly (A := ℚ))
      MacMahon.dilationRPoly k) := by
    apply coeffNonneg_of_complex
    rw [Schur.map_complete, complex_map_L, complex_map_R]
    exact h
  have hs := specialize_nonneg _ hq
  rw [Schur.map_complete, specialize_L, specialize_R] at hs
  exact hs

theorem shiftNonnegative_of_dilation
    (h : ∀ k d, 0 ≤ ((Schur.complete (MacMahon.dilationLPoly (A := ℂ))
      MacMahon.dilationRPoly k).coeff d).re) : ShiftNonnegative :=
  shiftNonnegative_of_complete_nonnegative fun k => complete_nonnegative_of_dilation k (h k)

/-- The only external mathematical premise is the named general MacMahon
identity. The explicit determinant, specialization, and coefficient identities
used to reach this conclusion are proved in the imported files. -/
theorem complete_nonnegative_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem)
    (k : ℕ) : CoeffNonneg (Schur.complete kzL kzD k : FourPoly ℚ) :=
  complete_nonnegative_of_dilation k (MacMahon.dilation_complete_coeff_re_nonneg hMMT k)

theorem shiftNonnegative_of_macMahon (hMMT : MacMahon.MacMahonMasterTheorem) :
    ShiftNonnegative :=
  shiftNonnegative_of_complete_nonnegative (complete_nonnegative_of_macMahon hMMT)

end Results.SharpPowersKz.SixSpecialization
