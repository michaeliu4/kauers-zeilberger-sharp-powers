import Results.SharpPowersKz.Defs
import Results.SharpPowersKz.Solution.DerivativeNumerator
import Results.SharpPowersKz.Solution.Geometry
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.Polynomial

/-!
Pure polynomial tangent transfer for all coordinate-derivative numerator words.
Affine substitution, denominator scaling, and the finite-parameter limit are
proved here. Cube J-positivity remains an explicit upstream hypothesis.
-/

noncomputable section

namespace Results.SharpPowersKz.TangentTransfer

open MvPolynomial DerivativeNumerator

section Affine
variable {σ R : Type*} [CommRing R]

def affineSub (r a : R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => C r + C a * X i)

@[simp] theorem affineSub_C (r a c : R) : affineSub r a (C c : MvPolynomial σ R) = C c := by
  simp [affineSub]

@[simp] theorem affineSub_X (r a : R) (i : σ) :
    affineSub r a (X i) = C r + C a * X i := by
  simp [affineSub]

/-- The exact affine chain rule for formal coordinate differentiation. -/
theorem pderiv_affineSub (r a : R) (i : σ) (p : MvPolynomial σ R) :
    pderiv i (affineSub r a p) = C a * affineSub r a (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst j
        simp [hp]
        ring
      · simp [hp, pderiv_X_of_ne hj]
        ring

/-- Each word contributes one affine derivative factor. -/
theorem numerator_affineSub (β r a : R) (Q : MvPolynomial σ R) (w : List σ) :
    numerator β (affineSub r a Q) w =
      C (a ^ w.length) * affineSub r a (numerator β Q w) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [numerator_cons, ih, pderiv_C_mul, pderiv_affineSub,
        List.length_cons, pow_succ, map_mul, map_sub, affineSub_C]
      ring

/-- Affine substitution evaluates at the actual affine point. -/
theorem eval_affineSub (r a : R) (x : σ → R) (p : MvPolynomial σ R) :
    eval x (affineSub r a p) = eval (fun i => r + a * x i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Affine

abbrev FourPoly := MvPolynomial (Fin 4) ℝ

def pFour : FourPoly := 1 - perturbation 4

def e2Poly : FourPoly := Algebra.e2 (X 0) (X 1) (X 2) (X 3)
def e3Poly : FourPoly := Algebra.e3 (X 0) (X 1) (X 2) (X 3)
def e4Poly : FourPoly := Algebra.e4 (X 0) (X 1) (X 2) (X 3)

def tangentPoly (ε : ℝ) : FourPoly :=
  C 2 * e2Poly - C (2 * Real.sqrt 3 * ε) * e3Poly + C (4 * ε ^ 2) * e4Poly

@[simp] theorem eval_pFour (x : Fin 4 → ℝ) :
    eval x pFour = Algebra.pκ 4 (x 0) (x 1) (x 2) (x 3) := by
  simp only [pFour, perturbation, Algebra.pκ, map_sub, map_one, map_add, map_mul,
    map_ofNat, eval_X]
  ring

@[simp] theorem eval_e2Poly (x : Fin 4 → ℝ) :
    eval x e2Poly = Algebra.e2 (x 0) (x 1) (x 2) (x 3) := by
  simp [e2Poly, Algebra.e2]

@[simp] theorem eval_e3Poly (x : Fin 4 → ℝ) :
    eval x e3Poly = Algebra.e3 (x 0) (x 1) (x 2) (x 3) := by
  simp [e3Poly, Algebra.e3]

@[simp] theorem eval_e4Poly (x : Fin 4 → ℝ) :
    eval x e4Poly = Algebra.e4 (x 0) (x 1) (x 2) (x 3) := by
  simp [e4Poly, Algebra.e4]

@[simp] theorem tangentPoly_zero : tangentPoly 0 = C 2 * e2Poly := by
  simp [tangentPoly]

/-- The previously checked scalar tangent identity gives an equality of
actual multivariate polynomials, hence may be formally differentiated. -/
theorem affine_pFour (ε : ℝ) :
    affineSub Algebra.rho (-ε) pFour = C (ε ^ 2) * tangentPoly ε := by
  apply MvPolynomial.funext
  intro x
  rw [eval_affineSub, eval_pFour]
  simp only [map_mul, eval_C, tangentPoly, map_add, map_sub,
    eval_e2Poly, eval_e3Poly, eval_e4Poly]
  simp only [neg_mul, ← sub_eq_add_neg]
  rw [Algebra.tangent_identity]
  ring

/-- Division-free numerator transfer at a nonzero tangent parameter. -/
theorem numerator_tangent_identity (β ε : ℝ) (w : List (Fin 4)) (x : Fin 4 → ℝ) :
    (ε ^ 2) ^ w.length * eval x (numerator β (tangentPoly ε) w) =
      (-ε) ^ w.length * eval (fun i => Algebra.rho - ε * x i) (numerator β pFour w) := by
  have h := congrArg (fun p : FourPoly => eval x p)
    (numerator_affineSub β Algebra.rho (-ε) pFour w)
  rw [affine_pFour, numerator_const_mul] at h
  simpa only [map_mul, eval_C, eval_affineSub, neg_mul, sub_eq_add_neg] using h

/-- The affine identity transports actual J-positivity, with the alternating
sign required by complete monotonicity. No analytic derivative identity is used. -/
theorem signed_numerator_tangent_nonnegative (β ε : ℝ) (hε : 0 < ε)
    (w : List (Fin 4)) (x : Fin 4 → ℝ)
    (hJ : 0 ≤ eval (fun i => Algebra.rho - ε * x i) (numerator β pFour w)) :
    0 ≤ (-1 : ℝ) ^ w.length * eval x (numerator β (tangentPoly ε) w) := by
  have h := numerator_tangent_identity β ε w x
  have hsign : (-1 : ℝ) ^ w.length * (-ε) ^ w.length = ε ^ w.length := by
    rw [← mul_pow]
    congr 1
    ring
  have he : (ε ^ 2) ^ w.length *
        ((-1 : ℝ) ^ w.length * eval x (numerator β (tangentPoly ε) w)) =
      ε ^ w.length * eval (fun i => Algebra.rho - ε * x i) (numerator β pFour w) := by
    calc
      _ = (-1 : ℝ) ^ w.length *
          ((ε ^ 2) ^ w.length * eval x (numerator β (tangentPoly ε) w)) := by ring
      _ = _ := by rw [h, ← mul_assoc, hsign]
  have hnonneg : 0 ≤ (ε ^ 2) ^ w.length *
      ((-1 : ℝ) ^ w.length * eval x (numerator β (tangentPoly ε) w)) := by
    rw [he]
    exact mul_nonneg (pow_nonneg hε.le _) hJ
  exact (mul_nonneg_iff_of_pos_left (pow_pos (pow_pos hε 2) _)).mp hnonneg

/-- An explicit polynomial in the tangent parameter, before specialization. -/
def tangentUniversal : MvPolynomial (Fin 4) (Polynomial ℝ) :=
  C 2 * MvPolynomial.map Polynomial.C e2Poly -
    C (Polynomial.C (2 * Real.sqrt 3) * Polynomial.X) * MvPolynomial.map Polynomial.C e3Poly +
    C (4 * Polynomial.X ^ 2) * MvPolynomial.map Polynomial.C e4Poly

theorem tangentUniversal_map (ε : ℝ) :
    MvPolynomial.map (Polynomial.evalRingHom ε) tangentUniversal = tangentPoly ε := by
  have hc : (Polynomial.evalRingHom ε).comp Polynomial.C = RingHom.id ℝ := by
    ext c
    simp
  simp [tangentUniversal, tangentPoly, MvPolynomial.map_map, hc, MvPolynomial.map_id]

theorem numerator_tangentUniversal_map (β ε : ℝ) (w : List (Fin 4)) :
    numerator β (tangentPoly ε) w =
      MvPolynomial.map (Polynomial.evalRingHom ε)
        (numerator (Polynomial.C β) tangentUniversal w) := by
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C, tangentUniversal_map] using
    numerator_map (Polynomial.evalRingHom ε) (Polynomial.C β) tangentUniversal w

/-- Commuting the two finite polynomial evaluations. -/
theorem eval_parameter_map (p : MvPolynomial (Fin 4) (Polynomial ℝ))
    (ε : ℝ) (x : Fin 4 → ℝ) :
    eval x (MvPolynomial.map (Polynomial.evalRingHom ε) p) =
      Polynomial.eval ε (eval (fun i => Polynomial.C (x i)) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Each individual numerator coefficient is polynomial in the tangent
parameter; in particular the whole finite numerator has a coefficientwise limit. -/
theorem continuous_numerator_tangent_coeff (β : ℝ) (w : List (Fin 4))
    (d : Fin 4 →₀ ℕ) :
    Continuous (fun ε : ℝ => (numerator β (tangentPoly ε) w).coeff d) := by
  simp_rw [numerator_tangentUniversal_map, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom]
  exact Polynomial.continuous _

/-- Every fixed word and spatial evaluation depends polynomially, hence
continuously, on the tangent parameter. This closes the limit without any
interchange of analytic differentiation and limits. -/
theorem continuous_numerator_tangent (β : ℝ) (w : List (Fin 4)) (x : Fin 4 → ℝ) :
    Continuous (fun ε : ℝ => eval x (numerator β (tangentPoly ε) w)) := by
  simp_rw [numerator_tangentUniversal_map, eval_parameter_map]
  exact Polynomial.continuous _

open Filter Topology

/-- For each positive spatial point, the reflected points lie in the cube
for every sufficiently small positive tangent parameter. -/
theorem eventually_affine_in_cube (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ i, 0 < Algebra.rho - ε * x i ∧ Algebra.rho - ε * x i < Algebra.rho := by
  have hlow : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, 0 < Algebra.rho - ε * x i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun ε : ℝ => Algebra.rho - ε * x i) :=
      continuous_const.sub (continuous_id.mul continuous_const)
    have ht : Tendsto (fun ε : ℝ => Algebra.rho - ε * x i) (𝓝 0) (𝓝 Algebra.rho) := by
      simpa using hc.tendsto 0
    exact ht.eventually (lt_mem_nhds Algebra.rho_pos)
  have hlow' := hlow.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  filter_upwards [hlow', hpos] with ε hεlow hεpos
  intro i
  exact ⟨hεlow i, sub_lt_self _ (mul_pos hεpos (hx i))⟩

/-- Pure polynomial tangent transfer. The premise is positivity of the actual
J_w(P) on the cube, not positivity of formal coefficients and not an assumed
tangent theorem. The conclusion covers every word on the entire orthant. -/
theorem signed_e2_numerator_nonnegative_of_cube (β : ℝ)
    (hJ : ∀ (w : List (Fin 4)) (y : Fin 4 → ℝ),
      (∀ i, 0 < y i ∧ y i < Algebra.rho) →
        0 ≤ eval y (numerator β pFour w))
    (w : List (Fin 4)) (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    0 ≤ (-1 : ℝ) ^ w.length * eval x (numerator β e2Poly w) := by
  have hc : Continuous (fun ε : ℝ =>
      (-1 : ℝ) ^ w.length * eval x (numerator β (tangentPoly ε) w)) :=
    continuous_const.mul (continuous_numerator_tangent β w x)
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 ≤ (-1 : ℝ) ^ w.length * eval x (numerator β (tangentPoly ε) w) := by
    have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
    filter_upwards [eventually_affine_in_cube x hx, hpos] with ε hcube hε
    exact signed_numerator_tangent_nonnegative β ε hε w x
      (hJ w (fun i => Algebra.rho - ε * x i) hcube)
  have ht := (hc.tendsto 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hzero := ge_of_tendsto ht hevent
  rw [tangentPoly_zero, numerator_const_mul, map_mul, eval_C] at hzero
  have hscaled : 0 ≤ (2 : ℝ) ^ w.length *
      ((-1 : ℝ) ^ w.length * eval x (numerator β e2Poly w)) := by
    simpa only [mul_left_comm] using hzero
  exact (mul_nonneg_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mp hscaled

end Results.SharpPowersKz.TangentTransfer
