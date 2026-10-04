import Results.SharpPowersKz.Solution.DerivativeNumerator
import Results.SharpPowersKz.ScottSokalDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

/-!
# Calculus semantics of the derivative numerators

This file identifies `DerivativeNumerator.numerator` with actual iterated
coordinate derivatives of a negative real power of a multivariate polynomial.
The head of a word is the final derivative applied, matching the recursion in
`DerivativeNumerator.numerator`.
-/

namespace Results.SharpPowersKz.NumeratorCalculus

open MvPolynomial
open Filter
open scoped Topology
open Results.SharpPowersKz.DerivativeNumerator

variable {σ : Type*} [DecidableEq σ]

@[simp]
theorem wordDeriv_nil (f : (σ → ℝ) → ℝ) : wordDeriv [] f = f := rfl

theorem wordDeriv_cons (i : σ) (w : List σ) (f : (σ → ℝ) → ℝ) :
    wordDeriv (i :: w) f = coordinateDeriv i (wordDeriv w f) := rfl

/-- A polynomial restricted to a coordinate line. -/
noncomputable def evalAlong (p : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) (t : ℝ) : ℝ :=
  p.eval (Function.update x i t)

@[simp]
theorem evalAlong_at (p : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) :
    evalAlong p x i (x i) = p.eval x := by
  simp [evalAlong]

/-- Evaluating `pderiv i p` gives the actual derivative along coordinate `i`. -/
theorem hasDerivAt_evalAlong (p : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) :
    HasDerivAt (evalAlong p x i) ((pderiv i p).eval x) (x i) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      convert hasDerivAt_const (x i) a using 1
      all_goals try with_reducible_and_instances rfl
      · funext t
        change (C a : MvPolynomial σ ℝ).eval (Function.update x i t) = a
        simp only [eval_C]
      · rw [pderiv_C, map_zero]
  | add p q hp hq =>
      convert HasDerivAt.add hp hq using 1
      all_goals try with_reducible_and_instances rfl
      · funext t
        change (p + q).eval (Function.update x i t) =
          p.eval (Function.update x i t) + q.eval (Function.update x i t)
        simp only [eval_add]
      · rw [map_add, eval_add]
  | mul_X p j hp =>
      have hj : HasDerivAt (fun t => Function.update x i t j)
          (if j = i then 1 else 0) (x i) := by
        by_cases hji : j = i
        · subst j
          rw [if_pos rfl]
          refine (hasDerivAt_id (x i)).congr_of_eventuallyEq ?_
          exact Filter.Eventually.of_forall fun t => by simp
        · rw [if_neg hji]
          refine (hasDerivAt_const (x i) (x j)).congr_of_eventuallyEq ?_
          exact Filter.Eventually.of_forall fun t => by simp [Function.update_of_ne hji]
      have hmul := HasDerivAt.mul hp hj
      refine (hmul.congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall fun t => by simp [evalAlong]
      · by_cases hji : j = i
        · subst j
          simp [pderiv_X, evalAlong]
          ring
        · simp [hji, pderiv_X, evalAlong]
          ring

/-- Kernel-checked interpretation of the recursive numerator as an actual
iterated coordinate derivative. -/
theorem wordDeriv_neg_rpow (β : ℝ) (Q : MvPolynomial σ ℝ) (w : List σ)
    (x : σ → ℝ) (hQ : 0 < Q.eval x) :
    wordDeriv w (fun y => (Q.eval y) ^ (-β)) x =
      (numerator β Q w).eval x * (Q.eval x) ^ (-β - (w.length : ℝ)) := by
  induction w generalizing x with
  | nil => simp [wordDeriv, numerator]
  | cons i w ih =>
      let N := numerator β Q w
      let a : ℝ := -β - (w.length : ℝ)
      let b : ℝ := -β - ((w.length + 1 : ℕ) : ℝ)
      have hQd := hasDerivAt_evalAlong Q x i
      have hNd := hasDerivAt_evalAlong N x i
      have hQcenter : evalAlong Q x i (x i) = Q.eval x := evalAlong_at Q x i
      have hpos : ∀ᶠ t in 𝓝 (x i), 0 < evalAlong Q x i t := by
        have hc : 0 < evalAlong Q x i (x i) := by simpa only [hQcenter]
        exact hQd.continuousAt.eventually_mem (isOpen_Ioi.mem_nhds hc)
      have heq :
          (fun t => wordDeriv w (fun y => (Q.eval y) ^ (-β))
            (Function.update x i t)) =ᶠ[𝓝 (x i)]
          (fun t => evalAlong N x i t * (evalAlong Q x i t) ^ a) := by
        exact hpos.mono fun t ht => by
          simpa only [N, a, evalAlong] using ih (Function.update x i t) ht
      have hpow : HasDerivAt (fun t => (evalAlong Q x i t) ^ a)
          ((pderiv i Q).eval x * a * (Q.eval x) ^ (a - 1)) (x i) := by
        have hcne : evalAlong Q x i (x i) ≠ 0 := by simpa using hQ.ne'
        simpa only [evalAlong_at] using hQd.rpow_const (p := a) (Or.inl hcne)
      have hprod := hNd.mul hpow
      rw [wordDeriv_cons, coordinateDeriv, heq.deriv_eq]
      have hsame :
          (fun t => evalAlong N x i t * (evalAlong Q x i t) ^ a) =ᶠ[𝓝 (x i)]
            (evalAlong N x i * fun t => (evalAlong Q x i t) ^ a) :=
        Filter.Eventually.of_forall fun _ => rfl
      rw [hsame.deriv_eq, hprod.deriv]
      simp only [evalAlong_at]
      have hab : a = b + 1 := by
        simp only [a, b, Nat.cast_add, Nat.cast_one]
        ring
      have hab' : a - 1 = b := by linarith
      have hpowstep : (Q.eval x) ^ a = (Q.eval x) ^ b * Q.eval x := by
        rw [hab, Real.rpow_add_one hQ.ne']
      have hlen : -β - ((List.length (i :: w) : ℕ) : ℝ) = b := by
        simp only [List.length_cons, b, Nat.cast_add, Nat.cast_one]
      rw [hlen]
      simp only [numerator_cons, map_sub, map_mul, eval_C]
      rw [hpowstep, hab']
      dsimp only [N, a, b]
      ring

end Results.SharpPowersKz.NumeratorCalculus
