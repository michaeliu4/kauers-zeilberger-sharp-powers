import Results.SharpPowersKz.Solution.NumeratorCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.FunProp

/-!
# Analyticity of polynomial real powers and their word derivatives
-/

namespace Results.SharpPowersKz.NumeratorCalculus

open MvPolynomial
open Filter
open scoped Topology
open Results.SharpPowersKz.DerivativeNumerator

variable {σ : Type*} [Fintype σ]

/-- Evaluation of a multivariate real polynomial is analytic. -/
theorem analyticAt_eval (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    AnalyticAt ℝ (fun y => p.eval y) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : σ → ℝ => a) x)
  | add p q hp hq =>
      refine (hp.add hq).congr (Filter.Eventually.of_forall fun y => ?_)
      exact eval_add.symm
  | mul_X p i hp =>
      have hi : AnalyticAt ℝ (fun y : σ → ℝ => y i) x :=
        ((ContinuousLinearMap.proj (R := ℝ) i : (σ → ℝ) →L[ℝ] ℝ).analyticAt x)
      refine (hp.mul hi).congr (Filter.Eventually.of_forall fun y => ?_)
      change p.eval y * y i = (p * X i).eval y
      rw [eval_mul, eval_X]

/-- A real power of a polynomial is analytic wherever the polynomial is positive. -/
theorem analyticAt_eval_rpow (p : MvPolynomial σ ℝ) (a : ℝ) (x : σ → ℝ)
    (hp : 0 < p.eval x) :
    AnalyticAt ℝ (fun y => (p.eval y) ^ a) x := by
  have hpoly : AnalyticAt ℝ (fun y => p.eval y) x := analyticAt_eval p x
  have hpos : ∀ᶠ y in 𝓝 x, 0 < p.eval y :=
    hpoly.continuousAt.eventually_mem (isOpen_Ioi.mem_nhds hp)
  have hlog0 : AnalyticAt ℝ Real.log (p.eval x) := analyticAt_log hp
  have hlog : AnalyticAt ℝ (fun y => Real.log (p.eval y)) x := by
    convert hlog0.comp (f := fun y : σ → ℝ => p.eval y) (x := x) hpoly using 1
    rfl
  have hmul : AnalyticAt ℝ (fun y => Real.log (p.eval y) * a) x :=
    hlog.mul analyticAt_const
  have hexp : AnalyticAt ℝ (fun y => Real.exp (Real.log (p.eval y) * a)) x :=
    hmul.rexp'
  apply hexp.congr
  exact hpos.mono fun y hy => (Real.rpow_def_of_pos hy a).symm

/-- The negative-power specialization used in the complete-monotonicity bridge. -/
theorem analyticAt_eval_neg_rpow (p : MvPolynomial σ ℝ) (β : ℝ) (x : σ → ℝ)
    (hp : 0 < p.eval x) :
    AnalyticAt ℝ (fun y => (p.eval y) ^ (-β)) x :=
  analyticAt_eval_rpow p (-β) x hp

/-- Every actual word derivative supplied by `wordDeriv_neg_rpow` is analytic
on the positive locus of the denominator. -/
theorem analyticAt_wordDeriv_neg_rpow (β : ℝ) (Q : MvPolynomial σ ℝ)
    [DecidableEq σ] (w : List σ) (x : σ → ℝ) (hQ : 0 < Q.eval x) :
    AnalyticAt ℝ (wordDeriv w (fun y => (Q.eval y) ^ (-β))) x := by
  have hQana := analyticAt_eval Q x
  have hpos : ∀ᶠ y in 𝓝 x, 0 < Q.eval y :=
    hQana.continuousAt.eventually_mem (isOpen_Ioi.mem_nhds hQ)
  have heq :
      wordDeriv w (fun y => (Q.eval y) ^ (-β)) =ᶠ[𝓝 x]
        fun y => (numerator β Q w).eval y * (Q.eval y) ^ (-β - (w.length : ℝ)) :=
    hpos.mono fun y hy => wordDeriv_neg_rpow β Q w y hy
  have hrhs : AnalyticAt ℝ
      (fun y => (numerator β Q w).eval y * (Q.eval y) ^ (-β - (w.length : ℝ))) x :=
    (analyticAt_eval (numerator β Q w) x).mul
      (analyticAt_eval_rpow Q (-β - (w.length : ℝ)) x hQ)
  exact hrhs.congr heq.symm

end Results.SharpPowersKz.NumeratorCalculus
