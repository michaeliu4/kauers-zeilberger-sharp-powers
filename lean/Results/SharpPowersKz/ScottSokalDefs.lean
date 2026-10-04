import Results.SharpPowersKz.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Neutral definitions for the published Scott--Sokal dependency. This module
imports no Solution file and introduces no axiom. The external classification
is a proposition passed explicitly to any proof relying on it.
-/

namespace Results.SharpPowersKz.NumeratorCalculus

variable {σ : Type*} [DecidableEq σ]

/-- Actual coordinate derivative, obtained by varying just coordinate `i`. -/
noncomputable def coordinateDeriv (i : σ) (f : (σ → ℝ) → ℝ) (x : σ → ℝ) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)

/-- The head of the word is the final derivative applied. -/
noncomputable def wordDeriv : List σ → ((σ → ℝ) → ℝ) → (σ → ℝ) → ℝ
  | [], f => f
  | i :: w, f => coordinateDeriv i (wordDeriv w f)

end Results.SharpPowersKz.NumeratorCalculus

namespace Results.SharpPowersKz.ScottSokal

open scoped ContDiff

def positiveOrthant : Set (Fin 4 → ℝ) := {x | ∀ i, 0 < x i}

def CompletelyMonotone (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f positiveOrthant ∧
    ∀ (w : List (Fin 4)) (x : Fin 4 → ℝ), x ∈ positiveOrthant →
      0 ≤ (-1 : ℝ) ^ w.length * NumeratorCalculus.wordDeriv w f x

noncomputable def e2InversePower (β : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (x 0 * x 1 + x 0 * x 2 + x 0 * x 3 +
    x 1 * x 2 + x 1 * x 3 + x 2 * x 3) ^ (-β)

/-- Scott--Sokal, Acta Math. 213 (2014), Corollary 1.6 for `E₂,₄`.
This is a named external hypothesis, not an asserted Lean theorem. -/
def E2InversePowers : Prop :=
  ∀ β : ℝ, CompletelyMonotone (e2InversePower β) ↔ β = 0 ∨ 1 ≤ β

end Results.SharpPowersKz.ScottSokal
