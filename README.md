# Sharp powers of the Kauers-Zeilberger rational function

This standalone Lean 4 package contains the proof sources for the sharp exponent results associated with the manuscript *Sharp powers of the Kauers-Zeilberger rational function*. The manuscript itself is not included here.

The default `Results` library imports only `Results.SharpPowersKz.Solution.Main`. It does not include the statement-only `Challenge.lean` module or any `sorry` placeholders.

## Scope

The selected declarations are `macMahon_master_theorem`, `main_range`, `main_shift`, `main_lower_bound`, `quartic_range`, `quartic_strict`, `quartic_joint`, and `quartic_obstruction`, all in namespace `Results.SharpPowersKz`.

The source formalization passed its Level 3 audit with coverage `full_assuming`. Only `main_range` takes the explicit external hypothesis `Results.SharpPowersKz.ScottSokal.E2InversePowers`, the Scott-Sokal classification for complete monotonicity of inverse powers of the elementary symmetric polynomial `E2`. The generic finite-dimensional complex MacMahon Master Theorem is proved within the package; the other selected targets do not assume the Scott-Sokal classification.

## Build

The package pins Lean and Mathlib to `v4.32.1` and records the complete dependency revisions in `lake-manifest.json`.

Run these commands from the repository root:

```sh
lake exe cache get
lake build Results
lake env lean PrintAxioms.lean
```

`PROVENANCE.md` maps every copied proof source to its Git blob at protected source commit `b3da9c75451546c72845b58d74308222adb5f9ae`.

## Review boundary

Lean checks the declarations relative to Lean's kernel, Mathlib, and the explicit theorem hypotheses. This package does not establish the Scott-Sokal classification, certify the manuscript's prose, or constitute journal peer review, publication, or acceptance of the mathematical claim.

## Rights

This repository makes no new license grant for the Lean sources. Lean and Mathlib are external dependencies with their own licenses.
