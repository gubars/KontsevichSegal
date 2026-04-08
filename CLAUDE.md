# KontsevichSegal

Lean 4 formalization of the Kontsevich-Segal axioms for quantum field theory,
based on arXiv:2105.10161 by Kontsevich and Segal.

## Key rules

- NEVER use the Lean `axiom` keyword. All physics axioms are fields of `structure`
  declarations. Gaps in proofs use `sorry`.
- Every .lean file must compile with `lake build`. Sorrys are fine, errors are not.
- Follow Mathlib conventions for naming, typeclass assumptions, and imports.
- Add docstrings referencing the paper: "KS paper Definition 2.1", "KS paper
  Theorem 2.2", "KS paper Proposition 2.5", etc.

## Project structure

- `KontsevichSegal/Basic.lean` — shared imports and notation
- `KontsevichSegal/ComplexMetrics/` — Section 2: domain of complex metrics
  - `Defs.lean` — working definition using angle condition (Theorem 2.2)
  - `Equivalence.lean` — placeholder for equivalence with Definition 2.1 (needs Hodge star)
  - `Domain.lean` — Props 2.4, 2.7 (contractibility, domain of holomorphy)
  - `Restriction.lean` — Prop 2.5 (restriction to subspaces)
  - `ShilovBoundary.lean` — Lorentzian metrics on the Shilov boundary
- `KontsevichSegal/Cobordism/` — (planned) Section 3: cobordism category
- `KontsevichSegal/FieldTheory/` — (planned) Section 3: field theory as functor
- `KontsevichSegal/WickRotation/` — (planned) Section 5: Wick rotation

## Design decisions

- Theorem 2.2 (angle condition) is used as the WORKING DEFINITION of allowable
  complex metrics because Definition 2.1 requires the Hodge star operator which
  is not in Mathlib. Equivalence is deferred.
- Props 2.3, 2.6, Lemma 2.8 are deferred — they depend on Wightman tube domain
  or Section 5 machinery not yet built.

## Status tracking

See docs/section2_status.md for detailed per-result status of Section 2.
See docs/development_plan.md for the overall phasing.

## Reference

The paper is at /KS.pdf in the project root (also arXiv:2105.10161).
