# KontsevichSegal

A Lean 4 formalization of the Kontsevich-Segal axioms for quantum field theory,
built on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Overview

This project formalizes the framework introduced in
[*Wick rotation and the positivity of energy in quantum field theory*](https://arxiv.org/abs/2105.10161)
by Maxim Kontsevich and Graeme Segal (arXiv:2105.10161).

The paper introduces a domain QC(V) of allowable complex-valued metrics on smooth
manifolds and defines quantum field theories as holomorphic functors from a cobordism
category of manifolds with complex metrics to topological vector spaces. Positivity
of energy is expressed by the requirement that a theory extends holomorphically over
this domain, whose Shilov boundary consists precisely of the Lorentzian metrics.

### Modules

| Module | Status |
|--------|--------|
| `ComplexMetrics/` | In progress — core definitions |
| `Cobordism/` | Planned |
| `FieldTheory/` | Planned |
| `WickRotation/` | Planned |

**`KontsevichSegal.ComplexMetrics`** — The domain QC(V) of allowable complex metrics
(Section 2 of the paper): Definition 2.1, diagonal characterization (Theorem 2.2),
the angle condition |arg(g_{ii})| < π/2, Shilov boundary, and restriction to
subspaces (Proposition 2.5).

## Project Status

The tracked production tree contains **zero `axiom` declarations**. All physics
axioms from the KS paper are encoded as fields of Lean `structure` declarations.
Remaining work is represented by explicit theorem-level `sorry` placeholders —
nothing is assumed.

Snapshot (2026-04-08, tracked production tree):

| Module | Direct `sorry` lines |
|--------|----------------------|
| `ComplexMetrics/` | 4 |
| **Total** | **4** |

### Sorry Inventory (File Level)

| File | `sorry`s | Notes |
|------|----------|-------|
| `ComplexMetrics/Defs.lean` | 2 | `not_neg_real_axis`, `volume_element_positive` |
| `ComplexMetrics/Equivalence.lean` | 0 | `True` placeholder — Hodge star equivalence blocked on Mathlib |
| `ComplexMetrics/Domain.lean` | 0 | `True` placeholders — Props 2.4, 2.7 (topology on QC not formalized) |
| `ComplexMetrics/Restriction.lean` | 2 | Prop 2.5 — `nondegenerate` and `angle_cond` fields (eigenvalue interleaving argument) |
| `ComplexMetrics/ShilovBoundary.lean` | 0 | No theorems stated yet — module docstring only |

### Axiom Inventory

The tracked production tree currently contains **zero explicit `axiom`
declarations**. If any are introduced in the future (e.g., for Mathlib gaps that
cannot be worked around), they will be tracked here with justification.

### Detailed Status

See [docs/section2_status.md](docs/section2_status.md) for per-result tracking
of Section 2 formalization against the paper.

## Repository Layout

```
KontsevichSegal/
├── Basic.lean                  -- shared imports and notation
├── ComplexMetrics.lean         -- umbrella for ComplexMetrics/
├── ComplexMetrics/
│   ├── Defs.lean               -- Theorem 2.2: allowable complex metrics (working def)
│   ├── Equivalence.lean        -- Definition 2.1 ↔ Theorem 2.2 (deferred)
│   ├── Domain.lean             -- QC(V): contractibility, domain of holomorphy
│   ├── Restriction.lean        -- Proposition 2.5: restriction to subspaces
│   └── ShilovBoundary.lean     -- Lorentzian metrics on the Shilov boundary
└── All.lean                    -- full umbrella
KontsevichSegal.lean            -- root entry point
docs/
├── development_plan.md
└── section2_status.md
```

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake build
```

## References

- Kontsevich, M. and Segal, G., "Wick rotation and the positivity of energy in
  quantum field theory", arXiv:2105.10161 [hep-th], 2021.

## License

[Apache License 2.0](LICENSE)
