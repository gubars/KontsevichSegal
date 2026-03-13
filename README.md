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
| `ComplexMetrics/` | Planned |
| `Cobordism/` | Planned |
| `FieldTheory/` | Planned |
| `WickRotation/` | Planned |

**`KontsevichSegal.ComplexMetrics`** — The domain QC(V) of allowable complex metrics
(Section 2 of the paper): Definition 2.1, diagonal characterization (Theorem 2.2),
the angle condition |arg(g_{ii})| < π/2, Shilov boundary, and restriction to
subspaces (Proposition 2.5).

## Project Status

This project uses **zero Lean `axiom` declarations**. All physics axioms from the
KS paper are encoded as fields of Lean `structure` declarations. Remaining work is
represented by explicit `sorry` placeholders — nothing is silently assumed.

## Repository Layout

```
KontsevichSegal/
├── Basic.lean                  -- shared imports and notation
├── ComplexMetrics.lean         -- umbrella for ComplexMetrics/
├── ComplexMetrics/
│   ├── Defs.lean               -- Definition 2.1: allowable complex metrics
│   ├── Diagonal.lean           -- Theorem 2.2: diagonal characterization
│   ├── Domain.lean             -- QC(V): contractibility, domain of holomorphy
│   └── Restriction.lean        -- Proposition 2.5: restriction to subspaces
└── All.lean                    -- full umbrella
KontsevichSegal.lean            -- root entry point
docs/
└── development_plan.md
```

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake build
```

## References

- Kontsevich, M. and Segal, G., "Wick rotation and the positivity of energy in
  quantum field theory", arXiv:2105.10161 [hep-th], 2021.
- Streater, R. F. and Wightman, A. S., *PCT, Spin and Statistics, and All That*,
  Princeton University Press, 2000.
- Feynman, R. P. and Hibbs, A. R., *Quantum Mechanics and Path Integrals*,
  McGraw-Hill, 1965.

## License

[Apache License 2.0](LICENSE)
