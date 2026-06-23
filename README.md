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

## Approach

The deliverable goal is **scope (a)**: state the paper's definitions, axioms, and
theorem statements precisely and faithfully in Lean. Proving the stated theorems is
additive work, done where the proof is tractable in-project; nothing stated is
wasted if a proof comes later.

The encoding follows a **content-vs-infrastructure** split:

- **Content** (KS's own definitions, axioms, theorem statements) is built
  concretely as Lean `structure`/`class`/`def` declarations.
- **Prerequisite infrastructure** that KS cite as known but do not develop is
  *axiomatized*, meaning it is encoded as a `class` listing the required
  properties as fields, with no concrete construction. This is **never** the Lean
  `axiom` keyword — the tracked tree contains zero `axiom` declarations. Physics
  axioms are likewise fields of `structure`/`class` declarations.

Two recurring Mathlib gaps gate most of the deferred analytic content, especially
in Section 3:

- **infinite-dimensional / Fréchet-modelled complex manifolds** (Mathlib's
  manifolds require normed models), and
- **limits and completed tensor products of topological vector spaces** (Mathlib
  has only algebraic tensor products and finite-rank traces).

Where a faithful statement is blocked by these, it is **deferred with a documented
reason** rather than approximated by a weaker stand-in (no-approximations policy).

The project is developed with [leanblueprint](https://github.com/PatrickMassot/leanblueprint):
each paper result is a blueprint node in `blueprint/src/`, annotated so the
dependency graph reflects the true state (statement formalized, proof complete,
or stated-but-deferred).

### Modules

| Module | Paper section | Status |
|--------|---------------|--------|
| `ComplexMetrics/` | Section 2 | **Substantially proven.** The consequences and Shilov-boundary results are proven; 2 `sorry`s remain in `restrict_allowable` (Prop 2.5), deferred under scope (a); plus documented `True`-placeholders for results blocked on Mathlib gaps. |
| `Cobordism/` | Section 3 | **Encoded.** The cobordism category C_d^ℂ as an identity-free `Semicategory` (it genuinely has no identity morphisms). |
| `FieldTheory/` | Section 3 | **Encoded.** All of Section 3's analytic infrastructure, the field-theory functor, and the six functor-condition/axiom nodes (together, all 11 Section 3 blueprint nodes). Stated faithfully; deep analytic content deferred to the Mathlib gaps above. |
| `WickRotation/` | Section 5 | **Encoded.** Nodes 1–10 of 11 stated faithfully (scope (a)): the real-analytic Lorentzian / globally-hyperbolic cobordism category, the invariance principle (Principle 5.1), Theorem 5.2 (the gh unitary functor and the rigged triple Ě ⊂ E^Hilb ⊂ Ê), observables and their ordering-independent action, and spacelike commutativity. Node 11 (`VacuumDomain`, V_k ⊇ U_k) is the last remaining node. No `sorry` and no `axiom` — deferrals are documented prose, the same character as the Section 3 rows. |

- **`ComplexMetrics`** (Section 2) — the domain QC(V) of allowable complex
  metrics: the angle condition ∑ᵢ |arg(λᵢ)| < π (working definition, Theorem 2.2),
  its deferred equivalence with Definition 2.1 (Hodge star), restriction to
  subspaces (Prop 2.5), and the Shilov boundary (real Lorentzian metrics, and no
  other nondegenerate real metrics, lie on it).
- **`Cobordism` / `FieldTheory`** (Section 3) — the cobordism category C_d^ℂ; the
  analytic infrastructure (nuclear Fréchet spaces, Met_ℂ(M) as a complex manifold,
  holomorphic vector bundles); a field theory as a holomorphic functor; and its
  conditions: holomorphicity, continuity (the injective/dense-image replacement
  for the missing identity morphisms), the disjoint-union/tensor axiom, the dual
  and conjugate functors, the conjugate-dual duality, and unitarity.
- **`WickRotation`** (Section 5) — Wick rotation and the unitary functor on the
  globally hyperbolic category: the real-analytic Lorentzian cobordism category and
  its globally-hyperbolic subcategory; the Wick rotation of time-symmetric metrics
  (geodesic normal form); the invariance principle (Principle 5.1); Theorem 5.2 (a
  unitary QFT induces a functor sending time-symmetric germs to Hilbert spaces and
  gh cobordisms to unitary operators, with the rigged triple Ě_Σ ⊂ E_Σ^Hilb ⊂ Ê_Σ);
  the well-definedness of the Lorentzian Ê_Σ; the observable spaces 𝒪_x with their
  action and the ordering-independent multilinear map
  𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_Σ; Ê_Σ); spacelike commutativity (the Wightman
  locality axiom); and the vacuum-expectation domain V_k (the last node, not yet
  started).

Section 4 ("Some analogies from representation theory") is expository analogy with
no KS definitions/axioms/theorems to formalize. Section 5 is now nearly complete:
10 of its 11 nodes are encoded, leaving only the vacuum-expectation domain V_k
(`WickRotation/VacuumDomain.lean`) still to do.

## Project Status

The tracked production tree contains **zero `axiom` declarations**: all physics
axioms are fields of `structure`/`class` declarations, and cited infrastructure is
axiomatized as property-classes (never the `axiom` keyword). Proof gaps are
explicit `sorry`s; statements not yet expressible use documented `True`
placeholders.

Snapshot (2026-06-22):

| Metric | Count |
|--------|-------|
| Total `sorry` | **2** |
| Total `True` placeholders | **6** |
| Total `axiom` declarations | **0** |

### Sorry inventory

Both remaining `sorry`s are in one declaration:

| File | `sorry`s | Notes |
|------|----------|-------|
| `ComplexMetrics/Restriction.lean` | 2 | `restrict_allowable` — its `nondegenerate` and `angle_cond` fields (Prop 2.5). Deferred under scope (a): the statement is faithful and complete, but the proof needs a Courant–Fischer min–max / eigenvalue-interlacing characterization not in Mathlib. |

All other Section 2 results are proven (`not_neg_real_axis`,
`volume_element_positive`, `lorentzian_on_boundary`, `only_lorentzian_on_boundary`)
or are `True` placeholders (Defn 2.1 equivalence, Props 2.4/2.7, the two-copies
Shilov statement) blocked on the Hodge star, topology on QC(V), or Stein/Siegel
domain theory.

The **Section 3 and Section 5 files contain no `sorry`s and no `axiom` keyword**:
each node is stated faithfully as `structure`/`class`/`def` declarations, with the
not-yet-constructible analytic content deferred via documented comments rather
than sorrys or stand-ins.

### Detailed status

See [docs/project_status.md](docs/project_status.md) for per-result tracking
against the paper, including the anchor-vs-assume-vs-defer breakdown of each
Section 3 node and the candidate additive tasks.

## Repository Layout

```
KontsevichSegal/
├── Basic.lean                     -- shared imports and notation
├── ComplexMetrics.lean            -- umbrella for ComplexMetrics/
├── ComplexMetrics/                -- Section 2: domain of complex metrics
│   ├── Defs.lean                  -- Theorem 2.2: allowable complex metrics (working def)
│   ├── Equivalence.lean           -- Definition 2.1 ↔ Theorem 2.2 (deferred: Hodge star)
│   ├── Domain.lean                -- QC(V): contractibility, domain of holomorphy
│   ├── Restriction.lean           -- Proposition 2.5: restriction to subspaces
│   └── ShilovBoundary.lean        -- Lorentzian metrics on the Shilov boundary
├── Cobordism.lean                 -- umbrella for Cobordism/
├── Cobordism/                     -- Section 3: the cobordism category
│   └── Category.lean              -- C_d^ℂ: assumed germ geometry + the Semicategory skeleton
├── FieldTheory.lean               -- umbrella for FieldTheory/
├── FieldTheory/                   -- Section 3: field theories as functors
│   ├── NuclearFrechet.lean        -- nuclear Fréchet spaces and nuclear maps (infrastructure)
│   ├── MetCManifold.lean          -- Met_ℂ(M) as a complex manifold (infrastructure)
│   ├── HolomorphicBundle.lean     -- holomorphic vector bundles over Met_ℂ (infrastructure)
│   ├── FieldTheory.lean           -- field theory as a (semicategory) functor; E_Σ, Ě_Σ, Ê_Σ
│   ├── Holomorphicity.lean        -- holomorphicity condition
│   ├── Continuity.lean            -- continuity: injective/dense-image (identity replacement)
│   ├── TensorAxiom.lean           -- disjoint unions to tensor products; E_∅ = ℂ
│   ├── DualConjugate.lean         -- dual (Σ*) and conjugate (Σ̄) functors
│   ├── ConjugateDualDuality.lean  -- plain duality, reality condition (5), conjugate-dual
│   └── Unitarity.lean             -- time-symmetric germs; unitarity
├── WickRotation.lean              -- umbrella for WickRotation/
├── WickRotation/                  -- Section 5: Wick rotation and the gh unitary functor
│   ├── LorentzianCategory.lean      -- node 1: real-analytic Lorentzian cobordism category
│   ├── GloballyHyperbolic.lean      -- node 2: the globally hyperbolic subcategory C_d^gh
│   ├── TimeSymmetricRotation.lean   -- node 3: Wick rotation (geodesic normal form, time-symmetric)
│   ├── Complexification.lean        -- node 4: the complexification hub (infrastructure)
│   ├── InvariancePrinciple.lean     -- node 5: Principle 5.1 (the invariance principle)
│   ├── UnitaryGH.lean               -- node 6: Theorem 5.2 — gh unitary functor + rigged triple
│   ├── LorentzianEWelldefined.lean  -- node 7: Remark 5.3 — Lorentzian Ê_Σ well-defined
│   ├── Observables.lean             -- node 8: the observable spaces 𝒪_x
│   ├── ObservableAction.lean        -- node 9: observable action + ordering-independent map
│   └── SpacelikeCommutativity.lean  -- node 10: spacelike commutativity (Wightman locality)
└── All.lean                       -- full umbrella
KontsevichSegal.lean               -- root entry point
blueprint/
└── src/
    ├── content.tex                -- Section 2 blueprint nodes
    ├── section3.tex               -- Section 3 blueprint nodes
    └── section5.tex               -- Section 5 blueprint nodes
docs/
├── project_status.md              -- authoritative per-result status
├── development_plan.md            -- overall phasing
├── section2_review.md             -- Section 2 audit
├── restrict_allowable_plan.md     -- plan for the remaining Prop 2.5 proof
└── only_lorentzian_plan.md        -- record of the only_lorentzian proof route
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
