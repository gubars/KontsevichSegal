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
| `ComplexMetrics/` | Section 2 | **Complete and sorry-free** (scope (a)). The consequences, the Shilov-boundary results, KS Theorem 2.2 (the Definition 2.1 equivalence, proved in both directions via a from-scratch Hodge star), and KS Proposition 2.5 (`restrict_allowable`: restriction of an allowable metric to a subspace remains allowable) are all proven; documented `True`-placeholders remain for the results blocked on Mathlib gaps (Props 2.4/2.7, the two-copies Shilov statement). |
| `Cobordism/` | Section 3 | **Encoded.** The cobordism category C_d^ℂ as an identity-free `Semicategory` (it genuinely has no identity morphisms). |
| `FieldTheory/` | Section 3 | **Encoded — complete under scope (a).** All of Section 3's analytic infrastructure, the field-theory functor, the action of germ isomorphisms, and the functor-condition/axiom nodes (together, all 12 Section 3 blueprint nodes; the condition layer is closed, with time-symmetry stated as the germ-isomorphism predicate Σ ≅ Σ̄* rather than an equality stand-in). Stated faithfully; cited infrastructure is no-instance property-classes, and deep analytic content is deferred to the Mathlib gaps above. |
| `WickRotation/` | Section 5 | **Encoded.** All 11 nodes stated faithfully (scope (a)): the real-analytic Lorentzian / globally-hyperbolic cobordism category, the invariance principle (Principle 5.1), Theorem 5.2 (the gh unitary functor and the rigged triple Ě ⊂ E^Hilb ⊂ Ê), observables and their ordering-independent action, spacelike commutativity, and the vacuum-expectation domain V_k with Proposition 5.4 (V_k ⊇ U_k; the domain-of-holomorphy of V_k kept as KS's open conjecture, stated but not asserted). No `sorry` and no `axiom` — deferrals are documented prose, the same character as the Section 3 rows. |

- **`ComplexMetrics`** (Section 2) — the domain QC(V) of allowable complex
  metrics: the angle condition ∑ᵢ |arg(λᵢ)| < π (working definition, Theorem 2.2),
  its proved equivalence with Definition 2.1 (via a Hodge star built from
  scratch), restriction to subspaces (Prop 2.5, proved via an in-repo
  Courant–Fischer min–max and eigenvalue interlacing), and the Shilov boundary
  (real Lorentzian metrics, and no other nondegenerate real metrics, lie on it).
- **`Cobordism` / `FieldTheory`** (Section 3) — the cobordism category C_d^ℂ; the
  analytic infrastructure (nuclear Fréchet spaces, Met_ℂ(M) as a complex manifold,
  holomorphic vector bundles); a field theory as a holomorphic functor; and its
  conditions: holomorphicity, continuity (the injective/dense-image replacement
  for the missing identity morphisms), the disjoint-union/tensor axiom, the
  action of germ isomorphisms, the dual and conjugate functors, the
  conjugate-dual duality, and unitarity (time-symmetric germs via the
  germ-isomorphism predicate Σ ≅ Σ̄*).
- **`WickRotation`** (Section 5) — Wick rotation and the unitary functor on the
  globally hyperbolic category: the real-analytic Lorentzian cobordism category and
  its globally-hyperbolic subcategory; the Wick rotation of time-symmetric metrics
  (geodesic normal form); the invariance principle (Principle 5.1); Theorem 5.2 (a
  unitary QFT induces a functor sending time-symmetric germs to Hilbert spaces and
  gh cobordisms to unitary operators, with the rigged triple Ě_Σ ⊂ E_Σ^Hilb ⊂ Ê_Σ);
  the well-definedness of the Lorentzian Ê_Σ; the observable spaces 𝒪_x with their
  action and the ordering-independent multilinear map
  𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_Σ; Ê_Σ); spacelike commutativity (the Wightman
  locality axiom); and the vacuum-expectation domain V_k with Proposition 5.4
  (V_k ⊇ U_k, a stated theorem), the domain-of-holomorphy of V_k kept separately as
  KS's open conjecture (stated, never asserted).

Section 4 ("Some analogies from representation theory") is expository analogy with
no KS definitions/axioms/theorems to formalize. All 11 of Section 5's nodes are now
encoded (scope (a): statements stated faithfully, the deep constructions deferred).

## Project Status

**Scope (a) is complete:** all 56 blueprint nodes are green/proved, documented-deferred, or
abstract-by-design (7 dark-green fully-proved results; Sections 2, 3 and 5 all encoded). The
remaining work is scope (b) — deep constructions and open proofs resting on the deferred
Mathlib gaps below.

The tracked production tree contains **zero `axiom` declarations**: all physics
axioms are fields of `structure`/`class` declarations, and cited infrastructure is
axiomatized as property-classes (never the `axiom` keyword). Proof gaps are
explicit `sorry`s; statements not yet expressible use documented `True`
placeholders.

Snapshot (2026-07-10):

| Metric | Count |
|--------|-------|
| Total `sorry` | **0** |
| Total `True` placeholders | **5** |
| Total `axiom` declarations | **0** |

### Sorry inventory

**None — the tree is sorry-free.** The last two `sorry`s, the `nondegenerate`
and `angle_cond` fields of `restrict_allowable` (KS Proposition 2.5), are now
proved. Their proof needed the Courant–Fischer min–max and
eigenvalue-interlacing characterization of the allowable angles, which Mathlib
lacks (it has only the spectral theorem and extremal Rayleigh quotients); that
characterization is built in-repo, from the spectral theorem, in
`ComplexMetrics/EigenvalueMinmax.lean`, and Proposition 2.5's codimension
induction is assembled on top of it in `ComplexMetrics/Restriction.lean`.

All Section 2 results in scope are proven (`not_neg_real_axis`,
`volume_element_positive`, `lorentzian_on_boundary`,
`only_lorentzian_on_boundary`, `defn_2_1_equiv_angle_condition` — KS
Theorem 2.2, both directions — and `restrict_allowable` — KS Proposition 2.5)
or are `True` placeholders (Props 2.4/2.7, the two-copies Shilov statement)
blocked on topology on QC(V) or Stein/Siegel domain theory. Sections 3 and 5
remain scope-(a) encodings: stated faithfully, with the deep analytic and
geometric constructions (the cobordism geometry chain among them) still open.

The **Section 3 and Section 5 files contain no `sorry`s and no `axiom` keyword**:
each node is stated faithfully as `structure`/`class`/`def` declarations, with the
not-yet-constructible analytic content deferred via documented comments rather
than sorrys or stand-ins.

### Detailed status

Per-result tracking against the paper, including the anchor-vs-assume-vs-defer
breakdown of each Section 3 node and the candidate additive tasks, is kept in
`docs/project_status.md`, a local working document that is git-ignored and not
part of the repository; the [Project Status](#project-status) section above is
the shipped summary.

## Repository Layout

```
KontsevichSegal/
├── Basic.lean                     -- shared imports and notation
├── ComplexMetrics.lean            -- umbrella for ComplexMetrics/
├── ComplexMetrics/                -- Section 2: domain of complex metrics
│   ├── Defs.lean                  -- Theorem 2.2: allowable complex metrics (working def)
│   ├── HodgeScaffold.lean         -- the Hodge star ⋆_g, built from scratch
│   ├── Equivalence.lean           -- Definition 2.1 ↔ Theorem 2.2 (proved, via the Hodge star)
│   ├── Domain.lean                -- QC(V): contractibility, domain of holomorphy
│   ├── EigenvalueMinmax.lean      -- Courant–Fischer min–max + interlacing (the Prop 2.5 engine)
│   ├── Restriction.lean           -- Proposition 2.5: restriction to subspaces (proved)
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
│   ├── IsomorphismAction.lean     -- action of germ isomorphisms (assumed germ-iso groupoid)
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
│   ├── SpacelikeCommutativity.lean  -- node 10: spacelike commutativity (Wightman locality)
│   └── VacuumDomain.lean            -- node 11: vacuum-expectation domain V_k / Prop 5.4 (V_k ⊇ U_k)
└── All.lean                       -- full umbrella
KontsevichSegal.lean               -- root entry point
blueprint/
└── src/
    ├── content.tex                -- Section 2 blueprint nodes
    ├── foundations.tex            -- deferred-foundations chapter (15 nodes: assumed classes + built foundations)
    ├── section3.tex               -- Section 3 blueprint nodes
    └── section5.tex               -- Section 5 blueprint nodes
docs/
├── development_plan.md            -- overall phasing
├── blueprint_roadmap_plan.md      -- foundations roadmap (the F-table)
├── section2_review.md             -- Section 2 audit
├── restrict_allowable_plan.md     -- Prop 2.5 proof plan (historical; the proof has landed)
├── project_status.md              -- per-result status (local, git-ignored — not in the repo)
└── only_lorentzian_plan.md        -- only_lorentzian proof route (local — not in the repo)
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
