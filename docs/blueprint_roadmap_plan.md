# Blueprint Roadmap Plan — making the deferred foundations explicit

> **Phase 1 of 2: DESIGN ONLY.** This document is a reviewable plan. It edits no
> `.tex` and no `.lean` file. Phase 2 (a later, separately-approved task) would
> implement the agreed subset as blueprint `\notready` foundation nodes plus the
> `\uses` edges below.

## Purpose and the three-state convention

Today the dependency graph has a green Section 2 island (a handful of genuinely
finished results) and a large field of scope-(a) content nodes whose statements are
faithfully encoded but which silently rest on assumed infrastructure. The deferred
infrastructure is invisible as *graph nodes*: it lives only inside `class` fields and
"deferred" docstrings. The goal is to surface every deferred FOUNDATION as an explicit
orange `\notready` node that the content nodes `\uses`, turning the graph into an
OSReconstruction-style roadmap where the unbuilt walls are visible and attributable.

The convention this plan targets:

- **GREEN** = statement *and* proof formalized **and** resting on no unbuilt foundation
  (transitively). The finish line. leanblueprint renders this **dark green**
  (`#1CAC78`, "proof and all ancestors formalized").
- **SCAFFOLD** = statement faithfully encoded per scope (a); the proof may even
  compile; but the node `\uses` ≥1 orange foundation. A genuinely-compiling proof
  **keeps** its proof-`\leanok` — the "not done" signal is the `\uses` edge into an
  orange foundation (and leanblueprint's regular-green `#9CEC8B`, *not* dark green),
  never the withholding of green.
- **ORANGE** (`\notready`) = either (a) a FOUNDATION not yet built (an assumed
  infrastructure `class` with no instance, or a documented Mathlib gap), or (b) a
  content node whose STATEMENT itself is faked (a `True`-placeholder).

"Green = full formalization including foundations, relative to nothing assumed."

---

## STEP 1+2 — Foundation nodes (enumerated from ground truth, then clustered)

Ground truth used: every assumed `class` in `KontsevichSegal/` (declared with fields,
**no instance ever constructed** — confirmed by the "construct no instance" / "not
constructed for any concrete …" docstrings and by the absence of any concrete
`instance : C := …`; the only `instance`/`attribute [instance]` lines register class
*fields* for typeclass search or build the genuine `Semicategory` skeleton), plus every
documented Mathlib-gap deferral, plus the README's two named gaps.

**Difficulty key:** `grind` = tractable, sit-down-and-formalize; `mathlib` =
Mathlib-contribution-scale (a real library to write); `research` = a genuine wall
(infinite-dim/holomorphic analysis or causal geometry with no Mathlib substrate).

**Classification key:** `STD-GAP` = standard math merely absent from Mathlib;
`KS-CONSTR` = a construction KS defer to "later/known" that is theirs to build;
`ABSTRACT?` = really just parametric/categorical setup that may legitimately never be
instantiated (flagged for a decision).

| # | Label | What it is | `.lean` evidence (assumed class / deferral) | Class | Difficulty |
|---|-------|-----------|----------------------------------------------|-------|-----------|
| F1 | `def:nuclear-frechet` *(EXISTING orange node)* | Nuclear Fréchet spaces, nuclear/trace-class maps, nuclear duality + trace | `NuclearFrechet.lean`: `FrechetSpace`, `IsNuclearFrechetSpace`, `NuclearFrechetDuality`, `IsNuclearMap`, `IsNuclearSpace`; fibre plumbing `NuclearFrechetFibres`/`ComplexTVSFibres` (`FieldTheory.lean`), `FrechetFibres` (`HolomorphicBundle.lean`) | STD-GAP | mathlib |
| F2 | `found:tvs-limits-tensor` *(NEW; today folded into F1's props + `def:field-theory` + `def:tensor-axiom`)* | Countable inverse/direct limits of nuclear maps, and the unique completed tensor product of nuclear spaces | `NuclearFrechet.lean` docstring properties (1) inverse-limit closure, (2) unique tensor product; `FieldTheory.lean` "limit CONSTRUCTION is deferred" (`EHat = lim←`, `ECheck = lim→`); `TensorAxiom.lean` (`MonoidalCobordism`, `IsTensorial`); inverse limits in `Observables`/`LorentzianEWelldefined`. **README gap 2.** | STD-GAP | mathlib |
| F3 | `def:metc-complex-manifold` *(EXISTING orange node)* | `Met_ℂ(M)` as an infinite-dim complex manifold | `MetCManifold.lean`: `TangentStructure`, `MetCManifold`, `MetCField`. **README gap 1.** | STD-GAP | research |
| F4 | `def:holomorphic-bundle` *(EXISTING orange node)* | Locally-trivial holomorphic vector bundles of TVS over `Met_ℂ` | `HolomorphicBundle.lean`: `FrechetFibres`, `HolomorphicBundle`, `BundleMorphism` | STD-GAP | research |
| F5 | `found:smooth-cobordism-geometry` *(NEW; today conflated in `def:cobordism-category`)* | Germs of `d`-manifolds along closed co-oriented `(d−1)`-submanifolds; complex metrics as `Met_ℂ` sections; cobordisms up to boundary-fixing isometry; gluing; disjoint unions | `Cobordism/Category.lean` `CobordismGeometry` (`Ambient`/`metric`/`Mor`/`concat`); `DualConjugate.lean` `DualConjugateGeometry` (Σ\*, Σ̄ ops); `TensorAxiom.lean` `MonoidalCobordism` (⊔). The `def:cobordism-category` "smooth-manifold infrastructure" deferral | KS-CONSTR **+ ABSTRACT?** | research |
| F6 | `found:lorentzian-causal-geometry` *(NEW; conflated in `def:lorentzian-cobordism-category` + `def:globally-hyperbolic`)* | Lorentzian metrics of signature `(d−1,1)`; light-cones; timelike geodesics; smooth time-functions; global hyperbolicity; geodesic normal form `h_t − dt²` | `LorentzianCategory.lean` `LorentzianCobordismGeometry`/`LorentzianField`; `GloballyHyperbolic.lean` `LightConeGeometry`, `GhCategory`; `TimeSymmetricRotation.lean` `GeodesicNormalForm` | KS-CONSTR **+ ABSTRACT?** | research |
| F7 | `found:real-analytic-complexification` *(NEW; conflated in `IsRealAnalytic`/Complexification hub)* | Real-analytic manifold structure and its holomorphic complexification `M_ℂ`: `M` totally real in `M_ℂ`, holomorphic symmetric form `g` on `TM_ℂ` inducing the allowable metric, isotopies inside `M_ℂ`. The paper's "heaviest assumed piece." | `LorentzianCategory.lean` `RealAnalyticStructure`, `ComplexManifoldStructure`, `IsRealAnalytic`; `Complexification.lean` `ComplexAnalyticStructure`, `HolomorphicComplexification`, `Isotopy`, `CurveSubmanifold` | STD-GAP + KS-CONSTR | research |
| F8 | `found:wick-correspondence` *(NEW)* | The boundary relation realizing `C_d^{Lor,ω}` inside `C_d^ℂ`: object-level `cplx` (Lorentzian germ → complex object) and morphism-level `realize` (Lorentzian cobordism → complex cobordism) | `UnitaryGH.lean` `WickObjectCorrespondence`; `InvariancePrinciple.lean` `CobordismRealization`; node-1 `metric_on_shilov_boundary` (tangent-level tie), node-3 `EuclideanSpace` | KS-CONSTR | research |
| F9 | `found:hilbert-completion` *(NEW)* | Completion of the pre-Hilbert `Ě` (under the reflection-positivity pairing) to the Hilbert space `E^Hilb`, sitting in the rigged triple `Ě ⊂ E^Hilb ⊂ Ê` by injective-dense maps with composite `= κ` | `UnitaryGH.lean` `HilbertFibres`; `InducesUnitaryGH` (`EHilb`/`checkIncl`/`hatIncl`/`factor`) | KS-CONSTR | grind→mathlib |
| F10 | `found:observable-bundle` *(NEW)* | The observable bundle on `Met_ℂ(x̂)` and `𝒪_x = lim← E_{∂D}` (inverse limit over boundary spheres of shrinking discs about `x`), with the disc-removal action `E_{∂D} → Hom(E_{Σ₀};E_{Σ₁})` | `Observables.lean` `Observables.Obs`/`Ox`; `ObservableAction.lean` (disc-removal, opaque `Mor`) | KS-CONSTR | research |
| F11 | `found:scv-tube-domain` *(NEW; today scattered across 4 nodes + 1 class)* | Several complex variables: domains of holomorphy / holomorphic envelopes, Bochner's tube theorem, Siegel domains + Cayley transform, the Shilov boundary, the Wightman permuted extended tube `U_k` | `Domain.lean` (Prop 2.7 Stein/Siegel); `ShilovBoundary.lean` (two-copies: Siegel/Cayley/Shilov); `content.tex` Prop 2.3 (Bochner tube), Lemma 2.8 (L-shape); `VacuumDomain.lean` `MinkowskiComplexGeometry.Uk` + `.isDomainOfHolomorphy` | STD-GAP | research |
| F12 | `found:hodge-star` *(NEW; ≈ the math under `def:allowable-hodge`)* | Hodge star `∗_g` for complex metrics + induced quadratic forms on exterior powers `Λ^p(V*)`, with the twisted determinant line | `Defs.lean`, `Equivalence.lean` (`def:allowable-hodge`, `thm:angle-equiv`); `ShilovBoundary.lean` (two-copies `p=0` branch) | STD-GAP | grind→mathlib |
| F13 | `found:homogeneous-bundles` *(NEW)* | `GL(V)/O(V)` and `O_ℂ(Z)` homogeneous-space actions, associated-bundle machinery, the real Grassmannian, and a topology on `QC(V)` (needed even to *state* contractibility) | `Domain.lean` (Prop 2.4 `QC_parametrization`/`QC_contractible`); `content.tex` Prop 2.6 (`prop:real-subspaces`); related small gap: the Courant–Fischer min–max in `Restriction.lean` (Prop 2.5 proof) | STD-GAP | grind→mathlib |
| F14 | `found:minkowski-totally-real` *(NEW; the geometric half of `MinkowskiComplexGeometry`)* | Complexified Minkowski `m_C = E ⊕ iE` with its ℂ-bilinear form (finite-dim, largely Mathlib-able), and totally-real `d`-submanifolds of `m_C` with induced allowable metric | `VacuumDomain.lean` `MinkowskiComplexGeometry` (`mC`/`bilin`/`Eucl`/`projE`/`TotallyRealSub`/`tangentSpace`/`inducedForm`); `Vcheck` | SPLIT: m_C = STD-GAP; submanifolds = KS-CONSTR | linear-alg grind; submanifolds research |

### Notes on the clustering choices (judgment calls)

- **F1 vs F2.** F1 is the *space theory*; F2 is the *limit + tensor construction* (the
  thing that actually realizes `Ê = lim←`, `Ě = lim→`, and `⊗`). They are split because
  F2 is README gap 2, is load-bearing for ~half the content graph, and is a separable
  body of work. **Decision:** split (recommended) vs. keep F2 folded into F1's prose.
- **Fibre-family typeclasses are plumbing, not their own foundations.**
  `NuclearFrechetFibres`, `ComplexTVSFibres`, `FrechetFibres` → F1; `HilbertFibres` → F9;
  `TangentStructure` → F3/F5; `ComplexManifoldStructure`/`ComplexAnalyticStructure` → F7;
  `DualConjugateGeometry` → F5. They thread the foundation per-fibre; they do not merit
  separate nodes.
- **`Semicategory`/`SemicategoryFunctor`/`instSemicategory` are CONTENT, already built**
  (parametric over the assumed geometry). They are *not* foundations; the foundation is
  the geometry the abstract `Obj`/`Mor` stand for (F5).
- **F14 is a split node.** The flat `m_C` linear algebra could reach GREEN with modest
  effort; the totally-real-submanifold half is research-scale and overlaps F7's
  techniques. **Decision:** one node F14, or split into `found:minkowski-linear` (grind)
  and fold the submanifold half into F7?

### Abstract-parametrization flags (the "may stay abstract forever" decisions)

These are the assumed classes that are really the *parametric setup* — a field theory is
defined over an **arbitrary** such geometry, the way an Atiyah-style TQFT is a functor on
an arbitrary cobordism category. Building a concrete instance from real manifolds is
*possible* (it is F5/F6/F7 work) but may **not be a project goal**: staying parametric is
a legitimate permanent end-state.

- **F5 `CobordismGeometry`** and **F6 `LorentzianCobordismGeometry`**: the classes are
  abstract parametrization; the geometry they bundle is buildable. **Decision needed:** is
  exhibiting a concrete `CobordismGeometry`/`LorentzianCobordismGeometry` from real smooth
  manifolds a roadmap goal, or do these stay deliberately abstract (so dependent content
  reaches "as-green-as-possible-relative-to-an-assumed-geometry")?
- **`TangentStructure`, `DualConjugateGeometry`, `GhCategory` (closure/openness),
  `WickObjectCorrespondence`**: arguably permanent parametric plumbing. Flag each: does it
  ever get a concrete instance, or is it definitionally an assumption?

The end-state target is therefore **"every node GREEN *or* deliberately-abstract-with-
reason,"** not necessarily 100% green.

---

## STEP 3a — Foundation `\uses` DAG (among foundations)

Roots (depend on no other foundation): **F1**, **F11**, **F12**, **F13**.

```
F1  nuclear-frechet            (root)
F12 hodge-star                 (root)
F13 homogeneous-bundles        (root)
F11 scv-tube-domain            (root)         [two-copies Shilov branch also touches F12]

F2  tvs-limits-tensor          → F1
F3  metc-complex-manifold      → F1
F4  holomorphic-bundle         → F3, F1
F5  smooth-cobordism-geometry  → F3
F6  lorentzian-causal-geometry → F5
F7  real-analytic-complexif.   → F6, F3
F8  wick-correspondence        → F7, F5
F9  hilbert-completion         → F2
F10 observable-bundle          → F2, F3, F5
F14 minkowski-totally-real     → F11   (shares U_k); submanifold half overlaps F7
```

Longest chain (the deep stack): `F1 → F3 → F5 → F6 → F7 → F8` — the analytic substrate up
through the Wick correspondence. This chain is the project's true critical path.

---

## STEP 3b — Content → foundation edges (the `\uses` edges to add)

Each row: the content node, the foundation(s) it rests on, and the **assumed class /
deferral it actually references** (the justification for the edge). "Status now" uses the
prior task's rendered colors.

### Section 2 (`content.tex`)

| Content node | Add `\uses` | Tied to | Status now |
|---|---|---|---|
| `def:allowable` | — | none (concrete angle condition) | **GREEN** (finish line) ✓ |
| `lem:convex-cone`, `lem:volume-element` | — | none | **GREEN** (dark `#1CAC78`) ✓ |
| `def:trace-norm-fiber`, `def:restrict-form`, `def:lorentzian` | — | none | **GREEN** ✓ |
| `prop:lorentzian-boundary`, `prop:only-lorentzian` | — | none | **GREEN** (dark) ✓ |
| `def:allowable-hodge` (Defn 2.1) | F12 | `∗_g`, exterior powers | ORANGE (stub) |
| `thm:angle-equiv` (Thm 2.2) | F12 | `defn_2_1_equiv_angle_condition` (True) | ORANGE (stub) |
| `prop:conf-envelope` (Prop 2.3) | F11 | Bochner tube, `U_k`, envelope | ORANGE (no decl) |
| `prop:parametrization` (Prop 2.4) | F13 | `GL/O` actions, `QC` topology | ORANGE (stub) |
| `prop:restriction` (Prop 2.5) | F13 (min–max sub-gap) | Courant–Fischer min–max | SCAFFOLD (stmt green, proof `sorry`; blue `#A3D6FF`) |
| `prop:real-subspaces` (Prop 2.6) | F13 | real Grassmannian, `O_ℂ` | ORANGE (no decl) |
| `prop:domain-holomorphy` (Prop 2.7) | F11 | Stein/Siegel | ORANGE (stub) |
| `lem:l-shape` (Lemma 2.8) | F11 | tube extension | ORANGE (no decl) |
| `thm:two-copies` | F12, F11 | Hodge `p=0` branch + Siegel/Shilov | ORANGE (stub) |
| `prop:two-dim-polydisc` | F13 | projective/conformal decomposition | ORANGE (stub) |

### Section 3 (`section3.tex`)

| Content node | Add `\uses` | Tied to | Status now |
|---|---|---|---|
| `def:cobordism-category` | F5 | `CobordismGeometry` (geometry) | SCAFFOLD (conflates F5) |
| `def:nuclear-frechet` | — *(is F1)* | — | ORANGE foundation |
| `def:metc-complex-manifold` | — *(is F3)* | — | ORANGE foundation |
| `def:holomorphic-bundle` | — *(is F4)* | — | ORANGE foundation |
| `def:field-theory` | F1, F2, F5, F4 | `FieldTheory` fibres + deferred `EHat`/`ECheck` limits + `Mor` | SCAFFOLD |
| `def:holomorphicity` | F3, F4 | `IsHolomorphic` over `Met_ℂ` bundles | SCAFFOLD |
| `def:continuity` | F2 | injective-dense maps `Ě→E→Ê` (limit spaces) | SCAFFOLD |
| `def:tensor-axiom` | F2, F5, F1 | `IsTensorial` (⊗) + `MonoidalCobordism` (⊔) | SCAFFOLD |
| `def:dual-conjugate-functors` | F5 | `DualConjugateGeometry` (Σ\*, Σ̄) | SCAFFOLD |
| `def:conjugate-dual-duality` | F1, F2 | nuclear reflexivity; `(Ě)* = Ê_{Σ*}` | SCAFFOLD |
| `def:unitarity` | F9 | pre-Hilbert→`E^Hilb` completion | SCAFFOLD |

### Section 5 (`section5.tex`)

| Content node | Add `\uses` | Tied to | Status now |
|---|---|---|---|
| `def:lorentzian-cobordism-category` | F6, F5, F11 | `LorentzianCobordismGeometry`; Shilov-boundary reuse | SCAFFOLD (stmt green; conflates F6) |
| `def:globally-hyperbolic` | F6 | `LightConeGeometry`, `GhCategory` | SCAFFOLD (stmt green) |
| `def:wick-rotation` | F6, F7, F8 | `GeodesicNormalForm`; `h_{it}` continuation; `EuclideanSpace` | SCAFFOLD (stmt green) |
| `prop:invariance-principle` | F7, F4, F8 | `Isotopy`/`M_ℂ`; holomorphicity; `CobordismRealization` | SCAFFOLD |
| `thm:unitary-gh` | F7, F9, F8, F2 | `M_ℂ`; `E^Hilb`; `cplx`; `Ě`/`Ê` | SCAFFOLD |
| `prop:lorentzian-E-welldefined` | F2, F7, F4 | inverse limit `Ê_f`; bundle `{Ê_f}` | SCAFFOLD |
| `def:observables` | F10, F3, F7, F13 | `Observables.Obs`; complexified tangent; Grassmannian `𝒰` | SCAFFOLD |
| `prop:observable-action` | F10, F2, F5 | `𝒪_x = lim← E_{∂D}`; multilinear/⊗; disc removal | SCAFFOLD |
| **`prop:spacelike-commutativity`** | F9, F8, F10 | rigged Hilbert spaces; propagation `Z`; `𝒪_x` | **SCAFFOLD — proof compiles (green `#9CEC8B`), the one place the convention bites: keep proof-`\leanok`, add orange edges** |
| `def:vacuum-domain` | F14, F11, F10, F7 | `m_C`/totally-real; `U_k`/`isDomainOfHolomorphy`; `𝒪`; allowable submanifolds | SCAFFOLD |
| `prop:Vk-contains-Uk` (Prop 5.4) | F14, F11 | ruled-manifold in `m_C`; `U_k` | SCAFFOLD (proof compiles via assumed `uk_subset_vcheck`; blue `#A3D6FF`) |
| conjecture `VkIsDomainOfHolomorphy` | F11 | `isDomainOfHolomorphy` | folded in `def:vacuum-domain`; never a proved theorem |

---

## STEP 4 — Stub re-audit (independent of foundations)

A node is a STUB (belongs ORANGE regardless of foundations) iff its **statement** is not
actually encoded — a `True`-placeholder or no Lean declaration at all.

**Confirmed stubs (statement faked / absent) — all already correctly `\notready`:**

| Node | Decl | Why orange |
|---|---|---|
| `def:allowable-hodge` (Defn 2.1) | none | statement needs `∗_g` (inexpressible) |
| `thm:angle-equiv` (Thm 2.2) | `defn_2_1_equiv_angle_condition` | `: True` placeholder |
| `prop:parametrization` (Prop 2.4) | `QC_parametrization`, `QC_contractible` | `: True` placeholders |
| `prop:domain-holomorphy` (Prop 2.7) | `QC_domain_of_holomorphy` | `: True` placeholder |
| `thm:two-copies` | `two_copies_on_boundary` | `: True` placeholder |
| `prop:two-dim-polydisc` | `QC_two_dim_polydisc` | `: True` placeholder |
| `prop:conf-envelope` (2.3), `prop:real-subspaces` (2.6), `lem:l-shape` (2.8) | none | no Lean declaration |

These six `True`-placeholders are exactly the project's tracked True count (the `: True`
inventory in `ComplexMetrics/Domain.lean ×4`, `Equivalence.lean`, `ShilovBoundary.lean`).
**No change of color needed — they are already orange.** Their only refinement is the
F11/F12/F13 `\uses` edges above (so the orange foundation they need is explicit).

**Re-check of the Section 5 nodes flipped to statement-green last task**
(`def:lorentzian-cobordism-category`, `def:globally-hyperbolic`, `def:wick-rotation`):

- **Verdict: real faithful statements, NOT stubs.** Each is a genuine
  `class`/`structure`/`def` with real fields (`LorentzianCobordismGeometry`,
  `LightConeGeometry`, `GhCategory`, `TimeSymmetricRotation`, …) that compile and encode
  KS's definitions faithfully. None is a `True`-placeholder. **Statement-green (green
  border) is correct.**
- **But under this task's stricter convention they are SCAFFOLD, not GREEN:** they rest
  on the assumed geometry classes (F5/F6/F7). The green border stays; the refinement is
  the orange `\uses` edges in §3b, which make them read as "green atop orange" rather
  than risk reading as finished. This is a *refinement* of last task's "all 11 nodes
  green-bordered," not a reversal — the border was right; the missing piece was the
  foundation ancestry.

**No currently-green node is secretly a stub.** And (separately) **no
currently-dark-green node secretly rests on a foundation**: the dark-green nodes are
exactly Section 2's proved core (`convex-cone`, `volume-element`, `lorentzian-boundary`,
`only-lorentzian`), which depend only on the concrete `def:allowable`/`def:lorentzian`.
The Section 2 green island is a *genuine* finish-line island.

---

## STEP 5 — Rendering mechanics (does the gap show on its own?)

**Finding: YES — leanblueprint already distinguishes the fully-resolved frontier from
"proved atop unbuilt foundations," automatically, via two shades of green.** Evidence
from this project's *currently rendered* `blueprint/web/dep_graph_document.html`
(legend + node fills):

- Legend: **"Green background — the proof of this result is formalized"** vs **"Dark green
  background — the proof of this result *and all its ancestors* are formalized."**
- `prop:only-lorentzian` (proved, all ancestors concrete) renders **dark green
  `#1CAC78`** — the finish line.
- `prop:spacelike-commutativity` (proved, but transitively `\uses` the orange
  `def:field-theory`) renders **regular green `#9CEC8B`** — proved-atop-unbuilt.

So the mechanism the task asks for **exists and is automatic**: a node only goes dark
green when its entire `\uses` ancestry is built. Adding the §3b foundation edges does not
*create* the distinction — it makes it **complete and honest**, guaranteeing every
scaffold node has an orange ancestor and so can never mis-render as dark-green/finished.
(Today node 9 is already `#9CEC8B` only because it happens to reach an orange Section 3
node; the edges make that robust for every scaffold node and every future compiling
proof.)

**Caveat / minimal optional convention.** `#9CEC8B` (scaffold) vs `#1CAC78` (finish) are
two similar greens — the distinction is real but *subtle* at a glance. If a sharper
visual is wanted, the minimal additions (convention only, no tool change) are:

1. **Make the foundations visually loud** — they are orange nodes, which already stand
   out; grouping the `found:*` nodes in their own blueprint section ("Deferred
   foundations") makes the orange wall a legible region the green/scaffold nodes point
   into.
2. **Legend callout** distinguishing the two greens in words (see STEP 6), so a reader
   knows `#9CEC8B` ≠ done.
3. (Heavier, optional) a custom CSS tweak to `blueprint/web` deepening the dark-green or
   adding a border to dark-green-only nodes. Not recommended for Phase 2; the two-greens
   semantics is already correct.

Net: **no code change is required for the gap to be visible** — only the `\uses` edges,
which are the substance of this plan.

---

## STEP 6 — Legend draft (for the blueprint chapter intro and/or README)

> **Reading this graph.** Each result is colored by how far its formalization rests on
> solid ground.
>
> - **Green (finish line).** Statement and proof are formalized in Lean **and every
>   result it depends on, transitively, is too** — it rests on nothing assumed. *Green
>   means full formalization including foundations, relative to nothing assumed.*
>   leanblueprint renders this as the **dark green** fill.
> - **Scaffold (green atop orange).** The statement is faithfully encoded (deliverable
>   scope (a)) and the proof may even compile, **but the result still depends on at least
>   one orange foundation that has not been built.** A compiling proof keeps its green;
>   the "not yet on solid ground" signal is the dependency edge into an orange node (and
>   leanblueprint's lighter green, not the dark finish-line green). Most of Sections 3
>   and 5 are scaffold.
> - **Orange (`\notready`).** Either a **deferred foundation** — a piece of infrastructure
>   the paper cites as known but does not build (nuclear Fréchet spaces and their limits
>   and tensor products; infinite-dimensional complex manifolds and holomorphic bundles;
>   the smooth/Lorentzian cobordism geometry; the holomorphic complexification `M_ℂ` and
>   Wick correspondence; the Hilbert completion; the observables; several-complex-variable
>   tube/Stein/Shilov theory; the Hodge star) encoded as a class of assumed properties
>   with no instance — **or** a content node whose statement cannot yet be expressed at
>   all and stands in as a `True`-placeholder.
>
> **The roadmap.** The orange foundations are the explicit list of unbuilt walls; every
> scaffold node names, by its dependency edges, which walls it is waiting on. The project
> is "done" when every node is **green, or a foundation deliberately left abstract with a
> recorded reason** — a field theory is defined over an *arbitrary* cobordism geometry, so
> some parametric foundations (the abstract cobordism/Lorentzian geometry classes) may
> legitimately never be instantiated. The end-state is therefore *every node green or
> deliberately-abstract-with-reason*, not necessarily 100% green.

---

## STEP 7 — Consolidated judgment calls / decisions for review

1. **Abstract-parametrization (the central decision).** Are F5
   (`CobordismGeometry`) and F6 (`LorentzianCobordismGeometry`) buildable foundation
   goals, or deliberately-permanent parametric assumptions? Same question for
   `TangentStructure`, `DualConjugateGeometry`, `GhCategory`, `WickObjectCorrespondence`.
   This decides whether the deep critical path `F1→F3→F5→F6→F7→F8` is "to build" or "to
   bless as abstract."
2. **Graph-only vs. `.lean` refactor for the conflated geometry nodes.**
   `def:cobordism-category` / `def:lorentzian-cobordism-category` /
   `def:globally-hyperbolic` / `def:wick-rotation` each *introduce* an assumed geometry
   class **and** state KS content. Two Phase-2 routes:
   - **(a) graph-only (lighter):** keep the nodes, mark them scaffold, add a separate
     `found:*` foundation node + a `\uses` edge. Some redundancy (both reference the same
     class), no `.lean` change.
   - **(b) refactor (cleaner):** split each geometry `class` in `.lean` into an assumed
     "geometry" class (→ `found:*`) and the KS-content structure that consumes it, so the
     node/foundation separation is physical. Heavier; touches `.lean`.
3. **Split F2 out of F1?** Recommended yes (README gap 2, load-bearing). Confirm.
4. **Split F14?** `found:minkowski-linear` (grind, near-green) + fold the submanifold half
   into F7, vs. one node.
5. **Relabel the 3 existing infra nodes** (`def:nuclear-frechet`, `def:metc-complex-manifold`,
   `def:holomorphic-bundle`) to `found:*`? Cosmetic and it **breaks existing `\uses`
   references** — recommend **keeping their labels**, just classifying them as foundations
   in the legend/section.
6. **Where do the new `found:*` nodes live?** Recommend a new "Deferred foundations"
   chapter/section in the blueprint (its own `foundations.tex`), so the orange wall is one
   legible region, with Sections 2/3/5 pointing into it. (Phase-2 file decision.)
7. **The min–max sub-gap** (`prop:restriction`/Prop 2.5 proof): list as its own tiny
   foundation, or note it under F13? Recommend note under F13 (it is one lemma, not a
   body of theory).
8. **`prop:spacelike-commutativity` is the load-bearing test of the convention.** It is
   the only Section-5 node whose proof compiles; the plan deliberately *keeps* its
   proof-`\leanok` and adds orange `\uses` edges (F9/F8/F10) so it reads as scaffold
   (`#9CEC8B`), not finish (`#1CAC78`). Confirm this is the intended reading of "a
   genuinely-compiling proof keeps its proof-green."

---

## STEP 8 — What Phase 2 would do (NOT done here)

For reference only; nothing below is executed in Phase 1.

1. Add ~11 new `found:*` `\notready` foundation nodes (F2, F5–F14) — recommended in a new
   `blueprint/src/foundations.tex` — each with the "what it is / what's missing / why
   deferred" prose already drafted in the STEP-1 table.
2. Add the §3b `\uses` edges from content nodes to foundations (statement-level and, where
   a proof leans on a foundation, proof-level `\uses`).
3. Leave the 3 existing infra nodes as the foundations they already are.
4. Resolve decisions §7 (esp. abstract-parametrization and graph-only-vs-refactor) before
   touching any `.lean`.
5. Rebuild (`leanblueprint web` + `checkdecls`) and confirm: Section 2's proved core stays
   dark-green; every scaffold node (incl. `prop:spacelike-commutativity`) renders regular
   green / blue / green-border with at least one orange ancestor; the new `found:*` nodes
   render orange.

*No `.tex` or `.lean` file was modified by this plan.*
