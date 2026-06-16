/- Holomorphic vector bundles over Met_ℂ(M): the third and final analytic
infrastructure object for Section 3 of the Kontsevich-Segal paper
(arXiv:2105.10161).

This is INFRASTRUCTURE-TO-AXIOMATIZE, per CLAUDE.md's "Deliverable scope and
Section 3 strategy": Kontsevich and Segal cite holomorphic vector bundles over
the space of complex metrics as known and do not develop them. We encode the
honest minimum as `class`/`structure`/`def` declarations (never the `axiom`
keyword), anchor the fibre side to the nuclear-Fréchet node, defer the
base-holomorphy side (which rests on the deferred complex-manifold structure of
`MetCManifold`), and construct no instance.

Blueprint: `def:holomorphic-bundle` in `blueprint/src/section3.tex`. Over the
complex manifold Met_ℂ(M) one assumes a locally trivial holomorphic vector
bundle whose fibres are Fréchet spaces (with nuclear comparison maps), together
with morphisms (fibrewise continuous linear maps depending holomorphically on
the base) and pullback along holomorphic maps, in particular along the
restriction maps Met_ℂ(M) → Met_ℂ(Σ_i).

What is anchored, assumed, and deferred:
  - FIBRE side: REUSED. The fibres are Fréchet spaces, anchored to
    `FrechetSpace` from `KontsevichSegal/FieldTheory/NuclearFrechet.lean`. The
    family of fibres is bundled as `FrechetFibres`.
  - BASE / bundle carrier: the fibres sit over the carrier of `Met_ℂ(M)` from
    `KontsevichSegal/FieldTheory/MetCManifold.lean`. `HolomorphicBundle` records
    the assumed fibre family over that carrier.
  - MORPHISMS: the underlying fibrewise continuous `ℂ`-linear maps are stated
    (`BundleMorphism`); the requirement that they depend HOLOMORPHICALLY on the
    base point is DEFERRED (it rests on the deferred complex-manifold structure).
  - DEFERRED (see the closing comment): local triviality and holomorphy over the
    base, and pullback along holomorphic maps. These all depend on the
    complex-manifold structure of `Met_ℂ(M)`, which `MetCManifold` deferred
    because Mathlib's manifolds and vector bundles require normed models, and
    Met_ℂ(M) is Fréchet-modelled. Per No-approximations we do not fake them with
    a normed/finite-dimensional stand-in. Mathlib's `VectorBundle`,
    `ContMDiffVectorBundle`, etc. require a normed model fibre and a normed
    manifold base, so they do not apply here.
-/

import KontsevichSegal.FieldTheory.NuclearFrechet
import KontsevichSegal.FieldTheory.MetCManifold

/-! ## Fréchet fibres (anchored to the nuclear-Fréchet node) -/

/-- A family of fibres `Fibre : B → Type*` is a **Fréchet-space family** if each
fibre is a Fréchet space, anchored to `FrechetSpace` from the nuclear-Fréchet
node. This is the faithful fibre side of a holomorphic vector bundle over
Met_ℂ(M); it reuses real `FrechetSpace` content, not an assumption beyond it. -/
class FrechetFibres {B : Type*} (Fibre : B → Type*) where
  [addCommGroup : ∀ b, AddCommGroup (Fibre b)]
  [moduleComplex : ∀ b, Module ℂ (Fibre b)]
  [moduleReal : ∀ b, Module ℝ (Fibre b)]
  [tower : ∀ b, IsScalarTower ℝ ℂ (Fibre b)]
  [uniform : ∀ b, UniformSpace (Fibre b)]
  [frechet : ∀ b, FrechetSpace (Fibre b)]

attribute [instance] FrechetFibres.addCommGroup FrechetFibres.moduleComplex
  FrechetFibres.moduleReal FrechetFibres.tower FrechetFibres.uniform
  FrechetFibres.frechet

/-! ## Holomorphic vector bundles over Met_ℂ(M) -/

/-- **Assumed (KS Section 3, blueprint `def:holomorphic-bundle`).** A holomorphic
vector bundle over `Met_ℂ(M)`: a family of fibres over the carrier of
`Met_ℂ(M)`, each a Fréchet space (`FrechetFibres`).

This records the honest minimum: the fibre family with its Fréchet structure
anchored to the nuclear-Fréchet node. Local triviality and holomorphy over the
base are DEFERRED (see the closing comment), since they rest on the deferred
complex-manifold structure of `MetCManifold`. The `class` records the assumed
object; it is not constructed for any concrete bundle. -/
structure HolomorphicBundle (M : Type*) [TangentStructure M] [MetCManifold M] where
  /-- The fibre over each point of `Met_ℂ(M)`. -/
  Fibre : MetCManifold.carrier M → Type*
  /-- The fibres form a Fréchet-space family. -/
  [frechetFibres : FrechetFibres Fibre]

attribute [instance] HolomorphicBundle.frechetFibres

/-- **A morphism of holomorphic vector bundles** over `Met_ℂ(M)`, honest part: a
fibrewise continuous `ℂ`-linear map `∀ b, (B₁.Fibre b) →L[ℂ] (B₂.Fibre b)` (KS
Section 3).

The requirement that the map depend HOLOMORPHICALLY on the base point `b` is
DEFERRED: it rests on the deferred complex-manifold structure of `Met_ℂ(M)`. This
type records the underlying fibrewise linear data only. -/
def BundleMorphism {M : Type*} [TangentStructure M] [MetCManifold M]
    (B₁ B₂ : HolomorphicBundle M) : Type _ :=
  letI := B₁.frechetFibres
  letI := B₂.frechetFibres
  ∀ b, B₁.Fibre b →L[ℂ] B₂.Fibre b

/-! ## Deferred structure

The following parts of the blueprint node are NOT encoded here, to avoid faking
or approximating (No-approximations); each rests on the complex-manifold
structure of `Met_ℂ(M)` that `MetCManifold` deferred:

* **Local triviality and holomorphy over the base.** A holomorphic vector bundle
  is locally trivial and holomorphic over the complex manifold Met_ℂ(M). Mathlib
  has `VectorBundle`, `FiberBundle`, `Trivialization`, `ContMDiffVectorBundle`,
  but they require a NORMED model fibre and (for the smooth/holomorphic version)
  a NORMED manifold base. Met_ℂ(M) is Fréchet-modelled with a deferred
  complex-manifold structure, so these do not apply, and a normed/finite-
  dimensional stand-in would diverge from the paper. Hence `HolomorphicBundle`
  records only the fibre family.

* **Holomorphic dependence of morphisms on the base.** `BundleMorphism` records
  the fibrewise continuous linear data; the holomorphy in the base point needs
  the deferred complex structure.

* **Pullback along holomorphic maps** (in particular along the restriction maps
  `Met_ℂ(M) → Met_ℂ(Σ_i)`). The underlying fibre reindexing is straightforward,
  but the restriction maps themselves are deferred in `MetCManifold` and their
  holomorphy rests on the deferred complex structure, so pullback as a holomorphic
  operation is deferred rather than assumed.

These are recorded in `docs/project_status.md`. -/
