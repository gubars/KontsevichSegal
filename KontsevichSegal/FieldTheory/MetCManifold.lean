/- Met_ℂ(M) as a complex manifold: the second analytic infrastructure object for
Section 3 of the Kontsevich-Segal paper (arXiv:2105.10161).

This is INFRASTRUCTURE-TO-AXIOMATIZE, per CLAUDE.md's "Deliverable scope and
Section 3 strategy": Kontsevich and Segal cite the complex-manifold structure on
the space of complex metrics as known and do not develop it. We encode the
assumed structure as `class`/`def` declarations (never the `axiom` keyword),
reuse the Section 2 domain `QC` for the fibre, and construct no instance.

Blueprint: `def:metc-complex-manifold` in `blueprint/src/section3.tex`.
Met_ℂ(M) is the space of complex metrics on `M`, the smooth fields
`x ↦ g_x ∈ Q_C(T_x M)`, assumed to carry an in-general-infinite-dimensional
complex-manifold structure, with the fibre complex structure coming from
`Q_C(T_x M)` being an open domain in the complex vector space of quadratic forms
(Section 2), and with holomorphic restriction maps `Met_ℂ(U) → Met_ℂ(U')` and
`Met_ℂ(M) → Met_ℂ(Σ_i)`.

What Mathlib provides and what is reused / assumed / deferred:
  - Manifolds: Mathlib has `ChartedSpace`, `ModelWithCorners`, `IsManifold`,
    `TangentSpace`, and holomorphic maps (`MDifferentiable`/`ContMDiff` over ℂ).
    But `ModelWithCorners` requires a NORMED model space. Met_ℂ(M) is modelled
    on a Fréchet space (smooth sections), which is not normable, so Mathlib's
    manifold framework cannot express Met_ℂ(M)'s complex-manifold structure
    without a normed/Banach approximation that would diverge from the paper.
    The complex-manifold structure is therefore DEFERRED (see the closing
    comment), not faked.
  - The fibre `Q_C(T_x M)`: REUSED concretely. It is the Section 2 domain `QC`
    (`AllowableComplexMetric`), and `MetCField` below is genuinely built on it.
  - The tangent datum (a finite-dimensional real tangent space at each point):
    part of the smooth-manifold geometry that KS take as given, ASSUMED here as
    `TangentStructure`. Mathlib's `TangentSpace` exists, but its
    finite-dimensionality instance is not transferred through the type synonym,
    so the datum is abstracted rather than wired through `ModelWithCorners`.
  - Met_ℂ(M) as a type, anchored to the fibre: ASSUMED as `MetCManifold` (its
    carrier together with the underlying field of allowable metrics).
-/

import KontsevichSegal.ComplexMetrics.Defs

/-! ## Tangent datum (assumed smooth-manifold geometry) -/

/-- **Assumed (smooth-manifold geometry, KS Section 3).** The tangent datum of a
manifold `M` needed to form complex metrics: a finite-dimensional real tangent
space at each point. This abstracts the part of the smooth structure that the
fibre `Q_C(T_x M)` depends on; it is the cited geometry KS take as given. -/
class TangentStructure (M : Type*) where
  /-- The tangent space at each point. -/
  Tangent : M → Type*
  [addCommGroup : ∀ x, AddCommGroup (Tangent x)]
  [module : ∀ x, Module ℝ (Tangent x)]
  [finiteDimensional : ∀ x, FiniteDimensional ℝ (Tangent x)]

attribute [instance] TangentStructure.addCommGroup TangentStructure.module
  TangentStructure.finiteDimensional

/-! ## Complex-metric fields (reusing the Section 2 domain) -/

/-- A **complex-metric field** on `M`: assigns to each point an allowable complex
metric on the tangent space. The fibre is the Section 2 domain `QC`
(`AllowableComplexMetric`), so this is genuinely built on Section 2 content.

This is the underlying data of a point of `Met_ℂ(M)`. Selecting the smooth
fields (the genuine `Met_ℂ(M)`) needs a smoothness notion on `QC`-valued fields,
which is part of the assumed/deferred manifold structure; see `MetCManifold`. -/
def MetCField (M : Type*) [TangentStructure M] : Type _ :=
  ∀ x : M, QC (TangentStructure.Tangent x)

/-! ## Met_ℂ(M) as an assumed complex manifold -/

/-- **Assumed (KS Section 3, blueprint `def:metc-complex-manifold`).** The space
`Met_ℂ(M)` of complex metrics on `M`. Its `carrier` is the type of complex
metrics, carrying at least a topology; `toField` records that each complex metric
is a field of allowable metrics on the tangent spaces, anchoring `Met_ℂ(M)` to
the Section 2 domain `QC`, and `toField_injective` records that a complex metric
is determined by that field.

The complex-manifold structure, in general infinite-dimensional and modelled on a
Fréchet space, is DEFERRED: Mathlib's manifolds require normed models, so it
cannot be stated faithfully yet (see the closing comment). This `class` records
the assumed object; it is not constructed for any concrete `M`. -/
class MetCManifold (M : Type*) [TangentStructure M] where
  /-- The carrier type of `Met_ℂ(M)`. -/
  carrier : Type*
  /-- `Met_ℂ(M)` is at least a topological space. -/
  [topology : TopologicalSpace carrier]
  /-- Each complex metric is a field of allowable metrics on the tangent spaces. -/
  toField : carrier → MetCField M
  /-- A complex metric is determined by its field of values. -/
  toField_injective : Function.Injective toField

attribute [instance] MetCManifold.topology

/-! ## Deferred structure

The following parts of the blueprint node are NOT encoded here, to avoid faking
or approximating:

* **The complex-manifold structure on `Met_ℂ(M)`.** It is in general
  infinite-dimensional and modelled on a Fréchet space of smooth sections.
  Mathlib's `ModelWithCorners`/`IsManifold` require a normed model space, so the
  genuine structure is not expressible; a normed/Banach model would diverge from
  the paper (No-approximations). Hence `MetCManifold` assumes only the carrier,
  its topology, and the anchoring `toField`. Likewise the smoothness condition
  selecting the genuine `Met_ℂ(M)` inside all complex-metric fields needs a
  manifold structure on `QC`, which is not available.

* **The holomorphic restriction maps** `Met_ℂ(U) → Met_ℂ(U')` and
  `Met_ℂ(M) → Met_ℂ(Σ_i)`. At the level of fields, restriction along an
  inclusion of manifolds is the pointwise Section 2 restriction
  `AllowableComplexMetric.restrict`, whose allowability is Proposition 2.5
  (`restrict_allowable`, proven; the Courant–Fischer min–max it needs was built
  in-repo in `ComplexMetrics/EigenvalueMinmax.lean`), and whose holomorphy is
  part of the deferred complex-manifold structure above. The restriction maps are
  therefore deferred rather than assumed as bare (and hence vacuous) functions.

These are recorded in `docs/project_status.md`. -/
