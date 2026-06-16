/- The dual and conjugate functors (KS paper Section 3, arXiv:2105.10161): the
first of three nodes building toward unitarity.

This follows the assume-operation / build-functoriality split of the
content-vs-infrastructure rule (CLAUDE.md), the same pattern by which the
`Semicategory` was built on the assumed `concat`:

* ASSUMED geometry (Layer 1, on the cobordism category, never the `axiom`
  keyword, no instance): the two operations on objects, `dual` (Σ ↦ Σ*, with the
  co-orientation reversed) and `conj` (Σ ↦ Σ̄, with the complex metric
  conjugated), together with their actions on cobordisms. `CobordismGeometry`
  provides neither, so they are added here as assumed geometric structure.
* STATABLE functoriality (content, built on top): `dual` is CONTRAVARIANT and
  `conj` is COVARIANT, and both are involutions. These are genuine laws on the
  assumed operations (`dual_dual`, `conj_conj`, `dualMor_contra`, `conjMor_cov`),
  non-vacuous constraints.
* LIMIT-LEVEL dual relation (on the field theory): `Ě_{Σ*}` is the strong dual
  TVS of `Ê_Σ` (`DualRelation`), reusing Mathlib's `StrongDual`.

The dual/conjugate OPERATIONS are on the category geometry; their use in the
limit-dual relation is on the field theory. The boundary is kept clear.

DEFERRED / noted (not faked):
* The metric-conjugation tie to Section 2. The conjugate object `conj o` carries
  the conjugate metric `ḡ`; conjugation maps allowable metrics to allowable
  metrics (`arg λ̄ = −arg λ`, so the angle sum is unchanged, and the
  non-nonpositive-real condition is preserved), but Section 2 provides no
  conjugation operation on `AllowableComplexMetric` / `QC`, so the precise
  `metric (conj o) = conjugate (metric o)` tie is deferred. Likewise `dual`
  leaves the underlying germ and metric unchanged (flipping only the
  co-orientation, which `CobordismGeometry` does not track separately), so that
  is documented rather than forced as a cast-heavy type equality.
* The "algebraic transposes" remark: a cobordism `M : Σ₀ ⤳ Σ₁` is equally
  `Σ₁* ⤳ Σ₀*`, and the induced maps `E_{Σ₀} → E_{Σ₁}` and `E_{Σ₁*} → E_{Σ₀*}`
  are algebraic transposes. Relating `dualMor` to transposes of the functor's `Z`
  rests on the duality of the spaces and the functor's structure; it is recorded
  in prose, not encoded here.

NOTE — this node states ONLY the basic relation it asserts, that `Ě_{Σ*}` is the
dual of `Ê_Σ`. The full conjugate-dual duality `(Ě_Σ)* ≅ Ê_{Σ*}` is the SEPARATE
next node (`def:conjugate-dual-duality`, the Section 3 appendix result) and is
not pre-empted here.

Blueprint: `def:dual-conjugate-functors` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.FieldTheory.FieldTheory
import Mathlib.Topology.Algebra.Module.StrongTopology

open Cobordism

/-! ## Assumed dual and conjugate operations (Layer 1) -/

/-- **Assumed Layer-1 geometry (KS Section 3).** The dual and conjugate
operations on the cobordism geometry, with their functoriality laws.
`CobordismGeometry` provides neither; they are assumed here.

* `dual` (`Σ ↦ Σ*`) reverses the co-orientation, leaving the underlying germ and
  metric unchanged; it is an involution (`dual_dual`). Its action on cobordisms
  (`dualMor`) sends `Mor a b` to `Mor (dual b) (dual a)` and is CONTRAVARIANT
  (`dualMor_contra`).
* `conj` (`Σ ↦ Σ̄`) conjugates the complex metric, leaving the co-orientation
  unchanged; it is an involution (`conj_conj`). Its action on cobordisms
  (`conjMor`) sends `Mor a b` to `Mor (conj a) (conj b)` and is COVARIANT
  (`conjMor_cov`).

The involution and variance laws are genuine, non-vacuous constraints. This
`class` records the assumed operations; it is not constructed for any concrete
family of manifolds. -/
class DualConjugateGeometry [g : CobordismGeometry] where
  /-- `Σ ↦ Σ*`: reverse the co-orientation. -/
  dual : g.Obj → g.Obj
  /-- `Σ* * = Σ`: reversing the co-orientation twice is the identity. -/
  dual_dual : ∀ o, dual (dual o) = o
  /-- The contravariant action of `dual` on cobordisms. -/
  dualMor : ∀ {a b}, g.Mor a b → g.Mor (dual b) (dual a)
  /-- `dual` is contravariant: it reverses the order of composition. -/
  dualMor_contra : ∀ {a b c} (f : g.Mor a b) (h : g.Mor b c),
    dualMor (g.concat f h) = g.concat (dualMor h) (dualMor f)
  /-- `Σ ↦ Σ̄`: conjugate the complex metric. -/
  conj : g.Obj → g.Obj
  /-- `Σ̄̄ = Σ`: conjugating the metric twice is the identity. -/
  conj_conj : ∀ o, conj (conj o) = o
  /-- The covariant action of `conj` on cobordisms. -/
  conjMor : ∀ {a b}, g.Mor a b → g.Mor (conj a) (conj b)
  /-- `conj` is covariant: it preserves the order of composition. -/
  conjMor_cov : ∀ {a b c} (f : g.Mor a b) (h : g.Mor b c),
    conjMor (g.concat f h) = g.concat (conjMor f) (conjMor h)

/-- The composite functor `Σ ↦ Σ̄*` (`dual` of `conj`): it reverses the
co-orientation and conjugates the metric. Being `dual ∘ conj`, it is
contravariant. -/
def dualConj [g : CobordismGeometry] [DualConjugateGeometry] (o : g.Obj) : g.Obj :=
  DualConjugateGeometry.dual (DualConjugateGeometry.conj o)

/-! ## Limit-level dual relation (on the field theory) -/

/-- **The basic dual relation** (KS Section 3, blueprint
`def:dual-conjugate-functors`): for every object, the upstream limit of `Σ*` is
the strong dual topological vector space of the downstream limit of `Σ`,
\[ \check E_{\Sigma^*} \;\cong\; (\hat E_{\Sigma})^*. \]
Stated for a field theory `T` using Mathlib's `StrongDual` and a continuous
linear equivalence (as existence, `Nonempty`).

This is ONLY the relation this node asserts. The full conjugate-dual duality
`(Ě_Σ)* ≅ Ê_{Σ*}` (the Section 3 appendix result) is the separate next node
`def:conjugate-dual-duality` and is not pre-empted here. The condition is on the
functor `T` (not the category). -/
def DualRelation [g : CobordismGeometry] [d : DualConjugateGeometry] (T : FieldTheory) :
    Prop :=
  letI := T.echeckFibres
  letI := T.ehatFibres
  ∀ o, Nonempty (T.ECheck (DualConjugateGeometry.dual o) ≃L[ℂ] StrongDual ℂ (T.EHat o))
