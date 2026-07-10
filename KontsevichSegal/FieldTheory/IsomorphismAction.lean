/- The isomorphism-action axiom on a field theory (KS paper Section 3,
arXiv:2105.10161; KSTeX line 408): a germ isomorphism acts on the field
theory's spaces, smoothly in the isomorphism.

THE PAPER'S CLAUSE. "Whichever line we take, we must assume that an isomorphism
f : Σ₀ → Σ₁ of germs of d-manifolds induces an isomorphism f_* : E_{Σ₀} → E_{Σ₁}
which depends smoothly on f, in the sense that for any family P × Σ₀ → Σ₁
parametrized by a finite-dimensional manifold P the induced map
P × E_{Σ₀} → E_{Σ₁} is smooth."

This is a condition ON THE FUNCTOR (a `FieldTheory`), never on the cobordism
category (Category vs. functor boundary, CLAUDE.md), encoded without the `axiom`
keyword and without exhibiting any concrete instance. Two assumed layers feed it:

* ASSUMED Layer-1 geometry (`GermIsoGeometry`): the groupoid of germ
  isomorphisms. Isomorphisms of metric germs (preserving the complex metric and
  the co-orientation, bundled into the assumed object data exactly as in
  `CobordismGeometry.Obj`) are smooth-germ geometry absent from Mathlib — the
  `found:smooth-cobordism-geometry` gap — and precisely the structure
  `Unitarity.lean`'s time-symmetry predicate consumes: `GermIsoGeometry` now
  supplies that object/germ-isomorphism notion, and `IsTimeSymmetric` has been
  upgraded to `Nonempty (GermIsoGeometry.Iso o (dualConj o))` (the witness is
  "a germ diffeomorphism, not a cobordism"; the reflection's involutivity and
  fixed-point-set content are NOT captured here and remain deferred). Unlike the cobordisms, germ
  isomorphisms DO have identities and inverses, so the honest interface is a
  groupoid: `Iso`, `idIso`, `compIso`, `invIso` with the five groupoid laws.
  NOT Mathlib's `CategoryTheory.Groupoid`: that extends `Category` →
  `CategoryStruct` → `Quiver`, and `Cobordism.instSemicategory` already installs
  the `Quiver` on `g.Obj` with `⟶` the cobordisms; a second `Quiver` instance on
  the same type would collide. The assumed smooth-family notion
  (`IsSmoothIsoFamily`: which `P`-families of isomorphisms are the paper's
  smooth families `P × Σ₀ → Σ₁`) also lives here: it is germ geometry.

* ASSUMED infrastructure (`SmoothLinearFamilies`): smoothness for a `P`-family
  of continuous linear maps into the Fréchet fibres. Mathlib's manifold calculus
  (`ModelWithCorners`, `MDifferentiable`, `ContMDiff`) requires NORMED model
  spaces, so no genuine smoothness notion exists for Fréchet targets (the same
  Fréchet-manifold gap as `MetCManifold`/`HolomorphicBundle`), and the abstract
  parameter manifold (`TangentStructure`) carries no calculus at all. The notion
  is therefore assumed as a predicate, PINNED, not floating: constant families
  are smooth (`isSmoothMapFamily_const`) and smooth families are JOINTLY
  CONTINUOUS (`isSmoothMapFamily_continuous`). The pin excludes the
  everything-is-smooth satisfier (`fun _ => True` would assert every family
  jointly continuous, which is false), so the assumed predicate cannot collapse
  below joint continuity.

* THE AXIOM (`IsoAction`): the action `f ↦ f_*`, landing in genuine continuous
  linear equivalences `T.E a ≃L[ℂ] T.E b` ("induces an ISOMORPHISM"), pinned
  float-free by functoriality — `act_id` and `act_comp` make `act` a groupoid
  representation, not a free family of equivalences — and depending smoothly on
  `f` (`act_smooth`, stated against the two assumed smoothness notions). NO
  `f_*`-vs-`Z` compatibility field is added: the paper asserts none in this
  clause (No-approximations cuts both ways).

NON-VACUITY. `GermIsoGeometry` cannot be emptied (`idIso` forces every
`Iso o o` inhabited). `IsoAction` bites three ways: (i) `act_comp` pins `act` —
an idempotent `f` (`compIso f f = f`) forces `act f = refl`, and
`(f⁻¹)_* = (f_*)⁻¹` is FORCED (`IsoAction.act_inv`, proved below); (ii)
whenever the assumed geometry makes `Iso a b` nonempty, `act` forces
`T.E a ≃L T.E b`, so a theory whose fibres are not isomorphic across isomorphic
germs cannot carry an `IsoAction`; (iii) along smooth families the action must
be jointly continuous, via the pin. Over the degenerate discrete geometry
(`Iso a b := PLift (a = b)`) a transport satisfier exists; that is the standard
scope-(a) state of every Layer-1 parametric class here (`MonoidalCobordism`,
`DualConjugateGeometry`), never instantiated by design.

DEFERRED (documented, not faked): any genuine smooth structure on the
germ-isomorphism spaces, and genuine calculus on maps into Fréchet fibres —
both rest on the smooth-germ geometry and Fréchet-manifold gaps recorded at
`found:smooth-cobordism-geometry` and `def:metc-complex-manifold`.

Blueprint: `def:isomorphism-action` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.FieldTheory.FieldTheory

open Cobordism

universe u v w

/- Register the field-theory fibre data as a file-local instance, so `T.E`
carries its TVS structure in the field types below (`WickRotation/UnitaryGH.lean`
makes the same registration globally for Section 5; local here keeps Section 3's
instance surface unchanged). -/
attribute [local instance] FieldTheory.eFrechet

/-! ## Assumed germ-isomorphism geometry (Layer 1) -/

/-- **Assumed Layer-1 geometry (KS Section 3, KSTeX line 408).** The groupoid of
germ isomorphisms over the cobordism geometry: isomorphisms of metric germs
(preserving the complex metric and the co-orientation, bundled into the assumed
data as in `CobordismGeometry.Obj`), with identities, inverses, associative
composition, and the assumed notion of a smooth `P`-family of isomorphisms.

Germ isomorphisms are NOT cobordisms (`Mor`): unlike the cobordisms they have
identities and inverses, forming a genuine groupoid. Mathlib's
`CategoryTheory.Groupoid` is not used because it extends `Category` →
`CategoryStruct` → `Quiver`, and `Cobordism.instSemicategory` already installs
the `Quiver` on `g.Obj` with `⟶` the cobordisms. This `class` records the
assumed geometry; it is not constructed for any concrete family of manifolds. -/
class GermIsoGeometry [g : CobordismGeometry] where
  /-- Isomorphisms of germs `Σ₀ → Σ₁`: metric-germ diffeomorphisms, preserving
  the complex metric and the co-orientation (part of the assumed data). -/
  Iso : g.Obj → g.Obj → Type*
  /-- The identity isomorphism (germ isomorphisms, unlike cobordisms, have
  identities). -/
  idIso : ∀ o, Iso o o
  /-- Composition of germ isomorphisms (diagrammatic order). -/
  compIso : ∀ {a b c}, Iso a b → Iso b c → Iso a c
  /-- Inversion of germ isomorphisms. -/
  invIso : ∀ {a b}, Iso a b → Iso b a
  /-- Composition is associative. -/
  compIso_assoc : ∀ {a b c d} (f : Iso a b) (h : Iso b c) (k : Iso c d),
    compIso (compIso f h) k = compIso f (compIso h k)
  /-- Left identity law. -/
  idIso_comp : ∀ {a b} (f : Iso a b), compIso (idIso a) f = f
  /-- Right identity law. -/
  compIso_idIso : ∀ {a b} (f : Iso a b), compIso f (idIso b) = f
  /-- Inverse law `f ≫ f⁻¹ = id` (diagrammatic order). -/
  compIso_invIso : ∀ {a b} (f : Iso a b), compIso f (invIso f) = idIso a
  /-- Inverse law `f⁻¹ ≫ f = id` (diagrammatic order). -/
  invIso_compIso : ∀ {a b} (f : Iso a b), compIso (invIso f) f = idIso b
  /-- Assumed: which families of germ isomorphisms, parametrized by an abstract
  finite-dimensional manifold `P` (`TangentStructure`, with a topology), are the
  paper's smooth families `P × Σ₀ → Σ₁`. -/
  IsSmoothIsoFamily : ∀ {P : Type u} [TangentStructure P] [TopologicalSpace P]
    {a b : g.Obj}, (P → Iso a b) → Prop
  /-- Constant families of isomorphisms are smooth. -/
  isSmoothIsoFamily_const : ∀ {P : Type u} [TangentStructure P]
    [TopologicalSpace P] {a b : g.Obj} (f : Iso a b),
    IsSmoothIsoFamily (fun _ : P => f)

/-! ## Assumed smoothness for families of linear maps into Fréchet fibres -/

/-- **Assumed infrastructure (KS Section 3, KSTeX line 408).** Smoothness for a
family of continuous linear maps between topological `ℂ`-vector spaces,
parametrized by an abstract finite-dimensional manifold `P` (`TangentStructure`,
with a topology). Mathlib's manifold calculus requires normed model spaces, so
no genuine notion exists for the Fréchet fibres of a field theory; the notion is
assumed as a predicate, PINNED by two laws: constant families are smooth, and
smooth families are jointly continuous. The pin excludes the trivial
`fun _ => True` satisfier (it would assert every family jointly continuous,
which is false), so the assumed notion cannot collapse below joint continuity.
This `class` records assumed structure (never the `axiom` keyword); no instance
is constructed. -/
class SmoothLinearFamilies where
  /-- Which `P`-families of continuous linear maps are smooth. -/
  IsSmoothMapFamily : ∀ {P : Type u} [TangentStructure P] [TopologicalSpace P]
    {E : Type v} {F : Type w} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F],
    (P → (E →L[ℂ] F)) → Prop
  /-- Constant families are smooth. -/
  isSmoothMapFamily_const : ∀ {P : Type u} [TangentStructure P]
    [TopologicalSpace P] {E : Type v} {F : Type w} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (S : E →L[ℂ] F), IsSmoothMapFamily (fun _ : P => S)
  /-- The pin: a smooth family is jointly continuous `P × E → F`. -/
  isSmoothMapFamily_continuous : ∀ {P : Type u} [TangentStructure P]
    [TopologicalSpace P] {E : Type v} {F : Type w} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (Φ : P → (E →L[ℂ] F)), IsSmoothMapFamily Φ →
    Continuous (fun q : P × E => Φ q.1 q.2)

/-! ## The action of germ isomorphisms on a field theory -/

/-- **The isomorphism-action axiom on a field theory (KS Section 3, KSTeX line
408; blueprint `def:isomorphism-action`).** A germ isomorphism `f : Σ₀ → Σ₁`
induces an isomorphism `f_* : E_{Σ₀} ≃L E_{Σ₁}`, functorially and smoothly:

* `act` — the action `f ↦ f_*`, a genuine continuous linear equivalence
  ("induces an ISOMORPHISM");
* `act_id`, `act_comp` — functoriality, the float-free pin: `act` is a groupoid
  representation, not a free family of equivalences (these force
  `(f⁻¹)_* = (f_*)⁻¹`, proved as `IsoAction.act_inv`);
* `act_smooth` — the smooth dependence on `f`: a smooth family of isomorphisms
  induces a smooth family `P × E_{Σ₀} → E_{Σ₁}`, stated against the assumed
  smoothness notions (whose continuity pin makes it bite).

NO `f_*`-vs-`Z` compatibility field: the paper asserts none in this clause. A
condition on the functor, never the category. Not constructed for any concrete
theory. -/
structure IsoAction [g : CobordismGeometry] [gi : GermIsoGeometry]
    [sf : SmoothLinearFamilies] (T : FieldTheory) where
  /-- `f ↦ f_*`: the induced continuous linear isomorphism on the fibres. -/
  act : ∀ {a b : g.Obj}, GermIsoGeometry.Iso a b → (T.E a ≃L[ℂ] T.E b)
  /-- `(id_Σ)_* = id`. -/
  act_id : ∀ o, act (GermIsoGeometry.idIso o) = ContinuousLinearEquiv.refl ℂ (T.E o)
  /-- `(g ∘ f)_* = g_* ∘ f_*` (diagrammatic order: the functoriality pin). -/
  act_comp : ∀ {a b c : g.Obj} (f : GermIsoGeometry.Iso a b)
    (h : GermIsoGeometry.Iso b c),
    act (GermIsoGeometry.compIso f h) = (act f).trans (act h)
  /-- Smooth dependence on `f`: a smooth family of isomorphisms induces a smooth
  family of maps on the fibres. -/
  act_smooth : ∀ {P : Type u} [TangentStructure P] [TopologicalSpace P]
    {a b : g.Obj} (φ : P → GermIsoGeometry.Iso a b),
    GermIsoGeometry.IsSmoothIsoFamily φ →
    SmoothLinearFamilies.IsSmoothMapFamily
      (fun p => (act (φ p) : T.E a →L[ℂ] T.E b))

/-- **`(f⁻¹)_* = (f_*)⁻¹`.** Forced by the functoriality pin: from
`act_comp (invIso f) f`, the inverse law `invIso_compIso`, and `act_id`, the
composite `(f⁻¹)_* ≫ f_*` is the identity, and applying `(f_*)⁻¹` pointwise
identifies `(f⁻¹)_*` with `(f_*).symm`. Genuine content of the groupoid
representation (the paper's "induces an isomorphism", closed under inverses). -/
theorem IsoAction.act_inv [g : CobordismGeometry] [gi : GermIsoGeometry]
    [sf : SmoothLinearFamilies] {T : FieldTheory} (A : IsoAction T)
    {a b : g.Obj} (f : GermIsoGeometry.Iso a b) :
    A.act (GermIsoGeometry.invIso f) = (A.act f).symm := by
  have h2 : (A.act (GermIsoGeometry.invIso f)).trans (A.act f)
      = ContinuousLinearEquiv.refl ℂ (T.E b) := by
    rw [← A.act_comp, GermIsoGeometry.invIso_compIso, A.act_id]
  refine DFunLike.ext _ _ fun y => ?_
  have h2y : A.act f (A.act (GermIsoGeometry.invIso f) y) = y := by
    simpa [ContinuousLinearEquiv.trans_apply] using DFunLike.congr_fun h2 y
  have h3 := congrArg (A.act f).symm h2y
  rwa [ContinuousLinearEquiv.symm_apply_apply] at h3
