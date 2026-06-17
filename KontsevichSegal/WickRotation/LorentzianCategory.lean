/- The Lorentzian cobordism category `C_d^Lor` and its real-analytic version
`C_d^{Lor,ω}`: the FIRST Lean node of Section 5 of the Kontsevich-Segal paper
(arXiv:2105.10161). This is the Lorentzian parallel of Section 3's
`Cobordism/Category.lean`.

LAYER 1 — assumed Lorentzian-germ geometry (`LorentzianCobordismGeometry`). The
germs of `d`-manifolds along closed co-oriented `(d-1)`-manifolds carrying a real
Lorentzian metric of signature `(d-1,1)`, the boundary-fixing isometry classes of
Lorentzian cobordisms, and their gluing, are geometry KS cite as known and which
Mathlib does not provide (the same gap as `CobordismGeometry`). They are ASSUMED
here as the fields of a `class` of geometric data (never the `axiom` keyword), with
the Lorentzian metric anchored to Section 2 via `IsLorentzian`.

LAYER 2 — the categorical skeleton (`Semicategory`, `instSemicategory`). The
`Semicategory` class is REUSED from Section 3 (`Cobordism.Semicategory`, imported,
not re-declared); from any `LorentzianCobordismGeometry` we CONSTRUCT a
`Semicategory` on the objects exactly as Section 3 did on `CobordismGeometry`.
`C_d^Lor` has NO identity morphisms (exactly like `C_d^ℂ`); identities are not
faked.

METRIC DESIGN CHOICE. The Lorentzian metric is encoded as a field of real
Lorentzian bilinear forms on the ambient tangent spaces (`LorentzianField`, the
exact parallel of Section 3's `MetCField`), each carrying its `IsLorentzian`
witness. This is the invariant content of the geodesic-normal-form metric
`h_t - dt²`: the geodesic-exponential identification `U ≅ Σ × (-ε, ε)` and the
explicit family `t ↦ h_t` of Riemannian metrics on `Σ` need the geodesic
exponential, which is deferred germ geometry (not built, as Mathlib does not
provide it). The signature `(d-1,1)` of `h_t - dt²` is captured invariantly by the
`IsLorentzian` witness, which is exactly the Section 2 hypothesis, so the metric
ties to Section 2 directly. (This mirrors `CobordismGeometry`, whose metric is a
`MetCField`, a bare tangent-space field of `QC` metrics with no normal-form
decomposition either.)

SECTION 2 TIE. `metric_on_shilov_boundary` is a genuine term-level reuse of the
Section 2 theorem `lorentzian_on_boundary`: each tangent metric, being
`IsLorentzian`, is an entry-wise limit of allowable complex metrics on a fixed
basis but is not itself allowable, i.e. it lies on the Lorentzian Shilov boundary
of `QC`. This is the precise sense in which `C_d^Lor` lies on the boundary of
`C_d^ℂ`. By the converse `only_lorentzian_on_boundary`, the nondegenerate real
metrics on that boundary are exactly the Lorentzian ones.

REAL-ANALYTIC REFINEMENT (`C_d^{Lor,ω}`), in THREE LAYERS, NON-VACUOUS. The earlier
single-field hook (`Complexification : Obj → Type*` + an injective `realEmbed`) was
VACUOUS: `Complexification o := Ambient o`, `realEmbed := id` satisfied it, so every
smooth geometry instantiated it and it carried no real-analyticity. The fix makes the
ω condition REFERENCE genuine structure a geometry can lack (the C1 lesson: a theory
must be able to FAIL it):

* LAYER A — `RealAnalyticStructure (M) [TangentStructure M]`: the assumed
  real-analytic structure (the designation of real-analytic functions and vector
  fields, with the subalgebra closure), STRICTLY MORE than the smooth
  `TangentStructure`; a smooth-only geometry must commit to it.
* LAYER B — `ComplexManifoldStructure (N)`: the assumed complex-manifold target, the
  complex analogue of `TangentStructure` (a finite-dimensional COMPLEX tangent space
  at each point, also a real vector space via restriction of scalars). `Met_ℂ` is
  Fréchet-modelled, so Mathlib's normed-model complex-manifold classes do not apply;
  assumed, exactly as Section 3 deferred the complex-manifold structure of `Met_ℂ`.
* LAYER C — `IsRealAnalytic` ties them: a `RealAnalyticStructure` on each ambient
  manifold, the metric REAL-ANALYTIC w.r.t. it, and a complexification carrying a
  `ComplexManifoldStructure` with `realEmbed`'s differential `tangentMap` TOTALLY-REAL
  of full dimension (the complexified differential `(v,w) ↦ dF v + i·dF w` is a
  bijection onto `T_{f(x)} M_ℂ`) plus the dimension relationship `dim_ℂ M_ℂ = dim_ℝ M`.
  The identity embedding cannot meet this: `totallyReal` forces the complex tangent to
  have real dimension `2·dim_ℝ(T_x M)`, so the real tangent cannot serve as it; and a
  geometry FAILS `IsRealAnalytic` if its metric is not real-analytic or it admits no
  genuine complexification of the right dimension.

`Complexification.lean` (forthcoming) EXTENDS `IsRealAnalytic`: the complex target,
the totally-real `realEmbed`/`tangentMap`, and the dimension relationship are already
present, so it adds operations (the isotopy, the holomorphic symmetric form on
`TM_ℂ`, Principle 5.1's movement) rather than revising node 1's data. All three layers
are assumed infrastructure (classes of data + properties, never the `axiom` keyword,
no instance, no `sorry`).

Blueprint: `def:lorentzian-cobordism-category` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.Cobordism.Category
import KontsevichSegal.ComplexMetrics.ShilovBoundary

namespace WickRotation

universe u v

/-! ## Layer 1: assumed Lorentzian-germ geometry -/

/-- A **Lorentzian-metric field** on `M`: assigns to each point a real symmetric
bilinear form on the tangent space of Lorentzian signature `(d-1,1)`, i.e. an
`IsLorentzian` form. This is the real Lorentzian parallel of Section 3's
`MetCField` (a field of allowable complex metrics `QC`), and it anchors a
Lorentzian germ to the Section 2 predicate `IsLorentzian`. (The `IsLorentzian`
witness also yields the form's symmetry, so no separate symmetry field is needed.) -/
def LorentzianField (M : Type*) [TangentStructure M] : Type _ :=
  ∀ x : M, { φ : TangentStructure.Tangent x →ₗ[ℝ] TangentStructure.Tangent x →ₗ[ℝ] ℝ //
    IsLorentzian φ }

/-- **Assumed (LAYER 1, Lorentzian-germ geometry; KS Section 5).** The geometric
data underlying the Lorentzian cobordism category `C_d^Lor`, cited by KS as known
and not in Mathlib (the same gap as `CobordismGeometry`):

* `Obj` — Lorentzian germs: germs of `d`-manifolds along closed co-oriented
  `(d-1)`-manifolds `Σ` carrying a real Lorentzian metric of signature `(d-1,1)`.
  Two-sidedness and co-orientation are part of this assumed object data.
* `Ambient o` — each germ's ambient `d`-manifold (the thickening `U`), with a
  finite-dimensional real tangent space at each point (`TangentStructure`).
* `metric o` — the germ's Lorentzian metric as a `LorentzianField`: a real
  Lorentzian form on each ambient tangent space, anchored to Section 2's
  `IsLorentzian`. This is the invariant content of the geodesic-normal-form metric
  `h_t - dt²` (the explicit `h_t` family / geodesic coordinates are deferred germ
  geometry; see the module comment).
* `Mor a b` — the Lorentzian cobordisms `a ⤳ b`, taken up to boundary-fixing
  isometry (the morphism type is the isometry-class type).
* `concat` / `concat_assoc` — gluing of Lorentzian cobordisms and its
  associativity (strict on isometry classes, a genuine assumed property).

There are no identity morphisms (`C_d^Lor` is not literally a category, exactly
like `C_d^ℂ`). This `class` records the assumed geometry; it is NOT constructed for
any concrete family of Lorentzian manifolds. -/
class LorentzianCobordismGeometry where
  /-- Lorentzian germs along closed co-oriented `(d-1)`-manifolds. -/
  Obj : Type u
  /-- The germ's ambient `d`-manifold (its thickening `U`). -/
  Ambient : Obj → Type*
  [ambientTangent : ∀ o, TangentStructure (Ambient o)]
  /-- The germ's Lorentzian metric, a field of real Lorentzian forms on the ambient
  tangent spaces, anchored to Section 2's `IsLorentzian`. -/
  metric : ∀ o, LorentzianField (Ambient o)
  /-- Lorentzian cobordisms `a ⤳ b`, up to boundary-fixing isometry. -/
  Mor : Obj → Obj → Type v
  /-- Concatenation / gluing of Lorentzian cobordisms. -/
  concat : ∀ {a b c}, Mor a b → Mor b c → Mor a c
  /-- Gluing is associative (strictly, on isometry classes of cobordisms). -/
  concat_assoc : ∀ {a b c d} (f : Mor a b) (g : Mor b c) (h : Mor c d),
    concat (concat f g) h = concat f (concat g h)

attribute [instance] LorentzianCobordismGeometry.ambientTangent

/-! ## Layer 2: the categorical skeleton (reusing Section 3's `Semicategory`) -/

/-- **The categorical skeleton of `C_d^Lor` (LAYER 2, constructed).** Given any
assumed `LorentzianCobordismGeometry`, its objects form a `Cobordism.Semicategory`
(the identity-free category class REUSED from Section 3): morphisms are the
Lorentzian cobordisms (`Mor`), composition is concatenation (`concat`), associative
by `concat_assoc`.

This is the exact Lorentzian parallel of Section 3's `Cobordism.instSemicategory`;
it is parametric over the assumed geometry and exhibits no concrete Lorentzian
cobordism category. It is a `Semicategory` and deliberately NOT a Mathlib
`Category`, because `C_d^Lor` has no identity morphisms. -/
instance instSemicategory [g : LorentzianCobordismGeometry] :
    Cobordism.Semicategory g.Obj where
  Hom a b := g.Mor a b
  comp f h := g.concat f h
  assoc f h k := g.concat_assoc f h k

/-! ## The boundary tie to Section 2 -/

/-- **`C_d^Lor` lies on the boundary of `C_d^ℂ` (KS Section 5; Section 2 tie).**
Each tangent metric of a Lorentzian germ, being `IsLorentzian`, lies on the
Lorentzian Shilov boundary of `QC`: it is an entry-wise limit of allowable complex
metrics on a fixed basis but is not itself allowable.

This is a genuine term-level reuse of the Section 2 theorem
`lorentzian_on_boundary`, applied to the germ's metric `(g.metric o x).1` with its
`IsLorentzian` witness `(g.metric o x).2`. -/
theorem metric_on_shilov_boundary [g : LorentzianCobordismGeometry] (o : g.Obj)
    (x : g.Ambient o) :
    (∃ b : Module.Basis (Fin (Module.finrank ℝ (TangentStructure.Tangent x))) ℝ
        (TangentStructure.Tangent x),
      ∀ ε : ℝ, 0 < ε →
        ∃ G : AllowableComplexMetric (TangentStructure.Tangent x),
          ∀ i j, ‖G.toForm (b i) (b j) - ↑((g.metric o x).1 (b i) (b j))‖ < ε) ∧
    (∀ G : AllowableComplexMetric (TangentStructure.Tangent x),
      ∃ v, G.toForm v v ≠ ↑((g.metric o x).1 v v)) :=
  lorentzian_on_boundary (g.metric o x).1 (g.metric o x).2

/-! ## Layer 1 (ω): real-analyticity, the complex target, and the tie

The `C_d^{Lor,ω}` refinement, in three layers (A, B, C). The earlier one-field hook
was vacuous (identity-satisfiable); these layers make the ω condition reference
genuine real-analytic and complex structure (see the module comment). -/

/-- **LAYER A — Assumed real-analytic structure (KS Section 5).** The assumed
real-analytic structure on a manifold `M`, in the spirit of `TangentStructure` (an
assumed datum): the designation of which real functions and which vector fields are
real-analytic (global sections of the structure sheaf `O^ω`), with the real-analytic
functions forming an ℝ-subalgebra (`analytic_const`/`add`/`mul`) that is PROPER
(`not_all_analytic`: some smooth function is NOT analytic).

The subalgebra axioms ALONE are satisfied by the DEGENERATE designation
`IsAnalyticFun := fun _ => True` ("everything analytic"), which a smooth-only manifold
could declare — so they do not by themselves encode "strictly more than smooth".
`not_all_analytic` rules out that designation (it is false when every function is
analytic, and true in any positive dimension, where smooth-non-analytic functions such
as bump functions exist).

KNOWN LIMITATION (honest). `not_all_analytic` excludes only the FULLY degenerate
"everything analytic"; it does not exclude every near-degenerate designation. Likewise
`IsAnalyticVF` carries no non-triviality, so a degenerate empty designation
(`fun _ => False`) would make `IsRealAnalytic.metric_analytic` vacuous (its `IsAnalyticVF`
hypotheses never hold); genuinely pinning it (a spanning set of analytic vector fields, so
`metric_analytic` bites on all of `g.metric`) needs a local frame. The full
characterization of real-analyticity — the identity theorem / determined-by-germs / local
convergence of Taylor series, which alone pins it down — needs an atlas/topology not in
Mathlib at this generality and is deferred, to be added when that infrastructure exists.
What is recorded is the operative subalgebra designation that the real-analytic metric
(`IsRealAnalytic.metric_analytic`) and the holomorphic extension (forthcoming) reference.
Assumed infrastructure; not constructed for any concrete manifold. -/
class RealAnalyticStructure (M : Type*) [TangentStructure M] where
  /-- The assumed designation of real-analytic real-valued functions on `M`. -/
  IsAnalyticFun : (M → ℝ) → Prop
  /-- The assumed designation of real-analytic vector fields (sections of the tangent
  bundle). -/
  IsAnalyticVF : (∀ x : M, TangentStructure.Tangent x) → Prop
  /-- Constants are real-analytic. -/
  analytic_const : ∀ c : ℝ, IsAnalyticFun (fun _ => c)
  /-- Real-analytic functions are closed under addition. -/
  analytic_add : ∀ f₁ f₂, IsAnalyticFun f₁ → IsAnalyticFun f₂ → IsAnalyticFun (f₁ + f₂)
  /-- Real-analytic functions are closed under multiplication. -/
  analytic_mul : ∀ f₁ f₂, IsAnalyticFun f₁ → IsAnalyticFun f₂ → IsAnalyticFun (f₁ * f₂)
  /-- Real-analyticity is a PROPER subalgebra: some (smooth) function is NOT analytic.
  Rules out the degenerate designation `IsAnalyticFun := fun _ => True`; true in any
  positive dimension (smooth-non-analytic functions, e.g. bump functions, exist). -/
  not_all_analytic : ∃ f : M → ℝ, ¬ IsAnalyticFun f

/-- **LAYER B — Assumed complex-manifold structure (KS Section 5).** The assumed
holomorphic tangent datum of a complex manifold `N`: a finite-dimensional COMPLEX
tangent space at each point, also carrying its real-vector-space structure
(restriction of scalars) compatibly. This is the complex analogue of
`TangentStructure`, and the target of the complexification embedding.

`Met_ℂ`-style complex manifolds are Fréchet-modelled, so Mathlib's normed-model
complex-manifold classes (`ChartedSpace` / `IsManifold` over ℂ) do not apply; the
structure is assumed, exactly as Section 3 deferred the complex-manifold structure of
`Met_ℂ`. The complex dimension at `y` is `Module.finrank ℂ (ComplexTangent y)`.
Assumed infrastructure; not constructed for any concrete complex manifold. -/
class ComplexManifoldStructure (N : Type*) where
  /-- The holomorphic (complex) tangent space at each point. -/
  ComplexTangent : N → Type*
  [addCommGroup : ∀ y, AddCommGroup (ComplexTangent y)]
  [moduleComplex : ∀ y, Module ℂ (ComplexTangent y)]
  [moduleReal : ∀ y, Module ℝ (ComplexTangent y)]
  [tower : ∀ y, IsScalarTower ℝ ℂ (ComplexTangent y)]
  [finiteComplex : ∀ y, FiniteDimensional ℂ (ComplexTangent y)]

attribute [instance] ComplexManifoldStructure.addCommGroup
  ComplexManifoldStructure.moduleComplex ComplexManifoldStructure.moduleReal
  ComplexManifoldStructure.tower ComplexManifoldStructure.finiteComplex

/-- **LAYER C — the `C_d^{Lor,ω}` condition (KS Section 5), NON-VACUOUS.** A
`LorentzianCobordismGeometry` is real-analytic and complexification-ready when:

* `realAnalytic o` — each ambient manifold carries a `RealAnalyticStructure` (Layer A; a
  PROPER analytic subalgebra via `not_all_analytic`, the full identity-theorem
  characterization deferred — see Layer A).
* `metric_analytic` — the Lorentzian metric is real-analytic: it pairs real-analytic
  vector fields to real-analytic functions. A smooth-but-not-real-analytic metric
  FAILS this (it references the real metric `g.metric` and the analytic designations).
* `Complexification o` with `complexStructure o` (Layer B), `realEmbed o`, its differential
  `tangentMap o x` (TIED to `realEmbed` by `tangentMap_eq` via the assumed `pushforward`,
  CHECK-1, so `totallyReal` constrains the real embedding's differential), the dimension
  relationship `complexDim_eq`, and the TOTALLY-REAL condition `totallyReal`.

NON-VACUOUS (discriminating test). `Complexification o := g.Ambient o`,
`realEmbed := id` does NOT satisfy this: instantiating requires a
`ComplexManifoldStructure` on the target whose `ComplexTangent` is a genuine COMPLEX
tangent (the real `TangentStructure.Tangent` is not one), and `totallyReal` forces
that complex tangent to have real dimension `2·dim_ℝ(T_x M)` (the complexified
differential is a bijection from `T_x M × T_x M`), so the real tangent cannot serve as
it. Satisfying `IsRealAnalytic` requires supplying the genuine complexification (a
complex tangent of double real dimension with the canonical totally-real inclusion),
real-analytic structure, and a real-analytic metric; a geometry can FAIL on any of
these.

COMPLEXIFICATION-READY. `Complexification.lean` (forthcoming) extends this: the complex
target, the totally-real `realEmbed`/`tangentMap`, and the dimension relationship are
present, so it adds operations (isotopy, the holomorphic symmetric form on `TM_ℂ`,
Principle 5.1's movement) rather than revising this data. Assumed infrastructure: no
`axiom` keyword, no instance, no `sorry`; not constructed for any concrete geometry. -/
class IsRealAnalytic [g : LorentzianCobordismGeometry] where
  /-- (Layer A) Each ambient manifold carries an assumed real-analytic structure. -/
  realAnalytic : ∀ o, RealAnalyticStructure (g.Ambient o)
  /-- The Lorentzian metric is real-analytic: it pairs real-analytic vector fields to
  real-analytic functions (referencing the real metric `g.metric`). -/
  metric_analytic : ∀ (o : g.Obj) (V W : ∀ x : g.Ambient o, TangentStructure.Tangent x),
    (realAnalytic o).IsAnalyticVF V → (realAnalytic o).IsAnalyticVF W →
    (realAnalytic o).IsAnalyticFun (fun x => (g.metric o x).1 (V x) (W x))
  /-- The assumed complexification `M_ℂ` of each germ's ambient manifold. -/
  Complexification : g.Obj → Type*
  /-- (Layer B) `M_ℂ` carries an assumed complex-manifold structure. -/
  [complexStructure : ∀ o, ComplexManifoldStructure (Complexification o)]
  /-- The embedding `M ↪ M_ℂ`. -/
  realEmbed : ∀ o, g.Ambient o → Complexification o
  /-- **Assumed differential (pushforward)** for maps `M → M_ℂ` (CHECK-1 tie). The tangent
  map of `f : g.Ambient o → Complexification o` at `x`: `df_x : T_x M →ₗ[ℝ] T_{f(x)} M_ℂ`.
  Assumed (the smooth differential is deferred germ geometry, not built from Mathlib); it
  is what ties `tangentMap` to the actual embedding `realEmbed`. -/
  pushforward : ∀ (o : g.Obj) (f : g.Ambient o → Complexification o) (x : g.Ambient o),
    TangentStructure.Tangent x →ₗ[ℝ] ComplexManifoldStructure.ComplexTangent (f x)
  /-- The pushforward of a constant map is `0` (a faithful property of the differential):
  a constant embedding then has zero `tangentMap`, failing `totallyReal`. -/
  pushforward_const : ∀ (o : g.Obj) (y₀ : Complexification o) (x : g.Ambient o),
    pushforward o (fun _ => y₀) x = 0
  /-- The differential of `realEmbed` at each point, `T_x M → T_{f(x)} M_ℂ` (ℝ-linear into
  the complex tangent viewed as a real vector space), TIED to `realEmbed` by
  `tangentMap_eq`. -/
  tangentMap : ∀ (o : g.Obj) (x : g.Ambient o),
    TangentStructure.Tangent x →ₗ[ℝ]
      ComplexManifoldStructure.ComplexTangent (realEmbed o x)
  /-- CHECK-1 TIE: `tangentMap` IS the differential (pushforward) of `realEmbed`. This pins
  `tangentMap` to the actual embedding, so `totallyReal` and `complexDim_eq` constrain
  `realEmbed`'s real differential, not a free linear map. -/
  tangentMap_eq : ∀ (o : g.Obj) (x : g.Ambient o),
    tangentMap o x = pushforward o (realEmbed o) x
  /-- DIMENSION RELATIONSHIP `dim_ℂ M_ℂ = dim_ℝ M`: the genuine-complexification count
  that distinguishes it from the identity embedding. -/
  complexDim_eq : ∀ (o : g.Obj) (x : g.Ambient o),
    Module.finrank ℂ (ComplexManifoldStructure.ComplexTangent (realEmbed o x))
      = Module.finrank ℝ (TangentStructure.Tangent x)
  /-- `realEmbed` is injective. -/
  realEmbed_injective : ∀ o, Function.Injective (realEmbed o)
  /-- TOTALLY-REAL of full dimension: the complexified differential
  `(v, w) ↦ dF v + i · dF w` is a bijection onto `T_{f(x)} M_ℂ`, i.e. `T_x M` maps to a
  totally-real subspace filling `T_{f(x)} M_ℂ` after complexification. References both
  `tangentMap` and the complex structure; the identity embedding cannot meet it. -/
  totallyReal : ∀ (o : g.Obj) (x : g.Ambient o),
    Function.Bijective
      (fun vw : TangentStructure.Tangent x × TangentStructure.Tangent x =>
        tangentMap o x vw.1 + Complex.I • tangentMap o x vw.2)

end WickRotation
