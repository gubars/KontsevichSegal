/- The complexification `M_ℂ` infrastructure: the FOUNDATIONAL HUB of Section 5 of the
Kontsevich-Segal paper (arXiv:2105.10161). Built on node 1 (`LorentzianCategory.lean`).

WHAT THIS FILE IS. It is INFRASTRUCTURE, not a content node: it encodes no single
blueprint definition/theorem, carries no `\lean` annotation, and maps to no blueprint
label of its own. It is the Lean realization of the heaviest ASSUMED-INFRASTRUCTURE
bullets of `prop:invariance-principle` (Principle 5.1) and `thm:unitary-gh`
(Theorem 5.2) — the pieces KS cite as given. The eventual `\lean` annotation for this
material lands on `prop:invariance-principle`, pointing at the forthcoming
`InvariancePrinciple.lean` (node 5), which IMPORTS this hub. Like Section 3's
`MetCManifold.lean` / `NuclearFrechet.lean`, it provides assumed objects (opaque data
+ genuine properties), never the `axiom` keyword, never a concrete instance.

WHAT IT REALIZES (KS Principle 5.1, KSTeX line 669, and its proof setup, line 707).
Principle 5.1: "If a `d`-dimensional cobordism `M` is a real submanifold of a complex
`d`-manifold `M_ℂ`, and `M` has an allowable complex metric INDUCED FROM a holomorphic
symmetric form `g` on the tangent bundle `TM_ℂ`, then `Z_M` does not change when `M` is
moved around smoothly inside `M_ℂ` (leaving its ends fixed), providing the restriction
of `g` to `M` remains an allowable complex metric." This hub provides, on top of
node 1's `IsRealAnalytic`:

* the holomorphic symmetric form `g` on `TM_ℂ` (`holForm`), with `M`'s allowable
  complex metric INDUCED from it by restriction along the totally-real embedding
  (`inducedMetric`, tied by `inducedMetric_eq` — "induced from", not float-free);
* the smooth isotopy of `M` inside `M_ℂ` holding the ends fixed, with `g|M_s` staying
  allowable (`Isotopy`), the movement Principle 5.1 quantifies over;
* the totally-real submanifold `M_f` over a curve `f:[0,1]→U` with `f(0)=0`,
  `Re f'(s)>0` (`CurveSubmanifold`), from the proof setup at line 707.

This hub does NOT encode `Z_M` or Principle 5.1's invariance statement (those live on
`FieldTheory`, node 5); it provides the `M_ℂ`-movement the invariance is stated over.

EXTENDS node 1, does NOT revise it. `HolomorphicComplexification extends IsRealAnalytic`,
building on node 1's `Complexification`/`complexStructure`/`realEmbed`/`tangentMap`/
`pushforward`/`pushforward_const`/`totallyReal`/`complexDim_eq` (exactly as node 1's
docstring anticipated: "it adds operations ... rather than revising this data").
node 1's file is UNCHANGED. The only downstream addition is
`attribute [instance] IsRealAnalytic.complexStructure`, registering node 1's
(inherited) complex-structure field as a global instance so `ComplexTangent` of the
complexification resolves outside node 1's class body; this registers, it does not
revise.

DEFERRED (documented, not faked). The holomorphic fibre bundle `τ = it : M_ℂ → U` and
its holomorphic trivialization (carried as the assumed `proj`); the full
holomorphic-function infrastructure underlying "`g` is holomorphic" (no Mathlib
complex-manifold holomorphy at this generality — the assumed `ComplexAnalyticStructure`
designation, like node 1's `RealAnalyticStructure`, with the same documented
identity-theorem/spanning-frame limitations); the group `Diff(M rel ∂M)` and its
complexified Lie algebra (node 5).

CONSTRAINTS: no `axiom` keyword, no concrete instance (all parametric over the assumed
geometry / extending `IsRealAnalytic`), no `sorry` — assumed properties are FIELDS;
`injective_of_totallyReal`, `tangentMap_injective`, `Isotopy.move_injective`,
`CurveSubmanifold.Mf_injective` are real proofs (axiom-clean).

Blueprint: this is infrastructure for `prop:invariance-principle` / `thm:unitary-gh` in
`blueprint/src/section5.tex` (no label of its own).
-/

import KontsevichSegal.WickRotation.LorentzianCategory
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace WickRotation

/- Register node 1's (inherited) complex-structure field as a global instance, so
`ComplexManifoldStructure.ComplexTangent (Complexification o)` resolves outside node 1's
class body. ADDITIVE: node 1's file is unchanged. -/
attribute [instance] IsRealAnalytic.complexStructure

/-! ## Totally-real ⟹ injective differential (a reusable proof from node 1's hook)

The single shared consequence of node 1's `totallyReal` shape: if the complexified
differential `(v,w) ↦ φ v + i·φ w` is bijective, the real differential `φ` is injective.
Applied below to node 1's `tangentMap`, and to the isotopy / `M_f` embeddings. -/

/-- If the complexification `(v, w) ↦ φ v + i · φ w` of a real-linear map `φ : V →ₗ[ℝ] W`
into a complex vector space `W` is bijective (the totally-real condition of node 1),
then `φ` itself is injective. -/
theorem injective_of_totallyReal {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [Module ℂ W] (φ : V →ₗ[ℝ] W)
    (h : Function.Bijective (fun vw : V × V => φ vw.1 + Complex.I • φ vw.2)) :
    Function.Injective φ := by
  intro v v' hvv
  have key : (fun vw : V × V => φ vw.1 + Complex.I • φ vw.2) (v, 0)
           = (fun vw : V × V => φ vw.1 + Complex.I • φ vw.2) (v', 0) := by
    change φ v + Complex.I • φ 0 = φ v' + Complex.I • φ 0
    rw [hvv]
  exact congrArg Prod.fst (h.injective key)

/-- **Node 1's totally-real embedding has an injective differential.** PROVED from
`IsRealAnalytic.totallyReal` via `injective_of_totallyReal`. -/
theorem tangentMap_injective [g : LorentzianCobordismGeometry] [IsRealAnalytic]
    (o : g.Obj) (x : g.Ambient o) :
    Function.Injective (IsRealAnalytic.tangentMap o x) :=
  injective_of_totallyReal _ (IsRealAnalytic.totallyReal o x)

/-! ## Assumed holomorphic-function structure on a complex manifold

The complex analogue of node 1's `RealAnalyticStructure`, used to state that the
holomorphic symmetric form `g` is holomorphic. Assumed designation, not constructed;
the same documented limitations as node 1's real-analytic structure apply (the full
identity-theorem characterization and a spanning frame of holomorphic vector fields
need a complex atlas not available at this generality). -/

/-- **Assumed (holomorphic-function structure, KS Section 5).** A designation of which
functions `N → ℂ` and which sections of the complex tangent bundle are HOLOMORPHIC, with
the holomorphic functions forming a ℂ-subalgebra that is PROPER (`not_all_holomorphic`).
The complex analogue of node 1's `RealAnalyticStructure`.

The subalgebra axioms alone are satisfied by the degenerate `IsHolomorphicFun := fun _ =>
True` ("everything holomorphic"); `not_all_holomorphic` rules that out. KNOWN LIMITATION
(as in node 1): this excludes only the fully degenerate designation; the full
holomorphy characterization (identity theorem / local power series) and a spanning frame
of holomorphic vector fields (so `holForm_holomorphic` bites on all of `g`) need a
complex atlas not in Mathlib at this generality, and are deferred. Assumed
infrastructure; not constructed. -/
class ComplexAnalyticStructure (N : Type*) [ComplexManifoldStructure N] where
  /-- The assumed designation of holomorphic ℂ-valued functions on `N`. -/
  IsHolomorphicFun : (N → ℂ) → Prop
  /-- The assumed designation of holomorphic vector fields (sections of `TN`). -/
  IsHolomorphicVF : (∀ y : N, ComplexManifoldStructure.ComplexTangent y) → Prop
  /-- Constants are holomorphic. -/
  holomorphic_const : ∀ c : ℂ, IsHolomorphicFun (fun _ => c)
  /-- Holomorphic functions are closed under addition. -/
  holomorphic_add : ∀ f₁ f₂, IsHolomorphicFun f₁ → IsHolomorphicFun f₂ →
    IsHolomorphicFun (f₁ + f₂)
  /-- Holomorphic functions are closed under multiplication. -/
  holomorphic_mul : ∀ f₁ f₂, IsHolomorphicFun f₁ → IsHolomorphicFun f₂ →
    IsHolomorphicFun (f₁ * f₂)
  /-- A PROPER subalgebra: some function is NOT holomorphic. Rules out the degenerate
  `IsHolomorphicFun := fun _ => True`. -/
  not_all_holomorphic : ∃ f : N → ℂ, ¬ IsHolomorphicFun f

/-! ## The holomorphic symmetric form `g` on `TM_ℂ`, extending node 1's `IsRealAnalytic`

`HolomorphicComplexification` EXTENDS node 1's `IsRealAnalytic`, adding the holomorphic
symmetric form `g` on `TM_ℂ` and the allowable complex metric it INDUCES on `M`. -/

/-- **Assumed (KS Principle 5.1 infrastructure; extends node 1).** A real-analytic
Lorentzian geometry whose complexification `M_ℂ` carries the holomorphic symmetric form
`g` on `TM_ℂ` from which `M`'s allowable complex metric is induced (Principle 5.1's
hypothesis). EXTENDS `IsRealAnalytic`, reusing its `Complexification` / `complexStructure`
/ `realEmbed` / `tangentMap` / `pushforward` / `totallyReal` / `complexDim_eq`; node 1 is
not revised.

* `holForm o y` — the holomorphic symmetric ℂ-bilinear form `g` on `TM_ℂ` at `y`
  (`holForm_symm` makes it symmetric).
* `holForm_holomorphic` — `g` is holomorphic (pairs holomorphic vector fields to
  holomorphic functions), referencing the assumed `complexAnalytic` designation. The
  complex analogue of node 1's `metric_analytic`; the full holomorphy infrastructure is
  deferred (see `ComplexAnalyticStructure`).
* `inducedMetric o x` — `M`'s allowable complex metric at `x`, an
  `AllowableComplexMetric` (hence allowable by type).
* `inducedMetric_eq` — **THE TIE (induced-metric, the most important float-free check
  here).** `M`'s metric is the RESTRICTION of `g` along the totally-real embedding:
  `(inducedMetric o x).toForm v w = holForm o (realEmbed o x) (tangentMap o x v)
  (tangentMap o x w)`. So `M`'s metric is "induced from `g`", not a free metric. Because
  `inducedMetric` is typed `AllowableComplexMetric`, the `g`-restriction is forced
  allowable (Principle 5.1's "allowable complex metric induced from `g`"), and a zero /
  degenerate `g` is EXCLUDED (it would make the restriction degenerate, contradicting
  `AllowableComplexMetric.nondegenerate`).

Assumed infrastructure: no `axiom`, no instance, no `sorry`; not constructed. -/
class HolomorphicComplexification [g : LorentzianCobordismGeometry] extends IsRealAnalytic where
  /-- Each complexification carries an assumed holomorphic-function structure. -/
  complexAnalytic : ∀ o, ComplexAnalyticStructure (Complexification o)
  /-- The holomorphic symmetric form `g` on `TM_ℂ`: a ℂ-bilinear form on each complex
  tangent space. -/
  holForm : ∀ (o : g.Obj) (y : Complexification o),
    ComplexManifoldStructure.ComplexTangent y →ₗ[ℂ]
      ComplexManifoldStructure.ComplexTangent y →ₗ[ℂ] ℂ
  /-- `g` is symmetric. -/
  holForm_symm : ∀ (o : g.Obj) (y : Complexification o)
    (v w : ComplexManifoldStructure.ComplexTangent y), holForm o y v w = holForm o y w v
  /-- `g` is holomorphic: it pairs holomorphic vector fields to holomorphic functions
  (complex analogue of node 1's `metric_analytic`). -/
  holForm_holomorphic : ∀ (o : g.Obj)
    (V W : ∀ y : Complexification o, ComplexManifoldStructure.ComplexTangent y),
    (complexAnalytic o).IsHolomorphicVF V → (complexAnalytic o).IsHolomorphicVF W →
    (complexAnalytic o).IsHolomorphicFun (fun y => holForm o y (V y) (W y))
  /-- `M`'s allowable complex metric at each point (allowable by type). -/
  inducedMetric : ∀ (o : g.Obj) (x : g.Ambient o),
    AllowableComplexMetric (TangentStructure.Tangent x)
  /-- **THE INDUCED-METRIC TIE.** `M`'s metric is the restriction of `g` along the
  totally-real embedding (via node 1's `tangentMap`). Not float-free. -/
  inducedMetric_eq : ∀ (o : g.Obj) (x : g.Ambient o) (v w : TangentStructure.Tangent x),
    (inducedMetric o x).toForm v w
      = holForm o (realEmbed o x) (tangentMap o x v) (tangentMap o x w)

/-! ## The smooth isotopy of `M` inside `M_ℂ` (what Principle 5.1 quantifies over) -/

/-- **A smooth isotopy of `M` inside `M_ℂ` holding the ends fixed (KS Principle 5.1).**
The movement Principle 5.1 quantifies over: a family `move s : M → M_ℂ`, `s ∈ [0,1]`,
of embeddings, starting at node 1's `realEmbed` (`move_zero`, the TIE), holding the
ends `∂M` fixed (`ends_fixed`), with each `M_s` totally-real (`movesTotallyReal`) and
the restriction of `g` to `M_s` staying allowable (`allowable_preserved` — Principle
5.1's proviso).

Non-vacuity. Each `move s`'s differential is node 1's `pushforward o (move s)` (tied to
`move s`); a degenerate (constant / collapsing) movement has `pushforward = 0`
(`pushforward_const`), so its complexified differential is not bijective, FAILING
`movesTotallyReal`. `allowable_preserved` references the actual `AllowableComplexMetric`,
so a movement leaving the allowable class FAILS it. `ends_fixed` references the carried
`ends`; for a closed `M` (`ends = ∅`) it is vacuous, which is the correct behaviour
(no ends to fix), and for a cobordism `ends = ∂M` is nonempty so the constraint bites. -/
structure Isotopy [g : LorentzianCobordismGeometry] [HC : HolomorphicComplexification]
    (o : g.Obj) where
  /-- The movement `M_s : M → M_ℂ`, `s ∈ [0,1]` (carried on all of `ℝ`, the germ at
  `[0,1]`). -/
  move : ℝ → g.Ambient o → IsRealAnalytic.Complexification o
  /-- The isotopy starts at node 1's totally-real embedding (TIE). -/
  move_zero : move 0 = IsRealAnalytic.realEmbed o
  /-- The ends `∂M` held fixed throughout. -/
  ends : Set (g.Ambient o)
  /-- The ends are held fixed: `move s` agrees with `realEmbed` on `∂M` for all `s`. -/
  ends_fixed : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ ends, move s x = IsRealAnalytic.realEmbed o x
  /-- Each `M_s` is a totally-real embedding: the complexified differential of `move s`
  (node 1's `pushforward`, so tied to `move s`) is bijective. Excludes degenerate
  (constant) movements via `pushforward_const`. -/
  movesTotallyReal : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : g.Ambient o,
    Function.Bijective
      (fun vw : TangentStructure.Tangent x × TangentStructure.Tangent x =>
        IsRealAnalytic.pushforward o (move s) x vw.1
          + Complex.I • IsRealAnalytic.pushforward o (move s) x vw.2)
  /-- **Principle 5.1's proviso:** the restriction of `g` to `M_s` remains an allowable
  complex metric for all `s`. References the actual `AllowableComplexMetric`. -/
  allowable_preserved : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : g.Ambient o,
    ∃ G : AllowableComplexMetric (TangentStructure.Tangent x), ∀ v w,
      G.toForm v w = HC.holForm o (move s x)
        (IsRealAnalytic.pushforward o (move s) x v) (IsRealAnalytic.pushforward o (move s) x w)

/-- **Each stage of an isotopy has an injective differential.** PROVED from
`movesTotallyReal` via `injective_of_totallyReal`. -/
theorem Isotopy.move_injective [g : LorentzianCobordismGeometry]
    [HolomorphicComplexification] {o : g.Obj} (iso : Isotopy o) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : g.Ambient o) :
    Function.Injective (IsRealAnalytic.pushforward o (iso.move s) x) :=
  injective_of_totallyReal _ (iso.movesTotallyReal s hs x)

/-! ## The totally-real submanifold `M_f` over a curve (KSTeX line 707) -/

/-- **The totally-real submanifold `M_f` over a curve (KS Theorem 5.2 proof, line 707).**
Given the holomorphic fibre-bundle projection `τ = it : M_ℂ → U ⊂ ℂ` (`proj`, assumed;
its bundle structure and holomorphic trivialization are deferred holomorphic-bundle
infrastructure) and a smooth curve `f : [0,1] → U` with `f(0) = 0` and `Re f'(s) > 0`
(`f_zero`, `f_deriv_re_pos`, the KEY constraints), the totally-real submanifold `M_f`
of `M_ℂ` sitting over the curve (`Mf`, `Mf_over_curve`, `MfTotallyReal`).

Non-vacuity. `f_deriv_re_pos` uses Mathlib's `deriv`, so it forces `f` differentiable
with positive-real derivative (a curve with `Re f' ≤ 0` somewhere fails). `Mf`'s
differential is node 1's `pushforward o Mf` (tied); `MfTotallyReal` (the same totally-real
notion node 1 made non-vacuous) excludes degenerate `Mf` via `pushforward_const`.
`Mf_over_curve` ties `Mf` to `proj` and `f`. -/
structure CurveSubmanifold [g : LorentzianCobordismGeometry] [HolomorphicComplexification]
    (o : g.Obj) where
  /-- The holomorphic fibre-bundle projection `τ = it : M_ℂ → U ⊂ ℂ` (assumed; bundle
  structure + trivialization deferred). -/
  proj : IsRealAnalytic.Complexification o → ℂ
  /-- The curve `f : [0,1] → U` (carried on `ℝ`). -/
  f : ℝ → ℂ
  /-- `f(0) = 0`. -/
  f_zero : f 0 = 0
  /-- `Re f'(s) > 0` on `[0,1]` (forces `f` differentiable with positive-real
  derivative). -/
  f_deriv_re_pos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < (deriv f s).re
  /-- The embedding of `M_f` into `M_ℂ`. -/
  Mf : g.Ambient o → IsRealAnalytic.Complexification o
  /-- `M_f` sits over the curve: each point projects onto `f([0,1])`. -/
  Mf_over_curve : ∀ x : g.Ambient o, ∃ s ∈ Set.Icc (0 : ℝ) 1, proj (Mf x) = f s
  /-- `M_f` is totally-real: the complexified differential of `Mf` (node 1's
  `pushforward`, tied to `Mf`) is bijective — the same notion node 1 made non-vacuous. -/
  MfTotallyReal : ∀ x : g.Ambient o,
    Function.Bijective
      (fun vw : TangentStructure.Tangent x × TangentStructure.Tangent x =>
        IsRealAnalytic.pushforward o Mf x vw.1 + Complex.I • IsRealAnalytic.pushforward o Mf x vw.2)

/-- **`M_f`'s embedding has an injective differential.** PROVED from `MfTotallyReal` via
`injective_of_totallyReal` (the totally-real property reused from node 1). -/
theorem CurveSubmanifold.Mf_injective [g : LorentzianCobordismGeometry]
    [HolomorphicComplexification] {o : g.Obj} (cs : CurveSubmanifold o) (x : g.Ambient o) :
    Function.Injective (IsRealAnalytic.pushforward o cs.Mf x) :=
  injective_of_totallyReal _ (cs.MfTotallyReal x)

end WickRotation
