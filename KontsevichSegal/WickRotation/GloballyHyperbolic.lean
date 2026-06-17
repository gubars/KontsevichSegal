/- Global hyperbolicity and the open subcategory `C_d^gh ⊆ C_d^Lor`: the SECOND Lean
node of Section 5 of the Kontsevich-Segal paper (arXiv:2105.10161). Encodes blueprint
node `def:globally-hyperbolic`. Built on node 1 (`LorentzianCategory.lean`).

CONTENT vs INFRASTRUCTURE. The globally-hyperbolic PREDICATE and the gh subcategory
(`GhMor`, `ghConcat`, `ghGeometry`, `ghSemicategory`) are CONTENT, built on top of
assumed causal/light-cone INFRASTRUCTURE (the cobordism's manifold + metric + the
positive light-cone + the assumed gh-closure and openness), which Mathlib does not
provide (no Lorentzian causal theory) and which node 1 deferred (its `Mor` is opaque).

NON-VACUITY (the C1 / `IsRealAnalytic` discipline). `IsGloballyHyperbolic` is a REAL
constraint, not "∃ t : M → [0,1]" (which every cobordism satisfies via a constant). A
`TimeFunction` carries the time-function `toFun`, and `differential_eq` ties its covector
field to the assumed exterior derivative `d(toFun)` (`exteriorD`), so the GRADIENT
condition (`gradient_timelike`: the metric-dual of `d(toFun)` is in the future-cone) and
the Riemannian-fibres condition (`fibres_riemannian`: the metric is positive-definite on
`ker d(toFun)`) constrain the REAL differential of a global function, not a free covector
field.

Two genuinely different failures show it bites:
* DEGENERATE: a cobordism whose future-cone is empty somewhere (no future-timelike
  direction; not time-orientable) admits no time-function, since `gradient_timelike` is
  `∃ v ∈ ∅, …`, false. A constant `toFun` also fails: `d(const) = 0`
  (`exteriorD_const_zero`) forces the gradient to be `0`, not in the cone (cone vectors
  are timelike, hence nonzero, by `posCone_timelike` + nondegeneracy of `IsLorentzian`).
* SHARP (good cones, no global time-function): a geometry with NONEMPTY, well-behaved
  future-cones everywhere can still fail. If `Cob M` contains a closed future-timelike
  curve `γ` (with `γ'` in the cone everywhere), then for any `toFun` the derivative of
  `toFun ∘ γ` is `d(toFun)(γ') = g(∇t, γ')`, of one definite sign for the two
  future-timelike vectors `∇t` (the gradient) and `γ'`; so `toFun ∘ γ` would be strictly
  monotone along a CLOSED curve, impossible. No time-function exists, so gh FAILS even
  though the causal structure is perfectly good. Thus gh is STRICTLY STRONGER than "has a
  future-cone structure": it bites on the existence of a GLOBAL time-function, not merely
  on local causal structure. The `differential_eq` tie (the gradient is `d` of a global
  `toFun`) is exactly what makes this global obstruction bite; without it the covector
  field floats free of `toFun` and gh collapses toward nonempty-cones.

DEFERRED (documented, not faked): the CONSTRUCTION of the assumed exterior derivative
`exteriorD` (the de Rham `d`) and the smoothness of `toFun` — `exteriorD` is assumed (a
field), and `differential_eq` ties `differential` to `d(toFun)`, so the STATEMENT is
faithful while the operator is not built from Mathlib. Also deferred: the topology making
"open" precise (assumed `morTopology`); gh-closure-under-concatenation (assumed
`gh_concat`, needing the deferred gluing of time-functions); the `h_t + c²dt²`
normal-form decomposition (needs the level sets) — but the deformation to an allowable
complex metric is tied term-level to Section 2's `lorentzian_on_boundary`
(`cob_metric_deformable_to_allowable`).

Blueprint: `def:globally-hyperbolic` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.LorentzianCategory

namespace WickRotation

universe u v w

/-! ## Assumed light-cone / causal geometry on the cobordisms -/

/-- **Assumed (causal/light-cone geometry; KS Section 5).** The cobordism-level
geometry node 1 left opaque, plus the causal structure, cited by KS as known and not in
Mathlib:

* `Cob M` — the cobordism `M`'s underlying `d`-manifold (its points), with a
  finite-dimensional real tangent space at each point (`TangentStructure`);
* `cobMetric M` — the cobordism's Lorentzian metric (a `LorentzianField` on `Cob M`,
  anchored to Section 2's `IsLorentzian`, exactly as node 1's `metric` on objects);
* `posCone M x` — the positive (future-timelike) light-cone at each tangent space, the
  assumed time-orientation, with the faithful properties that it is a convex cone of
  timelike (negative-norm, hence nonzero) vectors.

This `class` records the assumed causal geometry; it is NOT constructed for any concrete
family of Lorentzian cobordisms. -/
class LightConeGeometry [g : LorentzianCobordismGeometry] where
  /-- The cobordism's underlying `d`-manifold (its points). -/
  Cob : ∀ {a b}, g.Mor a b → Type*
  [cobTangent : ∀ {a b} (M : g.Mor a b), TangentStructure (Cob M)]
  /-- The cobordism's Lorentzian metric. -/
  cobMetric : ∀ {a b} (M : g.Mor a b), LorentzianField (Cob M)
  /-- The positive (future-timelike) light-cone at each tangent space. -/
  posCone : ∀ {a b} (M : g.Mor a b) (x : Cob M), Set (TangentStructure.Tangent x)
  /-- Light-cone vectors are timelike (negative norm, KS's convention `‖ξ‖² < 0`); in
  particular they are nonzero. -/
  posCone_timelike : ∀ {a b} (M : g.Mor a b) (x : Cob M) (v : TangentStructure.Tangent x),
    v ∈ posCone M x → (cobMetric M x).1 v v < 0
  /-- The light-cone is closed under positive scaling. -/
  posCone_smul : ∀ {a b} (M : g.Mor a b) (x : Cob M) (c : ℝ)
    (v : TangentStructure.Tangent x), 0 < c → v ∈ posCone M x → c • v ∈ posCone M x
  /-- The light-cone is convex (future-timelike vectors add). -/
  posCone_add : ∀ {a b} (M : g.Mor a b) (x : Cob M) (v w : TangentStructure.Tangent x),
    v ∈ posCone M x → w ∈ posCone M x → v + w ∈ posCone M x
  /-- **Assumed exterior derivative `d` on the cobordism** (ITEM 1 tie). The differential
  of a real function on `Cob M`: `d : (Cob M → ℝ) → ∀ x, T_x M → ℝ`. Assumed (the smooth /
  de Rham `d` is deferred germ geometry, not built from Mathlib); it is what ties a
  time-function's covector field to its actual function. -/
  exteriorD : ∀ {a b} (M : g.Mor a b),
    (Cob M → ℝ) → ∀ x : Cob M, TangentStructure.Tangent x →ₗ[ℝ] ℝ
  /-- `d` is additive. -/
  exteriorD_add : ∀ {a b} (M : g.Mor a b) (f₁ f₂ : Cob M → ℝ) (x : Cob M),
    exteriorD M (f₁ + f₂) x = exteriorD M f₁ x + exteriorD M f₂ x
  /-- `d` of a constant function is zero: a constant time-function has zero gradient,
  which cannot lie in the (timelike, hence nonzero) future-cone, so it fails
  `gradient_timelike`. -/
  exteriorD_const_zero : ∀ {a b} (M : g.Mor a b) (c : ℝ) (x : Cob M),
    exteriorD M (fun _ => c) x = 0

attribute [instance] LightConeGeometry.cobTangent

/-! ## Time-functions -/

/-- **A time-function on a Lorentzian cobordism** (KS Section 5, the compact-case
global-hyperbolicity datum). A smooth `t : M → [0,1]` whose gradient (w.r.t. the
Lorentzian metric) lies everywhere in the positive light-cone and which is a fibration
with Riemannian fibres. The covector field `differential` is TIED to `toFun` by
`differential_eq` (it equals the assumed `d(toFun)`, `LightConeGeometry.exteriorD`), so
`gradient_timelike` and `fibres_riemannian` constrain the real differential of the global
function `toFun`, not a free covector field. The gradient is the metric-dual of
`d(toFun)`; `gradient_timelike` is the KEY constraint. -/
structure TimeFunction [g : LorentzianCobordismGeometry] [lc : LightConeGeometry]
    {a b} (M : g.Mor a b) where
  /-- The time-function `t : M → ℝ`. -/
  toFun : LightConeGeometry.Cob M → ℝ
  /-- Its range lies in `[0,1]`. -/
  range_mem : ∀ x : LightConeGeometry.Cob M, toFun x ∈ Set.Icc (0 : ℝ) 1
  /-- The differential (cotangent) `dt` at each point. -/
  differential : ∀ x : LightConeGeometry.Cob M, TangentStructure.Tangent x →ₗ[ℝ] ℝ
  /-- ITEM 1 TIE: the covector field IS the differential of `toFun`, via the assumed
  `exteriorD`. This pins `differential` to `toFun`, so `gradient_timelike` and
  `fibres_riemannian` constrain `toFun` through its real differential `d(toFun)`, not a
  free covector field. -/
  differential_eq : ∀ x : LightConeGeometry.Cob M,
    differential x = LightConeGeometry.exteriorD M toFun x
  /-- KEY PROPERTY: the gradient (the metric-dual of `dt`) lies everywhere in the
  positive light-cone. -/
  gradient_timelike : ∀ x : LightConeGeometry.Cob M, ∃ v ∈ LightConeGeometry.posCone M x,
    ∀ w : TangentStructure.Tangent x, (LightConeGeometry.cobMetric M x).1 v w = differential x w
  /-- The fibres (level sets of `t`) are Riemannian: the metric is positive-definite on
  `ker dt`, the spacelike tangent hyperplane. -/
  fibres_riemannian : ∀ x : LightConeGeometry.Cob M, ∀ w : TangentStructure.Tangent x,
    differential x w = 0 → w ≠ 0 → 0 < (LightConeGeometry.cobMetric M x).1 w w

/-! ## The globally-hyperbolic predicate (content) -/

/-- **Global hyperbolicity** (KS Section 5, the compact-case definition KS adopt). A
Lorentzian cobordism is globally hyperbolic when it admits a time-function: a smooth
`t : M → [0,1]` with gradient everywhere in the positive light-cone (a fibration with
Riemannian fibres). NON-VACUOUS (see the module comment): a constant candidate fails
(`no_constant_timeFunction`, Lean-checked), and — the sharper failure — a geometry with
good nonempty cones but a closed timelike curve admits no global time-function. -/
def IsGloballyHyperbolic [g : LorentzianCobordismGeometry] [lc : LightConeGeometry]
    {a b} (M : g.Mor a b) : Prop :=
  Nonempty (TimeFunction M)

/-- **Non-vacuity witness (Lean-checked): a constant time-function is impossible.** If
`toFun` is constant then `d(toFun) = 0` (`exteriorD_const_zero` via the `differential_eq`
tie), so the future-cone gradient `v` of `gradient_timelike` would satisfy
`g(v, v) = differential v = 0`, contradicting `g(v, v) < 0` (`posCone_timelike`). So
`IsGloballyHyperbolic` genuinely constrains: the trivial constant candidate fails. (The
sharper good-cones-but-no-global-time-function failure, where a closed timelike curve
forces `toFun ∘ γ` to be strictly monotone along a closed curve, is argued in the module
comment; it needs the `differential_eq` tie to bite.) -/
theorem no_constant_timeFunction [g : LorentzianCobordismGeometry] [lc : LightConeGeometry]
    {a b} (M : g.Mor a b) (x₀ : LightConeGeometry.Cob M) (c : ℝ)
    (t : TimeFunction M) (hconst : t.toFun = fun _ => c) : False := by
  obtain ⟨v, hv, hvw⟩ := t.gradient_timelike x₀
  have hlt := LightConeGeometry.posCone_timelike M x₀ v hv
  have h0 : (LightConeGeometry.cobMetric M x₀).1 v v = 0 := by
    rw [hvw v, t.differential_eq x₀, hconst, LightConeGeometry.exteriorD_const_zero,
      LinearMap.zero_apply]
  linarith

/-! ## The open subcategory `C_d^gh` (content) -/

/-- The globally hyperbolic morphisms `a ⤳ b`: the predicate-restricted Hom. -/
def GhMor [g : LorentzianCobordismGeometry] [lc : LightConeGeometry] (a b : g.Obj) :
    Type _ :=
  { M : g.Mor a b // IsGloballyHyperbolic M }

/-- **Assumed (KS Section 5).** The data making the gh cobordisms an OPEN subcategory:
global hyperbolicity is closed under concatenation (so `GhMor` is closed under gluing,
hence a sub-semicategory), and it is an open condition with respect to an assumed
topology on cobordisms (the topology on the space of Lorentzian metrics; deferred
infrastructure). The closure needs the deferred gluing of time-functions, so it is
assumed here rather than proved. -/
class GhCategory [g : LorentzianCobordismGeometry] [lc : LightConeGeometry] where
  /-- Global hyperbolicity is closed under concatenation. -/
  gh_concat : ∀ {a b c} (f : g.Mor a b) (h : g.Mor b c),
    IsGloballyHyperbolic f → IsGloballyHyperbolic h → IsGloballyHyperbolic (g.concat f h)
  /-- An assumed topology on each morphism space (the topology on the space of
  Lorentzian metrics; deferred). -/
  [morTopology : ∀ a b, TopologicalSpace (g.Mor a b)]
  /-- Global hyperbolicity is an OPEN condition: `C_d^gh` is an open subcategory of
  `C_d^Lor`. -/
  gh_open : ∀ a b, IsOpen {M : g.Mor a b | IsGloballyHyperbolic M}

attribute [instance] GhCategory.morTopology

/-- Concatenation of gh cobordisms, using the assumed gh-closure. -/
def ghConcat [g : LorentzianCobordismGeometry] [lc : LightConeGeometry] [GhCategory]
    {a b c} (f : GhMor a b) (h : GhMor b c) : GhMor a c :=
  ⟨g.concat f.1 h.1, GhCategory.gh_concat f.1 h.1 f.2 h.2⟩

/-- Concatenation of gh cobordisms is associative (discharged from `g.concat_assoc`; the
gh-proofs are `Prop`, so `Subtype.ext` closes it — no `sorry`). -/
theorem ghConcat_assoc [g : LorentzianCobordismGeometry] [lc : LightConeGeometry]
    [GhCategory] {a b c d} (f : GhMor a b) (h : GhMor b c) (k : GhMor c d) :
    ghConcat (ghConcat f h) k = ghConcat f (ghConcat h k) :=
  Subtype.ext (g.concat_assoc f.1 h.1 k.1)

/-- **The globally hyperbolic subcategory `C_d^gh` as a Lorentzian cobordism geometry**
(KS Section 5, constructed). Same objects and germ geometry as `C_d^Lor`, with the
morphisms restricted to the gh cobordisms (`GhMor`) under `ghConcat`. Parametric over
the assumed geometry; exhibits no concrete cobordism category. -/
def ghGeometry [g : LorentzianCobordismGeometry] [lc : LightConeGeometry] [GhCategory] :
    LorentzianCobordismGeometry where
  Obj := g.Obj
  Ambient := g.Ambient
  ambientTangent := g.ambientTangent
  metric := g.metric
  Mor := GhMor
  concat := ghConcat
  concat_assoc := ghConcat_assoc

/-- The gh sub-semicategory `C_d^gh`: the `Semicategory` of `ghGeometry`, via node 1's
parametric `instSemicategory` (reused, not re-declared). A `def`, not an `instance`, to
avoid clashing with `C_d^Lor`'s own `Semicategory`. -/
def ghSemicategory [g : LorentzianCobordismGeometry] [lc : LightConeGeometry] [GhCategory] :
    Cobordism.Semicategory g.Obj :=
  @instSemicategory ghGeometry

/-! ## The real-analytic version `C_d^{gh,ω}` -/

/-- **The real-analytic globally hyperbolic condition `C_d^{gh,ω}`** (KS Section 5). A
gh cobordism in a real-analytic geometry: `IsGloballyHyperbolic` together with node 1's
`IsRealAnalytic` (visible as a hypothesis, gating the ω version — the same way Section 3
gates `ConjugateDualIdentification` on `IsReal`). -/
def IsGloballyHyperbolicOmega [g : LorentzianCobordismGeometry] [lc : LightConeGeometry]
    [IsRealAnalytic] {a b} (M : g.Mor a b) : Prop :=
  IsGloballyHyperbolic M

/-! ## The `h_t + c²dt²` normal form and the deformation to allowable -/

/-- **Lorentzian → complex bridge (KS Section 5; Section 2 tie).** For a gh cobordism,
in the time-function normal form the metric is `h_t + c² dt²` with `c` purely imaginary,
so `c² < 0` is the single timelike eigenvalue, sitting on the negative real axis.
Deforming `c` into the right half-plane moves that eigenvalue off the negative real axis
into the complex plane, yielding an ALLOWABLE complex metric (Section 2): each tangent
metric of the cobordism, being `IsLorentzian`, is an entry-wise limit of
`AllowableComplexMetric`s but is not itself allowable.

This is a genuine term-level reuse of Section 2's `lorentzian_on_boundary` for the
cobordism's metric `(cobMetric M x)`. The `h_t + c²dt²` normal-form decomposition itself
needs the chosen time-function's level sets and is deferred germ geometry; the
allowability of the deformation is exactly the Section 2 boundary perturbation. -/
theorem cob_metric_deformable_to_allowable [g : LorentzianCobordismGeometry]
    [lc : LightConeGeometry] {a b} (M : g.Mor a b) (x : LightConeGeometry.Cob M) :
    (∃ bs : Module.Basis (Fin (Module.finrank ℝ (TangentStructure.Tangent x))) ℝ
        (TangentStructure.Tangent x),
      ∀ ε : ℝ, 0 < ε →
        ∃ G : AllowableComplexMetric (TangentStructure.Tangent x),
          ∀ i j, ‖G.toForm (bs i) (bs j)
            - ↑((LightConeGeometry.cobMetric M x).1 (bs i) (bs j))‖ < ε) ∧
    (∀ G : AllowableComplexMetric (TangentStructure.Tangent x),
      ∃ v, G.toForm v v ≠ ↑((LightConeGeometry.cobMetric M x).1 v v)) :=
  lorentzian_on_boundary (LightConeGeometry.cobMetric M x).1 (LightConeGeometry.cobMetric M x).2

end WickRotation
