/- Observables at a point `𝒪_x` (the DEFINITION only): the EIGHTH Lean node of Section 5 of
the Kontsevich-Segal paper (arXiv:2105.10161). Encodes blueprint node `def:observables`, but
ONLY the definition of the observable space `𝒪_x` for a Lorentzian `M`. The ACTION of an
observable (`ψ : E_{Σ_0} → E_{Σ_1}`) and the ordering-independent multilinear map
`𝒪_{x_1} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_Σ; Ê_Σ)` are node 9 (`prop:observable-action`); spacelike
commutativity is node 10 (`prop:spacelike-commutativity`).

KS FIELD OPERATORS, the `𝒪_x` definition (KSTeX 737-739). "In Section 3 we associated a space
`𝒪_x` to a germ at `x` of a complex metric on a manifold containing `x`: it is the fibre of a
bundle on the space `Met_ℂ(x̂)` of such germs. If we embed a Lorentzian `M` in a complexification
`M_ℂ` there will be a holomorphic exponential map from a neighbourhood of `0` in the complexified
tangent space `T_x^ℂ = T_x M ⊗ ℂ` to `M_ℂ`. Inside `T_x^ℂ` we can consider the `d`-dimensional
real vector subspaces `V` on which the metric induced from the complex bilinear form of `T_x^ℂ`
is allowable. We saw in (2.6) that these `V` form a contractible open subset `𝒰` of the real
Grassmannian `Gr_d(T_x^ℂ)`. Exponentiating `V` will give us a germ of a `d`-manifold with a
complex metric, and hence a map `𝒰 → Met_ℂ(x̂)`. Pulling back the bundle of observables by this
map gives us a bundle on `𝒰`, which, using the principle (5.1) as we did in (5.3), we see to be
trivial. Identifying its fibres gives us our definition of `𝒪_x` for Lorentzian `M`."

THE ENCODING (scope (a): STATE the definition; the trivialization proof is additive prose).

* `IsAllowableSubspace o x V` / `AllowableSubspaces o x` — `𝒰 ⊂ Gr_d(T_x^ℂ)` (KS (2.6) = Prop 2.6,
  blueprint `prop:real-subspaces`). `V` is a real subspace `Submodule ℝ T_x^ℂ` of the complexified
  tangent `T_x^ℂ = ComplexTangent (realEmbed o x)`; it lies in `𝒰` when it is `d`-dimensional
  (`d = dim_ℝ T_x M`) AND its INDUCED METRIC is allowable: there is an `AllowableComplexMetric V`
  whose form is the RESTRICTION of the holomorphic complex bilinear form `holForm` (node 4) to `V`.
  This is the SAME induced-metric tie as node 4's `inducedMetric_eq` / `Isotopy.allowable_preserved`
  (not float-free): the allowable metric is the restriction of `holForm`, referencing the actual
  Section-2 `AllowableComplexMetric`. So a `V` whose restricted form is NOT allowable is excluded
  from `𝒰` (it BITES). Contractibility and openness of `𝒰` are KS Prop 2.6 (`prop:real-subspaces`,
  a DEFERRED Section 2 node with no Lean declaration); they need a topology on the real Grassmannian
  not in Mathlib at this generality, so they are not stated as fields here (no invented Section-2
  lemma) and are recorded as prose.
* `Observables o x` — the observable bundle on `Met_ℂ(x̂)`, the map `𝒰 → Met_ℂ(x̂)`, and the
  trivial pullback. `Met_ℂ(x̂)` REUSES Section 3's `Met_ℂ` (`def:metc-complex-manifold`): its base
  is `mc.carrier` for `mc : MetCManifold (Ambient o)` (the germ-localization `Met_ℂ(Ambient o) →
  Met_ℂ(x̂)` is deferred Section-3 infrastructure; the observable fibre depends only on the germ at
  `x`, so the bundle factors through it).
  - `Obs : Met_ℂ(x̂) → Type*` (with `NuclearFrechetFibres`) — the OBSERVABLE BUNDLE. Section 3
    associates `𝒪_x` to a complex-metric germ as the fibre of this bundle; Section 3 does NOT yet
    have an observable-bundle Lean declaration, so it is carried as ASSUMED infrastructure (like
    node 7's `EHatPath` carried the `{Ê_f}` bundle). Its fibres are nuclear Fréchet (the inverse
    limit of the disc-boundary spaces `E_{∂D}`; that inverse-limit construction inherits Section 3's
    deferred TVS-limit).
  - `expMap : 𝒰 → Met_ℂ(x̂)` — exponentiate `V`: the holomorphic exp of `V` is a germ of a
    `d`-manifold with a complex metric, a point of `Met_ℂ(x̂)`. The holomorphic-exp CONSTRUCTION is
    deferred (as node 4 deferred the bundle `proj` and node 5 the `realize` correspondence); the
    codomain is anchored to the actual Section-3 `Met_ℂ` (`mc.carrier`).
  - `triv`/`triv_symm`/`triv_coh` — TRIVIALITY of the pullback bundle `V ↦ Obs (expMap V)` on `𝒰`:
    a canonical `≃L[ℂ]` iso of any two fibres, mutually inverse, coherent (the cocycle). By
    Principle 5.1 (node 5, `IsInvariant`) as in Remark 5.3 (node 7), since `𝒰` is contractible; the
    interleaving/coherence proof is recorded as prose (scope (a)), not a `sorry`'d theorem. This is
    EXACTLY node 7's path-independence pattern (`pathIso`/`pathIso_symm`/`pathIso_coh`).
  - `base : 𝒰` — a basepoint of `𝒰` (the totally-real subspace `range (tangentMap o x)` is the
    canonical one; its membership follows from node 4's allowable `inducedMetric`, the
    `AllowableComplexMetric`-transport along `tangentMap` being deferred-additive). `base` witnesses
    `𝒰` nonempty (Prop 2.6).
* `Observables.Ox` — `𝒪_x` for Lorentzian `M`: the COMMON FIBRE of the trivial pullback bundle,
  namely the fibre `Obs (expMap base)` over the basepoint, which `triv` canonically identifies with
  every other fibre. "Identifying its fibres gives us our definition of `𝒪_x`." It inherits the
  nuclear-Fréchet structure of the bundle fibres.

VACUITY / FAITHFULNESS SELF-CHECK (per-predicate).
* `IsAllowableSubspace` BITES: the allowable condition references the actual `holForm` (node 4) and
  the actual `AllowableComplexMetric` (Section 2). A `V` whose restricted form admits no
  `AllowableComplexMetric` witness — e.g. a real subspace meeting the Lorentzian/forbidden locus, on
  which the angle condition fails — is EXCLUDED from `𝒰`. The dimension clause `dim_ℝ V = d` excludes
  subspaces of the wrong dimension (`𝒰 ⊂ Gr_d`). Most degenerate satisfier: there is none that
  hollows it; the predicate is a genuine constraint on `V`.
* TRIVIAL-SATISFIABILITY NUANCE (node 7). `triv` is satisfied by canonical-identity isos when the
  pulled-back fibres genuinely coincide — and that IS the content (KS: the bundle on `𝒰` "we see to
  be trivial"). So the trivial bundle is the CORRECT model, not a vacuity, exactly as node 7's
  constant `Ê`-bundle. It still BITES: a pullback with NON-isomorphic fibres (a non-trivializable
  bundle on `𝒰`) cannot supply `triv` (the all-pairs `≃L`); and the fibres are the ACTUAL
  `Obs (expMap V)`, so `𝒪_x = Obs (expMap base)` is genuinely the bundle's fibre (mis-anchored
  pullbacks excluded). Equate-vs-distinguish (node 5 lesson): the content is "the fibres are
  canonically isomorphic", so the isos are EQUATE-carried (`≃L` + `symm` + cocycle); NO
  injectivity/distinctness field is added (it would CONTRADICT "trivial bundle / same fibre").
* FORCED DEFERRAL of the fibre-IDENTITY anchor (verified forced, 2026-06-18). KS build `𝒪_x` from
  Section 3 as the inverse limit `𝒪_x = lim← E_{∂D}` of the field-theory spaces of the boundary
  spheres `∂D` of small discs `D` around `x` (blueprint `def:observables`). A faithful anchor would
  tie `Obs m` to that limit; it is forced-deferred for two verified reasons. (a) Section 3 has NO
  observable-bundle / `O_x` declaration: `FieldTheory` carries only the per-slice `E` / `Ê` / `Ě` /
  `Z`, with no observable and no disc / sphere / point-germ geometry. (b) The anchor needs the
  sphere-`∂D`-around-`x` objects (not formalized — the cobordism objects are abstract germs along
  `(d-1)`-manifolds, with no point-disc constructor) AND the inverse-limit TVS construction (deferred
  in Section 3, the same gap that leaves `Ê` / `Ě` unbuilt). Node 7 could anchor `EHatPath` to
  `T.EHat` only because `EHat` is a FIELD of `FieldTheory`; there is no observable field to play that
  role. The action `𝒪_x → Hom(Ě_Σ; Ê_Σ)` is node-9 content and a MAP, not an identification, so
  `Hom(Ě_Σ; Ê_Σ)` is not a node-8 anchor either. The faithful PARTIAL anchor that DOES exist IS
  carried: `[NuclearFrechetFibres Obs]` pins the fibres to nuclear Fréchet — the correct structural
  type of `𝒪_x` (an inverse limit of the nuclear Fréchet spaces `E_{∂D}`) — so `Obs` is NOT fully
  free; only the SPECIFIC fibre is unpinned, and building it (the Section-3 observable bundle: disc
  geometry + inverse limit) is out of scope for node 8, whose deliverable is the Wick-rotation
  definition of `𝒪_x` from the already-given complex observable bundle. The STRUCTURAL content (the
  allowable `𝒰`, the trivial pullback, `𝒪_x` as the identified fibre) bites regardless of the fibre
  identity.

FLOAT-FREE TIES. The induced-metric clause ties `𝒰`-membership to `holForm` and the actual
`AllowableComplexMetric` (the main content tie, as node 4's `inducedMetric_eq`); `triv` is over the
actual `Obs ∘ expMap`; `Ox` is the actual `Obs (expMap base)`; `expMap`'s codomain is the actual
Section-3 `Met_ℂ` (`mc.carrier`).

DEFERRED (documented, not faked): the holomorphic exponential CONSTRUCTION underlying `expMap` and
the germ-localization `Met_ℂ(Ambient o) → Met_ℂ(x̂)` (deferred holomorphic / Met_ℂ infrastructure);
contractibility and openness of `𝒰` (Prop 2.6 `prop:real-subspaces`, no Lean decl; no topology on
the real Grassmannian in Mathlib); the trivialization PROOF (Principle 5.1, prose); the Section-3
observable bundle's non-triviality anchor (above); `base`'s membership proof
(`AllowableComplexMetric`-transport along `tangentMap`).

CONSTRAINTS: no `axiom` keyword, no concrete instance (parametric over the assumed geometry; the one
`instance` provided is the routine fact that a complex tangent space is finite-dimensional over `ℝ`),
no `sorry` (the definition is STATED as a `structure`/`def`; the trivialization proof is prose, never
a `sorry`'d theorem). Reuses node 4's `HolomorphicComplexification` (`holForm`/`realEmbed`), node 5's
`IsInvariant` (Principle 5.1, prose), node 7's trivialization PATTERN, Section 2's
`AllowableComplexMetric`, and Section 3's `MetCManifold` / `NuclearFrechetFibres`.

Blueprint: `def:observables` in `blueprint/src/section5.tex` (its `\lean` annotation lands with the
forthcoming content-node annotation batch).
-/

import KontsevichSegal.WickRotation.InvariancePrinciple
import KontsevichSegal.FieldTheory.MetCManifold
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace WickRotation

open Cobordism

/-! ## The complexified tangent space `T_x^ℂ` -/

/-- A complex tangent space is finite-dimensional over `ℝ` (from finite-dimensionality over `ℂ`
through the scalar tower `ℝ → ℂ → ComplexTangent y`). Routine derived instance; needed so that real
subspaces of `T_x^ℂ` carry `AllowableComplexMetric`. -/
instance complexTangent_finiteDimensional_real {N : Type*} [ComplexManifoldStructure N] (y : N) :
    FiniteDimensional ℝ (ComplexManifoldStructure.ComplexTangent y) :=
  FiniteDimensional.trans ℝ ℂ (ComplexManifoldStructure.ComplexTangent y)

/-- The complexified tangent space `T_x^ℂ = T_x M ⊗ ℂ` at the embedded point `realEmbed o x ∈ M_ℂ`
(node 1/4's `ComplexTangent` at the image of `x`). -/
abbrev ComplexTangentAt [gl : LorentzianCobordismGeometry] [HolomorphicComplexification]
    (o : gl.Obj) (x : gl.Ambient o) : Type _ :=
  ComplexManifoldStructure.ComplexTangent (IsRealAnalytic.realEmbed o x)

/-! ## The contractible set `𝒰 ⊂ Gr_d(T_x^ℂ)` of allowable real subspaces (KS Prop 2.6) -/

/-- **A `d`-dimensional real subspace of `T_x^ℂ` with allowable induced metric (KS (2.6) = Prop 2.6,
blueprint `prop:real-subspaces`).** `V ⊂ T_x^ℂ` lies in `𝒰` when it is `d`-dimensional
(`d = dim_ℝ T_x M`) and the metric INDUCED on `V` from the complex bilinear form `holForm` (node 4)
is allowable: there is an `AllowableComplexMetric V` whose form is the restriction of `holForm` to
`V`.

This is the induced-metric tie of node 4 (`inducedMetric_eq` / `allowable_preserved`): the
allowable metric is the RESTRICTION of `holForm`, referencing the actual Section-2
`AllowableComplexMetric`, so the condition is not float-free. It BITES: a `V` whose restricted form
admits no `AllowableComplexMetric` (the angle condition fails, e.g. on the Lorentzian/forbidden
locus) is excluded, and a subspace of the wrong dimension is excluded by the first clause. -/
def IsAllowableSubspace [gl : LorentzianCobordismGeometry] [HC : HolomorphicComplexification]
    (o : gl.Obj) (x : gl.Ambient o) (V : Submodule ℝ (ComplexTangentAt o x)) : Prop :=
  Module.finrank ℝ V = Module.finrank ℝ (TangentStructure.Tangent x) ∧
    ∃ G : AllowableComplexMetric V,
      ∀ v w : V, G.toForm v w = HC.holForm o (IsRealAnalytic.realEmbed o x) (↑v) (↑w)

/-- **The contractible open set `𝒰 ⊂ Gr_d(T_x^ℂ)` (KS Prop 2.6).** The `d`-dimensional real
subspaces of `T_x^ℂ` whose induced metric is allowable. Contractibility and openness are KS
Proposition 2.6 (`prop:real-subspaces`), a deferred Section 2 result with no Lean declaration (no
topology on the real Grassmannian in Mathlib at this generality), recorded as prose rather than
stated as a field. -/
def AllowableSubspaces [gl : LorentzianCobordismGeometry] [HolomorphicComplexification]
    (o : gl.Obj) (x : gl.Ambient o) : Type _ :=
  {V : Submodule ℝ (ComplexTangentAt o x) // IsAllowableSubspace o x V}

/-! ## The observable bundle on `Met_ℂ(x̂)`, its trivial pullback to `𝒰`, and `𝒪_x` -/

/-- **The observable bundle, its pullback to `𝒰`, and `𝒪_x` for Lorentzian `M` (KS Section 5,
blueprint `def:observables`).** For a real-analytic Lorentzian germ `o` and `x ∈ Ambient o`, the
observable bundle on `Met_ℂ(x̂)`, the exponential map `𝒰 → Met_ℂ(x̂)`, and the trivial pullback
bundle on `𝒰` whose common fibre is `𝒪_x`.

`Met_ℂ(x̂)` reuses Section 3's `Met_ℂ` (`def:metc-complex-manifold`): its base is `mc.carrier` for
the ambient `MetCManifold` (the germ-localization is deferred; the observable fibre depends only on
the germ at `x`). The observable bundle `Obs` is carried as assumed Section-3 infrastructure
(Section 3 has no observable-bundle declaration yet); its fibres are nuclear Fréchet (the inverse
limit of the disc-boundary spaces). The trivialization `triv` is node 7's path-independence pattern:
canonical
`≃L[ℂ]` isos, mutually inverse and coherent, holding by Principle 5.1 (node 5) since `𝒰`
is contractible (proof prose, scope (a)). `base` is a basepoint of `𝒰` (the totally-real
subspace), witnessing `𝒰` nonempty. -/
structure Observables [gl : LorentzianCobordismGeometry] [HolomorphicComplexification]
    (o : gl.Obj) [mc : MetCManifold (gl.Ambient o)] (x : gl.Ambient o) where
  /-- The observable bundle on `Met_ℂ(x̂)`: the observable space at each complex-metric germ, the
  fibre of a bundle on `Met_ℂ(x̂) = mc.carrier`. Assumed Section-3 infrastructure (no Section-3
  observable-bundle declaration yet); its fibres are nuclear Fréchet (inverse limit of `E_{∂D}`). -/
  Obs : mc.carrier → Type*
  [obsFibres : NuclearFrechetFibres Obs]
  /-- The exponential map `𝒰 → Met_ℂ(x̂)`: the holomorphic exp of `V` is a germ of a `d`-manifold
  with a complex metric. Holomorphic-exp construction deferred; codomain anchored to Section-3
  `Met_ℂ`. -/
  expMap : AllowableSubspaces o x → mc.carrier
  /-- A basepoint of `𝒰` (the totally-real subspace `range (tangentMap o x)`), witnessing `𝒰`
  nonempty (Prop 2.6); its membership follows from node 4's allowable `inducedMetric`
  (`AllowableComplexMetric`-transport along `tangentMap` deferred-additive). -/
  base : AllowableSubspaces o x
  /-- **TRIVIALITY:** a canonical `≃L[ℂ]` iso of any two fibres of the pullback bundle
  `V ↦ Obs (expMap V)` on `𝒰`. (Node 7's `pathIso`.) -/
  triv : ∀ V V' : AllowableSubspaces o x, Obs (expMap V) ≃L[ℂ] Obs (expMap V')
  /-- The isos are mutually inverse. -/
  triv_symm : ∀ V V' : AllowableSubspaces o x, triv V' V = (triv V V').symm
  /-- The isos are COHERENT (the cocycle; holding by Principle 5.1 since `𝒰` is contractible). -/
  triv_coh : ∀ V V' V'' : AllowableSubspaces o x,
    triv V V'' = (triv V V').trans (triv V' V'')

attribute [instance] Observables.obsFibres

/-- The pullback bundle of observables on `𝒰`: `V ↦ Obs (expMap V)` (KS: "pulling back the bundle of
observables ... gives us a bundle on `𝒰`"). It is trivial by `Observables.triv`. -/
def Observables.pulledBack [gl : LorentzianCobordismGeometry] [HolomorphicComplexification]
    {o : gl.Obj} [MetCManifold (gl.Ambient o)] {x : gl.Ambient o}
    (O : Observables o x) : AllowableSubspaces o x → Type _ :=
  fun V => O.Obs (O.expMap V)

/-- **`𝒪_x` for Lorentzian `M` (KS Section 5, blueprint `def:observables`).** The common fibre of
the trivial pullback bundle on `𝒰`: the fibre `Obs (expMap base)` over the basepoint, which
`Observables.triv` canonically identifies with every other fibre ("identifying its fibres gives us
our definition of `𝒪_x`"). Inherits the bundle's nuclear-Fréchet structure. -/
def Observables.Ox [gl : LorentzianCobordismGeometry] [HolomorphicComplexification]
    {o : gl.Obj} [MetCManifold (gl.Ambient o)] {x : gl.Ambient o}
    (O : Observables o x) : Type _ :=
  O.Obs (O.expMap O.base)

end WickRotation
