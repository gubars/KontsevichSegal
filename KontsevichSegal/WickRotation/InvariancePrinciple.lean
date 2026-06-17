/- Principle 5.1 (the invariance principle): the FIFTH Lean node of Section 5 of the
Kontsevich-Segal paper (arXiv:2105.10161), and the FIRST CONTENT node built on the
node-4 Complexification hub. Encodes blueprint node `prop:invariance-principle` — this
file is where that node's `\lean` annotation will point (it is the blueprint home for
the complexification material node 4 realized as infrastructure).

KS PRINCIPLE 5.1 (KSTeX line 669). "If a `d`-dimensional cobordism `M` is a real
submanifold of a complex `d`-manifold `M_ℂ`, and `M` has an allowable complex metric
induced from a holomorphic symmetric form `g` on `TM_ℂ`, then the linear map `Z_M` does
not change when `M` is moved around smoothly inside `M_ℂ` (leaving its ends fixed),
providing the restriction of `g` to `M` remains an allowable complex metric."

THE ENCODING (scope (a): STATE the principle; the proof is additive). The principle is
a PREDICATE `IsInvariant` on a field theory `T` (Section 3's `FieldTheory`, where `Z`
lives): for every movement of `M` inside `M_ℂ`, `Z` is unchanged. The "movement" is the
node-4 hub `Isotopy` (which already bakes in Principle 5.1's PROVISO — `allowable_preserved`
and `ends_fixed`), bundled with the family of complex cobordisms it realizes.

* `Movement o` bundles the hub `Isotopy o` (the geometric movement in `M_ℂ`, whose very
  existence consumes the proviso) with the family `cob` of complex cobordisms realizing its
  stages `M_s`, TIED to the isotopy by `cob_realizes` (`cob s = CR.realize iso s`, via the
  assumed `CobordismRealization` correspondence) — so `cob` is ISOTOPY-LINKED, not a free
  family chosen side-by-side with `iso`. The endpoints `CR.dom iso ⤳ CR.cod iso` are FIXED
  (independent of `s`): this is "ends fixed" at the level `Z` sees, and it is load-bearing —
  exactly what makes the conclusion `Z(cob s) = Z(cob 0)` well-typed; were the ends to move,
  the equality could not even be stated.
* `CobordismRealization` (the `C_d^{Lor,ω} → C_d^ℂ` correspondence) is assumed as a GLOBAL
  operation (`class` fields `dom`/`cod`/`realize`), construction deferred — exactly as node 1
  assumed `pushforward` and node 2 assumed `exteriorD`; the tie `cob_realizes` is the carried
  field, like node-1 `tangentMap_eq`.
* `IsInvariant T` is the conclusion: `T.Z (mv.cob s) = T.Z (mv.cob 0)` for all
  `s ∈ [0,1]`, referencing the ACTUAL `FieldTheory.Z` and the ACTUAL hub `Isotopy`
  (via `mv.iso`), over isotopy-LINKED `cob`.

THE PROOF-REASON (KSTeX line 673), recorded as prose, NOT a Lean proof (no `sorry`, no
faked theorem): any infinitesimal movement of `M` inside `M_ℂ` is given by a complex
vector field on `M`; `Z_M` depends HOLOMORPHICALLY on `M` (blueprint `def:holomorphicity`,
the load-bearing input) and, being invariant under `Diff(M rel ∂M)`, does not change in a
direction given by a complexified tangent vector to that group. Hence `Z_M` is unchanged.
This is the higher-dimensional form of the `d = 1` contour argument. The principle is
STATED here (`IsInvariant`); that holomorphic theories SATISFY it is the deferred-additive
proof.

VACUITY / FAITHFULNESS SELF-CHECK.
* NOT OVERCOMMITTED: `cob` is isotopy-LINKED, not arbitrary. `cob_realizes` pins
  `mv.cob s = CR.realize mv.iso s` (the assumed correspondence applied to the geometric
  stages), so `IsInvariant` asserts `Z`-invariance only along the deformation the isotopy
  describes — matching KS — not along arbitrary `cob` families. The earlier version (a free
  `cob` field side-by-side with `iso`) overcommitted; the carried `cob_realizes` link fixes it.
* It BITES (is failable): a field theory whose `Z` CHANGES along a movement —
  `T.Z (mv.cob s) ≠ T.Z (mv.cob 0)` for some movement `mv`, `s ∈ [0,1]` — VIOLATES
  `IsInvariant T`. With the genuine (metric-reflecting) correspondence the moved stages are
  genuinely different cobordisms, so such non-holomorphic theories exist. Not vacuously true.
* The PROVISO is CONSUMED from the hub, not restated or weakened: forming `mv : Movement o`
  requires `mv.iso : Isotopy o`, and an `Isotopy` exists only when `allowable_preserved`
  (the restriction of `g` stays allowable) and `ends_fixed` hold. "Ends fixed" is doubly
  present: in `iso.ends_fixed` and in the fixed `CR.dom iso`/`CR.cod iso` of `cob` (which
  makes the conclusion type-check).
* `Z` is the real `FieldTheory.Z` (not a free map); the movement is the real hub `Isotopy`;
  the link `cob_realizes` is a carried field tied to `iso`.

DEFERRED (documented, not faked): the CONSTRUCTION of the `C_d^{Lor,ω} → C_d^ℂ` correspondence
`CobordismRealization.realize` — and, within it, the full metric-match (that `cob s` carries
the induced allowable metric of the geometric stage `M_s`). The metric-match is not statable
term-level: `CobordismGeometry.Mor` is opaque (no morphism-metric accessor) and the two
categories' manifolds are distinct types — the same boundary/embedding correspondence node 1
records only at the tangent level (`metric_on_shilov_boundary`) and node 3 deferred for
`EuclideanSpace`. So the correspondence is ASSUMED as a global operation and the PROPERTY that
`cob` realizes `iso` is CARRIED (`cob_realizes`), with only the construction deferred (not the
link); given the genuine (metric-reflecting) correspondence the statement is exactly KS's. The
PROOF (holomorphicity ⟹ invariance) is likewise deferred (scope (a)).

CONSTRAINTS: no `axiom` keyword, no concrete instance, no `sorry` (the principle is a
`Prop`; its proof is deferred-additive prose, never a `sorry`'d theorem). Reuses node 4's
`Isotopy` (proviso) and Section 3's `FieldTheory.Z` with their real signatures.

Blueprint: `prop:invariance-principle` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.Complexification
import KontsevichSegal.FieldTheory.FieldTheory

namespace WickRotation

open Cobordism

/-! ## The realization correspondence `C_d^{Lor,ω} → C_d^ℂ` (assumed; construction deferred) -/

/-- **Assumed (KS Principle 5.1 infrastructure): the realization correspondence.** Sends each
stage `M_s` of an isotopy — the geometric movement `iso.move s` inside `M_ℂ`, carrying the
induced allowable metric of `M_s` — to the complex cobordism (`C_d^ℂ`-morphism) that realizes
it, with FIXED endpoints `dom iso ⤳ cod iso` (independent of `s`: "ends fixed").

The CONSTRUCTION of this correspondence is DEFERRED: `CobordismGeometry.Mor` is opaque (no
morphism-metric accessor) and the two categories are distinct — the same boundary/embedding
correspondence node 1 records only at the tangent level (`metric_on_shilov_boundary`) and
node 3 deferred for `EuclideanSpace`. It is ASSUMED here as a GLOBAL operation (`class`
fields, never the `axiom` keyword, no instance), exactly as node 1 assumed `pushforward` and
node 2 assumed `exteriorD`; the TIE pinning `cob` to it is carried in `Movement.cob_realizes`.
Being a fixed global operation (not quantified per movement) is what keeps the principle from
overcommitting: `cob` is forced through this one correspondence, not chosen freely.

CARRIED vs DEFERRED (2026-06-17 narrowing check). The tie of `realize` to the geometry that the
available structure supports IS carried: `realize_functional` forces `realize iso s` to depend
only on the geometric stage `iso.move s` (well-definedness — equal stages realize to equal
cobordisms; faithful since a stage's induced metric is a function of `move s` via the hub).
EQUATING cobordisms (when stages coincide) needs no metric accessor, so it is statable. What is
genuinely INACCESSIBLE, hence deferred, is DISTINGUISHING cobordisms — `realize iso s ≠
realize iso 0` when the metric deforms. The genuine correspondence is metric-reflecting (the
moving stages, whose induced allowable metrics differ via `h_t + c² dt²` with `c` varying, go to
genuinely different cobordisms, so `Z`-invariance bites). A degenerate constant-in-`s` `realize`
on a MOVING isotopy would trivialize the principle; excluding it requires distinguishing
cobordisms, i.e. the morphism→metric accessor that `CobordismGeometry.Mor` does not provide (it
has only composition) plus the identification of the two categories' manifolds. Injectivity
cannot substitute: Principle 5.1 is invariance under reparametrization, so distinct embeddings
may realize to the SAME cobordism — `realize` is NOT injective. So only the metric-match (the
distinguishing part) stays deferred, documented; the well-definedness tie is carried. -/
class CobordismRealization [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] where
  /-- The fixed incoming end of the cobordism realizing an isotopy. -/
  dom : ∀ {o : gl.Obj}, Isotopy o → gc.Obj
  /-- The fixed outgoing end. -/
  cod : ∀ {o : gl.Obj}, Isotopy o → gc.Obj
  /-- The complex cobordism realizing stage `iso.move s` (construction deferred). -/
  realize : ∀ {o : gl.Obj} (iso : Isotopy o), ℝ → gc.Mor (dom iso) (cod iso)
  /-- **Partial well-definedness (FIX 2026-06-17; the most the available structure supports
  WITHOUT the deferred morphism-metric):** `realize iso s` depends only on the geometric stage
  `iso.move s` — equal stages realize to equal cobordisms. Faithful: a stage's induced allowable
  metric is itself a function of `iso.move s` (via the hub's `holForm`/`pushforward`), so the
  embedding determines the cobordism. This ties `realize` to the isotopy's geometry beyond its
  bare type, excluding `realize` that depend on `s` independently of `move s`. It does NOT
  exclude the degenerate constant-in-`s` `realize` on a MOVING isotopy (where the stages differ,
  so the hypothesis fails and this is vacuous); excluding that needs DISTINGUISHING cobordisms —
  the deferred morphism→metric accessor — which stays deferred. -/
  realize_functional : ∀ {o : gl.Obj} (iso : Isotopy o) (s s' : ℝ),
    iso.move s = iso.move s' → realize iso s = realize iso s'

/-! ## A movement of `M` inside `M_ℂ` and its complex-cobordism realization -/

/-- **A movement of `M` inside `M_ℂ` (KS Principle 5.1).** Bundles the node-4 hub `Isotopy o`
— the geometric movement in `M_ℂ`, whose existence consumes Principle 5.1's proviso
(`allowable_preserved` + `ends_fixed`) — with the family `cob` of complex cobordisms realizing
its stages, TIED to the isotopy by `cob_realizes`.

The endpoints `CR.dom iso ⤳ CR.cod iso` are FIXED (do not depend on `s`): this is "ends fixed"
at the level `Z` sees, and it is what makes `Z (cob s) = Z (cob 0)` well-typed.

`cob_realizes` is THE LINK (a carried field, exactly like node-1 `tangentMap_eq` / node-2
`differential_eq`): each `cob s` equals `CR.realize iso s`, the complex cobordism realizing the
geometric stage `iso.move s` via the assumed `CobordismRealization` correspondence. So `cob`
factors through `iso` — it is ISOTOPY-LINKED, not a free family chosen side-by-side with `iso`.
This is exactly what prevents `IsInvariant` from overcommitting (asserting `Z`-invariance along
arbitrary `cob`); the CONSTRUCTION of the correspondence stays deferred (see
`CobordismRealization`), but the PROPERTY that `cob` realizes `iso` is carried here. -/
structure Movement [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [CR : CobordismRealization] (o : gl.Obj) where
  /-- The geometric movement in `M_ℂ` (hub `Isotopy`); its existence consumes the proviso. -/
  iso : Isotopy o
  /-- The family of complex cobordisms realizing the stages `M_s`; fixed ends from `CR`. -/
  cob : ℝ → gc.Mor (CR.dom iso) (CR.cod iso)
  /-- **THE LINK (cob ↔ iso):** each `cob s` is the complex cobordism realizing stage
  `iso.move s` (via the assumed correspondence `CR.realize`). So `cob` factors through `iso`;
  `IsInvariant` quantifies over isotopy-LINKED `cob`, not arbitrary pairs. Carried field; the
  construction of `CR.realize` is deferred. -/
  cob_realizes : ∀ s, cob s = CR.realize iso s

/-! ## Principle 5.1 as a predicate on a field theory -/

/-- **Principle 5.1 (KS Section 5, blueprint `prop:invariance-principle`).** A field theory
`T` (Section 3's `FieldTheory`) satisfies the invariance principle when, for every movement
of `M` inside `M_ℂ`, the linear map `Z` does not change: `T.Z (mv.cob s) = T.Z (mv.cob 0)`
for all `s ∈ [0,1]`.

This references the ACTUAL `FieldTheory.Z` and the ACTUAL hub `Isotopy` (via `mv.iso`). The
proviso (the restriction of `g` to each `M_s` stays allowable, and the ends are fixed) is
CONSUMED from `mv.iso : Isotopy o` — an `Isotopy` exists only when `allowable_preserved` and
`ends_fixed` hold — not restated here. And `mv.cob` is the isotopy's realization, not a free
family: `mv.cob_realizes` pins `mv.cob s = CR.realize mv.iso s`, so the quantification is over
isotopy-LINKED `cob` (matching KS — invariance along the deformation the isotopy describes),
not over arbitrary `(iso, cob)` pairs.

NON-VACUOUS (it BITES): a field theory whose `Z` changes along some movement
(`T.Z (mv.cob s) ≠ T.Z (mv.cob 0)`) FAILS `IsInvariant`. With the genuine (metric-reflecting)
correspondence the moved stages are genuinely different cobordisms, so this is a real
constraint and a non-holomorphic `Z` fails it. The PROOF that holomorphic theories SATISFY it
(`Z` is holomorphic in `M`, invariant under `Diff(M rel ∂M)`, hence unchanged in
complexified-tangent directions — KSTeX line 673) is deferred-additive (scope (a)); it is
recorded in the module docstring as prose, not as a `sorry`'d theorem. -/
def IsInvariant [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [CobordismRealization] (T : FieldTheory) : Prop :=
  letI := T.eFrechet
  ∀ (o : gl.Obj) (mv : Movement o), ∀ s ∈ Set.Icc (0 : ℝ) 1, T.Z (mv.cob s) = T.Z (mv.cob 0)

end WickRotation
