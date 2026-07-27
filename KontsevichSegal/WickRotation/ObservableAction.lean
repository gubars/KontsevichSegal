/- The ACTION of observables and the ordering-independent multilinear map: the NINTH Lean
node of Section 5 of the Kontsevich-Segal paper (arXiv:2105.10161). Encodes the
observable-ACTION part of blueprint node `prop:observable-action`. The DEFINITION of the
observable space `𝒪_x` is node 8 (`def:observables`, `Observables.lean`); spacelike
commutativity is node 10 (`prop:spacelike-commutativity`); the vacuum-expectation domain `V_k`
is node 11 (`def:vacuum-domain` / `prop:Vk-contains-Uk`).

KS FIELD OPERATORS, the action (KSTeX 741-745). "We need no new ideas to see that for any
Lorentzian cobordism `M : Σ₀ ⤳ Σ₁` and any `x ∈ M̊` an element `ψ ∈ 𝒪_x` acts as an operator
`E_{Σ₀} → E_{Σ₁}`. Furthermore, if `x` lies on a time-slice `Σ` we get an operator
`ψ ∈ Hom(Ě_Σ; Ê_Σ)`, i.e. an unbounded operator in `E_Σ`, simply by considering the cobordisms
corresponding to a sequence of successively thinner collars of `Σ`. Indeed the same argument
shows that if `x₁,…,x_k` are distinct points on `Σ`, we have a map
`𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_Σ; Ê_Σ)` which does not depend on choosing an ordering of the
points."

THE ENCODING (scope (a): STATE the action data; the disc-removal / thinner-collars / disjoint-
collars construction is additive prose, NEVER a `sorry`'d theorem). Two pieces.

* `ObservableAction T ht M σ x O` — the SINGLE-observable action, for the ambient Lorentzian
  cobordism `M : σ₀ ⤳ σ₁` with `x` interior to `M` on the time-slice `σ` (the germ of `O`):
  - `act : 𝒪_x →ₗ[ℂ] (E_{σ₀} →L[ℂ] E_{σ₁})` — the ACTION as an operator `E_{σ₀} → E_{σ₁}`
    (`E_? = T.E (cplx ?)`, Section 3's field-theory space via the Wick object correspondence,
    node 6). Linear in `ψ` (the `k = 1` case of the multilinear map). KS's construction
    (remove a small disc `D` around `x`, leaving `M ∖ D̊ : ∂D ⊔ σ₀ ⤳ σ₁`, whose `Z` gives
    `E_{∂D} → Hom(E_{σ₀}; E_{σ₁})` by the TENSORING property `def:tensor-axiom`, then the
    inverse limit `𝒪_x = lim← E_{∂D}`) is deferred prose.
  - `slice : 𝒪_x →ₗ[ℂ] (Ě_σ →L[ℂ] Ê_σ)` — the TIME-SLICE operator `ψ ∈ Hom(Ě_σ; Ê_σ)`, an
    UNBOUNDED operator in `E_σ` (`Ě_σ = T.ECheck (cplx σ)`, `Ê_σ = T.EHat (cplx σ)`). In the
    rigging `Ě_σ ⊂ E_σ ⊂ Ê_σ` (node 6) an unbounded operator in `E_σ` is exactly an element
    of `Hom(Ě_σ; Ê_σ)`: a continuous map between the limit spaces, with NO requirement that
    it factor through a continuous operator on `E_σ`. KS's thinner-collar operators are each
    continuous on `E_σ` (positive-thickness collars `σ ⤳ σ`), but their limit in general is
    not — it escapes `Hom(E_σ; E_σ)` and exists only in `Hom(Ě_σ; Ê_σ)`; that escape is the
    content of KS's "i.e. an unbounded operator in `E_Σ`". The type therefore imposes no
    factorization through `E_σ` (and forbids none: "unbounded operator" in the standard
    usage includes operators that happen to be bounded, e.g. an observable acting as the
    identity).

RESTATEMENT (2026-07-27). The previous encoding carried two further fields:
`actAtSlice : 𝒪_x →ₗ[ℂ] (E_σ →L[ℂ] E_σ)` ("the bounded operator on `E_σ` the thinner-collar
actions converge to") and the tie
`slice_factors : ∀ ψ, slice ψ = toEHat ∘ actAtSlice ψ ∘ fromECheck`. That forced every
slice observable to be the rigging-restriction of a CONTINUOUS operator on `E_σ` and to land
in `range toEHat` — exactly what the paper's "i.e. an unbounded operator in `E_Σ`" excludes:
the collar limit in general has no bounded core, and postulating one contradicts the claim
(a genuinely non-factoring `slice` admits NO `actAtSlice` satisfying the tie, so the paper's
intended inhabitant could not inhabit the structure). Both fields were DELETED as a
statement-level infidelity (audit verdict (c) WRONG, 2026-07-27); the reviewed proposal is
`blueprint/restatements/prop-observable-action.md`. The true ties — `act` and `slice` both
arising from `T.Z` on disc-removal / collar cobordisms, and `slice` as the `k = 1` case of
`mmap` — remain deferred: the ambient `M : gl.Mor σ₀ σ₁` is OPAQUE (no disc-removal / collar
/ sub-cobordism accessor) and the morphism-level Wick correspondence is absent (the
nodes-5/6 gap), so no statable tie pins the operators to `T.Z`. Documented, not faked.

* `ObservableMultilinear T ht σ x hx O` — for `k` DISTINCT points `x₁,…,x_k` on the slice `σ`
  (`hx : Function.Injective x`), the ORDERING-INDEPENDENT multilinear map
  `𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_σ; Ê_σ)` (UNCHANGED by the restatement; the audit found this
  half faithful):
  - `mmap` gives, for each ordering `π` of the points, the `MultilinearMap` of the `k`
    observables (heterogeneous fibres `𝒪_{x_{π i}}`) into `Hom(Ě_σ; Ê_σ)`. A `MultilinearMap`
    is precisely a map OUT of the tensor product `𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k}` (its universal
    property), so this is the faithful encoding WITHOUT constructing the completed topological
    tensor product of the nuclear-Fréchet `𝒪_{x_i}` — the SAME tensor-product gap
    `def:tensor-axiom` defers (Mathlib has no topological tensor product). Per No-approximations
    the algebraic stand-in is not used; `MultilinearMap` needs no tensor-product type.
  - `ordering_indep` is the ordering-independence as an EQUATE (a SAMENESS assertion): for any
    two orderings `π, π'`, evaluating the respective maps on the respectively-reordered inputs
    gives the SAME operator. This is exactly KS's "does not depend on choosing an ordering" (the
    blueprint reason: "disjoint collars may be taken in any order"). It is NOT a
    distinctness/injectivity field (which would CONTRADICT ordering-independence — node 5/7
    lesson). `eval_orderIndep` packages the canonical operator (every ordering agrees with the
    identity ordering); PROVED, axiom-clean.

TENSOR REUSE (`def:tensor-axiom`, real signatures). Both structures carry `[MonoidalCobordism]`
and `(ht : IsTensorial T)` — the disjoint-union `⊔` of objects/cobordisms and the tensoring
property of `T` that the construction uses (the disc-removal `∂D ⊔ σ₀ ⤳ σ₁` for `act`, the
disjoint collars of the distinct points for `mmap`). These are used in the deferred construction
(prose), exactly as node 7 carries `hReal : IsReal T` and node 6 carries `hU : IsUnitary T`.
Neither `ht` nor the ambient `M` is referenced by any field (phantom parameters, kept as
documentation of the construction's context); `hx` likewise documents the distinctness the
deferred disjoint-collars construction needs.

SELF-CHECK — per-predicate degeneracy (NON-VACUITY).
* `act`/`slice` are carried MAPS from the real `𝒪_x` (node 8) into the real operator spaces
  (Section 3 `E`/`Ě`/`Ê`). The degenerate `act := 0` / `slice := 0` satisfies the fields: a
  FORCED DEFERRAL, since the genuine operator-from-`ψ` construction (disc removal / thinner
  collars + the tensoring split of `Z` + the inverse limit) is deferred infrastructure — and
  the ambient `M : gl.Mor σ₀ σ₁` is OPAQUE (no disc-removal / sub-cobordism accessor), so no
  statable tie pins the operator to `T.Z`. This is inhabitation-degeneracy, not
  statement-vacuity: the structure states the SHAPE of KS's data, and after the restatement
  it carries no propositional field — nothing ties `slice` to `act` (the removed tie was
  FALSE, not partial; the true tie via `T.Z` is deferred). The node's bite lives in
  `ordering_indep`. Documented.
* `mmap` with `mmap π := 0` degenerately satisfies `ordering_indep` (`0 = 0`); same forced
  deferral. BUT `ordering_indep` BITES as a CONDITION (its content, the ordering-independence,
  is an identity assertion that a genuinely order-DEPENDENT assignment FAILS — see below). Per
  the node-7 trivial-satisfiability nuance: when the content IS an identity assertion, the
  symmetric model is the CORRECT one, and the condition still excludes order-dependent maps.

SELF-CHECK — float-free ties (the family is pinned).
* `act`/`slice`/`mmap` reference the REAL `𝒪_x` (node 8's `Observables.Ox`) and the REAL
  `E`/`ECheck`/`EHat` (Section 3, via `WickObjectCorrespondence.cplx`, node 6). The deeper tie
  (operator = `Z` of the disc-removed / collar cobordism) is the deferred construction (opaque
  `Mor`, deferred tensor split), the same deferral as node 5's `realize` (carried field,
  construction deferred).
* `ordering_indep` PINS the family `mmap π` to `mmap (Equiv.refl _)` (no slack). From
  `eval_orderIndep`, `mmap π (v ∘ π) = mmap refl v`; and every input `w : ∀ i, 𝒪_{x_{π i}}` is of
  the form `v ∘ π` with `v := w ∘ π⁻¹` (so `(v ∘ π) i = w i`), hence `mmap π w = mmap refl (w ∘ π⁻¹)`
  for ALL `w` — `mmap π` is fully determined by `mmap refl`. So the family-plus-coherence genuinely
  encodes KS's ONE order-independent map (the family carries no data beyond `mmap refl`); it is a
  faithful encoding, not under-determination. No fix.

SELF-CHECK — equate vs distinguish (opaque `Hom`). The action lands in `Hom(Ě_σ; Ê_σ)`, an
OPAQUE operator space. The only constraint stated on it is `ordering_indep`, an EQUATE (sameness
of operators). The distinguish/measure constraints — that `act`/`slice`/`mmap` are nonzero, that
`slice ψ` is genuinely unbounded (not of the form `toEHat ∘ A ∘ fromECheck` for continuous
`A : E_σ →L E_σ`), that the operator equals `Z` of a specific cobordism — would require
measuring the operator or the deferred construction; they are deferred, not faked. NO
distinctness/injectivity field is added, and NO factorization field either: mandating the
factorization was the restated infidelity, and mandating its negation would overshoot the
paper (KS assert membership in `Hom(Ě_σ; Ê_σ)`, which contains the boundedly-factoring
operators as special cases).

SELF-CHECK — ordering-independence BITES. Take a genuinely order-DEPENDENT assignment, e.g.
`mmap π := if π = 1 then m₀ else 0` with `m₀ ≠ 0`. Then `ordering_indep 1 π v` (for `π ≠ 1`)
demands `m₀ v = 0` for all `v`, forcing `m₀ = 0` — contradiction. So an order-dependent map is
EXCLUDED; the symmetric / order-independent KS construction satisfies it. It is a genuine
constraint, not vacuously true.

DEFERRED (documented, not faked): the disc-removal `M ∖ D̊` and the inverse limit `𝒪_x = lim← E_{∂D}`
producing `act`; the thinner-collars limit producing `slice` (the limit exists only in
`Hom(Ě_σ; Ê_σ)` — there is no bounded core to carry, which is why none is); the tie of `act`
and `slice` to `T.Z` and to each other (needs the morphism-level Wick correspondence + the
split of the opaque `M`); `slice` as the `k = 1` case of `mmap` (needs shared context between
the two structures); the disjoint-collars construction of `mmap` and the completed topological
tensor product `𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k}` (the same Mathlib gap `def:tensor-axiom` defers); the
geometric relationships `x ∈ M̊`, "`σ` is a time-slice of `M` through `x`", and the
distinctness-of-collars (no interior/time-slice predicate on the opaque `Mor`; the same
Lorentzian↔complex deferral as nodes 1/3/5/6).

CONSTRAINTS: no `axiom` keyword, no concrete instance, no `sorry` (the action and the multilinear
map are STATED as `structure`s; the construction is prose, never a `sorry`'d theorem;
`eval_orderIndep` is PROVED from `ordering_indep`, axiom-clean). Reuses node 8's `Observables` /
`Observables.Ox`, node 6's `WickObjectCorrespondence` and Section 3's `FieldTheory.E`/`ECheck`/`EHat`,
and `def:tensor-axiom`'s `MonoidalCobordism` / `IsTensorial`, with their real signatures.

MARKING: `prop:observable-action` is `\notready` in the blueprint after the restatement (the
decided post-fix marking): the statement-level infidelity is fixed, but the encoding
underspecifies the proposition — `M`/`ht` are phantoms and no existence-level claim or `T.Z`
tie is statable against the opaque `Mor` — the same standard as the 2026-07-27 demotion batch
(thm:unitary-gh, prop:invariance-principle, prop:lorentzian-E-welldefined).

Blueprint: `prop:observable-action` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.Observables
import KontsevichSegal.WickRotation.UnitaryGH
import KontsevichSegal.FieldTheory.TensorAxiom
import Mathlib.LinearAlgebra.Multilinear.Basic

namespace WickRotation

open Cobordism

/-! ## The action of an observable: `E_{σ₀} → E_{σ₁}` and the time-slice operator `Hom(Ě_σ; Ê_σ)` -/

/-- **The action of an observable on a Lorentzian cobordism (KS Section 5, blueprint
`prop:observable-action`), the single-observable case.** For a field theory `T` (tensorial,
`ht`), an ambient Lorentzian cobordism `M : σ₀ ⤳ σ₁`, and an observable `O` at a point `x` on
a time-slice `σ` in the interior of `M`:

* `act` is the action `ψ ↦ (E_{σ₀} → E_{σ₁})`, linear in `ψ`. (`E_? = T.E (cplx ?)` via the
  Wick object correspondence, node 6.) Built — in deferred prose — by removing a small disc
  around `x` (`M ∖ D̊ : ∂D ⊔ σ₀ ⤳ σ₁`), applying the tensoring property `def:tensor-axiom` to
  get `E_{∂D} → Hom(E_{σ₀}; E_{σ₁})`, and passing to the inverse limit `𝒪_x = lim← E_{∂D}`.
* `slice` is the time-slice operator `ψ ∈ Hom(Ě_σ; Ê_σ)`, an UNBOUNDED operator in `E_σ`:
  in the rigging `Ě_σ ⊂ E_σ ⊂ Ê_σ` an unbounded operator in `E_σ` is exactly an element of
  `Hom(Ě_σ; Ê_σ)`, with NO requirement that it factor through a continuous operator on `E_σ`
  (KS: "simply by considering the cobordisms corresponding to a sequence of successively
  thinner collars of `Σ`" — the collar operators are each continuous on `E_σ`, but their
  limit in general is not; the type deliberately does NOT assert such a factorization).

The geometric relationships (`x ∈ M̊`, `σ` a time-slice of `M` through `x`) and the
operator-from-`ψ` constructions are deferred (the opaque `Mor`, the deferred tensor split /
inverse limit). The action MAPS are carried, tied to the real `𝒪_x` (node 8) and the real
`E`/`Ě`/`Ê` (Section 3). Not constructed for any concrete theory. -/
structure ObservableAction [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [m : MonoidalCobordism] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (ht : IsTensorial T)
    {σ₀ σ₁ : gl.Obj} (M : gl.Mor σ₀ σ₁)
    (σ : gl.Obj) [MetCManifold (gl.Ambient σ)] (x : gl.Ambient σ)
    (O : Observables σ x) where
  /-- The action `ψ ↦ (E_{σ₀} → E_{σ₁})` of an observable on the ambient cobordism `M`,
  linear in `ψ ∈ 𝒪_x`. The construction (disc removal + tensoring + inverse limit) and the
  tie to `T.Z` across the opaque `M` are deferred prose. -/
  act : O.Ox →ₗ[ℂ] (T.E (WOC.cplx σ₀) →L[ℂ] T.E (WOC.cplx σ₁))
  /-- The time-slice operator `ψ ∈ Hom(Ě_σ; Ê_σ)`, an unbounded operator in `E_σ` — an
  element of the Hom-space of the rigging with no factorization through `E_σ` imposed. The
  thinner-collars construction is deferred prose. -/
  slice : O.Ox →ₗ[ℂ] (T.ECheck (WOC.cplx σ) →L[ℂ] T.EHat (WOC.cplx σ))

/-! ## The ordering-independent multilinear map `𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_σ; Ê_σ)` -/

/-- **The ordering-independent multilinear map (KS Section 5, blueprint `prop:observable-action`),
the key content.** For a tensorial field theory `T` (`ht`), a time-slice `σ`, and `k` DISTINCT
points `x₁,…,x_k` on `σ` (`hx : Function.Injective x`) with observables `O i` at `x i`, the
multilinear map `𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k} → Hom(Ě_σ; Ê_σ)` that does NOT depend on the ordering.

* `mmap π` is, for each ordering `π` of the points, the `MultilinearMap` of the `k` observable
  spaces `𝒪_{x_{π i}}` into `Hom(Ě_σ; Ê_σ)`. A `MultilinearMap` is exactly a map out of the
  tensor product `𝒪_{x₁} ⊗ … ⊗ 𝒪_{x_k}` (universal property), so this encodes the map WITHOUT
  the completed topological tensor product Mathlib lacks (the gap `def:tensor-axiom` defers). The
  disjoint-collars construction (via the tensoring property `def:tensor-axiom`) is deferred prose.

* `ordering_indep` is the ordering-independence, an EQUATE (SAMENESS): for any two orderings
  `π, π'`, the maps agree on the respectively-reordered inputs. This is "disjoint collars may be
  taken in any order". It BITES: an order-DEPENDENT assignment fails it (so a non-symmetric map is
  excluded). It is NOT a distinctness field (which would contradict ordering-independence).

The points being distinct (`hx`) is needed for the disjoint collars (deferred construction). Not
constructed for any concrete theory. -/
structure ObservableMultilinear [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [m : MonoidalCobordism] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (ht : IsTensorial T)
    (σ : gl.Obj) [MetCManifold (gl.Ambient σ)] {k : ℕ}
    (x : Fin k → gl.Ambient σ) (hx : Function.Injective x)
    (O : ∀ i, Observables σ (x i)) where
  /-- The multilinear map of the `k` observables into `Hom(Ě_σ; Ê_σ)`, presented for each ordering
  `π` of the points (a map out of `𝒪_{x_{π 1}} ⊗ … ⊗ 𝒪_{x_{π k}}`). The disjoint-collars
  construction is deferred prose. -/
  mmap : ∀ π : Equiv.Perm (Fin k),
    MultilinearMap ℂ (fun i => (O (π i)).Ox)
      (T.ECheck (WOC.cplx σ) →L[ℂ] T.EHat (WOC.cplx σ))
  /-- **ORDERING-INDEPENDENCE (the identity-content), as an EQUATE.** For any two orderings
  `π, π'`, evaluating the respective maps on the respectively-reordered inputs gives the SAME
  operator. A sameness assertion (different orderings ⟹ same map), NOT a distinctness field. -/
  ordering_indep : ∀ (π π' : Equiv.Perm (Fin k)) (v : ∀ i, (O i).Ox),
    mmap π (fun i => v (π i)) = mmap π' (fun i => v (π' i))

/-- **The canonical ordering-independent operator.** Every ordering `π` agrees with the identity
ordering: evaluating `mmap π` on the `π`-reordered inputs equals `mmap (Equiv.refl _)` on the
original inputs. This packages `ordering_indep` as "there is a well-defined operator for the
unordered configuration". PROVED from `ordering_indep` (axiom-clean). -/
theorem ObservableMultilinear.eval_orderIndep [gc : CobordismGeometry]
    [gl : LorentzianCobordismGeometry] [HolomorphicComplexification] [m : MonoidalCobordism]
    [WOC : WickObjectCorrespondence] {T : FieldTheory} {ht : IsTensorial T} {σ : gl.Obj}
    [MetCManifold (gl.Ambient σ)] {k : ℕ} {x : Fin k → gl.Ambient σ}
    {hx : Function.Injective x} {O : ∀ i, Observables σ (x i)}
    (W : ObservableMultilinear T ht σ x hx O) (π : Equiv.Perm (Fin k)) (v : ∀ i, (O i).Ox) :
    W.mmap π (fun i => v (π i)) = W.mmap (Equiv.refl (Fin k)) v :=
  W.ordering_indep π (Equiv.refl (Fin k)) v

end WickRotation
