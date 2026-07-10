/- Spacelike commutativity (the Wightman locality axiom): the TENTH Lean node of Section 5 of
the Kontsevich-Segal paper (arXiv:2105.10161). Encodes blueprint node
`prop:spacelike-commutativity`. The observable ACTION + the ordering-independent multilinear map
are node 9 (`prop:observable-action`, `ObservableAction.lean`); the unitary propagation and the
rigged triple `Ě ⊂ E^Hilb ⊂ Ê` are node 6 (`thm:unitary-gh`, `UnitaryGH.lean`); the vacuum domain
`V_k` is node 11.

KS FIELD OPERATORS, spacelike commutativity (KSTeX 749-753). "the spaces `Ě_{Σ_t} ⊂ E_{Σ_t}^Hilb
⊂ E_{Σ_t}` for all times `t_0 ≤ t ≤ t_1` can be identified with those at time `t_0` by the unitary
propagation `Z_{t,t'}` from time `t` to a later time `t'` to get a single rigged Hilbert space
`Ě ⊂ E^Hilb ⊂ Ê`, and we can define an unbounded operator `ψ̃ = Z_{t_0,t}^{-1} ∘ ψ ∘ Z_{t_0,t} :
Ě → Ê` for any `ψ ∈ 𝒪_x` with `x ∈ Σ_t`. Furthermore, if we change the choice of time-function on
the cobordism, so that `x` lies on a different time-slice, then `ψ̃` will not change. The fact that
two observables `ψ, ψ'` situated at space-like separated points `x, x'` give rise to operators
`ψ̃, ψ̃'` which are composable, and commute, is now clear. For if `x` and `x'` are space-like
separated we can choose a single time-slice `Σ_t` which contains them both, and we see that the
composed operator, in either order, is `Z_{t_0,t}^{-1} ∘ (ψ ⊗ ψ') ∘ Z_{t_0,t}`."

THE ENCODING (scope (a): STATE the result; the proof of commutativity is PROVED from node 9's
ordering-independence, not asserted).

* `RiggedPropagation W base s M hM` — the unitary propagation `Z_{t_0,t}` on the rigged triple. The
  propagation on `E^Hilb` IS the node-6 unitary iso `W.unitary M hM : E^Hilb_base ≃L E^Hilb_s` (NOT
  a free equiv); its action on the rigging is carried as `propCheck : Ě_base ≃L Ě_s` and
  `propHat : Ê_base ≃L Ê_s`, whose ACTION DIRECTION is tied to `W.unitary` by `propCheck_compat`/
  `propHat_compat` plus `checkIncl_injective` (matching node 6's `unitary_check`/`unitary_hat` — the
  iso carries `Ě → Ě`, `Ê → Ê`), `propCheck_eq`/`propHat_eq` proving it canonical. The `≃L`
  invertibility of `propCheck`/`propHat` is KS's asserted identification, ASSUMED (node 6 exposes only
  one-directional `→L` carrying; see discipline 5).

* `RiggedPropagation.conjugate P op = propHat.symm ∘L op ∘L propCheck` — the conjugation
  `Z^{-1} ∘ op ∘ Z`. Both the single-observable `ψ̃` and the composed operator factor through it.

* `RiggedPropagation.tildePsi P A ψ = P.conjugate (A.slice ψ)` — the conjugated operator
  `ψ̃ = Z^{-1} ∘ ψ ∘ Z : Ě → Ê`, where `A.slice ψ` is node 9's time-slice operator
  (`ObservableAction.slice`). `tildePsi_eq` is the carried `*_eq` tie (definitional): `ψ̃` is the
  conjugate of node 9's slice operator by the node-6 propagation, NOT a free `Hom` element.

* `RiggedPropagation.spacelike_commute` (the MAIN result, PROVED) — for the multilinear map of node 9
  (`ObservableMultilinear`, the unordered tensor `𝒪_{x_1} ⊗ … ⊗ 𝒪_{x_k}`) the composed operator
  `Z^{-1} ∘ (mmap π) ∘ Z` is INDEPENDENT of the ordering `π`: `P.conjugate (mmap π (v∘π)) =
  P.conjugate (mmap π' (v∘π'))`. For `k = 2` this is KS's "the composed operator, in either order,
  is `Z^{-1}(ψ ⊗ ψ')Z`", hence `ψ̃, ψ̃'` commute. PROVED by `rw [mult.ordering_indep π π' v]` — the
  commutator content IS node 9's ordering-independence, conjugated by `Z`.

* `RiggedPropagation.propCheck_eq` / `RiggedPropagation.propHat_eq` (both PROVED) — the propagation
  is CANONICAL on the rigging: any two `RiggedPropagation`s (same `W`, `base`, `s`, `M`, `hM`) have
  the same `propCheck` (forced by `propCheck_compat` + node 6's `checkIncl_injective`) and the same
  `propHat` (forced by `propHat_compat` + the DENSE range and continuity of `hatIncl`). So `Z`'s
  action on `Ě`/`Ê` is not free data — it is forced by the node-6 unitary; this fully closes the
  canonicity of `tildePsi`.

THE FIVE STANDING DISCIPLINES.
1. FLOAT-FREE JOIN. `ψ̃` is the conjugate of node 9's `slice` operator by `Z`: `tildePsi := conjugate
   (A.slice ψ)`, with `tildePsi_eq` the definitional `*_eq` tie (`ψ̃ = propHat.symm ∘L A.slice ψ ∘L
   propCheck`). The ACTION DIRECTION of `propCheck`/`propHat` is tied to the node-6 iso `W.unitary` by
   `propCheck_compat`/`propHat_compat` plus `checkIncl_injective`; `propCheck_eq` PROVES `propCheck`
   canonical and `propHat_eq` PROVES `propHat` canonical. (The `≃L` INVERTIBILITY of `propCheck`/
   `propHat` is KS's asserted identification, ASSUMED — node 6 exposes only one-directional `→L`
   carrying; see discipline 5.) The composed operator is `conjugate (ObservableMultilinear.mmap …)`,
   tied to node 9's unordered tensor — not a free `Hom` element.
2. EQUATE-vs-DISTINGUISH. Spacelike commutativity is the EQUATE `conjugate (mmap π …) = conjugate
   (mmap π' …)` (sameness of the two orders). NO distinctness field is added (no "commutator ≠ 0", no
   "ψ̃ depends on the time-function") — those would be FALSE and contradict the content. (Fourth
   application of the key lesson, after nodes 5/6/7/9.)
3. VERIFICATION POSTURE. `spacelike_commute` is PROVED (not asserted): it reduces to
   `mult.ordering_indep`. `propCheck_eq` is PROVED from `checkIncl_injective`. No `commutes` raw field.
4. NON-VACUITY / trivial-satisfiability nuance. The trivial model (zero operators, `Z = id`,
   `propCheck = propHat = refl`) is the CORRECT trivial model for a sameness assertion. It still
   BITES: the equate references the REAL `ContinuousLinearMap.comp` and the REAL node-9 unordered
   tensor `mmap`, so an order-DEPENDENT `mmap` (a `mult` failing `ordering_indep`) FAILS it, and a
   `propCheck`/`propHat` not compatible with `W.unitary` is excluded by the `*_compat` ties.
5. FORCED-DEFERRAL honesty. (a) The literal composition of unbounded operators `ψ̃ ∘ ψ̃' : Ě → Ê`
   then `Ě → Ê` has a rigged-Hilbert-space DOMAIN subtlety the paper glosses ("composable"): the
   types `Ě → Ê` do not compose. Following KS, the "composed operator, in either order" is encoded as
   the conjugate of node 9's UNORDERED single-slice tensor (`conjugate (mmap …)`) — KS's actual
   content — and `spacelike_commute` proves the two orders equal; the abstract unbounded-operator
   composition is DEFERRED (named reason: rigged-Hilbert-space domain of `Ě → Ê` composition, not in
   Mathlib). (b) Cross-foliation TIME-FUNCTION INDEPENDENCE ("if a different time-function puts `x`
   on a different slice, `ψ̃` will not change") is DEFERRED (named reason: it needs node 8's
   Wick-rotation trivialization identifying `𝒪_x` across the slices `x` lies on — node 8 deferred its
   observable-bundle trivialization — together with Principle 5.1, node 5). NO distinctness field is
   added in its place (discipline 2). (c) `≃L` INVERTIBILITY of the rigging propagation
   `propCheck`/`propHat` is DEFERRED: node 6's `unitary_check`/`unitary_hat` give only one-directional
   `→L` carrying of `W.unitary`; the continuous inverse on `Ě`/`Ê` is not exposed, so packaging
   `propCheck`/`propHat` as `≃L` is KS's asserted identification ("the spaces … can be identified … by
   the unitary propagation `Z`"), ASSUMED. The `*_compat` ties plus `checkIncl_injective` still force
   the ACTION DIRECTION (`propCheck_eq`/`propHat_eq` prove it canonical); only the invertibility is
   assumed. Principled fix: strengthen node 6's `unitary_check`/`unitary_hat` to deliver `≃L` and prove
   them canonical — flagged for the advisor checkpoint. The same-foliation well-definedness IS
   captured: `propCheck_eq` (on `Ě`) and `propHat_eq` (on `Ê`) show the propagation canonical on the
   whole rigging, so `ψ̃` — which rides on both `propCheck` and `propHat` — does not depend on the
   realization of `Z`.

GEOMETRY (assumed / deferred). Spacelike separation and "a common time-slice containing both points"
are Lorentzian causal geometry, not in Mathlib. They are encoded by taking the common time-slice `s`
as given, with the points `x : Fin k → gl.Ambient s.1` DISTINCT (`hx : Function.Injective x`): a
time-slice is a spacelike hypersurface, so distinct points on it ARE mutually spacelike separated —
this realizes the KS premise. The spacelike ⟹ common-slice direction (that spacelike-separated points
can be put on one slice) is the deferred geometric input (the same causal-geometry gap as node 2's
`LightConeGeometry`). No concrete instance of any assumed-geometry class is constructed.

CONSTRAINTS: no `axiom` keyword, no concrete instance, no `sorry` (`spacelike_commute` and
`propCheck_eq` are PROVED; the deferrals are documented prose, never `sorry`'d). Reuses node 6's
`InducesUnitaryGH` (`unitary`, `checkIncl`/`hatIncl`, `checkIncl_injective`, `unitary_check`/
`unitary_hat` content) and node 9's `ObservableAction.slice` / `ObservableMultilinear` (`mmap`,
`ordering_indep`), with their real signatures.

Blueprint: `prop:spacelike-commutativity` in `blueprint/src/section5.tex` (its `\lean` annotation
lands with the forthcoming content-node annotation batch).
-/

import KontsevichSegal.WickRotation.ObservableAction

namespace WickRotation

open Cobordism

universe u

variable [gc : CobordismGeometry] [gi : GermIsoGeometry] [dc : DualConjugateGeometry]
  [gl : LorentzianCobordismGeometry] [HolomorphicComplexification] [lc : LightConeGeometry]
  [CobordismRealization] [WOC : WickObjectCorrespondence]
  {T : FieldTheory} {hU : IsUnitary T} {hI : IsInvariant T}

/-! ## The unitary propagation `Z_{t₀,t}` on the rigged triple -/

/-- **The unitary propagation `Z_{t₀,t}` on the rigged triple `Ě ⊂ E^Hilb ⊂ Ê` (KS Section 5,
blueprint `prop:spacelike-commutativity`).** For a node-6 unitary-functor witness `W` and a globally
hyperbolic cobordism `M : base ⤳ s` between time-symmetric germs (the propagation from the base
time-slice `t₀` to the slice `s = Σ_t`), the propagation on the rigging.

The propagation on `E^Hilb` IS the node-6 unitary iso `W.unitary M hM : E^Hilb_base ≃L E^Hilb_s`
(NOT a free equiv). Its action on the limit spaces of the rigging is carried as `propCheck` (on
`Ě`) and `propHat` (on `Ê`), each a `≃L[ℂ]`. The ACTION DIRECTION of `propCheck`/`propHat` is tied
to `W.unitary` by `propCheck_compat` / `propHat_compat` together with node 6's `checkIncl_injective`
— these record exactly node 6's `unitary_check` / `unitary_hat` content (the unitary iso carries
`Ě → Ě` and `Ê → Ê`), so on `Ě`/`Ê` the action is the node-6 unitary iso seen on the rigging, not
free data (`propCheck_eq` / `propHat_eq` prove it canonical). The `≃L` INVERTIBILITY of `propCheck`/
`propHat`, by contrast, is KS's asserted identification ("the spaces … can be identified … by the
unitary propagation `Z`"), ASSUMED here, not derived: node 6's `unitary_check` / `unitary_hat`
expose only a ONE-DIRECTIONAL `→L` carrying of `W.unitary`, never the continuous inverse on `Ě`/`Ê`
(see discipline 5). Not constructed for any concrete theory. -/
structure RiggedPropagation (W : InducesUnitaryGH.{u} T hU hI)
    (base s : TimeSymmetricGerm) (M : gl.Mor base.1 s.1) (hM : IsGloballyHyperbolicOmega M) where
  /-- The propagation on `Ě`: `Z_{t₀,t}|_{Ě} : Ě_base ≃L Ě_s` (the `Ě`-carrying of `W.unitary`). -/
  propCheck : T.ECheck (WOC.cplx base.1) ≃L[ℂ] T.ECheck (WOC.cplx s.1)
  /-- The propagation on `Ê`: `Z_{t₀,t}|_{Ê} : Ê_base ≃L Ê_s` (the `Ê`-carrying of `W.unitary`). -/
  propHat : T.EHat (WOC.cplx base.1) ≃L[ℂ] T.EHat (WOC.cplx s.1)
  /-- **TIE:** `propCheck` is the `Ě`-carrying of the node-6 unitary `W.unitary M hM` (matches
  `unitary_check`): along `checkIncl`, propagating then including equals including then propagating
  via `W.unitary`. Ties `propCheck`'s ACTION DIRECTION to the node-6 iso (with
  `checkIncl_injective`, `propCheck_eq` then forces it canonical); the `≃L` invertibility is KS's
  assumed identification (discipline 5). -/
  propCheck_compat : ∀ v : T.ECheck (WOC.cplx base.1),
    W.checkIncl s (propCheck v) = W.unitary M hM (W.checkIncl base v)
  /-- **TIE:** `propHat` is the `Ê`-carrying of `W.unitary M hM` (matches `unitary_hat`). -/
  propHat_compat : ∀ e : W.EHilb base,
    W.hatIncl s (W.unitary M hM e) = propHat (W.hatIncl base e)

/-- **The conjugation `Z^{-1} ∘ op ∘ Z` by the propagation.** Sends a time-slice operator
`op : Ě_s → Ê_s` at the slice `s` to the operator `Ě_base → Ê_base` on the single rigged Hilbert
space at the base time `t₀`. Both the single-observable `ψ̃` and the composed operator factor
through this. -/
def RiggedPropagation.conjugate {W : InducesUnitaryGH.{u} T hU hI} {base s : TimeSymmetricGerm}
    {M : gl.Mor base.1 s.1} {hM : IsGloballyHyperbolicOmega M} (P : RiggedPropagation W base s M hM)
    (op : T.ECheck (WOC.cplx s.1) →L[ℂ] T.EHat (WOC.cplx s.1)) :
    T.ECheck (WOC.cplx base.1) →L[ℂ] T.EHat (WOC.cplx base.1) :=
  P.propHat.symm.toContinuousLinearMap.comp (op.comp P.propCheck.toContinuousLinearMap)

/-! ## The conjugated field operator `ψ̃ = Z^{-1} ∘ ψ ∘ Z` -/

/-- **The conjugated field operator `ψ̃ = Z_{t₀,t}^{-1} ∘ ψ ∘ Z_{t₀,t} : Ě → Ê` (KS line 750).**
For an observable `ψ ∈ 𝒪_x` with `x` on the slice `s`, with node 9's time-slice operator `A.slice`
(`ObservableAction.slice`), `ψ̃` is the slice operator conjugated by the propagation `Z`. The
float-free tie is `tildePsi_eq` (definitional). -/
def RiggedPropagation.tildePsi {W : InducesUnitaryGH.{u} T hU hI} {base s : TimeSymmetricGerm}
    {M : gl.Mor base.1 s.1} {hM : IsGloballyHyperbolicOmega M} (P : RiggedPropagation W base s M hM)
    [MonoidalCobordism] (ht : IsTensorial T) {σ₀ σ₁ : gl.Obj} {M_amb : gl.Mor σ₀ σ₁}
    [MetCManifold (gl.Ambient s.1)] {xpt : gl.Ambient s.1} {O : Observables s.1 xpt}
    (A : ObservableAction T ht M_amb s.1 xpt O) (ψ : O.Ox) :
    T.ECheck (WOC.cplx base.1) →L[ℂ] T.EHat (WOC.cplx base.1) :=
  P.conjugate (A.slice ψ)

/-- **The float-free tie (discipline 1), definitional.** `ψ̃ = Z^{-1} ∘ (node-9 slice op) ∘ Z`:
`tildePsi` is the conjugate of node 9's `A.slice ψ` by the node-6 propagation, not a free `Hom`
element. -/
theorem RiggedPropagation.tildePsi_eq {W : InducesUnitaryGH.{u} T hU hI}
    {base s : TimeSymmetricGerm} {M : gl.Mor base.1 s.1} {hM : IsGloballyHyperbolicOmega M}
    (P : RiggedPropagation W base s M hM) [MonoidalCobordism] (ht : IsTensorial T) {σ₀ σ₁ : gl.Obj}
    {M_amb : gl.Mor σ₀ σ₁} [MetCManifold (gl.Ambient s.1)] {xpt : gl.Ambient s.1}
    {O : Observables s.1 xpt} (A : ObservableAction T ht M_amb s.1 xpt O)
    (ψ : O.Ox) :
    P.tildePsi ht A ψ
      = P.propHat.symm.toContinuousLinearMap.comp
          ((A.slice ψ).comp P.propCheck.toContinuousLinearMap) :=
  rfl

/-! ## The propagation is canonical (verification posture) -/

/-- **The propagation on `Ě` is CANONICAL (PROVED).** Any two `RiggedPropagation`s for the same
`W`, `base`, `s`, `M`, `hM` have the same `propCheck`: it is determined by `propCheck_compat` and
node 6's `checkIncl_injective` (the inclusion `Ě_s → E^Hilb_s` is injective). So `Z` on `Ě` is not
free data — it is forced by the node-6 unitary `W.unitary M hM`. (The `Ê`-side `propHat` is likewise
canonical, PROVED in `propHat_eq` — by `propHat_compat` together with the dense range and continuity
of `hatIncl`.) -/
theorem RiggedPropagation.propCheck_eq {W : InducesUnitaryGH.{u} T hU hI}
    {base s : TimeSymmetricGerm} {M : gl.Mor base.1 s.1} {hM : IsGloballyHyperbolicOmega M}
    (P P' : RiggedPropagation W base s M hM) (v : T.ECheck (WOC.cplx base.1)) :
    P.propCheck v = P'.propCheck v :=
  W.checkIncl_injective s (by rw [P.propCheck_compat, P'.propCheck_compat])

/-- **The propagation on `Ê` is CANONICAL (PROVED).** Any two `RiggedPropagation`s for the same
`W`, `base`, `s`, `M`, `hM` have the same `propHat`. Unlike `propCheck` (pinned by INJECTIVITY of
`checkIncl`), `propHat` is pinned by DENSITY: by `propHat_compat`, both `P.propHat` and `P'.propHat`
agree with the `W.unitary M hM`-conjugation on the range of `W.hatIncl base`; that range is dense
(node 6's `hatIncl_dense`); both maps are continuous; so they agree everywhere. Together with
`propCheck_eq` this fully closes the canonicity of `tildePsi` — `ψ̃` rides on BOTH `propCheck` and
`propHat`, so `ψ̃` does not depend on the realization of `Z`. -/
theorem RiggedPropagation.propHat_eq {W : InducesUnitaryGH.{u} T hU hI}
    {base s : TimeSymmetricGerm} {M : gl.Mor base.1 s.1} {hM : IsGloballyHyperbolicOmega M}
    (P P' : RiggedPropagation W base s M hM) (e : T.EHat (WOC.cplx base.1)) :
    P.propHat e = P'.propHat e := by
  have hagree : ⇑P.propHat ∘ ⇑(W.hatIncl base) = ⇑P'.propHat ∘ ⇑(W.hatIncl base) := by
    funext y
    exact (P.propHat_compat y).symm.trans (P'.propHat_compat y)
  have heq : ⇑P.propHat = ⇑P'.propHat :=
    (W.hatIncl_dense base).equalizer P.propHat.continuous P'.propHat.continuous hagree
  exact congrFun heq e

/-! ## Spacelike commutativity (the main result, PROVED) -/

/-- **Spacelike commutativity / the Wightman locality axiom (KS line 753, PROVED).** For `k`
distinct points on a common time-slice `s` (`hx : Function.Injective x` — distinct points on the
spacelike hypersurface `s`, realizing mutual spacelike separation), with node 9's ordering-
independent multilinear map `mult` (`ObservableMultilinear`), the composed operator
`Z^{-1} ∘ (𝒪_{x_1} ⊗ … ⊗ 𝒪_{x_k}) ∘ Z` does NOT depend on the ordering `π` of the points:
`P.conjugate (mmap π (v ∘ π)) = P.conjugate (mmap π' (v ∘ π'))`.

For `k = 2` this is exactly KS's "the composed operator, in either order, is
`Z_{t₀,t}^{-1} ∘ (ψ ⊗ ψ') ∘ Z_{t₀,t}`", so the field operators `ψ̃, ψ̃'` at space-like separated
points commute. EQUATE (sameness of the two orders), NOT a distinctness field.

PROVED by reducing to node 9's `ordering_indep` (`mmap π (v ∘ π) = mmap π' (v ∘ π')`) conjugated by
`Z`. The literal composition `ψ̃ ∘ ψ̃'` of unbounded operators `Ě → Ê` (domain subtlety the paper
glosses as "composable") is deferred; KS's "composed operator, in either order" is the conjugate of
node 9's unordered tensor, which is what is stated and proved here. -/
theorem RiggedPropagation.spacelike_commute {W : InducesUnitaryGH.{u} T hU hI}
    {base s : TimeSymmetricGerm} {M : gl.Mor base.1 s.1} {hM : IsGloballyHyperbolicOmega M}
    (P : RiggedPropagation W base s M hM) [MonoidalCobordism] (ht : IsTensorial T)
    [MetCManifold (gl.Ambient s.1)] {k : ℕ} {x : Fin k → gl.Ambient s.1}
    {hx : Function.Injective x} {O : ∀ i, Observables s.1 (x i)}
    (mult : ObservableMultilinear T ht s.1 x hx O)
    (v : ∀ i, (O i).Ox) (π π' : Equiv.Perm (Fin k)) :
    P.conjugate (mult.mmap π (fun i => v (π i)))
      = P.conjugate (mult.mmap π' (fun i => v (π' i))) := by
  rw [mult.ordering_indep π π' v]

end WickRotation
