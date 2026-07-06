/- Theorem 5.2 (the unitary functor on the globally hyperbolic category): the SIXTH
Lean node of Section 5 of the Kontsevich-Segal paper (arXiv:2105.10161), and the
CAPSTONE of Section 5. Encodes blueprint node `thm:unitary-gh`. This is the convergence
node: it reuses Principle 5.1 (node 5, `IsInvariant`, taken as a hypothesis — the proof
engine), Section 3's C1-FIXED `IsUnitary` (genuine reflection-positivity, the load-bearing
hypothesis), the field theory's limit spaces `Ě`/`E`/`Ê` and the Hilbert completion Section 3
deferred, time-symmetry, and global hyperbolicity (node 2).

KS THEOREM 5.2 (KSTeX line 685, functor form; 689–693, precise form).
* FUNCTOR FORM: a unitary QFT on `C_d^ℂ` (Section 3 `def:unitarity`) induces a functor from
  the real-analytic globally hyperbolic category `C_d^{gh,ω}` (node 2) to topological vector
  spaces, taking time-symmetric objects to Hilbert spaces and gh cobordisms between them to
  UNITARY operators.
* PRECISE FORM (kept, carries content the functor form does not): for a time-symmetric germ
  `Σ` there is a Hilbert space `E_Σ^Hilb` with `Ě_Σ ⊂ E_Σ^Hilb ⊂ Ê_Σ` (the completion of the
  pre-Hilbert `Ě_Σ` of `def:unitarity`, between the limit spaces of `def:field-theory` via the
  injective-dense maps of `def:continuity`); a real-analytic gh cobordism `Σ_0 ⤳ Σ_1` between
  time-symmetric hypersurfaces induces a UNITARY isomorphism `E_{Σ_0}^Hilb → E_{Σ_1}^Hilb`
  which ALSO carries `Ě_{Σ_0} → Ě_{Σ_1}` and `Ê_{Σ_0} → Ê_{Σ_1}`.

THE ENCODING (scope (a): STATE both forms; the proof is deferred-additive prose). Both forms
are bundled in the structure `InducesUnitaryGH T hU hI` (the witness data of the conclusion),
parametrized by the hypotheses `hU : IsUnitary T` (C1-fixed reflection-positivity) and
`hI : IsInvariant T` (Principle 5.1, node 5 — the proof engine). Theorem 5.2 is the assertion that
this structure is INHABITED for a unitary `T` — "a unitary QFT (with Principle 5.1) induces the gh
unitary functor". It is STATED (the structure, parametrized by `hU`), not proved (no `sorry`'d
theorem); like nodes 4–5's assumed structures, the inhabitation is the deferred-additive proof.
(Germ variables are written `σ`, lowercase, since `Σ` is reserved for Sigma-type notation.)

* `EHilb : TimeSymmetricGerm → Type*` with `HilbertFibres` — the Hilbert spaces `E_Σ^Hilb`
  (functor form: time-symmetric objects → Hilbert spaces).
* `checkIncl`/`hatIncl` + injective/dense + `factor` — the inclusions `Ě_Σ ⊂ E_Σ^Hilb ⊂ Ê_Σ`
  (precise form), the composite `Ě → E^Hilb → Ê` being the field theory's `κ = toEHat ∘
  fromECheck` of `def:continuity`/`def:field-theory`.
* `pairing`/`inner_eq` — the GENUINE use of `hU`: `E_Σ^Hilb`'s inner product, restricted to
  `Ě_Σ`, IS the C1-fixed reflection-positivity pairing `B(x,y) = J(κ x) y` of `def:unitarity`.
  This makes `E_Σ^Hilb` the completion of the pre-Hilbert `(Ě_Σ, B)`. Because an inner product
  is positive-definite, `inner_eq` + `checkIncl_injective` FORCE `B` positive-definite — exactly
  hU's reflection-positivity. So a theory failing `hU` cannot have this structure: the capstone
  rests on REAL unitarity (the C1 fix paying off — the old vacuous `IsUnitary` would have made
  this hollow).
* `unitary`/`unitary_inner` — gh cobordisms between time-symmetric germs → UNITARY isomorphisms
  (a continuous linear equivalence PRESERVING the inner product; functor form + precise form).
* `unitary_check`/`unitary_hat` — the iso ALSO carries `Ě → Ě` and `Ê → Ê` (precise form's "also
  maps", encoded, not lost to the functor form).

THE PROOF-REASON (KSTeX 705–709), recorded as PROSE, NOT a Lean proof (no `sorry`, no faked
theorem): on a time-symmetric `Σ`, reflection-positivity (`def:unitarity`) makes `Ě_Σ`
pre-Hilbert, completing to `E_Σ^Hilb`. For a real-analytic gh cobordism `M : Σ_0 ⤳ Σ_1`: choose
a time-function foliating `M`, identify `M ≅ Σ_0 × [0,1]`; complexify `M` to `M_ℂ` (node 4);
a curve `f` with `Re f' > 0` gives a totally-real `M_f` carrying an allowable complex metric
(the higher-dimensional Wick rotation, node 3); Principle 5.1 (node 5, `IsInvariant`) gives the
unitary `Z_M`, as `Z_f` was used in the `d = 1` contour argument; its unitarity comes from
reflection-positivity. `Z_M` is independent of the curve and the time-function, both by
Principle 5.1. This is the deferred-additive proof; the theorem is STATED here.

DEFERRED (documented, not faked): (1) the object correspondence `WickObjectCorrespondence.cplx`
(Lorentzian germ → its complex object via the Wick rotation/boundary) is the
`C_d^{Lor,ω} → C_d^ℂ` correspondence node 1 records only at the tangent level
(`metric_on_shilov_boundary`), node 3 deferred for `EuclideanSpace`, node 5 deferred for
`CobordismRealization`; (2) the CONSTRUCTION of the Hilbert completion `E_Σ^Hilb` (Section 3
deferred it; here its existence + the inclusions + the inner product = `hU`'s pairing are STATED,
the construction inherits that deferral); (3) the PROOF (`hU` + Principle 5.1 ⟹ the structure),
scope (a).

CONSTRAINTS: no `axiom` keyword, no concrete instance, no `sorry` (the theorem is a structure +
a `Prop`; its proof is deferred-additive prose, never a `sorry`'d theorem). Reuses node 5's
`IsInvariant`, node 2's gh, Section 3's `IsUnitary` (C1-fixed) and `E`/`Ě`/`Ê`, with their real
signatures.

Blueprint: `thm:unitary-gh` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.InvariancePrinciple
import KontsevichSegal.WickRotation.GloballyHyperbolic
import KontsevichSegal.WickRotation.TimeSymmetricRotation
import KontsevichSegal.FieldTheory.Unitarity

namespace WickRotation

open Cobordism

universe u

/- Register Section 3's field-theory fibre data as global instances, so the limit spaces
`T.E`/`T.ECheck`/`T.EHat` carry their TVS structure in the field types below (additive; the
`FieldTheory` structure is unchanged — the same registration node 4 used for
`IsRealAnalytic.complexStructure`). -/
attribute [instance] FieldTheory.eFrechet FieldTheory.echeckFibres FieldTheory.ehatFibres

/-! ## Hilbert fibres -/

/-- A family of Hilbert spaces over an index type: each fibre is a complete complex inner
product space. Used for the `E_Σ^Hilb` of Theorem 5.2. -/
class HilbertFibres {B : Type*} (F : B → Type*) where
  [normedAddCommGroup : ∀ b, NormedAddCommGroup (F b)]
  [innerProductSpace : ∀ b, InnerProductSpace ℂ (F b)]
  [completeSpace : ∀ b, CompleteSpace (F b)]

attribute [instance] HilbertFibres.normedAddCommGroup HilbertFibres.innerProductSpace
  HilbertFibres.completeSpace

/-! ## The Lorentzian-germ → complex-object correspondence (assumed; deferred) -/

/-- **Assumed (KS Section 5 infrastructure): the object correspondence.** Sends a Lorentzian
germ `σ` (object of `C_d^{Lor,ω}`) to the complex object `cplx σ` of `C_d^ℂ` it Wick-rotates to
(node 3's Euclidean germ / the boundary relation). DEFERRED construction: the
`C_d^{Lor,ω} → C_d^ℂ` correspondence, which node 1 records only at the tangent level
(`metric_on_shilov_boundary`), node 3 deferred for `EuclideanSpace`, and node 5 deferred for
`CobordismRealization`. Assumed here as a global operation (a `class` field, never the `axiom`
keyword, no instance). -/
class WickObjectCorrespondence [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry] where
  /-- The complex object `C_d^ℂ` that a Lorentzian germ Wick-rotates to. -/
  cplx : gl.Obj → gc.Obj

/-- A **time-symmetric Lorentzian germ**: a germ `σ` whose complex object `cplx σ` is
time-symmetric in Section 3's sense (`IsTimeSymmetric`, i.e. `Σ ≅ Σ̄*`). These are the objects
Theorem 5.2 sends to Hilbert spaces. -/
def TimeSymmetricGerm [gc : CobordismGeometry] [dc : DualConjugateGeometry]
    [gl : LorentzianCobordismGeometry] [WickObjectCorrespondence] : Type _ :=
  {σ : gl.Obj // IsTimeSymmetric (WickObjectCorrespondence.cplx σ)}

/-! ## Theorem 5.2: the induced gh unitary functor (both forms) -/

/-- **Theorem 5.2's conclusion, both forms (KS Section 5, blueprint `thm:unitary-gh`).** The
witness data that a unitary QFT `T` (with reflection-positivity `hU` and Principle 5.1 `hI`)
induces on the gh category. Parametrized by `hU : IsUnitary T` (the C1-FIXED reflection-positivity
— the load-bearing hypothesis) and `hI : IsInvariant T` (Principle 5.1, node 5, the proof engine).

FUNCTOR FORM: `EHilb` assigns a Hilbert space to each time-symmetric germ; `unitary` assigns a
unitary isomorphism to each gh cobordism between time-symmetric germs.

PRECISE FORM: `checkIncl`/`hatIncl` give `Ě_Σ ⊂ E_Σ^Hilb ⊂ Ê_Σ` (injective dense, `factor`
making the composite the field theory's `κ = toEHat ∘ fromECheck`); `inner_eq` makes `E_Σ^Hilb`'s
inner product the C1-fixed reflection-positivity pairing of `hU`; `unitary_inner` makes the iso
preserve it (unitary); `unitary_check`/`unitary_hat` make the iso ALSO carry `Ě → Ě` and `Ê → Ê`.

Rests on REAL unitarity: `inner_eq` + `checkIncl_injective` force the pairing positive-definite
(an inner product is), which is exactly `hU`'s reflection-positivity — so a non-unitary `T`
cannot satisfy this. Not constructed for any concrete theory (the proof is deferred). -/
structure InducesUnitaryGH [gc : CobordismGeometry] [dc : DualConjugateGeometry]
    [gl : LorentzianCobordismGeometry] [HolomorphicComplexification] [lc : LightConeGeometry]
    [CobordismRealization] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (hU : IsUnitary T) (hI : IsInvariant T) where
  /-- `E_Σ^Hilb`: the Hilbert space of a time-symmetric germ (functor form). -/
  EHilb : TimeSymmetricGerm → Type u
  [hilbert : HilbertFibres EHilb]
  /-- The conjugate-dual identification `J : Ê_Σ ≃ (Ě_Σ)^{conj-dual}` of `hU` (per
  time-symmetric germ), giving the reflection-positivity pairing `B(x,y) = J(κ x) y`. -/
  pairing : ∀ σ : TimeSymmetricGerm,
    T.EHat (WOC.cplx σ.1) ≃L[ℂ] (T.ECheck (WOC.cplx σ.1) →SL[starRingEnd ℂ] ℂ)
  /-- The inclusion `Ě_Σ ⊂ E_Σ^Hilb` (`def:continuity`'s upstream map into the completion). -/
  checkIncl : ∀ σ : TimeSymmetricGerm, T.ECheck (WOC.cplx σ.1) →L[ℂ] EHilb σ
  /-- The inclusion `E_Σ^Hilb ⊂ Ê_Σ` (into the downstream limit). -/
  hatIncl : ∀ σ : TimeSymmetricGerm, EHilb σ →L[ℂ] T.EHat (WOC.cplx σ.1)
  /-- `Ě_Σ → E_Σ^Hilb` is injective. -/
  checkIncl_injective : ∀ σ, Function.Injective (checkIncl σ)
  /-- `Ě_Σ → E_Σ^Hilb` has dense range. -/
  checkIncl_dense : ∀ σ, DenseRange (checkIncl σ)
  /-- `E_Σ^Hilb → Ê_Σ` is injective. -/
  hatIncl_injective : ∀ σ, Function.Injective (hatIncl σ)
  /-- `E_Σ^Hilb → Ê_Σ` has dense range. -/
  hatIncl_dense : ∀ σ, DenseRange (hatIncl σ)
  /-- The composite `Ě_Σ → E_Σ^Hilb → Ê_Σ` is the field theory's canonical map
  `κ = toEHat ∘ fromECheck` (so `E_Σ^Hilb` sits on `κ`, between `Ě_Σ` and `Ê_Σ`). -/
  factor : ∀ σ : TimeSymmetricGerm,
    (hatIncl σ).comp (checkIncl σ)
      = (T.toEHat (WOC.cplx σ.1)).comp (T.fromECheck (WOC.cplx σ.1))
  /-- **The genuine use of `hU`:** `E_Σ^Hilb`'s inner product, restricted to `Ě_Σ` via
  `checkIncl`, IS the C1-fixed reflection-positivity pairing `B(x,y) = J(κ x) y` of `def:unitarity`.
  With `checkIncl_injective`, this forces `B` positive-definite (an inner product is), i.e. `hU`'s
  reflection-positivity — the capstone rests on real unitarity. -/
  inner_eq : ∀ (σ : TimeSymmetricGerm) (x y : T.ECheck (WOC.cplx σ.1)),
    @inner ℂ (EHilb σ) _ (checkIncl σ y) (checkIncl σ x)
      = pairing σ (T.toEHat (WOC.cplx σ.1) (T.fromECheck (WOC.cplx σ.1) x)) y
  /-- A real-analytic gh cobordism between time-symmetric germs induces a unitary ISOMORPHISM
  `E_{Σ_0}^Hilb → E_{Σ_1}^Hilb` (the iso is bijective — it IDENTIFIES the Hilbert spaces; per the
  node-5 lesson no distinctness field is added, which would contradict the identification). -/
  unitary : ∀ {σ0 σ1 : TimeSymmetricGerm} (M : gl.Mor σ0.1 σ1.1),
    IsGloballyHyperbolicOmega M → (EHilb σ0 ≃L[ℂ] EHilb σ1)
  /-- The induced iso is UNITARY: it preserves the inner product (the reflection-positivity
  pairing). (Equate-able: `⟪U x, U y⟫ = ⟪x, y⟫`, no distinguishing accessor needed.) -/
  unitary_inner : ∀ {σ0 σ1 : TimeSymmetricGerm} (M : gl.Mor σ0.1 σ1.1)
    (hM : IsGloballyHyperbolicOmega M) (x y : EHilb σ0),
    @inner ℂ (EHilb σ1) _ (unitary M hM x) (unitary M hM y) = @inner ℂ (EHilb σ0) _ x y
  /-- The iso ALSO carries `Ě_{Σ_0} → Ě_{Σ_1}`: it restricts, along the inclusions, to a map on
  the upstream limits (the field theory's `Z`-action on `Ě`). -/
  unitary_check : ∀ {σ0 σ1 : TimeSymmetricGerm} (M : gl.Mor σ0.1 σ1.1)
    (hM : IsGloballyHyperbolicOmega M),
    ∃ zc : T.ECheck (WOC.cplx σ0.1) →L[ℂ] T.ECheck (WOC.cplx σ1.1),
      ∀ x, (unitary M hM) (checkIncl σ0 x) = checkIncl σ1 (zc x)
  /-- The iso ALSO carries `Ê_{Σ_0} → Ê_{Σ_1}`: it descends, along the inclusions, to a map on
  the downstream limits. -/
  unitary_hat : ∀ {σ0 σ1 : TimeSymmetricGerm} (M : gl.Mor σ0.1 σ1.1)
    (hM : IsGloballyHyperbolicOmega M),
    ∃ zh : T.EHat (WOC.cplx σ0.1) →L[ℂ] T.EHat (WOC.cplx σ1.1),
      ∀ e, hatIncl σ1 ((unitary M hM) e) = zh (hatIncl σ0 e)

/-- **`pairing` is FORCED to be a genuine reflection-positivity pairing (no float-free join).**
For any `InducesUnitaryGH` witness `W`, the carried `W.pairing σ` satisfies — on the image of
`κ = toEHat ∘ fromECheck` — exactly the three conditions of `IsUnitary`'s C1-fixed
reflection-positivity (ii): hermitian, positive-semidefinite, and definite. So `pairing` is NOT a
free `≃L`: it is tied (via `inner_eq`) to `E_Σ^Hilb`'s genuine inner product, which is hermitian
and positive-definite, and `checkIncl_injective` upgrades semidefinite to definite. `IsUnitary`'s
`J` is existentially quantified (no nameable `hU.J` to tie to); this PROVES `pairing` matches what
that existential `J` guarantees, so a witness with an invalid (non-positive-definite) `pairing`
cannot exist. PROVED from `inner_conj_symm` / `inner_self_nonneg` / `inner_self_eq_zero`. -/
theorem InducesUnitaryGH.pairing_reflectionPositive [gc : CobordismGeometry]
    [dc : DualConjugateGeometry] [gl : LorentzianCobordismGeometry] [HolomorphicComplexification]
    [lc : LightConeGeometry] [CobordismRealization] [WOC : WickObjectCorrespondence]
    {T : FieldTheory} {hU : IsUnitary T} {hI : IsInvariant T}
    (W : InducesUnitaryGH T hU hI) (σ : TimeSymmetricGerm) :
    (∀ (x y : T.ECheck (WOC.cplx σ.1)),
        (starRingEnd ℂ)
            (W.pairing σ (T.toEHat (WOC.cplx σ.1) (T.fromECheck (WOC.cplx σ.1) y)) x)
          = W.pairing σ (T.toEHat (WOC.cplx σ.1) (T.fromECheck (WOC.cplx σ.1) x)) y) ∧
    (∀ (x : T.ECheck (WOC.cplx σ.1)),
        0 ≤ (W.pairing σ (T.toEHat (WOC.cplx σ.1) (T.fromECheck (WOC.cplx σ.1) x)) x).re) ∧
    (∀ (x : T.ECheck (WOC.cplx σ.1)),
        W.pairing σ (T.toEHat (WOC.cplx σ.1) (T.fromECheck (WOC.cplx σ.1) x)) x = 0 → x = 0) := by
  letI := W.hilbert
  refine ⟨fun x y => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [← W.inner_eq σ y x, ← W.inner_eq σ x y]
    exact inner_conj_symm (𝕜 := ℂ) (W.checkIncl σ y) (W.checkIncl σ x)
  · rw [← W.inner_eq σ x x]
    exact inner_self_nonneg (𝕜 := ℂ) (x := W.checkIncl σ x)
  · rw [← W.inner_eq σ x x] at hx
    have hcx : W.checkIncl σ x = 0 := inner_self_eq_zero.mp hx
    have hxeq : W.checkIncl σ x = W.checkIncl σ 0 := by rw [hcx, map_zero]
    exact W.checkIncl_injective σ hxeq

/- **Theorem 5.2** is the assertion that, for a unitary QFT `T` (with Principle 5.1), the
conclusion data `InducesUnitaryGH T hU hI` is INHABITED — for every `hU : IsUnitary T` (the
C1-fixed reflection-positivity) and `hI : IsInvariant T` (Principle 5.1, node 5). Like nodes 4–5's
assumed structures, that inhabitation is the deferred-additive proof (KSTeX 705–709, via the
complexification + Principle 5.1 + the `d = 1` contour argument, recorded as prose in the module
docstring), STATED here as the structure, never `sorry`'d. (A `def` of `Prop`
`∀ hU hI, Nonempty (InducesUnitaryGH T hU hI)` is not added: `InducesUnitaryGH` is universe-poly
in the Hilbert-space universe, which `Nonempty` would leave as an unbindable metavariable; the
structure parametrized by `hU` already states the implication — the conclusion holds OF a unitary
theory.) NON-VACUOUS: the structure references the ACTUAL C1-fixed `IsUnitary` (via `hU`) and, via
`inner_eq` + `checkIncl_injective`, encodes reflection-positivity, so a non-unitary theory cannot
inhabit it — `hU` is a real hypothesis, not baked in. -/

end WickRotation
