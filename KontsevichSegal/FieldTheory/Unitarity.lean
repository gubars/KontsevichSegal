/- Unitarity (KS paper Section 3, arXiv:2105.10161): the LAST Section 3 node, and
the third of the three building toward unitarity.

This is a condition ON THE FUNCTOR (a `FieldTheory`), encoded without the `axiom`
keyword and without exhibiting any concrete unitary theory, never on the
cobordism category (Category vs. functor boundary, CLAUDE.md). It composes
earlier nodes: the reality condition `IsReal` (from `ConjugateDualDuality.lean`),
`dualConj` (= `dual ∘ conj` = Σ̄*, from `DualConjugate.lean`), the
germ-isomorphism groupoid `GermIsoGeometry` (from `IsomorphismAction.lean`), and
the real `T.ECheck`.

Contents:

* TIME-SYMMETRIC germ (`IsTimeSymmetric`): `Σ ≅ Σ̄*`, encoded as
  `Nonempty (GermIsoGeometry.Iso o (dualConj o))` — the paper's displayed
  condition `Σ ≅ Σ̄*` (KSTeX 480 and 494) exactly, with the germ isomorphism
  drawn from the assumed groupoid `GermIsoGeometry`
  (`FieldTheory/IsomorphismAction.lean`). This is WEAKER than the paper's
  reflection gloss (KSTeX 480): that reflection is an involution with
  fixed-point set `Σ` that reverses the co-orientation and conjugates the
  metric; its involutivity and fixed-point-set content are NOT captured and
  remain deferred inside the assumed `GermIsoGeometry`. The node stays
  `\notready` because the predicate rests on the undischarged `GermIsoGeometry`
  (no instance).

* UNITARITY (`IsUnitary`): a field theory is unitary if it satisfies
  (i) the reality condition (5) (`IsReal`, reused), and
  (ii) reflection-positivity: for every time-symmetric object, the hermitian
  duality between `Ě_Σ` and `Ě_{Σ̄}` is positive-definite. This is encoded on the
  ACTUAL functor-induced pairing, not as the existence of some free inner product
  (which would be vacuous: every complex vector space admits a positive-definite
  hermitian form, e.g. via a Hamel basis). For a time-symmetric `o` the conjugate
  dual of `Ě_Σ` is `Ê_{Σ̄*}` (`ConjugateDualIdentification`, since the theory is
  real by (i)), identified with `Ê_Σ` across `Σ ≅ Σ̄*` in prose only (no germ-iso
  action on `Ê` is encoded); with the functor's own canonical map
  `κ = T.toEHat o ∘ T.fromECheck o` (`Ě_Σ → Ê_Σ`) and an identification
  `J : Ê_Σ ≃L (Ě_Σ)^{conj-dual}`, the pairing `B(x, y) = J (κ x) y` on `Ě_Σ`
  (linear in `x`, antilinear in `y`) is required to be hermitian and
  positive-definite. This genuinely constrains the functor: if `κ` is degenerate
  the form fails definiteness, so a real theory can fail (ii) (non-vacuous).

* HILBERT COMPLETION (consequence): the positive-definite form `B` of (ii) makes
  `Ě_Σ` a pre-Hilbert space, completing to a Hilbert space `E^Hilb_Σ` with
  `Ě_Σ → E^Hilb_Σ → Ê_Σ`. That positive-definite hermitian form `B` is the statable
  heart. The completion construction and the maps are DEFERRED: the inner-product
  norm topology differs from `Ě_Σ`'s nuclear topology, and the map
  `E^Hilb_Σ → Ê_Σ` needs the limit relation; Mathlib has `UniformSpace.Completion`
  and inner-product completions, but tying `E^Hilb_Σ` to `Ě_Σ`'s existing
  structure and to `Ê_Σ` is not faked here.

* SECTION 2 CONNECTION (prose citation, not a term-level Lean tie). The metric of
  a time-symmetric germ is real and Riemannian on `Σ`, and by Section 2's
  `lorentzian_on_boundary` and `only_lorentzian_on_boundary` the nondegenerate
  real metrics on the Shilov boundary of `Q_ℂ(V)` are exactly the Lorentzian ones
  (`IsLorentzian`). The time-symmetric hypersurfaces on which a unitary theory
  acquires Hilbert spaces are the functorial counterpart of those boundary
  Lorentzian metrics. No genuine term-level dependency is expressible here (the
  germ's real-Riemannian metric structure is not formalized), so this is a
  faithful prose connection, matching the blueprint's `\uses` of
  `prop:lorentzian-boundary` / `prop:only-lorentzian`; no false Lean dependency is
  manufactured.

Blueprint: `def:unitarity` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.FieldTheory.ConjugateDualDuality
import KontsevichSegal.FieldTheory.IsomorphismAction
import Mathlib.Analysis.InnerProductSpace.Basic

open Cobordism

/-! ## Time-symmetric germs -/

/-- **A time-symmetric germ** (KS Section 3, blueprint `def:unitarity`):
`Σ ≅ Σ̄*`, encoded as `Nonempty (GermIsoGeometry.Iso o (dualConj o))` — the
paper's displayed condition `Σ ≅ Σ̄*` (KSTeX 480 and 494) exactly.

This is WEAKER than the paper's reflection gloss (KSTeX 480): that reflection is
an involution with fixed-point set `Σ` that reverses the co-orientation and
conjugates the metric; its involutivity and fixed-point-set content are NOT
captured and remain deferred inside the assumed `GermIsoGeometry`.

The node stays `\notready` because the predicate rests on the undischarged
`GermIsoGeometry` (no instance). -/
def IsTimeSymmetric [g : CobordismGeometry] [gi : GermIsoGeometry]
    [d : DualConjugateGeometry] (o : g.Obj) : Prop :=
  Nonempty (GermIsoGeometry.Iso o (dualConj o))

/-! ## Unitarity -/

/-- **A unitary field theory** (KS Section 3, blueprint `def:unitarity`). A
condition ON the functor `T`, requiring two things:

* (i) the reality condition (5), `IsReal T` (reused from
  `ConjugateDualDuality.lean`);
* (ii) reflection-positivity: for every time-symmetric object `o`, the hermitian
  duality between `Ě_Σ` and `Ě_{Σ̄}` is positive-definite.

Condition (ii) is stated on the ACTUAL functor-induced pairing, not as the mere
existence of some inner product. For a time-symmetric `o` the conjugate dual of
`Ě_Σ` is `Ê_{Σ̄*}` (the `ConjugateDualIdentification` of
`ConjugateDualDuality.lean`, available because the theory is real by (i)),
identified with `Ê_Σ` across `Σ ≅ Σ̄*` in prose only (no germ-iso action on `Ê`
is encoded), so an
identification `J : Ê_Σ ≃L (Ě_Σ)^{conj-dual}` together with the functor's OWN
canonical map `κ = T.toEHat o ∘ T.fromECheck o : Ě_Σ → Ê_Σ` induces the hermitian
duality pairing `B(x, y) = J (κ x) y` on `Ě_Σ` (linear in `x`, antilinear in
`y`). Reflection-positivity (ii) requires `B` to be hermitian
(`conj (B y x) = B x y`) and positive-definite (`0 ≤ re (B x x)`, and
`B x x = 0 → x = 0`).

NON-VACUOUS: `B` is built from the theory's own maps `T.toEHat` / `T.fromECheck`,
so (ii) cannot be met by an unrelated free form. If the canonical map `κ` is
degenerate (e.g. `T.fromECheck o` is not injective) then `B x x = 0` for some
`x ≠ 0`, so no `J` makes `B` definite and the theory fails (ii). (The previous
`Nonempty (InnerProductSpace.Core ℂ (T.ECheck o))` encoding was vacuous: every
complex vector space admits some positive-definite hermitian form, e.g. via a
Hamel basis, so existence of one constrained nothing.) The identification `J` is
existential, matching the `Nonempty` status of `ConjugateDualIdentification`.

M4 note (executed): `IsTimeSymmetric o` is now
`Nonempty (GermIsoGeometry.Iso o (dualConj o))`, the paper's `Σ ≅ Σ̄*`; the
former equality stand-in `o = dualConj o` is gone. Two deferrals remain:
(1) `IsReal`'s naturality and involution law — `IsReal` is an existential `Prop`
that cannot state them; data-fying it is a separate interface split.
(2) the `E^Hilb` completion tie — it needs a nameable inner product living
inside the `∃ J` existential, and `found:tvs-limits-tensor`.

The Hilbert completion `Ě_Σ → E^Hilb_Σ → Ê_Σ` induced by `B` is the consequence;
the completion construction and the maps are deferred (see the module comment).
Not instantiated for any concrete theory. -/
def IsUnitary [g : CobordismGeometry] [gi : GermIsoGeometry]
    [d : DualConjugateGeometry] (T : FieldTheory) : Prop :=
  letI := T.eFrechet
  letI := T.echeckFibres
  letI := T.ehatFibres
  IsReal T ∧
    ∀ o, IsTimeSymmetric o →
      ∃ J : T.EHat o ≃L[ℂ] (T.ECheck o →SL[starRingEnd ℂ] ℂ),
        (∀ (x y : T.ECheck o),
            (starRingEnd ℂ) (J (T.toEHat o (T.fromECheck o y)) x)
              = J (T.toEHat o (T.fromECheck o x)) y) ∧
        (∀ (x : T.ECheck o), 0 ≤ (J (T.toEHat o (T.fromECheck o x)) x).re) ∧
        (∀ (x : T.ECheck o), J (T.toEHat o (T.fromECheck o x)) x = 0 → x = 0)
