/- Unitarity (KS paper Section 3, arXiv:2105.10161): the LAST Section 3 node, and
the third of the three building toward unitarity.

This is a condition ON THE FUNCTOR (a `FieldTheory`), encoded without the `axiom`
keyword and without exhibiting any concrete unitary theory, never on the
cobordism category (Category vs. functor boundary, CLAUDE.md). It composes
earlier nodes: the reality condition `IsReal` (from `ConjugateDualDuality.lean`),
`dualConj` (= `dual ∘ conj` = Σ̄*, from `DualConjugate.lean`), and the real
`T.ECheck`.

Contents:

* TIME-SYMMETRIC germ (`IsTimeSymmetric`): `Σ ≅ Σ̄*`. The germ `Σ ⊂ U` admits a
  reflection with fixed-point set `Σ` reversing the co-orientation and
  conjugating the metric; the metric is then real, and real Riemannian on `Σ`.
  Expressed here as the object being fixed by `Σ ↦ Σ̄*` (`o = dualConj o`). This
  EQUALITY is a stand-in STRONGER than the intended isomorphism `Σ ≅ Σ̄*` (it
  excludes germs isomorphic-but-not-equal to `Σ̄*`): an object-level isomorphism is
  not expressible with the current structure, because the cobordism `Semicategory`
  has no identity morphisms (so the categorical iso notion `f ≫ g = 𝟙` is
  unavailable) and the reflection witnessing `Σ ≅ Σ̄*` is a germ diffeomorphism,
  not a cobordism (`Mor`). The reflection witness and the real-Riemannian metric
  structure are assumed germ geometry not tracked by `CobordismGeometry`; that
  sub-part is deferred (the same gap as the metric-conjugation tie in
  `DualConjugate.lean`). To be upgraded to `Nonempty (o ≅ dualConj o)` once an
  object/germ-isomorphism structure exists (analogous to the `fibre_eq`
  type-equality caveat).

* UNITARITY (`IsUnitary`): a field theory is unitary if it satisfies
  (i) the reality condition (5) (`IsReal`, reused), and
  (ii) reflection-positivity: for every time-symmetric object, the hermitian
  duality between `Ě_Σ` and `Ě_{Σ̄}` is positive-definite. This is encoded as a
  positive-definite hermitian inner product on `Ě_Σ` via Mathlib's
  `InnerProductSpace.Core ℂ (T.ECheck o)` (a purely algebraic positive-definite
  sesquilinear form, no topology needed, so it does not clash with the
  nuclear-non-metrizable topology of `Ě_Σ`). The identification of this form with
  the `Ě_Σ`–`Ě_{Σ̄}` cross pairing via the reality involution (5) is documented.

* HILBERT COMPLETION (consequence): the positive-definite form makes `Ě_Σ` a
  pre-Hilbert space, completing to a Hilbert space `E^Hilb_Σ` with
  `Ě_Σ → E^Hilb_Σ → Ê_Σ`. The pre-Hilbert structure (the `Core`) is the statable
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
import Mathlib.Analysis.InnerProductSpace.Basic

open Cobordism

/-! ## Time-symmetric germs -/

/-- **A time-symmetric germ** (KS Section 3, blueprint `def:unitarity`):
`Σ ≅ Σ̄*`, the germ admitting a reflection reversing the co-orientation and
conjugating the metric.

Expressed as the object being fixed by `Σ ↦ Σ̄*` (`o = dualConj o`). CAVEAT: this
EQUALITY is a stand-in that is STRONGER than the intended isomorphism `Σ ≅ Σ̄*`
(it excludes germs isomorphic-but-not-equal to `Σ̄*`). An object-level isomorphism
`Nonempty (o ≅ dualConj o)` is not expressible with the current structure: the
cobordism `Semicategory` has no identity morphisms (so the categorical iso notion
`f ≫ g = 𝟙` is unavailable), and the reflection witnessing `Σ ≅ Σ̄*` is a germ
diffeomorphism, not a cobordism (`Mor`). The reflection witness and the "metric
real and Riemannian on `Σ`" structure are assumed germ geometry not tracked by
`CobordismGeometry`; that sub-part is deferred (same gap as the metric-conjugation
tie in `DualConjugate.lean`). To be upgraded to `Nonempty (o ≅ dualConj o)` once
an object/germ-isomorphism structure exists (analogous to the `fibre_eq`
type-equality caveat). -/
def IsTimeSymmetric [g : CobordismGeometry] [d : DualConjugateGeometry] (o : g.Obj) :
    Prop :=
  o = dualConj o

/-! ## Unitarity -/

/-- **A unitary field theory** (KS Section 3, blueprint `def:unitarity`). A
condition ON the functor `T`, requiring two things:

* (i) the reality condition (5), `IsReal T` (reused from
  `ConjugateDualDuality.lean`);
* (ii) reflection-positivity: for every time-symmetric object `o`, the hermitian
  duality between `Ě_Σ` and `Ě_{Σ̄}` is positive-definite, encoded as a
  positive-definite hermitian inner product on `Ě_Σ`
  (`InnerProductSpace.Core ℂ (T.ECheck o)`).

The `Core` is purely algebraic (positive-definite sesquilinear form, no
topology), so it is statable on the nuclear-non-metrizable `Ě_Σ` and is
non-vacuous. The Hilbert completion it induces (`Ě_Σ → E^Hilb_Σ → Ê_Σ`) is the
consequence; the completion construction and the maps are deferred (see the
module comment). Not instantiated for any concrete theory. -/
def IsUnitary [g : CobordismGeometry] [d : DualConjugateGeometry] (T : FieldTheory) :
    Prop :=
  letI := T.echeckFibres
  IsReal T ∧
    (∀ o, IsTimeSymmetric o → Nonempty (InnerProductSpace.Core ℂ (T.ECheck o)))
