/- The conjugate-dual duality (KS paper Section 3, Appendix; arXiv:2105.10161):
the second of three nodes building toward unitarity.

This is the Section 3 APPENDIX result. Under deliverable scope (a) (state, do not
prove), we STATE the duality; the appendix proof is not formalized (so no `sorry`
is needed — these are assumed-result statements, stated as "an iso exists", like
`DualRelation` in `DualConjugate.lean`).

The critical structure, preserved exactly as the blueprint separates it:

* UNCONDITIONAL (no further hypothesis): the plain duality `(Ě_Σ)* ≅ Ê_{Σ*}`
  (`PlainDuality`), the appendix result, holding for ANY field theory. Its
  companion `(Ê_Σ)* ≅ Ě_{Σ*}` is exactly `DualRelation` from the previous node
  (`def:dual-conjugate-functors`); the two forms are related not by a trivial
  swap of `Σ` and `Σ*` but by dualizing and invoking the reflexivity of the
  nuclear Fréchet space `Ê_Σ` (`NuclearFrechetDuality.reflexive`). We keep the two
  coherent and do not duplicate `DualRelation`.

* THE REALITY CONDITION (5) (`IsReal`): a SEPARATE hypothesis on the field
  theory, a natural antilinear involution `E_{Σ̄} ≅ Ē_Σ`. It is NOT part of the
  plain duality.

* CONDITIONAL on (5) (`ConjugateDualIdentification`): only for a theory
  satisfying (5) does the conjugate dual of `Ě_Σ` equal `Ê_{Σ̄*}`. The dependency
  on (5) is visible in the type (the statement takes an `IsReal T` hypothesis);
  it does NOT hold without (5).

All of these are conditions/results ON THE FUNCTOR (a `FieldTheory`), never on the
cobordism category (Category vs. functor boundary, CLAUDE.md).

Mathlib provides the antilinear maps used: `E ≃SL[starRingEnd ℂ] F` (a
conjugate-linear continuous equivalence, notation `E ≃L⋆[ℂ] F`) and
`E →SL[starRingEnd ℂ] ℂ` (the conjugate dual, antilinear continuous functionals,
`E →L⋆[ℂ] ℂ`). The complex-conjugate space `Ē_Σ` is not formed directly; the
reality condition is stated via a conjugate-linear equivalence `E_{conj Σ} ≃ E_Σ`,
the faithful equivalent form.

Blueprint: `def:conjugate-dual-duality` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.FieldTheory.DualConjugate
import Mathlib.Analysis.InnerProductSpace.Basic

open Cobordism

/-! ## The plain duality (unconditional, appendix result) -/

/-- **The plain duality** (KS Section 3 Appendix, blueprint
`def:conjugate-dual-duality`): for any field theory `T`, with NO further
hypothesis, the strong dual of `Ě_Σ` is `Ê_{Σ*}`,
\[ (\check E_{\Sigma})^* \;\cong\; \hat E_{\Sigma^*}. \]
Stated (scope (a)) as the existence of a continuous linear equivalence; the
appendix proof is not formalized.

The companion form `(Ê_Σ)* ≅ Ě_{Σ*}` is exactly `DualRelation` from the previous
node (`def:dual-conjugate-functors`). Passing between this form and the companion
is not a trivial swap of `Σ` and `Σ*`: it dualizes and invokes the reflexivity of
the nuclear Fréchet space `Ê_Σ` (`NuclearFrechetDuality.reflexive`). This `def`
states the `(Ě_Σ)* ≅ Ê_{Σ*}` direction as the appendix result, kept coherent with
`DualRelation`, not duplicating it. Condition on the functor `T`. -/
def PlainDuality [g : CobordismGeometry] [d : DualConjugateGeometry] (T : FieldTheory) :
    Prop :=
  letI := T.echeckFibres
  letI := T.ehatFibres
  ∀ o, Nonempty (StrongDual ℂ (T.ECheck o) ≃L[ℂ] T.EHat (DualConjugateGeometry.dual o))

/-! ## The reality condition (5) -/

/-- **The reality condition (5)** (KS Section 3, blueprint
`def:conjugate-dual-duality`): a SEPARATE hypothesis on a field theory `T`, a
natural antilinear involution
\[ E_{\bar\Sigma} \;\cong\; \overline{E_{\Sigma}}. \tag{5} \]
The complex-conjugate space `Ē_Σ` is not formed directly; this is stated in the
faithful equivalent form, a conjugate-linear (`starRingEnd ℂ`-semilinear)
continuous equivalence `E_{conj Σ} ≃ E_Σ`.

This is an ADDITIONAL hypothesis, not part of the plain duality. Condition on the
functor `T`. -/
def IsReal [g : CobordismGeometry] [d : DualConjugateGeometry] (T : FieldTheory) : Prop :=
  letI := T.eFrechet
  ∀ o, Nonempty (T.E (DualConjugateGeometry.conj o) ≃SL[starRingEnd ℂ] T.E o)

/-! ## The conjugate-dual identification (conditional on (5)) -/

/-- **The conjugate-dual identification** (KS Section 3, blueprint
`def:conjugate-dual-duality`): ONLY for a field theory satisfying the reality
condition (5), the conjugate dual of `Ě_Σ` is `Ê_{Σ̄*}`,
\[ (\check E_{\Sigma})^{\overline{*}} \;\cong\; \hat E_{\bar\Sigma^*}. \]
The conjugate dual is the space `Ě_Σ →L⋆[ℂ] ℂ` of antilinear continuous
functionals; `Ê_{Σ̄*}` is `T.EHat (dualConj o)` (`dualConj = dual ∘ conj`).

The dependency on (5) is explicit: the statement takes an `IsReal T` hypothesis,
so it cannot even be formed for a theory not known to satisfy (5). This step
combines the plain duality with the reality involution (5); unlike the plain
duality, it does NOT hold without (5). Stated (scope (a)) as the existence of a
continuous linear equivalence; the appendix proof is not formalized. Condition on
the functor `T`. -/
def ConjugateDualIdentification [g : CobordismGeometry] [d : DualConjugateGeometry]
    (T : FieldTheory) (_hReal : IsReal T) : Prop :=
  letI := T.echeckFibres
  letI := T.ehatFibres
  ∀ o, Nonempty ((T.ECheck o →SL[starRingEnd ℂ] ℂ) ≃L[ℂ] T.EHat (dualConj o))
