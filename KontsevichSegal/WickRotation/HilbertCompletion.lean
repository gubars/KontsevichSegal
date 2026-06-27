/- The Hilbert completion of a pre-Hilbert space: the buildable content of the foundation node
`found:hilbert-completion` of the Kontsevich-Segal blueprint (arXiv:2105.10161).

KS Section 5 (KSTeX 498, Theorem 5.2): "when we have a time-symmetric germ `Σ` we can complete the
pre-Hilbert space `Ě_Σ` to obtain a Hilbert space `E^Hilb_Σ`", sitting in the rigged triple
`Ě_Σ ⊂ E^Hilb_Σ ⊂ Ê_Σ` by injective dense maps whose composite is the field-theory map `κ`. The
reflection-positivity pairing of `def:unitarity` makes `Ě_Σ` a genuine (positive-DEFINITE) inner
product space, so `E^Hilb_Σ` is its plain metric/uniform completion -- no null-space quotient.

This file BUILDS the part of the foundation that is pure Mathlib: the completion of a pre-Hilbert
space to a Hilbert space, with the dense injective embedding and the inner-product extension. As the
blueprint node records, "Mathlib has Hilbert completion of an inner-product space; what is missing is
the wiring to the deferred limit spaces `Ě`, `Ê`" -- that wiring (the downstream `E^Hilb → Ê` and the
`κ`-factorisation) needs the topological-vector-space inverse/direct limits of
`found:tvs-limits-tensor`, and stays deferred (the node keeps its `\uses{found:tvs-limits-tensor}`
edge). So this foundation is built scaffold-green: the completion machinery is real, the rigged-triple
wiring to the abstract `Ě = T.ECheck` / `Ê = T.EHat` is not.

The Mathlib backing (`Mathlib.Analysis.InnerProductSpace.Completion`,
`Mathlib.Analysis.Normed.Module.Completion`):

* `UniformSpace.Completion.innerProductSpace : InnerProductSpace ℂ (Completion E)` and
  `UniformSpace.Completion.completeSpace : CompleteSpace (Completion E)` -- the completion is a
  Hilbert space;
* `UniformSpace.Completion.toComplL : E →L[ℂ] Completion E` -- the embedding (a continuous linear
  isometry, `coe_toComplL` ties it to the canonical completion coercion);
* `UniformSpace.Completion.coe_injective` / `denseRange_coe` -- injective with dense range;
* `UniformSpace.Completion.inner_coe : ⟪↑a, ↑b⟫ = ⟪a, b⟫` -- the inner product on the completion
  EXTENDS the original (the float-free tie).

The assumed `HilbertFibres` of `UnitaryGH.lean` asserts each fibre is
`NormedAddCommGroup + InnerProductSpace ℂ + CompleteSpace`; `hilbertCompletion` proves EXACTLY these
three for the completion `Hilb`, so the assumed fibre-class is realised fibrewise by completions.

No `axiom` keyword, no `sorry`. -/

import KontsevichSegal.Basic
import Mathlib.Analysis.InnerProductSpace.Completion

namespace WickRotation

universe u

/-! ## The Hilbert-completion interface -/

/-- **The Hilbert completion of a pre-Hilbert space.** For a (positive-definite) complex inner
product space `E` (the `Ě_Σ` of the rigged triple), the datum of its completion to a Hilbert space:
a Hilbert space `Hilb` (`= E^Hilb_Σ`), a dense injective embedding `incl : E ↪ Hilb`, and the
inner-product extension `⟪incl x, incl y⟫ = ⟪x, y⟫`. This is the buildable abstraction underlying
`found:hilbert-completion`; the downstream inclusion `Hilb ↪ Ê_Σ` and the `κ`-factorisation are the
deferred half (`found:tvs-limits-tensor`). Realised by `hilbertCompletion`. -/
structure HilbertCompletion (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The Hilbert space `E^Hilb_Σ`: the completion of the pre-Hilbert `E`. -/
  Hilb : Type u
  [normedAddCommGroup : NormedAddCommGroup Hilb]
  [innerProductSpace : InnerProductSpace ℂ Hilb]
  [completeSpace : CompleteSpace Hilb]
  /-- The dense inclusion `Ě_Σ ⊂ E^Hilb_Σ` (a continuous linear map). -/
  incl : E →L[ℂ] Hilb
  /-- `Ě_Σ → E^Hilb_Σ` is injective. -/
  incl_injective : Function.Injective incl
  /-- `Ě_Σ → E^Hilb_Σ` has dense range (`E^Hilb_Σ` is the completion, not anything larger). -/
  incl_dense : DenseRange incl
  /-- **Float-free extension tie:** the inner product on `E^Hilb_Σ`, restricted to `Ě_Σ` via `incl`,
  IS the inner product of `Ě_Σ`. No floating second inner product. -/
  inner_eq : ∀ x y : E, inner ℂ (incl x) (incl y) = inner ℂ x y

attribute [instance] HilbertCompletion.normedAddCommGroup HilbertCompletion.innerProductSpace
  HilbertCompletion.completeSpace

/-! ## The Mathlib model -/

/-- **The model: `UniformSpace.Completion` realises `HilbertCompletion`.** The completion of a
complex inner product space `E` is a Hilbert space, with the canonical embedding
`UniformSpace.Completion.toComplL` as the dense injective inclusion and
`UniformSpace.Completion.inner_coe` as the inner-product extension. Every field is proved from
standard Mathlib; no `axiom`, no `sorry`. -/
noncomputable def hilbertCompletion (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    HilbertCompletion E where
  Hilb := UniformSpace.Completion E
  normedAddCommGroup := inferInstance
  innerProductSpace := inferInstance
  completeSpace := inferInstance
  incl := UniformSpace.Completion.toComplL
  incl_injective := by
    rw [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.coe_injective E
  incl_dense := by
    rw [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.denseRange_coe
  inner_eq x y := by
    simp only [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.inner_coe x y

/-- The model's embedding is the canonical completion map `toComplL` (so it does not float; via
`UniformSpace.Completion.coe_toComplL` its underlying function is the completion coercion). -/
@[simp] lemma hilbertCompletion_incl (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (hilbertCompletion E).incl = UniformSpace.Completion.toComplL := rfl

end WickRotation
