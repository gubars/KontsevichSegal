/- Scaffolding for the Hodge star operator (FOUND:HODGE-STAR — scaffolding-only
increment; the operator ⋆ itself, `star_wedge`, `star_star`, Definition 2.1, and the
equivalence with Theorem 2.2 are deferred to a later increment).

Mathlib ships no Hodge star, no induced form on exterior powers, and no block-level
graded commutativity. This file builds the reusable (P) foundation that the Hodge star
will sit on:

* `inducedForm` — the induced bilinear form `g_p` on the `p`-th exterior power `⋀ᵖW`
  of a nondegenerate bilinear form `B` on a finite-dimensional vector space `W` over a
  field. On decomposables it is the Gram determinant `det (B (vᵢ) (wⱼ))`
  (`inducedForm_apply_ιMulti`), the classical induced metric. This is the `g_p` of
  KS paper Definition 2.1 (the positive-definiteness of `Re(α ∧ ⋆α)` builds on it).

* the complexification `Vc V = ℂ ⊗[ℝ] V` and the ℂ-bilinear extension `gc` of an
  `AllowableComplexMetric` `g` (KS paper Section 2): the carrier on which `⋆` will live,
  since `⋆α` is a complex (d−p)-form when the metric is ℂ-valued.

Construction strategy (advisor three-strategy technique): the induced form is built by
route B (coordinate-free composite) using Mathlib's `exteriorPower.pairingDual` and the
metric isomorphism `LinearMap.BilinForm.toDual`, so `g_p` is canonical (basis-free) and
its decomposable value is a determinant by construction.
-/

import KontsevichSegal.ComplexMetrics.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace KontsevichSegal.Hodge

open exteriorPower LinearMap
open scoped TensorProduct

section Generic

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- The induced bilinear form `g_p` on the `p`-th exterior power `⋀ᵖW` of a nondegenerate
bilinear form `B` on `W`.

Built canonically (route B) as the composite
`⋀ᵖW --⋀ᵖ(B♭)--> ⋀ᵖ(W*) --pairingDual--> (⋀ᵖW)*`, where `B♭ = B.toDual hB : W ≃ W*` is
the metric isomorphism. On decomposables it equals the Gram determinant
`det (B (vᵢ) (wⱼ))` (see `inducedForm_apply_ιMulti`), the classical induced metric on
exterior powers used in KS paper Definition 2.1. -/
noncomputable def inducedForm (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate) (p : ℕ) :
    LinearMap.BilinForm K (⋀[K]^p W) :=
  (exteriorPower.pairingDual K W p).comp (exteriorPower.map p (B.toDual hB).toLinearMap)

/-- **The Gram-determinant formula (float-free tie of `g_p` to `B`).** On decomposable
`p`-vectors, the induced form is the determinant of the matrix of pairwise `B`-values.
This pins `inducedForm` to `B` on the nose. -/
theorem inducedForm_apply_ιMulti (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (p : ℕ) (v w : Fin p → W) :
    inducedForm B hB p (ιMulti K p v) (ιMulti K p w)
      = (Matrix.of fun i j => B (v j) (w i)).det := by
  rw [inducedForm, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  -- the two matrices are equal: entry `((B♭) (v j)) (w i) = B (v j) (w i)` by `toDual_def` (`rfl`)
  congr 1

/-- `exteriorPower.pairingDual` is injective over a field for a finite-dimensional module: it
carries the basis `(b*)^{∧p}` of `⋀ᵖ(W*)` to the dual basis of `⋀ᵖW`. Mathlib constructs the
pairing but does not record its bijectivity, which the induced-form nondegeneracy needs. -/
theorem pairingDual_injective (p : ℕ) :
    Function.Injective (exteriorPower.pairingDual K W p) := by
  classical
  set b := Module.finBasis K W with hb
  have key : exteriorPower.pairingDual K W p
      = ((b.dualBasis.exteriorPower p).equiv ((b.exteriorPower p).dualBasis)
          (Equiv.refl _)).toLinearMap := by
    refine (b.dualBasis.exteriorPower p).ext (fun s => ?_)
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, coe_basis,
      Module.Basis.coe_dualBasis, Module.Basis.coe_dualBasis]
    exact (basis_coord K p b s).symm
  rw [key]
  exact LinearEquiv.injective _

/-- **`g_p` is nondegenerate (from `B` nondegenerate).** The induced form on `⋀ᵖW` of a
nondegenerate symmetric `B` is again nondegenerate: it is the composite of the isomorphism
`⋀ᵖ(B♭)` (from `B`'s metric isomorphism `B♭ : W ≃ W*`) and the injective `pairingDual`. -/
theorem inducedForm_nondegenerate (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (p : ℕ) : (inducedForm B hB p).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  change Function.Injective
    (⇑((exteriorPower.pairingDual K W p).comp (exteriorPower.map p (B.toDual hB).toLinearMap)))
  rw [LinearMap.coe_comp]
  exact (pairingDual_injective p).comp
    (exteriorPower.map_injective_field (B.toDual hB).injective)

/-! ### The wedge pairing `∧ᵖ × ∧^q → ∧^{p+q}`

The graded multiplication of the exterior algebra restricts to homogeneous pieces. The
pairing `∧ᵖ × ∧^{d−p} → ∧ᵈ` underlying the Hodge star (KS paper Definition 2.1, the form
`α ↦ α ∧ ⋆α`) is the case `q = d − p`. -/

/-- The wedge product `∧ᵖW × ∧^qW → ∧^{p+q}W`, the graded multiplication of the exterior
algebra restricted to homogeneous pieces (`⋀[K]^i W` is a submodule of `ExteriorAlgebra K W`,
and the product of degree-`p` and degree-`q` elements has degree `p + q`). -/
noncomputable def wedge (p q : ℕ) :
    (⋀[K]^p W) →ₗ[K] (⋀[K]^q W) →ₗ[K] (⋀[K]^(p + q) W) :=
  LinearMap.mk₂ K
    (fun x y => ⟨(x : ExteriorAlgebra K W) * (y : ExteriorAlgebra K W),
      SetLike.mul_mem_graded x.2 y.2⟩)
    (fun x₁ x₂ y => by ext1; simp [add_mul])
    (fun c x y => by ext1; simp)
    (fun x y₁ y₂ => by ext1; simp [mul_add])
    (fun c x y => by ext1; simp)

omit [FiniteDimensional K W] in
@[simp]
lemma wedge_coe (p q : ℕ) (x : ⋀[K]^p W) (y : ⋀[K]^q W) :
    ((wedge p q x y : ⋀[K]^(p + q) W) : ExteriorAlgebra K W)
      = (x : ExteriorAlgebra K W) * (y : ExteriorAlgebra K W) :=
  rfl

end Generic

/-! ## The complexification `V_ℂ` and the ℂ-bilinear extension `g_ℂ`

KS state Definition 2.1 with the metric as a ℂ-valued quadratic form on the REAL space
`V`, and the Hodge star `⋆α` is a complex `(d−p)`-form (twisted, since the metric is
ℂ-valued). The carrier for `⋆` is therefore the complexification `V_ℂ = ℂ ⊗_ℝ V` with the
ℂ-bilinear extension `g_ℂ` of `g`. The project's `AllowableComplexMetric` carries only the
ℝ-bilinear ℂ-valued `toForm` on real `V`; this section builds `V_ℂ` and `g_ℂ` on top of it.
-/

section Complexification

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The complexification `V_ℂ = ℂ ⊗_ℝ V` of a real vector space, the carrier on which the
Hodge star of a complex metric lives (since `⋆α` is a complex `(d−p)`-form). -/
abbrev Complexified (V : Type*) [AddCommGroup V] [Module ℝ V] := ℂ ⊗[ℝ] V

/-- Real part of the complex-valued form `g`, as a real bilinear form on `V`. -/
noncomputable def reForm (g : AllowableComplexMetric V) : LinearMap.BilinForm ℝ V :=
  g.toForm.compr₂ Complex.reLm

/-- Imaginary part of the complex-valued form `g`, as a real bilinear form on `V`. -/
noncomputable def imForm (g : AllowableComplexMetric V) : LinearMap.BilinForm ℝ V :=
  g.toForm.compr₂ Complex.imLm

/-- The ℂ-bilinear extension `g_ℂ` of an allowable complex metric `g` to the complexification
`V_ℂ = ℂ ⊗_ℝ V`. Built as `(Re g)_ℂ + i·(Im g)_ℂ`, the base changes of the real and imaginary
parts of `g`. On `1 ⊗ v, 1 ⊗ w` it restricts to `g v w` (`gc_apply_tmul`), the float-free
tie to `g`. -/
noncomputable def gc (g : AllowableComplexMetric V) :
    LinearMap.BilinForm ℂ (ℂ ⊗[ℝ] V) :=
  (reForm g).baseChange ℂ + Complex.I • (imForm g).baseChange ℂ

/-- **Float-free tie of `g_ℂ` to `g`.** The ℂ-bilinear extension restricts to the original
ℂ-valued form on the (real) generators `1 ⊗ v`. -/
theorem gc_apply_tmul (g : AllowableComplexMetric V) (v w : V) :
    gc g ((1 : ℂ) ⊗ₜ[ℝ] v) ((1 : ℂ) ⊗ₜ[ℝ] w) = g.toForm v w := by
  simp only [gc, reForm, imForm, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.BilinForm.baseChange_tmul, LinearMap.compr₂_apply, Complex.reLm_coe,
    Complex.imLm_coe, mul_one, Complex.real_smul, smul_eq_mul]
  linear_combination Complex.re_add_im (g.toForm v w)

end Complexification

end KontsevichSegal.Hodge
