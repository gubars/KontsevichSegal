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
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace KontsevichSegal.Hodge

open exteriorPower LinearMap
open scoped TensorProduct

/-! ## General exterior-algebra lemmas

Two facts about wedge products that Mathlib does not provide directly, used to build the perfect
wedge pairing. They hold over any commutative ring / field and any module. -/

section ExteriorAux

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The wedge of a concatenated family is the algebra product of the two wedges: `ιMulti` turns
`Fin.append` into multiplication in the exterior algebra. -/
theorem ιMulti_append_eq_mul {m n : ℕ} (v : Fin m → M) (w : Fin n → M) :
    ExteriorAlgebra.ιMulti R (m + n) (Fin.append v w)
      = ExteriorAlgebra.ιMulti R m v * ExteriorAlgebra.ιMulti R n w := by
  have happ : (fun i => (ExteriorAlgebra.ι R) (Fin.append v w i))
      = Fin.append (fun i => (ExteriorAlgebra.ι R) (v i))
          (fun i => (ExteriorAlgebra.ι R) (w i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [Fin.append_left, Fin.append_right]
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply,
    happ, List.ofFn_fin_append, List.prod_append]

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- The wedge of a linearly independent family is nonzero. (Over a field; the family is then part
of a basis of its span, whose exterior power has it as a nonzero basis vector.) -/
theorem ιMulti_ne_zero_of_linearIndependent {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent K v) : exteriorPower.ιMulti K n v ≠ 0 := by
  have hli := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv
  have hcard : (Finset.univ : Finset (Fin n)) ∈ Set.powersetCard (Fin n) n := by simp
  have h0 := hli.ne_zero ⟨Finset.univ, hcard⟩
  have hid : Finset.univ.orderEmbOfFin (Finset.card_univ.trans (Fintype.card_fin n))
      = RelEmbedding.refl (α := Fin n) (· ≤ ·) :=
    (Finset.orderEmbOfFin_unique' _ (fun j => Finset.mem_univ _)).symm
  rw [exteriorPower.ιMulti_family] at h0
  convert h0 using 3
  funext i
  exact congrArg v (congrFun (congrArg DFunLike.coe hid.symm) i)

end ExteriorAux

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

/-- **`g_p` is symmetric (from `B` symmetric).** Checked on the `Basis.exteriorPower` basis:
the Gram-determinant value is unchanged under `S ↔ T` by `B`'s symmetry and `det_transpose`. -/
theorem inducedForm_isSymm (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (hsymm : B.IsSymm) (p : ℕ) : (inducedForm B hB p).IsSymm := by
  classical
  rw [LinearMap.BilinForm.isSymm_iff_basis ((Module.finBasis K W).exteriorPower p)]
  intro S T
  rw [basis_apply, basis_apply]
  simp only [ιMulti_family]
  rw [inducedForm_apply_ιMulti, inducedForm_apply_ιMulti]
  conv_rhs => rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, Function.comp_apply]
  exact hsymm.eq _ _

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

/-! ### Pairing-perfectness: the wedge `∧ᵖ × ∧^{d−p} → ∧ᵈ` is a perfect pairing

For `p + q = d = finrank`, the wedge `η ↦ (γ ↦ γ ∧ η)` into the 1-dimensional top exterior power is
a linear equivalence `⋀^q W ≃ (⋀^p W →ₗ ⋀^d W)`. This is the perfect pairing underlying the Hodge
star (KS paper Definition 2.1, the form `α ↦ α ∧ ⋆α`): `⋆` is defined from its inverse. -/

/-- A wedge of two `Basis.exteriorPower` vectors is `ιMulti` of the concatenated index families. -/
theorem wedge_eb_eq {p q : ℕ}
    (S : Set.powersetCard (Fin (Module.finrank K W)) p)
    (T : Set.powersetCard (Fin (Module.finrank K W)) q) :
    wedge p q ((Module.finBasis K W).exteriorPower p S) ((Module.finBasis K W).exteriorPower q T)
      = exteriorPower.ιMulti K (p + q)
          (Module.finBasis K W ∘ Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm S))
            (⇑(Set.powersetCard.ofFinEmbEquiv.symm T))) := by
  apply Subtype.ext
  rw [wedge_coe, basis_apply, basis_apply]
  simp only [ιMulti_family, ιMulti_apply_coe]
  rw [← ιMulti_append_eq_mul]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]

/-- On a complementary pair `(S, Sᶜ)` the wedge of basis vectors is nonzero (distinct factors). -/
theorem wedge_eb_compl_ne_zero {p q : ℕ} (hpq : p + q = Module.finrank K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) p) :
    wedge p q ((Module.finBasis K W).exteriorPower p S)
      ((Module.finBasis K W).exteriorPower q
        (Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S)) ≠ 0 := by
  classical
  set T := Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S with hT
  have hinj : Function.Injective
      (Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm S))
        (⇑(Set.powersetCard.ofFinEmbEquiv.symm T))) := by
    rw [Fin.append_injective_iff]
    refine ⟨EmbeddingLike.injective _, EmbeddingLike.injective _, fun i j hc => ?_⟩
    have hi := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp (Set.mem_range_self i)
    have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).mp (Set.mem_range_self j)
    rw [hT, Set.powersetCard.mem_compl] at hj
    rw [hc] at hi
    exact hj hi
  rw [wedge_eb_eq]
  exact ιMulti_ne_zero_of_linearIndependent ((Module.finBasis K W).linearIndependent.comp _ hinj)

/-- On a non-complementary pair the wedge of basis vectors vanishes (a repeated factor). -/
theorem wedge_eb_ne_compl_eq_zero {p q : ℕ} (hpq : p + q = Module.finrank K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) p)
    (T : Set.powersetCard (Fin (Module.finrank K W)) q)
    (hST : T ≠ Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S) :
    wedge p q ((Module.finBasis K W).exteriorPower p S) ((Module.finBasis K W).exteriorPower q T)
      = 0 := by
  classical
  rw [wedge_eb_eq]
  have hov : ¬ Disjoint (S : Finset (Fin (Module.finrank K W))) (T : Finset (Fin _)) := by
    intro hdis
    apply hST
    rw [Set.powersetCard.eq_iff_subset, Set.powersetCard.coe_compl]
    exact Finset.subset_compl_iff_disjoint_right.mpr hdis.symm
  rw [Finset.not_disjoint_iff] at hov
  obtain ⟨a, haS, haT⟩ := hov
  obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S a).mpr haS
  obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T a).mpr haT
  refine (exteriorPower.ιMulti K (p + q)).map_eq_zero_of_eq _ (i := Fin.castAdd q i)
    (j := Fin.natAdd p j) ?_ ?_
  · simp only [Function.comp_apply, Fin.append_left, Fin.append_right, hi, hj]
  · simp [Fin.ext_iff, Fin.castAdd, Fin.natAdd]; omega

/-- The wedge into the top exterior power `∧ᵖ × ∧^q → ∧ᵈ` (`d = finrank`). The degree cast
`∧^{p+q} ≃ ∧ᵈ` is `LinearEquiv.ofEq` (the two are literally the same submodule once `p + q = d`),
so it is the identity on the underlying exterior-algebra element. -/
noncomputable def wedgeTop {p q : ℕ} (hpq : p + q = Module.finrank K W) :
    (⋀[K]^p W) →ₗ[K] (⋀[K]^q W) →ₗ[K] (⋀[K]^(Module.finrank K W) W) :=
  LinearMap.compr₂ (wedge p q)
    (LinearEquiv.ofEq (⋀[K]^(p + q) W) (⋀[K]^(Module.finrank K W) W)
      (by rw [hpq])).toLinearMap

omit [FiniteDimensional K W] in
theorem wedgeTop_apply {p q : ℕ} (hpq : p + q = Module.finrank K W)
    (γ : ⋀[K]^p W) (η : ⋀[K]^q W) :
    wedgeTop hpq γ η
      = LinearEquiv.ofEq (⋀[K]^(p + q) W) (⋀[K]^(Module.finrank K W) W)
          (by rw [hpq]) (wedge p q γ η) :=
  rfl

/-- `wedgeTop` is right-nondegenerate: pairing with every `γ` detects `η`. -/
theorem wedgeTop_flip_injective {p q : ℕ} (hpq : p + q = Module.finrank K W) :
    Function.Injective (wedgeTop hpq).flip := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro η hη
  have hall : ∀ γ : ⋀[K]^p W, wedge p q γ η = 0 := by
    intro γ
    have hγ := LinearMap.congr_fun hη γ
    rw [LinearMap.flip_apply, wedgeTop_apply, LinearMap.zero_apply] at hγ
    exact (LinearEquiv.ofEq _ _ (by rw [hpq])).map_eq_zero_iff.mp hγ
  apply ((Module.finBasis K W).exteriorPower q).repr.injective
  ext T
  rw [map_zero]
  set S := (Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq)).symm T
  have hcompl : Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S = T :=
    Equiv.apply_symm_apply _ _
  have key := hall ((Module.finBasis K W).exteriorPower p S)
  rw [← ((Module.finBasis K W).exteriorPower q).sum_repr η, map_sum] at key
  simp only [map_smul] at key
  rw [Finset.sum_eq_single
    (Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S), hcompl] at key
  · rcases smul_eq_zero.mp key with hr | hw
    · simpa using hr
    · exact absurd (hcompl ▸ hw) (wedge_eb_compl_ne_zero hpq S)
  · intro T' _ hne
    rw [wedge_eb_ne_compl_eq_zero hpq S T' hne, smul_zero]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- `dim ⋀^q W = C(d,q) = C(d,p) = dim (⋀^p W →ₗ ⋀^d W)` (the top power is 1-dimensional). -/
theorem wedgeTop_finrank_eq {p q : ℕ} (hpq : p + q = Module.finrank K W) :
    Module.finrank K (⋀[K]^q W)
      = Module.finrank K ((⋀[K]^p W) →ₗ[K] (⋀[K]^(Module.finrank K W) W)) := by
  have hp : p ≤ Module.finrank K W := by omega
  have hq : Module.finrank K W - p = q := by omega
  rw [Module.finrank_linearMap, exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    exteriorPower.finrank_eq, Nat.choose_self, mul_one, ← hq, Nat.choose_symm hp]

/-- **Pairing-perfectness (KS Definition 2.1; the input Run 3's `⋆` consumes).** For
`p + q = finrank K W`, the wedge pairing into the top exterior power is a linear equivalence
`⋀^q W ≃ₗ (⋀^p W →ₗ ⋀^{finrank} W)`, namely `η ↦ (γ ↦ γ ∧ η)`. -/
noncomputable def wedgePairingEquiv {p q : ℕ} (hpq : p + q = Module.finrank K W) :
    (⋀[K]^q W) ≃ₗ[K] ((⋀[K]^p W) →ₗ[K] (⋀[K]^(Module.finrank K W) W)) :=
  LinearEquiv.ofBijective (wedgeTop hpq).flip
    ⟨wedgeTop_flip_injective hpq,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (wedgeTop_finrank_eq hpq)).mp (wedgeTop_flip_injective hpq)⟩

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

/-- **`g_ℂ` is symmetric**, inherited from `g`. -/
theorem gc_isSymm (g : AllowableComplexMetric V) : (gc g).IsSymm := by
  classical
  rw [LinearMap.BilinForm.isSymm_iff_basis ((Module.finBasis ℝ V).baseChange ℂ)]
  intro i j
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply, gc_apply_tmul, gc_apply_tmul]
  exact g.symmetric' _ _

/-- **`g_ℂ` is nondegenerate** (the load-bearing nondegeneracy). Its Gram matrix in the
base-change basis `{1 ⊗ eᵢ}` is `g`'s complex Gram matrix `[g(eᵢ, eⱼ)]` (via `gc_apply_tmul`),
whose determinant is nonzero because `volume_element_positive` exhibits a square root with
positive real part. -/
theorem gc_nondegenerate (g : AllowableComplexMetric V) : (gc g).Nondegenerate := by
  classical
  set b := Module.finBasis ℝ V with hb
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange ℂ)]
  have hM : LinearMap.BilinForm.toMatrix (b.baseChange ℂ) (gc g)
      = Matrix.of (fun i j => g.toForm (b i) (b j)) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply, gc_apply_tmul,
      Matrix.of_apply]
  rw [hM]
  obtain ⟨w, hw, hwre⟩ := (volume_element_positive g b).2
  rw [← hw]
  exact pow_ne_zero 2 (fun h => by rw [h] at hwre; simp at hwre)

/-- The **complex induced form** `g_p^ℂ` on `⋀ᵖ(V_ℂ)`: the induced form (`inducedForm`) of the
ℂ-bilinear extension `g_ℂ`. This is the object on which KS paper Definition 2.1 places its
positivity condition (the quadratic form `α ↦ α ∧ ⋆α` builds on it). -/
noncomputable def formC (g : AllowableComplexMetric V) (p : ℕ) :
    LinearMap.BilinForm ℂ (⋀[ℂ]^p (ℂ ⊗[ℝ] V)) :=
  inducedForm (gc g) (gc_nondegenerate g) p

/-- Gram-determinant tie for the complex induced form (corollary of `inducedForm_apply_ιMulti`
at `g_ℂ`), pinning `formC` to `g_ℂ`. -/
theorem formC_apply_ιMulti (g : AllowableComplexMetric V) (p : ℕ)
    (v w : Fin p → ℂ ⊗[ℝ] V) :
    formC g p (ιMulti ℂ p v) (ιMulti ℂ p w) = (Matrix.of fun i j => gc g (v j) (w i)).det :=
  inducedForm_apply_ιMulti (gc g) (gc_nondegenerate g) p v w

/-- The complex induced form is nondegenerate (corollary of `inducedForm_nondegenerate`). -/
theorem formC_nondegenerate (g : AllowableComplexMetric V) (p : ℕ) :
    (formC g p).Nondegenerate :=
  inducedForm_nondegenerate (gc g) (gc_nondegenerate g) p

end Complexification

end KontsevichSegal.Hodge
