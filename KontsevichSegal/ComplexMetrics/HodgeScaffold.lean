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

/-! ### Block graded-commutativity

Mathlib provides only degree-1 graded commutativity (`ι_add_mul_swap`). The Hodge star's sign
`(-1)^{p(d−p)}` comes from swapping a `p`-blade past a `q`-blade, which costs `(-1)^{pq}`
(`block_comm`). These hold over any commutative ring. -/

/-- Anticommutativity of generators: `ι a * ι b = -(ι b * ι a)`. -/
theorem ι_anticomm (a b : M) :
    ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b
      = -(ExteriorAlgebra.ι R b * ExteriorAlgebra.ι R a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

/-- Moving a single generator past an `n`-blade costs `(-1)^n`:
`ι a * ιMulti n w = (-1)^n • (ιMulti n w * ι a)`. -/
theorem ι_mul_block (a : M) {n : ℕ} (w : Fin n → M) :
    ExteriorAlgebra.ι R a * ExteriorAlgebra.ιMulti R n w
      = (-1 : R) ^ n • (ExteriorAlgebra.ιMulti R n w * ExteriorAlgebra.ι R a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc, ι_anticomm, neg_mul, mul_assoc,
      ih (Matrix.vecTail w), mul_smul_comm, mul_assoc, pow_succ, mul_neg_one, neg_smul]

/-- **Block graded-commutativity**: an `m`-blade and an `n`-blade commute up to the sign
`(-1)^{mn}`: `ιMulti m v * ιMulti n w = (-1)^{mn} • (ιMulti n w * ιMulti m v)`. The source of the
Hodge star's `(-1)^{p(d−p)}` sign. -/
theorem block_comm {m n : ℕ} (v : Fin m → M) (w : Fin n → M) :
    ExteriorAlgebra.ιMulti R m v * ExteriorAlgebra.ιMulti R n w
      = (-1 : R) ^ (m * n) • (ExteriorAlgebra.ιMulti R n w * ExteriorAlgebra.ιMulti R m v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, ih (Matrix.vecTail v), mul_smul_comm,
      ← mul_assoc, ι_mul_block, smul_mul_assoc, smul_smul, mul_assoc,
      ← ExteriorAlgebra.ιMulti_succ_apply, ← pow_add,
      show m * n + n = (m + 1) * n from by ring]

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

/-- **Graded commutativity of the wedge**: `x ∧ y = (-1)^{pq} • (y ∧ x)` for `x ∈ ⋀ᵖW`,
`y ∈ ⋀^qW` (the degree match `⋀^{q+p} = ⋀^{p+q}` is the identity-on-carrier `LinearEquiv.ofEq`).
Extends `block_comm` from decomposables to all of `⋀ᵖW × ⋀^qW` by bilinearity and the
`Basis.exteriorPower` spanning. This is the source of the Hodge star's `(-1)^{p(d−p)}` sign. -/
theorem wedge_comm {p q : ℕ} (x : ⋀[K]^p W) (y : ⋀[K]^q W) :
    wedge p q x y
      = (-1 : K) ^ (p * q) •
          (LinearEquiv.ofEq (⋀[K]^(q + p) W) (⋀[K]^(p + q) W) (by rw [Nat.add_comm])
            (wedge q p y x)) := by
  have hbil : wedge p q
      = ((wedge q p).flip).compr₂
          (((-1 : K) ^ (p * q)) • (LinearEquiv.ofEq (⋀[K]^(q + p) W) (⋀[K]^(p + q) W)
            (by rw [Nat.add_comm])).toLinearMap) := by
    refine Module.Basis.ext ((Module.finBasis K W).exteriorPower p) fun S => ?_
    refine Module.Basis.ext ((Module.finBasis K W).exteriorPower q) fun T => ?_
    apply Subtype.ext
    simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.smul_apply,
      wedge_coe, SetLike.val_smul, LinearEquiv.coe_ofEq_apply, LinearEquiv.coe_coe,
      basis_apply, ιMulti_family, ιMulti_apply_coe]
    exact block_comm _ _
  have h := LinearMap.congr_fun (LinearMap.congr_fun hbil x) y
  simpa only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe] using h

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

/-- Evaluation of the pairing equivalence: `wedgePairingEquiv hpq η γ = γ ∧ η` (into the top
power). -/
@[simp] lemma wedgePairingEquiv_apply_apply {p q : ℕ} (hpq : p + q = Module.finrank K W)
    (η : ⋀[K]^q W) (γ : ⋀[K]^p W) :
    wedgePairingEquiv hpq η γ = wedgeTop hpq γ η := by
  rw [wedgePairingEquiv, LinearEquiv.ofBijective_apply, LinearMap.flip_apply]

/-! ### The volume form and the Hodge star operator `⋆`

KS paper Definition 2.1 builds the star from the perfect wedge pairing `⋀ᵖ × ⋀^{d−p} → ⋀ᵈ`:
`⋆β` is the unique `(d−p)`-vector with `γ ∧ ⋆β = g_p(γ,β) · vol` for all `γ`. We realize it as
`wedgePairingEquiv.symm` applied to the functional `γ ↦ g_p(γ,β) · vol`. -/

/-- The canonical **volume form** `vol`: the `Basis.exteriorPower` top vector of
`Module.finBasis K W` at the unique index `univ ∈ powersetCard (Fin d) d`, a generator of the
1-dimensional top exterior power `⋀ᵈW` (`d = finrank K W`). This is the `*1` of KS paper
Definition 2.1 against which the Hodge star wedges. (It is the basis volume `|dx¹…dxᵈ|`, not the
metric-normalized `vol_g = (det g)^{1/2}|dx|` of KS (3); the `(det g)^{1/2}` factor is recorded
separately, see `starOp_starOp`.) -/
noncomputable def volForm : ⋀[K]^(Module.finrank K W) W :=
  (Module.finBasis K W).exteriorPower (Module.finrank K W) ⟨Finset.univ, by simp⟩

/-- The volume form is nonzero (it is a basis vector of `⋀ᵈW`). -/
theorem volForm_ne_zero : (volForm : ⋀[K]^(Module.finrank K W) W) ≠ 0 :=
  ((Module.finBasis K W).exteriorPower (Module.finrank K W)).ne_zero _

/-- The functional `γ ↦ g_p(γ, β) · vol` packaged as a `K`-linear map in `β`, the input to
`wedgePairingEquiv.symm` that defines `⋆`. -/
noncomputable def wedgeFunctional (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate) (p : ℕ) :
    (⋀[K]^p W) →ₗ[K] ((⋀[K]^p W) →ₗ[K] (⋀[K]^(Module.finrank K W) W)) :=
  (LinearMap.llcomp K (⋀[K]^p W) K (⋀[K]^(Module.finrank K W) W)
      (LinearMap.toSpanSingleton K _ volForm)).comp (inducedForm B hB p).flip

@[simp] lemma wedgeFunctional_apply (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate) (p : ℕ)
    (β γ : ⋀[K]^p W) :
    wedgeFunctional B hB p β γ = inducedForm B hB p γ β • volForm := by
  simp [wedgeFunctional, LinearMap.llcomp_apply, LinearMap.toSpanSingleton_apply]

/-- **The Hodge star operator `⋆`** at degree `p` (with `q = d − p`, `d = finrank K W`), for a
nondegenerate bilinear form `B`. Built from the perfect wedge pairing: `⋆β` is the unique
`(d−p)`-vector with `γ ∧ ⋆β = g_p(γ, β) · vol` for all `γ` (`starOp_wedge`). This is the `⋆` of
KS paper Definition 2.1. -/
noncomputable def starOp (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate) (p q : ℕ)
    (hpq : p + q = Module.finrank K W) : (⋀[K]^p W) →ₗ[K] (⋀[K]^q W) :=
  (wedgePairingEquiv hpq).symm.toLinearMap.comp (wedgeFunctional B hB p)

/-- **The defining equation of the Hodge star.** `γ ∧ ⋆β = g_p(γ, β) · vol` for all `γ`, with
the wedge landing in the top power `⋀ᵈW` (KS paper Definition 2.1, the form `α ↦ α ∧ ⋆α`). This
pins `⋆` to the pair `(g_p, vol)`. -/
theorem starOp_wedge (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate) (p q : ℕ)
    (hpq : p + q = Module.finrank K W) (γ β : ⋀[K]^p W) :
    wedgeTop hpq γ (starOp B hB p q hpq β) = inducedForm B hB p γ β • volForm := by
  have h2 := LinearMap.congr_fun
    ((wedgePairingEquiv hpq).apply_symm_apply (wedgeFunctional B hB p β)) γ
  rw [wedgePairingEquiv_apply_apply, wedgeFunctional_apply] at h2
  exact h2

/-- **Uniqueness of the Hodge star.** `⋆β` is the unique `(d−p)`-vector satisfying the defining
equation `γ ∧ x = g_p(γ, β) · vol` for all `γ` (the wedge pairing is perfect). -/
theorem starOp_unique (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate) (p q : ℕ)
    (hpq : p + q = Module.finrank K W) (β : ⋀[K]^p W) (x : ⋀[K]^q W)
    (hx : ∀ γ, wedgeTop hpq γ x = inducedForm B hB p γ β • volForm) :
    x = starOp B hB p q hpq β := by
  apply wedgeTop_flip_injective hpq
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.flip_apply, LinearMap.flip_apply, hx z, starOp_wedge]

/-- **The Hodge star is a linear equivalence** `⋀ᵖW ≃ₗ ⋀^{d−p}W`, a corollary of nondegeneracy
of `g_p` and `dim ⋀ᵖW = dim ⋀^{d−p}W`. -/
noncomputable def starEquiv (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (p q : ℕ) (hpq : p + q = Module.finrank K W) : (⋀[K]^p W) ≃ₗ[K] (⋀[K]^q W) :=
  LinearEquiv.ofBijective (starOp B hB p q hpq) <| by
    have hinj : Function.Injective (starOp B hB p q hpq) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro β hβ
      have key : ∀ γ, inducedForm B hB p γ β = 0 := by
        intro γ
        have h := starOp_wedge B hB p q hpq γ β
        rw [hβ, map_zero] at h
        exact (smul_eq_zero.mp h.symm).resolve_right volForm_ne_zero
      exact (inducedForm_nondegenerate B hB p).2 β key
    refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
    rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq,
      show q = Module.finrank K W - p from by omega,
      Nat.choose_symm (show p ≤ Module.finrank K W from by omega)]

/-! ### Diagonal Gram determinants on a `B`-orthogonal basis (toward `star_star`)

For a `B`-orthogonal basis `c`, the induced form `g_n` is diagonal in the exterior-power basis
`{c_S}`: `g_n(c_S, c_T) = δ_{ST} · ∏_{i} B(c_{S(i)}, c_{S(i)})` (KS Theorem-2.2 computation,
KSTeX 201–205). This is the magnitude input to `star_star`. -/

omit [FiniteDimensional K W] in
/-- A `Basis.exteriorPower` blade is `ιMulti` of the corresponding ordered subfamily. -/
theorem exteriorPower_basis_apply_eq {n : ℕ}
    (c : Module.Basis (Fin (Module.finrank K W)) K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) n) :
    c.exteriorPower n S
      = exteriorPower.ιMulti K n (c ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm S)) := by
  rw [basis_apply]; rfl

/-- **Diagonal Gram (diagonal entry) on an orthogonal basis.** `g_n(c_S, c_S)` is the determinant
of a diagonal matrix, `∏ᵢ B(c_{S i}, c_{S i})`. -/
theorem gram_blade_diag {n : ℕ} (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    {c : Module.Basis (Fin (Module.finrank K W)) K W} (hc : B.IsOrthoᵢ c)
    (S : Set.powersetCard (Fin (Module.finrank K W)) n) :
    inducedForm B hB n (c.exteriorPower n S) (c.exteriorPower n S)
      = ∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
              (c (Set.powersetCard.ofFinEmbEquiv.symm S i)) := by
  rw [exteriorPower_basis_apply_eq, inducedForm_apply_ιMulti]
  have hM : (Matrix.of fun i j => B ((c ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm S)) j)
              ((c ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm S)) i))
        = Matrix.diagonal (fun i => B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
            (c (Set.powersetCard.ofFinEmbEquiv.symm S i))) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      exact isOrthoᵢ_def.mp hc _ _
        (fun h => hij (((Set.powersetCard.ofFinEmbEquiv.symm S).injective h).symm))
  rw [hM, Matrix.det_diagonal]

/-- **Diagonal Gram on an orthogonal basis (off-diagonal).** `g_n(c_S, c_T) = 0` for `S ≠ T`
(the Gram matrix has a zero row). -/
theorem gram_blade_eq_zero {n : ℕ} (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    {c : Module.Basis (Fin (Module.finrank K W)) K W} (hc : B.IsOrthoᵢ c)
    (S T : Set.powersetCard (Fin (Module.finrank K W)) n) (hST : S ≠ T) :
    inducedForm B hB n (c.exteriorPower n S) (c.exteriorPower n T) = 0 := by
  rw [exteriorPower_basis_apply_eq, exteriorPower_basis_apply_eq, inducedForm_apply_ιMulti]
  have hsub : ¬ ((T : Finset (Fin (Module.finrank K W)))
      ⊆ (S : Finset (Fin (Module.finrank K W)))) := by
    intro hts
    exact hST ((Subtype.ext (Finset.eq_of_subset_of_card_le hts (by simp))).symm)
  obtain ⟨a, haT, haS⟩ := Finset.not_subset.mp hsub
  obtain ⟨i₀, hi₀⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T a).mpr haT
  apply Matrix.det_eq_zero_of_row_eq_zero i₀
  intro j
  simp only [Matrix.of_apply, Function.comp_apply]
  apply isOrthoᵢ_def.mp hc
  intro h
  rw [hi₀] at h
  exact haS (h ▸ (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨j, rfl⟩)

/-- **Diagonal Gram for an `ιMulti` of an injective reindex of an orthogonal basis.** The general
form of `gram_blade_diag`, also covering the top-degree wedge `c_S ∧ c_{Sᶜ}` (which is `ιMulti` of a
permuted, not increasing, family). -/
theorem gram_ιMulti_diag {n : ℕ} (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    {c : Module.Basis (Fin (Module.finrank K W)) K W} (hc : B.IsOrthoᵢ c)
    {e : Fin n → Fin (Module.finrank K W)} (he : Function.Injective e) :
    inducedForm B hB n (exteriorPower.ιMulti K n (c ∘ e)) (exteriorPower.ιMulti K n (c ∘ e))
      = ∏ i, B (c (e i)) (c (e i)) := by
  rw [inducedForm_apply_ιMulti]
  have hM : (Matrix.of fun i j => B ((c ∘ e) j) ((c ∘ e) i))
        = Matrix.diagonal (fun i => B (c (e i)) (c (e i))) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.diagonal_apply, Function.comp_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      exact isOrthoᵢ_def.mp hc _ _ (fun h => hij (he h).symm)
  rw [hM, Matrix.det_diagonal]

/-- **Naturality of the induced form under the degree cast.** `g` commutes with the
`LinearEquiv.ofEq` identification `⋀^m ≃ ⋀^n` (`m = n`). -/
theorem inducedForm_ofEq {m n : ℕ} (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (h : m = n) (x y : ⋀[K]^m W) :
    inducedForm B hB n (LinearEquiv.ofEq _ _ (by rw [h]) x)
        (LinearEquiv.ofEq _ _ (by rw [h]) y) = inducedForm B hB m x y := by
  subst h
  rw [show (LinearEquiv.ofEq _ _ (by rfl) x : ⋀[K]^m W) = x from
        Subtype.ext (LinearEquiv.coe_ofEq_apply _ x),
      show (LinearEquiv.ofEq _ _ (by rfl) y : ⋀[K]^m W) = y from
        Subtype.ext (LinearEquiv.coe_ofEq_apply _ y)]

omit [FiniteDimensional K W] in
/-- A wedge of two `Basis.exteriorPower` blades (for any basis `c`) is `ιMulti` of the concatenated
ordered subfamilies. The general-basis version of `wedge_eb_eq`. -/
theorem wedge_basis_append {p q : ℕ} (c : Module.Basis (Fin (Module.finrank K W)) K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) p)
    (T : Set.powersetCard (Fin (Module.finrank K W)) q) :
    wedge p q (c.exteriorPower p S) (c.exteriorPower q T)
      = exteriorPower.ιMulti K (p + q)
          (c ∘ Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm S))
            (⇑(Set.powersetCard.ofFinEmbEquiv.symm T))) := by
  apply Subtype.ext
  rw [wedge_coe, basis_apply, basis_apply]
  simp only [ιMulti_family, ιMulti_apply_coe]
  rw [← ιMulti_append_eq_mul]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]

/-- **Top Gram of a complementary wedge.** `g_d(c_S ∧ c_T, c_S ∧ c_T) = (∏ᵢ B(c_{S i}, c_{S i})) ·
(∏ⱼ B(c_{T j}, c_{T j}))` when `S, T` are complementary (`Fin.append` of their order embeddings is
injective). The magnitude bridge `R_S = P_S · Q_S` for `star_star`. -/
theorem gram_wedgeTop_self {p q : ℕ} (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    {c : Module.Basis (Fin (Module.finrank K W)) K W} (hc : B.IsOrthoᵢ c)
    (hpq : p + q = Module.finrank K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) p)
    (T : Set.powersetCard (Fin (Module.finrank K W)) q)
    (hinj : Function.Injective (Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm S))
      (⇑(Set.powersetCard.ofFinEmbEquiv.symm T)))) :
    inducedForm B hB (Module.finrank K W)
        (wedgeTop hpq (c.exteriorPower p S) (c.exteriorPower q T))
        (wedgeTop hpq (c.exteriorPower p S) (c.exteriorPower q T))
      = (∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
              (c (Set.powersetCard.ofFinEmbEquiv.symm S i)))
        * (∏ j, B (c (Set.powersetCard.ofFinEmbEquiv.symm T j))
              (c (Set.powersetCard.ofFinEmbEquiv.symm T j))) := by
  rw [wedgeTop_apply, inducedForm_ofEq B hB hpq, wedge_basis_append,
    gram_ιMulti_diag B hB hc hinj, Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [Fin.append_left]
  · exact Finset.prod_congr rfl fun j _ => by rw [Fin.append_right]

omit [FiniteDimensional K W] in
/-- General-basis version of `wedge_eb_compl_ne_zero`: on a complementary pair `(S, Sᶜ)` the wedge
of basis blades is nonzero. -/
theorem wedge_basis_compl_ne_zero {p q : ℕ} (c : Module.Basis (Fin (Module.finrank K W)) K W)
    (hpq : p + q = Module.finrank K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) p) :
    wedge p q (c.exteriorPower p S)
      (c.exteriorPower q (Set.powersetCard.compl
        (by rw [Fintype.card_fin, add_comm]; exact hpq) S)) ≠ 0 := by
  classical
  set T := Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S with hT
  have hinj : Function.Injective
      (Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm S))
        (⇑(Set.powersetCard.ofFinEmbEquiv.symm T))) := by
    rw [Fin.append_injective_iff]
    refine ⟨EmbeddingLike.injective _, EmbeddingLike.injective _, fun i j hc' => ?_⟩
    have hi := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp (Set.mem_range_self i)
    have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).mp (Set.mem_range_self j)
    rw [hT, Set.powersetCard.mem_compl] at hj
    rw [hc'] at hi
    exact hj hi
  rw [wedge_basis_append]
  exact ιMulti_ne_zero_of_linearIndependent (c.linearIndependent.comp _ hinj)

omit [FiniteDimensional K W] in
/-- General-basis version of `wedge_eb_ne_compl_eq_zero`: on a non-complementary pair the wedge of
basis blades vanishes (a repeated factor). -/
theorem wedge_basis_ne_compl_zero {p q : ℕ} (c : Module.Basis (Fin (Module.finrank K W)) K W)
    (hpq : p + q = Module.finrank K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) p)
    (T : Set.powersetCard (Fin (Module.finrank K W)) q)
    (hST : T ≠ Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S) :
    wedge p q (c.exteriorPower p S) (c.exteriorPower q T) = 0 := by
  classical
  rw [wedge_basis_append]
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

/-- **The Hodge star of an orthogonal-basis blade is a scalar multiple of the complementary blade.**
`⋆(c_S) = b · c_{Sᶜ}`, where the scalar `b` satisfies the float-free relation
`b · (c_S ∧ c_{Sᶜ}) = (∏ᵢ B(c_{S i}, c_{S i})) · vol`. (KS Theorem-2.2 diagonalization.) -/
theorem star_blade {n m : ℕ} (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    {c : Module.Basis (Fin (Module.finrank K W)) K W} (hc : B.IsOrthoᵢ c)
    (hnm : n + m = Module.finrank K W)
    (S : Set.powersetCard (Fin (Module.finrank K W)) n) :
    ∃ b : K,
      starOp B hB n m hnm (c.exteriorPower n S)
          = b • c.exteriorPower m (Set.powersetCard.compl
              (by rw [Fintype.card_fin, add_comm]; exact hnm) S)
        ∧ b • wedgeTop hnm (c.exteriorPower n S)
              (c.exteriorPower m (Set.powersetCard.compl
                (by rw [Fintype.card_fin, add_comm]; exact hnm) S))
            = (∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
                (c (Set.powersetCard.ofFinEmbEquiv.symm S i))) • volForm := by
  classical
  obtain ⟨lam, hlam⟩ : ∃ lam : K, lam • wedgeTop hnm (c.exteriorPower n S)
      (c.exteriorPower m (Set.powersetCard.compl
        (by rw [Fintype.card_fin, add_comm]; exact hnm) S)) = volForm := by
    have hwne : wedge n m (c.exteriorPower n S)
        (c.exteriorPower m (Set.powersetCard.compl
          (by rw [Fintype.card_fin, add_comm]; exact hnm) S)) ≠ 0 :=
      wedge_basis_compl_ne_zero c hnm S
    have hW₀ne : wedgeTop hnm (c.exteriorPower n S)
        (c.exteriorPower m (Set.powersetCard.compl
          (by rw [Fintype.card_fin, add_comm]; exact hnm) S)) ≠ 0 := by
      rw [wedgeTop_apply]
      exact fun h => hwne ((LinearEquiv.ofEq _ _ (by rw [hnm])).map_eq_zero_iff.mp h)
    have hdim1 : Module.finrank K (⋀[K]^(Module.finrank K W) W) = 1 := by
      rw [exteriorPower.finrank_eq, Nat.choose_self]
    exact (finrank_eq_one_iff_of_nonzero' _ hW₀ne).mp hdim1 volForm
  refine ⟨(∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
      (c (Set.powersetCard.ofFinEmbEquiv.symm S i))) * lam, ?_, ?_⟩
  · -- proportionality, via uniqueness of `⋆`
    have hmap : (wedgeTop hnm).flip
          ((((∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
              (c (Set.powersetCard.ofFinEmbEquiv.symm S i))) * lam) •
            c.exteriorPower m (Set.powersetCard.compl
              (by rw [Fintype.card_fin, add_comm]; exact hnm) S)))
        = wedgeFunctional B hB n (c.exteriorPower n S) := by
      refine Module.Basis.ext (c.exteriorPower n) fun U => ?_
      rw [LinearMap.flip_apply, wedgeFunctional_apply, map_smul]
      by_cases hUS : U = S
      · subst hUS
        rw [gram_blade_diag B hB hc, mul_smul, hlam]
      · rw [gram_blade_eq_zero B hB hc U S hUS, zero_smul]
        rw [wedgeTop_apply,
          wedge_basis_ne_compl_zero c hnm U _
            (fun h => hUS ((Set.powersetCard.compl _).injective h).symm),
          map_zero, smul_zero]
    refine (starOp_unique B hB n m hnm (c.exteriorPower n S) _ fun γ => ?_).symm
    have hg := LinearMap.congr_fun hmap γ
    rwa [LinearMap.flip_apply, wedgeFunctional_apply] at hg
  · rw [mul_smul, hlam]

/-- Swapping the wedge order in the top power costs the block sign `(-1)^{pq}` (the `wedgeTop`
form of `wedge_comm`). -/
theorem wedgeTop_comm {p q : ℕ} (hpq : p + q = Module.finrank K W)
    (hqp : q + p = Module.finrank K W) (γ : ⋀[K]^p W) (η : ⋀[K]^q W) :
    wedgeTop hqp η γ = (-1 : K) ^ (p * q) • wedgeTop hpq γ η := by
  have hcm := congrArg (Subtype.val) (wedge_comm γ η)
  apply Subtype.ext
  simp only [wedgeTop_apply, SetLike.val_smul, LinearEquiv.coe_ofEq_apply, wedge_coe] at hcm ⊢
  rw [hcm, smul_smul, ← pow_add, show p * q + p * q = 2 * (p * q) from by ring, pow_mul,
    neg_one_sq, one_pow, one_smul]

/-- **`⋆⋆ = (-1)^{p(d−p)} · g_d(vol, vol) · id` (generic, magnitude-explicit).** The Hodge star
composed with itself is the homothety by `(-1)^{p·q}` times the top-degree induced form
`g_d(vol, vol)` of the (unnormalized) volume form. Proven by diagonalizing `B` (an orthogonal basis,
KS Theorem-2.2, KSTeX 201–205): `⋆` permutes the blades `c_S ↦ c_{Sᶜ}` and the per-blade scalars
multiply to `(-1)^{pq} · g_d(vol, vol)`, independent of `S`. The sign is `wedge_comm`; the magnitude
is `gram_wedgeTop_self`. -/
theorem starOp_starOp [Invertible (2 : K)] (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (hsymm : B.IsSymm) (p q : ℕ) (hpq : p + q = Module.finrank K W)
    (hqp : q + p = Module.finrank K W) :
    (starOp B hB q p hqp).comp (starOp B hB p q hpq)
      = (inducedForm B hB (Module.finrank K W) volForm volForm)
        • ((-1 : K) ^ (p * q) • LinearMap.id) := by
  classical
  obtain ⟨c, hc⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
    (⟨fun x y => hsymm.eq x y⟩ : LinearMap.IsSymm B)
  refine Module.Basis.ext (c.exteriorPower p) fun S => ?_
  obtain ⟨b1, hb1prop, hb1def⟩ := star_blade B hB hc hpq S
  obtain ⟨b2, hb2prop, hb2def⟩ := star_blade B hB hc hqp
    (Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S)
  have hcc : Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hqp)
      (Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S) = S := by
    apply Subtype.ext
    rw [Set.powersetCard.coe_compl, Set.powersetCard.coe_compl, compl_compl]
  rw [hcc] at hb2def
  rw [wedgeTop_comm hpq hqp, smul_smul] at hb2def
  have hW₀ne : wedgeTop hpq (c.exteriorPower p S)
      (c.exteriorPower q (Set.powersetCard.compl
        (by rw [Fintype.card_fin, add_comm]; exact hpq) S)) ≠ 0 := by
    rw [wedgeTop_apply]
    exact fun h => (wedge_basis_compl_ne_zero c hpq S)
      ((LinearEquiv.ofEq _ _ (by rw [hpq])).map_eq_zero_iff.mp h)
  obtain ⟨lam, hlam⟩ := (finrank_eq_one_iff_of_nonzero' _ hW₀ne).mp
    (by rw [exteriorPower.finrank_eq, Nat.choose_self]) volForm
  have hinj : Function.Injective (Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm S))
      (⇑(Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
        (by rw [Fintype.card_fin, add_comm]; exact hpq) S)))) := by
    rw [Fin.append_injective_iff]
    refine ⟨EmbeddingLike.injective _, EmbeddingLike.injective _, fun i j hij => ?_⟩
    have hi := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp (Set.mem_range_self i)
    have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.compl (by rw [Fintype.card_fin, add_comm]; exact hpq) S) _).mp
        (Set.mem_range_self j)
    rw [Set.powersetCard.mem_compl] at hj
    rw [hij] at hi
    exact hj hi
  have hb1eq : b1 = (∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
      (c (Set.powersetCard.ofFinEmbEquiv.symm S i))) * lam := by
    apply smul_left_injective K hW₀ne
    change b1 • _ = _ • _
    rw [hb1def, mul_smul, hlam]
  have hsq : ((-1 : K) ^ (p * q)) * ((-1 : K) ^ (p * q)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hb2eq : b2 * (-1 : K) ^ (p * q)
      = (∏ j, B (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
          (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))
          (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
          (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))) * lam := by
    apply smul_left_injective K hW₀ne
    change (b2 * (-1 : K) ^ (p * q)) • _ = _ • _
    rw [hb2def, mul_smul, hlam]
  have hg : inducedForm B hB (Module.finrank K W) volForm volForm
      = lam * lam * ((∏ i, B (c (Set.powersetCard.ofFinEmbEquiv.symm S i))
          (c (Set.powersetCard.ofFinEmbEquiv.symm S i)))
        * (∏ j, B (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
            (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))
            (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
            (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j)))) := by
    rw [← hlam]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [gram_wedgeTop_self B hB hc hpq S _ hinj]
    ring
  have hb2' : b2 = (∏ j, B (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
      (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))
      (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
      (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))) * lam * (-1 : K) ^ (p * q) := by
    have h : b2 * (-1 : K) ^ (p * q) * (-1 : K) ^ (p * q)
        = (∏ j, B (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
            (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))
            (c (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.compl
            (by rw [Fintype.card_fin, add_comm]; exact hpq) S) j))) * lam * (-1 : K) ^ (p * q) := by
      rw [hb2eq]
    rwa [mul_assoc b2, hsq, mul_one] at h
  have hscalar : b1 * b2
      = inducedForm B hB (Module.finrank K W) volForm volForm * (-1 : K) ^ (p * q) := by
    rw [hb1eq, hb2', hg]; ring
  rw [LinearMap.comp_apply, hb1prop, map_smul, hb2prop, hcc, smul_smul,
    LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, hscalar]

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

/-- The complex induced form is symmetric (corollary of `inducedForm_isSymm`, using `gc_isSymm`). -/
theorem formC_isSymm (g : AllowableComplexMetric V) (p : ℕ) : (formC g p).IsSymm :=
  inducedForm_isSymm (gc g) (gc_nondegenerate g) (gc_isSymm g) p

/-- **The Hodge star `⋆` of an allowable complex metric**, at degree `p` (`q = d − p`,
`d = finrank ℂ (V_ℂ)`), acting on complex `p`-forms `⋀ᵖ(V_ℂ)`. This is the `⋆_g` of KS paper
Definition 2.1: `⋆β` is the unique complex `(d−p)`-form with `γ ∧ ⋆β = g_p^ℂ(γ,β) · vol` for
all `γ`. -/
noncomputable def star (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) :
    (⋀[ℂ]^p (ℂ ⊗[ℝ] V)) →ₗ[ℂ] (⋀[ℂ]^q (ℂ ⊗[ℝ] V)) :=
  starOp (gc g) (gc_nondegenerate g) p q hpq

/-- **The defining equation of `⋆_g`** (corollary of `starOp_wedge` at `g_ℂ`): the float-free
pin `γ ∧ ⋆β = g_p^ℂ(γ,β) · vol`, tying `⋆_g` to `(formC, vol)`. -/
theorem star_wedge (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) (γ β : ⋀[ℂ]^p (ℂ ⊗[ℝ] V)) :
    wedgeTop hpq γ (star g p q hpq β) = formC g p γ β • volForm :=
  starOp_wedge (gc g) (gc_nondegenerate g) p q hpq γ β

/-- **`⋆_g` is the unique** complex `(d−p)`-form with the defining property (corollary of
`starOp_unique`). -/
theorem star_unique (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) (β : ⋀[ℂ]^p (ℂ ⊗[ℝ] V))
    (x : ⋀[ℂ]^q (ℂ ⊗[ℝ] V))
    (hx : ∀ γ, wedgeTop hpq γ x = formC g p γ β • volForm) :
    x = star g p q hpq β :=
  starOp_unique (gc g) (gc_nondegenerate g) p q hpq β x hx

/-- **`⋆_g` is a linear equivalence** `⋀ᵖ(V_ℂ) ≃ₗ ⋀^{d−p}(V_ℂ)` (corollary of `starEquiv`,
using nondegeneracy and symmetry of `g_ℂ`). -/
noncomputable def starLinearEquiv (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) :
    (⋀[ℂ]^p (ℂ ⊗[ℝ] V)) ≃ₗ[ℂ] (⋀[ℂ]^q (ℂ ⊗[ℝ] V)) :=
  starEquiv (gc g) (gc_nondegenerate g) p q hpq

/-- **`⋆⋆ = (-1)^{p(d−p)} · g_d^ℂ(vol, vol) · id` for an allowable complex metric** (corollary of
`starOp_starOp` at `g_ℂ`). KS paper Definition 2.1: the Hodge star squares to `(-1)^{p(d−p)}` times
the top-degree complex induced form of the volume form (the magnitude `g_d^ℂ(vol, vol)` is the
unnormalized `det g_ℂ` factor; with the metric-normalized `vol_g` it would be `±1`). Note
`p·q = p·(d−p)`, matching KS's exponent `(-1)^{p(d−p)}`. -/
theorem star_star (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) (hqp : q + p = Module.finrank ℂ (ℂ ⊗[ℝ] V)) :
    (star g q p hqp).comp (star g p q hpq)
      = (formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) volForm volForm)
        • ((-1 : ℂ) ^ (p * q) • LinearMap.id) :=
  starOp_starOp (gc g) (gc_nondegenerate g) (gc_isSymm g) p q hpq hqp

/-! ### Normalization: the metric volume `vol_g` and the normalized Hodge star `⋆_g`

KS paper (3) / page 7: the metric volume element is `vol_g = (det g)^{1/2} · |dx|`, and the
normalized Hodge star `⋆_g` wedges against `vol_g` rather than the coordinate volume `volForm`,
yielding the clean `⋆⋆ = (-1)^{p(d−p)}·id` of KS paper Definition 2.1 with the `det g` magnitude
divided out.

Option A (finBasis volume). `volForm` is the top blade of the arbitrary complex basis
`Module.finBasis ℂ (ℂ⊗V)`, not a real coframe, so `g_d^ℂ(volForm, volForm)` equals `det g` only up
to a nonzero complex square; the positive-real-part branch of `(det g)^{1/2}` (KSTeX line 126,
`volume_element_positive`) is therefore not available on it, and is not needed: `detSqrt` is an
arbitrary square root, and every result below (`formC_vol_g_self`, `star_g_star_g`,
`IsAllowableHodge`) is invariant under `detSqrt ↦ −detSqrt`. -/

/-- The top-degree induced form of the volume form is nonzero: `g_d^ℂ(vol, vol) ≠ 0`. Since `⋀ᵈ` is
one-dimensional and `formC g d` is nondegenerate with `volForm ≠ 0`, the single Gram entry is
nonzero. This is `det g_ℂ` (up to the finBasis change-of-basis square), the radicand of
`detSqrt`. -/
theorem formC_volForm_self_ne_zero (g : AllowableComplexMetric V) :
    formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) volForm volForm ≠ 0 := by
  intro h
  refine volForm_ne_zero (K := ℂ) (W := ℂ ⊗[ℝ] V) ?_
  have hdim1 : Module.finrank ℂ (⋀[ℂ]^(Module.finrank ℂ (ℂ ⊗[ℝ] V)) (ℂ ⊗[ℝ] V)) = 1 := by
    rw [exteriorPower.finrank_eq, Nat.choose_self]
  refine (formC_nondegenerate g (Module.finrank ℂ (ℂ ⊗[ℝ] V))).1 volForm (fun y => ?_)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' volForm volForm_ne_zero).mp hdim1 y
  rw [← hc, map_smul, h, smul_zero]

/-- `√det(g_ℂ)`: a square root of the top-degree induced form `g_d^ℂ(vol, vol)` of the volume form,
the `(det g)^{1/2}` normalizing factor of the metric volume element (KS paper (3), page 7). Built by
the polar formula `√‖z‖ · exp(i·arg z / 2)`, so `detSqrt_sq` holds unconditionally. (Option A: an
arbitrary branch — the finBasis `volForm` is not a real coframe, so the positive-real-part branch of
KSTeX line 126 is unavailable; it is also unused, every downstream result being
branch-invariant.) -/
noncomputable def detSqrt (g : AllowableComplexMetric V) : ℂ :=
  (Real.sqrt ‖formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) volForm volForm‖ : ℂ) *
    Complex.exp ((↑(Complex.arg
      (formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) volForm volForm) / 2) : ℂ) * Complex.I)

/-- **`detSqrt` is a square root** of the top induced form (float-free tie): `(detSqrt g)² =
g_d^ℂ(vol, vol)`. -/
theorem detSqrt_sq (g : AllowableComplexMetric V) :
    (detSqrt g) ^ 2 = formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) volForm volForm := by
  set z := formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) volForm volForm with hz
  rw [detSqrt, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg z), pow_two,
    ← Complex.exp_add]
  rw [show (↑(Complex.arg z / 2) : ℂ) * Complex.I + (↑(Complex.arg z / 2) : ℂ) * Complex.I
      = (↑(Complex.arg z) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- `detSqrt g ≠ 0` (its square `g_d^ℂ(vol, vol)` is nonzero). -/
theorem detSqrt_ne_zero (g : AllowableComplexMetric V) : detSqrt g ≠ 0 := by
  intro h
  apply formC_volForm_self_ne_zero g
  rw [← detSqrt_sq g, h]; ring

/-- The **metric volume element** `vol_g = (det g)^{-1/2} · |dx|` (KS paper (3)): the coordinate
volume `volForm` rescaled by `detSqrt⁻¹`, normalized so `g_d^ℂ(vol_g, vol_g) = 1`
(`formC_vol_g_self`). This is the `*1` of KS paper Definition 2.1 against which `⋆_g` wedges. -/
noncomputable def vol_g (g : AllowableComplexMetric V) :
    ⋀[ℂ]^(Module.finrank ℂ (ℂ ⊗[ℝ] V)) (ℂ ⊗[ℝ] V) :=
  (detSqrt g)⁻¹ • volForm

/-- Float-free tie of the metric volume to the coordinate volume. -/
theorem vol_g_eq (g : AllowableComplexMetric V) :
    vol_g g = (detSqrt g)⁻¹ • volForm := rfl

/-- The metric volume is nonzero. -/
theorem vol_g_ne_zero (g : AllowableComplexMetric V) : vol_g g ≠ 0 :=
  smul_ne_zero (inv_ne_zero (detSqrt_ne_zero g)) volForm_ne_zero

/-- **The metric volume is unit-normalized**: `g_d^ℂ(vol_g, vol_g) = 1` (KS paper (3): `vol_g =
(det g)^{-1/2}|dx|` has unit norm). The two `detSqrt⁻¹` factors cancel `(detSqrt)² = g_d(vol, vol)`,
so this is independent of the branch of `detSqrt`. -/
theorem formC_vol_g_self (g : AllowableComplexMetric V) :
    formC g (Module.finrank ℂ (ℂ ⊗[ℝ] V)) (vol_g g) (vol_g g) = 1 := by
  have hne := detSqrt_ne_zero g
  simp only [vol_g, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← detSqrt_sq g]; field_simp

/-- **The normalized Hodge star `⋆_g`**: the committed `⋆` rescaled by `detSqrt⁻¹`, so it wedges
against the metric volume `vol_g` (KS paper Definition 2.1). -/
noncomputable def star_g (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) :
    (⋀[ℂ]^p (ℂ ⊗[ℝ] V)) →ₗ[ℂ] (⋀[ℂ]^q (ℂ ⊗[ℝ] V)) :=
  (detSqrt g)⁻¹ • star g p q hpq

/-- **The defining equation of the normalized Hodge star**: `γ ∧ ⋆_g β = g_p^ℂ(γ, β) · vol_g`, now
against the metric volume `vol_g` (KS paper Definition 2.1, the form `α ↦ α ∧ ⋆α`). The `detSqrt⁻¹`
rescaling of `⋆` lands exactly on `vol_g = detSqrt⁻¹ • volForm`. -/
theorem star_g_wedge (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) (γ β : ⋀[ℂ]^p (ℂ ⊗[ℝ] V)) :
    wedgeTop hpq γ (star_g g p q hpq β) = formC g p γ β • vol_g g := by
  simp only [star_g, LinearMap.smul_apply, map_smul]
  rw [star_wedge, vol_g, smul_comm]

/-- **`⋆⋆ = (-1)^{p(d−p)} · id` (normalized, clean).** With the metric volume the `det g` magnitude
of `star_star` cancels against the two `detSqrt⁻¹` rescalings (`(detSqrt)² = g_d(vol, vol)`), giving
KS paper Definition 2.1's `⋆⋆ = (-1)^{p(d−p)}·id`. Independent of the branch of `detSqrt`. -/
theorem star_g_star_g (g : AllowableComplexMetric V) (p q : ℕ)
    (hpq : p + q = Module.finrank ℂ (ℂ ⊗[ℝ] V)) (hqp : q + p = Module.finrank ℂ (ℂ ⊗[ℝ] V)) :
    (star_g g q p hqp).comp (star_g g p q hpq) = (-1 : ℂ) ^ (p * q) • LinearMap.id := by
  have hne := detSqrt_ne_zero g
  simp only [star_g]
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, star_star g p q hpq hqp, smul_smul,
    ← detSqrt_sq g, show (detSqrt g)⁻¹ * (detSqrt g)⁻¹ * (detSqrt g) ^ 2 = 1 from by field_simp,
    one_smul]

/-! ### The real-coframe determinant and its principal square root

KS's normalization datum (KS paper (3) + KSTeX 126): the volume element is
`vol_g = (det g)^{1/2}|dx¹…dxᵈ|`, with `det g` computed in a REAL coframe, where it is invariant
up to a positive real square (a real change of basis) — exactly the ambiguity of the twisted line
`|⋀ᵈ(V*)|`. On a real-coframe determinant, "not real and negative" and "the square root with
positive real part" are therefore well-defined (`volume_element_positive`), and KS fix the
principal branch: "we choose `(det g)^{1/2}` to have positive real part" (KSTeX 126). This
subsection provides that determinant (`detGramReal`), its principal root (`detSqrtReal`), and the
diagonal factorization and blade translation that Definition 2.1 consumes. (Contrast the `detSqrt`
of the normalized operator above: its radicand `g_d^ℂ(volForm, volForm)` sits over a finBasis of
`ℂ ⊗ V`, not a real coframe, so it is defined only up to a nonzero complex square and has no
principal branch — fine for the operator, unusable for Definition 2.1's positivity.) -/

/-- Polarization of the diagonal form (export of the computation inside
`volume_element_positive`): a diagonalization `g(v,v) = ∑ᵢ λᵢ·(yᵢ v)²` of the quadratic values
determines the full bilinear form, `g(v,w) = ∑ᵢ λᵢ·(yᵢ v)·(yᵢ w)`. -/
theorem toForm_eq_sum_of_diag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2) (v w : V) :
    g.toForm v w = ∑ i, eig i * (b.repr v i : ℂ) * (b.repr w i : ℂ) := by
  have h1 := hdiag (v + w)
  simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, Complex.ofReal_add] at h1
  have hexp : ∑ i, eig i * ((b.repr v i : ℂ) + (b.repr w i : ℂ)) ^ 2
      = (∑ i, eig i * (b.repr v i : ℂ) ^ 2)
        + (∑ i, eig i * (b.repr w i : ℂ) ^ 2)
        + 2 * ∑ i, eig i * (b.repr v i : ℂ) * (b.repr w i : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linear_combination h1 / 2 + hexp / 2 - hdiag v / 2 - hdiag w / 2
    + g.symmetric' v w / 2

/-- On a diagonalizing basis the Gram matrix of `g` is `Matrix.diagonal eig`: the diagonalizing
basis is `g`-orthogonal with the `λᵢ` on the diagonal. -/
theorem gram_eq_diagonal_of_diag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2) :
    Matrix.of (fun i j => g.toForm (b i) (b j)) = Matrix.diagonal eig := by
  ext i j
  rw [Matrix.of_apply, toForm_eq_sum_of_diag g hdiag, Matrix.diagonal_apply,
    Finset.sum_eq_single i (fun k _ hk => by
      simp [Module.Basis.repr_self, Finsupp.single_apply, Ne.symm hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  by_cases hij : i = j
  · subst hij
    simp [Module.Basis.repr_self]
  · simp [Module.Basis.repr_self, hij]

/-- **Change of real basis for the Gram matrix**: `M_b = Pᵀ·(M_c·P)` with `P` the (complexified)
real change-of-basis matrix. The general-basis version of the computation inside
`volume_element_positive`. -/
theorem gramMatrix_basisChange (g : AllowableComplexMetric V)
    (b c : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    Matrix.of (fun i j => g.toForm (b i) (b j))
      = (Complex.ofRealHom.mapMatrix (c.toMatrix b)).transpose
          * (Matrix.of (fun i j => g.toForm (c i) (c j))
            * Complex.ofRealHom.mapMatrix (c.toMatrix b)) := by
  ext i j
  have expand1 : ∀ w : V,
      g.toForm (b i) w = ∑ k, (c.repr (b i) k : ℂ) * g.toForm (c k) w := by
    intro w
    conv_lhs => rw [show b i = ∑ k, c.repr (b i) k • c k from (c.sum_repr (b i)).symm]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_smul, LinearMap.smul_apply, Complex.real_smul]
  have expand2 : ∀ k,
      g.toForm (c k) (b j) = ∑ l, (c.repr (b j) l : ℂ) * g.toForm (c k) (c l) := by
    intro k
    conv_lhs => rw [show b j = ∑ l, c.repr (b j) l • c l from (c.sum_repr (b j)).symm]
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, Complex.real_smul]
  rw [Matrix.of_apply, expand1 (b j), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expand2 k, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Module.Basis.toMatrix_apply, Complex.ofRealHom_eq_coe]
  ring

/-- The determinant of the Gram matrix of `g` in the canonical REAL basis `Module.finBasis ℝ V`:
KS's `det g` computed in a real coframe (KSTeX 126). A real change of basis multiplies it by a
positive real square (`detGramReal_welldef`) — the twisted-line ambiguity — so "off the
non-positive real axis" and the principal square root are well-defined for it. -/
noncomputable def detGramReal (g : AllowableComplexMetric V) : ℂ :=
  (Matrix.of fun i j =>
    g.toForm (Module.finBasis ℝ V i) (Module.finBasis ℝ V j)).det

/-- **Well-definedness of the real-coframe determinant.** Two real bases give Gram determinants
differing by a positive real factor (the square of the real change-of-basis determinant), under
which "not negative real" and the sign of `Re √·` are invariant. -/
theorem detGramReal_welldef (g : AllowableComplexMetric V)
    (b c : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    ∃ r : ℝ, 0 < r ∧
      (Matrix.of fun i j => g.toForm (b i) (b j)).det
        = (r : ℂ) * (Matrix.of fun i j => g.toForm (c i) (c j)).det := by
  refine ⟨(c.toMatrix b).det ^ 2, ?_, ?_⟩
  · refine sq_pos_of_ne_zero ?_
    have h1 : c.toMatrix b * b.toMatrix c = 1 := by
      rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
    exact left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, h1, Matrix.det_one])
  · have hP : (Complex.ofRealHom.mapMatrix (c.toMatrix b)).det
        = ((c.toMatrix b).det : ℂ) := by
      rw [← RingHom.map_det, Complex.ofRealHom_eq_coe]
    rw [gramMatrix_basisChange g b c, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hP]
    push_cast
    ring

/-- KS's first allowability condition (KSTeX 126) for the real-coframe determinant: it is not
real and negative. Direct from `volume_element_positive` at the canonical real basis. -/
theorem detGramReal_not_neg_real (g : AllowableComplexMetric V) :
    ¬ ((detGramReal g).im = 0 ∧ (detGramReal g).re < 0) := by
  obtain ⟨h, -⟩ := volume_element_positive g (Module.finBasis ℝ V)
  exact h

/-- The real-coframe determinant admits a principal square root (positive real part): KSTeX 126,
"we choose `(det g)^{1/2}` to have positive real part". From `volume_element_positive`. -/
theorem detGramReal_exists_principal_sqrt (g : AllowableComplexMetric V) :
    ∃ w : ℂ, w ^ 2 = detGramReal g ∧ 0 < w.re := by
  obtain ⟨-, h⟩ := volume_element_positive g (Module.finBasis ℝ V)
  exact h

/-- `(det g)^{1/2}`: THE principal square root (positive real part) of the real-coframe
determinant `detGramReal` — the normalizing factor of KS's `vol_g = (det g)^{1/2}|dx|` read
against a real coframe (KS paper (3), KSTeX 126). The principal branch exists precisely because
the radicand is a real-coframe determinant (`volume_element_positive`); it is unique
(`detSqrtReal_eq_of_sq`). -/
noncomputable def detSqrtReal (g : AllowableComplexMetric V) : ℂ :=
  (detGramReal_exists_principal_sqrt g).choose

/-- **`detSqrtReal` is a square root of the real-coframe determinant** (float-free tie). -/
theorem detSqrtReal_sq (g : AllowableComplexMetric V) :
    detSqrtReal g ^ 2 = detGramReal g :=
  (detGramReal_exists_principal_sqrt g).choose_spec.1

/-- **`detSqrtReal` is the principal branch**: its real part is positive (KSTeX 126). This is
the branch condition that is provable on a real coframe and false for the finBasis-of-`ℂ⊗V`
radicand of `detSqrt`. -/
theorem detSqrtReal_re_pos (g : AllowableComplexMetric V) : 0 < (detSqrtReal g).re :=
  (detGramReal_exists_principal_sqrt g).choose_spec.2

theorem detSqrtReal_ne_zero (g : AllowableComplexMetric V) : detSqrtReal g ≠ 0 := by
  intro h
  have hre := detSqrtReal_re_pos g
  rw [h] at hre
  simp at hre

/-- A complex number has at most one square root with positive real part (the two roots differ
by a sign, which flips the real part). Pins `detSqrtReal` uniquely. -/
theorem sq_eq_sq_re_pos_unique {w u : ℂ} (hw : 0 < w.re) (hu : 0 < u.re)
    (h : w ^ 2 = u ^ 2) : w = u := by
  have hfac : (w - u) * (w + u) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact sub_eq_zero.mp h1
  · have hwu : w = -u := eq_neg_of_add_eq_zero_left h1
    rw [hwu, Complex.neg_re] at hw
    linarith

/-- Any square root of `detGramReal g` with positive real part is `detSqrtReal g`. -/
theorem detSqrtReal_eq_of_sq (g : AllowableComplexMetric V) {u : ℂ} (hu : 0 < u.re)
    (h : u ^ 2 = detGramReal g) : detSqrtReal g = u :=
  sq_eq_sq_re_pos_unique (detSqrtReal_re_pos g) hu (by rw [detSqrtReal_sq g, h])

/-- **Diagonal factorization of the real-coframe determinant.** For any diagonalization
`(b, eig)` of `g`, `detGramReal g = r·∏ᵢ λᵢ` with `r > 0` real (the square of the
change-of-basis determinant to the canonical basis). So `detSqrtReal g` squares to a positive
real multiple of `∏ᵢ λᵢ` — KS's `(λ₁⋯λ_d)^{1/2}` up to the twisted-line ambiguity. -/
theorem detGramReal_eq_prod_of_diag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2) :
    ∃ r : ℝ, 0 < r ∧ detGramReal g = (r : ℂ) * ∏ i, eig i := by
  obtain ⟨r, hr, heq⟩ := detGramReal_welldef g (Module.finBasis ℝ V) b
  refine ⟨r, hr, ?_⟩
  calc detGramReal g
      = (r : ℂ) * (Matrix.of fun i j => g.toForm (b i) (b j)).det := heq
    _ = (r : ℂ) * ∏ i, eig i := by
        rw [gram_eq_diagonal_of_diag g hdiag, Matrix.det_diagonal]

/-- **The vector↔covector eigenvalue translation (KSTeX 202).** If `w² = r·∏ᵢλᵢ` with `r > 0`
real (as `detSqrtReal g` does, by `detGramReal_eq_prod_of_diag`), then for every blade-index set
`S` the normalized vector-side blade value `w⁻¹·∏_{i∈S}λᵢ` is the positive multiple `r⁻¹` of
KS's covector-side value at the complementary blade, `w·∏_{i∉S}λᵢ⁻¹` — the
`(λ₁⋯λ_d)^{1/2}·∏_{i∈Sᶜ}λᵢ⁻¹` of KSTeX 202 evaluated on `e*_{Sᶜ}`. In particular the two real
parts have the same sign (`normalized_blade_re_pos_iff`): positivity of the encoded vector-side
form and of KS's covector-side form agree blade by blade. -/
theorem normalized_blade_eq_covector {d : ℕ} {w : ℂ} {r : ℝ} {eig : Fin d → ℂ}
    (hr : 0 < r) (hne : ∀ i, eig i ≠ 0) (hw : w ^ 2 = (r : ℂ) * ∏ i, eig i)
    (S : Finset (Fin d)) :
    w⁻¹ * ∏ i ∈ S, eig i = (r : ℂ)⁻¹ * (w * ∏ i ∈ Sᶜ, (eig i)⁻¹) := by
  have hprodS : (∏ i ∈ S, eig i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hprodSc : (∏ i ∈ Sᶜ, eig i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    rw [← Finset.prod_mul_prod_compl S eig] at hw
    exact mul_ne_zero hr' (mul_ne_zero hprodS hprodSc) (by simpa using hw.symm)
  have hsplit : (∏ i ∈ S, eig i) * ∏ i ∈ Sᶜ, eig i = ∏ i, eig i :=
    Finset.prod_mul_prod_compl S eig
  rw [Finset.prod_inv_distrib]
  have key : (w⁻¹ * ∏ i ∈ S, eig i) * (w * ((r : ℂ) * ∏ i ∈ Sᶜ, eig i)) = w ^ 2 := by
    rw [show (w⁻¹ * ∏ i ∈ S, eig i) * (w * ((r : ℂ) * ∏ i ∈ Sᶜ, eig i))
        = (w⁻¹ * w) * ((r : ℂ) * ((∏ i ∈ S, eig i) * ∏ i ∈ Sᶜ, eig i)) from by ring,
      inv_mul_cancel₀ hw0, one_mul, hsplit, hw]
  have key2 : ((r : ℂ)⁻¹ * (w * (∏ i ∈ Sᶜ, eig i)⁻¹))
      * (w * ((r : ℂ) * ∏ i ∈ Sᶜ, eig i)) = w ^ 2 := by
    rw [show ((r : ℂ)⁻¹ * (w * (∏ i ∈ Sᶜ, eig i)⁻¹)) * (w * ((r : ℂ) * ∏ i ∈ Sᶜ, eig i))
        = (((r : ℂ)⁻¹ * (r : ℂ)) * ((∏ i ∈ Sᶜ, eig i)⁻¹ * ∏ i ∈ Sᶜ, eig i)) * (w * w)
        from by ring,
      inv_mul_cancel₀ hr', inv_mul_cancel₀ hprodSc, one_mul, one_mul, ← pow_two]
  exact mul_right_cancel₀ (mul_ne_zero hw0 (mul_ne_zero hr' hprodSc))
    (key.trans key2.symm)

/-- Blade-wise sign agreement: the encoded vector-side value and KS's covector-side value have
positive real part together (corollary of `normalized_blade_eq_covector`). -/
theorem normalized_blade_re_pos_iff {d : ℕ} {w : ℂ} {r : ℝ} {eig : Fin d → ℂ}
    (hr : 0 < r) (hne : ∀ i, eig i ≠ 0) (hw : w ^ 2 = (r : ℂ) * ∏ i, eig i)
    (S : Finset (Fin d)) :
    0 < (w⁻¹ * ∏ i ∈ S, eig i).re ↔ 0 < (w * ∏ i ∈ Sᶜ, (eig i)⁻¹).re := by
  rw [normalized_blade_eq_covector hr hne hw S, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  constructor
  · intro h
    have hmul := mul_pos hr h
    rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hmul
  · exact fun h => mul_pos (inv_pos.mpr hr) h

/-- **`detSqrtReal`-level translation (the proved faithfulness tie for `IsAllowableHodge`).**
For any diagonalization `(b, eig)` of `g`, the encoded blade value
`(detSqrtReal g)⁻¹·∏_{i∈S}λᵢ` is a positive real multiple of KS's covector value
`(det g)^{1/2}·∏_{i∈Sᶜ}λᵢ⁻¹` (KSTeX 202). -/
theorem detSqrtReal_blade_eq_covector (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ} (hne : ∀ i, eig i ≠ 0)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (S : Finset (Fin (Module.finrank ℝ V))) :
    ∃ r : ℝ, 0 < r ∧
      (detSqrtReal g)⁻¹ * ∏ i ∈ S, eig i
        = (r : ℂ)⁻¹ * (detSqrtReal g * ∏ i ∈ Sᶜ, (eig i)⁻¹) := by
  obtain ⟨r, hr, heq⟩ := detGramReal_eq_prod_of_diag g hdiag
  exact ⟨r, hr, normalized_blade_eq_covector hr hne (by rw [detSqrtReal_sq g, heq]) S⟩

/-! ### Definition 2.1 of [KS] (Hodge-star positivity)

KS paper Definition 2.1 (KSTeX 140–142): the complex metric `g` on the real space `V` is
allowable iff, for every degree `p`, the real part of the quadratic form `α ↦ α ∧ ⋆_g α` on the
real exterior power `⋀ᵖ(V*)`, valued in the twisted line `|⋀ᵈ(V*)|_ℂ`, is positive-definite.
The positivity is read against the REAL positive volume ray of the twisted line (KSTeX 130–131:
"an element of the real part of the line is positive if it is a positive volume-element"), NOT
against `vol_g`; on a diagonalizing basis the blade eigenvalue is
`(λ₁⋯λ_d)^{1/2}·∏_{i∈S}λᵢ⁻¹` (KSTeX 202) — the `(det g)^{1/2}` of `vol_g` stays in the
eigenvalue. Two conventions translate KS's form to the vector-side machinery of this file:

* **orientation of the exterior power**: KS's form lives on `p`-covectors with the dual metric
  (blade values `∏_{i∈S}λᵢ⁻¹`), while `formC`/`realExtPow` live on `p`-vectors (blade values
  `∏_{i∈S}λᵢ`); the two sides are mirrored by `S ↔ Sᶜ`;
* **normalization**: the `(det g)^{1/2}` is the principal square root of the real-coframe Gram
  determinant (`detGramReal`/`detSqrtReal` above), well-defined up to the positive real
  twisted-line ambiguity (`detGramReal_welldef`).

The encoded form is therefore `α ↦ (detSqrtReal g)⁻¹ · g_p^ℂ(α, α)` on real `p`-vectors, whose
blade values are positive-real multiples of KS's covector values at the complementary blade —
proved, not asserted, in `detSqrtReal_blade_eq_covector`/`normalized_blade_re_pos_iff`. -/

/-- The `ιMulti` alternating map of `V_ℂ`, with scalars restricted from `ℂ` to `ℝ`. (Mathlib ships
`MultilinearMap.restrictScalars` but not the alternating-map version; the alternating property is
inherited unchanged since the underlying function is the same.) -/
noncomputable def ιMultiRestrict (p : ℕ) :
    (ℂ ⊗[ℝ] V) [⋀^Fin p]→ₗ[ℝ] (⋀[ℂ]^p (ℂ ⊗[ℝ] V)) where
  toMultilinearMap := (exteriorPower.ιMulti ℂ p).toMultilinearMap.restrictScalars ℝ
  map_eq_zero_of_eq' v _i _j hv hij := (exteriorPower.ιMulti ℂ p).map_eq_zero_of_eq v hv hij

/-- The **real `p`-forms** included into the complex exterior power `⋀ᵖ(V_ℂ)`: the ℝ-linear map
`⋀[ℝ]^p V →ₗ[ℝ] ⋀[ℂ]^p (ℂ⊗V)` extending `v ↦ 1 ⊗ v` (so on decomposables `v₁ ∧ ⋯ ∧ v_p ↦
(1⊗v₁) ∧ ⋯ ∧ (1⊗v_p)`). This is KS's `⋀ᵖ(V*)`, the real forms sitting inside the complexification on
which `g_p^ℂ` and `⋆_g` live. -/
noncomputable def realExtPow (p : ℕ) : ⋀[ℝ]^p V →ₗ[ℝ] ⋀[ℂ]^p (ℂ ⊗[ℝ] V) :=
  exteriorPower.alternatingMapLinearEquiv
    ((ιMultiRestrict (V := V) p).compLinearMap ((TensorProduct.mk ℝ ℂ V) 1))

omit [FiniteDimensional ℝ V] in
/-- **`realExtPow` maps real blades to complex blades** (float-free tie of `realExtPow` to its
defining extension of `v ↦ 1 ⊗ v`): on decomposables,
`realExtPow p (v₁ ∧ ⋯ ∧ v_p) = (1⊗v₁) ∧ ⋯ ∧ (1⊗v_p)`. -/
theorem realExtPow_ιMulti (p : ℕ) (v : Fin p → V) :
    realExtPow p (exteriorPower.ιMulti ℝ p v)
      = exteriorPower.ιMulti ℂ p (fun i => (1 : ℂ) ⊗ₜ[ℝ] v i) := by
  unfold realExtPow
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **Definition 2.1 of [KS]** (Hodge-star positivity; KSTeX 140–142). `g` is allowable iff for
all degrees `p`, the real part of the quadratic form `α ↦ α ∧ ⋆_g α` on `⋀ᵖ(V*)`, read against
the real positive volume ray of the twisted line `|⋀ᵈ(V*)|_ℂ` (KSTeX 130–131), is
positive-definite. Encoded on real `p`-vectors via `realExtPow`, with the real-coframe principal
normalization `(detSqrtReal g)⁻¹` carrying the `(det g)^{1/2}` phase that reading against the
real volume ray retains: the blade values of `(detSqrtReal g)⁻¹ · g_p^ℂ(·,·)` are positive-real
multiples of KS's `(λ₁⋯λ_d)^{1/2}·∏λᵢ⁻¹` (KSTeX 202) at the complementary blade — the proved
translation `detSqrtReal_blade_eq_covector` (see the section header for the two conventions).

Its equivalence with the working (angle-condition) definition is KS paper Theorem 2.2
(`ComplexMetrics/Equivalence.lean`), deferred pending real simultaneous diagonalization. -/
def IsAllowableHodge (g : AllowableComplexMetric V) : Prop :=
  ∀ (p : ℕ) (α : ⋀[ℝ]^p V), α ≠ 0 →
    0 < ((detSqrtReal g)⁻¹ * formC g p (realExtPow p α) (realExtPow p α)).re

/-! ### The forward direction of KS Theorem 2.2: angle condition ⇒ Definition 2.1

KS's proof (KSTeX 199–205), forward half: with `g` diagonalized as `∑ λᵢ yᵢ²`, the form
`α ↦ α ∧ ⋆_g α` is diagonal on the basis blades with values of argument
`½(∑_{i∈S} arg λᵢ − ∑_{i∉S} arg λᵢ)` (KSTeX 204), which lies in `(−π/2, π/2)` for every `S`
as soon as `∑|arg λᵢ| < π` — the triangle inequality (`angle_sum_subset_bound`). The converse
(the maximum over `S` is attained at `S = {i : θᵢ ≥ 0}`) belongs to the reverse direction and
is not needed here. -/

/-- **The combinatorial half of KS condition (4)** (easy direction, KSTeX 204–205): if
`∑ᵢ|θᵢ| < π` then for every subset `S` the signed sum `∑_{i∈S}θᵢ − ∑_{i∉S}θᵢ` has absolute
value `< π` (triangle inequality). -/
theorem angle_sum_subset_bound {d : ℕ} (θ : Fin d → ℝ) (S : Finset (Fin d))
    (h : ∑ i, |θ i| < Real.pi) :
    |(∑ i ∈ S, θ i) - ∑ i ∈ Sᶜ, θ i| < Real.pi := by
  calc |(∑ i ∈ S, θ i) - ∑ i ∈ Sᶜ, θ i|
      = |(∑ i ∈ S, θ i) + -(∑ i ∈ Sᶜ, θ i)| := by rw [sub_eq_add_neg]
    _ ≤ |∑ i ∈ S, θ i| + |-(∑ i ∈ Sᶜ, θ i)| := abs_add_le _ _
    _ = |∑ i ∈ S, θ i| + |∑ i ∈ Sᶜ, θ i| := by rw [abs_neg]
    _ ≤ (∑ i ∈ S, |θ i|) + ∑ i ∈ Sᶜ, |θ i| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, |θ i| := Finset.sum_add_sum_compl S _
    _ < Real.pi := h

/-- Polar form of a finite product: `∏_{i∈S} zᵢ = (∏_{i∈S}‖zᵢ‖)·exp(i·∑_{i∈S} arg zᵢ)`.
(Unconditional: each factor is `Complex.norm_mul_exp_arg_mul_I`.) -/
theorem prod_eq_norm_mul_exp_sum_arg {d : ℕ} (z : Fin d → ℂ) (S : Finset (Fin d)) :
    ∏ i ∈ S, z i
      = ((∏ i ∈ S, ‖z i‖ : ℝ) : ℂ)
        * Complex.exp ((↑(∑ i ∈ S, Complex.arg (z i)) : ℂ) * Complex.I) := by
  have hexpsum : ∑ i ∈ S, (↑(Complex.arg (z i)) : ℂ) * Complex.I
      = (↑(∑ i ∈ S, Complex.arg (z i)) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul]
  calc ∏ i ∈ S, z i
      = ∏ i ∈ S, ((‖z i‖ : ℂ) * Complex.exp ((↑(Complex.arg (z i)) : ℂ) * Complex.I)) :=
        Finset.prod_congr rfl fun i _ => (Complex.norm_mul_exp_arg_mul_I _).symm
    _ = (∏ i ∈ S, (‖z i‖ : ℂ))
          * ∏ i ∈ S, Complex.exp ((↑(Complex.arg (z i)) : ℂ) * Complex.I) :=
        Finset.prod_mul_distrib
    _ = _ := by rw [← Complex.exp_sum, hexpsum, Complex.ofReal_prod]

/-- **Positivity of the normalized blade values** (the per-`S` step of KS's Theorem-2.2 proof,
KSTeX 202–205, forward half): for a diagonalization `(b, eig)` of `g` satisfying the angle
condition, every normalized blade value `(detSqrtReal g)⁻¹·∏_{i∈S}λᵢ` has positive real part.
Its argument is `½(∑_{i∈S}θᵢ − ∑_{i∉S}θᵢ) ∈ (−π/2, π/2)` by `angle_sum_subset_bound`; the
principal root is identified in polar form via `detSqrtReal_eq_of_sq`, with no arg-of-product
computation (`prod_eq_norm_mul_exp_sum_arg` carries the sums). -/
theorem blade_re_pos (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ} (hAC : AngleCondition eig)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (S : Finset (Fin (Module.finrank ℝ V))) :
    0 < ((detSqrtReal g)⁻¹ * ∏ i ∈ S, eig i).re := by
  obtain ⟨r, hr, hdet⟩ := detGramReal_eq_prod_of_diag g hdiag
  have hnorm_pos : ∀ i, (0 : ℝ) < ‖eig i‖ := fun i => norm_pos_iff.mpr (hAC.nonzero i)
  obtain ⟨hSlo, hShi⟩ := abs_lt.mp
    (lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) hAC.sum_arg_lt_pi)
  set c₀ : ℝ := Real.sqrt r * ∏ i, Real.sqrt ‖eig i‖ with hc₀def
  have hc₀pos : 0 < c₀ :=
    mul_pos (Real.sqrt_pos.mpr hr)
      (Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hnorm_pos i))
  -- the principal root in polar form
  have hwid : detSqrtReal g
      = (c₀ : ℂ) * Complex.exp ((↑((∑ i, Complex.arg (eig i)) / 2) : ℂ) * Complex.I) := by
    apply detSqrtReal_eq_of_sq
    · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      exact mul_pos hc₀pos
        (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
    · have hc₀sq : c₀ ^ 2 = r * ∏ i, ‖eig i‖ := by
        rw [hc₀def, mul_pow, Real.sq_sqrt hr.le, ← Finset.prod_pow]
        congr 1
        exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (norm_nonneg _)
      rw [mul_pow, ← Complex.ofReal_pow, hc₀sq,
        show (Complex.exp ((↑((∑ i, Complex.arg (eig i)) / 2) : ℂ) * Complex.I)) ^ 2
            = Complex.exp ((↑(∑ i, Complex.arg (eig i)) : ℂ) * Complex.I) from by
          rw [pow_two, ← Complex.exp_add]
          congr 1
          push_cast
          ring,
        hdet, prod_eq_norm_mul_exp_sum_arg]
      push_cast
      ring
  -- the value in polar form
  have hhalf : (∑ i ∈ S, Complex.arg (eig i)) - (∑ i, Complex.arg (eig i)) / 2
      = ((∑ i ∈ S, Complex.arg (eig i)) - ∑ i ∈ Sᶜ, Complex.arg (eig i)) / 2 := by
    have hsplit := Finset.sum_add_sum_compl S (fun i => Complex.arg (eig i))
    linarith
  have hval : (detSqrtReal g)⁻¹ * ∏ i ∈ S, eig i
      = ((c₀⁻¹ * ∏ i ∈ S, ‖eig i‖ : ℝ) : ℂ)
        * Complex.exp
            ((↑(((∑ i ∈ S, Complex.arg (eig i)) - ∑ i ∈ Sᶜ, Complex.arg (eig i)) / 2) : ℂ)
              * Complex.I) := by
    rw [hwid, prod_eq_norm_mul_exp_sum_arg, mul_inv, ← Complex.exp_neg, ← Complex.ofReal_inv,
      show ((c₀⁻¹ : ℝ) : ℂ)
            * Complex.exp (-((↑((∑ i, Complex.arg (eig i)) / 2) : ℂ) * Complex.I))
            * (((∏ i ∈ S, ‖eig i‖ : ℝ) : ℂ)
              * Complex.exp ((↑(∑ i ∈ S, Complex.arg (eig i)) : ℂ) * Complex.I))
          = ((c₀⁻¹ * ∏ i ∈ S, ‖eig i‖ : ℝ) : ℂ)
            * (Complex.exp (-((↑((∑ i, Complex.arg (eig i)) / 2) : ℂ) * Complex.I))
              * Complex.exp ((↑(∑ i ∈ S, Complex.arg (eig i)) : ℂ) * Complex.I)) from by
        push_cast
        ring,
      ← Complex.exp_add]
    congr 2
    rw [← hhalf]
    push_cast
    ring
  rw [hval, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp
    (angle_sum_subset_bound (fun i => Complex.arg (eig i)) S hAC.sum_arg_lt_pi)
  exact mul_pos
    (mul_pos (inv_pos.mpr hc₀pos) (Finset.prod_pos fun i _ => hnorm_pos i))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

/-- Gram value of complexified diagonalizing blades, diagonal case: for an injective reindex
`e` of the diagonalizing basis, `g_p^ℂ` on the blade `(1⊗b_{e 0}) ∧ ⋯ ∧ (1⊗b_{e (p−1)})` is
`∏ᵢ λ_{e i}` (the diagonal Gram determinant, computed at the `tmul` level via
`gc_apply_tmul` + `gram_eq_diagonal_of_diag`). -/
theorem formC_tmul_blade_diag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    {p : ℕ} {e : Fin p → Fin (Module.finrank ℝ V)} (he : Function.Injective e) :
    formC g p (exteriorPower.ιMulti ℂ p (fun i => (1 : ℂ) ⊗ₜ[ℝ] b (e i)))
        (exteriorPower.ιMulti ℂ p (fun i => (1 : ℂ) ⊗ₜ[ℝ] b (e i)))
      = ∏ i, eig (e i) := by
  rw [formC_apply_ιMulti]
  have hM : (Matrix.of fun i j => gc g ((1 : ℂ) ⊗ₜ[ℝ] b (e j)) ((1 : ℂ) ⊗ₜ[ℝ] b (e i)))
      = Matrix.diagonal (fun i => eig (e i)) := by
    ext i j
    have hentry := congrFun (congrFun (gram_eq_diagonal_of_diag g hdiag) (e j)) (e i)
    rw [Matrix.of_apply] at hentry
    rw [Matrix.of_apply, gc_apply_tmul, hentry, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij, if_neg (show ¬ e j = e i from fun h => hij ((he h).symm))]
  rw [hM, Matrix.det_diagonal]

/-- Gram value of complexified diagonalizing blades, separated case: if some `e' i₀` avoids the
range of `e`, the Gram determinant has a zero row and `g_p^ℂ` vanishes on the pair of blades. -/
theorem formC_tmul_blade_offdiag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    {p : ℕ} {e e' : Fin p → Fin (Module.finrank ℝ V)}
    (hsep : ∃ i₀, ∀ j, e j ≠ e' i₀) :
    formC g p (exteriorPower.ιMulti ℂ p (fun i => (1 : ℂ) ⊗ₜ[ℝ] b (e i)))
        (exteriorPower.ιMulti ℂ p (fun i => (1 : ℂ) ⊗ₜ[ℝ] b (e' i)))
      = 0 := by
  obtain ⟨i₀, hi₀⟩ := hsep
  rw [formC_apply_ιMulti]
  apply Matrix.det_eq_zero_of_row_eq_zero i₀
  intro j
  have hentry := congrFun (congrFun (gram_eq_diagonal_of_diag g hdiag) (e j)) (e' i₀)
  rw [Matrix.of_apply] at hentry
  rw [Matrix.of_apply, gc_apply_tmul, hentry, Matrix.diagonal_apply, if_neg (hi₀ j)]

/-- **Diagonal expansion of the quadratic form on real forms** (KS Theorem-2.2 proof, KSTeX
201–202, in vector-side form): expanding a real `p`-form `α` over the exterior powers of the
diagonalizing basis, `g_p^ℂ(α, α) = ∑_S a_S²·∏_{i∈S}λᵢ` with real coordinates `a_S` (the
off-diagonal Gram values vanish). -/
theorem formC_realExtPow_diag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (p : ℕ) (α : ⋀[ℝ]^p V) :
    formC g p (realExtPow p α) (realExtPow p α)
      = ∑ T : Set.powersetCard (Fin (Module.finrank ℝ V)) p,
          ((b.exteriorPower p).repr α T : ℂ) ^ 2
            * ∏ j ∈ (T : Finset (Fin (Module.finrank ℝ V))), eig j := by
  classical
  set Y : Set.powersetCard (Fin (Module.finrank ℝ V)) p → ⋀[ℂ]^p (ℂ ⊗[ℝ] V) := fun T =>
    exteriorPower.ιMulti ℂ p
      (fun i => (1 : ℂ) ⊗ₜ[ℝ] b (Set.powersetCard.ofFinEmbEquiv.symm T i)) with hY
  have hexpand : realExtPow p α = ∑ T, (b.exteriorPower p).repr α T • Y T := by
    conv_lhs => rw [← (b.exteriorPower p).sum_repr α]
    rw [map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_smul, exteriorPower_basis_apply_eq, realExtPow_ιMulti]
    rfl
  have hgram_diag : ∀ T : Set.powersetCard (Fin (Module.finrank ℝ V)) p,
      formC g p (Y T) (Y T) = ∏ j ∈ (T : Finset (Fin (Module.finrank ℝ V))), eig j := by
    intro T
    have h1 : formC g p (Y T) (Y T)
        = ∏ i, eig (Set.powersetCard.ofFinEmbEquiv.symm T i) :=
      formC_tmul_blade_diag g hdiag (EmbeddingLike.injective _)
    have himg : Finset.image (⇑(Set.powersetCard.ofFinEmbEquiv.symm T)) Finset.univ
        = (T : Finset (Fin (Module.finrank ℝ V))) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).mp ⟨i, rfl⟩
      · intro hx
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T x).mpr hx
    rw [h1, ← himg, Finset.prod_image fun i _ j _ h => EmbeddingLike.injective _ h]
  have hgram_off : ∀ T T' : Set.powersetCard (Fin (Module.finrank ℝ V)) p,
      T ≠ T' → formC g p (Y T) (Y T') = 0 := by
    intro T T' hTT'
    refine formC_tmul_blade_offdiag g hdiag ?_
    have hsub : ¬ ((T' : Finset (Fin (Module.finrank ℝ V)))
        ⊆ (T : Finset (Fin (Module.finrank ℝ V)))) := by
      intro hts
      exact hTT' (Subtype.ext (Finset.eq_of_subset_of_card_le hts (by simp)).symm)
    obtain ⟨x, hxT', hxT⟩ := Finset.not_subset.mp hsub
    obtain ⟨i₀, hi₀⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T' x).mpr hxT'
    refine ⟨i₀, fun j h => ?_⟩
    rw [hi₀] at h
    exact hxT (h ▸ (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T _).mp ⟨j, rfl⟩)
  have expand1 : ∀ z, formC g p (realExtPow p α) z
      = ∑ T, ((b.exteriorPower p).repr α T : ℂ) * formC g p (Y T) z := by
    intro z
    conv_lhs => rw [hexpand]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun T _ => by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, Complex.real_smul]
  have expand2 : ∀ T, formC g p (Y T) (realExtPow p α)
      = ∑ T', ((b.exteriorPower p).repr α T' : ℂ) * formC g p (Y T) (Y T') := by
    intro T
    conv_lhs => rw [hexpand]
    rw [map_sum]
    exact Finset.sum_congr rfl fun T' _ => by
      rw [LinearMap.map_smul_of_tower, Complex.real_smul]
  rw [expand1 (realExtPow p α)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [expand2 T, Finset.mul_sum, Finset.sum_eq_single T]
  · rw [hgram_diag T]
    ring
  · intro T' _ hT'
    rw [hgram_off T T' (Ne.symm hT'), mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ T) h

/-- **The forward direction of KS Theorem 2.2** (KSTeX 199–205, the half provable without real
simultaneous diagonalization): every allowable complex metric — i.e. every `g` satisfying the
angle condition, which `AllowableComplexMetric` carries as `angle_cond` — satisfies KS
Definition 2.1, `IsAllowableHodge g`. The quadratic form is a nonnegative real combination of
the normalized blade values (`formC_realExtPow_diag`), each of positive real part
(`blade_re_pos`), with a strictly positive coefficient since `α ≠ 0`. The REVERSE direction
(Definition 2.1 ⇒ angle condition) requires stating Definition 2.1 for a bare symmetric
nondegenerate ℂ-valued form (no angle condition assumed), a type this development does not yet
have; it is deferred. -/
theorem isAllowableHodge (g : AllowableComplexMetric V) : IsAllowableHodge g := by
  classical
  obtain ⟨b, eig, hAC, hdiag⟩ := g.angle_cond
  intro p α hα
  rw [formC_realExtPow_diag g hdiag p α, Finset.mul_sum, Complex.re_sum]
  have hrepr : (b.exteriorPower p).repr α ≠ 0 :=
    fun h => hα ((b.exteriorPower p).repr.map_eq_zero_iff.mp h)
  obtain ⟨T₀, hT₀⟩ := Finsupp.ne_iff.mp hrepr
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hT₀
  refine Finset.sum_pos' (fun T _ => ?_) ⟨T₀, Finset.mem_univ _, ?_⟩
  · rw [show (detSqrtReal g)⁻¹
          * (((b.exteriorPower p).repr α T : ℂ) ^ 2
            * ∏ j ∈ (T : Finset (Fin (Module.finrank ℝ V))), eig j)
        = ((((b.exteriorPower p).repr α T : ℝ) ^ 2 : ℝ) : ℂ)
          * ((detSqrtReal g)⁻¹ * ∏ j ∈ (T : Finset (Fin (Module.finrank ℝ V))), eig j) from by
        push_cast
        ring,
      Complex.re_ofReal_mul]
    exact mul_nonneg (sq_nonneg _) (blade_re_pos g hAC hdiag _).le
  · rw [show (detSqrtReal g)⁻¹
          * (((b.exteriorPower p).repr α T₀ : ℂ) ^ 2
            * ∏ j ∈ (T₀ : Finset (Fin (Module.finrank ℝ V))), eig j)
        = ((((b.exteriorPower p).repr α T₀ : ℝ) ^ 2 : ℝ) : ℂ)
          * ((detSqrtReal g)⁻¹ * ∏ j ∈ (T₀ : Finset (Fin (Module.finrank ℝ V))), eig j) from by
        push_cast
        ring,
      Complex.re_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero hT₀) (blade_re_pos g hAC hdiag _)

end Complexification

end KontsevichSegal.Hodge
