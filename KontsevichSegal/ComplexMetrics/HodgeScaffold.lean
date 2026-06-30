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

end Complexification

end KontsevichSegal.Hodge
