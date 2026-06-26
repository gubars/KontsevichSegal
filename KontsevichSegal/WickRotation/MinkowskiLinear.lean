/- The linear algebra of complexified Minkowski space: the foundation node
`found:minkowski-linear` of the Kontsevich-Segal blueprint (arXiv:2105.10161).

This is the linear-algebra half of `MinkowskiComplexGeometry` (the ambient geometry of the
closing vacuum-domain conjecture, `VacuumDomain.lean`), separated out and BUILT with a genuine
Mathlib model rather than assumed. The blueprint node `found:minkowski-linear` covers exactly the
fields `mC`, `bilin`, `Eucl`, `projE` of that class; the totally-real-submanifold half (the
`TotallyRealSub`/`tangentSpace`/`inducedForm` and the Wightman tube `Uk`) stays deferred, folded
into `found:real-analytic-complexification` and `found:scv-tube-domain`.

The CONTENT (KS Section 5, the traditional Minkowski-space treatment): real Minkowski space
`m = ℝ^{d-1,1}` with its Lorentzian form of signature `(d-1,1)`; its complexification
`m_C = m ⊗_ℝ ℂ = m ⊕ i·m`, with the ℂ-bilinear extension `bilin` of the real form; and the
Euclidean real subspace `E = ℝ^d` of the second splitting `m_C = E ⊕ i·E`, on which the ℂ-bilinear
form is real and positive definite. `E` is the Wick rotation of `m`: rotating the time axis by `i`
turns the mostly-plus Lorentzian form into the positive-definite Euclidean one.

`MinkowskiLinear` is the foundation class (the interface consumed by `MinkowskiComplexGeometry`); it
is genuinely inhabited by `MinkowskiModel.minkowskiLinear`, a concrete model on coordinate space
`Fin (n+2) → ℂ` (the `+2` pins the dimension `≥ 2`, so the form is genuinely indefinite: a timelike
AND a spacelike direction both exist). Every structural tie is proved from standard Mathlib linear
algebra:

* the complexified form is the base change of the real form (`bilin_real`: restriction to the real
  points `coeM` equals `realForm`), so `bilin` is not a free second form;
* `m_C = m ⊕ i·m` (`mc_span`) and `m_C = E ⊕ i·E` (`eucl_span`);
* the form is real and positive definite on `E` (`bilin_eucl_real`, `bilin_eucl_pos`) -- the Wick
  rotation `etaC i · (mu i)² = 1` cancels the signature on `E`;
* the form is genuinely Lorentzian: indefinite (`exists_timelike`, `exists_spacelike`) and
  nondegenerate (`realForm_nondegen`).

No `axiom` keyword, no `sorry`. -/

import KontsevichSegal.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace WickRotation

universe u

/-! ## The foundation class: complexified Minkowski linear algebra -/

/-- **Built foundation `found:minkowski-linear`: the linear algebra of complexified Minkowski
space.** Real Minkowski space `m = ℝ^{d-1,1}` with its Lorentzian form `realForm` of signature
`(d-1,1)`; the complexification `mC = m ⊗_ℝ ℂ` with the ℂ-bilinear base change `bilin` of
`realForm`; and the Euclidean real subspace `Eucl = ℝ^d` of `mC = Eucl ⊕ i·Eucl`, on which `bilin`
is real and positive definite. This is the interface that `MinkowskiComplexGeometry` extends; it is
realized by a genuine Mathlib model (`MinkowskiModel.minkowskiLinear`), not assumed. -/
class MinkowskiLinear where
  /-- Real Minkowski space `m = ℝ^{d-1,1}` (the real form on which `bilin` restricts to the
  Lorentzian form). -/
  m : Type u
  [macg : AddCommGroup m]
  [mmod : Module ℝ m]
  [mfin : FiniteDimensional ℝ m]
  /-- The real Lorentzian form on `m`, signature `(d-1,1)`. -/
  realForm : m →ₗ[ℝ] m →ₗ[ℝ] ℝ
  /-- The real form is symmetric. -/
  realForm_symm : ∀ x y, realForm x y = realForm y x
  /-- The real form is nondegenerate. -/
  realForm_nondegen : ∀ x, x ≠ 0 → ∃ y, realForm x y ≠ 0
  /-- There is a timelike vector (the `1` of signature `(d-1,1)`): the form is not
  positive definite. -/
  exists_timelike : ∃ x, realForm x x < 0
  /-- There is a spacelike vector (the `d-1` of signature `(d-1,1)`): the form is not
  negative definite. Together with `exists_timelike` this makes the form genuinely indefinite. -/
  exists_spacelike : ∃ x, 0 < realForm x x
  /-- Complexified Minkowski space `m_C = m ⊗_ℝ ℂ` (a complex vector space, ℂ-dimension `d`). -/
  mC : Type u
  [acg : AddCommGroup mC]
  [mod : Module ℂ mC]
  /-- The inclusion of the real points `m ↪ m_C`. -/
  coeM : m →ₗ[ℝ] mC
  /-- The real points include injectively. -/
  coeM_injective : Function.Injective coeM
  /-- `m_C = m ⊕ i·m`: every complex point is a real point plus `i` times a real point. Together
  with `bilin_real` and ℂ-bilinearity this pins `bilin` as the base change of `realForm`. -/
  mc_span : ∀ z : mC, ∃ x y : m, z = coeM x + Complex.I • coeM y
  /-- The ℂ-bilinear extension of the Minkowski form; `‖v‖² := bilin v v`. -/
  bilin : mC →ₗ[ℂ] mC →ₗ[ℂ] ℂ
  /-- The Minkowski form is symmetric. -/
  bilin_symm : ∀ v w, bilin v w = bilin w v
  /-- **Float-free restriction tie:** `bilin` restricted to the real points is `realForm`. -/
  bilin_real : ∀ x y : m, bilin (coeM x) (coeM y) = (realForm x y : ℂ)
  /-- The real Euclidean subspace `E = ℝ^d` of `m_C = E ⊕ iE` (where the observables live). -/
  Eucl : Type u
  [eacg : AddCommGroup Eucl]
  [emod : Module ℝ Eucl]
  /-- The inclusion `E ↪ m_C` of the Euclidean real subspace (the Wick rotation of `m`). -/
  coeEucl : Eucl →ₗ[ℝ] mC
  /-- The projection `m_C → E` along `iE` (a plain map; the surjectivity condition (ii) of `V̌_k`
  uses only the underlying function). -/
  projE : mC → Eucl
  /-- `projE` retracts `coeEucl`: `E` is genuinely a real slice of `m_C`. -/
  projE_coeEucl : ∀ e, projE (coeEucl e) = e
  /-- `projE` is the projection onto the `E`-component of `m_C = E ⊕ iE`
      (pins it as the canonical projection along `iE`; subsumes `projE_coeEucl` via `e' = 0`). -/
  projE_eucl_span : ∀ e e' : Eucl, projE (coeEucl e + Complex.I • coeEucl e') = e
  /-- `m_C = E ⊕ i·E`: the Euclidean splitting. -/
  eucl_span : ∀ z : mC, ∃ e e' : Eucl, z = coeEucl e + Complex.I • coeEucl e'
  /-- The form is real on `E` (the Wick rotation makes it Euclidean). -/
  bilin_eucl_real : ∀ e e' : Eucl, (bilin (coeEucl e) (coeEucl e')).im = 0
  /-- The form is positive definite on `E`. -/
  bilin_eucl_pos : ∀ e : Eucl, e ≠ 0 → 0 < (bilin (coeEucl e) (coeEucl e)).re

attribute [instance] MinkowskiLinear.macg MinkowskiLinear.mmod MinkowskiLinear.mfin
  MinkowskiLinear.acg MinkowskiLinear.mod MinkowskiLinear.eacg MinkowskiLinear.emod

/-! ## The concrete model

A genuine Mathlib model on coordinate space `Fin (n+2) → ℂ`, mostly-plus signature with the time
axis at index `0`. The dimension `d = n+2 ≥ 2` is pinned so that index `0` (timelike) and index `1`
(spacelike) both exist, making the form indefinite. -/

namespace MinkowskiModel

variable (n : ℕ)

/-- The Minkowski signature coefficients (real): `-1` at the time index `0`, `+1` on space. -/
def eta (i : Fin (n + 2)) : ℝ := if i = 0 then -1 else 1

/-- The Minkowski signature coefficients (complex). -/
def etaC (i : Fin (n + 2)) : ℂ := if i = 0 then -1 else 1

/-- The Wick-rotation coefficients: multiply the time coordinate by `i`, leave space alone. -/
def mu (i : Fin (n + 2)) : ℂ := if i = 0 then Complex.I else 1

/-- The diagonal bilinear form `∑ i, c i * z i * w i` over a commutative ring `R`. -/
def diagForm {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (c : ι → R) :
    (ι → R) →ₗ[R] (ι → R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun z w => ∑ i, c i * z i * w i)
    (fun z₁ z₂ w => by
      simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun a z w => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun z w₁ w₂ => by
      simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun z a w => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

@[simp] lemma diagForm_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (c : ι → R) (z w : ι → R) : diagForm c z w = ∑ i, c i * z i * w i := rfl

/-- The real Lorentzian form. -/
def realForm : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ := diagForm (eta n)

/-- The ℂ-bilinear Minkowski form. -/
def bilin : (Fin (n + 2) → ℂ) →ₗ[ℂ] (Fin (n + 2) → ℂ) →ₗ[ℂ] ℂ := diagForm (etaC n)

/-- The inclusion of the real points `m ↪ m_C`, coordinatewise `ℝ → ℂ`. -/
def coeM : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℂ) where
  toFun x i := (x i : ℂ)
  map_add' x y := by funext i; simp
  map_smul' r x := by funext i; simp [Complex.real_smul]

/-- The inclusion of the Euclidean real subspace `E ↪ m_C` (the Wick rotation). -/
def coeEucl : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℂ) where
  toFun e i := mu n i * (e i : ℂ)
  map_add' e e' := by funext i; simp [mul_add]
  map_smul' r e := by funext i; simp [Complex.real_smul]; ring

/-- The projection `m_C → E` along `iE`: take the imaginary part of the time coordinate and the
real parts of the space coordinates. -/
def projE : (Fin (n + 2) → ℂ) → (Fin (n + 2) → ℝ) :=
  fun z i => if i = 0 then (z i).im else (z i).re

@[simp] lemma coeM_apply (x : Fin (n + 2) → ℝ) (i) : coeM n x i = (x i : ℂ) := rfl
@[simp] lemma coeEucl_apply (e : Fin (n + 2) → ℝ) (i) : coeEucl n e i = mu n i * (e i : ℂ) := rfl
@[simp] lemma projE_apply (z : Fin (n + 2) → ℂ) (i) :
    projE n z i = if i = 0 then (z i).im else (z i).re := rfl

lemma realForm_apply (x y : Fin (n + 2) → ℝ) : realForm n x y = ∑ i, eta n i * x i * y i := rfl
lemma bilin_apply (z w : Fin (n + 2) → ℂ) : bilin n z w = ∑ i, etaC n i * z i * w i := rfl

lemma eta_ne_zero (i : Fin (n + 2)) : eta n i ≠ 0 := by
  unfold eta; split <;> norm_num

lemma etaC_eq (i : Fin (n + 2)) : etaC n i = ((eta n i : ℝ) : ℂ) := by
  unfold etaC eta; split <;> simp

/-- The Wick rotation cancels the signature on `E`: `etaC i · (mu i)² = 1` for every coordinate. -/
lemma etaC_mul_mu_sq (i : Fin (n + 2)) : etaC n i * mu n i ^ 2 = 1 := by
  unfold etaC mu; split
  · rw [Complex.I_sq]; ring
  · ring

/-- The ℂ-bilinear form on the Euclidean subspace is the real Euclidean inner product. -/
lemma bilin_eucl_eq (e e' : Fin (n + 2) → ℝ) :
    bilin n (coeEucl n e) (coeEucl n e') = ((∑ i, e i * e' i : ℝ) : ℂ) := by
  rw [bilin_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeEucl_apply, coeEucl_apply]
  have h := etaC_mul_mu_sq n i
  calc etaC n i * (mu n i * (e i : ℂ)) * (mu n i * (e' i : ℂ))
      = (etaC n i * mu n i ^ 2) * ((e i : ℂ) * (e' i : ℂ)) := by ring
    _ = (e i : ℂ) * (e' i : ℂ) := by rw [h, one_mul]
    _ = ((e i * e' i : ℝ) : ℂ) := by push_cast; ring

/-- **The model: complexified Minkowski space realizes `MinkowskiLinear`.** -/
noncomputable def minkowskiLinear : MinkowskiLinear where
  m := Fin (n + 2) → ℝ
  macg := inferInstance
  mmod := inferInstance
  mfin := inferInstance
  realForm := realForm n
  realForm_symm x y := by rw [realForm_apply, realForm_apply]
                          exact Finset.sum_congr rfl fun i _ => by ring
  realForm_nondegen x hx := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    simp only [Pi.zero_apply] at hi₀
    refine ⟨Pi.single i₀ 1, ?_⟩
    rw [realForm_apply]
    rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, mul_one]
    exact mul_ne_zero (eta_ne_zero n i₀) hi₀
  exists_timelike := by
    refine ⟨Pi.single 0 1, ?_⟩
    rw [realForm_apply]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, mul_one, eta]
    norm_num
  exists_spacelike := by
    have h1 : (1 : Fin (n + 2)) ≠ 0 := by rw [Ne, Fin.ext_iff]; simp
    refine ⟨Pi.single 1 1, ?_⟩
    rw [realForm_apply]
    rw [Finset.sum_eq_single 1 (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, mul_one, eta]
    rw [if_neg h1]; norm_num
  mC := Fin (n + 2) → ℂ
  acg := inferInstance
  mod := inferInstance
  coeM := coeM n
  coeM_injective := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [coeM_apply] at this
    exact Complex.ofReal_injective this
  mc_span z := by
    refine ⟨fun i => (z i).re, fun i => (z i).im, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, coeM_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (z i)).symm
  bilin := bilin n
  bilin_symm v w := by rw [bilin_apply, bilin_apply]
                       exact Finset.sum_congr rfl fun i _ => by ring
  bilin_real x y := by
    rw [bilin_apply, realForm_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeM_apply, coeM_apply, etaC_eq]
    push_cast; ring
  Eucl := Fin (n + 2) → ℝ
  eacg := inferInstance
  emod := inferInstance
  coeEucl := coeEucl n
  projE := projE n
  projE_coeEucl e := by
    funext i
    simp only [projE_apply, coeEucl_apply]
    by_cases h : i = 0
    · simp [h, mu]
    · simp [h, mu]
  projE_eucl_span e e' := by
    funext i
    simp only [projE_apply, Pi.add_apply, Pi.smul_apply, coeEucl_apply, smul_eq_mul]
    by_cases h : i = 0 <;>
      simp [mu, h, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  eucl_span z := by
    refine ⟨projE n z, fun i => if i = 0 then -(z i).re else (z i).im, ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, coeEucl_apply, projE_apply, smul_eq_mul]
    by_cases h : i = 0 <;>
      · apply Complex.ext <;>
          simp [mu, h, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_neg]
  bilin_eucl_real e e' := by rw [bilin_eucl_eq]; exact Complex.ofReal_im _
  bilin_eucl_pos e he := by
    rw [bilin_eucl_eq, Complex.ofReal_re]
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp he
    simp only [Pi.zero_apply] at hi₀
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
    · exact mul_self_nonneg (e i)
    · exact mul_self_pos.mpr hi₀

/-! ## The forward light cone

The forward light cone `C ⊂ m` is a linear-algebra ingredient that the Proposition 5.4
ruled-manifold construction and the general Wightman tube `Uk` consume (carried in prose by
`found:scv-tube-domain`).
It is NOT a field of `MinkowskiLinear`; it is exhibited here, on the concrete model, to confirm the
model is genuinely Lorentzian with a nonempty, open, proper cone (closed under positive scaling).
Its CONVEXITY is a causal-geometry fact (the reverse Cauchy-Schwarz inequality for timelike vectors)
that belongs to `found:lorentzian-causal-geometry`, and is not proved here. -/

/-- The open forward light cone: future-pointing (`0 < x 0`) timelike (`realForm x x < 0`)
vectors. -/
def forwardCone : Set (Fin (n + 2) → ℝ) := {x | 0 < x 0 ∧ realForm n x x < 0}

lemma mem_forwardCone {x : Fin (n + 2) → ℝ} :
    x ∈ forwardCone n ↔ 0 < x 0 ∧ realForm n x x < 0 := Iff.rfl

/-- `realForm` on a coordinate basis vector returns the signature coefficient. -/
lemma realForm_self_single (i₀ : Fin (n + 2)) :
    realForm n (Pi.single i₀ 1) (Pi.single i₀ 1) = eta n i₀ := by
  rw [realForm_apply, Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The forward light cone is nonempty (the time axis). -/
lemma forwardCone_nonempty : (forwardCone n).Nonempty := by
  refine ⟨Pi.single 0 1, ?_, ?_⟩
  · simp
  · rw [realForm_self_single]; unfold eta; norm_num

/-- The map `x ↦ realForm x x` is continuous. -/
lemma continuous_realForm_self :
    Continuous (fun x : Fin (n + 2) → ℝ => realForm n x x) := by
  simp only [realForm_apply]
  exact continuous_finset_sum _ fun i _ => by fun_prop

/-- The forward light cone is open. -/
lemma forwardCone_isOpen : IsOpen (forwardCone n) :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_realForm_self n) continuous_const)

/-- The forward light cone is proper: it is not all of `m` (it misses the origin). -/
lemma forwardCone_ne_univ : forwardCone n ≠ Set.univ := by
  intro h
  have hmem : (0 : Fin (n + 2) → ℝ) ∈ forwardCone n := h ▸ Set.mem_univ _
  simp only [mem_forwardCone, Pi.zero_apply, lt_self_iff_false, false_and] at hmem

/-- The forward light cone is closed under positive scaling: it is a genuine cone. -/
lemma forwardCone_smul {x : Fin (n + 2) → ℝ} (hx : x ∈ forwardCone n) {c : ℝ} (hc : 0 < c) :
    c • x ∈ forwardCone n := by
  obtain ⟨h0, hQ⟩ := hx
  refine ⟨?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using mul_pos hc h0
  · have hexp : realForm n (c • x) (c • x) = c ^ 2 * realForm n x x := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
    rw [hexp]
    exact mul_neg_of_pos_of_neg (pow_pos hc 2) hQ

end MinkowskiModel

end WickRotation
