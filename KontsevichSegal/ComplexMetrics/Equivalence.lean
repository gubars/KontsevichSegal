/- KS paper Theorem 2.2: the equivalence between Definition 2.1 (Hodge-star positivity)
and the angle condition (the working definition).

**Definition 2.1 of [KS]** is `KontsevichSegal.Hodge.IsAllowableHodge`
(`ComplexMetrics/HodgeScaffold.lean`), stated on the bare type
`KontsevichSegal.Hodge.ComplexMetric` — a symmetric ℝ-bilinear ℂ-valued form whose
real-coframe Gram determinant avoids the closed negative real axis (KSTeX 118/126). The
angle condition is NOT assumed there, so the equivalence proved here is non-vacuous.

**Theorem 2.2 of [KS]** is the biconditional `defn_2_1_equiv_angle_condition`: such a `g`
satisfies Definition 2.1 iff there is a real basis of `V` in which `g = ∑ᵢ λᵢ yᵢ²` with
every `λᵢ` nonzero, off the negative real axis, and `∑ᵢ |arg λᵢ| < π` (`AngleCondition`).

The FORWARD direction (angle condition ⇒ Definition 2.1) is
`KontsevichSegal.Hodge.isAllowableHodge_of_diag` (KSTeX 201–205, proved in
`HodgeScaffold.lean`). The REVERSE direction, proved here as
`angle_condition_of_isAllowableHodge`, follows KS's proof (KSTeX 199–205):

1. Definition 2.1 at `p = 1` makes `Re((det g)^{-1/2}·g)` positive-definite
   (`re_normalized_toForm_pos`).
2. A positive-definite real linear combination of `Re g` and `Im g` yields a simultaneous
   real diagonalization: the spectral theorem
   (`LinearMap.IsSymmetric.eigenvectorBasis`) applied to the operator representing `Re g`
   in the inner product defined by the combination
   (`exists_basis_isOrtho_pair_of_posdef`, `exists_basis_isOrtho_pair_of_posdef_combination`).
3. On the diagonalizing basis, Definition 2.1's form is diagonal with blade values
   `(det g)^{-1/2}·∏_{i∈S} λᵢ`, all in the open right half-plane
   (`blade_re_pos_of_isAllowableHodge`); exact additivity of principal arguments in the
   right half-plane (`arg_mul_of_re_pos`, `arg_mul_prod_of_re_pos`) turns positivity for
   every subset `S` into the angle condition (4)
   (`sum_abs_arg_lt_pi_of_prod_re_pos`, `angle_sum_subset_converse`,
   `not_nonpos_real_of_prod_re_pos`).
-/

import KontsevichSegal.ComplexMetrics.Defs
import KontsevichSegal.ComplexMetrics.HodgeScaffold
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace KontsevichSegal.Hodge

open scoped TensorProduct

/-! ## Exact additivity of arguments in the right half-plane

The rigorous form of KS's per-blade argument bookkeeping (KSTeX 203–205): for complex
numbers confined to the open right half-plane, principal arguments add exactly (no mod-2π
correction), because a correction of `±2π` would move the argument out of `(−π/2, π/2)`. -/

section ArgAdditivity

/-- **Exact additivity of principal arguments in the right half-plane**: if `z` and `z * w`
both have positive real part, then `arg (z * w) = arg z + arg w` exactly. Proof: factor
`w = z⁻¹ · (z·w)`; both factors have `|arg| < π/2`, so their argument sum lies in `(−π, π)`
and `Complex.arg_mul` applies with no wraparound. -/
theorem arg_mul_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : w ≠ 0)
    (hzw : 0 < (z * w).re) : (z * w).arg = z.arg + w.arg := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hzinv : 0 < (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have h0 : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have h1 : |Complex.arg z⁻¹| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzinv)
  have h2 : |Complex.arg (z * w)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzw)
  obtain ⟨h1l, h1r⟩ := abs_lt.mp h1
  obtain ⟨h2l, h2r⟩ := abs_lt.mp h2
  have hIoc : Complex.arg z⁻¹ + Complex.arg (z * w) ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith, by linarith⟩
  have key := Complex.arg_mul (inv_ne_zero hz0) (mul_ne_zero hz0 hw) hIoc
  rw [inv_mul_cancel_left₀ hz0] at key
  have hargpi : Complex.arg z ≠ Real.pi := by
    intro h
    rw [h, abs_of_nonneg Real.pi_pos.le] at h0
    linarith [Real.pi_pos]
  rw [Complex.arg_inv, if_neg hargpi] at key
  linarith [key]

/-- **Exact additivity over blades**: if every value `w * ∏_{i∈S} λᵢ` has positive real
part, arguments add exactly over every subset:
`arg (w * ∏_{i∈S} λᵢ) = arg w + ∑_{i∈S} arg λᵢ`. Finset induction on
`arg_mul_of_re_pos`. -/
theorem arg_mul_prod_of_re_pos {d : ℕ} {w : ℂ} {eig : Fin d → ℂ}
    (hne : ∀ i, eig i ≠ 0)
    (hpos : ∀ S : Finset (Fin d), 0 < (w * ∏ i ∈ S, eig i).re) :
    ∀ S : Finset (Fin d),
      (w * ∏ i ∈ S, eig i).arg = w.arg + ∑ i ∈ S, (eig i).arg := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hprod : w * ∏ i ∈ insert a S, eig i = (w * ∏ i ∈ S, eig i) * eig a := by
      rw [Finset.prod_insert ha]; ring
    rw [hprod, arg_mul_of_re_pos (hpos S) (hne a) (by rw [← hprod]; exact hpos _), ih,
      Finset.sum_insert ha]
    ring

/-- **The converse combinatorial half of KS condition (4)** (KSTeX 204–205): if for every
subset `S` the signed sum `∑_{i∈S}θᵢ − ∑_{i∉S}θᵢ` has absolute value `< π`, then
`∑ᵢ|θᵢ| < π` — the maximum over `S` is attained at `S = {i : 0 ≤ θᵢ}`. Converse of
`angle_sum_subset_bound`. -/
theorem angle_sum_subset_converse {d : ℕ} (θ : Fin d → ℝ)
    (h : ∀ S : Finset (Fin d), |(∑ i ∈ S, θ i) - ∑ i ∈ Sᶜ, θ i| < Real.pi) :
    ∑ i, |θ i| < Real.pi := by
  classical
  have habs : ∑ i, |θ i|
      = (∑ i ∈ Finset.univ.filter (fun i => 0 ≤ θ i), θ i)
        - ∑ i ∈ (Finset.univ.filter (fun i => 0 ≤ θ i))ᶜ, θ i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 ≤ θ i)
        (fun i => |θ i|), Finset.compl_filter]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ θ i), |θ i|
        = ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ θ i), θ i :=
      Finset.sum_congr rfl fun i hi => abs_of_nonneg (Finset.mem_filter.mp hi).2
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 ≤ θ i), |θ i|
        = ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 ≤ θ i), -θ i :=
      Finset.sum_congr rfl fun i hi =>
        abs_of_neg (not_le.mp (Finset.mem_filter.mp hi).2)
    rw [h1, h2, Finset.sum_neg_distrib]
    ring
  calc ∑ i, |θ i|
      ≤ |(∑ i ∈ Finset.univ.filter (fun i => 0 ≤ θ i), θ i)
          - ∑ i ∈ (Finset.univ.filter (fun i => 0 ≤ θ i))ᶜ, θ i| := habs ▸ le_abs_self _
    _ < Real.pi := h _

/-- **Blade positivity forces the angle sum below π** (KS Theorem 2.2, reverse eigenvalue
step, KSTeX 203–205): if every value `w * ∏_{i∈S} λᵢ` lies in the open right half-plane,
then `∑ᵢ|arg λᵢ| < π`. -/
theorem sum_abs_arg_lt_pi_of_prod_re_pos {d : ℕ} {w : ℂ} {eig : Fin d → ℂ}
    (hne : ∀ i, eig i ≠ 0)
    (hpos : ∀ S : Finset (Fin d), 0 < (w * ∏ i ∈ S, eig i).re) :
    ∑ i, |Complex.arg (eig i)| < Real.pi := by
  classical
  have hadd := arg_mul_prod_of_re_pos hne hpos
  refine angle_sum_subset_converse _ (fun S => ?_)
  have hS : |Complex.arg w + ∑ i ∈ S, Complex.arg (eig i)| < Real.pi / 2 := by
    rw [← hadd S]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos S))
  have hSc : |Complex.arg w + ∑ i ∈ Sᶜ, Complex.arg (eig i)| < Real.pi / 2 := by
    rw [← hadd Sᶜ]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos Sᶜ))
  have hkey : (∑ i ∈ S, Complex.arg (eig i)) - ∑ i ∈ Sᶜ, Complex.arg (eig i)
      = (Complex.arg w + ∑ i ∈ S, Complex.arg (eig i))
        - (Complex.arg w + ∑ i ∈ Sᶜ, Complex.arg (eig i)) := by ring
  rw [hkey]
  calc |(Complex.arg w + ∑ i ∈ S, Complex.arg (eig i))
        - (Complex.arg w + ∑ i ∈ Sᶜ, Complex.arg (eig i))|
      = |(Complex.arg w + ∑ i ∈ S, Complex.arg (eig i))
          + -(Complex.arg w + ∑ i ∈ Sᶜ, Complex.arg (eig i))| := by rw [sub_eq_add_neg]
    _ ≤ |Complex.arg w + ∑ i ∈ S, Complex.arg (eig i)|
          + |-(Complex.arg w + ∑ i ∈ Sᶜ, Complex.arg (eig i))| := abs_add_le _ _
    _ = |Complex.arg w + ∑ i ∈ S, Complex.arg (eig i)|
          + |Complex.arg w + ∑ i ∈ Sᶜ, Complex.arg (eig i)| := by rw [abs_neg]
    _ < Real.pi / 2 + Real.pi / 2 := add_lt_add hS hSc
    _ = Real.pi := by ring

/-- **Blade positivity keeps every eigenvalue off the closed negative real axis** (KS
Theorem 2.2, reverse eigenvalue step, per-eigenvalue half): if every value
`w * ∏_{i∈S} λᵢ` lies in the open right half-plane, then no `λᵢ` is real and nonpositive. -/
theorem not_nonpos_real_of_prod_re_pos {d : ℕ} {w : ℂ} {eig : Fin d → ℂ}
    (hne : ∀ i, eig i ≠ 0)
    (hpos : ∀ S : Finset (Fin d), 0 < (w * ∏ i ∈ S, eig i).re) (i : Fin d) :
    0 < (eig i).re ∨ (eig i).im ≠ 0 := by
  classical
  have hadd := arg_mul_prod_of_re_pos hne hpos
  have hi := hadd {i}
  rw [Finset.sum_singleton] at hi
  have h1 : |Complex.arg w + Complex.arg (eig i)| < Real.pi / 2 := by
    rw [← hi]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos {i}))
  have h0 : |Complex.arg w| < Real.pi / 2 := by
    have := hadd ∅
    rw [Finset.sum_empty, add_zero] at this
    rw [← this]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hpos ∅))
  have hlt : |Complex.arg (eig i)| < Real.pi := by
    have hsplit : Complex.arg (eig i)
        = (Complex.arg w + Complex.arg (eig i)) - Complex.arg w := by ring
    calc |Complex.arg (eig i)|
        = |(Complex.arg w + Complex.arg (eig i)) + -(Complex.arg w)| := by
          rw [← sub_eq_add_neg, ← hsplit]
      _ ≤ |Complex.arg w + Complex.arg (eig i)| + |-(Complex.arg w)| := abs_add_le _ _
      _ = |Complex.arg w + Complex.arg (eig i)| + |Complex.arg w| := by rw [abs_neg]
      _ < Real.pi / 2 + Real.pi / 2 := add_lt_add h1 h0
      _ = Real.pi := by ring
  have hne_pi : Complex.arg (eig i) ≠ Real.pi := by
    intro h
    rw [h, abs_of_nonneg Real.pi_pos.le] at hlt
    exact lt_irrefl _ hlt
  by_contra hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  rcases lt_or_eq_of_le hre with hlt' | heq
  · exact hne_pi (Complex.arg_eq_pi_iff.mpr ⟨hlt', him⟩)
  · exact hne i (Complex.ext (by simpa using heq) (by simpa using him))

end ArgAdditivity

/-! ## Simultaneous real diagonalization from a positive-definite combination

The linear-algebra engine of KS's Theorem 2.2 reverse direction (KSTeX 199): "To
diagonalize a complex form `g = A + iB` with respect to a real basis is to diagonalize its
real and imaginary parts simultaneously, which is possible if either `A` or `B` — or, more
generally, a real linear combination of them such as the real part of `(det g)^{-1/2}·g` —
is positive-definite." The proof is the real spectral theorem
(`LinearMap.IsSymmetric.eigenvectorBasis`): the positive-definite form is an inner product,
the other form is represented by a self-adjoint operator, and its eigenbasis diagonalizes
both. -/

section Diagonalization

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A positive-definite symmetric real bilinear form packaged as an
`InnerProductSpace.Core` — the inner-product structure of KS's proof of Theorem 2.2
(KSTeX 199). -/
noncomputable def posDefCore (P : LinearMap.BilinForm ℝ V)
    (hsymm : ∀ x y, P x y = P y x) (hpos : ∀ v, v ≠ 0 → 0 < P v v) :
    InnerProductSpace.Core ℝ V where
  inner x y := P x y
  conj_inner_symm x y := by simpa using hsymm y x
  re_inner_nonneg x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simpa using (hpos x hx).le
  add_left x y z := by simp [map_add]
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    exact (hpos x h).ne' (by simpa using hx)

/-- **Simultaneous diagonalization against a positive-definite form** (the spectral-theorem
step of KS's Theorem 2.2 reverse direction, KSTeX 199): a symmetric bilinear form `A` and a
positive-definite symmetric form `P` on a finite-dimensional real vector space are
simultaneously diagonalized by some basis — the eigenbasis
(`LinearMap.IsSymmetric.eigenvectorBasis`) of the `P`-self-adjoint operator
`T = P♭⁻¹ ∘ A♭` representing `A` in the `P`-inner product. -/
theorem exists_basis_isOrtho_pair_of_posdef (P A : LinearMap.BilinForm ℝ V)
    (hPsymm : ∀ x y, P x y = P y x) (hAsymm : ∀ x y, A x y = A y x)
    (hpos : ∀ v, v ≠ 0 → 0 < P v v) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      (∀ i j, i ≠ j → P (b i) (b j) = 0) ∧ (∀ i j, i ≠ j → A (b i) (b j) = 0) := by
  classical
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (posDefCore P hPsymm hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (posDefCore P hPsymm hpos).toCore
  have hinner : ∀ x y : V, inner ℝ x y = P x y := fun x y => rfl
  have hPnd : P.Nondegenerate := by
    constructor
    · intro x hx
      by_contra hx0
      exact (hpos x hx0).ne' (hx x)
    · intro y hy
      by_contra hy0
      exact (hpos y hy0).ne' (hy y)
  obtain ⟨T, hPT⟩ : ∃ T : V →ₗ[ℝ] V, ∀ x y, P (T x) y = A x y :=
    ⟨(P.toDual hPnd).symm.toLinearMap ∘ₗ A, fun x y =>
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := hPnd) (A x) y⟩
  have hTsymm : T.IsSymmetric := by
    intro x y
    change inner ℝ (T x) y = inner ℝ x (T y)
    rw [hinner, hinner, hPT, hPsymm x (T y), hPT, hAsymm y x]
  set b0 := hTsymm.eigenvectorBasis rfl with hb0
  refine ⟨b0.toBasis, fun i j hij => ?_, fun i j hij => ?_⟩
  · rw [OrthonormalBasis.coe_toBasis]
    rw [← hinner]
    exact b0.orthonormal.2 hij
  · rw [OrthonormalBasis.coe_toBasis, ← hPT, ← hinner, hb0,
      hTsymm.apply_eigenvectorBasis, real_inner_smul_left, ← hb0,
      b0.orthonormal.2 hij, mul_zero]

/-- **Simultaneous real diagonalization from a positive-definite combination** (KSTeX 199):
if some real linear combination `c·A − s·B` of two symmetric bilinear forms is
positive-definite, then some basis diagonalizes `A` and `B` simultaneously. The form the
combination takes here matches `Re((c + is)·(A + iB)) = c·A − s·B`, the real part of
`(det g)^{-1/2}·g` in KS's proof. -/
theorem exists_basis_isOrtho_pair_of_posdef_combination
    (A B : LinearMap.BilinForm ℝ V)
    (hAsymm : ∀ x y, A x y = A y x) (hBsymm : ∀ x y, B x y = B y x) (c s : ℝ)
    (hpos : ∀ v, v ≠ 0 → 0 < c * A v v - s * B v v) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      (∀ i j, i ≠ j → A (b i) (b j) = 0) ∧ (∀ i j, i ≠ j → B (b i) (b j) = 0) := by
  classical
  set P : LinearMap.BilinForm ℝ V := c • A - s • B with hPdef
  have hPapply : ∀ x y, P x y = c * A x y - s * B x y := by
    intro x y
    simp [hPdef]
  have hPsymm : ∀ x y, P x y = P y x := by
    intro x y
    rw [hPapply, hPapply, hAsymm x y, hBsymm x y]
  have hPpos : ∀ v, v ≠ 0 → 0 < P v v := by
    intro v hv
    rw [hPapply]
    exact hpos v hv
  by_cases hs : s = 0
  · -- `P = c·A`: diagonalize `(P, B)`; `A` is recovered as `P/c`, with `c ≠ 0` witnessed
    -- by positivity on any basis vector.
    obtain ⟨b, hPb, hBb⟩ := exists_basis_isOrtho_pair_of_posdef P B hPsymm hBsymm hPpos
    refine ⟨b, fun i j hij => ?_, hBb⟩
    have hc : c ≠ 0 := by
      intro hc0
      have h1 := hpos (b i) (b.ne_zero i)
      rw [hc0, hs] at h1
      simp at h1
    have h1 := hPb i j hij
    rw [hPapply, hs, zero_mul, sub_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc
  · obtain ⟨b, hPb, hAb⟩ := exists_basis_isOrtho_pair_of_posdef P A hPsymm hAsymm hPpos
    refine ⟨b, hAb, fun i j hij => ?_⟩
    have h1 := hPb i j hij
    rw [hPapply, hAb i j hij, mul_zero, zero_sub, neg_eq_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hs

end Diagonalization

/-! ## The reverse direction of KS Theorem 2.2 -/

section Reverse

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Definition 2.1 at `p = 1`** (KSTeX 199: "But 2.1, applied when `p = 1`, implies that
the real part of `(det g)^{-1/2}·g` is positive"): for `g` satisfying `IsAllowableHodge`,
the normalized quadratic form `(detSqrtReal g)⁻¹ · g(v,v)` has positive real part on every
nonzero `v`. -/
theorem re_normalized_toForm_pos (g : ComplexMetric V) (h : IsAllowableHodge g)
    (v : V) (hv : v ≠ 0) : 0 < ((detSqrtReal g)⁻¹ * g.toForm v v).re := by
  have hα : exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => v) ≠ 0 :=
    ιMulti_ne_zero_of_linearIndependent (LinearIndependent.of_subsingleton 0 hv)
  have hpos := h 1 (exteriorPower.ιMulti ℝ 1 (fun _ : Fin 1 => v)) hα
  rw [realExtPow_ιMulti, formC_apply_ιMulti] at hpos
  rw [show (Matrix.of fun _ _ : Fin 1 =>
        gc g ((1 : ℂ) ⊗ₜ[ℝ] v) ((1 : ℂ) ⊗ₜ[ℝ] v)).det
      = gc g ((1 : ℂ) ⊗ₜ[ℝ] v) ((1 : ℂ) ⊗ₜ[ℝ] v) from Matrix.det_fin_one _,
    gc_apply_tmul] at hpos
  exact hpos

/-- **Diagonal expansion of the quadratic form on a `g`-orthogonal basis**: if the basis
`b` is orthogonal for `g` (off-diagonal Gram entries vanish), the quadratic values expand
diagonally, `g(v,v) = ∑ᵢ g(bᵢ,bᵢ)·(yᵢ v)²`. Converse polarization of
`gram_eq_diagonal_of_diag`. -/
theorem toForm_diag_of_orthogonal (g : ComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    (horth : ∀ i j, i ≠ j → g.toForm (b i) (b j) = 0) (v : V) :
    g.toForm v v = ∑ i, g.toForm (b i) (b i) * (b.repr v i : ℂ) ^ 2 := by
  classical
  suffices hbil : ∀ v w : V, g.toForm v w
      = ∑ i, g.toForm (b i) (b i) * (b.repr v i : ℂ) * (b.repr w i : ℂ) by
    rw [hbil v v]
    exact Finset.sum_congr rfl fun i _ => by ring
  intro v w
  have expand2 : ∀ i, g.toForm (b i) w
      = (b.repr w i : ℂ) * g.toForm (b i) (b i) := by
    intro i
    conv_lhs => rw [show w = ∑ j, b.repr w j • b j from (b.sum_repr w).symm]
    rw [map_sum, Finset.sum_eq_single i]
    · rw [map_smul, Complex.real_smul]
    · intro j _ hj
      rw [map_smul, Complex.real_smul, horth i j (Ne.symm hj), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  conv_lhs => rw [show v = ∑ i, b.repr v i • b i from (b.sum_repr v).symm]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, Complex.real_smul, expand2 i]
  ring

/-- **Nondegeneracy passes to the diagonal coefficients**: on a diagonalizing basis of a
complex metric every `λᵢ` is nonzero, because the real-coframe Gram determinant is a
positive multiple of `∏ᵢλᵢ` (`detGramReal_eq_prod_of_diag`) and is nonzero
(`detGramReal_ne_zero`). -/
theorem eig_ne_zero_of_diag (g : ComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (i : Fin (Module.finrank ℝ V)) : eig i ≠ 0 := by
  obtain ⟨r, hr, hdet⟩ := detGramReal_eq_prod_of_diag g hdiag
  have hne := detGramReal_ne_zero g
  rw [hdet] at hne
  intro h0
  exact hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero])

/-- **Blade positivity under Definition 2.1** (KSTeX 201–202, reverse reading): evaluating
`IsAllowableHodge` on the basis blades `b_S` of a diagonalizing basis gives
`0 < Re((detSqrtReal g)⁻¹ · ∏_{i∈S} λᵢ)` for every subset `S`. -/
theorem blade_re_pos_of_isAllowableHodge (g : ComplexMetric V) (h : IsAllowableHodge g)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (S : Finset (Fin (Module.finrank ℝ V))) :
    0 < ((detSqrtReal g)⁻¹ * ∏ i ∈ S, eig i).re := by
  classical
  set T : Set.powersetCard (Fin (Module.finrank ℝ V)) S.card := ⟨S, by simp⟩ with hTdef
  have hα : (b.exteriorPower S.card) T ≠ 0 := Module.Basis.ne_zero _ _
  have hpos := h S.card ((b.exteriorPower S.card) T) hα
  rw [formC_realExtPow_diag g hdiag S.card] at hpos
  have hcollapse : ∑ U : Set.powersetCard (Fin (Module.finrank ℝ V)) S.card,
      (((b.exteriorPower S.card).repr ((b.exteriorPower S.card) T) U : ℝ) : ℂ) ^ 2
        * ∏ j ∈ (U : Finset (Fin (Module.finrank ℝ V))), eig j
      = ∏ j ∈ S, eig j := by
    rw [Finset.sum_eq_single T]
    · rw [Module.Basis.repr_self]
      simp [hTdef]
    · intro U _ hU
      rw [Module.Basis.repr_self]
      simp [Ne.symm hU]
    · intro hmem
      exact absurd (Finset.mem_univ T) hmem
  rwa [hcollapse] at hpos

/-- **The reverse direction of KS Theorem 2.2** (KSTeX 199–205): a complex metric
satisfying KS Definition 2.1 (`IsAllowableHodge`) admits a real diagonalization whose
coefficients satisfy the angle condition. KS's three steps: `p = 1` positivity makes
`Re((det g)^{-1/2}·g)` positive-definite (`re_normalized_toForm_pos`); the spectral theorem
simultaneously diagonalizes `Re g` and `Im g` over ℝ
(`exists_basis_isOrtho_pair_of_posdef_combination`); blade positivity plus exact argument
additivity in the right half-plane yields condition (4)
(`blade_re_pos_of_isAllowableHodge`, `not_nonpos_real_of_prod_re_pos`,
`sum_abs_arg_lt_pi_of_prod_re_pos`). -/
theorem angle_condition_of_isAllowableHodge (g : ComplexMetric V)
    (h : IsAllowableHodge g) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
      (eig : Fin (Module.finrank ℝ V) → ℂ),
      AngleCondition eig ∧ ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2 := by
  classical
  -- Step 1: `p = 1` positivity gives the positive-definite real combination
  -- `Re(k·g) = (Re k)·(Re g) − (Im k)·(Im g)`, `k := (det g)^{-1/2}`.
  have hcomb : ∀ v, v ≠ 0 →
      0 < (detSqrtReal g)⁻¹.re * (reForm g v v) - (detSqrtReal g)⁻¹.im * (imForm g v v) := by
    intro v hv
    have h1 := re_normalized_toForm_pos g h v hv
    rw [Complex.mul_re] at h1
    exact h1
  -- Step 2: simultaneous real diagonalization of `Re g` and `Im g`.
  obtain ⟨b, hre, him⟩ := exists_basis_isOrtho_pair_of_posdef_combination
    (reForm g) (imForm g)
    (fun x y => by
      change (g.toForm x y).re = (g.toForm y x).re
      rw [g.symmetric'])
    (fun x y => by
      change (g.toForm x y).im = (g.toForm y x).im
      rw [g.symmetric'])
    (detSqrtReal g)⁻¹.re (detSqrtReal g)⁻¹.im hcomb
  have horth : ∀ i j, i ≠ j → g.toForm (b i) (b j) = 0 := fun i j hij =>
    Complex.ext (by simpa using hre i j hij) (by simpa using him i j hij)
  refine ⟨b, fun i => g.toForm (b i) (b i),
    ?_, toForm_diag_of_orthogonal g horth⟩
  -- Step 3: blade positivity + exact argument additivity give the angle condition.
  have hdiag := toForm_diag_of_orthogonal g horth
  have hne : ∀ i, (fun i => g.toForm (b i) (b i)) i ≠ 0 :=
    eig_ne_zero_of_diag g hdiag
  have hblade := blade_re_pos_of_isAllowableHodge g h hdiag
  exact ⟨hne, not_nonpos_real_of_prod_re_pos hne hblade,
    sum_abs_arg_lt_pi_of_prod_re_pos hne hblade⟩

end Reverse

end KontsevichSegal.Hodge

/-- **KS paper Theorem 2.2** (the full biconditional, unconditional). A complex metric on a
finite-dimensional real vector space `V` — a symmetric ℂ-valued form whose real-coframe
Gram determinant avoids the closed negative real axis
(`KontsevichSegal.Hodge.ComplexMetric`, the domain of Definition 2.1; the angle condition
is NOT assumed) — satisfies KS Definition 2.1
(`KontsevichSegal.Hodge.IsAllowableHodge`: for all degrees `p ≥ 0` the real part of the
quadratic form `α ↦ α ∧ ⋆_g α` on real `p`-forms is positive-definite) if and only if there
is a real basis of `V` in which `g = ∑ᵢ λᵢ yᵢ²` with the coefficients satisfying the angle
condition: all `λᵢ` nonzero, none on the negative real axis, and `∑ᵢ|arg λᵢ| < π`
(`AngleCondition`, condition (4)).

Forward direction: `KontsevichSegal.Hodge.isAllowableHodge_of_diag` (KSTeX 201–205).
Reverse direction: `KontsevichSegal.Hodge.angle_condition_of_isAllowableHodge`
(KSTeX 199–205, via the spectral-theorem simultaneous diagonalization). Both directions are
fully proved; the biconditional carries no deferred hypotheses. -/
theorem defn_2_1_equiv_angle_condition
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : KontsevichSegal.Hodge.ComplexMetric V) :
    KontsevichSegal.Hodge.IsAllowableHodge g ↔
      ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
        (eig : Fin (Module.finrank ℝ V) → ℂ),
        AngleCondition eig ∧ ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2 :=
  ⟨KontsevichSegal.Hodge.angle_condition_of_isAllowableHodge g,
    fun ⟨_, _, hAC, hdiag⟩ => KontsevichSegal.Hodge.isAllowableHodge_of_diag g hAC hdiag⟩
