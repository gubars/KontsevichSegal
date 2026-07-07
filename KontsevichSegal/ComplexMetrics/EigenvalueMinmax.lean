/- Checkpoint 1 of the eigenvalue min-max (KS paper Proposition 2.5): the bridge from
the angle condition to a real self-adjoint operator.

KS paper Proposition 2.5 (arXiv:2105.10161, p. 13) characterizes the critical angles
`θ₁ ≥ … ≥ θ_d` of `v ↦ arg g(v)` by a min-max over subspaces and derives eigenvalue
interlacing under restriction (blueprint `lem:eigenvalue-minmax`). This file builds the
linear-algebra bridge that turns those angles into the spectrum of an operator:

1. the angle condition supplies a single global rotation `φ` (the midpoint
   `φ = (N − Q)/2` of the argument arc) moving every diagonal coefficient into the open
   right half-plane (`AngleCondition.exists_rotation`);
2. a symmetric bilinear form with diagonal quadratic values is diagonal as a bilinear
   form (`bilin_diag_of_quadratic_diag`, polarization);
3. the real part `ĝ_R` of `e^{-iφ}·g` is then a positive-definite symmetric real form
   (`rotatedRe_posDef`), an inner product via `posDefCore`;
4. the operator `T` representing the imaginary part `ĝ_I` in that inner product
   (`pencilOperator`) is self-adjoint (`isSymmetric_of_pairing`);
5. on the diagonalizing basis, `T bᵢ = tan(arg(e^{-iφ}λᵢ)) · bᵢ`
   (`pencilOperator_eigen_basis`): the critical angles of `arg g`, rotated by `φ`, are
   the arctangents of the eigenvalues of `T`.

The min-max characterization of those eigenvalues (Courant-Fischer) and the interlacing
under restriction are the next checkpoint and are NOT proved here.
-/

import KontsevichSegal.ComplexMetrics.Defs
import KontsevichSegal.ComplexMetrics.Equivalence
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Order.Monotone

/-! ## Polarization: a diagonal quadratic form has a diagonal bilinear form

Extracted from the `hbil` step inside `volume_element_positive`
(`ComplexMetrics/Defs.lean`), stated for a general symmetric ℝ-bilinear ℂ-valued form so
that it also serves KS paper Proposition 2.5 (nondegeneracy of the restricted form). -/

section Polarization

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]

/-- **Polarization**: a symmetric ℝ-bilinear ℂ-valued form whose quadratic values are
diagonal in a basis `rb`, `B(v,v) = ∑ₖ cₖ·(yₖ v)²`, is diagonal as a bilinear form:
`B(u,v) = ∑ₖ cₖ·(yₖ u)·(yₖ v)`. -/
theorem bilin_diag_of_quadratic_diag (B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hsymm : ∀ v w, B v w = B w v) (rb : Module.Basis ι ℝ V) (c : ι → ℂ)
    (hdiag : ∀ v, B v v = ∑ k, c k * (rb.repr v k : ℂ) ^ 2) (u v : V) :
    B u v = ∑ k, c k * (rb.repr u k : ℂ) * (rb.repr v k : ℂ) := by
  have h1 := hdiag (u + v)
  simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, Complex.ofReal_add] at h1
  have hexp : ∑ k, c k * ((rb.repr u k : ℂ) + (rb.repr v k : ℂ)) ^ 2
      = (∑ k, c k * (rb.repr u k : ℂ) ^ 2)
        + (∑ k, c k * (rb.repr v k : ℂ) ^ 2)
        + 2 * ∑ k, c k * (rb.repr u k : ℂ) * (rb.repr v k : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linear_combination h1 / 2 + hexp / 2 - hdiag u / 2 - hdiag v / 2 + hsymm u v / 2

/-- The basis vectors of a diagonalizing basis are orthogonal for the bilinear form:
`B(rbᵢ, rbⱼ) = 0` for `i ≠ j`. -/
theorem bilin_basis_eq_zero_of_ne (B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hsymm : ∀ v w, B v w = B w v) (rb : Module.Basis ι ℝ V) (c : ι → ℂ)
    (hdiag : ∀ v, B v v = ∑ k, c k * (rb.repr v k : ℂ) ^ 2)
    {i j : ι} (hij : i ≠ j) : B (rb i) (rb j) = 0 := by
  classical
  rw [bilin_diag_of_quadratic_diag B hsymm rb c hdiag]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne k i with rfl | hki
  · have h0 : rb.repr (rb j) k = 0 := by
      rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm hij)]
    rw [h0]
    simp
  · have h0 : rb.repr (rb i) k = 0 := by
      rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm hki)]
    rw [h0]
    simp

/-- The diagonal value of the bilinear form on a diagonalizing basis vector is the
diagonal coefficient: `B(rbᵢ, rbᵢ) = cᵢ`. -/
theorem bilin_basis_apply_self (B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (rb : Module.Basis ι ℝ V) (c : ι → ℂ)
    (hdiag : ∀ v, B v v = ∑ k, c k * (rb.repr v k : ℂ) ^ 2) (i : ι) :
    B (rb i) (rb i) = c i := by
  classical
  rw [hdiag (rb i), Finset.sum_eq_single i]
  · simp [Module.Basis.repr_self]
  · intro k _ hki
    have h0 : rb.repr (rb i) k = 0 := by
      rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm hki)]
    rw [h0]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

end Polarization

/-! ## The global rotation

The arc-midpoint construction extracted verbatim from the interior of
`not_neg_real_axis` (`ComplexMetrics/Defs.lean`): the arguments lie in `[-Q, N]` with
`N + Q < π`, and the midpoint `φ = (N − Q)/2` of that arc is within `π/2` of every
argument, so `e^{-iφ}` rotates all diagonal coefficients into the open right
half-plane. -/

/-- **The global rotation of the angle condition** (KS paper Proposition 2.5, first
step). For `eig` satisfying `AngleCondition` there is a single angle `φ`, the midpoint
`(N − Q)/2` of the argument arc, with `|φ| < π/2`, every argument within `π/2` of `φ`,
and every rotated coefficient `e^{-iφ}·λᵢ` of strictly positive real part. -/
theorem AngleCondition.exists_rotation {d : ℕ} {eig : Fin d → ℂ}
    (hAC : AngleCondition eig) :
    ∃ φ : ℝ, |φ| < Real.pi / 2 ∧
      (∀ i, |Complex.arg (eig i) - φ| < Real.pi / 2) ∧
      (∀ i, 0 < (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re) := by
  -- Positive and negative parts of the total argument variation: all the
  -- arguments lie in [-Q, N] with N + Q < π, an arc of width < π containing 0.
  set N : ℝ := ∑ i, max (Complex.arg (eig i)) 0 with hNdef
  set Q : ℝ := ∑ i, max (-(Complex.arg (eig i))) 0 with hQdef
  have hNQ : N + Q < Real.pi := by
    have hsplit : ∀ x : ℝ, max x 0 + max (-x) 0 = |x| := by
      intro x
      rcases le_total x 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    calc N + Q
        = ∑ i, (max (Complex.arg (eig i)) 0 + max (-(Complex.arg (eig i))) 0) := by
          rw [hNdef, hQdef, ← Finset.sum_add_distrib]
      _ = ∑ i, |Complex.arg (eig i)| := Finset.sum_congr rfl fun i _ => hsplit _
      _ < Real.pi := hAC.sum_arg_lt_pi
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hargleN : ∀ i, Complex.arg (eig i) ≤ N := by
    intro i
    rw [hNdef]
    calc Complex.arg (eig i) ≤ max (Complex.arg (eig i)) 0 := le_max_left _ _
      _ ≤ ∑ j, max (Complex.arg (eig j)) 0 :=
          Finset.single_le_sum (f := fun j => max (Complex.arg (eig j)) 0)
            (fun j _ => le_max_right _ _) (Finset.mem_univ i)
  have harggeQ : ∀ i, -Q ≤ Complex.arg (eig i) := by
    intro i
    have h : -(Complex.arg (eig i)) ≤ Q := by
      rw [hQdef]
      calc -(Complex.arg (eig i)) ≤ max (-(Complex.arg (eig i))) 0 := le_max_left _ _
        _ ≤ ∑ j, max (-(Complex.arg (eig j))) 0 :=
            Finset.single_le_sum (f := fun j => max (-(Complex.arg (eig j))) 0)
              (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    linarith
  -- The separating direction: the midpoint of the arc. Both 0 and every
  -- argument are within π/2 of φ.
  set φ : ℝ := (N - Q) / 2 with hφdef
  have hφlt : |φ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · rw [hφdef]; linarith
    · rw [hφdef]; linarith
  have hargφ : ∀ i, |Complex.arg (eig i) - φ| < Real.pi / 2 := by
    intro i
    rw [abs_lt]
    constructor
    · rw [hφdef]; linarith [harggeQ i]
    · rw [hφdef]; linarith [hargleN i]
  -- The rotated coefficients have positive real part: the linear functional
  -- z ↦ Re(e^{-iφ} z) is ‖z‖·cos(arg z − φ) on each eigenvalue.
  have hpos : ∀ i, 0 < (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re := by
    intro i
    have hzne : eig i ≠ 0 := hAC.nonzero i
    have hnorm : (0 : ℝ) < ‖eig i‖ := norm_pos_iff.mpr hzne
    have hkey : (eig i).re * Real.cos φ + (eig i).im * Real.sin φ
        = ‖eig i‖ * Real.cos (Complex.arg (eig i) - φ) := by
      rw [Real.cos_sub, Complex.cos_arg hzne, Complex.sin_arg]
      field_simp
    have hcos : 0 < Real.cos (Complex.arg (eig i) - φ) :=
      Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp (hargφ i)).1, (abs_lt.mp (hargφ i)).2⟩
    have hre : (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re
        = (eig i).re * Real.cos φ + (eig i).im * Real.sin φ := by
      have h1 : -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I := by
        rw [Complex.ofReal_neg]
      rw [h1, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Real.cos_neg, Real.sin_neg]
      ring
    rw [hre, hkey]
    exact mul_pos hnorm hcos
  exact ⟨φ, hφlt, hargφ, hpos⟩

/-! ## The rotated real and imaginary forms -/

section RotatedForms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The real part `ĝ_R = Re(e^{-iφ}·g)` of the rotated form, as a real bilinear form on
`V` (KS paper Proposition 2.5: the positive-definite form of the pencil). -/
noncomputable def AllowableComplexMetric.rotatedRe (g : AllowableComplexMetric V)
    (φ : ℝ) : LinearMap.BilinForm ℝ V where
  toFun v :=
    { toFun := fun w => (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm v w).re
      map_add' := fun w₁ w₂ => by rw [map_add, mul_add, Complex.add_re]
      map_smul' := fun r w => by
        simp only [map_smul, Complex.real_smul, RingHom.id_apply, smul_eq_mul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring }
  map_add' v₁ v₂ := by
    ext w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add,
      Complex.add_re]
  map_smul' r v := by
    ext w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      smul_eq_mul, map_smul, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- The imaginary part `ĝ_I = Im(e^{-iφ}·g)` of the rotated form, as a real bilinear
form on `V` (KS paper Proposition 2.5: the second form of the pencil). -/
noncomputable def AllowableComplexMetric.rotatedIm (g : AllowableComplexMetric V)
    (φ : ℝ) : LinearMap.BilinForm ℝ V where
  toFun v :=
    { toFun := fun w => (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm v w).im
      map_add' := fun w₁ w₂ => by rw [map_add, mul_add, Complex.add_im]
      map_smul' := fun r w => by
        simp only [map_smul, Complex.real_smul, RingHom.id_apply, smul_eq_mul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring }
  map_add' v₁ v₂ := by
    ext w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add,
      Complex.add_im]
  map_smul' r v := by
    ext w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      smul_eq_mul, map_smul, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

@[simp] theorem AllowableComplexMetric.rotatedRe_apply (g : AllowableComplexMetric V)
    (φ : ℝ) (v w : V) :
    g.rotatedRe φ v w = (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm v w).re := rfl

@[simp] theorem AllowableComplexMetric.rotatedIm_apply (g : AllowableComplexMetric V)
    (φ : ℝ) (v w : V) :
    g.rotatedIm φ v w = (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm v w).im := rfl

/-- `ĝ_R` is symmetric (from the symmetry of `g`). -/
theorem AllowableComplexMetric.rotatedRe_symm (g : AllowableComplexMetric V) (φ : ℝ)
    (v w : V) : g.rotatedRe φ v w = g.rotatedRe φ w v := by
  rw [g.rotatedRe_apply, g.rotatedRe_apply, g.symmetric' v w]

/-- `ĝ_I` is symmetric (from the symmetry of `g`). -/
theorem AllowableComplexMetric.rotatedIm_symm (g : AllowableComplexMetric V) (φ : ℝ)
    (v w : V) : g.rotatedIm φ v w = g.rotatedIm φ w v := by
  rw [g.rotatedIm_apply, g.rotatedIm_apply, g.symmetric' v w]

/-- Diagonal expansion of `ĝ_R` on a diagonalizing basis of `g`:
`ĝ_R(v,v) = ∑ᵢ Re(e^{-iφ}λᵢ)·(yᵢ v)²`. -/
theorem AllowableComplexMetric.rotatedRe_apply_self (g : AllowableComplexMetric V)
    (φ : ℝ) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (eig : ι → ℂ)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2) (v : V) :
    g.rotatedRe φ v v
      = ∑ i, (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re * (b.repr v i) ^ 2 := by
  rw [g.rotatedRe_apply, hdiag v, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- **`ĝ_R` is positive-definite** (KS paper Proposition 2.5): with every rotated
coefficient in the open right half-plane, the diagonal expansion of `ĝ_R` is a sum of
nonnegative terms with at least one strictly positive term. -/
theorem AllowableComplexMetric.rotatedRe_posDef (g : AllowableComplexMetric V) (φ : ℝ)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V) (eig : ι → ℂ)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (hpos : ∀ i, 0 < (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re)
    (v : V) (hv : v ≠ 0) : 0 < g.rotatedRe φ v v := by
  rw [g.rotatedRe_apply_self φ b eig hdiag v]
  have hrepr : b.repr v ≠ 0 := fun h => hv (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hrepr
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hi₀
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hpos i).le (sq_nonneg _))
    ⟨i₀, Finset.mem_univ _, ?_⟩
  exact mul_pos (hpos i₀)
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi₀)))

/-- The inner-product core of `ĝ_R`, fed to `posDefCore` as-is (KS paper
Proposition 2.5: `ĝ_R` is the inner product of the pencil). -/
noncomputable def AllowableComplexMetric.rotatedCore (g : AllowableComplexMetric V)
    (φ : ℝ) (hpos : ∀ v, v ≠ 0 → 0 < g.rotatedRe φ v v) :
    InnerProductSpace.Core ℝ V :=
  KontsevichSegal.Hodge.posDefCore (g.rotatedRe φ) (g.rotatedRe_symm φ) hpos

omit [FiniteDimensional ℝ V] in
/-- A positive-definite bilinear form is nondegenerate (both slots separate points).
Extracted from the interior of `exists_basis_isOrtho_pair_of_posdef`
(`ComplexMetrics/Equivalence.lean`). -/
theorem nondegenerate_of_posDef (P : LinearMap.BilinForm ℝ V)
    (hpos : ∀ v, v ≠ 0 → 0 < P v v) : P.Nondegenerate := by
  constructor
  · intro x hx
    by_contra hx0
    exact (hpos x hx0).ne' (hx x)
  · intro y hy
    by_contra hy0
    exact (hpos y hy0).ne' (hy y)

end RotatedForms

/-! ## The self-adjoint pencil operator -/

section Pencil

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **The pencil operator** `T = P♭⁻¹ ∘ A♭` representing the bilinear form `A` in the
nondegenerate form `P` (KS paper Proposition 2.5: `P = ĝ_R`, `A = ĝ_I`). Mirrors the
operator constructed inside `exists_basis_isOrtho_pair_of_posdef`
(`ComplexMetrics/Equivalence.lean`). -/
noncomputable def pencilOperator (P A : LinearMap.BilinForm ℝ V)
    (hnd : P.Nondegenerate) : V →ₗ[ℝ] V :=
  (P.toDual hnd).symm.toLinearMap ∘ₗ A

/-- The defining pairing of the pencil operator: `P(T x, y) = A(x, y)`. -/
theorem pencilOperator_pairing (P A : LinearMap.BilinForm ℝ V)
    (hnd : P.Nondegenerate) (x y : V) :
    P (pencilOperator P A hnd x) y = A x y :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) (A x) y

/-- **The pencil operator is self-adjoint** in any inner product agreeing with `P`
(KS paper Proposition 2.5; the three-rewrite proof of
`exists_basis_isOrtho_pair_of_posdef`). Instantiated with the `posDefCore` instances of
`ĝ_R`, where `inner x y = ĝ_R x y` holds definitionally. -/
theorem isSymmetric_of_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P A : LinearMap.BilinForm ℝ E) (T : E →ₗ[ℝ] E)
    (hinner : ∀ x y : E, inner ℝ x y = P x y)
    (hPsymm : ∀ x y, P x y = P y x) (hAsymm : ∀ x y, A x y = A y x)
    (hT : ∀ x y, P (T x) y = A x y) : T.IsSymmetric := by
  intro x y
  change inner ℝ (T x) y = inner ℝ x (T y)
  rw [hinner, hinner, hT, hPsymm x (T y), hT, hAsymm y x]

/-- **The eigenvalue bridge** (KS paper Proposition 2.5): on a diagonalizing basis `b`
of an allowable metric `g` with rotated coefficients in the open right half-plane, the
pencil operator of `(ĝ_R, ĝ_I)` acts diagonally with eigenvalues the tangents of the
rotated angles: `T bᵢ = tan(arg(e^{-iφ}·λᵢ)) · bᵢ`. The eigenvalue is
`ĝ_I(bᵢ,bᵢ)/ĝ_R(bᵢ,bᵢ) = Im/Re` of the rotated coefficient, which is the tangent of
its argument. -/
theorem pencilOperator_eigen_basis {ι : Type*} [Fintype ι]
    (g : AllowableComplexMetric V) (φ : ℝ)
    (b : Module.Basis ι ℝ V) (eig : ι → ℂ)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (hpos : ∀ i, 0 < (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re)
    (hnd : (g.rotatedRe φ).Nondegenerate) (i : ι) :
    pencilOperator (g.rotatedRe φ) (g.rotatedIm φ) hnd (b i)
      = Real.tan (Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * eig i)) • b i := by
  classical
  -- `g.toForm` is diagonal on `b` (polarization).
  have hoff : ∀ p q, p ≠ q → g.toForm (b p) (b q) = 0 := fun p q hpq =>
    bilin_basis_eq_zero_of_ne g.toForm g.symmetric' b eig hdiag hpq
  have hdd : ∀ p, g.toForm (b p) (b p) = eig p := fun p =>
    bilin_basis_apply_self g.toForm b eig hdiag p
  -- Basis pairings of the rotated forms.
  have hRoff : ∀ p q, p ≠ q → g.rotatedRe φ (b p) (b q) = 0 := by
    intro p q hpq
    rw [g.rotatedRe_apply, hoff p q hpq, mul_zero, Complex.zero_re]
  have hIoff : ∀ p q, p ≠ q → g.rotatedIm φ (b p) (b q) = 0 := by
    intro p q hpq
    rw [g.rotatedIm_apply, hoff p q hpq, mul_zero, Complex.zero_im]
  have hRdd : ∀ p, g.rotatedRe φ (b p) (b p)
      = (Complex.exp (-(φ : ℂ) * Complex.I) * eig p).re := by
    intro p
    rw [g.rotatedRe_apply, hdd p]
  have hIdd : ∀ p, g.rotatedIm φ (b p) (b p)
      = (Complex.exp (-(φ : ℂ) * Complex.I) * eig p).im := by
    intro p
    rw [g.rotatedIm_apply, hdd p]
  -- The tangent identity `tan(arg z)·Re z = Im z` on the right half-plane.
  have htan : Real.tan (Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * eig i))
      * (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).re
      = (Complex.exp (-(φ : ℂ) * Complex.I) * eig i).im := by
    rw [Complex.tan_arg]
    exact div_mul_cancel₀ _ (hpos i).ne'
  -- `T bᵢ − tan(arg(e^{-iφ}λᵢ))·bᵢ` pairs to zero against every basis vector.
  have hzero : ∀ j, g.rotatedRe φ
      (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ) hnd (b i)
        - Real.tan (Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * eig i)) • b i)
      (b j) = 0 := by
    intro j
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      pencilOperator_pairing, smul_eq_mul]
    rcases eq_or_ne j i with rfl | hji
    · rw [hIdd j, hRdd j, htan, sub_self]
    · rw [hIoff i j (Ne.symm hji), hRoff i j (Ne.symm hji), mul_zero, sub_zero]
  -- Vanishing against a basis and nondegeneracy give the eigen-equation.
  have hfun : g.rotatedRe φ
      (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ) hnd (b i)
        - Real.tan (Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * eig i)) • b i)
      = 0 :=
    b.ext fun j => by rw [hzero j, LinearMap.zero_apply]
  have hker : pencilOperator (g.rotatedRe φ) (g.rotatedIm φ) hnd (b i)
      - Real.tan (Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * eig i)) • b i
      = 0 :=
    hnd.1 _ fun y => by rw [hfun, LinearMap.zero_apply]
  exact sub_eq_zero.mp hker

end Pencil

/-! ## Faithfulness gate: concrete evaluation of the eigenvalue formula

The abstract eigen-equation of `pencilOperator_eigen_basis` lives on an abstract `V`
through `BilinForm.toDual`, so it does not reduce under `decide`/`norm_num`; the
checks below instead evaluate the eigenvalue expression symbolically on the concrete
allowable pair `eig = (e^{iπ/3}, e^{-iπ/6})` (angle sum `π/3 + π/6 = π/2 < π`). The
arc of the construction is `[-Q, N] = [-π/6, π/3]`, so the midpoint rotation is
`φ = (N − Q)/2 = π/12`, and the rotated angles are `π/3 − π/12 = π/4` and
`−π/6 − π/12 = −π/4`: the two eigenvalues are `tan(π/4) = 1` and `tan(−π/4) = −1`,
both nonzero — no eigenvalue is spuriously forced to `0`. -/

/-- `arg(e^{iθ}) = θ` for `θ ∈ (−π, π]` (helper for the concrete checks). -/
theorem arg_exp_ofReal_mul_I {θ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    (Complex.exp ((θ : ℂ) * Complex.I)).arg = θ := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hθ

/-- The concrete pair satisfies the angle condition: both coefficients are nonzero
unit complex numbers off the negative real axis with `|π/3| + |−π/6| = π/2 < π`. -/
example : AngleCondition
    ![Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I),
      Complex.exp (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I)] := by
  have hπ := Real.pi_pos
  have h1 : (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)).arg = Real.pi / 3 :=
    arg_exp_ofReal_mul_I ⟨by linarith, by linarith⟩
  have h2 : (Complex.exp (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I)).arg
      = -(Real.pi / 6) :=
    arg_exp_ofReal_mul_I ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [Complex.exp_ne_zero]
  · intro i
    fin_cases i
    · left
      change 0 < (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)).re
      rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
      norm_num
    · left
      change 0 < (Complex.exp (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I)).re
      rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_div_six]
      positivity
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h1, h2, abs_of_pos (by positivity), abs_neg, abs_of_pos (by positivity)]
    linarith

/-- First eigenvalue of the concrete pair: with the midpoint rotation `φ = π/12`, the
rotated first coefficient is `e^{iπ/4}`, so the ITEM-5 eigenvalue expression evaluates
to `tan(π/4) = 1 ≠ 0`. -/
example :
    Real.tan (Complex.arg (Complex.exp (-((Real.pi / 12 : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I))) = 1 := by
  have hπ := Real.pi_pos
  have hcomb : Complex.exp (-((Real.pi / 12 : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcomb, arg_exp_ofReal_mul_I ⟨by linarith, by linarith⟩, Real.tan_pi_div_four]

/-- Second eigenvalue of the concrete pair: the rotated second coefficient is
`e^{-iπ/4}`, so the ITEM-5 eigenvalue expression evaluates to `tan(−π/4) = −1 ≠ 0`. -/
example :
    Real.tan (Complex.arg (Complex.exp (-((Real.pi / 12 : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I))) = -1 := by
  have hπ := Real.pi_pos
  have hcomb : Complex.exp (-((Real.pi / 12 : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcomb, arg_exp_ofReal_mul_I ⟨by linarith, by linarith⟩, Real.tan_neg,
    Real.tan_pi_div_four]

-- General Courant-Fischer (Mathlib-side; no Kontsevich-Segal content)

/-! ## General Courant-Fischer min-max for a symmetric operator

Pure spectral-theorem content over the reals: for `T : E ->l[R] E` symmetric on a
finite-dimensional real inner product space, the `k`-th eigenvalue of Mathlib's
decreasing enumeration `hT.eigenvalues hn` is characterized as a sup-inf (over
subspaces of dimension `k + 1`) and as an inf-sup (over subspaces of dimension
`n - k`) of the Rayleigh quotient `inner R (T x) x / ‖x‖ ^ 2`. The index sets are
encoded as subtypes so that no vacuous supremum or infimum of an empty family enters:
every index is a genuinely qualifying subspace, every inner family is nonempty, and
the Rayleigh quotient is uniformly bounded by the extreme eigenvalues. -/

section CourantFischer

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Real inner product expanded over an orthonormal basis:
`inner R x y = ∑ i, (repr x i) * (repr y i)`. -/
theorem real_inner_eq_sum_repr {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (x y : E) : inner ℝ x y = ∑ i, b.repr x i * b.repr y i := by
  conv_lhs => rw [← b.sum_repr x]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, ← b.repr_apply_apply]

/-- Norm squared expanded over an orthonormal basis: `‖x‖^2 = ∑ i, (repr x i)^2`. -/
theorem norm_sq_eq_sum_repr {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (x : E) : ‖x‖ ^ 2 = ∑ i, b.repr x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_sum_repr b x x]
  exact Finset.sum_congr rfl fun i _ => (pow_two _).symm

/-- For `x ≠ 0` the coordinate square sum is strictly positive. -/
theorem sum_repr_sq_pos {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {x : E}
    (hx : x ≠ 0) : 0 < ∑ i, b.repr x i ^ 2 := by
  rw [← norm_sq_eq_sum_repr b x]
  exact pow_pos (norm_pos_iff.mpr hx) 2

/-- A vector in the span of part of an orthonormal basis has vanishing coordinates
outside that part. -/
theorem repr_eq_zero_of_mem_span {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {m : ℕ} (f : Fin m → ι) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range fun i => b (f i))) {j : ι}
    (hj : ∀ i, f i ≠ j) : b.repr x j = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  rw [b.repr_apply_apply, inner_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [real_inner_smul_right, b.orthonormal.2 (Ne.symm (hj i)), mul_zero]

/-- The span of `m` distinct vectors of an orthonormal basis has dimension `m`. -/
theorem finrank_span_orthonormal_comp {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {m : ℕ} (f : Fin m → ι) (hf : Function.Injective f) :
    finrank ℝ (Submodule.span ℝ (Set.range fun i => b (f i))) = m := by
  have hli : LinearIndependent ℝ fun i => b (f i) :=
    (b.orthonormal.linearIndependent).comp f hf
  rw [finrank_span_eq_card hli, Fintype.card_fin]

variable [FiniteDimensional ℝ E] {n : ℕ} {T : E →ₗ[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- A submodule of positive dimension contains a nonzero vector. -/
theorem exists_ne_zero_mem_of_finrank_pos {S : Submodule ℝ E}
    (h : 0 < finrank ℝ S) : ∃ x : E, x ∈ S ∧ x ≠ 0 := by
  have hbot : S ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h
    exact lt_irrefl 0 h
  obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hbot
  exact ⟨x, hxS, hx0⟩

/-- **The dimension crux**: two subspaces whose dimensions add to more than `dim E`
intersect in a nonzero vector. -/
theorem exists_ne_zero_mem_inf_of_finrank_add (S W : Submodule ℝ E)
    (h : finrank ℝ E < finrank ℝ S + finrank ℝ W) :
    ∃ x : E, x ∈ S ⊓ W ∧ x ≠ 0 := by
  refine exists_ne_zero_mem_of_finrank_pos ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S W
  have h2 : finrank ℝ ↥(S ⊔ W) ≤ finrank ℝ E := Submodule.finrank_le _
  omega

/-- Coordinates of `T x` in the eigenbasis: `repr (T x) i = (eigenvalue i) * repr x i`. -/
theorem eigenvectorBasis_repr_T_apply (hT : T.IsSymmetric) (hn : finrank ℝ E = n)
    (x : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (T x) i
      = hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr x i := by
  rw [(hT.eigenvectorBasis hn).repr_apply_apply,
    ← hT (hT.eigenvectorBasis hn i) x, hT.apply_eigenvectorBasis,
    real_inner_smul_left]
  simp [(hT.eigenvectorBasis hn).repr_apply_apply, RCLike.ofReal_real_eq_id]

/-- **The Rayleigh quotient on the eigenbasis** (the workhorse): for every `x`,
`inner R (T x) x / ‖x‖^2 = (∑ i, μ_i (repr x i)^2) / (∑ i, (repr x i)^2)`. -/
theorem rayleigh_eq_sum (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (x : E) :
    inner ℝ (T x) x / ‖x‖ ^ 2
      = (∑ i, hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr x i ^ 2)
        / ∑ i, (hT.eigenvectorBasis hn).repr x i ^ 2 := by
  rw [real_inner_eq_sum_repr (hT.eigenvectorBasis hn) (T x) x,
    norm_sq_eq_sum_repr (hT.eigenvectorBasis hn) x]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eigenvectorBasis_repr_T_apply hT hn x i, pow_two]
  ring

/-- The Rayleigh quotient is bounded above by the largest eigenvalue. -/
theorem rayleigh_le_sup' (hT : T.IsSymmetric) (hn : finrank ℝ E = n)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) {x : E} (hx : x ≠ 0) :
    inner ℝ (T x) x / ‖x‖ ^ 2 ≤ Finset.univ.sup' hne (hT.eigenvalues hn) := by
  rw [rayleigh_eq_sum hT hn x,
    div_le_iff₀ (sum_repr_sq_pos (hT.eigenvectorBasis hn) hx)]
  calc (∑ i, hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr x i ^ 2)
      ≤ ∑ i, Finset.univ.sup' hne (hT.eigenvalues hn)
          * (hT.eigenvectorBasis hn).repr x i ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ i)) (sq_nonneg _)
    _ = Finset.univ.sup' hne (hT.eigenvalues hn)
          * ∑ i, (hT.eigenvectorBasis hn).repr x i ^ 2 := by rw [Finset.mul_sum]

/-- The Rayleigh quotient is bounded below by the smallest eigenvalue. -/
theorem inf'_le_rayleigh (hT : T.IsSymmetric) (hn : finrank ℝ E = n)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) {x : E} (hx : x ≠ 0) :
    Finset.univ.inf' hne (hT.eigenvalues hn) ≤ inner ℝ (T x) x / ‖x‖ ^ 2 := by
  rw [rayleigh_eq_sum hT hn x,
    le_div_iff₀ (sum_repr_sq_pos (hT.eigenvectorBasis hn) hx)]
  calc Finset.univ.inf' hne (hT.eigenvalues hn)
        * ∑ i, (hT.eigenvectorBasis hn).repr x i ^ 2
      = ∑ i, Finset.univ.inf' hne (hT.eigenvalues hn)
          * (hT.eigenvectorBasis hn).repr x i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i, hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr x i ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i)) (sq_nonneg _)

/-- The span of the top `k + 1` eigenvectors (indices `0, …, k`). -/
noncomputable def lowSpan (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (k : Fin n) :
    Submodule ℝ E :=
  Submodule.span ℝ
    (Set.range fun i : Fin ((k : ℕ) + 1) => hT.eigenvectorBasis hn (Fin.castLE k.isLt i))

/-- The index embedding `Fin (n - k) → Fin n`, `i ↦ k + i`, onto indices `≥ k`. -/
def highIdx (k : Fin n) (i : Fin (n - (k : ℕ))) : Fin n :=
  ⟨(k : ℕ) + i.1, by have h1 := i.2; have h2 := k.isLt; omega⟩

/-- The span of the bottom `n - k` eigenvectors (indices `k, …, n - 1`). -/
noncomputable def highSpan (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (k : Fin n) :
    Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i => hT.eigenvectorBasis hn (highIdx k i))

theorem finrank_lowSpan (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (k : Fin n) :
    finrank ℝ (lowSpan hT hn k) = (k : ℕ) + 1 :=
  finrank_span_orthonormal_comp _ _ (Fin.castLE_injective k.isLt)

theorem finrank_highSpan (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (k : Fin n) :
    finrank ℝ (highSpan hT hn k) = n - (k : ℕ) := by
  refine finrank_span_orthonormal_comp _ _ fun a b hab => ?_
  have hval : (k : ℕ) + a.1 = (k : ℕ) + b.1 := congrArg Fin.val hab
  exact Fin.ext (by omega)

/-- On the span of the top `k + 1` eigenvectors the Rayleigh quotient is at least the
`k`-th eigenvalue (the coordinates live where the eigenvalues are `≥ μ_k`). -/
theorem eigenvalue_le_rayleigh_of_mem_lowSpan (hT : T.IsSymmetric)
    (hn : finrank ℝ E = n) (k : Fin n) {x : E} (hx : x ∈ lowSpan hT hn k)
    (hx0 : x ≠ 0) : hT.eigenvalues hn k ≤ inner ℝ (T x) x / ‖x‖ ^ 2 := by
  rw [rayleigh_eq_sum hT hn x,
    le_div_iff₀ (sum_repr_sq_pos (hT.eigenvectorBasis hn) hx0), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases eq_or_ne ((hT.eigenvectorBasis hn).repr x i) 0 with h0 | h0
  · rw [h0]
    simp
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hex : ∃ i' : Fin ((k : ℕ) + 1), Fin.castLE k.isLt i' = i := by
      by_contra hno
      push_neg at hno
      exact h0 (repr_eq_zero_of_mem_span (hT.eigenvectorBasis hn)
        (Fin.castLE k.isLt) hx hno)
    obtain ⟨i', rfl⟩ := hex
    have hle : Fin.castLE k.isLt i' ≤ k := by
      rw [Fin.le_def]
      simpa using Nat.lt_succ_iff.mp i'.isLt
    exact hT.eigenvalues_antitone hn hle

/-- On the span of the bottom `n - k` eigenvectors the Rayleigh quotient is at most
the `k`-th eigenvalue (the coordinates live where the eigenvalues are `≤ μ_k`). -/
theorem rayleigh_le_eigenvalue_of_mem_highSpan (hT : T.IsSymmetric)
    (hn : finrank ℝ E = n) (k : Fin n) {x : E} (hx : x ∈ highSpan hT hn k)
    (hx0 : x ≠ 0) : inner ℝ (T x) x / ‖x‖ ^ 2 ≤ hT.eigenvalues hn k := by
  rw [rayleigh_eq_sum hT hn x,
    div_le_iff₀ (sum_repr_sq_pos (hT.eigenvectorBasis hn) hx0), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases eq_or_ne ((hT.eigenvectorBasis hn).repr x i) 0 with h0 | h0
  · rw [h0]
    simp
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hex : ∃ i' : Fin (n - (k : ℕ)), highIdx k i' = i := by
      by_contra hno
      push_neg at hno
      exact h0 (repr_eq_zero_of_mem_span (hT.eigenvectorBasis hn) (highIdx k) hx hno)
    obtain ⟨i', rfl⟩ := hex
    have hle : k ≤ highIdx k i' := by
      rw [Fin.le_def]
      exact Nat.le_add_right _ _
    exact hT.eigenvalues_antitone hn hle

/-- **Courant-Fischer, sup-inf form**: the `k`-th eigenvalue (decreasing order) is the
supremum over `(k+1)`-dimensional subspaces `S` of the infimum of the Rayleigh
quotient over nonzero vectors of `S`. -/
theorem eigenvalues_eq_iSup_iInf_rayleigh (hT : T.IsSymmetric)
    (hn : finrank ℝ E = n) (k : Fin n) :
    hT.eigenvalues hn k
      = ⨆ S : {S : Submodule ℝ E // finrank ℝ S = (k : ℕ) + 1},
          ⨅ x : {x : E // x ∈ S.1 ∧ x ≠ 0}, inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2 := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨k, Finset.mem_univ k⟩
  haveI hSne : Nonempty {S : Submodule ℝ E // finrank ℝ S = (k : ℕ) + 1} :=
    ⟨⟨lowSpan hT hn k, finrank_lowSpan hT hn k⟩⟩
  have hxne : ∀ S : {S : Submodule ℝ E // finrank ℝ S = (k : ℕ) + 1},
      Nonempty {x : E // x ∈ S.1 ∧ x ≠ 0} := by
    intro S
    obtain ⟨x, hxS, hx0⟩ := exists_ne_zero_mem_of_finrank_pos (S := S.1)
      (by rw [S.2]; omega)
    exact ⟨⟨x, hxS, hx0⟩⟩
  have hbdd : ∀ S : {S : Submodule ℝ E // finrank ℝ S = (k : ℕ) + 1},
      BddBelow (Set.range fun x : {x : E // x ∈ S.1 ∧ x ≠ 0} =>
        inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    intro S
    refine ⟨Finset.univ.inf' hne (hT.eigenvalues hn), ?_⟩
    rintro r ⟨x, rfl⟩
    exact inf'_le_rayleigh hT hn hne x.2.2
  have houter : BddAbove (Set.range
      fun S : {S : Submodule ℝ E // finrank ℝ S = (k : ℕ) + 1} =>
        ⨅ x : {x : E // x ∈ S.1 ∧ x ≠ 0}, inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    refine ⟨Finset.univ.sup' hne (hT.eigenvalues hn), ?_⟩
    rintro r ⟨S, rfl⟩
    obtain ⟨x⟩ := hxne S
    exact le_trans (ciInf_le (hbdd S) x) (rayleigh_le_sup' hT hn hne x.2.2)
  refine le_antisymm ?_ ?_
  · refine le_ciSup_of_le houter ⟨lowSpan hT hn k, finrank_lowSpan hT hn k⟩ ?_
    haveI := hxne ⟨lowSpan hT hn k, finrank_lowSpan hT hn k⟩
    exact le_ciInf fun x =>
      eigenvalue_le_rayleigh_of_mem_lowSpan hT hn k x.2.1 x.2.2
  · refine ciSup_le fun S => ?_
    obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem_inf_of_finrank_add S.1
      (highSpan hT hn k)
      (by rw [S.2, finrank_highSpan hT hn k, hn]; have := k.isLt; omega)
    obtain ⟨hxS, hxW⟩ := Submodule.mem_inf.mp hx
    exact le_trans (ciInf_le (hbdd S) ⟨x, hxS, hx0⟩)
      (rayleigh_le_eigenvalue_of_mem_highSpan hT hn k hxW hx0)

/-- **Courant-Fischer, inf-sup form**: the `k`-th eigenvalue (decreasing order) is the
infimum over `(n-k)`-dimensional subspaces `S` of the supremum of the Rayleigh
quotient over nonzero vectors of `S`. Proved directly by the symmetric dimension
count (not by reflection through `-T`). -/
theorem eigenvalues_eq_iInf_iSup_rayleigh (hT : T.IsSymmetric)
    (hn : finrank ℝ E = n) (k : Fin n) :
    hT.eigenvalues hn k
      = ⨅ S : {S : Submodule ℝ E // finrank ℝ S = n - (k : ℕ)},
          ⨆ x : {x : E // x ∈ S.1 ∧ x ≠ 0}, inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2 := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨k, Finset.mem_univ k⟩
  haveI hSne : Nonempty {S : Submodule ℝ E // finrank ℝ S = n - (k : ℕ)} :=
    ⟨⟨highSpan hT hn k, finrank_highSpan hT hn k⟩⟩
  have hxne : ∀ S : {S : Submodule ℝ E // finrank ℝ S = n - (k : ℕ)},
      Nonempty {x : E // x ∈ S.1 ∧ x ≠ 0} := by
    intro S
    obtain ⟨x, hxS, hx0⟩ := exists_ne_zero_mem_of_finrank_pos (S := S.1)
      (by rw [S.2]; have := k.isLt; omega)
    exact ⟨⟨x, hxS, hx0⟩⟩
  have hbdd : ∀ S : {S : Submodule ℝ E // finrank ℝ S = n - (k : ℕ)},
      BddAbove (Set.range fun x : {x : E // x ∈ S.1 ∧ x ≠ 0} =>
        inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    intro S
    refine ⟨Finset.univ.sup' hne (hT.eigenvalues hn), ?_⟩
    rintro r ⟨x, rfl⟩
    exact rayleigh_le_sup' hT hn hne x.2.2
  have houter : BddBelow (Set.range
      fun S : {S : Submodule ℝ E // finrank ℝ S = n - (k : ℕ)} =>
        ⨆ x : {x : E // x ∈ S.1 ∧ x ≠ 0}, inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    refine ⟨Finset.univ.inf' hne (hT.eigenvalues hn), ?_⟩
    rintro r ⟨S, rfl⟩
    obtain ⟨x⟩ := hxne S
    exact le_trans (inf'_le_rayleigh hT hn hne x.2.2) (le_ciSup (hbdd S) x)
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun S => ?_
    obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem_inf_of_finrank_add S.1
      (lowSpan hT hn k)
      (by rw [S.2, finrank_lowSpan hT hn k, hn]; have := k.isLt; omega)
    obtain ⟨hxS, hxW⟩ := Submodule.mem_inf.mp hx
    exact le_trans (eigenvalue_le_rayleigh_of_mem_lowSpan hT hn k hxW hx0)
      (le_ciSup (hbdd S) ⟨x, hxS, hx0⟩)
  · refine ciInf_le_of_le houter ⟨highSpan hT hn k, finrank_highSpan hT hn k⟩ ?_
    haveI := hxne ⟨highSpan hT hn k, finrank_highSpan hT hn k⟩
    exact ciSup_le fun x =>
      rayleigh_le_eigenvalue_of_mem_highSpan hT hn k x.2.1 x.2.2

end CourantFischer

/-! ### Faithfulness gate for the min-max

The abstract statements are indexed by `Submodule`s of an abstract `E` and pass
through Mathlib's choice-based `eigenvalues`, so they do not reduce under
`decide`/`norm_num`. The checks below therefore evaluate the min-max content on the
concrete diagonal operator `(3, 1, -2)` on `EuclideanSpace ℝ (Fin 3)` (eigenvalues
already in decreasing order, middle eigenvalue `1` at `k = 1`):

* on the achieving `2`-dimensional plane `{x | x 2 = 0}` (= sup-inf witness for
  `k = 1`, dimension `k + 1 = 2`) the Rayleigh quotient is `≥ 1`, with value exactly
  `1` at `e₁` — the max-min at `k = 1` is `1`, not the extremes `3` or `-2`;
* the plane `{x | x 0 = 0}` (= inf-sup witness for `k = 1`, dimension `n - k = 2`)
  has Rayleigh quotient `≤ 1`, again with value `1` at `e₁`;
* a wrong plane (`span {e₀, e₂}`) contains `e₂` with Rayleigh value `-2 < 1`, so its
  inf does not beat the achieving plane. -/

/-- The diagonal operator `(3, 1, -2)` on `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def diagOp3 : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
    ∘ₗ (LinearMap.pi fun i => (![3, 1, -2] i : ℝ) • LinearMap.proj i)
    ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

@[simp] theorem diagOp3_apply (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    diagOp3 x i = ![3, 1, -2] i * x i := rfl

/-- The diagonal operator is symmetric. -/
theorem diagOp3_isSymmetric : diagOp3.IsSymmetric := by
  intro x y
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_repr, diagOp3_apply]
  ring

/-- On the sup-inf witness plane `{x | x 2 = 0}` (dimension `k + 1 = 2` for `k = 1`)
the Rayleigh quotient of `diag (3, 1, -2)` is at least the middle eigenvalue `1`. -/
example {x : EuclideanSpace ℝ (Fin 3)} (h2 : x 2 = 0) (hx : x ≠ 0) :
    1 ≤ inner ℝ (diagOp3 x) x / ‖x‖ ^ 2 := by
  have hden : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    rcases eq_or_ne (x 0) 0 with h0 | h0
    · rcases eq_or_ne (x 1) 0 with h1 | h1
      · exfalso
        apply hx
        ext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      · have := lt_of_le_of_ne (sq_nonneg (x 1)) (Ne.symm (pow_ne_zero 2 h1))
        nlinarith [sq_nonneg (x 0)]
    · have := lt_of_le_of_ne (sq_nonneg (x 0)) (Ne.symm (pow_ne_zero 2 h0))
      nlinarith [sq_nonneg (x 1)]
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    norm_sq_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [EuclideanSpace.basisFun_repr, diagOp3_apply, h2, mul_zero,
    add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [le_div_iff₀ (by nlinarith [hden])]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- On the inf-sup witness plane `{x | x 0 = 0}` (dimension `n - k = 2` for `k = 1`)
the Rayleigh quotient of `diag (3, 1, -2)` is at most the middle eigenvalue `1`. -/
example {x : EuclideanSpace ℝ (Fin 3)} (h0 : x 0 = 0) (hx : x ≠ 0) :
    inner ℝ (diagOp3 x) x / ‖x‖ ^ 2 ≤ 1 := by
  have hden : 0 < x 1 ^ 2 + x 2 ^ 2 := by
    rcases eq_or_ne (x 1) 0 with h1 | h1
    · rcases eq_or_ne (x 2) 0 with h2 | h2
      · exfalso
        apply hx
        ext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      · have := lt_of_le_of_ne (sq_nonneg (x 2)) (Ne.symm (pow_ne_zero 2 h2))
        nlinarith [sq_nonneg (x 1)]
    · have := lt_of_le_of_ne (sq_nonneg (x 1)) (Ne.symm (pow_ne_zero 2 h1))
      nlinarith [sq_nonneg (x 2)]
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    norm_sq_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    Fin.sum_univ_three, Fin.sum_univ_three]
  have hc2 : (![(3 : ℝ), 1, -2]) 2 = -2 := rfl
  simp only [EuclideanSpace.basisFun_repr, diagOp3_apply, h0, mul_zero,
    zero_add, Matrix.cons_val_zero, Matrix.cons_val_one, hc2, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [div_le_iff₀ (by nlinarith [hden])]
  nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]

/-- The middle eigenvalue is attained at `e₁`: Rayleigh value exactly `1`. -/
example :
    inner ℝ (diagOp3 (EuclideanSpace.single 1 1)) (EuclideanSpace.single 1 1)
      / ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 := by
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    norm_sq_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    Fin.sum_univ_three, Fin.sum_univ_three]
  have hc2 : (![(3 : ℝ), 1, -2]) 2 = -2 := rfl
  have h21 : ¬((2 : Fin 3) = 1) := by decide
  norm_num [EuclideanSpace.basisFun_repr, diagOp3_apply, EuclideanSpace.single_apply,
    hc2, h21]

/-- A wrong plane cannot beat the max-min: `span {e₀, e₂}` contains `e₂`, whose
Rayleigh value is `-2 < 1`, so the infimum over that plane is `< 1`. -/
example :
    inner ℝ (diagOp3 (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1)
      / ‖(EuclideanSpace.single 2 1 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = -2 := by
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    norm_sq_eq_sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ),
    Fin.sum_univ_three, Fin.sum_univ_three]
  have hc2 : (![(3 : ℝ), 1, -2]) 2 = -2 := rfl
  have h02 : ¬((0 : Fin 3) = 2) := by decide
  have h12 : ¬((1 : Fin 3) = 2) := by decide
  norm_num [EuclideanSpace.basisFun_repr, diagOp3_apply, EuclideanSpace.single_apply,
    hc2, h02, h12]

-- KS angle min-max (phi-free; transport of Courant-Fischer)

/-! ## KS angle min-max: transport of Courant-Fischer through `arctan` and the rotation

KS paper Proposition 2.5 (p. 13): the critical angles of `v ↦ arg g(v)` are
characterized by a min-max over subspaces. `ksAngle` below is that min-max, stated
canonically (choice-free, a function of `g` alone). For any global rotation `φ` of the
angle condition the pointwise identity
`arg g(x,x) = arctan(⟪T x, x⟫/‖x‖²) + φ` holds for the pencil operator `T` of
`(ĝ_R, ĝ_I)`, so the Courant-Fischer characterizations of checkpoint 2a transport
through the monotone continuous `arctan` and the constant shift `φ`: the `k`-th KS
angle is `arctan(μ_k) + φ` (with `μ` the decreasing eigenvalues of `T`), and equals the
dual inf-sup of `arg g` — with `φ` absent from both statements' interfaces. -/

section KSAngleMinmax

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Every allowable metric admits a rotation making `ĝ_R` positive-definite
(packaging `AngleCondition.exists_rotation` + `rotatedRe_posDef` over the
`angle_cond` witness). -/
theorem exists_rotation_posDef (g : AllowableComplexMetric V) :
    ∃ φ : ℝ, |φ| < Real.pi / 2 ∧ ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x := by
  obtain ⟨b, eig, hAC, hdiag⟩ := g.angle_cond
  obtain ⟨φ, hφ, -, hposI⟩ := hAC.exists_rotation
  exact ⟨φ, hφ, fun x hx => g.rotatedRe_posDef φ b eig hdiag hposI x hx⟩

/-- The rotated value `e^{-iφ}·g(x,x)` has argument in `(-π/2, π/2)` for `x ≠ 0`
(STEP 2(i): positivity of `ĝ_R` is positivity of the rotated real part). -/
theorem abs_arg_rotated_lt_pi_div_two (g : AllowableComplexMetric V) (φ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x) {x : V} (hx : x ≠ 0) :
    |Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm x x)| < Real.pi / 2 := by
  refine Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
  have h := hpos x hx
  rwa [g.rotatedRe_apply] at h

/-- STEP 2(ii): the rotation shifts the argument exactly, with no `2π` wrap:
`arg g(x,x) = arg(e^{-iφ}·g(x,x)) + φ`. Both the rotated argument and `φ` lie in
`(-π/2, π/2)`, so their sum stays in `(-π, π)` and `Complex.arg_mul` applies. -/
theorem arg_toForm_eq_arg_rotated_add (g : AllowableComplexMetric V) (φ : ℝ)
    (hφ : |φ| < Real.pi / 2)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x) {x : V} (hx : x ≠ 0) :
    Complex.arg (g.toForm x x)
      = Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm x x) + φ := by
  set w := Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm x x with hw
  have hwre : 0 < w.re := by
    have h := hpos x hx
    rwa [g.rotatedRe_apply] at h
  have hwne : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre
  have hargw : |w.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hπ := Real.pi_pos
  have h1 := abs_lt.mp hφ
  have h2 := abs_lt.mp hargw
  have hargexp : (Complex.exp ((φ : ℂ) * Complex.I)).arg = φ :=
    arg_exp_ofReal_mul_I ⟨by linarith, by linarith⟩
  have hz : g.toForm x x = Complex.exp ((φ : ℂ) * Complex.I) * w := by
    rw [hw, ← mul_assoc, ← Complex.exp_add,
      show (φ : ℂ) * Complex.I + -(φ : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero, one_mul]
  rw [hz, Complex.arg_mul (Complex.exp_ne_zero _) hwne
    (by rw [hargexp]; exact ⟨by linarith, by linarith⟩), hargexp]
  exact add_comm φ w.arg

/-- STEP 1: the Rayleigh quotient of the pencil is the tangent of the rotated
argument, `ĝ_I(x,x)/ĝ_R(x,x) = tan(arg(e^{-iφ}·g(x,x)))`. Under the `posDefCore`
instances of `ĝ_R` the left side is `⟪T x, x⟫/‖x‖²` for the pencil operator `T`
(used in that form inside the transport theorems). -/
theorem pencil_rayleigh_eq_tan (g : AllowableComplexMetric V) (φ : ℝ) (x : V) :
    g.rotatedIm φ x x / g.rotatedRe φ x x
      = Real.tan (Complex.arg (Complex.exp (-(φ : ℂ) * Complex.I) * g.toForm x x)) := by
  rw [g.rotatedIm_apply, g.rotatedRe_apply, Complex.tan_arg]

/-- STEP 2(iii): `arctan(ĝ_I(x,x)/ĝ_R(x,x)) = arg g(x,x) − φ` for `x ≠ 0`. -/
theorem arctan_pencil_rayleigh_eq_arg_sub (g : AllowableComplexMetric V) (φ : ℝ)
    (hφ : |φ| < Real.pi / 2)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x) {x : V} (hx : x ≠ 0) :
    Real.arctan (g.rotatedIm φ x x / g.rotatedRe φ x x)
      = Complex.arg (g.toForm x x) - φ := by
  have hargw := abs_arg_rotated_lt_pi_div_two g φ hpos hx
  rw [pencil_rayleigh_eq_tan g φ x,
    Real.arctan_tan (abs_lt.mp hargw).1 (abs_lt.mp hargw).2,
    arg_toForm_eq_arg_rotated_add g φ hφ hpos hx]
  ring

end KSAngleMinmax

/-! ### `arctan` and constant shifts through conditional suprema and infima -/

section ArctanTransport

/-- `arctan` commutes with a bounded-below conditional infimum. -/
theorem arctan_ciInf {ι : Sort*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddBelow (Set.range f)) :
    Real.arctan (⨅ i, f i) = ⨅ i, Real.arctan (f i) :=
  Monotone.map_ciInf_of_continuousAt (f := Real.arctan)
    (Real.continuous_arctan.continuousAt) Real.arctan_mono hb

/-- `arctan` commutes with a bounded-above conditional supremum. -/
theorem arctan_ciSup {ι : Sort*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddAbove (Set.range f)) :
    Real.arctan (⨆ i, f i) = ⨆ i, Real.arctan (f i) :=
  Monotone.map_ciSup_of_continuousAt (f := Real.arctan)
    (Real.continuous_arctan.continuousAt) Real.arctan_mono hb

/-- Adding a constant commutes with a bounded-below conditional infimum. -/
theorem ciInf_add_const {ι : Sort*} [Nonempty ι] (f : ι → ℝ) (c : ℝ)
    (hb : BddBelow (Set.range f)) :
    (⨅ i, f i) + c = ⨅ i, (f i + c) :=
  Monotone.map_ciInf_of_continuousAt (f := fun r : ℝ => r + c)
    ((continuous_id.add continuous_const).continuousAt)
    (fun _ _ h => by exact add_le_add h le_rfl) hb

/-- Adding a constant commutes with a bounded-above conditional supremum. -/
theorem ciSup_add_const {ι : Sort*} [Nonempty ι] (f : ι → ℝ) (c : ℝ)
    (hb : BddAbove (Set.range f)) :
    (⨆ i, f i) + c = ⨆ i, (f i + c) :=
  Monotone.map_ciSup_of_continuousAt (f := fun r : ℝ => r + c)
    ((continuous_id.add continuous_const).continuousAt)
    (fun _ _ h => by exact add_le_add h le_rfl) hb

/-- The range of an `arctan`-composed family is bounded below by `-π/2`. -/
theorem bddBelow_range_arctan {ι : Sort*} (f : ι → ℝ) :
    BddBelow (Set.range fun i => Real.arctan (f i)) := by
  refine ⟨-(Real.pi / 2), ?_⟩
  rintro r ⟨i, rfl⟩
  exact (Real.arctan_mem_Ioo _).1.le

/-- The range of an `arctan`-composed family is bounded above by `π/2`. -/
theorem bddAbove_range_arctan {ι : Sort*} (f : ι → ℝ) :
    BddAbove (Set.range fun i => Real.arctan (f i)) := by
  refine ⟨Real.pi / 2, ?_⟩
  rintro r ⟨i, rfl⟩
  exact (Real.arctan_mem_Ioo _).2.le

end ArctanTransport

/-! ### The phi-free KS angle min-max -/

section KSAngleMain

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The decreasing eigenvalues of the pencil operator of `(ĝ_R, ĝ_I)`, with the
`posDefCore` inner-product instances of `ĝ_R` installed locally (this realizes
`hT.eigenvalues hn` as an instance-free function of `(g, φ, hpos)`). -/
noncomputable def pencilEigenvalues (g : AllowableComplexMetric V) (φ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x) {n : ℕ}
    (hn : Module.finrank ℝ V = n) : Fin n → ℝ :=
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
  LinearMap.IsSymmetric.eigenvalues
    (isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ)
      (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
        (nondegenerate_of_posDef (g.rotatedRe φ) hpos))
      (fun _ _ => rfl) (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
      (fun x y => pencilOperator_pairing _ _ _ x y)) hn

/-- **The KS critical angles** (KS paper Proposition 2.5): the `k`-th angle of
`v ↦ arg g(v)`, defined canonically (choice-free) as the sup-inf of `arg g(x,x)` over
`(k+1)`-dimensional subspaces, in the same junk-free subtype encoding as the
Courant-Fischer theorems. -/
noncomputable def ksAngle (g : AllowableComplexMetric V)
    (k : Fin (Module.finrank ℝ V)) : ℝ :=
  ⨆ S : {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1},
    ⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1)

/-- **The KS angles are arctangents of the pencil eigenvalues, shifted by the
rotation** (KS paper Proposition 2.5, sup-inf form): `ksAngle g k = arctan(μ_k) + φ`
for any rotation `φ` with `ĝ_R` positive-definite. This transports checkpoint 2a's
`eigenvalues_eq_iSup_iInf_rayleigh` through `arctan` and the constant shift `φ`. -/
theorem ksAngle_eq_arctan_eigenvalue (g : AllowableComplexMetric V) (φ : ℝ)
    (hφ : |φ| < Real.pi / 2)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x)
    (k : Fin (Module.finrank ℝ V)) :
    ksAngle g k = Real.arctan (pencilEigenvalues g φ hpos rfl k) + φ := by
  classical
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
  have hTsym : (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
      (nondegenerate_of_posDef (g.rotatedRe φ) hpos)).IsSymmetric :=
    isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ (fun _ _ => rfl)
      (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
      (fun x y => pencilOperator_pairing _ _ _ x y)
  set T := pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
    (nondegenerate_of_posDef (g.rotatedRe φ) hpos) with hTdef
  have hpe : pencilEigenvalues g φ hpos rfl = hTsym.eigenvalues rfl := rfl
  -- the Rayleigh quotient of `T` is the `ĝ` ratio
  have hray : ∀ x : V, inner ℝ (T x) x / ‖x‖ ^ 2
      = g.rotatedIm φ x x / g.rotatedRe φ x x := by
    intro x
    have h1 : inner ℝ (T x) x = g.rotatedIm φ x x :=
      pencilOperator_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ x x
    have h2 : ‖x‖ ^ 2 = g.rotatedRe φ x x := by
      rw [← real_inner_self_eq_norm_sq]
      rfl
    rw [h1, h2]
  -- pointwise: arg g(x,x) = arctan (Rayleigh x) + φ
  have hpt : ∀ (x : V), x ≠ 0 →
      Complex.arg (g.toForm x x)
        = Real.arctan (inner ℝ (T x) x / ‖x‖ ^ 2) + φ := by
    intro x hx
    rw [hray x, arctan_pencil_rayleigh_eq_arg_sub g φ hφ hpos hx]
    ring
  -- side facts for the transport
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ V))).Nonempty :=
    ⟨k, Finset.mem_univ k⟩
  haveI hSne : Nonempty {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1} :=
    ⟨⟨lowSpan hTsym rfl k, finrank_lowSpan hTsym rfl k⟩⟩
  have hxne : ∀ S : {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1},
      Nonempty {x : V // x ∈ S.1 ∧ x ≠ 0} := by
    intro S
    obtain ⟨x, hxS, hx0⟩ := exists_ne_zero_mem_of_finrank_pos (S := S.1)
      (by rw [S.2]; omega)
    exact ⟨⟨x, hxS, hx0⟩⟩
  have hbddR : ∀ S : {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1},
      BddBelow (Set.range fun x : {x : V // x ∈ S.1 ∧ x ≠ 0} =>
        inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    intro S
    refine ⟨Finset.univ.inf' hne (hTsym.eigenvalues rfl), ?_⟩
    rintro r ⟨x, rfl⟩
    exact inf'_le_rayleigh hTsym rfl hne x.2.2
  -- inner transport, per subspace
  have hInner : ∀ S : {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1},
      (⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1))
        = Real.arctan (⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0},
            inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) + φ := by
    intro S
    haveI := hxne S
    have hfx : (fun x : {x : V // x ∈ S.1 ∧ x ≠ 0} =>
        Complex.arg (g.toForm x.1 x.1))
        = fun x => Real.arctan (inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) + φ :=
      funext fun x => hpt x.1 x.2.2
    rw [hfx, ← ciInf_add_const _ φ (bddBelow_range_arctan _),
      ← arctan_ciInf _ (hbddR S)]
  -- outer transport
  have hfS : (fun S : {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1} =>
      ⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1))
      = fun S => Real.arctan (⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0},
          inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) + φ :=
    funext hInner
  have hbddU : BddAbove (Set.range
      fun S : {S : Submodule ℝ V // finrank ℝ S = (k : ℕ) + 1} =>
        ⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    refine ⟨Finset.univ.sup' hne (hTsym.eigenvalues rfl), ?_⟩
    rintro r ⟨S, rfl⟩
    obtain ⟨x⟩ := hxne S
    exact le_trans (ciInf_le (hbddR S) x) (rayleigh_le_sup' hTsym rfl hne x.2.2)
  unfold ksAngle
  rw [hfS, ← ciSup_add_const _ φ (bddAbove_range_arctan _),
    ← arctan_ciSup _ hbddU, ← eigenvalues_eq_iSup_iInf_rayleigh hTsym rfl k, hpe]

/-- **The dual inf-sup characterization of the KS angles** (φ-free): the `k`-th angle
is also the inf-sup of `arg g(x,x)` over `(n−k)`-dimensional subspaces, transporting
checkpoint 2a's `eigenvalues_eq_iInf_iSup_rayleigh`. This is the form the interlacing
lower bound consumes. -/
theorem ksAngle_eq_iInf_iSup (g : AllowableComplexMetric V)
    (k : Fin (Module.finrank ℝ V)) :
    ksAngle g k
      = ⨅ S : {S : Submodule ℝ V // finrank ℝ S = Module.finrank ℝ V - (k : ℕ)},
          ⨆ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1) := by
  classical
  obtain ⟨φ, hφ, hpos⟩ := exists_rotation_posDef g
  rw [ksAngle_eq_arctan_eigenvalue g φ hφ hpos k]
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
  have hTsym : (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
      (nondegenerate_of_posDef (g.rotatedRe φ) hpos)).IsSymmetric :=
    isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ (fun _ _ => rfl)
      (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
      (fun x y => pencilOperator_pairing _ _ _ x y)
  set T := pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
    (nondegenerate_of_posDef (g.rotatedRe φ) hpos) with hTdef
  have hpe : pencilEigenvalues g φ hpos rfl = hTsym.eigenvalues rfl := rfl
  have hray : ∀ x : V, inner ℝ (T x) x / ‖x‖ ^ 2
      = g.rotatedIm φ x x / g.rotatedRe φ x x := by
    intro x
    have h1 : inner ℝ (T x) x = g.rotatedIm φ x x :=
      pencilOperator_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ x x
    have h2 : ‖x‖ ^ 2 = g.rotatedRe φ x x := by
      rw [← real_inner_self_eq_norm_sq]
      rfl
    rw [h1, h2]
  have hpt : ∀ (x : V), x ≠ 0 →
      Complex.arg (g.toForm x x)
        = Real.arctan (inner ℝ (T x) x / ‖x‖ ^ 2) + φ := by
    intro x hx
    rw [hray x, arctan_pencil_rayleigh_eq_arg_sub g φ hφ hpos hx]
    ring
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ V))).Nonempty :=
    ⟨k, Finset.mem_univ k⟩
  haveI hSne : Nonempty
      {S : Submodule ℝ V // finrank ℝ S = Module.finrank ℝ V - (k : ℕ)} :=
    ⟨⟨highSpan hTsym rfl k, finrank_highSpan hTsym rfl k⟩⟩
  have hxne : ∀ S : {S : Submodule ℝ V //
      finrank ℝ S = Module.finrank ℝ V - (k : ℕ)},
      Nonempty {x : V // x ∈ S.1 ∧ x ≠ 0} := by
    intro S
    obtain ⟨x, hxS, hx0⟩ := exists_ne_zero_mem_of_finrank_pos (S := S.1)
      (by rw [S.2]; have := k.isLt; omega)
    exact ⟨⟨x, hxS, hx0⟩⟩
  have hbddR : ∀ S : {S : Submodule ℝ V //
      finrank ℝ S = Module.finrank ℝ V - (k : ℕ)},
      BddAbove (Set.range fun x : {x : V // x ∈ S.1 ∧ x ≠ 0} =>
        inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    intro S
    refine ⟨Finset.univ.sup' hne (hTsym.eigenvalues rfl), ?_⟩
    rintro r ⟨x, rfl⟩
    exact rayleigh_le_sup' hTsym rfl hne x.2.2
  have hInner : ∀ S : {S : Submodule ℝ V //
      finrank ℝ S = Module.finrank ℝ V - (k : ℕ)},
      (⨆ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1))
        = Real.arctan (⨆ x : {x : V // x ∈ S.1 ∧ x ≠ 0},
            inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) + φ := by
    intro S
    haveI := hxne S
    have hfx : (fun x : {x : V // x ∈ S.1 ∧ x ≠ 0} =>
        Complex.arg (g.toForm x.1 x.1))
        = fun x => Real.arctan (inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) + φ :=
      funext fun x => hpt x.1 x.2.2
    rw [hfx, ← ciSup_add_const _ φ (bddAbove_range_arctan _),
      ← arctan_ciSup _ (hbddR S)]
  have hfS : (fun S : {S : Submodule ℝ V //
      finrank ℝ S = Module.finrank ℝ V - (k : ℕ)} =>
      ⨆ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1))
      = fun S => Real.arctan (⨆ x : {x : V // x ∈ S.1 ∧ x ≠ 0},
          inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) + φ :=
    funext hInner
  have hbddU : BddBelow (Set.range
      fun S : {S : Submodule ℝ V //
        finrank ℝ S = Module.finrank ℝ V - (k : ℕ)} =>
        ⨆ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2) := by
    refine ⟨Finset.univ.inf' hne (hTsym.eigenvalues rfl), ?_⟩
    rintro r ⟨S, rfl⟩
    obtain ⟨x⟩ := hxne S
    exact le_trans (inf'_le_rayleigh hTsym rfl hne x.2.2) (le_ciSup (hbddR S) x)
  rw [hfS, ← ciInf_add_const _ φ (bddBelow_range_arctan _),
    ← arctan_ciInf _ hbddU, ← eigenvalues_eq_iInf_iSup_rayleigh hTsym rfl k, hpe]

/-- The KS angles are decreasing in `k` (φ-free statement): `arctan` is monotone, the
pencil eigenvalues are antitone, and the shift is constant. -/
theorem ksAngle_antitone (g : AllowableComplexMetric V) : Antitone (ksAngle g) := by
  obtain ⟨φ, hφ, hpos⟩ := exists_rotation_posDef g
  intro k l hkl
  rw [ksAngle_eq_arctan_eigenvalue g φ hφ hpos k,
    ksAngle_eq_arctan_eigenvalue g φ hφ hpos l]
  have hmono : pencilEigenvalues g φ hpos rfl l ≤ pencilEigenvalues g φ hpos rfl k := by
    letI : NormedAddCommGroup V :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
    letI : InnerProductSpace ℝ V :=
      InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
    have hTsym : (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
        (nondegenerate_of_posDef (g.rotatedRe φ) hpos)).IsSymmetric :=
      isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ (fun _ _ => rfl)
        (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
        (fun x y => pencilOperator_pairing _ _ _ x y)
    exact hTsym.eigenvalues_antitone rfl hkl
  exact add_le_add (Real.arctan_mono hmono) le_rfl

end KSAngleMain

/-! ### Faithfulness gate for the angle min-max

The abstract `ksAngle` is `Submodule`-indexed through choice-based eigenvalues and
does not reduce. The checks below pin the symbolic chain on the checkpoint-1 concrete
pair `eig = (e^{iπ/3}, e^{-iπ/6})` with rotation `φ = π/12`: the rotated tangents are
`tan(π/4) = 1` and `tan(-π/4) = -1` (compiled checkpoint-1 examples), the sorted
eigenvalue vector of the corresponding diagonal pencil `diag (1, -1)` is `![1, -1]`
(proved below via the eigen-equations, `exists_eigenvalues_eq`, and antitonicity), and
the chain `ksAngle k = arctan(μ_k) + φ` evaluates to `arctan 1 + π/12 = π/3` at
`k = 0` and `arctan (-1) + π/12 = -π/6` at `k = 1` — landing `k = 0` on the LARGER
angle `π/3`, i.e. the sorted order of the two `arg(eig i)` with no index flip. -/

/-- The diagonal operator `(1, -1)` on `EuclideanSpace ℝ (Fin 2)` (the concrete
pencil of the checkpoint-1 pair after rotation by `φ = π/12`). -/
noncomputable def diagOp2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap
    ∘ₗ (LinearMap.pi fun i => (![1, -1] i : ℝ) • LinearMap.proj i)
    ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap

@[simp] theorem diagOp2_apply (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    diagOp2 x i = ![1, -1] i * x i := rfl

/-- The concrete diagonal pencil is symmetric. -/
theorem diagOp2_isSymmetric : diagOp2.IsSymmetric := by
  intro x y
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 2) ℝ),
    real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 2) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_repr, diagOp2_apply]
  ring

/-- `1` is an eigenvalue of the concrete pencil (eigenvector `e₀`). -/
theorem diagOp2_hasEigenvalue_one : Module.End.HasEigenvalue diagOp2 1 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 0 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [diagOp2_apply, EuclideanSpace.single_apply]
  · intro h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp [EuclideanSpace.single_apply] at h0

/-- `-1` is an eigenvalue of the concrete pencil (eigenvector `e₁`). -/
theorem diagOp2_hasEigenvalue_neg_one : Module.End.HasEigenvalue diagOp2 (-1) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 1 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [diagOp2_apply, EuclideanSpace.single_apply]
  · intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp [EuclideanSpace.single_apply] at h1

/-- **The sorted eigenvalue vector of the concrete pencil is `![1, -1]`**: both values
occur among the two eigenvalues (`exists_eigenvalues_eq`), they are distinct, and
Mathlib's enumeration is antitone, so index `0` carries `1` and index `1` carries
`-1` — the sorted decreasing order, no index flip. -/
theorem diagOp2_eigenvalues (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :
    diagOp2_isSymmetric.eigenvalues hn = ![1, -1] := by
  obtain ⟨i1, hi1⟩ :=
    diagOp2_isSymmetric.exists_eigenvalues_eq hn diagOp2_hasEigenvalue_one
  obtain ⟨i2, hi2⟩ :=
    diagOp2_isSymmetric.exists_eigenvalues_eq hn diagOp2_hasEigenvalue_neg_one
  have hne12 : i1 ≠ i2 := by
    intro h
    rw [h, hi2] at hi1
    norm_num at hi1
  have hle : diagOp2_isSymmetric.eigenvalues hn 1
      ≤ diagOp2_isSymmetric.eigenvalues hn 0 :=
    diagOp2_isSymmetric.eigenvalues_antitone hn (by decide : (0 : Fin 2) ≤ 1)
  have hkey : diagOp2_isSymmetric.eigenvalues hn 0 = 1
      ∧ diagOp2_isSymmetric.eigenvalues hn 1 = -1 := by
    fin_cases i1 <;> fin_cases i2
    · exact absurd rfl hne12
    · exact ⟨hi1, hi2⟩
    · have b1 : diagOp2_isSymmetric.eigenvalues hn 1 = 1 := hi1
      have b2 : diagOp2_isSymmetric.eigenvalues hn 0 = -1 := hi2
      constructor <;> linarith
    · exact absurd rfl hne12
  funext j
  fin_cases j
  · exact hkey.1
  · exact hkey.2

/-- Symbolic chain, `k = 0`: `arctan(μ₀) + φ = arctan 1 + π/12 = π/3` — the sup-inf at
`k = 0` lands on the larger angle `π/3`. -/
example : Real.arctan 1 + Real.pi / 12 = Real.pi / 3 := by
  rw [Real.arctan_one]
  ring

/-- Symbolic chain, `k = 1`: `arctan(μ₁) + φ = arctan(-1) + π/12 = -π/6` — the smaller
angle, in sorted order. -/
example : Real.arctan (-1) + Real.pi / 12 = -(Real.pi / 6) := by
  rw [show ((-1 : ℝ)) = -(1 : ℝ) from rfl, Real.arctan_neg, Real.arctan_one]
  ring

-- Codim-1 interlacing (Cauchy; phi-free)

/-! ## Codim-1 interlacing of the KS angles

KS paper Proposition 2.5 (p. 13): for a codimension-one subspace `W ≤ V` the critical
angles of `arg (g|_W)` interleave those of `arg g`: `θ_j ≥ θ'_j ≥ θ_{j+1}`. Here the
restricted angles are `ksAngleOn g W`, the same sup-inf ranged over subspaces of `V`
contained in `W`. The upper bound is pure family inclusion; the lower bound intersects
the span of the top `j+2` eigenvectors of the pencil with `W` (dimension count
`(j+2) + (n−1) − n = j+1`) and extracts a `(j+1)`-dimensional witness inside the
intersection. -/

section Interlacing

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The span of the top `k+1` pencil eigenvectors, with the `rotatedCore` instances
internalized (checkpoint-2b device; realizes `lowSpan` as an instance-free function of
`(g, φ, hpos)`). -/
noncomputable def pencilLowSpan (g : AllowableComplexMetric V) (φ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x)
    (k : Fin (Module.finrank ℝ V)) : Submodule ℝ V :=
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
  lowSpan (isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ)
    (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
      (nondegenerate_of_posDef (g.rotatedRe φ) hpos))
    (fun _ _ => rfl) (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
    (fun x y => pencilOperator_pairing _ _ _ x y)) rfl k

theorem finrank_pencilLowSpan (g : AllowableComplexMetric V) (φ : ℝ)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x)
    (k : Fin (Module.finrank ℝ V)) :
    finrank ℝ (pencilLowSpan g φ hpos k) = (k : ℕ) + 1 := by
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
  have hTsym : (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
      (nondegenerate_of_posDef (g.rotatedRe φ) hpos)).IsSymmetric :=
    isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ (fun _ _ => rfl)
      (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
      (fun a b => pencilOperator_pairing _ _ _ a b)
  exact finrank_lowSpan hTsym rfl k

/-- **STEP 1 (transported witness fact)**: on the span of the top `k+1` pencil
eigenvectors, every nonzero vector has `arg g(x,x) ≥ ksAngle g k`. Transport of
checkpoint 2a's `eigenvalue_le_rayleigh_of_mem_lowSpan` through `arctan` and the
rotation, with `φ` cancelling against `ksAngle_eq_arctan_eigenvalue`. -/
theorem ksAngle_le_arg_of_mem_pencilLowSpan (g : AllowableComplexMetric V) (φ : ℝ)
    (hφ : |φ| < Real.pi / 2)
    (hpos : ∀ x : V, x ≠ 0 → 0 < g.rotatedRe φ x x)
    (k : Fin (Module.finrank ℝ V)) {x : V}
    (hx : x ∈ pencilLowSpan g φ hpos k) (hx0 : x ≠ 0) :
    ksAngle g k ≤ Complex.arg (g.toForm x x) := by
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ (g.rotatedCore φ hpos)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore (g.rotatedCore φ hpos).toCore
  have hTsym : (pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
      (nondegenerate_of_posDef (g.rotatedRe φ) hpos)).IsSymmetric :=
    isSymmetric_of_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ (fun _ _ => rfl)
      (g.rotatedRe_symm φ) (g.rotatedIm_symm φ)
      (fun a b => pencilOperator_pairing _ _ _ a b)
  set T := pencilOperator (g.rotatedRe φ) (g.rotatedIm φ)
    (nondegenerate_of_posDef (g.rotatedRe φ) hpos) with hTdef
  have h1 : hTsym.eigenvalues rfl k ≤ inner ℝ (T x) x / ‖x‖ ^ 2 :=
    eigenvalue_le_rayleigh_of_mem_lowSpan hTsym rfl k hx hx0
  have hray : inner ℝ (T x) x / ‖x‖ ^ 2
      = g.rotatedIm φ x x / g.rotatedRe φ x x := by
    have hA : inner ℝ (T x) x = g.rotatedIm φ x x :=
      pencilOperator_pairing (g.rotatedRe φ) (g.rotatedIm φ) _ x x
    have hB : ‖x‖ ^ 2 = g.rotatedRe φ x x := by
      rw [← real_inner_self_eq_norm_sq]
      rfl
    rw [hA, hB]
  have h2 : Real.arctan (hTsym.eigenvalues rfl k)
      ≤ Complex.arg (g.toForm x x) - φ := by
    have h3 := Real.arctan_mono h1
    rwa [hray, arctan_pencil_rayleigh_eq_arg_sub g φ hφ hpos hx0] at h3
  rw [ksAngle_eq_arctan_eigenvalue g φ hφ hpos k]
  have hpe : pencilEigenvalues g φ hpos rfl = hTsym.eigenvalues rfl := rfl
  rw [hpe]
  linarith

/-- **STEP 0(a) build**: inside any submodule `U` there is a submodule of any smaller
dimension, obtained by spanning the first `m` vectors of a basis of `U` pushed into
`V`. -/
theorem exists_finrank_eq_of_le {U : Submodule ℝ V} {m : ℕ}
    (hm : m ≤ finrank ℝ U) :
    ∃ A : Submodule ℝ V, A ≤ U ∧ finrank ℝ A = m := by
  classical
  have hli : LinearIndependent ℝ
      (fun i : Fin m => ((Module.finBasis ℝ ↥U (Fin.castLE hm i) : ↥U) : V)) :=
    ((Module.finBasis ℝ ↥U).linearIndependent.comp _
      (Fin.castLE_injective hm)).map' U.subtype (Submodule.ker_subtype U)
  refine ⟨Submodule.span ℝ (Set.range fun i : Fin m =>
    ((Module.finBasis ℝ ↥U (Fin.castLE hm i) : ↥U) : V)), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact (Module.finBasis ℝ ↥U (Fin.castLE hm i)).2
  · rw [finrank_span_eq_card hli, Fintype.card_fin]

omit [FiniteDimensional ℝ V] in
/-- A positive-dimensional submodule yields a nonempty nonzero-vector subtype (stated
over the bare module, with no inner-product instances). -/
theorem nonempty_subtype_mem_ne_zero {S : Submodule ℝ V} (h : 0 < finrank ℝ S) :
    Nonempty {x : V // x ∈ S ∧ x ≠ 0} := by
  have hbot : S ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h
    exact lt_irrefl 0 h
  obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hbot
  exact ⟨⟨x, hxS, hx0⟩⟩

/-- Argument families are bounded below by `-π`. -/
theorem bddBelow_range_arg {ι : Sort*} (f : ι → ℂ) :
    BddBelow (Set.range fun i => Complex.arg (f i)) := by
  refine ⟨-Real.pi, ?_⟩
  rintro r ⟨i, rfl⟩
  exact (Complex.neg_pi_lt_arg _).le

/-- Families of infima of argument families are bounded above by `π`. -/
theorem bddAbove_range_iInf_arg {ι : Sort*} (g : AllowableComplexMetric V)
    (F : ι → Submodule ℝ V)
    (hne : ∀ i, Nonempty {x : V // x ∈ F i ∧ x ≠ 0}) :
    BddAbove (Set.range fun i =>
      ⨅ x : {x : V // x ∈ F i ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1)) := by
  refine ⟨Real.pi, ?_⟩
  rintro r ⟨i, rfl⟩
  haveI := hne i
  obtain ⟨x⟩ := hne i
  exact le_trans (ciInf_le (bddBelow_range_arg _) x) (Complex.arg_le_pi _)

/-- **STEP 2: the restricted KS angles** (KS paper Proposition 2.5): the same sup-inf
of `arg g(x,x)`, ranged over subspaces of `V` contained in `W` (kept inside `V`, so
dimension counts and intersections avoid coercions to `↥W`). -/
noncomputable def ksAngleOn (g : AllowableComplexMetric V) (W : Submodule ℝ V)
    (k : Fin (Module.finrank ℝ ↥W)) : ℝ :=
  ⨆ S : {S : Submodule ℝ V // S ≤ W ∧ finrank ℝ S = (k : ℕ) + 1},
    ⨅ x : {x : V // x ∈ S.1 ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1)

/-- **STEP 3 (upper bound, family inclusion)**: `ksAngleOn g W j ≤ ksAngle g j` (the
index `j` viewed in `Fin n` via `finrank ↥W ≤ n`). Every subspace of the restricted
family belongs to the ambient family with the identical inner infimum. -/
theorem ksAngleOn_le_ksAngle (g : AllowableComplexMetric V) (W : Submodule ℝ V)
    (j : Fin (Module.finrank ℝ ↥W)) :
    ksAngleOn g W j ≤ ksAngle g (Fin.castLE (Submodule.finrank_le W) j) := by
  classical
  obtain ⟨A0, hA0le, hA0dim⟩ := exists_finrank_eq_of_le (U := W)
    (Nat.succ_le_of_lt j.isLt)
  haveI : Nonempty {S : Submodule ℝ V // S ≤ W ∧ finrank ℝ S = (j : ℕ) + 1} :=
    ⟨⟨A0, hA0le, hA0dim⟩⟩
  refine ciSup_le fun S => ?_
  refine le_ciSup_of_le
    (bddAbove_range_iInf_arg g (fun S' : {S' : Submodule ℝ V //
        finrank ℝ S' = ((Fin.castLE (Submodule.finrank_le W) j : ℕ)) + 1} => S'.1)
      (fun S' => nonempty_subtype_mem_ne_zero (by rw [S'.2]; omega)))
    ⟨S.1, S.2.2⟩ le_rfl

/-- **STEP 4 (lower bound, constructive)**: `ksAngle g (j+1) ≤ ksAngleOn g W j` for
codimension-one `W`. The span `U` of the top `j+2` pencil eigenvectors meets `W` in
dimension `≥ (j+2) + (n−1) − n = j+1`; a `(j+1)`-dimensional `A ≤ U ⊓ W` is a member
of the restricted family on which `arg g ≥ ksAngle g (j+1)` pointwise (STEP 1). -/
theorem ksAngle_le_ksAngleOn (g : AllowableComplexMetric V) (W : Submodule ℝ V)
    (hcodim : finrank ℝ ↥W + 1 = Module.finrank ℝ V)
    (j : Fin (Module.finrank ℝ ↥W)) :
    ksAngle g ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ ≤ ksAngleOn g W j := by
  classical
  obtain ⟨φ, hφ, hpos⟩ := exists_rotation_posDef g
  set jV1 : Fin (Module.finrank ℝ V) := ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
    with hjV1
  set U := pencilLowSpan g φ hpos jV1 with hU
  have hUdim : finrank ℝ ↥U = (j : ℕ) + 2 := by
    rw [hU, finrank_pencilLowSpan g φ hpos jV1]
  have hinf : (j : ℕ) + 1 ≤ finrank ℝ ↥(U ⊓ W) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
    have h2 : finrank ℝ ↥(U ⊔ W) ≤ finrank ℝ V := Submodule.finrank_le _
    omega
  obtain ⟨A, hAle, hAdim⟩ := exists_finrank_eq_of_le (U := U ⊓ W) hinf
  have hAW : A ≤ W := le_trans hAle inf_le_right
  have hAU : A ≤ U := le_trans hAle inf_le_left
  haveI hAne : Nonempty {x : V // x ∈ A ∧ x ≠ 0} :=
    nonempty_subtype_mem_ne_zero (by rw [hAdim]; omega)
  have hAinf : ksAngle g jV1
      ≤ ⨅ x : {x : V // x ∈ A ∧ x ≠ 0}, Complex.arg (g.toForm x.1 x.1) :=
    le_ciInf fun x =>
      ksAngle_le_arg_of_mem_pencilLowSpan g φ hφ hpos jV1 (hAU x.2.1) x.2.2
  refine le_trans hAinf (le_ciSup
    (bddAbove_range_iInf_arg g (fun S : {S : Submodule ℝ V //
        S ≤ W ∧ finrank ℝ S = (j : ℕ) + 1} => S.1)
      (fun S => nonempty_subtype_mem_ne_zero (by rw [S.2.2]; omega)))
    ⟨A, hAW, hAdim⟩)

/-- **Codim-1 interlacing of the KS angles** (KS paper Proposition 2.5, p. 13):
`θ_{j+1} ≤ θ'_j ≤ θ_j`, i.e. the restricted angles interleave the ambient ones,
`θ_j ≥ θ'_j ≥ θ_{j+1}`. -/
theorem ksAngle_interlace (g : AllowableComplexMetric V) (W : Submodule ℝ V)
    (hcodim : finrank ℝ ↥W + 1 = Module.finrank ℝ V)
    (j : Fin (Module.finrank ℝ ↥W)) :
    ksAngle g ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ ≤ ksAngleOn g W j ∧
      ksAngleOn g W j ≤ ksAngle g (Fin.castLE (Submodule.finrank_le W) j) :=
  ⟨ksAngle_le_ksAngleOn g W hcodim j, ksAngleOn_le_ksAngle g W j⟩

end Interlacing

/-! ### Faithfulness gate for the interlacing

`ksAngleOn` is `Submodule`-indexed through choice-based data and does not reduce; per
the standing discipline the two checks are: (1) the compiled index/direction
arithmetic of the witness construction (the off-by-one guard), and (2) a compiled
SEMANTIC PROXY: eigenvalue interlacing of the concrete pencil `diag(3,1,−2)` against
its top-left `2×2` compression `diag(3,1)`. The proxy exhibits the
phenomenon+direction+index (`μ_k ≥ μ'_k ≥ μ_{k+1}`), which is equivalent to the angle
interlacing under the monotone `arctan + φ` transport proven in checkpoint 2b; it is
NOT a reduction of `ksAngleOn` itself, which cannot reduce. -/

/-- Index/direction arithmetic (off-by-one guard): the lower-bound dimension count
`(j+2) + (n−1) − n = j+1` over the valid range. -/
example (n j : ℕ) (h : j + 1 < n) : (j + 2) + (n - 1) - n = j + 1 := by omega

/-- Index pins: in `ksAngle_interlace` the `≥`-side index (`Fin.castLE`) has value `j`
(the paper's `θ_j`) and the `≤`-side index has value `j+1` (the paper's `θ_{j+1}`):
`θ_j ≥ θ'_j ≥ θ_{j+1}`. -/
example {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (hcodim : Module.finrank ℝ ↥W + 1 = Module.finrank ℝ V)
    (j : Fin (Module.finrank ℝ ↥W)) :
    ((Fin.castLE (Submodule.finrank_le W) j : Fin (Module.finrank ℝ V)) : ℕ) = (j : ℕ)
      ∧ ((⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ : Fin (Module.finrank ℝ V)) : ℕ)
          = (j : ℕ) + 1 :=
  ⟨rfl, rfl⟩

/-- The top-left `2×2` compression `diag(3, 1)` of the concrete pencil
`diag(3, 1, −2)`. -/
noncomputable def diagTL2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap
    ∘ₗ (LinearMap.pi fun i => (![3, 1] i : ℝ) • LinearMap.proj i)
    ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap

@[simp] theorem diagTL2_apply (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    diagTL2 x i = ![3, 1] i * x i := rfl

/-- The compression is symmetric. -/
theorem diagTL2_isSymmetric : diagTL2.IsSymmetric := by
  intro x y
  rw [real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 2) ℝ),
    real_inner_eq_sum_repr (EuclideanSpace.basisFun (Fin 2) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_repr, diagTL2_apply]
  ring

/-- `3` is an eigenvalue of the compression (eigenvector `e₀`). -/
theorem diagTL2_hasEigenvalue_three : Module.End.HasEigenvalue diagTL2 3 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 0 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [diagTL2_apply, EuclideanSpace.single_apply]
  · intro h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp [EuclideanSpace.single_apply] at h0

/-- `1` is an eigenvalue of the compression (eigenvector `e₁`). -/
theorem diagTL2_hasEigenvalue_one : Module.End.HasEigenvalue diagTL2 1 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 1 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [diagTL2_apply, EuclideanSpace.single_apply]
  · intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp [EuclideanSpace.single_apply] at h1

/-- The sorted eigenvalue vector of the compression is `![3, 1]`. -/
theorem diagTL2_eigenvalues (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :
    diagTL2_isSymmetric.eigenvalues hn = ![3, 1] := by
  obtain ⟨i1, hi1⟩ :=
    diagTL2_isSymmetric.exists_eigenvalues_eq hn diagTL2_hasEigenvalue_three
  obtain ⟨i2, hi2⟩ :=
    diagTL2_isSymmetric.exists_eigenvalues_eq hn diagTL2_hasEigenvalue_one
  have hne12 : i1 ≠ i2 := by
    intro h
    rw [h, hi2] at hi1
    norm_num at hi1
  have hle : diagTL2_isSymmetric.eigenvalues hn 1
      ≤ diagTL2_isSymmetric.eigenvalues hn 0 :=
    diagTL2_isSymmetric.eigenvalues_antitone hn (by decide : (0 : Fin 2) ≤ 1)
  have hkey : diagTL2_isSymmetric.eigenvalues hn 0 = 3
      ∧ diagTL2_isSymmetric.eigenvalues hn 1 = 1 := by
    fin_cases i1 <;> fin_cases i2
    · exact absurd rfl hne12
    · exact ⟨hi1, hi2⟩
    · have b1 : diagTL2_isSymmetric.eigenvalues hn 1 = 3 := hi1
      have b2 : diagTL2_isSymmetric.eigenvalues hn 0 = 1 := hi2
      constructor <;> linarith
    · exact absurd rfl hne12
  funext j
  fin_cases j
  · exact hkey.1
  · exact hkey.2

/-- `3` is an eigenvalue of `diag(3,1,−2)` (eigenvector `e₀`). -/
theorem diagOp3_hasEigenvalue_three : Module.End.HasEigenvalue diagOp3 3 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 0 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [diagOp3_apply, EuclideanSpace.single_apply]
  · intro h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp [EuclideanSpace.single_apply] at h0

/-- `1` is an eigenvalue of `diag(3,1,−2)` (eigenvector `e₁`). -/
theorem diagOp3_hasEigenvalue_one : Module.End.HasEigenvalue diagOp3 1 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 1 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [diagOp3_apply, EuclideanSpace.single_apply]
  · intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
    simp [EuclideanSpace.single_apply] at h1

/-- `−2` is an eigenvalue of `diag(3,1,−2)` (eigenvector `e₂`). -/
theorem diagOp3_hasEigenvalue_neg_two : Module.End.HasEigenvalue diagOp3 (-2) := by
  have hc2 : (![(3 : ℝ), 1, -2]) 2 = -2 := rfl
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := EuclideanSpace.single 2 1) ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [diagOp3_apply, EuclideanSpace.single_apply, Fin.ext_iff, hc2]
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
    simp [EuclideanSpace.single_apply] at h2

/-- Every eigenvalue of `diag(3,1,−2)` is one of `3, 1, −2` (coordinate extraction on
an eigenvector). -/
theorem diagOp3_eigenvalue_mem {μ : ℝ} (h : Module.End.HasEigenvalue diagOp3 μ) :
    μ = 3 ∨ μ = 1 ∨ μ = -2 := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have heq : diagOp3 v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hv.2 (by ext i; exact hall i)
  obtain ⟨i, hi⟩ := hex
  have hcoord := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w i) heq
  simp only [diagOp3_apply, PiLp.smul_apply, smul_eq_mul] at hcoord
  have hμ : μ = ![3, 1, -2] i := mul_right_cancel₀ hi hcoord.symm
  fin_cases i
  · exact Or.inl (by simpa using hμ)
  · exact Or.inr (Or.inl (by simpa using hμ))
  · exact Or.inr (Or.inr (by rw [hμ]; rfl))

/-- The sorted eigenvalue vector of `diag(3,1,−2)` is `![3, 1, −2]`. -/
theorem diagOp3_eigenvalues (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :
    diagOp3_isSymmetric.eigenvalues hn = ![3, 1, -2] := by
  obtain ⟨i3, hi3⟩ :=
    diagOp3_isSymmetric.exists_eigenvalues_eq hn diagOp3_hasEigenvalue_three
  obtain ⟨i1, hi1⟩ :=
    diagOp3_isSymmetric.exists_eigenvalues_eq hn diagOp3_hasEigenvalue_one
  obtain ⟨i2, hi2⟩ :=
    diagOp3_isSymmetric.exists_eigenvalues_eq hn diagOp3_hasEigenvalue_neg_two
  have hanti := diagOp3_isSymmetric.eigenvalues_antitone hn
  have hmem : ∀ j, diagOp3_isSymmetric.eigenvalues hn j = 3
      ∨ diagOp3_isSymmetric.eigenvalues hn j = 1
      ∨ diagOp3_isSymmetric.eigenvalues hn j = -2 := fun j =>
    diagOp3_eigenvalue_mem (diagOp3_isSymmetric.hasEigenvalue_eigenvalues hn j)
  have h0 : diagOp3_isSymmetric.eigenvalues hn 0 = 3 := by
    have hge : (3 : ℝ) ≤ diagOp3_isSymmetric.eigenvalues hn 0 :=
      hi3 ▸ hanti (Fin.zero_le i3)
    rcases hmem 0 with h | h | h
    · exact h
    · linarith
    · linarith
  have h2 : diagOp3_isSymmetric.eigenvalues hn 2 = -2 := by
    have hle : diagOp3_isSymmetric.eigenvalues hn 2 ≤ -2 :=
      hi2 ▸ hanti (Fin.le_last i2)
    rcases hmem 2 with h | h | h
    · linarith
    · linarith
    · exact h
  have h1 : diagOp3_isSymmetric.eigenvalues hn 1 = 1 := by
    have hne0 : i1 ≠ 0 := by
      intro h
      rw [h, h0] at hi1
      norm_num at hi1
    have hne2 : i1 ≠ 2 := by
      intro h
      rw [h, h2] at hi1
      norm_num at hi1
    have hi1eq : i1 = 1 := by
      have hv := i1.isLt
      have hv0 : (i1 : ℕ) ≠ 0 := fun hh => hne0 (Fin.ext (by simpa using hh))
      have hv2 : (i1 : ℕ) ≠ 2 := fun hh => hne2 (Fin.ext (by simpa using hh))
      apply Fin.ext
      simp only [Fin.val_one]
      omega
    rw [← hi1eq]
    exact hi1
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- **SEMANTIC PROXY** for the interlacing: the sorted eigenvalues of the pencil
`diag(3,1,−2)` and of its compression `diag(3,1)` interlace,
`μ_k ≥ μ'_k ≥ μ_{k+1}`: `3 ≥ 3 ≥ 1` and `1 ≥ 1 ≥ −2`. -/
example (hn3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    (hn2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :
    (diagTL2_isSymmetric.eigenvalues hn2 0 ≤ diagOp3_isSymmetric.eigenvalues hn3 0
      ∧ diagOp3_isSymmetric.eigenvalues hn3 1 ≤ diagTL2_isSymmetric.eigenvalues hn2 0)
    ∧ (diagTL2_isSymmetric.eigenvalues hn2 1 ≤ diagOp3_isSymmetric.eigenvalues hn3 1
      ∧ diagOp3_isSymmetric.eigenvalues hn3 2
          ≤ diagTL2_isSymmetric.eigenvalues hn2 1) := by
  have hc2 : (![(3 : ℝ), 1, -2]) 2 = -2 := rfl
  rw [diagOp3_eigenvalues hn3, diagTL2_eigenvalues hn2]
  norm_num [hc2]
