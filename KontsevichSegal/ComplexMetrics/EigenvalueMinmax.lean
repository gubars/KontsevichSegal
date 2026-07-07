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
