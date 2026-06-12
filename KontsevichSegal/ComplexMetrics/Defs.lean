/- Working definition of allowable complex metrics using the angle condition
(Theorem 2.2 of the KS paper). This is equivalent to Definition 2.1 but avoids
the Hodge star operator.

This file develops the definition of allowable complex metrics on a finite-dimensional
real vector space `V`, following Section 2 of:

  Kontsevich, M. and Segal, G., "Wick rotation and the positivity of energy in
  quantum field theory", arXiv:2105.10161 [hep-th], 2021.

**Working definition.** We use the diagonal characterization from Theorem 2.2 of
[KS] as our primary definition: a complex quadratic form `g` on a `d`-dimensional
real vector space `V` is *allowable* if and only if there exists a basis in which

  g = ∑ᵢ λᵢ yᵢ²,

where each `λᵢ ∈ ℂ` is nonzero, not on the negative real axis, and
`∑ᵢ |arg λᵢ| < π`.

**Deferred.** Equivalence with Definition 2.1 of [KS] (which asserts positivity of
the induced form on all exterior powers via the Hodge star) is not formalized here,
as the necessary Hodge star machinery is not yet available in Mathlib.
-/

import KontsevichSegal.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Analysis.Complex.Trigonometric

variable {d : ℕ}

/-! ## Angle condition -/

/-- The angle condition from Theorem 2.2 of [KS] on a tuple of complex diagonal
coefficients `eig : Fin d → ℂ`. The three conditions are:
- every `eig i` is nonzero,
- no `eig i` lies on the non-positive real axis
  (equivalently: `(eig i).re > 0` or `(eig i).im ≠ 0`),
- the sum of absolute arguments satisfies `∑ i, |Complex.arg (eig i)| < π`.

Note: `λ` is a Lean keyword; we use `eig` for the eigenvalue tuple throughout. -/
structure AngleCondition (eig : Fin d → ℂ) : Prop where
  /-- Every diagonal coefficient is nonzero. -/
  nonzero         : ∀ i, eig i ≠ 0
  /-- No diagonal coefficient lies on the non-positive real axis. -/
  not_nonpos_real : ∀ i, 0 < (eig i).re ∨ (eig i).im ≠ 0
  /-- The sum of absolute arguments is strictly less than π. -/
  sum_arg_lt_pi   : ∑ i, |Complex.arg (eig i)| < Real.pi

/-! ## Allowable complex metrics -/

/-- An *allowable complex metric* on a finite-dimensional real vector space `V`
(Theorem 2.2 of [KS]) is an ℝ-bilinear symmetric nondegenerate complex-valued
form that admits a diagonalization whose diagonal coefficients satisfy the angle
condition `AngleCondition`.

This is used as the working definition in place of Definition 2.1 of [KS];
see the module docstring for why. -/
structure AllowableComplexMetric (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] where
  /-- The underlying ℝ-bilinear map `V × V → ℂ`. -/
  toForm : V →ₗ[ℝ] V →ₗ[ℝ] ℂ
  /-- Symmetry: `g(v, w) = g(w, v)`. -/
  symmetric' : ∀ v w, toForm v w = toForm w v
  /-- Nondegeneracy: every nonzero vector is detected by some pairing. -/
  nondegenerate : ∀ v, v ≠ 0 → ∃ w, toForm v w ≠ 0
  /-- Diagonal characterization (Theorem 2.2 of [KS]): there exists a basis `b`
  and coefficients `eig` satisfying `AngleCondition` such that
  `g(v, v) = ∑ i, eig i * (b.repr v i)²` for all `v`. -/
  angle_cond    : ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
      (eig : Fin (Module.finrank ℝ V) → ℂ),
      AngleCondition eig ∧
      ∀ v, toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2

/-! ## The domain QC(V) -/

/-- `QC V` is the type of all allowable complex metrics on `V`.
It is the complex analogue of the space of Riemannian metrics: a contractible
domain in the space of complex quadratic forms on `V` whose Shilov boundary
consists precisely of the Lorentzian metrics (Section 2, [KS]). -/
def QC (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :=
  AllowableComplexMetric V

/-! ## Consequences of the angle condition -/

/-- For an allowable complex metric, the quadratic form `g(v, v)` is never real
and negative for a nonzero vector `v`.

This is stated on page 9 of [KS] as a direct consequence of the angle condition:
since `|arg(∑ λᵢ yᵢ²)| ≤ ∑ |arg λᵢ| < π`, the value cannot reach the negative
real axis. -/
lemma not_neg_real_axis {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (g : AllowableComplexMetric V)
    (v : V) (hv : v ≠ 0) :
    ¬ ((g.toForm v v).im = 0 ∧ (g.toForm v v).re < 0) := by
  rintro ⟨him, hre⟩
  obtain ⟨b, eig, hAC, hdiag⟩ := g.angle_cond
  -- `v` has a nonzero coordinate in the diagonalizing basis.
  have hrepr : b.repr v ≠ 0 := fun h => hv (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hrepr
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hi₀
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
  have hcosφ : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp hφlt).1, (abs_lt.mp hφlt).2⟩
  -- The linear functional z ↦ Re(e^{-iφ} z) is positive on every eigenvalue.
  have hpos : ∀ i, 0 < (eig i).re * Real.cos φ + (eig i).im * Real.sin φ := by
    intro i
    have hzne : eig i ≠ 0 := hAC.nonzero i
    have hnorm : (0 : ℝ) < ‖eig i‖ := norm_pos_iff.mpr hzne
    have hkey : (eig i).re * Real.cos φ + (eig i).im * Real.sin φ
        = ‖eig i‖ * Real.cos (Complex.arg (eig i) - φ) := by
      rw [Real.cos_sub, Complex.cos_arg hzne, Complex.sin_arg]
      field_simp
    have hcos : 0 < Real.cos (Complex.arg (eig i) - φ) :=
      Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp (hargφ i)).1, (abs_lt.mp (hargφ i)).2⟩
    rw [hkey]
    exact mul_pos hnorm hcos
  -- Real and imaginary parts of the diagonal expansion of g(v,v).
  have hzre : (g.toForm v v).re = ∑ i, (eig i).re * (b.repr v i) ^ 2 := by
    rw [hdiag v, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hzim : (g.toForm v v).im = ∑ i, (eig i).im * (b.repr v i) ^ 2 := by
    rw [hdiag v, Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add]
  -- The functional is strictly positive on g(v,v) (nonnegative combination of
  -- the eigenvalues with at least one strictly positive coefficient).
  have hsum : 0 < ∑ i,
      ((eig i).re * Real.cos φ + (eig i).im * Real.sin φ) * (b.repr v i) ^ 2 := by
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hpos i).le (sq_nonneg _))
      ⟨i₀, Finset.mem_univ _, ?_⟩
    have h2 : 0 < (b.repr v i₀ : ℝ) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi₀))
    exact mul_pos (hpos i₀) h2
  have heq : ∑ i,
      ((eig i).re * Real.cos φ + (eig i).im * Real.sin φ) * (b.repr v i) ^ 2
      = (g.toForm v v).re * Real.cos φ + (g.toForm v v).im * Real.sin φ := by
    rw [hzre, hzim, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq, him] at hsum
  simp only [zero_mul, add_zero] at hsum
  -- But on a negative real number the functional is negative: contradiction.
  exact absurd hsum (not_lt.mpr (mul_neg_of_neg_of_pos hre hcosφ).le)

/-- The determinant of the Gram matrix of an allowable complex metric (with
respect to any basis) is not real and negative, and its square root — taken as
the unique `w : ℂ` with `w ^ 2 = det` and `0 < w.re` — has strictly positive
real part.

This is used on page 7 of [KS] to define the holomorphic volume element `√det(g)`.
The branch of the square root is fixed by requiring positive real part, which is
unambiguous since `det(g)` avoids the non-positive real axis. -/
lemma volume_element_positive {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (g : AllowableComplexMetric V)
    (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    let M : Matrix (Fin (Module.finrank ℝ V))
                   (Fin (Module.finrank ℝ V)) ℂ :=
      Matrix.of (fun i j => g.toForm (b i) (b j))
    ¬ (M.det.im = 0 ∧ M.det.re < 0) ∧
    ∃ w : ℂ, w ^ 2 = M.det ∧ 0 < w.re := by
  intro M
  obtain ⟨e, eig, hAC, hdiag⟩ := g.angle_cond
  -- Polarization: in the diagonalizing basis the full bilinear form is diagonal.
  have hbil : ∀ v w, g.toForm v w
      = ∑ i, eig i * (e.repr v i : ℂ) * (e.repr w i : ℂ) := by
    intro v w
    have h1 := hdiag (v + w)
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
      Complex.ofReal_add] at h1
    have hexp : ∑ i, eig i * ((e.repr v i : ℂ) + (e.repr w i : ℂ)) ^ 2
        = (∑ i, eig i * (e.repr v i : ℂ) ^ 2)
          + (∑ i, eig i * (e.repr w i : ℂ) ^ 2)
          + 2 * ∑ i, eig i * (e.repr v i : ℂ) * (e.repr w i : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linear_combination h1 / 2 + hexp / 2 - hdiag v / 2 - hdiag w / 2
      + g.symmetric' v w / 2
  -- Change of basis: the Gram matrix of `b` factors through the diagonal one,
  -- so its determinant is `(det P)² · ∏ eig i` with `P` the real base-change matrix.
  set P : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℂ :=
    Complex.ofRealHom.mapMatrix (e.toMatrix b) with hPdef
  have hM : M = P.transpose * (Matrix.diagonal eig * P) := by
    ext i j
    have hMij : M i j = g.toForm (b i) (b j) := rfl
    rw [hMij, hbil, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.transpose_apply, Matrix.diagonal_mul, hPdef,
      RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
      Complex.ofRealHom_eq_coe]
    ring
  have hdetP : P.det = ((e.toMatrix b).det : ℂ) := by
    rw [hPdef, ← RingHom.map_det, Complex.ofRealHom_eq_coe]
  have hPdetne : (e.toMatrix b).det ≠ 0 := by
    have h1 : e.toMatrix b * b.toMatrix e = 1 := by
      rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
    exact left_ne_zero_of_mul_eq_one
      (by rw [← Matrix.det_mul, h1, Matrix.det_one])
  have hdetM : M.det = (((e.toMatrix b).det ^ 2 : ℝ) : ℂ) * ∏ i, eig i := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_diagonal, hdetP]
    push_cast
    ring
  -- Polar form of the determinant: `det M = r · exp(iS)` with `r > 0` and
  -- `S = ∑ arg(eig i) ∈ (-π, π)` by the angle condition.
  set S : ℝ := ∑ i, Complex.arg (eig i) with hSdef
  have hSlt : |S| < Real.pi :=
    lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) hAC.sum_arg_lt_pi
  obtain ⟨hSlo, hShi⟩ := abs_lt.mp hSlt
  set r : ℝ := (e.toMatrix b).det ^ 2 * ∏ i, ‖eig i‖ with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact mul_pos (sq_pos_of_ne_zero hPdetne)
      (Finset.prod_pos fun i _ => norm_pos_iff.mpr (hAC.nonzero i))
  have hexpsum : ∑ i, (Complex.arg (eig i) : ℂ) * Complex.I
      = (S : ℂ) * Complex.I := by
    rw [hSdef]
    push_cast
    rw [Finset.sum_mul]
  have hpolar : M.det = (r : ℂ) * Complex.exp ((S : ℂ) * Complex.I) := by
    have hprod : ∏ i, eig i
        = ((∏ i, ‖eig i‖ : ℝ) : ℂ) * Complex.exp ((S : ℂ) * Complex.I) := by
      calc ∏ i, eig i
          = ∏ i, ((‖eig i‖ : ℂ)
              * Complex.exp ((Complex.arg (eig i) : ℂ) * Complex.I)) :=
            Finset.prod_congr rfl fun i _ =>
              (Complex.norm_mul_exp_arg_mul_I _).symm
        _ = (∏ i, (‖eig i‖ : ℂ))
              * ∏ i, Complex.exp ((Complex.arg (eig i) : ℂ) * Complex.I) :=
            Finset.prod_mul_distrib
        _ = ((∏ i, ‖eig i‖ : ℝ) : ℂ) * Complex.exp ((S : ℂ) * Complex.I) := by
            rw [← Complex.exp_sum, hexpsum, Complex.ofReal_prod]
    rw [hdetM, hprod, hrdef]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · -- `det M` is not real and negative: `sin S = 0` forces `S = 0` on `(-π, π)`,
    -- and then `det M = r > 0`.
    rintro ⟨him, hre⟩
    rw [hpolar] at him hre
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero, sub_zero] at him hre
    have hsin : Real.sin S = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h hrpos.ne'
      · exact h
    have hS0 : S = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hSlo hShi).mp hsin
    rw [hS0, Real.cos_zero, mul_one] at hre
    exact absurd hre (not_lt.mpr hrpos.le)
  · -- Principal square root: `w = √r · exp(iS/2)` has `|arg w| = |S|/2 < π/2`,
    -- hence positive real part.
    refine ⟨(Real.sqrt r : ℂ) * Complex.exp ((↑(S / 2) : ℂ) * Complex.I), ?_, ?_⟩
    · rw [hpolar, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hrpos.le, pow_two,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        zero_mul, sub_zero]
      refine mul_pos (Real.sqrt_pos.mpr hrpos)
        (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
