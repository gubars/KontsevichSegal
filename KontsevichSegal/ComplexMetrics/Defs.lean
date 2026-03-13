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
  sorry

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
  sorry
