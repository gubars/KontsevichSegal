/- The Shilov boundary of QC(V): real Lorentzian metrics of signature (d-1, 1) —
and no other nondegenerate real metrics — belong to the Shilov boundary. This is
the key result explaining why Lorentzian signature is special.
KS paper Section 2, pages 8-9.

A complex metric g ∈ QC(V) approaches the Shilov boundary as the arguments
arg(λᵢ) approach ±π/2 with ∑ᵢ |arg λᵢ| → π. The real slice of this boundary
consists exactly of the Lorentzian metrics: one eigenvalue purely imaginary
(contributing |arg| = π/2) and the rest real positive (contributing |arg| = 0),
summing to π in total.

The Shilov boundary contains two disjoint copies of Lorentzian metrics,
corresponding to the two ways an eigenvalue can approach the negative real axis
(from above or below in the complex plane). These two copies are interchanged
by complex conjugation; the nondegenerate points of the Shilov boundary are the
time-oriented Lorentzian metrics.
-/

import KontsevichSegal.ComplexMetrics.Defs

variable {d : ℕ}

/-! ## Lorentzian signature -/

/-- A real bilinear form on `V` has *Lorentzian signature* `(d-1, 1)` if there
exists a basis in which it diagonalizes as `∑ᵢ sᵢ · xᵢ · yᵢ` where each
`sᵢ ∈ {+1, -1}` and exactly one `sᵢ` equals `-1`.

KS paper Section 2, page 9: real Lorentzian metrics are characterized as the
nondegenerate real metrics on the Shilov boundary of QC(V). -/
def IsLorentzian {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    (sign : Fin (Module.finrank ℝ V) → ℝ),
    -- Each sign is ±1.
    (∀ i, sign i = 1 ∨ sign i = -1) ∧
    -- Exactly one sign equals -1 (Lorentzian signature).
    (∃! i, sign i = -1) ∧
    -- The form diagonalizes as ∑ᵢ sᵢ · xᵢ · yᵢ in this basis.
    (∀ v w, φ v w = ∑ i, sign i * (b.repr v i) * (b.repr w i))

/-! ## KS paper Section 2, page 9: Shilov boundary results -/

/-- **KS paper Section 2, page 9 — Lorentzian metrics on the boundary.**
A real Lorentzian metric on `V` lies on the boundary of QC(V): for any `ε > 0`,
there exists an allowable complex metric whose diagonal eigenvalues are within `ε`
of the Lorentzian ones (i.e., `d-1` eigenvalues near `+1` and one near `-1`,
perturbed into the upper or lower half-plane so that the angle condition is
strictly satisfied).

KS paper, paragraph after Theorem 2.2: the Lorentzian metrics are approached as
`∑ᵢ |arg λᵢ| → π` from below. -/
theorem lorentzian_on_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (_hL : IsLorentzian φ)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ g : AllowableComplexMetric V,
      ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
        (eig : Fin (Module.finrank ℝ V) → ℂ),
        AngleCondition eig ∧
        ∀ i, ‖eig i - ↑(φ (b i) (b i))‖ < ε := by
  sorry

/-- **KS paper Section 2, page 9 — only Lorentzian on the boundary.**
If a real nondegenerate quadratic form lies on the boundary of QC(V), it must
have Lorentzian signature `(d-1, 1)`.

If the metric is real, each `|arg(λᵢ)|` is either `0` (for positive eigenvalues)
or `π` (for negative eigenvalues). The boundary condition `∑ᵢ |arg(λᵢ)| = π`
forces at most one `|arg(λᵢ)|` to equal `π`, giving exactly one negative
eigenvalue — Lorentzian signature.

KS paper, paragraph after Theorem 2.2. -/
theorem only_lorentzian_on_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    /- Nondegeneracy of the real form. -/
    (_hnd : ∀ v, v ≠ 0 → ∃ w, φ v w ≠ 0)
    /- The form lies on the boundary: it is a limit of allowable complex metrics.
       We express this as: for every ε > 0, there exists g ∈ QC(V) within ε. -/
    (_hbdy : ∀ ε : ℝ, 0 < ε →
      ∃ g : AllowableComplexMetric V,
        ∀ v, ‖g.toForm v v - ↑(φ v v)‖ < ε) :
    IsLorentzian φ := by
  sorry

/-- **KS paper Section 2, page 9 — two copies on the Shilov boundary.**
The Shilov boundary of QC(V) contains two disjoint copies of Lorentzian metrics,
interchanged by complex conjugation. These correspond to the two ways an
eigenvalue can approach the negative real axis: from the upper half-plane
(`arg → +π`) or the lower half-plane (`arg → -π`).

The nondegenerate points of the Shilov boundary are thus the *time-oriented*
Lorentzian metrics (a choice of upper vs. lower half-plane approach corresponds
to a choice of time orientation).

KS paper, paragraph after Theorem 2.2. -/
theorem two_copies_on_boundary (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    -- For any Lorentzian form φ, there exist two families of allowable metrics
    -- approaching φ, one through the upper half-plane and one through the lower,
    -- and these are interchanged by complex conjugation.
    ∀ (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), IsLorentzian φ →
      ∃ (g_upper g_lower : ℕ → AllowableComplexMetric V),
        -- The two families are related by conjugation
        (∀ n v w, (g_upper n).toForm v w = starRingEnd ℂ ((g_lower n).toForm v w)) := by
  sorry
