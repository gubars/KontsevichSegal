/- The Shilov boundary of QC(V): real Lorentzian metrics of signature (d-1, 1) —
and no other nondegenerate real metrics — belong to the Shilov boundary. This is
the key result explaining why Lorentzian signature is special.
KS paper Section 2, pages 8-9.

A real metric has each |arg(λᵢ)| equal to 0 (positive eigenvalue) or π (negative
eigenvalue), so the angle condition ∑ᵢ |arg λᵢ| < π fails for every real metric
that is not positive-definite. A real Lorentzian metric — exactly one negative
eigenvalue — sits exactly at the threshold ∑ᵢ |arg λᵢ| = π: it is the limit of
allowable metrics in which the negative eigenvalue is perturbed off the negative
real axis (|arg| = π - δ) while the positive eigenvalues stay real positive.
Real metrics with two or more negative eigenvalues would need ∑ᵢ |arg λᵢ| ≥ 2π in
the limit and so are not even in the closure of QC(V).

The Shilov boundary contains two disjoint copies of Lorentzian metrics,
corresponding to the two ways the negative eigenvalue can approach the negative
real axis (from the upper or lower half-plane). These two copies are interchanged
by complex conjugation; the nondegenerate points of the Shilov boundary are the
time-oriented Lorentzian metrics. (Distinguishing the two copies as boundary
*points* requires the bounded affine-variety realization of QC(V) from the proof
of Prop 2.7 — the branch of √det(g) differs in the two limits — which is beyond
the current formalization; see `two_copies_on_boundary` below.)
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
A real Lorentzian metric `φ` on `V` lies on the boundary of QC(V):

1. φ is a *limit of allowable metrics*: there is a basis `b` such that for
   every `ε > 0` some allowable complex metric is entry-wise within `ε` of φ
   on `b`. (Closeness of the entries on a fixed basis is the canonical topology
   on the finite-dimensional space of forms.)
2. φ is *not itself allowable*: no allowable metric has the same quadratic
   form as φ.

Proof sketch: diagonalize φ as `∑ sᵢ yᵢ²` with exactly one `sᵢ = -1`, and
perturb the negative eigenvalue to `exp(i(π - δ))`, giving angle sum `π - δ < π`.
For (2), φ takes a real negative value on the timelike basis vector, which an
allowable metric cannot (`not_neg_real_axis`).

KS paper, paragraph after Theorem 2.2: the Lorentzian metrics are approached as
`∑ᵢ |arg λᵢ| → π` from below. -/
theorem lorentzian_on_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hL : IsLorentzian φ) :
    (∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ ε : ℝ, 0 < ε →
        ∃ g : AllowableComplexMetric V,
          ∀ i j, ‖g.toForm (b i) (b j) - ↑(φ (b i) (b j))‖ < ε) ∧
    (∀ g : AllowableComplexMetric V, ∃ v, g.toForm v v ≠ ↑(φ v v)) := by
  sorry

/-- **KS paper Section 2, page 9 — only Lorentzian on the boundary.**
If a real nondegenerate bilinear form lies on the boundary of QC(V) — it is a
limit of allowable complex metrics (entry-wise on a fixed basis `b`) but is not
positive-definite (the positive-definite forms are the *interior* real points
of QC(V), not boundary points) — then it has Lorentzian signature `(d-1, 1)`.

If the metric is real, each `|arg(λᵢ)|` is either `0` (positive eigenvalue)
or `π` (negative eigenvalue). For a limit of allowable metrics, at most one
`|arg(λᵢ)|` can reach `π` (a 2-dimensional negative-definite subspace would
force `∑ᵢ |arg(λᵢ)| → 2π`, contradicting the angle condition under restriction).
Nondegeneracy plus failure of positive-definiteness then force exactly one
negative eigenvalue — Lorentzian signature.

KS paper, paragraph after Theorem 2.2. -/
theorem only_lorentzian_on_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    /- Nondegeneracy of the real form. -/
    (hnd : ∀ v, v ≠ 0 → ∃ w, φ v w ≠ 0)
    /- The form is a limit of allowable complex metrics, entry-wise on `b`. -/
    (hbdy : ∀ ε : ℝ, 0 < ε →
      ∃ g : AllowableComplexMetric V,
        ∀ i j, ‖g.toForm (b i) (b j) - ↑(φ (b i) (b j))‖ < ε)
    /- The form is not positive-definite (otherwise it lies in the interior of
       QC(V), not on the boundary). -/
    (hnotpos : ¬ ∀ v, v ≠ 0 → 0 < φ v v) :
    IsLorentzian φ := by
  sorry

/-- **KS paper Section 2, page 9 — two copies on the Shilov boundary.**
PLACEHOLDER (`True` conclusion). The paper's actual claim, quoted:

"In fact the Shilov boundary of Q_C(V) contains *two* disjoint copies of the
space of Lorentzian metrics on V, for an eigenvalue λ can approach the
negative real axis either from above or from below. The two copies are
interchanged by the complex-conjugation map on Q_C(V). Because of our choice
to make the orientation-reversing elements of GL(V) act antilinearly on the
orientation-line of V, we can say that the nondegenerate points of the Shilov
boundary are the *time-oriented* Lorentzian metrics."

The subject of the claim is the **Shilov boundary** of QC(V) "regarded as a
bounded domain in an affine variety (cf. the proof of 2.7)". This cannot be
faithfully expressed with current infrastructure. Precisely missing:

1. **Induced forms on exterior powers / Hodge star `∗_g`** (same Mathlib gap
   blocking `Equivalence.lean`): needed for the embedding of QC(V) into the
   product `∏_{0 ≤ p ≤ d/2} U(⋀ᵖ V)` of Siegel domains from the proof of
   Prop 2.7. The p = 0 factor is `vol_g = (det g)^(1/2)`, whose branch is
   what separates the two copies — in the naive closure of QC(V) inside
   S²(V*_ℂ) the two copies coincide, so no statement about subsets of the
   space of forms can express the disjointness.
2. **Siegel domain theory and the Cayley transform** ("unit disc"
   realization): needed to regard the image as a *bounded* domain, without
   which sup-norm characterizations degenerate.
3. **The Shilov boundary itself**: the smallest compact subset of the closure
   on which every holomorphic function defined near the closure attains its
   sup ([Hör] p. 67). Statable from Mathlib's holomorphy + topology once
   (1)–(2) exist, but meaningless before.

(A partial double-cover formulation — the closure of the graph
`{(g, √det g) : g ∈ QC(V)}` having exactly two conjugate-swapped points over
each Lorentzian metric — *is* expressible today, but its subject is not the
Shilov boundary, so per the project's no-approximations policy it is not used
as a stand-in.)

KS paper, paragraph after Theorem 2.2. -/
theorem two_copies_on_boundary (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    -- PLACEHOLDER: True stands for the Shilov-boundary claim quoted in the
    -- docstring, which cannot yet be expressed (see items 1-3 above).
    True := by
  trivial
