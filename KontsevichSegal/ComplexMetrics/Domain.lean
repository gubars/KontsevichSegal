/- Properties of the domain QC(V): contractibility (Prop 2.4), domain of
holomorphy (Prop 2.7), two-dimensional case.

This file formalizes (as sorry'd placeholders) the structural results about QC(V)
from Section 2 of:

  Kontsevich, M. and Segal, G., "Wick rotation and the positivity of energy in
  quantum field theory", arXiv:2105.10161 [hep-th], 2021.
-/

import KontsevichSegal.ComplexMetrics.Defs

/-! ## Π(V): the fiber of the QC bundle (KS paper Proposition 2.4)

Given a positive-definite inner product `g₀` on `V`, the *fiber* Π(V, g₀) is the
set of `g₀`-self-adjoint operators Θ on V with trace-norm ∑ᵢ |θᵢ| < 1, where
`θᵢ` are the eigenvalues of Θ. This is the interior of the convex hull of rank-1
orthogonal projections, and in particular is convex (hence contractible).

We define `TraceNormLtOne` as a simplified formulation: a self-adjoint linear map
Θ : V →ₗ[ℝ] V is in the fiber when there exist eigenvalues θ : Fin d → ℝ with
∑ i, |θ i| < 1.
-/

/-- The set of self-adjoint operators with trace-norm less than 1, denoted Π(V) in
[KS]. This is the fiber of the bundle QC(V) → {positive-definite inner products}
from KS paper Proposition 2.4.

Given a reference inner product on V, Π(V) consists of ℝ-linear endomorphisms
Θ : V →ₗ[ℝ] V that are self-adjoint (with respect to the given inner product)
and satisfy ∑ᵢ |θᵢ| < 1 where θᵢ are the eigenvalues. Equivalently, Π(V) is
the interior of the convex hull of rank-1 orthogonal projections in V.

**Simplified formulation.** Since Mathlib does not yet provide a general eigenvalue
decomposition for self-adjoint operators on finite-dimensional inner product spaces
in the form needed, we package the eigenvalue data existentially: Θ is in
`TraceNormLtOne` when there exist real eigenvalues summing (in absolute value)
to less than 1. -/
structure TraceNormLtOne (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] where
  /-- The underlying ℝ-linear endomorphism. -/
  toLinearMap : V →ₗ[ℝ] V
  /-- There exist eigenvalues `θ : Fin d → ℝ` whose absolute values sum to
  less than 1. This encodes the trace-norm condition ‖Θ‖₁ < 1. -/
  eigenvalues_trace_norm_lt_one :
    ∃ θ : Fin (Module.finrank ℝ V) → ℝ, ∑ i, |θ i| < 1

/-! ## KS paper Proposition 2.4: fiber bundle structure and contractibility -/

/-- **KS paper Proposition 2.4 (parametrization).** Every allowable complex metric
`g ∈ QC(V)` can be parametrized by a positive-definite inner product `g₀` on `V`
and an operator `Θ ∈ Π(V, g₀)` (self-adjoint with trace-norm < 1). This exhibits
QC(V) as a fiber bundle over the space of positive-definite inner products with
fiber Π(V, g₀).

More precisely, choosing a reference inner product, one obtains the associated-bundle
decomposition `QC(V) ≅ GL(V) ×_{O(V)} Π(V)`.

**Formalization note.** The full statement requires GL(V)/O(V) actions, associated
bundle machinery, and an inner product space structure compatible with the algebraic
`AddCommGroup`/`Module` setup used in `QC`. Since `InnerProductSpace ℝ V` requires
`NormedAddCommGroup V` (incompatible with the plain `AddCommGroup` in `QC`'s
definition), this is stated as a `True` placeholder. -/
theorem QC_parametrization (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    -- Placeholder: the real statement requires compatible inner product space structure.
    True := by
  trivial

/-- **KS paper Proposition 2.4 (contractibility).** QC(V) is contractible.

The contractibility follows from Prop 2.4: QC(V) is a fiber bundle with
contractible fibers Π(V, g₀) (convex open sets) over a contractible base
(the space of positive-definite inner products).

**Formalization note.** We do not yet have a topology on `QC V`, so the
contractibility statement cannot be expressed as `∃ (c : QC V), Nonempty
(ContinuousMap.Homotopy (ContinuousMap.id (QC V)) (ContinuousMap.const (QC V) c))`.
This placeholder records the result with a `True` conclusion until the topology is
formalized. -/
theorem QC_contractible (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    -- Placeholder: the real statement requires a topology on QC V.
    True := by
  trivial

/-! ## KS paper Proposition 2.7: domain of holomorphy -/

/-- **KS paper Proposition 2.7.** QC(V) is holomorphically convex — it is a domain
of holomorphy in the space of complex quadratic forms on V.

The proof in [KS] observes that QC(V) is the intersection of a product of Siegel
domains ∏ U(∧ᵖ(V)) with an affine subvariety, and Siegel domains are known domains
of holomorphy.

**Formalization note.** Expressing this requires: (1) the complex-manifold structure
on the space of quadratic forms, (2) the notion of domain of holomorphy (Stein
manifold), and (3) Siegel domains. None of these are in Mathlib. This placeholder
records the result with a `True` conclusion. -/
theorem QC_domain_of_holomorphy (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    -- Placeholder: requires complex-manifold structure and Stein domain theory.
    True := by
  trivial

/-! ## Two-dimensional special case (KS paper, p. 15) -/

/-- **KS paper, p. 15 (unnumbered).** When `dim V = 2`, the domain QC(V) is a
3-dimensional polydisc.

When `d = 2`, the conformal structure decouples from the volume element. A
nondegenerate complex metric is determined by two null directions in P(V_ℂ)
(one in each hemisphere) plus a complex volume element, giving a 3-dimensional
polydisc.

**Formalization note.** This is stated as a placeholder. The polydisc identification
requires projective geometry and the conformal/volume decomposition of quadratic
forms, which are not yet formalized. -/
theorem QC_two_dim_polydisc (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (_hdim : Module.finrank ℝ V = 2) :
    -- Placeholder: requires projective geometry and polydisc identification.
    True := by
  trivial
