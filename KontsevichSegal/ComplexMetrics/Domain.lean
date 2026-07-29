/- The fibre Π(V) of the QC(V) bundle (KS Proposition 2.4).

This file formalizes the trace-norm fibre Π(V, g₀) of Proposition 2.4 from Section 2 of:

  Kontsevich, M. and Segal, G., "Wick rotation and the positivity of energy in
  quantum field theory", arXiv:2105.10161 [hep-th], 2021.

RETIREMENT (2026-07-29). This file previously carried four `True`-conclusion placeholder
theorems: `QC_parametrization` and `QC_contractible` (Prop 2.4),
`QC_domain_of_holomorphy` (Prop 2.7), and `QC_two_dim_polydisc` (p. 15). None of their
real statements is expressible against the current formalization, so none could carry a
`sorry` either; a `True` conclusion credentialled claims that no Lean statement made. All
four were REMOVED, and each claim now lives as `\notready` prose at its blueprint node
(`prop:parametrization`, `prop:domain-holomorphy`, `prop:two-dim-polydisc`), naming the
foundation it waits on: F1 (a topology on QC(V)), F2 (`found:homogeneous-bundles`, the
associated bundle GL(V) ×_{O(V)} Π(V) with a compatible inner-product layer), and F3
(`found:scv-tube-domain`, Stein/Siegel/Shilov theory). Reviewed artifact:
`blueprint/restatements/true-retirement-section2.md`.

(2026-07-30 addendum: `QC_contractible`, restated here at F1 with the project's
first honest `sorry`, MOVED to `ComplexMetrics/Contractibility.lean` when it was
proved — the proof lives in that file, which imports this one, so the theorem
could not remain here.)
-/

import KontsevichSegal.ComplexMetrics.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Homotopy.Contractible

/-! ## Π(V): the fiber of the QC bundle (KS paper Proposition 2.4)

Given a positive-definite inner product `g₀` on `V`, the *fiber* Π(V, g₀) is the
set of `g₀`-self-adjoint operators Θ on V with trace-norm ∑ᵢ |θᵢ| < 1, where
`θᵢ` are the eigenvalues of Θ. This is the interior of the convex hull of rank-1
orthogonal projections, and in particular is convex (hence contractible).

We define `TraceNormLtOne` as a simplified formulation: a linear map
Θ : V →ₗ[ℝ] V is in the fiber when it admits an eigenbasis with real
eigenvalues θ : Fin d → ℝ satisfying ∑ i, |θ i| < 1.
-/

/-- The set of self-adjoint operators with trace-norm less than 1, denoted Π(V) in
[KS]. This is the fiber of the bundle QC(V) → {positive-definite inner products}
from KS paper Proposition 2.4.

Given a reference inner product g₀ on V, Π(V, g₀) consists of ℝ-linear
endomorphisms Θ : V →ₗ[ℝ] V that are self-adjoint with respect to g₀
and satisfy ∑ᵢ |θᵢ| < 1 where θᵢ are the eigenvalues. Equivalently, Π(V, g₀) is
the interior of the convex hull of rank-1 orthogonal projections in V.

**Simplified formulation.** `V` carries no inner product here (`QC`'s
definition uses a plain `AddCommGroup`/`Module ℝ`, whereas
`InnerProductSpace ℝ V` would require `NormedAddCommGroup V`), so
g₀-self-adjointness cannot be stated directly. We instead require that Θ is
diagonalizable over ℝ — there is a basis `b` of eigenvectors with eigenvalues
`θ i` — with ∑ᵢ |θᵢ| < 1. An
operator is self-adjoint with respect to *some* positive-definite inner product
iff it is diagonalizable over ℝ (declare the eigenbasis orthonormal), so this
encodes "Θ ∈ Π(V, g₀) for some positive-definite g₀". The fiber at a *fixed*
g₀ will need genuine self-adjointness once the inner-product-space version of
Prop 2.4 is formalized. -/
structure TraceNormLtOne (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] where
  /-- The underlying ℝ-linear endomorphism. -/
  toLinearMap : V →ₗ[ℝ] V
  /-- There is an eigenbasis `b` with real eigenvalues `θ` whose absolute
  values sum to less than 1. This ties the eigenvalues to the operator and
  encodes the trace-norm condition ‖Θ‖₁ < 1. -/
  exists_eigenbasis_trace_norm_lt_one :
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
      (θ : Fin (Module.finrank ℝ V) → ℝ),
      (∀ i, toLinearMap (b i) = θ i • b i) ∧ ∑ i, |θ i| < 1

/-! ## F1: the topology on QC(V) -/

/-- Two allowable complex metrics with the same underlying form are equal. All
fields of `AllowableComplexMetric` other than `toForm` (`symmetric'`,
`nondegenerate`, `angle_cond`) are `Prop`-valued, so the form determines the
structure. -/
@[ext]
theorem AllowableComplexMetric.ext {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {g g' : AllowableComplexMetric V}
    (h : g.toForm = g'.toForm) : g = g' := by
  cases g with | mk f₁ s₁ n₁ a₁ =>
  cases g' with | mk f₂ s₂ n₂ a₂ =>
  obtain rfl : f₁ = f₂ := h
  rfl

/-- `toForm` is injective: an allowable complex metric is determined by its
bilinear form. This is load-bearing for F1, not decorative: it makes `toForm`
an embedding of `AllowableComplexMetric V` into the space of forms, so the
induced topology of `AllowableComplexMetric.instTopologicalSpace` is faithful,
and `QC_contractible` below is a claim about QC(V) itself rather than about
the image of `toForm` in the space of forms. -/
theorem AllowableComplexMetric.toForm_injective (V : Type*) [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] :
    Function.Injective
      (AllowableComplexMetric.toForm : AllowableComplexMetric V → (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)) :=
  fun _ _ h => AllowableComplexMetric.ext h

/-- The topology on QC(V) (foundation F1): the topology induced along `toForm`
from the canonical module topology on the space of forms. `moduleTopology ℝ _`
is canonical and basis-free (the finest topology making addition and the
ℝ-action continuous), so no choice is made here and no basis-independence
proof is owed. Moreover `FiniteDimensional ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)` holds by
instance search, so `isModuleTopologyOfFiniteDimensional` applies: any
Hausdorff topological-vector-space topology on the form space agrees with the
module topology, and every reasonable alternative therefore induces the same
topology on QC(V). -/
instance AllowableComplexMetric.instTopologicalSpace (V : Type*) [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] :
    TopologicalSpace (AllowableComplexMetric V) :=
  TopologicalSpace.induced AllowableComplexMetric.toForm
    (moduleTopology ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ))
