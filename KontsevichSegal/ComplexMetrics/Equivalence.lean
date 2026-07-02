/- Equivalence between the working definition (angle condition, Theorem 2.2) and
the original Definition 2.1 (Hodge star formulation).

**Definition 2.1 of [KS]** states: a complex quadratic form g on V is allowable if,
for all degrees p ≥ 0, the real part of the quadratic form on ∧ᵖ(V*) defined by
  α ↦ α ∧ ∗_g α
is positive-definite, where ∗_g is the Hodge star operator associated to g. This is
formalized as `KontsevichSegal.Hodge.IsAllowableHodge`
(`ComplexMetrics/HodgeScaffold.lean`), on the project's from-scratch Hodge star.

**Theorem 2.2 of [KS]** (our working definition) characterizes the same class
diagonally: g is allowable iff there is a basis in which g = ∑ᵢ λᵢ yᵢ² with
each λᵢ nonzero, not on the negative real axis, and ∑ᵢ |arg λᵢ| < π.

The FORWARD direction of the equivalence (angle condition ⇒ Definition 2.1) is
proved here (`defn_2_1_equiv_angle_condition`, via
`KontsevichSegal.Hodge.isAllowableHodge`). The REVERSE direction requires stating
Definition 2.1 for a bare symmetric nondegenerate ℂ-valued form (no angle condition
assumed) — a type this development does not yet have — together with the real
simultaneous diagonalization step of KS's proof (KSTeX 199); it is deferred, so the
biconditional of Theorem 2.2 is not yet stated.
-/

import KontsevichSegal.ComplexMetrics.Defs
import KontsevichSegal.ComplexMetrics.HodgeScaffold

/-- **Forward direction of the equivalence between Definition 2.1 and the angle
condition (KS paper Theorem 2.2).** Every allowable complex metric — the working,
angle-condition definition `AllowableComplexMetric` — satisfies KS Definition 2.1:
for all degrees p ≥ 0, the real part of the quadratic form `α ↦ α ∧ ∗_g α` on real
`p`-forms is positive-definite (`KontsevichSegal.Hodge.IsAllowableHodge`).

The reverse direction (Definition 2.1 ⇒ the angle condition) needs Definition 2.1
stated on a bare symmetric nondegenerate ℂ-valued form, with no diagonalization
assumed, plus the real simultaneous diagonalization of KS's proof (KSTeX 199); it
is deferred, so the biconditional of Theorem 2.2 is not yet stated in Lean. -/
theorem defn_2_1_equiv_angle_condition
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : AllowableComplexMetric V) :
    KontsevichSegal.Hodge.IsAllowableHodge g :=
  KontsevichSegal.Hodge.isAllowableHodge g
