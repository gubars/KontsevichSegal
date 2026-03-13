/- Equivalence between the working definition (angle condition, Theorem 2.2) and
the original Definition 2.1 (Hodge star formulation). Deferred until Hodge star
infrastructure is available in Mathlib.

**Definition 2.1 of [KS]** states: a complex quadratic form g on V is allowable if,
for all degrees p ≥ 0, the real part of the quadratic form on ∧ᵖ(V*) defined by
  α ↦ α ∧ ∗_g α
is positive-definite, where ∗_g is the Hodge star operator associated to g.

**Theorem 2.2 of [KS]** (our working definition) characterizes the same class
diagonally: g is allowable iff there is a basis in which g = ∑ᵢ λᵢ yᵢ² with
each λᵢ nonzero, not on the negative real axis, and ∑ᵢ |arg λᵢ| < π.

The equivalence of these two conditions is proved in [KS] but cannot yet be
formalized here, as the Hodge star operator is not available in Mathlib.
-/

import KontsevichSegal.ComplexMetrics.Defs

/-- Placeholder for the equivalence between Definition 2.1 and the angle condition
(Theorem 2.2) of [KS].

The Hodge star side of the equivalence asserts: for all p ≥ 0, Re(α ∧ ∗_g α) > 0
for all nonzero α ∈ ∧ᵖ(V*). This is equivalent to `AngleCondition` on the
eigenvalues in any diagonal form of g, as shown in [KS, Section 2].

Formalization is blocked on Hodge star infrastructure in Mathlib. -/
theorem defn_2_1_equiv_angle_condition
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (_g : AllowableComplexMetric V) :
    -- Placeholder: True stands for "g satisfies Definition 2.1 (Hodge star condition)"
    -- which we cannot yet express. The real statement is a biconditional between
    -- Definition 2.1 and the AngleCondition encoded in AllowableComplexMetric.
    True := by
  trivial
