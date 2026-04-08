# Section 2: The Domain of Complex Metrics — Formalization Status

## Completed

| Result | Description | File | Status |
|--------|-------------|------|--------|
| Defn 2.1 | Allowable complex metric (Hodge star formulation) | `ComplexMetrics/Equivalence.lean` | Deferred — equivalence with Thm 2.2 stated as placeholder. Blocked on Hodge star not being in Mathlib. |
| Thm 2.2 | Diagonal characterization / angle condition | `ComplexMetrics/Defs.lean` | ✅ Used as working definition. `AngleCondition` and `AllowableComplexMetric` structures defined. |
| Prop 2.4 | QC(V) is a fiber bundle over positive-definite inner products; QC(V) is contractible | `ComplexMetrics/Domain.lean` | ✅ Stated with sorry. `TraceNormLtOne` defined. Contractibility and fiber bundle parametrization stated as placeholders (topology on QC not yet formalized). |
| Prop 2.5 | Restriction of an allowable metric to a subspace is allowable | `ComplexMetrics/Restriction.lean` | ✅ Stated with sorry. `restrict` and `restrict_symmetric` defined. Main def `restrict_allowable` stated, proof requires eigenvalue interleaving argument. |
| Prop 2.7 | QC(V) is holomorphically convex (domain of holomorphy) | `ComplexMetrics/Domain.lean` | ✅ Stated as placeholder with sorry. |
| Shilov boundary (unnumbered, p.9) | Real Lorentzian metrics of signature (d-1,1) — and no other nondegenerate real metrics — lie on the Shilov boundary of QC(V) | `ComplexMetrics/ShilovBoundary.lean` | ✅ `IsLorentzian` predicate defined. `lorentzian_on_boundary`, `only_lorentzian_on_boundary`, and `two_copies_on_boundary` stated with sorry. |

## In Progress

All Section 2 results are now either completed or deferred. No results currently in progress.

## Deferred

| Result | Description | Why deferred | When needed |
|--------|-------------|--------------|-------------|
| Prop 2.3 | Conf_k(V) is contained in the holomorphic envelope of the Wightman permuted extended tube U_k(V) | Depends on Wightman tube domain machinery (not yet formalized). This result motivates the angle condition but is not needed for the complex metrics module itself. | When `WickRotation/` or a Wightman tube domain module is built |
| Prop 2.6 | The space R(Z) of real subspaces of a complex quadratic space on which g is allowable is contractible | Used in Section 5 for the Wick rotation of field operators. Not needed for the complex metrics module. | When `WickRotation/FieldOperators.lean` is built |
| Lemma 2.8 | Holomorphic extension from an L-shaped subset (technical lemma in the appendix) | Part of the proof of Prop 2.3. Deferred along with it. | When Prop 2.3 is formalized |

## Additional consequences (unnumbered, stated with sorry)

| Result | Page | File | Status |
|--------|------|------|--------|
| g(v) is never real and negative for v ≠ 0 | p.9 | `ComplexMetrics/Defs.lean` | `not_neg_real_axis` — stated with sorry |
| det(g) avoids the negative real axis; √det(g) has positive real part | p.7 | `ComplexMetrics/Defs.lean` | `volume_element_positive` — stated with sorry |
| Values g(v) form a convex cone disjoint from the negative real axis | p.9 | `ComplexMetrics/Defs.lean` | Not yet stated |
| Two-dimensional case: QC(V) is a 3-dimensional polydisc | p.15 | `ComplexMetrics/Domain.lean` | `QC_two_dim_polydisc` — stated as placeholder with sorry |
| One-dimensional case: electrical circuits | p.16 | — | Not planned for now |
