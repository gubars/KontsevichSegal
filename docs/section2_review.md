# Section 2 Review — Lean formalization vs. KS paper

Date: 2026-06-10
Scope: every declaration in `KontsevichSegal/ComplexMetrics/` and
`KontsevichSegal/Basic.lean`, checked line-by-line against Section 2 (and its
appendix) of `docs/KSTeX.tex` (arXiv:2105.10161).

Classification:
- **CRITICAL** — the Lean statement is mathematically wrong relative to the paper
  (false, vacuous/trivially satisfiable, or expressing a different claim).
- **MODERATE** — statement is right but the proof approach, sorry, or
  surrounding documentation is misguided.
- **MINOR** — cosmetic, naming, redundancy, or docstring issues.

## Summary

| # | Severity | Location | Issue | Action taken |
|---|----------|----------|-------|--------------|
| 1 | CRITICAL | `Domain.lean` `TraceNormLtOne` | Trace-norm condition is vacuous (eigenvalues not tied to the operator) | **Fixed** |
| 2 | CRITICAL | `ShilovBoundary.lean` `only_lorentzian_on_boundary` | Statement is **false** — boundary hypothesis forces `g = φ`, so the hypothesis actually says φ is positive-definite | **Fixed** |
| 3 | CRITICAL | `ShilovBoundary.lean` `lorentzian_on_boundary` | Conclusion never relates the allowable metric `g` to the basis/eigenvalues or to φ; trivially satisfiable | **Fixed** |
| 4 | CRITICAL | `ShilovBoundary.lean` `two_copies_on_boundary` | Trivially satisfiable (no convergence to φ required); also the genuine "two disjoint copies" statement needs infrastructure we lack | **Fixed** (approximate version; see flag) |
| 5 | MODERATE | `ShilovBoundary.lean` module docstring | Wrong mathematics: claims the boundary Lorentzian metrics have "one eigenvalue purely imaginary (contributing \|arg\| = π/2)" summing to π | **Fixed** |
| 6–12 | MINOR | various | Redundant fields/hypotheses, docstring mismatches, README formula error | README formula fixed; rest flagged, left as-is |

Sorry count is unchanged (7); `True`-placeholder count unchanged (5); no `axiom`
introduced. All sorrys now sit under statements I believe are mathematically
correct and faithful to the paper.

---

## CRITICAL issues

### 1. `Domain.lean` — `TraceNormLtOne` was vacuous

**Lean (before):**

```lean
structure TraceNormLtOne (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] where
  toLinearMap : V →ₗ[ℝ] V
  eigenvalues_trace_norm_lt_one :
    ∃ θ : Fin (Module.finrank ℝ V) → ℝ, ∑ i, |θ i| < 1
```

The existential `∃ θ, ∑ i, |θ i| < 1` never mentions `toLinearMap`. It is
satisfied by `θ = 0` for **every** linear map, so `TraceNormLtOne V` was just
"an arbitrary endomorphism of V" — it carried no mathematical content. The
status doc listed it as "Proven (definitional)", which obscured this.

**Paper (p. 11, after the proof of Thm 2.2):**

> "the space Q_C(V) is parametrized by the pairs (g₀, Θ), where g₀ is a
> positive-definite inner-product on V and Θ belongs to the convex open set
> Π(V,g₀) of operators in V which are self-adjoint with respect to g₀ and
> satisfy ‖Θ‖₁ < 1" — where "The trace-norm is the sum of the absolute values
> of the eigenvalues."

**Fix applied.** The eigenvalues are now tied to the operator through an
eigenbasis:

```lean
  exists_eigenbasis_trace_norm_lt_one :
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
      (θ : Fin (Module.finrank ℝ V) → ℝ),
      (∀ i, toLinearMap (b i) = θ i • b i) ∧ ∑ i, |θ i| < 1
```

Note on self-adjointness: `V` carries no inner product here (deliberately —
see the `QC_parametrization` formalization note), so "self-adjoint with respect
to g₀" cannot be stated directly. An operator is g₀-self-adjoint for *some*
positive-definite g₀ iff it is diagonalizable over ℝ (make the eigenbasis
orthonormal), so the encoding above is a faithful basis-free packaging of
"Θ ∈ Π(V, g₀) for some g₀". When the inner-product-space version of Prop 2.4
is formalized, the fiber at a *fixed* g₀ will need the genuine self-adjointness
condition; this is recorded in the docstring.

### 2. `ShilovBoundary.lean` — `only_lorentzian_on_boundary` was false

**Lean (before):**

```lean
theorem only_lorentzian_on_boundary ... (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (_hnd : ∀ v, v ≠ 0 → ∃ w, φ v w ≠ 0)
    (_hbdy : ∀ ε : ℝ, 0 < ε →
      ∃ g : AllowableComplexMetric V,
        ∀ v, ‖g.toForm v v - ↑(φ v v)‖ < ε) :
    IsLorentzian φ
```

The boundary hypothesis `∀ v, ‖g.toForm v v - ↑(φ v v)‖ < ε` quantifies over
**all** `v` with a fixed ε. Quadratic forms scale: replacing `v` by `t • v`
scales the difference by `t²`, so the only way the bound can hold for all `v`
is `g.toForm v v = φ v v` for every `v`. Hence `_hbdy` is equivalent to
"φ itself (complexified) is allowable". But a *real* allowable form is
positive-definite (in any diagonalizing basis from `angle_cond`, each
eigenvalue `eig i = Q(b i)` is real, and `not_nonpos_real` forces it positive).
So the hypothesis implies φ is positive-definite, while the conclusion asserts
φ is Lorentzian — a contradiction. Concrete counterexample: `V = ℝ`,
`φ(x, y) = x * y`, with `g` the complexification of φ (allowable, eig = 1):
all hypotheses hold but `IsLorentzian φ` is false. **The theorem was false and
its sorry unfillable.**

**Paper (p. 9):**

> "It follows from Theorem 2.2 that the real inner products with signature
> (d−1,1) --- but not those with other signatures --- lie on the boundary of
> the domain Q_C(V). For if the metric is real then each |arg(λ_i)| is either
> 0 or π, and the inequality (4) shows that at most *one* of the |arg(λ_i)|
> can become π on the boundary."

**Fix applied.** Two changes:

1. *Closeness is now measured on the entries of a fixed basis* (`∀ i j,
   ‖g.toForm (b i) (b j) - ↑(φ (b i) (b j))‖ < ε`), which is the correct
   encoding of convergence in the (finite-dimensional, hence canonical)
   topology on the space of forms. The basis must be fixed *outside* the
   `∀ ε` quantifier: allowing it to vary with ε would let one rescale the
   basis and shrink any signature's negative directions toward a degenerate
   positive-semidefinite form, again making the statement false.
2. *Added the hypothesis that φ is not positive-definite.* "Boundary" means
   closure minus interior; the real points of the open domain QC(V) are
   exactly the positive-definite forms, and these are also limits of allowable
   metrics. Without excluding them the conclusion is false (the same
   counterexample as above, now with entry-wise closeness). With the new
   hypotheses the statement matches the paper: a real nondegenerate form in
   the closure of QC(V) has at most one negative eigenvalue; nondegeneracy
   plus not-positive-definite forces exactly one, i.e. signature (d−1, 1).

### 3. `ShilovBoundary.lean` — `lorentzian_on_boundary` did not say what it claimed

**Lean (before):**

```lean
theorem lorentzian_on_boundary ... (φ ...) (_hL : IsLorentzian φ)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ g : AllowableComplexMetric V,
      ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
        (eig : Fin (Module.finrank ℝ V) → ℂ),
        AngleCondition eig ∧
        ∀ i, ‖eig i - ↑(φ (b i) (b i))‖ < ε
```

Nothing connects `g` to `(b, eig)`: the conclusion asserts (a) some allowable
metric exists, and (b) some tuple `eig` satisfying the angle condition is close
to the diagonal values of φ in some basis. Both are easy facts that hold with
`g` and `(b, eig)` chosen completely independently, so the statement does not
express "φ lies on the boundary of QC(V)". Also only diagonal entries `(i, i)`
were constrained, not the off-diagonal ones.

**Paper (p. 9):** same passage as issue 2 — Lorentzian metrics *lie on the
boundary* of QC(V), i.e. they are limits of allowable metrics without being
allowable themselves.

**Fix applied.** The conclusion now says exactly that, in two conjuncts:

```lean
    (∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ ε : ℝ, 0 < ε →
        ∃ g : AllowableComplexMetric V,
          ∀ i j, ‖g.toForm (b i) (b j) - ↑(φ (b i) (b j))‖ < ε) ∧
    (∀ g : AllowableComplexMetric V, ∃ v, g.toForm v v ≠ ↑(φ v v))
```

— φ is a limit of allowable metrics (entry-wise in a fixed basis), and φ is
not itself allowable. Both parts are true and provable (perturb the negative
eigenvalue to `exp(i(π−δ))`; the second conjunct follows from
`not_neg_real_axis`). ε moved into the statement so the basis can be shared
across all ε.

### 4. `ShilovBoundary.lean` — `two_copies_on_boundary` was trivially satisfiable

**Lean (before):**

```lean
    ∀ (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), IsLorentzian φ →
      ∃ (g_upper g_lower : ℕ → AllowableComplexMetric V),
        (∀ n v w, (g_upper n).toForm v w = starRingEnd ℂ ((g_lower n).toForm v w))
```

The families were not required to converge to φ (or relate to φ at all), and
nothing distinguished "upper" from "lower". Any allowable `g` with constant
families `g_lower n = g`, `g_upper n = conj g` witnesses the statement, so the
sorry sat under a contentless claim.

**Paper (p. 9):**

> "In fact the Shilov boundary of Q_C(V) contains *two* disjoint copies of the
> space of Lorentzian metrics on V, for an eigenvalue λ can approach the
> negative real axis either from above or from below. The two copies are
> interchanged by the complex-conjugation map on Q_C(V)."

**Fix applied.** The statement now requires: a basis diagonalizing φ with a
distinguished time direction `i₀` (where `φ (b i₀) (b i₀) < 0`), pointwise
complex-conjugate families, the upper family approaching through the upper
half-plane (`0 < ((g_upper n).toForm (b i₀) (b i₀)).im`), and entry-wise
convergence of the families to φ.

**Flag for decision (left open).** Even the fixed statement only captures
"φ is approachable from both half-planes, symmetrically under conjugation".
The paper's actual claim — that the two limits are *distinct points* of the
Shilov boundary — is invisible in the naive closure of QC(V) in S²(V*_ℂ),
where both families converge to the *same* form φ. The two copies are
distinguished only in the bounded affine-variety realization used in the proof
of Prop 2.7 (the embedding involves `(det g)^(1/2)`, whose branch differs in
the two limits), and a Shilov boundary formalization needs that embedding plus
Stein-domain theory not in Mathlib. If you prefer, this theorem could instead
be downgraded to a `True` placeholder; I kept the approximate-but-true version
per the "prefer sorry over True" rule.

**Resolution (2026-06-10 follow-up).** Decision made: approximate statements
that diverge from the paper are not acceptable (see the new "No
approximations" section in CLAUDE.md). `two_copies_on_boundary` is now a
`True` placeholder whose docstring quotes the paper's claim and names the
precise missing infrastructure: (1) induced forms on exterior powers / Hodge
star (for the embedding into ∏_{0≤p≤d/2} U(⋀ᵖV) from the proof of Prop 2.7),
(2) Siegel domains + Cayley transform (bounded realization), (3) the Shilov
boundary notion itself. Sorry count 7 → 6; True placeholders 5 → 6.

---

## MODERATE issues

### 5. `ShilovBoundary.lean` module docstring — wrong description of the boundary

**Lean (before):**

> "A complex metric g ∈ QC(V) approaches the Shilov boundary as the arguments
> arg(λᵢ) approach ±π/2 with ∑ᵢ |arg λᵢ| → π. The real slice of this boundary
> consists exactly of the Lorentzian metrics: one eigenvalue purely imaginary
> (contributing |arg| = π/2) and the rest real positive (contributing
> |arg| = 0), summing to π in total."

This is wrong twice over: (a) one purely imaginary eigenvalue plus positive
real ones gives ∑|arg| = π/2, not π — such a metric is *allowable* (interior),
not boundary; (b) the real Lorentzian boundary points have one eigenvalue on
the **negative real axis** (|arg| → π), not the imaginary axis. The paper
(p. 9): a real metric has each |arg(λᵢ)| equal to 0 or π, and exactly one can
reach π on the boundary. (Purely imaginary eigenvalues are how the *Siegel
domain's* Shilov boundary is described on p. 5, which is presumably the source
of the confusion.)

**Fix applied:** rewrote the module header.

---

## MINOR issues (flagged, not changed unless noted)

### 6. `Defs.lean` `AngleCondition` — redundant fields

`not_nonpos_real` (`0 < re ∨ im ≠ 0`) excludes the *non-positive* real axis,
hence already implies `nonzero`. Moreover both are implied by
`nonzero ∧ sum_arg_lt_pi` (a negative-real eigenvalue contributes |arg| = π ≥
the whole budget). The three fields faithfully mirror the paper's phrasing
("non-zero complex numbers, not on the negative real axis, such that (4)"),
so I left them; just be aware constructors must discharge redundant
obligations. Not an error.

### 7. `Defs.lean` `AllowableComplexMetric.nondegenerate` — redundant field

Nondegeneracy is derivable from `symmetric'` + `angle_cond` (polarization
gives `B(v, b i₀) = eig i₀ · (repr v i₀)` in the diagonalizing basis). The
paper does not list it as a separate condition. Keeping it is sound but means
`restrict_allowable` must sorry it separately. Consider deriving it as a lemma
and dropping the field in a later refactor — left for you to decide since it
changes the public API.

### 8. `Defs.lean` `not_neg_real_axis` — unnecessary hypothesis

The hypothesis `hv : v ≠ 0` is not needed: `g(0,0) = 0` is not negative-real
either. Harmless; matches the paper's "for v ∈ V" emphasis on the cone. Left.

### 9. `Defs.lean` `volume_element_positive` — docstring/statement mismatch

The docstring says "the *unique* `w : ℂ` with `w ^ 2 = det` and `0 < w.re`"
but the statement only asserts existence (`∃ w`). Uniqueness is true and easy
(the other root is `−w`). Suggest upgrading to `∃!` when the sorry is filled.
Left as-is to avoid churning a sorry'd goal. Statement itself is correct and
faithful to p. 7 ("we require that det g ... is *not* real and negative, and
we choose (det g)^{1/2} to have positive real part") — checked that the claim
is basis-independent (Gram determinants differ by `det(P)² > 0`).

### 10. `Equivalence.lean` `defn_2_1_equiv_angle_condition` — placeholder shape

The placeholder takes `_g : AllowableComplexMetric V` as an argument, but the
real Theorem 2.2 is a biconditional over *arbitrary* complex quadratic forms
(Definition 2.1 ⟺ angle condition), not a statement about already-allowable
metrics. The docstring describes the intended content accurately; when Hodge
star lands, the statement should quantify over symmetric forms
`V →ₗ[ℝ] V →ₗ[ℝ] ℂ`, not over `AllowableComplexMetric`. Left (it's `True`
anyway).

### 11. `Restriction.lean` — redundant instance argument

`[FiniteDimensional ℝ W]` on `restrict_allowable` is inferable for any
submodule of a finite-dimensional space. Harmless. Left. The two sorry'd
fields (`nondegenerate`, `angle_cond`) sit under a **correct** statement of
Prop 2.5 ("If g ∈ Q_C(V) and W is any vector subspace of V then g|W belongs
to Q_C(W)", p. 13) — verified, including the degenerate case `W = ⊥`.

### 12. `README.md` — wrong angle condition formula

README described the angle condition as "|arg(g_{ii})| < π/2"; the actual
condition (paper eq. (4)) is `∑ᵢ |arg(λᵢ)| < π`. **Fixed** (doc-only change).

---

## Declarations verified correct (no action)

| Declaration | Verdict |
|-------------|---------|
| `AngleCondition.sum_arg_lt_pi` | Faithfully encodes paper eq. (4): `∑ i, |Complex.arg (eig i)| < Real.pi`. Mathlib's `Complex.arg` ranges in (−π, π], matching the paper's convention given the nonzero/not-negative-axis constraints. |
| `AllowableComplexMetric.angle_cond` | Faithful to Thm 2.2: diagonal values on the quadratic form determine the symmetric bilinear form by polarization, so constraining `toForm v v` suffices. Basis indexed by `Fin (finrank ℝ V)` = dimension d. ✓ |
| `QC` | Type-level alias for the domain; fine at current infrastructure level (paper's QC(V) is an *open subset* of S²(V*_ℂ); the subset/topology aspect is deferred with Prop 2.4). |
| `not_neg_real_axis` (statement) | True consequence of (4) via the convex-cone argument (p. 9, "g(v) can never be real and negative"). Sorry is fillable. |
| `volume_element_positive` (statement) | True for every basis; see issue 9. Sorry is fillable. |
| `QC_parametrization`, `QC_contractible`, `QC_domain_of_holomorphy`, `QC_two_dim_polydisc` | `True` placeholders; docstrings accurately describe Prop 2.4, Prop 2.7, and the p. 15 polydisc discussion, and the stated blockers (no topology on QC, no Stein/Siegel theory, no projective machinery) are genuine Mathlib gaps. |
| `AllowableComplexMetric.restrict`, `restrict_symmetric` | Correct and fully proven. |
| `restrict_allowable` | Correct statement of Prop 2.5; sorrys are the right goals. |
| `IsLorentzian` | Faithful encoding of signature (d−1, 1): by Sylvester's law every such form admits a ±1-diagonal basis with exactly one −1. Bilinear (not just quadratic) diagonal formula is fine for symmetric forms. |

## Build verification

`lake build` passes after the fixes (see project_status.md for the updated
inventory). Sorry count 7, `True` placeholders 5, `axiom` count 0 — unchanged.
