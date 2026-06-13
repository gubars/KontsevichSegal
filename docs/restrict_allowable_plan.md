# Plan: `restrict_allowable` (Prop 2.5)

Assessment of the two sorry'd fields of `restrict_allowable`
(`KontsevichSegal/ComplexMetrics/Restriction.lean`), the last open result in
Section 2. Verified against `docs/KSTeX.tex` p. 13 and Mathlib via the LSP.

## 1. The two fields: `nondegenerate` vs `angle_cond`

**Not independent — `nondegenerate` follows from `angle_cond`.** Once
`angle_cond` is proven we have a basis `bw` of `W` and `eig'` with
`AngleCondition eig'` and `(g|_W)(w,w) = ∑ eig'ₖ (bw.repr w k)²`. Polarize (as
in `volume_element_positive`'s `hbil` step, using `symmetric'`) to get
`(g|_W)(w,w') = ∑ eig'ₖ (bw.repr w k)(bw.repr w' k)`. For `w ≠ 0` pick `j` with
`bw.repr w j ≠ 0`; then `(g|_W)(w, bw j) = eig'_j · (bw.repr w j) ≠ 0`
(`eig'_j ≠ 0` by `AngleCondition.nonzero`). This is exactly the `hdne`/
nondegeneracy step already done inside `only_lorentzian_on_boundary`. So
**prove `angle_cond` first, then derive `nondegenerate` from it** (short,
low-risk). All difficulty is in `angle_cond`.

## 2. `angle_cond`: interlacing, and Mathlib support (thin)

The paper's proof is differential-geometric: `arg(g(v))` is a smooth function
on `ℙ(V)`, its critical values are the sorted angles `θ_k = arg(eigₖ)`,
characterized by a min–max over subspaces; for codimension-1 `W` the critical
values interleave (`θ_k ≥ θ'_k ≥ θ_{k+1}`), giving `∑|θ'_k| ≤ ∑|θ_k| < π`.
Formalizing critical values of a smooth map on `ℙ(V)` is out of scope; the
realistic substitute is the **algebraic** interlacing of a Hermitian
operator's eigenvalues. The angles are `arg(eigₖ)`, **not** eigenvalues of a
self-adjoint operator, so a Hermitian-interlacing lemma does not apply
directly without setup (the "subtlety" the task flags). The setup:

- All angles lie in an arc of width `< π` (the `φ = (N−Q)/2` construction
  already in `not_neg_real_axis`), so **rotate** `g̃ = e^{−iφ} g` to put every
  `arg(eigₖ) ∈ (−π/2, π/2)`. Then `g̃_R := Re(g̃)` is **positive-definite**,
  defining a real inner product on `V`, and the operator `T` with
  `Im(g̃)(v,w) = g̃_R(Tv,w)` is `g̃_R`-self-adjoint with eigenvalues `tan θ̃_k`.
  Interlacing is rotation-invariant, and `arctan` is monotone, so eigenvalue
  interlacing of `T` transfers to angle interlacing.

**Mathlib status (checked via LSP, all typecheck unless noted):**
- CONFIRMED `LinearMap.IsSymmetric.eigenvalues` (sorted eigenvalues `Fin n → ℝ`)
  and `LinearMap.IsSymmetric.eigenvalues_antitone`; spectral theorem present as
  `LinearMap.IsSymmetric.diagonalization` / `eigenvectorBasis`
  (NOT `spectral_theorem` — that name is unknown).
- CONFIRMED only **extremal** Rayleigh characterizations:
  `IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` / `...iInf...` (top and
  bottom eigenvalue only).
- **NOT FOUND: Cauchy interlacing** (`interlace` search empty) and **NOT FOUND:
  Courant–Fischer min–max for the `k`-th eigenvalue** (only the extremal
  iSup/iInf exist). These are the linchpins and are absent.

So the angle_cond proof would have to **build Courant–Fischer min–max (or
Cauchy interlacing) from scratch** on top of `IsSymmetric.eigenvalues`, plus
the inner-product-from-rotated-real-part setup and the matching of the
`angle_cond` existential basis to the spectral eigenbasis.

## 3. Is there an elementary route avoiding min–max?

Not a real one. The `only_lorentzian` inline trick worked because it needed
only a **coarse count** ("at most one negative direction"), cut out by a single
linear condition. `angle_cond` needs control of the **entire sorted spectrum**
(`∑|θ'_k| ≤ ∑|θ_k|`), which is precisely interlacing — the 2-plane/dimension
trick does not generalize. The paper's own reduction to **codimension 1** does
not remove the need: codim-1 interlacing of a Hermitian compression is itself
Cauchy interlacing, still proved via min–max (or a secular-equation / inertia
argument of comparable cost). Alternatives (Sylvester inertia counting,
characteristic-polynomial interlacing) have no more Mathlib support than min–max
and are fiddlier. There is no shortcut that bypasses building one of these.

## 4. Difficulty estimate

**Defer with a thorough blueprint entry.** This is not a "session or two"
grind. Rough size 600–1000+ lines, with two genuinely hard, foundational
pieces and thin Mathlib support:
- **Riskiest:** formalizing Courant–Fischer min–max (or Cauchy interlacing) for
  `IsSymmetric.eigenvalues` — a known-nontrivial result that is simply not in
  Mathlib today. This is the linchpin; everything else is plumbing.
- **Second:** the inner-product-from-`g̃_R` construction (`InnerProductSpace`
  from a positive-definite real bilinear form), the `g̃_R`-self-adjoint `T`,
  `eigenvalues T = tan θ̃_k`, and reconciling the spectral eigenbasis with the
  `AngleCondition` existential.

Recommended next move: keep the faithful sorry'd statement; write the blueprint
proof node to record the rotation→positive-definite→self-adjoint→interlacing
plan and explicitly flag the missing Courant–Fischer/interlacing infrastructure
as the blocker (analogous to how Props 2.3/2.6/Hodge gaps are recorded). If
pursued, the highest-leverage step is contributing a general min–max lemma to
Mathlib's spectral file first; with that in hand the rest becomes a hard but
bounded grind. `nondegenerate` should be closed regardless once `angle_cond`
lands, since it is immediate from the diagonalization.
