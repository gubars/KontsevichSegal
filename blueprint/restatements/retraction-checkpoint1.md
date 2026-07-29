# The positive-definite retraction of $Q_{\mathbb C}(V)$ — checkpoint 1 (proved machinery)

**Status: RULINGS RECORDED 2026-07-29 — D1 new file, D2 full restructure. No repo file has been edited yet.**
Target path when approved: `blueprint/restatements/retraction-checkpoint1.md` (git-tracked;
commit with the checkpoint-1 edit).
Verified against `origin/main` at `32bffa2`. Scratch sources that this checkpoint transcribes:
`_scratch/f3_p1.lean`, `_scratch/f3_p2.lean`, `_scratch/f3_p5.lean` (untracked; they are the
working blueprint for the tracked build, not the deliverable).

This artifact covers **checkpoint 1 only**: transcribing the five already-proved pieces into
tracked Lean, with `QC_contractible`'s `sorry` still standing. Assembly — allowability of the
homotopy, joint continuity, `Homotopy` packaging, the endpoint contraction — is **checkpoint 2**
and gets its own artifact.

---

## 1. What this is, and how it relates to KS

KS derive contractibility of $Q_{\mathbb C}(V)$ from Proposition 2.4: a fibre bundle with
contractible convex fibres $\Pi(V,g_0)$ over a contractible base. **This proof takes a different
route** — a deformation retraction of $Q_{\mathbb C}(V)$ onto the real positive-definite cone,
which is convex hence contractible.

**That divergence is legitimate, with precedent.** Faithfulness attaches to the *theorem*, not to
the *proof*: Run 7 proved Theorem 2.2's reverse direction by a spectral-theorem assembly rather
than KS's route, and `restrict_nondegenerate` closed by the codim-free rotation route rather than
the polarization trio recorded in the plan. The theorem stated must be KS's; the argument need not
be.

**Two consequences that must be recorded, not glossed.** First,
`prop:contractibility`'s proof node currently reads "Contractibility follows from the fibre-bundle
description of Proposition~\ref{prop:parametrization}", which becomes a **false description of the
Lean** and must be rewritten. Second, this route does **not** prove Proposition 2.4, so F2 remains
owed for `prop:parametrization` regardless — the retraction is additive, never a substitute.

**Provenance of the argument, stated plainly.** The retraction argument was constructed in the
planning conversation, not taken from KS or from any source. It was then put to a compiler rather
than accepted on plausibility, and every load-bearing step closed sorry-free (P1–P5 below). The
remaining assembly steps are *unproved* and are explicitly not claimed here.

---

## 2. The five proved pieces

All five compiled sorry-free and axiom-free in scratch. Names below are the intended tracked
names; transcribe the scratch proofs, do not re-derive them.

**P1 — the segment angle bound.** For $\lambda \neq 0$ with $|\arg\lambda| < \pi$, $r > 0$ real,
and $t \in [0,1]$: $z := (1-t)\lambda + tr$ satisfies $z \neq 0$ and
$|\arg z| \le |\arg\lambda|$. Closed in the **full $\le$ form**, no weakening needed. Proof shape:
reduce along `Complex.cos_arg` to $\lambda.\mathrm{re}\,\|z\| \le z.\mathrm{re}\,\|\lambda\|$,
sign-split, close by `nlinarith` from the identity
$(z.\mathrm{re}\|\lambda\|)^2 - (\lambda.\mathrm{re}\|z\|)^2
= \lambda.\mathrm{im}^2 (tr)(z.\mathrm{re} + (1-t)\lambda.\mathrm{re})$; lower half-plane by
conjugation. **No Mathlib support exists for this** (established by the earlier probe), so it is a
genuine from-scratch addition and a plausible upstreaming candidate.

**P2 — the retraction map.**
`g0 g := ((detSqrtReal g.toComplexMetric)⁻¹ • g.toForm).compr₂ Complex.reLm`, with `g0_apply` by
`rfl`. The $\mathbb C$-valued coercion that works is postcomposition with
`Algebra.linearMap ℝ ℂ`, also `rfl`-evaluating. Note: no `SMul` on `ComplexMetric` is needed — the
scalar multiplies the *form*, which is already a module. The bridge
`AllowableComplexMetric.toComplexMetric` exists (`HodgeScaffold.lean:884`) with the `@[simp]`
float-free tie `toComplexMetric_toForm`; an earlier probe reported it NONE FOUND, which was a
wrong-file grep, independently corrected on both sides.

**P3 — positive-definiteness of `g0`.** Chain: `g.angle_cond` → `isAllowableHodge_of_diag` →
`re_normalized_toForm_pos` (`Equivalence.lean:327`). The bridge transfers definitionally; no
rewriting needed.

**P4 — same-basis diagonality.** `g0_diag : g0 g v v = ∑ i, (c * eig i).re * (b.repr v i)^2` on
$g$'s **own** `angle_cond` basis. This is the step that makes P1 apply per-entry, and it is why
the argument works: $g_0(g)$ is diagonal in the same *real* basis as $g$, so the segment is
diagonal there too. The witness is $g$'s own basis, so `angle_cond` is consumed as a **Prop**, not
as extracted data — the route therefore does not depend on Proposition 2.4 content.

**P5 — continuity of `g0`.** Proved, from F1's induced topology to the real form space with its
`moduleTopology`. The `Exists.choose` in `detSqrtReal` was **not** an obstruction: it is routed
around by proving `detSqrtReal g = exp ((1/2) • log (detGramReal g))` via the uniqueness pin
`detSqrtReal_eq_of_sq`, then composing continuous pieces. Requires
`haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional` (Mathlib's instance is
local-only), `IsModuleTopology.continuous_bilinear_of_finite_left` for the $\mathbb C$-`smul`, and
root-level `continuousAt_clog`.

**Pin-specific naming friction to carry into the transcription** (hit three times in P1):
`le_or_lt` / `lt_or_le` are gone at this pin — use `le_total`; `div_le_div_iff` is now
`div_le_div_iff₀`; `StrictAntiOn.le_iff_le` does not resolve — `by_contra` plus direct application
does.

---

## 3. Where the code goes — D1 **[RULED: new file]**

**RULED — a NEW file, `KontsevichSegal/ComplexMetrics/Contractibility.lean`,** importing
`ComplexMetrics.Domain` (for F1's topology instance) and `ComplexMetrics.Equivalence` (for
`re_normalized_toForm_pos` and `isAllowableHodge_of_diag`; `HodgeScaffold` arrives transitively).

Verified: **no cycle risk either way.** Nothing in the repo imports `Domain`, and `Equivalence`
does not import `Domain`, so appending to `Domain.lean` would also be legal. The reason to prefer
a new file is that `Domain.lean` is currently 66 lines holding $\Pi(V)$ and the F1 topology, and
appending would drag `HodgeScaffold` + `Equivalence` + `InnerProductSpace.Spectrum` into its
import surface for material that is a distinct concern.

**Consequence to predict in the gate:** `mk_all` **stops being a no-op**. A new file means
`KontsevichSegal.lean` is regenerated and `KontsevichSegal/ComplexMetrics.lean` needs an
`import KontsevichSegal.ComplexMetrics.Contractibility` line added by hand. The CI `mk_all-check`
will fail if the root is not regenerated. This is the first commit in the phase where that
applies.

---

## 4. Blueprint — D2 **[RULED: full `\uses` restructure]**

**A new lemma node for the machinery.** This material is *not* KS content; it is in-repo machinery
supporting a KS proof. The exact precedent is `lem:eigenvalue-minmax`, which is Courant–Fischer —
also not KS content — extracted as its own lemma node to support Proposition 2.5's proof, and now
dark green. Follow that pattern, including the titling convention of *no* KS citation in the
title.

Proposed node, in `content.tex` immediately before `prop:contractibility`:

- `\begin{lemma}[The positive-definite retraction of $Q_{\mathbb C}(V)$; in-repo machinery]`
- `\label{lem:posdef-retraction}`
- `\lean{...}` — the five names, exactly as they compile
- statement `\leanok` **and** a proof block with `\leanok` (everything listed is proved)
- `\uses{def:allowable, def:allowable-hodge, thm:angle-equiv, found:hodge-star}`

**`prop:contractibility`'s `\uses` restructure.** Its current edges were written when I believed
the proof went via the bundle. They are now wrong in two places:

- **statement** `\uses{def:allowable, def:trace-norm-fiber, prop:parametrization}` →
  `\uses{def:allowable}`. The *statement* — "$Q_{\mathbb C}(V)$ is contractible" over F1's
  topology — never needed the fibre or the bundle. That was my error when the node was created.
- **proof** `\uses{prop:parametrization}` → `\uses{lem:posdef-retraction}`, with the prose
  rewritten to describe the retraction rather than the bundle.

**RULED — do the full restructure now.** Deferring a known-wrong edge is precisely what the
F4-correction lesson was about, and the alternative — fixing only the proof `\uses` — leaves the
statement claiming a dependency on Proposition 2.4 that it does not have.

**Source-pair accounting** (distinct `\uses` pairs): $+4$ into the new node;
$-2$ from `prop:contractibility` (`def:trace-norm-fiber`, `prop:parametrization`); $+1$
(`lem:posdef-retraction → prop:contractibility`). Net **$+3$ distinct source pairs**.

**Rendered delta cannot be predicted exactly** — the graph is transitively reduced, so some of the
four new incoming edges may be hidden. The gate condition is therefore *structural*, not a number:

- nodes **58 → 59**, the new one being `lem:posdef-retraction`
- edge `prop:parametrization → prop:contractibility` **REMOVED**
- edge `lem:posdef-retraction → prop:contractibility` **ADDED**
- `def:trace-norm-fiber → prop:contractibility` removed if it was rendered
- no edge added or removed anywhere else
- `prop:contractibility` keeps green-border/no-fill — its proof is still `\notready`

**Predicted: dark-green 7 → 8.** `lem:posdef-retraction` has statement and proof `\leanok`, and
its four ancestors are all built (`thm:angle-equiv` is itself dark green; `def:allowable`,
`def:allowable-hodge`, `found:hodge-star` are all `#B0ECA3` with `\leanok`). If so it would be the
**first dark-green increase since 2026-07-08**, and a genuine one rather than a Trap-1
transparency artifact, since there are no `\notready` ancestors at all. **The standing check
fires:** when a node newly turns dark green, re-verify its entire foundation ancestry rather than
trusting the colour. If it does *not* flip, that is informative — it points at an unbuilt ancestor
worth naming.

---

## 5. Predicted gate

- `lake build` green; **`sorry` stays 1**, still `QC_contractible`, still the only one. A second
  sorry, or zero, is a stop condition.
- `True` 0; bare `axiom` 0. Grep must exclude `_scratch/` (it holds scratch sorries).
- **`mk_all` is NOT a no-op** — new file. Root regenerated; `ComplexMetrics.lean` umbrella gains
  one import line.
- `lean_decls` grows by exactly the names placed in the new `\lean` list.
- `checkdecls` clean.
- Graph: exactly the structural delta in §4, and dark-green 7 → 8 with full ancestry re-verified.

---

## 6. What checkpoint 1 does not claim

It does not prove contractibility. It does not prove that $H(t,g)$ stays allowable, does not
establish joint $(t,g)$-continuity, does not package a `Homotopy`, and does not contract the
positive-definite endpoint. Those four are checkpoint 2, and until they compile the retraction
route is a well-supported plan rather than a theorem. `QC_contractible`'s `sorry` stands, and its
docstring should be extended to name the retraction route as the intended proof so a reader is not
misdirected toward the bundle.
