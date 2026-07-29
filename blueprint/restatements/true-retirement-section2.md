# Reviewed restatement: retiring the five Section-2 `True` placeholders

**Status: DRAFT FOR REVIEW. No repo file has been edited.**
Target path when approved: `blueprint/restatements/true-retirement-section2.md` (git-tracked;
commit together with the edit, per the existing per-node artifact convention).
All facts below verified against `origin/main` at `2033bf7` "Blueprint prose update cont".

---

## 1. Shape of this change

Subtractive, in one commit. Delete five `True`-conclusion Lean declarations and the four
`\lean{}` lines that name them; add one sentence per blueprint node naming the foundation the
claim waits on; repair two now-dangling comment cross-references.

Two points that narrow the phase brief's description of Step 1:

- **The prose already exists.** All four nodes carrying the five placeholders are already
  `\notready` with a faithful statement of the claim and `\uses` edges into `found:` nodes;
  `thm:two-copies` already itemises its three missing pieces. This pass therefore does not write
  the claims — it adds only the F-number naming, and removes the false Lean credentials.
- **No new statement, so no `sorry`.** Each claim is not statable against the current
  formalization, so it cannot carry a `sorry`. This is the node-4 (`def:wick-rotation`) shape:
  un-statable, retreat to `\notready` prose — not the node-2 shape (statable but false).

**No `\uses` edge is added or removed** (see decision D1). Consequently the dependency graph
should be *bit-for-bit unchanged in structure*: this is the strongest available gate.

### Predicted gate

| quantity | before | after |
|---|---|---|
| `True := by` | 5 | 0 |
| `sorry` (code) | 0 | 0 |
| `axiom` | 0 | 0 |
| `lean_decls` logical lines / names | 133 | 128 |
| blueprint nodes | 57 | 57 |
| rendered edges | 85 | 85 |
| dark green `#1CAC78` | 7 | 7 |
| fill census | 7 / 1 / 15 / 2 | unchanged |
| graph parse-diff | — | **EMPTY** |

`lake build` green; `lake exe checkdecls blueprint/lean_decls` clean. A non-empty parse-diff, or
any fill-map or edge change, is a **stop condition** — nothing in this change can legitimately
move a colour, because every affected node is already `\notready` and dropping a `\lean{}`
pointer does not set a border (established at node 2 and node 4).

`checkdecls` couples the two halves: the Lean deletions and the `\lean{}` deletions **must land in
the same commit**. Removing the declarations while `content.tex` still names them reproduces the
`263e747` / `3f82b05` broken-intermediate class exactly.

---

## 2. Decisions (all three RULED as recommended, 2026-07-29)

### D1 — `prop:two-dim-polydisc`: which foundation, and does its `\uses` edge change? **RULED: as recommended — name F1 + F3 + the extra piece, change no edge.**

There is a three-way disagreement in the current record:

- the phase brief's foundation map says site 4 "needs `found:scv-tube-domain`" (F3);
- the blueprint node's actual edge is `\uses{def:allowable, found:homogeneous-bundles}`;
- the node's own prose says it needs the projective geometry of $\mathbb P(V_{\mathbb C})$ and the
  conformal/volume decomposition — which is neither of those foundations.

Reading KS (KSTeX 284–294), all three are partly right. The claim needs: a topology and complex
structure on $Q_{\mathbb C}(V)$ even to say "is a polydisc" (**F1**, currently bundled inside
`found:homogeneous-bundles`, which is why the existing edge is defensible rather than wrong); the
polydisc as a *bounded* domain, which is F3-adjacent (cf. KS's own polydisc/Shilov example at
KSTeX 106) (**F3**); and the null-direction parametrization in $\mathbb P(V_{\mathbb C})$ plus the
$(\det g)^{-1/2}g$ conformal/volume decoupling — **a small in-repo build that is in none of
F1–F4**, and not a hard Mathlib gap (Mathlib has `Projectivization`; the d = 2 decoupling is
elementary).

**Recommendation:** name **F1 + F3 + a named projective/conformal piece** in prose, and change no
edge. Rationale: it keeps Step 1 purely subtractive so the parse-diff stays empty; the edge
question resolves itself when `found:homogeneous-bundles` is split into F1 and F2 (already a
queued bookkeeping item — the `def:metc-complex-manifold` node-split / F1 edge restore); and
adding an unreviewed edge inside a subtractive commit is precisely what the discipline hardened
against after the `lem:convex-cone` split.

**Correction to the brief this forces:** "5 sites reduce to 4 foundations" undercounts. Site 4
also needs a projective/conformal piece outside F1–F4. This is the second scoping correction
after the F4 finding.

### D2 — the two now-dangling comment cross-references. **RULED: repair both in this commit.**

Deleting the declarations strands two in-file mentions (discovery item B; neither is a term-level
use, so there is no stop condition):

- `Domain.lean:35`, inside `TraceNormLtOne`'s docstring: "*see the formalization note on
  `QC_parametrization`*" — the note it points at is being deleted.
- `ShilovBoundary.lean:22`, in the module header: "*see `two_copies_on_boundary` below*" — the
  declaration it points at is being deleted.

Precedent cuts both ways: node 4 left four such mentions as "accepted historical staleness", but
the log has also repeatedly logged stale prose as a defect to be swept later
(`MetCManifold.lean:111` calling `restrict_allowable` "currently a deferred sorry").

**Recommendation: repair both now**, since we are already editing both files and a docstring
pointing at a non-existent declaration is worse than a stale adjective. Make each self-contained
rather than re-pointing at another moving target:

- `Domain.lean:35` → drop the cross-reference and inline the reason: `V` carries no inner product
  here because `QC`'s definition uses a plain `AddCommGroup` (`InnerProductSpace ℝ V` would
  require `NormedAddCommGroup V`).
- `ShilovBoundary.lean:22` → point at the blueprint instead of at Lean: the claim is recorded as
  `\notready` prose at blueprint node `thm:two-copies`.

### D3 — `Domain.lean`'s module docstring. **RULED: rewrite in this commit.**

`Domain.lean:1–9` currently reads "This file formalizes (**as sorry'd placeholders**) the
structural results about QC(V)". This is *already* inaccurate — the file has never contained a
`sorry`; the placeholders are `True`-conclusion theorems — and after this change the sentence is
wholly false, since the only surviving content is `TraceNormLtOne` (the Π(V) fibre) and the
module docstring. **Recommendation: rewrite lines 1–9** to describe what remains and to record
that the four Prop-2.4 / 2.7 / p.15 placeholders were retired to `\notready` blueprint prose on
this date. Flagged because it was not in the discovery brief and would otherwise ship stale.

---

## 3. Per-site restatements

### Site 1 — `QC_parametrization` → `prop:parametrization` (label 255)

**KS claim (KSTeX 220–222).** $Q_{\mathbb C}(V)$ is a fibre bundle over the space of
positive-definite inner products on $V$, with fibre $\Pi(V,g_0)$ over $g_0$; equivalently, after
choosing a reference inner product, $Q_{\mathbb C}(V) \cong \mathrm{GL}(V)\times_{\mathrm O(V)}\Pi(V)$.

**Current Lean.** `Domain.lean` 57–75, declaration at line 71, conclusion `True`.

**Why not statable.** The associated-bundle construction $\mathrm{GL}(V)\times_{\mathrm O(V)}\Pi(V)$
has no usable form in Mathlib, and the statement additionally needs an inner-product-space layer
compatible with `QC`'s plain `AddCommGroup` / `Module ℝ` setup — `InnerProductSpace ℝ V` demands
`NormedAddCommGroup V`. Not statable, hence not `sorry`-able.

**Foundation.** **F2** (associated bundle `GL ×_O` plus the compatible inner-product layer;
`found:homogeneous-bundles`). Build-vs-narrow-axiom to be decided after a Mathlib dig.

**Prose to add** (one sentence, appended to the existing formalization paragraph):
> The missing infrastructure is foundation F2 (`found:homogeneous-bundles`): the
> $\mathrm{GL}(V)/\mathrm O(V)$ homogeneous-space action with associated-bundle machinery,
> together with an inner-product layer compatible with the algebraic setup of `QC`.

### Site 2 — `QC_contractible` → `prop:parametrization` (same node, label 255)

**KS claim (KSTeX 222).** $Q_{\mathbb C}(V)$ is contractible.

**Current Lean.** `Domain.lean` 77–92, declaration at 88, conclusion `True`.

**Why not statable.** `QC V` carries no topology, so `ContractibleSpace (QC V)` — or the explicit
homotopy form — cannot be written at all.

**Foundation.** **F1** (topology on `QC(V)`). Note for the F1 build, not for this pass: Mathlib
does not endow a bare finite-dimensional `Module ℝ V` with a topology, so "induced along `toForm`
from the form space" presupposes a topology on the form space that must itself be constructed
(basis pullback plus basis-independence). This is the same bare-module-versus-normed friction
recorded for site 1, and the reason F1 warrants a read-only probe before it is treated as a
few-line warm-up. A conditional theorem taking topology binders is the clean fallback.

**Prose to add:**
> The missing infrastructure is foundation F1: a topology on $Q_{\mathbb C}(V)$, which
> contractibility needs even to be stated. F1 is currently bundled inside
> `found:homogeneous-bundles`; it separates out when that node is split.

### Site 3 — `QC_domain_of_holomorphy` → `prop:domain-holomorphy` (label 356)

**KS claim (KSTeX 271; proof 275–277).** $Q_{\mathbb C}(V)$ is holomorphically convex — a domain
of holomorphy in $S^2(V^*_{\mathbb C})$. KS prove it by realising $Q_{\mathbb C}(V)$ as the
intersection of $\prod_{0\le p\le d/2}\mathcal U(\Lambda^p V)$ with the affine variety embedding
$S^2(V^*_{\mathbb C})$.

**Current Lean.** `Domain.lean` 96–111, declaration at 107, conclusion `True`. Orphaned section
header at line 94.

**Why not statable.** Needs a complex structure on the form space, the domain-of-holomorphy /
Stein predicate, and Siegel domains. Mathlib provides none of the three.

**Foundation.** **F3** (`found:scv-tube-domain`). The existing statement `\uses` edge already
points there; the proof block's `\uses{def:allowable-hodge}` is also already correct, since the
per-degree induced forms that the embedding needs are built.

**Prose to add:**
> The missing infrastructure is foundation F3 (`found:scv-tube-domain`): a complex structure on
> the space of forms, the Stein / domain-of-holomorphy predicate, and Siegel domains. Per the
> project's axiomatize-versus-prove rule, the deep classical theorems there are background to be
> axiomatized, while "$Q_{\mathbb C}(V)$ is Stein" remains a proof obligation.

### Site 4 — `QC_two_dim_polydisc` → `prop:two-dim-polydisc` (label 505)

**KS claim (KSTeX 284–294).** For $\dim V = 2$ the matrix $(\det g)^{-1/2}g$ depends only on the
conformal structure and decouples from the volume element (288); a nondegenerate complex inner
product is determined up to scale by its two null directions in $\mathbb P(V_{\mathbb C})$, and
allowability places one in each open hemisphere cut out by the real equator $\mathbb P(V)$ (290);
each off-equator point is a complex structure on $V$, the two hemispheres giving the two
orientations (292); hence $Q_{\mathbb C}(V)$ is a 3-dimensional polydisc — one disc per complex
structure, one for the volume element (294).

**Current Lean.** `Domain.lean` 115–130 (130 = EOF), declaration at 126, conclusion `True`.
Orphaned section header at line 113.

**Why not statable.** Needs the polydisc as a bounded complex domain, a complex structure on
$Q_{\mathbb C}(V)$, the projective geometry of $\mathbb P(V_{\mathbb C})$, and the
conformal/volume decoupling.

**Foundation.** See **D1**: F1 + F3 + a small in-repo projective/conformal piece that is in none
of F1–F4.

**Prose to add:**
> The missing infrastructure is foundation F1 (a topology and complex structure on
> $Q_{\mathbb C}(V)$) together with foundation F3 (`found:scv-tube-domain`, for the polydisc as a
> bounded domain), plus one piece belonging to neither: the projective geometry of
> $\mathbb P(V_{\mathbb C})$ and the $(\det g)^{-1/2}g$ conformal/volume decoupling, which is a
> small in-repo build rather than a Mathlib gap.

### Site 5 — `two_copies_on_boundary` → `thm:two-copies` (label 473)

**KS claim (KSTeX 166).** The Shilov boundary of $Q_{\mathbb C}(V)$ — taken as a bounded domain
in the affine variety of the Prop-2.7 proof — contains two disjoint copies of the space of
Lorentzian metrics on $V$, since an eigenvalue may approach the negative real axis from either
side; complex conjugation interchanges the copies; and with orientation-reversing elements of
$\mathrm{GL}(V)$ acting antilinearly on the orientation line, the nondegenerate Shilov-boundary
points are the *time-oriented* Lorentzian metrics.

**Current Lean.** `ShilovBoundary.lean` 618–660 (660 = EOF), declaration at 655, conclusion
`True`. No dedicated section header (the line-51 header covers the whole section and stays).

**Why not statable.** The subject is the Shilov boundary of the *bounded* realization; in the
naive closure inside $S^2(V^*_{\mathbb C})$ the two copies coincide, so no statement about
subsets of the form space can express the disjointness. The existing docstring already records
this correctly, and correctly rejects the expressible-but-wrong-subject stand-in (the closure of
the graph $\{(g,\sqrt{\det g})\}$) under the no-approximations policy.

**Foundation — this is the second scoping correction to the brief.** The node currently
`\uses{found:hodge-star, found:scv-tube-domain}`, and both the docstring and the brief attribute
item (1) to missing "exterior-power induced forms". **That attribution is wrong.**
`HodgeScaffold.lean` already provides, at arbitrary degree `p`: `inducedForm` with
`inducedForm_apply_ιMulti` / `_nondegenerate` / `_isSymm`; the complex `formC g p` with the same
three; `formC_realExtPow_diag`; `star_g` and `star_g_star_g`; `starOp_starOp`, `star_blade`,
`gram_blade_diag`, `gram_ιMulti_diag`; and `detGramReal` / `detSqrtReal` for the $p = 0$ branch
$(\det g)^{1/2}$. `IsAllowableHodge` is literally `∀ (p : ℕ) (α : ⋀[ℝ]^p V), …`, so the
all-degree induced forms are load-bearing for the already-dark-green `thm:angle-equiv`, and
`found:hodge-star` is `\leanok` on that basis.

What is genuinely missing for this site is therefore **F3 only**: the *target* of the embedding
— $\prod_{0\le p\le d/2}\mathcal U(\Lambda^p V)$ as a product of Siegel domains — the Cayley
transform / bounded realization, and the Shilov-boundary notion. The per-degree forms are the
map's components and exist; the codomain does not.

One question this leaves open, to settle at the F3 step rather than here: whether the remaining
gap is instead the **covector** side $\Lambda^p(V^*)$. The Run-6a record shows route (R1), the
vector side with real-coframe normalization, was built and route (R2), verbatim-covector, was
not. If the two-copies argument needs (R2), that is a genuine additional build — but it is a
vector-versus-covector question, not a question of degrees.

**Prose to add** (replacing item (1)'s attribution, keeping items (2) and (3)):
> Item (1) is not a missing exterior-algebra layer: the induced forms on $\Lambda^p$ at every
> degree, the Hodge star, and the $p = 0$ branch $(\det g)^{1/2}$ are built in
> `ComplexMetrics/HodgeScaffold.lean` (`found:hodge-star`, `\leanok`) and are load-bearing for
> Theorem 2.2. What is missing is the *codomain* of the embedding: the product of Siegel domains
> $\prod_{0\le p\le d/2}\mathcal U(\Lambda^p V)$, the Cayley transform giving the bounded
> realization, and the Shilov-boundary notion itself — all foundation F3
> (`found:scv-tube-domain`).

---

## 4. Exact edit inventory

Line numbers are as of `2033bf7`. **Delete from the bottom up** so earlier numbers stay valid.

**`KontsevichSegal/ComplexMetrics/ShilovBoundary.lean`**
1. Delete 618–660 (`two_copies_on_boundary` with its doc comment; 660 is EOF). Keep the line-51
   section header. Ensure the file still ends with a newline after the truncation.
2. Repair the header cross-reference at line 22 (D2).

**`KontsevichSegal/ComplexMetrics/Domain.lean`**
3. Delete 113–130 (header + `QC_two_dim_polydisc`; 130 is EOF).
4. Delete 94–111 (header + `QC_domain_of_holomorphy`).
5. Delete 55–92 (the joint Prop-2.4 header + `QC_parametrization` + `QC_contractible`).
   Steps 3–5 remove everything from line 55 to EOF; what remains is the module docstring, the
   import, the Π(V) section and `TraceNormLtOne`.
6. Repair the `TraceNormLtOne` docstring cross-reference at line 35 (D2).
7. Rewrite the module docstring, lines 1–9 (D3).

**`blueprint/src/content.tex`** — delete four whole lines, bottom-up: 506, 474, 357, 256. Each
line contains only a `\lean{}` macro (verified verbatim in discovery item C); no other line in
`blueprint/src/` mentions any of the five names. Then add the per-node sentences from section 3
above. Node `\notready` markings, `\uses` lists and proof environments are **left untouched**.

**Not touched:** `blueprint/src/section5.tex`, `foundations.tex`, any `KontsevichSegal/**` file
other than the two above, `All.lean` and `KontsevichSegal.lean` (no file added or removed, so
`mk_all` is a no-op and the CI `mk_all-check` is unaffected).

**Regenerated, not hand-edited:** `blueprint/lean_decls` (133 → 128 names; the five appear as bare
unqualified entries at lines 9, 10, 14, 18, 19 — note the file is CRLF and ends without a
trailing newline, so strip `\r` before matching and do not "fix" the missing newline) and
`blueprint/web/dep_graph_document.html`.

**Staging:** read the set off `git status` output at the time of the commit. Do not stage from any
list above — including this one. `blueprint/web/` holds 22 tracked files, not one; `blueprint/print/*`
(7 files, including `print.pdf`) is tracked and is standing regen noise to leave dirty;
`blueprint/lean_decls` is tracked despite appearing in `.gitignore`; `docs/project_status.md` is
ignored and untracked and must never be staged.

---

## 5. Verification order

1. `lake build` — green, 0 sorry warnings.
2. Grep gate: `rg -e 'True := by' -e ': True\b'` over `*.lean` → **NONE FOUND** for the first
   pattern; the second previously matched only the placeholder's own comment at
   `ShilovBoundary.lean:657`, which is deleted with the block, so it too should now report NONE
   FOUND. `axiom` 0. Real `sorry` 0.
3. `leanblueprint web`, then `lake exe checkdecls blueprint/lean_decls` → clean.
4. Graph **parse-diff** (node→fillcolor map plus sorted edge set — never a byte-diff) against the
   committed graph → **EMPTY**. Nodes 57, edges 85, dark green 7, fill census 7/1/15/2.
5. `lean_decls` audit by NAMES: 133 → 128; confirm exactly the five bare names disappeared and no
   other name changed. The single legitimate duplicate (`WickRotation.HilbertCompletion`) stands.
6. Read `git status`, resolve the staging set from it, then hand over for commit.

## 6. What this pass does *not* claim

The blueprint becomes honest in the sense that no Lean declaration any longer credentials a claim
it does not state. It does not make any of the four claims true, statable, or closer to proved.
`sorry` stays at 0 here; the honest rise in `sorry` begins when F1 lands and site 2's prose
becomes a real statement.
