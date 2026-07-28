# Restatement proposal: `lem:convex-cone` (node 3/5)

**Status: PROPOSAL for human review. Nothing applied — no `.lean` or `.tex` edited, no marker
flipped, no build or regen run.** Audit provenance: Pass 1-A, verdict **OVERSTATED /
statement-partial** — the blueprint node claims three things, the Lean proves only the third.
This is the batch's first **ADD-CONTENT** restatement (nodes 1-2 were deletions): the fix is
(i) NARROW the node to what is proved (it stays dark-green) and (ii) SPLIT the unproved
content into a new `\notready` node so no claim is lost. It is also the first fix that
**changes the graph edge set** — the exact expected delta is predicted below so the edit gate
can check for THOSE edges and only those.

---

## KS claim (quoted, 3 clauses)

`docs/KSTeX.tex:160-162` (immediately after the Theorem 2.2 proof; verbatim):

> Another consequence of (4) is that
> $$\max \arg \lambda_i \ - \ \min \arg \lambda_i \ < \ \pi,$$
> which shows that when $v$ runs through $V$ the complex numbers $g(v)$ form a closed convex
> cone in $\mathbb C$ disjoint from the open negative real axis. In particular, $g(v)$ can
> never be real and negative.

* **Clause A** — the arg-spread bound $\max_i \arg\lambda_i - \min_i \arg\lambda_i < \pi$
  (a consequence of the angle condition (4)).
* **Clause B** — $g(V)$ is a **closed convex cone** in $\mathbb C$ **disjoint from the open
  negative real axis**.
* **Clause C** — "in particular", $g(v)$ is never real and negative. **← the only clause
  proved in Lean.**

---

## Current blueprint statement + Lean (verbatim)

Blueprint block, `blueprint/src/content.tex:139-160` (statement `\leanok` AND proof `\leanok`
— the node is one of the 7 dark-greens, confirmed from the committed graph:
`NODE lem:convex-cone fill=#1CAC78 border=green`):

```latex
\begin{lemma}[Values form a convex cone; KS p.~9]
  \label{lem:convex-cone}
  \lean{not_neg_real_axis}
  \leanok
  \uses{def:allowable}
  For $g \in Q_{\mathbb C}(V)$ one has
  $\max_i \arg \lambda_i - \min_i \arg \lambda_i < \pi$, so as $v$ runs
  through $V$ the values $g(v)$ form a closed convex cone in $\mathbb C$
  disjoint from the open negative real axis. In particular $g(v)$ is never
  real and negative.
\end{lemma}

\begin{proof}
  \leanok
  \uses{def:allowable}
  From (4), if $\arg \lambda_j > 0 > \arg \lambda_k$ then
  $\arg \lambda_j - \arg \lambda_k \leq \sum_i |\arg \lambda_i| < \pi$;
  hence all values $\lambda_i y_i^2$ lie in a closed convex cone of opening
  angle less than $\pi$, which contains no two opposite rays and avoids the
  open negative real axis. Nonnegative combinations stay in the cone.
\end{proof}
```

So the current prose asserts **all three clauses A + B + C**, and even the proof block's prose
argues via the cone (clause-B reasoning).

The Lean, `KontsevichSegal/ComplexMetrics/Defs.lean:95-98` (signature; the full proof runs to
~line 175, sorry-free — project-wide sorry = 0 re-verified this session by grep and by a green
`lake build`):

```lean
lemma not_neg_real_axis {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (g : AllowableComplexMetric V)
    (v : V) (hv : v ≠ 0) :
    ¬ ((g.toForm v v).im = 0 ∧ (g.toForm v v).re < 0) := by
  ...
```

**Exact type, in symbols:** for $v \neq 0$,
$\neg(\operatorname{Im} g(v,v) = 0 \wedge \operatorname{Re} g(v,v) < 0)$ — i.e. $g(v)$ does
not lie on the **open negative real axis**. That is clause C (with a nonzero-$v$ hypothesis;
see the sliver note below) and nothing more: no arg-spread bound, no cone, no closedness, no
convexity appears in the statement.

**Shape of the Lean proof** (relevant to the narrowed proof sketch): diagonalize; condition
(4) puts all $\arg\lambda_i$ in an arc $[-Q, N]$ with $N + Q < \pi$ containing $0$; take the
arc midpoint $\varphi = (N-Q)/2$; the functional $z \mapsto \operatorname{Re}(e^{-i\varphi}z)$
is strictly positive on every eigenvalue, hence on $g(v) = \sum_i \lambda_i y_i^2$ for
$v \neq 0$, while a real negative $z$ has $\operatorname{Re}(e^{-i\varphi}z) = z\cos\varphi <
0$. (The separating-line half of the cone picture, used directly — the cone itself is never
constructed.)

### Consumers (1d, every hit)

* Blueprint `grep -rn 'convex-cone' blueprint/src/`:
  `content.tex:140` (the `\label` itself); `content.tex:400` — **`prop:lorentzian-boundary`**
  (label at `content.tex:388`), whose PROOF has `\uses{def:allowable, lem:convex-cone}`;
  `content.tex:405` — that proof's prose: "That $\varphi$ itself is not allowable follows from
  Lemma~\ref{lem:convex-cone}: $\varphi$ takes a real negative value on the timelike basis
  vector." (web.paux is a binary render artifact.)
* Lean `grep -rn 'not_neg_real_axis' KontsevichSegal/`:
  `Defs.lean:95` (the declaration); `ShilovBoundary.lean:278` — the one real consumer, inside
  `lorentzian_on_boundary` (ShilovBoundary.lean:70): `not_neg_real_axis g (b i₀) (b.ne_zero
  i₀) ⟨_, _⟩` showing a Lorentzian metric takes a real negative value on the timelike basis
  vector, hence is not allowable; `EigenvalueMinmax.lean:133` and `ShilovBoundary.lean:66`
  (comments only).
* **Both consumers use clause C only** — the "real negative value on the timelike vector"
  argument. Nothing consumes A or B. **No consumer re-pointing is needed.**
* No Lean decl proves A or B: the repo-wide grep for arg-spread/convex/cone surfaces only
  unrelated hits (QC(V)-convexity prose in `Domain.lean` — a different claim, Prop 2.4's
  contractibility context; category-theoretic cones in `NuclearFrechet.lean`; light-cones in
  the Minkowski files). Confirms the audit.

---

## The gap (audit finding)

The blueprint prose asserts **A + B + C**; `not_neg_real_axis` proves **only C** (for nonzero
$v$). The statement-`\leanok` (and the dark-green rendering) therefore covers a sub-claim: a
faithful, complete, sorry-free proof of C sits under a statement that also claims A and B.
Nothing is WRONG — C is genuinely proved, and A/B are true KS claims — the defect is partial
coverage presented as full. Fix = narrow + split, not delete or demote.

---

## Part (i): narrowed `lem:convex-cone`

Proposed narrowed block, matching `not_neg_real_axis` symbol for symbol (title changes; the
`\label` stays — see Open question 2):

```latex
\begin{lemma}[Values avoid the negative real axis; KS p.~9]
  \label{lem:convex-cone}
  \lean{not_neg_real_axis}
  \leanok
  \uses{def:allowable}
  For $g \in Q_{\mathbb C}(V)$ and every nonzero $v \in V$ the value $g(v)$
  is never real and negative: it does not lie on the open negative real
  axis, that is, not both $\mathrm{Im}\, g(v) = 0$ and $\mathrm{Re}\, g(v) < 0$.
\end{lemma}

\begin{proof}
  \leanok
  \uses{def:allowable}
  In a diagonalizing basis, condition (4) puts all the arguments
  $\arg \lambda_i$ in an arc $[-Q, N]$ of width $N + Q < \pi$ containing
  $0$. Let $\varphi = (N - Q)/2$ be the arc's midpoint; then
  $|\varphi| < \pi/2$ and $|\arg \lambda_i - \varphi| < \pi/2$ for every
  $i$, so the linear functional $z \mapsto \mathrm{Re}(e^{-\mathrm i \varphi} z)$
  is strictly positive on every $\lambda_i$, hence strictly positive on
  $g(v) = \sum_i \lambda_i y_i^2$ when $v \neq 0$. A real negative value
  $z$ has $\mathrm{Re}(e^{-\mathrm i \varphi} z) = z \cos \varphi < 0$, so
  $g(v)$ is not one.
\end{proof}
```

**CRITICAL FIDELITY CHECK — residual gap between narrowed prose and the Lean:**

* No cone/closed/convex language survives; the statement is exactly the
  open-negative-axis exclusion. ✓
* The nonzero hypothesis is stated ("every nonzero $v \in V$"), matching `hv : v ≠ 0`
  exactly. KS's own sentence has no such restriction — but at $v = 0$ the value is $0$,
  which is not on the OPEN negative axis, so the all-$v$ claim exceeds the Lean by only that
  trivial case. The narrowed prose deliberately keeps the restriction rather than claim the
  (trivial) sliver the Lean does not prove. Flagged as Open question 4 — this is the one
  judgment call in part (i).
* The proof sketch is REWRITTEN to match the Lean proof's actual route (arc midpoint +
  separating functional, `Defs.lean:105-175`) — the current proof prose argues via the cone
  (clause B), which the Lean never constructs; leaving it would smuggle B back in through the
  proof block. The cone-flavored sketch moves to the new node, where it belongs.
* Both `\leanok`s retained: the statement is now exactly what `not_neg_real_axis` states, and
  its proof is complete and sorry-free (green build; project sorry = 0). Node stays
  dark-green.
* `\uses{def:allowable}` unchanged (both statement and proof) — narrowing removes claims, not
  dependencies; C needs only the angle condition, which is `def:allowable` (the working
  definition). No change to what it uses.

---

## Part (ii): the NEW node for clauses A + B

Proposed new block, placed in `blueprint/src/content.tex` immediately AFTER the narrowed
`lem:convex-cone`'s proof block (adjacent, before `lem:volume-element`):

```latex
\begin{lemma}[Values form a convex cone; KS p.~9]
  \label{lem:convex-cone-geometry}
  \notready
  \uses{def:allowable}
  For $g \in Q_{\mathbb C}(V)$ one has
  $\max_i \arg \lambda_i - \min_i \arg \lambda_i < \pi$, a consequence of
  condition (4); consequently, as $v$ runs through $V$, the values $g(v)$
  form a closed convex cone in $\mathbb C$ disjoint from the open negative
  real axis. Lemma~\ref{lem:convex-cone} is the ``in particular'' of this
  statement.
\end{lemma}

\begin{proof}
  \uses{def:allowable}
  From (4), if $\arg \lambda_j > 0 > \arg \lambda_k$ then
  $\arg \lambda_j - \arg \lambda_k \leq \sum_i |\arg \lambda_i| < \pi$,
  which is the spread bound. Hence all values $\lambda_i y_i^2$ lie in a
  closed convex cone of opening angle less than $\pi$, which contains no
  two opposite rays and avoids the open negative real axis; nonnegative
  combinations stay in the cone.
\end{proof}
```

* **Label:** `lem:convex-cone-geometry` (recommended; alternative `prop:arg-spread-cone`).
  Grep confirms neither exists — no collision. The new node inherits the OLD title ("Values
  form a convex cone") since it now carries that content.
* **Marking:** `\notready`, no `\leanok` anywhere (statement unproved in Lean; the proof block
  is KS's sketch, prose only — this is the standard shape for unproved nodes).
* **`\lean`:** NONE — no declaration proves A or B (grep-confirmed above); annotating would
  repeat the original bug. Consistent with the node-2 drop precedent and the bare-`\notready`
  G3 nodes.
* **`\uses{def:allowable}`:** KS derive A "as a consequence of (4)", and (4) IS the working
  definition `def:allowable` — the same dependency the current node has. `thm:angle-equiv` is
  NOT needed: it relates the angle condition to Definition 2.1's Hodge-star form and plays no
  role in A or B (Open question 3).
* **No consumer re-pointing:** both consumers of the old node use clause C only (see 1d), so
  `prop:lorentzian-boundary` keeps `\uses{lem:convex-cone}` unchanged and nothing points at
  the new node yet.
* The cross-reference `Lemma~\ref{lem:convex-cone}` is a `\ref`, not a `\uses` — it renders as
  text and creates NO graph edge (deliberate: the Lean proof of C does not pass through B, so
  a dependency edge in either direction would misrepresent; Open question 5).

---

## Graph-edge prediction (FIRST fix that changes the edge set)

Current committed baseline (parsed from the graph after node 2/5): **56 nodes, 84 edges,
dark-green #1CAC78 = 7, orange-border = 30, no-fill = 30, #B0ECA3 = 16, acyclic.**

Predicted delta — the edit gate should confirm EXACTLY this and nothing else:

* **Nodes: 56 → 57** (+ `lem:convex-cone-geometry`).
* **Edges: 84 → 85.** Exactly ONE new edge: `def:allowable -> lem:convex-cone-geometry`
  (statement-`\uses` and proof-`\uses` name the same node, merging to one edge, as with the
  existing pattern). ZERO removed edges: `def:allowable -> lem:convex-cone` and
  `lem:convex-cone -> prop:lorentzian-boundary` both stay (no consumer re-point, `\uses`
  lists of existing nodes untouched). Transitive-reduction check: the new node has one
  in-edge and no out-edges, so it creates no new paths and reduction can neither drop the
  new edge nor any existing one.
* **Fills/borders:** narrowed `lem:convex-cone` STAYS `#1CAC78`/green (statement+proof
  `\leanok` retained, ancestry unchanged); new node = no-fill/`#FFAA33` border (`\notready`).
  Dark-green count **7 → 7**. Orange-border 30 → 31; no-fill 30 → 31; all other tallies
  unchanged (#B0ECA3 16, #9CEC8B 1, #ECECEC 2). Acyclic stays (the one new edge points from
  an existing node into a sink).

"Edges changed" is EXPECTED here — the gate condition is that the delta is exactly the above.

---

## Fidelity check

* **(a)** The narrowed `lem:convex-cone` states exactly clause C as `not_neg_real_axis`
  proves it — same quantification (nonzero $v$), same conclusion
  ($\neg(\mathrm{Im}=0 \wedge \mathrm{Re}<0)$ = not on the open negative axis), no cone
  residue, proof sketch matching the actual Lean route. The one sliver (KS's implicit
  $v = 0$ case, trivially true, not in the Lean) is EXCLUDED from the prose rather than
  claimed — the conservative direction. No overclaim remains.
* **(b)** The new node states A + B in KS's own words (spread bound as a consequence of (4);
  closed convex cone disjoint from the open negative axis) and is honestly `\notready` with
  no `\lean` — nothing in the repo proves any part of it.
* **(c)** Coverage: A and B live in the new node; C lives in the narrowed node; the "in
  particular" relation is kept as prose. Every clause of KS's sentence is stated somewhere
  with an honest marker — nothing is lost by the split.

---

## Build implications

**Blueprint-text-only.** The fix touches `blueprint/src/content.tex` and nothing else, then
regenerates the web graph:

* NO `.lean` change — `not_neg_real_axis` and both its consumers are untouched.
* `lake build` NOT required (nothing Lean changed); running it anyway is a cheap no-op gate.
* `blueprint/lean_decls` UNCHANGED (132 lines): the narrowed node keeps
  `\lean{not_neg_real_axis}` (which exists), the new node adds no `\lean` name. Therefore
  `lake exe checkdecls` is unaffected (expect pass, and it's cheap to run as confirmation).
* Regen surface: `leanblueprint web` only; the commit = content.tex +
  dep_graph_document.html + this artifact.
* Net: node 3 is LOWER-risk than nodes 1-2 despite being "add content" — closer to the two
  queued blueprint-text-only fixes than to the Lean surgeries.

---

## Proposed post-fix markings

* `lem:convex-cone` (narrowed): statement-`\leanok` AND proof-`\leanok` RETAINED —
  dark-green. Faithful-rule reasoning: after narrowing, the statement is exactly the proved
  Lean lemma, and the proof is complete and sorry-free; this is precisely the state
  dark-green is supposed to certify. (Unlike the demotion batch: there the statements
  underspecified structures with unproved content; here the narrowed statement and its proof
  are both fully covered.)
* `lem:convex-cone-geometry` (new): `\notready` — faithful statement of unproved content with
  no Lean declaration; the definition of that marker.

---

## Open questions for human review

1. **Label for the new node:** `lem:convex-cone-geometry` (recommended) vs
   `prop:arg-spread-cone` — both free of collisions. Also lemma-vs-proposition environment
   (KS present it as a remark-consequence; `lemma` recommended for parallelism).
2. **Keep `\label{lem:convex-cone}` on the narrowed node?** Recommended KEEP (title changes to
   "Values avoid the negative real axis", label stays): renaming the label would touch
   `prop:lorentzian-boundary`'s proof `\uses` and the `\ref` at content.tex:405 for zero
   semantic gain. The cost: the label reads "convex-cone" on a node that no longer claims the
   cone — cosmetic misnomer, flagged for your call.
3. **`\uses` of the new node:** `def:allowable` only (recommended — condition (4) IS the
   working definition), or additionally `thm:angle-equiv`? My reading: A is derived from (4)
   directly; `thm:angle-equiv` is about the equivalence with Definition 2.1 and is not used.
4. **The $v = 0$ sliver:** the narrowed prose restricts to nonzero $v$ (matching `hv : v ≠ 0`
   exactly); KS's sentence has no restriction, and at $v = 0$ the claim is trivially true
   ($g(0) = 0$ is not on the OPEN negative axis). Alternatives: (α) as proposed — match the
   Lean exactly (recommended; conservative); (β) state for all $v$ and accept a trivial
   unproved sliver (rejected — the same overstatement bug in miniature); (γ) strengthen the
   Lean lemma to all $v$ (a 3-line case split) and state for all $v$ — the only option that
   both matches KS verbatim and keeps zero sliver, but it touches Lean and turns a
   blueprint-only fix into a Lean fix. I recommend (α) now, (γ) opportunistically later.
5. **No edge between the two nodes** (recommended): the Lean proof of C does not pass through
   B, and B's statement does not depend on C, so the `\ref` stays prose-only. Alternative: a
   proof-`\uses{lem:convex-cone-geometry}` edge on the narrowed node would mirror KS's "in
   particular" derivation — but it would claim the Lean proof routes through the cone, which
   it does not, and would hang a dark-green node's proof on an orange ancestor. Confirm the
   no-edge choice.
6. **Proof-`\leanok` earned:** `not_neg_real_axis` is sorry-free (project sorry = 0 by grep +
   green build this session) and proves exactly the narrowed statement; the rewritten proof
   sketch mirrors its actual argument. Confirm you're satisfied the sketch matches (the old
   sketch argued via the cone and is being moved out).
7. **Consumer re-pointing:** none proposed — `prop:lorentzian-boundary` (blueprint) and
   `lorentzian_on_boundary` (Lean) both consume clause C only. Confirm.
