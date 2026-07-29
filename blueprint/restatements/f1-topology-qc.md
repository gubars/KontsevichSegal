# F1 — a topology on $Q_{\mathbb C}(V)$: reviewed statements

**Status: RULINGS RECORDED 2026-07-29 — D1 split, D2/D3/D4 as recommended. No repo file has been edited yet.**
Target path when approved: `blueprint/restatements/f1-topology-qc.md` (git-tracked; commit with
the F1 edit, per convention (d)).
Verified against `origin/main` at `d1d9bfc`. Probe outputs: `_scratch/f1_probe1.lean`,
`_scratch/f1_probe2.lean`, `/tmp/f1_probe_summary.txt`, `/tmp/f1_mathlib.txt`.

---

## 1. What the probe established

The phase brief scopes F1 as "a `TopologicalSpace` instance induced via `toForm` from the
finite-dim form space. Mathlib FULLY provides the ingredients … only the in-repo instance is
unwritten. SMALLEST — a few lines." Three corrections.

**Correction A — the premise is false; the outline is right.** No instance gives a bare
finite-dimensional real module a topology, and `TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)` does not
synthesize under `QC`'s binders (probe Q1, Q2). So there is nothing to induce *from*: the form
space must be **given** a topology, not found carrying one. `FiniteDimensional ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)`
*does* synthesize, which is what makes the canonical choice available. Real size: **SMALL**, not a
few lines.

**Correction B — "unlocks site 2" is half-right; it unlocks the statement, not the proof.**
$Q_{\mathbb C}(V)$ is **not convex**, so `Convex.contractibleSpace` does not apply to it
directly. Witness at $d = 1$: with $V = \mathbb R$ a complex metric is $g(v,w) = \lambda vw$, and
allowability reduces to $\lambda \neq 0$ with $|\arg\lambda| < \pi$, i.e. the allowable set is
$\mathbb C \setminus (-\infty, 0]$. Take $\lambda_1 = -1 + \varepsilon i$ and
$\lambda_2 = -1 - \varepsilon i$: both allowable, midpoint $-1$ excluded. Convexity lives in the
**fibres** $\Pi(V,g_0)$, and reaching them is the bundle decomposition — Prop 2.4, i.e. **F2**.
KS's own proof goes that way. (Note for a future session: at $d = 1$ the set *is* star-convex
about $1$, so a $d = 1$ special case is separately provable; whether star-convexity or a direct
homotopy works in general is unexplored, and is **not** what KS prove. Do not spend a session on
the convex route for general $d$ without settling that first.)

**Correction C — my error in the probe prompt, recorded so it isn't repeated.** The Q5 binders I
prescribed (`[TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]`) were on the
wrong object: a topology on $V$ induces nothing on $V \to_{\ell} V \to_{\ell} \mathbb C$. The
binders belong on the form space.

**A correction to the probe's own verdict.** Q5 reports the minimal elaborating binder set as
`[TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)]` alone. That is minimal-to-**elaborate**, not
minimal-to-be-**true**: give the form space the discrete topology and $Q_{\mathbb C}(V)$ inherits
a discrete topology on more than one point, which is not contractible. A conditional theorem over
that binder alone would be a *false* theorem. An honest conditional must carry `ContinuousAdd` and
`ContinuousSMul ℝ`; and once `T2Space` is added alongside the `FiniteDimensional` already present,
`isModuleTopologyOfFiniteDimensional` pins the topology to the module topology regardless. **So
the conditional-theorem route, done honestly, collapses into the `moduleTopology` route.** This is
the same minimal-to-elaborate versus minimal-to-be-true gap the vacuity audits kept finding.

---

## 2. Decision: `moduleTopology`, induced along `toForm`

Give the form space `moduleTopology ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)` — **scoped** (`letI` or a scoped
instance), never a global instance on a generic `LinearMap` type — and give
`AllowableComplexMetric V` the topology induced along `toForm`.

**Why this is *the* topology and not *a* topology** (the float-free / non-vacuity obligation).
`moduleTopology` is canonical and basis-free, so no choice is made and no independence proof is
owed. `isModuleTopologyOfFiniteDimensional` then supplies faithfulness: over a complete
nontrivially-normed field, on a finite-dimensional space, **any** T2 TVS topology *is* the module
topology. Since `FiniteDimensional ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)` synthesizes (probe Q2), every
reasonable alternative agrees with this one. `ContinuousAdd` and `ContinuousSMul` for the module
topology are pre-proven in Mathlib (`ModuleTopology.continuousAdd` / `continuousSMul`), which is
exactly what `Convex.contractibleSpace` will want later at the fibre level.

**Rejected alternatives.**
- *Basis transfer* via `Module.Basis.equivFun` and a Pi topology: owes a basis-independence
  proof, and no Mathlib lemma supplies one (probe Q3c). Strictly more assuming.
- *Permanent extra topology binders* on every `QC` statement: changes the object under study,
  and as shown above the honest binder set collapses to `moduleTopology` anyway.
- *A normed structure on $V$*: excluded. `QC`'s binders are plain `AddCommGroup` / `Module ℝ`, and
  `NormedAddCommGroup` incompatibility is precisely what blocked `QC_parametrization`.

---

## 3. Statements to add

### S1 — `AllowableComplexMetric.toForm_injective`. PROVABLE, no `sorry`.

> `Function.Injective (AllowableComplexMetric.toForm : AllowableComplexMetric V → (V →ₗ[ℝ] V →ₗ[ℝ] ℂ))`

Provable because, verified at `d1d9bfc`: `AngleCondition` is declared `: Prop`, and all three
non-`toForm` fields are Prop-valued — `symmetric' : ∀ v w, toForm v w = toForm w v`,
`nondegenerate : ∀ v, v ≠ 0 → ∃ w, toForm v w ≠ 0`, and
`angle_cond : ∃ b eig, AngleCondition eig ∧ ∀ v, …`. Two structures with equal `toForm` are
therefore equal by cases plus proof irrelevance. No `@[ext]` lemma currently exists; add one
alongside if it makes the proof cleaner.

**Load-bearing, not decorative.** Without injectivity the map `toForm` is not an embedding, and
"$Q_{\mathbb C}(V)$ is contractible" would be a claim about a quotient-like image rather than
about $Q_{\mathbb C}(V)$ itself. This is the statement that makes the induced topology the right
one.

### S2 — the topology (a `def` / scoped instance, not a theorem)

The induced topology of §2. Not a proposition; nothing to prove beyond what Mathlib supplies.
Record in its docstring: the module topology is canonical, and
`isModuleTopologyOfFiniteDimensional` is why any T2 alternative agrees.

### S3 — `QC_contractible` as a real statement plus a tracked `sorry`

**KS pin.** KSTeX 220–222: the fibre-bundle statement at 220–221, and "In particular,
$Q_{\mathbb C}(V)$ is contractible." at 222.

> `ContractibleSpace (QC V)` — under the S2 topology.

The probe confirmed that `[TopologicalSpace (AllowableComplexMetric V)] → ContractibleSpace
(AllowableComplexMetric V)` elaborates, so with S2 supplying the instance the bare form
elaborates.

**Why this `sorry` is honest** — the three conditions, all of which the retired placeholders
failed:
1. **Statable** — S2 supplies the topology, S1 makes it faithful.
2. **True** — KS prove it (Prop 2.4: a fibre bundle with contractible fibres $\Pi(V,g_0)$ over a
   contractible base).
3. **Not provable with current infrastructure** — the proof routes through the bundle
   decomposition, i.e. F2, and $Q_{\mathbb C}(V)$ is not itself convex (Correction B).

That is exactly what a `sorry` asserts: true, proof deferred. Contrast the two shapes already on
record — the five retired `True` placeholders were **not statable**, and node 2's $V_k$ claim was
statable but **false**. This is the first case in the project that is statable *and* true *and*
unproved.

**This is the honest-`sorry` milestone.** `sorry` goes 0 → 1. The "`sorry` = 0" invariant retires
here and is replaced by "`sorry` tracked, each under a real pinned statement" (the advisor-repo
convention, which runs 53 tracked sorrys). Recording it as planned, not as slippage.

---

## 4. Blueprint consequences — two decisions

> **D1 RULED: SPLIT.** **D2 RULED: amend text, defer the node split to F2.**
> **D3 RULED: extend `Domain.lean`.** **D4 RULED: prose only, with the $d=1$ witness recorded.**

**D1 — split `prop:parametrization`?** The node covers both Prop 2.4's parametrization *and* its
contractibility corollary, and after F1 those have different status: contractibility becomes
statable, parametrization stays unstatable (it still needs F2's associated bundle plus the
inner-product layer). Under the locked statement-complete convention, `\leanok` asserts the
statement is faithfully formalized — which would be true of half this node and false of the other
half.

**RULED — split**, into `prop:parametrization` (stays `\notready`, F2) and a new
`prop:contractibility` (statement-`\leanok`, `\lean{QC_contractible}`, proof `\notready`). This is
the `lem:convex-cone` precedent — narrow and split when a node's parts have different status —
and it is the only way the graph shows the truth. Node count 57 → 58 with a predicted edge delta
that must be stated exactly before the edit and matched after; an edge change is otherwise a stop
condition. The alternative is (a) keep one `\notready` node and add `\lean{QC_contractible}` as
statement-linked orange, the `found:rigged-triple` precedent — less informative but zero graph
risk.

**D2 — split `found:homogeneous-bundles` now?** F1 is currently bundled inside it ("the
$\mathrm{GL}(V)/\mathrm O(V)$ … and a topology on $Q_{\mathbb C}(V)$"). Once F1 is built that
node's text overstates what remains.

**RULED — amend the text only, defer the node split to F2**, when the F1/F2 separation has
to happen anyway and is already queued as the `def:metc-complex-manifold` node-split / F1 edge
restore. Splitting now means two graph-structure changes instead of one.

---

## 5. Predicted gate

- `lake build` green; **`sorry` 0 → 1**, and the single sorry reported by name (`QC_contractible`).
- `True` stays 0. Bare `axiom` stays 0.
- `lean_decls` grows by exactly the new `\lean`-named declarations.
- Graph: node and edge delta exactly as predicted by the D1 ruling, nothing else moving;
  dark-green stays 7.
- `checkdecls` clean; `mk_all` no-op **if** the code goes into `Domain.lean`.

**D3 — new file or extend `Domain.lean`? RULED: `Domain.lean`.** It is the natural
home, it was left holding only $\Pi(V)$ after the retirement, and it keeps `mk_all` a no-op and
`All.lean` untouched. A new file means regenerating the root import and a CI `mk_all-check`
dependency.

**D4 — state non-convexity in Lean? RULED: prose only, in the blueprint node,** with
the $d = 1$ witness written down explicitly so a future session does not burn time on the convex
route. It is a negative fact about $Q_{\mathbb C}(V)$, not KS content, and formalizing it invites
scope creep.

---

## 6. What F1 does not deliver

It gives $Q_{\mathbb C}(V)$ a canonical topology and makes contractibility statable and honestly
deferred. It does not prove contractibility, does not touch `QC_parametrization`, and does not
move any node to dark green. The first *proved* unlock in this phase is downstream of F2.

---

## 7. Implementation consequences of the D1 ruling (added after the rulings)

**Where the F1 Lean is named in the graph.** All three new declarations —
`AllowableComplexMetric.toForm_injective`, the named topology instance, and `QC_contractible` —
go on the new `prop:contractibility` node's `\lean` list. This keeps the split to **one** new
node rather than also adding a `def:qc-topology` node, and multi-name `\lean` lists are standard
here (`found:hodge-star` carries two, `lem:eigenvalue-minmax` six). Override if you would rather
the topology got its own definition node — it would render light green and make F1's landing more
visible, at the cost of a second graph-structure change.

**Predicted graph delta — the gate condition.** Source `\uses` pairs **+3**:
`def:allowable → prop:contractibility`, `def:trace-norm-fiber → prop:contractibility`,
`prop:parametrization → prop:contractibility`. Rendered (transitively reduced) delta **+1**: only
`prop:parametrization → prop:contractibility` appears, because the other two already reach the new
node through `prop:parametrization`. So:

- nodes **57 → 58**, rendered edges **85 → 86**
- **zero edges removed**, and no pre-existing node changes fill or border
- filled-fill census unchanged at `7 / 1 / 15 / 2`; the new node is green-border/no-fill
  (statement-`\leanok`, proof `\notready` — the shape of the five open proofs), so no-fill goes
  32 → 33
- dark-green stays **7**. Trap-1 is structurally safe: `prop:contractibility` `\uses`
  `prop:parametrization`, an unproved *proposition* ancestor, not merely a definition-foundation,
  so it cannot mis-render dark green.

Anything outside that exact delta is a stop condition.

**`prop:contractibility` does not `\uses found:homogeneous-bundles` directly.** Its F2 dependency
is inherited through `prop:parametrization`, which carries that edge. The topology it needs is
built, so it owes no foundation edge of its own — which is the point of F1.

**Type spelling.** State the theorem on `AllowableComplexMetric V`, not `QC V`. They are the same
type, so the claim is about $Q_{\mathbb C}(V)$ either way, but `QC` is a `def` and typeclass search
does not see through a `def` to find the instance — the lesson already recorded for
`Observables.Ox`, which needed explicit bridge instances for exactly this reason. The probe
confirmed the `AllowableComplexMetric V` spelling elaborates.
