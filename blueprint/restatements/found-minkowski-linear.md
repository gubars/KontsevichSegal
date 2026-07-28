# Restatement proposal: `found:minkowski-linear` (node 5/5, LAST) — v2, post-probe

**Status: PROPOSAL for human review. Nothing applied — no `.lean` or `.tex` edited, no marker
flipped, no build or regen run.** This version SUPERSEDES the pre-probe draft at this same
path (v1 established the L3 layer verdict — built linear base, node 4's rotation layer
adjacent and separate — and recommended the `neg_index_le_one` pin; the read-only provability
probe has since COMPILED the pin's proof sorry-free, upgrading the fix from proposed to
P1-established). Audit finding: the (d−1,1) signature conjunct of the node's `\leanok`'d
statement is UNSTATED in the Lean class (the (2,2) instance is admissible). P1: the signature
is statable with current imports AND provable now for the concrete model. This is the batch's
only ADD-PROVED-CONTENT fix (nodes 1-2 deleted, 3 narrowed+split, 4 deferred); no sorry
arises.

**Two gate-premise corrections, up front (verified against the tree — the fix gate must use
THESE, not the brief's expectations):**

1. **`found:minkowski-linear` rests on NO `True` placeholder.** `grep 'True := by'` finds the
   five placeholders at `Domain.lean:74,91,110,129` + `ShilovBoundary.lean:659` — all
   Section 2; `MinkowskiLinear.lean` contains zero `True`. **True count stays 5 → 5.** A
   True-count change during this fix is a STOP condition, not an expectation.
2. **Dark-green stays 7 → 7 and the node stays `#B0ECA3` (predicted).** The node is a
   DEFINITION with statement-`\leanok`, no proof block, and — decisively — NO `\uses` at all,
   hence no ancestors; yet it renders `#B0ECA3`, not `#1CAC78`. So ancestry is not what
   withholds dark-green: the proof-side marker is, and definition nodes here carry none (all
   the project's dark-greens are proof-carrying lemma/prop/thm nodes). Adding a proved Lean
   field does not add a blueprint proof block, so no color change is predicted. Residual
   uncertainty about leanblueprint's definition-coloring rule is flagged (Open question 4);
   the gate is: EXPECT an empty color diff, treat ANY color change as STOP-and-inspect.

---

## KS claim (quoted)

`docs/KSTeX.tex:764`: "We end with a conjecture about a question arising in the traditional
treatment of field theories defined in the standard Minkowski space $\m = \R^{d-1,1}$."

`docs/KSTeX.tex:158`: "It follows from Theorem 2.2 that the real inner products with
signature $(d-1,1)$ --- but not those with other signatures --- lie on the boundary of the
domain $Q_{\C}(V)$."

`docs/KSTeX.tex:765` (footnote): the normalization "for which $||\xi||^2 < 0$ when $\xi$ is
time-like" (mostly-plus, timelike-negative). `docs/KSTeX.tex:93`: "The special role of
Lorentzian signature is perhaps the most notable feature of our work."

What KS assert 𝕄's linear structure IS: a real d-dimensional vector space with a symmetric
nondegenerate bilinear form of signature **exactly (d−1,1)** — one negative (timelike)
direction, d−1 positive — not merely "some indefinite form".

---

## Built foundation (verbatim, re-read)

`KontsevichSegal/WickRotation/MinkowskiLinear.lean:50-68` — the class head and every
sign-relevant field (full field list continues with `mC`/`coeM`/`mc_span`/`bilin`/
`bilin_symm`/`bilin_real`/`Eucl`/`coeEucl`/`projE`/`projE_coeEucl`/`projE_eucl_span`/
`eucl_span`/`bilin_eucl_real`/`bilin_eucl_pos`, lines 69-105):

```lean
class MinkowskiLinear where
  m : Type u
  [macg : AddCommGroup m]
  [mmod : Module ℝ m]
  [mfin : FiniteDimensional ℝ m]
  /-- The real Lorentzian form on `m`, signature `(d-1,1)`. -/
  realForm : m →ₗ[ℝ] m →ₗ[ℝ] ℝ
  realForm_symm : ∀ x y, realForm x y = realForm y x
  realForm_nondegen : ∀ x, x ≠ 0 → ∃ y, realForm x y ≠ 0
  exists_timelike : ∃ x, realForm x x < 0
  exists_spacelike : ∃ x, 0 < realForm x x
  ...
```

(The docstrings SAY "signature (d−1,1)"; the fields do not state it.)

The concrete model's form (`MinkowskiLinear.lean:121,150,205-210`):

```lean
def eta (i : Fin (n + 2)) : ℝ := if i = 0 then -1 else 1
def realForm : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ := diagForm (eta n)
-- realForm n x y = ∑ i, eta n i * x i * y i  — diag(−1, +1, …, +1), time at index 0

noncomputable def minkowskiLinear : MinkowskiLinear where
  m := Fin (n + 2) → ℝ
  realForm := realForm n
  ...
```

Manifestly (d−1,1): exactly one −1 on the diagonal.

---

## Current blueprint statement + Lean (verbatim)

`blueprint/src/foundations.tex:284-305` — statement marker is **`\leanok`** (no `\notready`,
no True placeholder — see correction 1), no `\uses`, no proof block; committed graph:
`NODE found:minkowski-linear fill=#B0ECA3 border=green`, single (transitively reduced) edge
`found:minkowski-linear -> def:vacuum-domain`:

```latex
\begin{definition}[Complexified Minkowski space]
  \label{found:minkowski-linear}
  \lean{WickRotation.MinkowskiLinear, WickRotation.MinkowskiModel.minkowskiLinear}
  \leanok
  Real Minkowski space $\mathbb M = \mathbb R^{d-1,1}$ with its Lorentzian form of signature
  $(d-1,1)$; [...] the Lorentzian form is
  indefinite and nondegenerate; the forward light cone is exhibited (nonempty, open,
  proper), its convexity left to [...]
\end{definition}
```

The two `\lean`'d decls are exactly the class and the model instance pasted above
(`lean_decls:131-132` of 131 total — the last two lines).

### Consumers (1d, every hit)

* Blueprint `\uses`: `def:vacuum-domain` (section5.tex:586) and `prop:Vk-contains-Uk`
  (section5.tex:634); prose `\texttt` mention in node-4's future-work note (section5.tex:247,
  not a `\uses`). Graph: one edge out (to def:vacuum-domain; the Vk edge is transitively
  reduced through it). No consumer touches the signature fields — nothing strands.
* Lean: `MinkowskiComplexGeometry extends MinkowskiLinear` (`VacuumDomain.lean:184`) — a
  class with NO concrete instances (project constraint), so a new field costs nothing there;
  `WickRotation.lean` import rollup; prose mentions in VacuumDomain's header. The ONLY
  instance of `MinkowskiLinear` anywhere is `MinkowskiModel.minkowskiLinear` — verified by
  grep (`: MinkowskiLinear` hits: the class line and the model line only).

---

## The gap (audit finding, P1-confirmed)

`MinkowskiLinear` states the full linear structure (form, complexification with tied base
change, Euclidean slice with both splittings — all genuinely built and model-realized) but
NO signature condition: `exists_timelike` + `exists_spacelike` say only "indefinite", which
every signature (p,q) with p,q ≥ 1 satisfies. The (2,2)-admissibility is concrete:
`diagForm (−1,−1,+1,+1)` on `Fin 4 → ℝ` satisfies every field (the Euclidean-slice fields
via `mu = (I,I,1,1)` — the model's own cancellation works for any sign pattern). So the
node's `\leanok`'d headline "signature (d−1,1)" — the content that makes it MINKOWSKI — is
unstated. NOT a wrong object (node 4's shape), NOT un-statable, NOT false: P1 — statable
now, true for the model, and (per the probe) provable now.

---

## Proposed faithful statement (Lean) — the state part

**A new field on `MinkowskiLinear`, placed after `exists_spacelike` (recommended
placement):**

```lean
  /-- **The signature pin: negative index at most one.** No two-dimensional subspace of `m`
  is negative definite. With `exists_timelike` (negative index ≥ 1), `realForm_nondegen`,
  and finite-dimensionality, Sylvester's law pins the signature to `(d-1, 1)`: exactly one
  timelike direction. Excludes the `(2,2)`-style forms the other fields admit. -/
  neg_index_le_one : ∀ W : Submodule ℝ m,
    (∀ w ∈ W, w ≠ 0 → realForm w w < 0) → Module.finrank ℝ W ≤ 1
```

* **Why a field (vs a separate lemma about the model):** the node's claim is about 𝕄's
  STRUCTURE (the interface), not about one model; a model-only lemma would leave the class
  — the thing `MinkowskiComplexGeometry` and the node-2 degenerate-instance arguments
  quantify over — still (2,2)-admissible. Instance check done: the model is the only
  instance, and it can satisfy the field (probe-proved); `MinkowskiComplexGeometry` has no
  concrete instances to break. (Open question 1 records the alternative.)
* **Why this formulation:** "negative index ≤ 1" is the coordinate-free "at most one
  timelike direction"; simpler shapes are WRONG (two independent timelike vectors exist even
  in genuine Minkowski — `(1, ±1/2, 0, …)`). Statable with current imports (`Submodule`,
  `Module.finrank` — no new Mathlib); the QuadraticForm signature API was NOT verified to
  exist in the pin and is not needed.
* **What it encodes / rules out:** encodes "negative index ≤ 1"; rules out (2,2) (the span
  of the two −1 axes is a 2-dimensional negative-definite subspace — `finrank = 2` fails
  it) and every (p,q) with q ≥ 2; Euclidean forms were already excluded by
  `exists_timelike`. Non-vacuous in both directions: falsifiable, and non-trivially
  satisfied by the model.

---

## Proposed proof (Lean) — the prove part (PROBE-COMPILED, sorry-free)

The probe lemma, compiled clean (exit 0, zero diagnostics, first attempt) via
`lake env lean` against the repo environment — this exact statement and proof:

```lean
example (n : ℕ) (W : Submodule ℝ (Fin (n + 2) → ℝ))
    (hW : ∀ w ∈ W, w ≠ 0 → MinkowskiModel.realForm n w w < 0) :
    Module.finrank ℝ W ≤ 1 := by
  set φ : W →ₗ[ℝ] ℝ :=
    (LinearMap.proj (0 : Fin (n + 2))).comp W.subtype with hφ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w, hwW⟩ h0
    have hw0 : w 0 = 0 := h0
    have hw : w = 0 := by
      by_contra hne
      have hneg := hW w hwW hne
      have hnn : (0 : ℝ) ≤ MinkowskiModel.realForm n w w := by
        rw [MinkowskiModel.realForm_apply]
        refine Finset.sum_nonneg fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [hw0]
          simp
        · have hεi : MinkowskiModel.eta n i = 1 := by
            unfold MinkowskiModel.eta
            rw [if_neg hi]
          rw [hεi, one_mul]
          exact mul_self_nonneg _
      linarith
    exact Subtype.ext hw
  have h1 : Module.finrank ℝ W ≤ Module.finrank ℝ ℝ :=
    LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_self] using h1
```

Tactic shape: explicit-witness/elementary — the time-coordinate functional restricted to W,
kernel-triviality from termwise `Finset.sum_nonneg` (+ `mul_self_nonneg`), then
`LinearMap.finrank_le_finrank_of_injective` + `Module.finrank_self`. No diagonalization, no
spectral machinery, no new imports.

**Real-tree wiring (the one delta from the probe, FLAGGED):** in the fix this body becomes
the field witness inside the instance —
`neg_index_le_one := fun W hW => by <same body>` — where the instance's `realForm` is
definitionally `MinkowskiModel.realForm n`, the exact form the probe proved against; the
goal statement inside the instance is presented through the class field, which is defeq
(a `show`/`intro` may be needed to re-display it). Low risk, but `lake build` is the real
gate, as always.

---

## Fidelity check

**(a)** With the field, `MinkowskiLinear` states: finite-dimensional real space, symmetric
nondegenerate form, negative index exactly 1 (≥ 1 `exists_timelike`, ≤ 1 the new field),
positive direction existing — by Sylvester (meta-level, Open question 5), signature
(d−1,1): KS's $\m = \R^{d-1,1}$ with the timelike-negative normalization. The rest of the
node's claims (complexification, tied base change, Euclidean slice) were already faithful
and proved.

**(b)** True for the model: PROVED (the compiled probe), not just inspected. Non-vacuity,
adversarially: could something satisfy `neg_index_le_one` without being (d−1,1)? Signatures
(d,0) (Euclidean) and (0,1)/(0,q) fail `exists_timelike`/`exists_spacelike` respectively;
(p,q) with q ≥ 2 fails the new field (a 2-dim negative-definite plane exists — span two
negative axes of a diagonalization); degenerate forms fail `realForm_nondegen`. What
remains is exactly negative index 1 with positive directions = (d−1,1). No trivial
satisfaction exists: the field quantifies over ALL subspaces, so it cannot be discharged by
a clever choice of witness (contrast the existential fields). Inhabitation-degeneracy: none
new — the class was and remains genuinely inhabited by a proved model; nothing here is a
deferred-construction placeholder.

---

## Build & graph implications (gate predictions — with the two corrections)

* **Touches Lean: YES** — `MinkowskiLinear.lean` only (class field + instance witness).
  `lake build` REQUIRED and is the real gate; the probe compiling clean makes green the
  strong expectation. `VacuumDomain.lean` recompiles (parent class extended; no constructor
  sites exist).
* **sorry: STAYS 0** — P1, the proof is already written and compiled. Any sorry appearing →
  STOP (it would mean the instance wiring failed, not that the math is missing).
* **lean_decls: 131 → 132 (recommended path)** — annotate the new content by adding
  `WickRotation.MinkowskiLinear.neg_index_le_one` (a field accessor IS a real declaration;
  precedent: `InducesUnitaryGH.pairing_reflectionPositive` is `\lean`'d) to the node's
  `\lean{}`. `checkdecls`: expect PASS. Alternative (don't annotate): lean_decls unchanged
  at 131 — Open question 2; the gate should check whichever is decided, exactly.
* **True count: 5 → 5** (correction 1 — no placeholder involved; a True delta → STOP).
* **Colors: NO change predicted** (correction 2) — `found:minkowski-linear` stays
  `#B0ECA3`/green (definition node, statement-`\leanok`, no proof block); **dark-green
  7 → 7**. Any color change anywhere → STOP-and-inspect (if the node DOES flip to `#1CAC78`
  because leanblueprint treats `\leanok`'d definitions as proved once regenerated, that is
  a benign single-node change — inspect, confirm it is exactly this node, and record the
  coloring-rule learning; any OTHER node changing → hard stop).
* **Nodes/edges: 57 → 57, 85 → 85, sorted edge set IDENTICAL** — no new blueprint node, no
  `\uses` change; the blueprint edit is the marker-adjacent prose clause + the `\lean{}`
  addition only.
* **Blueprint edit:** add the one clause to the model-description sentence ("...indefinite
  and nondegenerate, with negative index exactly one, pinning the signature to
  $(d-1,1)$;") and (per Open question 2) the `\lean{}` name. `\leanok` UNCHANGED.
* **STAGING NOTE (node-4 two-commit lesson):** the commit set is the FULL git-status dirty
  set after `leanblueprint web`: `MinkowskiLinear.lean`, `foundations.tex`, `lean_decls`
  (if the annotation path is taken), `dep_graph_document.html`, PLUS any tracked render of
  foundations.tex's section (check `git status --porcelain -- blueprint/web/` and stage
  everything listed), plus this artifact. Verify the commit's `--stat` against that list
  before logging.

---

## Proposed post-fix marking

**`found:minkowski-linear`: `\leanok` KEPT — now genuinely earned.** After the pin, every
clause of the node's prose, including the headline "signature (d−1,1)", is stated by the
class and proved for the model. This is the batch's only node whose fix direction is
strengthen-the-Lean-to-meet-the-claim; the marker doesn't move, its justification does.
(The brief's "gains a green" framing, corrected: no NEW green is predicted — the node keeps
its `#B0ECA3` honestly rather than gaining `#1CAC78`; see correction 2.)

---

## Open questions for human review

1. **Field vs separate lemma:** field on `MinkowskiLinear` (recommended — the claim is
   about the interface; sole instance verified, `MinkowskiComplexGeometry` instance-free)
   vs a model-only lemma (weaker: leaves the class (2,2)-admissible). Confirm the field.
2. **Annotate the accessor?** Add `WickRotation.MinkowskiLinear.neg_index_le_one` to the
   node's `\lean{}` (lean_decls 131 → 132, checkdecls-resolvable, precedent exists) or
   leave the `\lean` list unchanged (131). Recommend ANNOTATE; decide before the fix so the
   gate's lean_decls expectation is exact.
3. **The two gate-premise corrections:** sign off that True stays 5 (no placeholder here)
   and that the expected color delta is EMPTY with dark-green 7 → 7 — overriding the
   brief's "True 5→4" and "dark-green 7→8" expectations, which do not match the tree.
4. **Definition-coloring residual:** if the regen unexpectedly flips the node to `#1CAC78`,
   treat as benign-if-isolated (record the leanblueprint rule); confirm this handling.
5. **Sylvester diligence:** the "these fields ⟺ signature (d−1,1)" step is classical and
   asserted at meta level (the Lean states the index bound, not Sylvester's law itself).
   Confirm this standard (matches nodes 2/5's meta-level reasoning).
6. **Batch closure:** 5/5 — after this fix lands, the restatement batch is complete. The
   L3 layer verdict and the node-4 reconciliation note from v1 of this artifact remain in
   force (𝕄_ℂ/𝔼 are built; node 4's unbuilt part is the exp(iΘ/2)/Π₀ rotation layer atop
   them — two future-work items, not one).
