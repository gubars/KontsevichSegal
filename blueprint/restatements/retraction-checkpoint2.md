# Retraction checkpoint 2 — closing `QC_contractible`

**Status: RULINGS RECORDED 2026-07-29 — D1/D2/D3 as recommended. Plus D4, a FORCED correction to this artifact's own placement table (see §2a). No repo file has been edited yet.**
Target path when approved: `blueprint/restatements/retraction-checkpoint2.md` (git-tracked;
commit with the checkpoint-2 edit).
Verified against `origin/main` at `45742c2`. Scratch source this checkpoint transcribes:
`_scratch/cp2_probe.lean` (390 lines, compiled clean, zero sorries, zero axioms).

**This checkpoint closes the project's only `sorry` and makes `Q_C(V)` contractible a theorem.**

---

## 1. What the probe established

All four assembly items closed sorry-free in scratch, and so did the theorem itself:

- **A0** — no basepoint for `AllowableComplexMetric V` existed anywhere (independently
  confirmed: the `euclid` grep hits are `euclideanPath` in `LorentzianEWelldefined.lean`,
  unrelated). Built: `euclid`, the Euclidean form on `Module.finBasis`, as an ℝ-valued `mk₂`
  postcomposed with `Algebra.linearMap ℝ ℂ`. Also no general `angle_cond → nondegenerate` lemma
  existed; the predicted route works and is now `nondeg_of_ac`, eight lines from
  `exists_rotation_posDef` + `rotatedReOfForm_posDef`, witness `w := v`.
- **A1** — `segMetric g t ht`, allowability of the straight-line segment, closed on the first
  compile with all five obligations exactly as sketched.
- **A2** — joint `(t,g)`-continuity and the `ContinuousMap.Homotopy` packaging, all three
  sub-items. `ModuleTopology.continuousSMul` and `IsModuleTopology.toContinuousAdd` supply the
  ℝ-`smul` and addition **directly** — the bilinear lemma was *not* needed here, unlike P5's
  ℂ-`smul`. `Set.Icc`-versus-`unitInterval` friction was nil.
- **A3** — `posDef_convex`, and `seg2Metric` via a new general constructor `ofRealPosDef`
  (real positive-definite ⇒ allowable). The two-stage `Homotopy.trans` route is what closed;
  applying `Convex.contractibleSpace` to the image subtype was unnecessary.
- **A4** — `ContractibleSpace (AllowableComplexMetric V)` proved outright:
  `rw [contractible_iff_id_nullhomotopic]; exact ⟨euclid, ⟨stage1.trans stage2⟩⟩`.

This was the expected-risk item (A2) closing along with everything else. The probe order —
compiler before plan — has now caught two planning errors and confirmed two arguments across
three probes; it is the reason this checkpoint is a transcription rather than an attempt.

---

## 2. Placement — D1, D2, D3

The repo has an established **import-direction rule**: a lemma lives in the earliest file whose
imports suffice, judged by what its statement mentions (the F1–F4 split of the Prop 2.5 flag
induction is the precedent — `F1`/`F2` in `EigenvalueMinmax.lean`, `F3`/`F4` in
`Restriction.lean` "their statements mention `g.restrict` — import-direction rule").

Applying it, with one correction to the probe's own advice:

| declaration | home | why |
|---|---|---|
| `nondeg_of_ac` + arg helpers | `EigenvalueMinmax.lean` | needs `exists_rotation_posDef` (`:1028`), `rotatedReOfForm_posDef` (`:310`), `nondegenerate_of_posDef` (`:393`) — all in that file |
| `ofRealPosDef` | `EigenvalueMinmax.lean` | needs `bilin_diag_of_orthogonal` (`EigenvalueMinmax:104`) **and** `exists_basis_isOrtho_pair_of_posdef` (`Equivalence:239`); `EigenvalueMinmax` imports `Equivalence`, so this is the earliest legal home — **NOT `Equivalence.lean`**, correcting the probe |
| `euclid` | `EigenvalueMinmax.lean` | built via `ofRealPosDef` |
| `segMetric`, `seg2Metric`, `posDef_convex`, `stage1`, `stage2`, the homotopies | `Contractibility.lean` | retraction-specific |
| `QC_contractible` **moves here** | `Contractibility.lean` | see §2a — the original plan was impossible |

**D1 [RULED: `EigenvalueMinmax.lean`] — `euclid` there, or rebuilt directly in `Defs.lean`?**
*Recommendation: `EigenvalueMinmax.lean`, as the probe built it.* Conceptually the nonemptiness
of the basic object belongs in `Defs.lean`, and it *could* be built there from an explicit
all-eigenvalues-1 witness needing nothing but `Defs`. But that means re-deriving a proof that
already compiles, and the standing rule is not to re-derive working scratch. Relocation to
`Defs.lean` is a fine later tidy.

**D2 [RULED: yes] — do `nondeg_of_ac`, `ofRealPosDef`, `euclid` get `\lean`-listed?**
*Recommendation: yes, appended to `lem:posdef-retraction`'s `\lean` list, with one prose
sentence naming them.* This keeps the node count fixed at 59 and adds no edges, while making the
three general-purpose additions visible. The alternative — leaving them un-`\lean`'d, which is
normal for supporting machinery — hides that `Q_C(V)` is now known nonempty, which is worth
surfacing.

**D3 [RULED: three files] — three files, or everything in `Contractibility.lean`?**
*Recommendation: three files, per the import-direction rule.* Cost to note: touching
`EigenvalueMinmax.lean` rebuilds `Restriction.lean`, which imports it, and `prop:restriction` is
dark green. The additions are purely additive so there is no correctness risk, but the gate must
confirm all eight existing dark-greens survive.


### 2a. D4 — `QC_contractible` must MOVE. Forced, not a preference.

This artifact's first draft said the final proof term would "replace `QC_contractible`'s `sorry`"
in `Domain.lean`. **That is impossible.** Verified at `45742c2`: `QC_contractible` is declared at
root level in `Domain.lean:141`, and `Contractibility.lean` **imports** `Domain.lean` (line 31).
A proof term living in `Contractibility.lean` therefore cannot be referenced from `Domain.lean` —
it would be an import cycle.

**Resolution: move the theorem to `Contractibility.lean`, where its proof lives**, and keep it at
**root level** (either by closing `namespace KontsevichSegal.Retraction` before it, or by
declaring it as `_root_.QC_contractible`). Root level is not cosmetic: the `lean_decls` entry is
the bare `QC_contractible` (line 16) and `prop:contractibility`'s `\lean` list names it
unqualified, so re-namespacing it would silently break `checkdecls`.

`Domain.lean` then keeps `TraceNormLtOne`, `AllowableComplexMetric.ext`, `toForm_injective` and
`instTopologicalSpace`, and its module docstring — whose RETIREMENT paragraph names
`QC_contractible` at line 9 — needs a line recording that the theorem moved and why.

This is the second time the import direction has forced a placement decision in this phase; the
first was F1's D3. Worth treating as a standing check: before siting a declaration, confirm the
direction of every file it must reference.

---

## 3. HAZARD — do not remove the `nondegenerate` field

`nondeg_of_ac` is a general `angle_cond → nondegenerate` derivation, which **meets the
precondition** the status doc set for a long-deferred refactor: the `nondegenerate` field of
`AllowableComplexMetric` was flagged as "redundant — derivable in principle", to be acted on
"ONLY after the derivation is confirmed to compile in Lean". It now compiles.

**Do not act on it in this commit, or in any commit without its own review.** Removing a
structure field is a breaking refactor touching every construction site in the project —
`ShilovBoundary`'s inline metrics, `Restriction`'s flag induction, `HodgeScaffold`'s projection,
and now three new constructors. `nondeg_of_ac` is **additive**; the field stays. What has changed
is only that the refactor's stated precondition is met, which should be recorded as
newly-unblocked and still out of scope.

---

## 4. Predicted gate

- `lake build` green. **`sorry` 1 → 0**, and `QC_contractible` becomes a proved theorem. Note the
  invariant is now "`sorry` tracked, each under a real pinned statement" — going to zero is a
  discharge, not a regression, and does **not** reinstate "`sorry` = 0" as an invariant.
- `True` 0; bare `axiom` 0. Grep must exclude `_scratch/`.
- `mk_all` a **no-op** — no new file this time (unlike checkpoint 1).
- `lean_decls` grows by exactly the names added to `\lean` (three under D2, plus any of the
  retraction-specific ones judged worth listing).
- `checkdecls` clean.
- **Graph, and this is sharply predictable:** nodes **59 → 59**, edges **87 → 87** (no new node,
  no `\uses` change), `prop:contractibility`'s proof `\notready` → `\leanok`, so its fill goes
  `#A3D6FF` → `#1CAC78` and **dark-green 8 → 9**. Census becomes
  `9 #1CAC78 / 1 #9CEC8B / 15 #B0ECA3 / 2 #ECECEC`, with `#A3D6FF` **disappearing from the
  census** — it had exactly one occupant. All eight existing dark-greens must survive.
- **Standing check fires** on the new dark green: enumerate `prop:contractibility`'s full
  transitive `\uses` ancestry from SOURCE — expected `def:allowable` (statement) and
  `lem:posdef-retraction` (proof), itself dark green — and confirm no `\notready` ancestor.

---

## 5. Carry-forwards from the probe, for the transcription

- **The `letI` trap (iteration 1's main error class).** `continuous_induced_rng.mpr` needs
  `letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _` in scope first; without it
  instance synthesis fails.
- **`posDef_convex` resists `nlinarith`.** The goal `0 < a·X + c·Y` needs an explicit
  positive-combination case split; `nlinarith` alone failed.
- **Heartbeats.** Scratch used an unscoped file-level `set_option maxHeartbeats 1000000`, and
  which declarations actually need it is **untested**. The tracked build must use the scoped,
  linter-approved form (`set_option … in`, then the reason comment, then the docstring) **per
  declaration**, and must test which ones genuinely need it rather than blanket-applying. An
  unscoped file-level bump would fail the repo linter.
- `ModuleTopology.continuousSMul` + `IsModuleTopology.toContinuousAdd` suffice for ℝ-`smul` and
  addition; do not reach for `continuous_bilinear_of_finite_left` here.

---

## 6. What this closes, and what it does not

**Closes:** `QC_contractible` becomes a theorem; the contractibility clause of KS Proposition 2.4
is formalized and proved, by a route KS do not take; `Q_C(V)` gains a basepoint; and the project
gains two general-purpose additions (`nondeg_of_ac`, `ofRealPosDef`).

**Does not close:** `prop:parametrization` — the fibre-bundle statement `Q_C(V) ≅ GL(V) ×_{O(V)}
Π(V)` — which still needs **F2** and is untouched by any of this. The retraction proves the
corollary without proving the theorem it is a corollary of in KS. That asymmetry is worth stating
in the blueprint prose so no reader concludes Proposition 2.4 is done.
