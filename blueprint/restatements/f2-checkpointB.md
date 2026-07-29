# F2 checkpoint B — the modulus form and the contractible base

**Status: RULINGS RECORDED 2026-07-29 — D1/D2/D3/D4 all as recommended. No repo file has been edited yet.**
Target path when approved: `blueprint/restatements/f2-checkpointB.md` (git-tracked; commit with
the edit).
Verified against `origin/main` at `3a2b685`. Scratch source: `_scratch/f2_modulus.lean`,
`_scratch/f2_scope.lean`.

This checkpoint banks the sorry-free work from the checkpoint-B probe and lands the canonicity
statement as a tracked `sorry`. It does **not** prove that `modulusForm` is KS's canonical `g₀` —
see §3, which is the honesty constraint on this commit.

---

## 1. What the probe established

**Both planning-chat observations held, one more strongly than proposed.** The angles are already
a genuine function of `g` (`ksAngle`, `ksAngle_eq_iInf_iSup`, `ksAngle_antitone` all take `g`
alone), so only the eigenspace decomposition was missing. And the rescaling computation I offered
turned out to be *subsumed*: a rescaled basis is simply another eigenbasis of the same pencil
operator, which is a cleaner mechanism than the summand-invariance argument.

**CLOSED sorry-free:** `modulusForm` (choose-witness `mk₂`), `modulusForm_apply` (`rfl`),
`modulusForm_posDef` — closed because it is witness-local — and `modulusForm_nondegenerate`;
`arg_mem_transfer` and `rotation_transfer`, the two transfer lemmas that compile the boundary of
the canonicity proof; `sinPencil`, which is **a sorry-free function of `g` alone** — exactly the
de-choicing the scoping probe reported as missing; and the whole of B6:
`base_contractible : ContractibleSpace (PosDefForm V)` with `symmPosDef_convex`, `euclidR_symm`,
`euclidR_posDef`.

**OPEN:** `modulus_welldef` — canonicity. The remaining subgoal is named precisely: both witnesses
are eigenbases of the *same* pencil operator (via `pencilOperator_eigen_basis_of_form`, with
P-orthogonality and diagonal values already supplied by the pre-existing
`bilin_basis_eq_zero_of_ne` / `bilin_basis_apply_self`), so what remains is uniqueness of the
eigenspace decomposition — that the `ker(T − s)`-components of `v` are witness-independent — plus
`Finset.sum_fiberwise` regrouping and the sec·cos collapse. Estimated 150–250 lines. **No
choice-dependence failure of the Target-A kind was found**, which is the result that matters:
`g₀` is the right anchor.

**Also open, one layer out:** `sinPencil`'s `g₀`-self-adjointness (route named:
`pencilOperator_pairing` + `isSymmetric_of_pairing` through `posDefCore`), and KS's Θ itself,
which needs arcsin calculus on `sinPencil` or a per-eigenspace definition. Not in this checkpoint.

---

## 2. Placement — D1 **[RULED: new file]**

`Contractibility.lean` imports `Domain`, `Equivalence` **and** `EigenvalueMinmax`, so it is
downstream of everything this checkpoint needs; `posDef_convex` and `convex_pos_combo` live there,
while `pencilOperator`, `euclid` and `nondegenerate_of_angle_cond` live in `EigenvalueMinmax.lean`.

**RULED — a NEW file `KontsevichSegal/ComplexMetrics/Parametrization.lean`,** importing
`Contractibility`, `EigenvalueMinmax` and `Domain` explicitly (the repo's style lists what is used
even when transitively available — `Contractibility` itself lists `Equivalence` redundantly).

Rationale: F2 is a multi-checkpoint build and deserves its own home, exactly as the retraction did.
The alternative — modulus machinery into `EigenvalueMinmax.lean` (already ~2700 lines) and the base
into `Contractibility.lean` — mixes F2's base material into the retraction file and spreads one
checkpoint across two unrelated files.

**Note for the docstring, so a reader is not misled:** the import of `Contractibility` is for
*reuse of two convexity lemmas*, not a logical dependence of Proposition 2.4 on the retraction
proof. Duplicating a five-liner to avoid the import would be worse than the import.

**Consequence to predict:** `mk_all` is **NOT** a no-op — new file, so `KontsevichSegal.lean` is
regenerated and `ComplexMetrics.lean` needs a hand-added import. Same as checkpoint 1.

---

## 3. HONESTY CONSTRAINT — `modulusForm` is not yet known to be KS's `g₀`

`modulusForm` is a well-defined function of `g` (`Exists.choose` is deterministic), but without
`modulus_welldef` it is only known to equal `∑|λ_k| y_k²` **for the chosen witness**. KS's claim is
that this form is *canonically* associated to `g`.

**Therefore no docstring, and no blueprint prose, may call `modulusForm` canonical, or identify it
with KS's `g₀`, in this commit.** The permitted claim is: a positive-definite form built from a
diagonalizing witness, conjectured — and asserted by KS — to be witness-independent, with that
independence carried as a tracked `sorry`. Over-claiming here would be the node-2 failure mode
(a Lean credential for something the Lean does not establish) in a new place.

---

## 4. Which sorries land — D2 **[RULED: two]**

**RULED — two.**

- **`modulus_welldef`** — the canonicity statement. Honest on all three counts: statable (it
  compiles), true (KS assert it, KSTeX 214–216), not yet proved (the named eigenspace-uniqueness
  core).
- **`sinPencil_isSelfAdjoint`** — independently statable and true; it does not depend on canonicity,
  since self-adjointness of `sinPencil` with respect to `modulusForm` follows from
  `pencilOperator_pairing` + `isSymmetric_of_pairing` whichever witness `modulusForm` used.

*Not landed:* `modulus_existsUnique`. It is statable, but it is **equivalent to
`modulus_welldef`** — a second sorry for the same mathematical content, which inflates the tracked
count without adding information. If the `∃!`-plus-pin route (B2(ii)) is later preferred as the
definition, it replaces `modulus_welldef` rather than joining it.

`sorry` goes **0 → 2**, both under real pinned statements. That is the tracked-sorry convention
working, not a regression.

---

## 5. Blueprint — D3 and D4 **[RULED: both as recommended]**

**D3 — two new lemma nodes.** The proved and unproved content are genuinely different claims and
must not share a node.

- `lem:posdef-base` — "The space of positive-definite real forms on `V` is contractible."
  `\lean{PosDefForm, symmPosDef_convex, base_contractible}` (actual names to be reported),
  statement **and** proof `\leanok`. `\uses{}` — **empty**, and correctly so: this is a statement
  about real positive-definite forms and depends on no other node. Precedent for an empty `\uses`:
  `def:nuclear-frechet`. **Predicted dark green, taking the count 9 → 10.**
- `lem:modulus-form` — the modulus form: definition, positive-definiteness, the transfer lemmas,
  `sinPencil`, and the canonicity statement. `\lean{...}`, statement `\leanok`, proof `\notready`.
  `\uses{def:allowable, lem:eigenvalue-minmax}` — it consumes `angle_cond` and the `ksAngle`
  bridge. Prose must observe §3's constraint.

**D4 — two edits to existing nodes.**

- `prop:parametrization`'s **proof** `\uses{def:allowable}` → `\uses{def:allowable,
  lem:modulus-form, lem:posdef-base}`, with a sentence naming the intended route. Same pattern as
  checkpoint 1 attaching `lem:posdef-retraction` to `prop:contractibility`'s proof. The node stays
  `\notready`; nothing here proves Proposition 2.4.
- `def:trace-norm-fiber`'s prose — **a graph-honesty item the probe surfaced.** That node is
  labelled as the fibre `Π(V,g₀)`, but its Lean encodes self-adjointness with respect to *some*
  positive-definite form, so the `∃ g₀` makes every fibre the same union set. The probe's verdict
  was blunt: it **cannot** serve as the fibre, and the simplification the docstring itself
  predicted would bite now bites. **RULED — amend the prose only** — record that a
  `g₀`-relative version is required and owed, with no marking or `\uses` change. Splitting the node
  belongs with the relative fibre when it is built, not here.

---

## 6. Predicted gate

- `lake build` green; **`sorry` 0 → 2**, named: `modulus_welldef` and `sinPencil_isSelfAdjoint`.
  Any third sorry is a stop condition.
- `True` 0; bare `axiom` 0. Grep must exclude `_scratch/`.
- **`mk_all` NOT a no-op** (new file); `ComplexMetrics.lean` gains an import line.
- `lean_decls` grows by the names placed on the two new `\lean` lists.
- `checkdecls` clean.
- Graph: **nodes 59 → 61**, `lem:posdef-base` **dark green** so **dark-green 9 → 10**,
  `lem:modulus-form` green-border/no-fill. Edge delta is the new incoming edges only, with **zero
  removals**; the rendered count cannot be predicted exactly under transitive reduction, so the
  gate condition is structural — report the number and confirm every change is an edge into a new
  node or into `prop:parametrization`'s proof.
- **Standing check** on the new dark green: enumerate `lem:posdef-base`'s ancestry from SOURCE. An
  empty `\uses` makes it trivially clean, but confirm rather than assume — and confirm all nine
  existing dark-greens survive, since `Restriction.lean` rebuilds if `EigenvalueMinmax` is touched
  (it is not, under D1, but confirm).

---

## 7. Carry-forwards

- **A new instance of the `moduleTopology`-whnf hazard.** `base_contractible` required a scoped
  heartbeat bump: unifying the declared subtype-topology instance grinds through the `sInf`. This
  is the second heartbeat bump in the project (checkpoint 1's `aux_upper` was the first) and the
  first tied to `moduleTopology` subtypes. Expect it whenever a topology is induced on a subtype of
  a `moduleTopology` space. Use the scoped, linter-approved form.
- **Eigenvalue collisions are the obstruction to budget for in B5** (continuity of `g₀`): angle
  multiplicities can change along paths in `Q_C(V)`, making per-eigenvalue formulas delicate even
  though `g₀` itself stays continuous. Price that separately, outside checkpoint B.

---

## 8. What this checkpoint does not claim

It does not prove Proposition 2.4, does not prove canonicity, does not construct KS's Θ, and does
not establish the fibre-bundle or balanced-product structure. `prop:parametrization` stays
`\notready`. What it banks is the anchor — a positive-definite form and a Θ-precursor that are both
functions of `g` alone — plus the contractible base, which is a KS ingredient in its own right.
