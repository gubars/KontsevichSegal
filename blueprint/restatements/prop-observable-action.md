# Restatement proposal: `prop:observable-action` (node 1/5)

**Status: PROPOSAL for human review. Nothing in this file has been applied — no `.lean` or
`.tex` was edited, no marker flipped, no build or graph regen run.** This artifact records the
audited defect in the current Lean statement of `prop:observable-action`, the proposed faithful
restatement, and every uncertainty the reviewer must resolve before the Lean edit.

Audit provenance: independent re-check of 2026-07-27 (this session), judged against the paper
text only, verdict **(c) WRONG** — the statement asserts a factorization the paper's claim
excludes.

---

## KS claim (quoted)

KS arXiv:2105.10161, "Field operators", `docs/KSTeX.tex:743` (verbatim):

> if x lies on a time-slice Σ we get an operator ψ ∈ Hom(Ě_Σ; Ê_Σ), i.e. an UNBOUNDED
> operator in E_Σ, simply by considering the cobordisms corresponding to a sequence of
> successively thinner collars of Σ. Indeed the same argument shows that if x_1,...,x_k
> are distinct points on Σ, we have a map  O_{x_1} ⊗ ... ⊗ O_{x_k} → Hom(Ě_Σ; Ê_Σ)
> which does not depend on choosing an ordering of the points.

The two key points the faithful statement must respect:

1. the slice observable is a map Ě_Σ → Ê_Σ — an operator that is **unbounded on E_Σ**; it does
   **not** factor through a bounded operator on E_Σ;
2. the multilinear map on k distinct points is **order-independent**.

The blueprint block (`blueprint/src/section5.tex:473-489`, statement `\leanok` at line 477) is
itself faithful to this; the defect is Lean-side only:

```latex
\begin{proposition}[Action of observables; KS Section 5]
  \label{prop:observable-action}
  \lean{WickRotation.ObservableAction, WickRotation.ObservableMultilinear,
    WickRotation.ObservableMultilinear.eval_orderIndep}
  \leanok
  \uses{def:observables, def:field-theory, def:tensor-axiom,
    found:observable-bundle, found:tvs-limits-tensor, found:smooth-cobordism-geometry}
  Let $M \colon \Sigma_0 \leadsto \Sigma_1$ be a Lorentzian cobordism and
  $x \in \mathring M$. An observable $\psi \in \mathcal O_x$ acts as an operator
  $E_{\Sigma_0} \to E_{\Sigma_1}$. If $x$ lies on a time-slice $\Sigma$, then $\psi$
  acts as an element of $\mathrm{Hom}(\check E_{\Sigma}; \hat E_{\Sigma})$, an unbounded
  operator in $E_{\Sigma}$. For distinct points $x_1, \ldots, x_k$ on $\Sigma$ there is
  a multilinear map
  \[ \mathcal O_{x_1} \otimes \cdots \otimes \mathcal O_{x_k} \;\longrightarrow\;
     \mathrm{Hom}(\check E_{\Sigma}; \hat E_{\Sigma}) \]
  that does not depend on an ordering of the points.
\end{proposition}
```

---

## Current Lean (verbatim)

`KontsevichSegal/WickRotation/ObservableAction.lean:167-198` (docstrings elided inside the
structure for legibility; every field and its exact type is reproduced):

```lean
structure ObservableAction [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [m : MonoidalCobordism] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (ht : IsTensorial T)
    {σ₀ σ₁ : gl.Obj} (M : gl.Mor σ₀ σ₁)
    (σ : gl.Obj) [MetCManifold (gl.Ambient σ)] (x : gl.Ambient σ)
    (O : Observables σ x) where
  act : O.Ox →ₗ[ℂ] (T.E (WOC.cplx σ₀) →L[ℂ] T.E (WOC.cplx σ₁))
  actAtSlice : O.Ox →ₗ[ℂ] (T.E (WOC.cplx σ) →L[ℂ] T.E (WOC.cplx σ))
  slice : O.Ox →ₗ[ℂ] (T.ECheck (WOC.cplx σ) →L[ℂ] T.EHat (WOC.cplx σ))
  slice_factors : ∀ ψ : O.Ox,
    slice ψ = (T.toEHat (WOC.cplx σ)).comp ((actAtSlice ψ).comp (T.fromECheck (WOC.cplx σ)))
```

Field docstrings of record (abridged, from the same file): `actAtSlice` is described as "the
bounded operator on `E_σ` that the thinner-collar actions converge to. This is the CORE through
which the time-slice operator `slice` factors"; `slice_factors` as "It BITES: a `slice` not of
the form `toEHat ∘ (bounded) ∘ fromECheck` is excluded."

`KontsevichSegal/WickRotation/ObservableAction.lean:220-236`:

```lean
structure ObservableMultilinear [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [m : MonoidalCobordism] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (ht : IsTensorial T)
    (σ : gl.Obj) [MetCManifold (gl.Ambient σ)] {k : ℕ}
    (x : Fin k → gl.Ambient σ) (hx : Function.Injective x)
    (O : ∀ i, Observables σ (x i)) where
  mmap : ∀ π : Equiv.Perm (Fin k),
    MultilinearMap ℂ (fun i => (O (π i)).Ox)
      (T.ECheck (WOC.cplx σ) →L[ℂ] T.EHat (WOC.cplx σ))
  ordering_indep : ∀ (π π' : Equiv.Perm (Fin k)) (v : ∀ i, (O i).Ox),
    mmap π (fun i => v (π i)) = mmap π' (fun i => v (π' i))
```

`KontsevichSegal/WickRotation/ObservableAction.lean:242-249`:

```lean
theorem ObservableMultilinear.eval_orderIndep [gc : CobordismGeometry]
    [gl : LorentzianCobordismGeometry] [HolomorphicComplexification] [m : MonoidalCobordism]
    [WOC : WickObjectCorrespondence] {T : FieldTheory} {ht : IsTensorial T} {σ : gl.Obj}
    [MetCManifold (gl.Ambient σ)] {k : ℕ} {x : Fin k → gl.Ambient σ}
    {hx : Function.Injective x} {O : ∀ i, Observables σ (x i)}
    (W : ObservableMultilinear T ht σ x hx O) (π : Equiv.Perm (Fin k)) (v : ∀ i, (O i).Ox) :
    W.mmap π (fun i => v (π i)) = W.mmap (Equiv.refl (Fin k)) v :=
  W.ordering_indep π (Equiv.refl (Fin k)) v
```

Supporting rigging-map types, `KontsevichSegal/FieldTheory/FieldTheory.lean:141,143`:

```lean
  toEHat : ∀ o, E o →L[ℂ] EHat o
  fromECheck : ∀ o, ECheck o →L[ℂ] E o
```

---

## Why the current statement is wrong

The defect is entirely in the pair `actAtSlice` + `slice_factors`. Type-level statement of the
problem:

`slice_factors` asserts, for **every** ψ,

```
slice ψ = (T.toEHat σc).comp ((actAtSlice ψ).comp (T.fromECheck σc))
```

with `actAtSlice ψ : E_σ →L[ℂ] E_σ` a **continuous (bounded) operator on E_σ**. Writing
Φ : (E_σ →L E_σ) → (Ě_σ →L Ê_σ), Φ(A) = toEHat ∘ A ∘ fromECheck, the constraint says
`slice ψ ∈ range Φ` for all ψ. Two consequences follow from the types alone:

1. `slice ψ` is the rigging-restriction of a globally defined continuous operator on E_σ —
   i.e. it **is** a bounded operator in E_σ, merely viewed on the rigging;
2. `range (slice ψ) ⊆ range (toEHat)` — `slice ψ` can never produce a vector of Ê_σ outside
   the image of E_σ.

The paper's "i.e. an unbounded operator in E_Σ" is precisely the assertion that the
thinner-collar limit lives in Hom(Ě_Σ; Ê_Σ) and **not**, in general, in range Φ. That is the
entire point of the collar device: each positive-thickness collar gives an operator
E_Σ → E_Σ, and the limit escapes to Hom(Ě; Ê) because no continuous limit on E_Σ exists in
general. If the limit were Φ(A) with A continuous on E_σ, ψ would *be* a bounded operator in
E_Σ and KS's sentence would be false. A generic field operator moreover produces vectors in
Ê_σ outside E_σ's image, violating consequence 2 directly.

The exclusion is not escapable by a clever inhabitant: `actAtSlice` is a field, so an
inhabitant must *supply* it, and a genuinely non-factoring `slice` admits **no** choice of
`actAtSlice` satisfying `slice_factors`. The structure therefore excludes the paper's intended
inhabitant. The very field `actAtSlice` postulates "the bounded operator on E_σ that the
thinner-collar actions converge to" — the object whose nonexistence is the content of the word
"unbounded".

This is classification (c) of the audit taxonomy: not merely incomplete, but a statement the
paper's claim rules out. The fix must change the statement, not the marker.

(The module's own gloss at `ObservableAction.lean:33-35` — that a continuous map Ě_σ → Ê_σ is
the faithful encoding of "unbounded operator in E_σ" — is correct; `slice`'s **type** was
always right. The infidelity entered only with the factorization tie.)

---

## Proposed faithful statement (Lean)

**The fix: delete the fields `actAtSlice` and `slice_factors`. Keep `act` and `slice`
unchanged. Touch nothing else in the declaration.** The corrected structure in full, with
proposed docstrings:

```lean
/-- **The action of an observable on a Lorentzian cobordism (KS Section 5, blueprint
`prop:observable-action`), the single-observable case.** For a field theory `T` (tensorial,
`ht`), an ambient Lorentzian cobordism `M : σ₀ ⤳ σ₁`, and an observable `O` at a point `x` on
a time-slice `σ` in the interior of `M`:

* `act` is the action `ψ ↦ (E_{σ₀} → E_{σ₁})`, linear in `ψ`. Built — in deferred prose — by
  removing a small disc around `x`, applying the tensoring property `def:tensor-axiom`, and
  passing to the inverse limit `𝒪_x = lim← E_{∂D}`.
* `slice` is the time-slice operator `ψ ∈ Hom(Ě_σ; Ê_σ)`, an UNBOUNDED operator in `E_σ`:
  in the rigging `Ě_σ ⊂ E_σ ⊂ Ê_σ` an unbounded operator in `E_σ` is exactly an element of
  `Hom(Ě_σ; Ê_σ)`, with NO requirement that it factor through a continuous operator on `E_σ`
  (KS: "simply by considering the cobordisms corresponding to a sequence of successively
  thinner collars of `Σ`" — the collar operators are each continuous on `E_σ`, but their
  limit in general is not; the type deliberately does NOT assert such a factorization).

The geometric relationships (`x ∈ M̊`, `σ` a time-slice of `M` through `x`) and the
operator-from-`ψ` constructions are deferred (the opaque `Mor`, the deferred tensor split /
inverse limit). Not constructed for any concrete theory. -/
structure ObservableAction [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [m : MonoidalCobordism] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (ht : IsTensorial T)
    {σ₀ σ₁ : gl.Obj} (M : gl.Mor σ₀ σ₁)
    (σ : gl.Obj) [MetCManifold (gl.Ambient σ)] (x : gl.Ambient σ)
    (O : Observables σ x) where
  /-- The action `ψ ↦ (E_{σ₀} → E_{σ₁})` of an observable on the ambient cobordism `M`,
  linear in `ψ ∈ 𝒪_x`. The construction (disc removal + tensoring + inverse limit) and the
  tie to `T.Z` across the opaque `M` are deferred prose. -/
  act : O.Ox →ₗ[ℂ] (T.E (WOC.cplx σ₀) →L[ℂ] T.E (WOC.cplx σ₁))
  /-- The time-slice operator `ψ ∈ Hom(Ě_σ; Ê_σ)`, an unbounded operator in `E_σ` — an
  element of the Hom-space of the rigging with no factorization through `E_σ` imposed. The
  thinner-collars construction is deferred prose. -/
  slice : O.Ox →ₗ[ℂ] (T.ECheck (WOC.cplx σ) →L[ℂ] T.EHat (WOC.cplx σ))
```

**`ObservableMultilinear` and `eval_orderIndep` stay byte-identical.** The audit found the
order-independence half faithful: `mmap π` is the multilinear map out of the (universal
property of the) tensor product for each ordering; `ordering_indep` is genuine permutation
invariance — it is falsifiable (an order-dependent family `mmap π₀ = m₀ ≠ 0`, `mmap π = 0`
otherwise forces `m₀ = 0`) and pins the whole family to `mmap (Equiv.refl _)` (every input `w`
is `v ∘ π` for `v := w ∘ π⁻¹`), so the family carries no data beyond the one order-independent
map — exactly KS's single map. `eval_orderIndep` is a real, sorry-free proof.

### Per-field / per-parameter inventory of the corrected `ObservableAction`

| item | what it encodes | what it rules out / constrains |
|---|---|---|
| `[gc] [gl] [HolomorphicComplexification]` | ambient cobordism + Lorentzian geometry; needed by the types (`gl.Obj`, `gl.Ambient`, `Observables`) | nothing beyond well-formedness |
| `[m : MonoidalCobordism]` | needed only to state `ht : IsTensorial T`'s type | **referenced by no field** |
| `[WOC : WickObjectCorrespondence]` | the Lorentzian→complex object map `cplx`; used by every field's type | ties the operator spaces to the genuine Section-3 spaces |
| `T : FieldTheory` | the theory whose `E`/`Ě`/`Ê` the operators live on; used by every field | codomains are the real Section-3 spaces, not stand-ins |
| `ht : IsTensorial T` | the tensoring property KS's construction uses (disc removal `∂D ⊔ σ₀ ⤳ σ₁`) | **PHANTOM — referenced by no field**; documentation only |
| `{σ₀ σ₁} (M : gl.Mor σ₀ σ₁)` | the ambient cobordism of the first sentence | **M is PHANTOM — referenced by no field** (`act` uses σ₀, σ₁ only); the structure is inhabitable with `act` unrelated to `M` |
| `σ`, `[MetCManifold (gl.Ambient σ)]` | the time-slice object; `MetCManifold` required by `Observables`' type | used by `slice`'s type |
| `x : gl.Ambient σ` | the point; enters only through `O`'s type | not otherwise constrained (no "x ∈ M̊ / σ through x" predicate exists on the opaque `Mor`) |
| `O : Observables σ x` | node 8's genuine observable space; `O.Ox` is every field's domain | ties ψ to the real `𝒪_x` |
| `act` | "ψ acts as an operator E_{Σ₀} → E_{Σ₁}", linear in ψ | per-ψ continuity + linearity; nothing ties it to `M`/`T.Z` (deferred) |
| `slice` | "ψ ∈ Hom(Ě_Σ; Ê_Σ), i.e. an unbounded operator in E_Σ" | per-ψ continuity + linearity; deliberately does NOT impose (nor forbid) factorization through E_σ |

In `ObservableMultilinear` (unchanged): `ht` and `hx : Function.Injective x` are likewise
phantoms — no field references them; `hx` documents the distinctness the deferred
disjoint-collars construction needs.

**Phantom-parameter RECOMMENDATION (not a decision):** keep `M`, `ht`, `hx` (and `[m]`) as
documentation-parameters. Precedent in-repo: node 7 carries `hReal : IsReal T` and node 6
carries `hU : IsUnitary T` the same way, and dropping `M` would detach the node from the
paper's "Let M : Σ₀ ⤳ Σ₁ be a Lorentzian cobordism" framing. The honest cost: they constrain
nothing, so the structure quietly says less than its parameter list suggests — if the
reviewer prefers parameters to be load-bearing only, dropping `M`/`ht` is defensible and the
blueprint prose would carry the framing instead. Flagged in Open questions.

---

## Fidelity check

**(a) The proposed statement states the KS claim.**

* *Slice map.* KS's sentence is a membership claim: ψ ∈ Hom(Ě_Σ; Ê_Σ), with "i.e. an unbounded
  operator in E_Σ" as KS's own gloss of what membership in that Hom-space means in the rigging
  Ě ⊂ E ⊂ Ê. The corrected `slice ψ : Ě_σ →L[ℂ] Ê_σ` is exactly that membership: an element of
  the Hom-space with no E-preservation requirement. Note the direction of fidelity: "unbounded
  operator" in standard usage *includes* operators that happen to be bounded (e.g. an
  observable acting as the identity), so the faithful statement must *permit* factoring
  inhabitants while *not mandating* factorization. Adding a positive "slice ψ ∉ range Φ" field
  would overshoot the paper exactly as `slice_factors` undershot it. The bare Hom-typed field
  is the unique reading that neither adds nor removes content.
* *Order-independence.* `ordering_indep` is KS's "does not depend on choosing an ordering",
  stated as the sameness of evaluations across any two orderings, and `MultilinearMap` is the
  universal-property encoding of the map out of `𝒪_{x₁} ⊗ ⋯ ⊗ 𝒪_{x_k}` (the completed
  topological tensor product itself being a known Mathlib gap). Unchanged from the audited
  version, which found it faithful.
* *First sentence.* `act` states "ψ acts as an operator E_{Σ₀} → E_{Σ₁}" (present in both the
  paper's paragraph and the blueprint node).

**(b) Adversarial pass — what a degenerate inhabitant can still do.**

Being honest, since this is the point of the artifact:

* `act := 0`, `slice := 0` (and `mmap π := 0`) inhabit the corrected structures. This is
  **inhabitation-degeneracy, not statement-vacuity**: the structures assert the *shape* of the
  data plus the one property KS state (order-independence, which genuinely bites — see the
  falsifiability argument above); the *existence* of the genuine inhabitant is KS's
  construction (disc removal, thinner collars, disjoint collars), which is deferred prose
  under scope (a), and nothing statable against the opaque `Mor` (no disc-removal or collar
  accessor, no morphism-level Wick correspondence) can currently pin `act`/`slice` to `T.Z`.
  The same degeneracy existed before this fix and exists in the sibling nodes (5, 6, 7); the
  fix removes a *false* constraint, it does not (and cannot yet) add the true one.
* After the fix, **nothing ties `slice` to `act`** (previously `slice_factors` tied `slice` to
  `actAtSlice`, but to the *wrong* thing). The true tie — both arise from `T.Z` on
  collar/disc-removal cobordisms — is not statable today for the same infrastructure reasons.
  So the corrected structure is two independent carried maps plus types. That is weaker than
  what the paper *proves*, but it no longer contradicts anything the paper *says*, and every
  removed constraint was false rather than merely partial.
* Worth stating plainly: deleting `slice_factors` deletes the only "BITES" constraint the
  single-observable structure had. The corrected `ObservableAction` has **no** propositional
  field at all. The bite of the node now lives entirely in `ObservableMultilinear.ordering_indep`
  (which is also where the paper's own emphasis lies: "the same argument shows... does not
  depend on choosing an ordering").

**Net fidelity verdict on the proposal:** states point (1) (Hom(Ě;Ê)-membership, no bounded
factorization imposed) and point (2) (order-independence) of the KS claim; excludes the
paper's inhabitant in no way; remains degenerately inhabitable, which is the known scope-(a)
deferral pattern, now honestly labeled.

---

## Proof status after restatement — recommended marking

**Recommendation: after the Lean fix, mark the statement `\notready` (do NOT restore the
statement-`\leanok` in the same change), and record why in project_status.md.**

Reasoning, both directions:

* *For `\leanok`:* the wrongness is removed; `slice`'s type is the exact Hom-space; the one
  property KS assert (order-independence) is stated non-vacuously and its packaging lemma is
  proved. Under a reading where a scope-(a) structure earns statement-`\leanok` when its
  carried data + properties mirror the paper's stated objects, this would qualify.
* *For `\notready` (recommended):* today's demotion batch (thm:unitary-gh,
  prop:invariance-principle, prop:lorentzian-E-welldefined) set the bar that
  **underspecifying** statements sit at `\notready` even when nothing in them is false. The
  corrected `ObservableAction` is squarely in that class: `M` and `ht` are phantoms, `act` and
  `slice` are tied to neither `M` nor `T.Z` nor each other, and the proposition's actual
  assertion — that a field theory *has* such an action — is not stated (there is no
  existence-level claim, and none is statable against the opaque `Mor`). Consistency with the
  demotion batch requires `\notready` here too. What would earn the marker back: a statable
  tie of `act`/`slice` to `T.Z` (needs collar/disc-removal accessors on the cobordism
  category and the morphism-level Wick correspondence), or an explicit recorded convention
  that shape-level encodings qualify for statement-`\leanok` (in which case the three demoted
  nodes should be re-examined under the same rule).

The proof-side marking is unaffected: no `\leanok` on the proof either way (KS's construction
remains deferred prose; `eval_orderIndep`'s proof is real but is packaging, not the node's
proof).

---

## Open questions for human review

1. **Marking after the fix** (previous section): `\notready` recommended for consistency with
   the demotion batch — but this interacts with the project-wide convention decision
   (memory: "leanok convention 1b, statement-complete `\leanok`"). If convention 1b is read as
   "faithful carried-data statement ⇒ statement-`\leanok`", the recommendation flips to
   `\leanok`. This is a convention call only the maintainer can make; the artifact
   deliberately does not make it.
2. **Phantom parameters `M`, `ht`, `hx`, `[m]`**: keep as documentation (recommended, matches
   nodes 6/7 precedent) or drop for a parameters-are-load-bearing discipline? If dropped, the
   blueprint prose must carry the "ambient cobordism M" framing.
3. **Is dropping `actAtSlice` outright the right repair**, vs. demoting it to an *optional*
   side-structure (e.g. a separate `BoundedSliceCore` extension for those ψ whose slice
   operator does extend boundedly)? The paper asserts no such core exists in general, and no
   sibling node has an optional-extension pattern, so the proposal is a clean drop — but a
   reviewer might want the bounded case kept somewhere as a definition (not a field). The
   proposal's position: add nothing; reintroduce a bounded-core *definition* only if a later
   node needs it.
4. **Ê vs E^Hilb reading of "unbounded operator in E_Σ"**: after `thm:unitary-gh`, one could
   alternatively read the slice operator as a densely-defined operator in the Hilbert space
   E^Hilb_Σ with domain Ě_Σ. KS's own "i.e." glosses Hom(Ě_Σ; Ê_Σ)-membership, and the
   blueprint node states it the same way, so the proposal encodes the Hom-space membership —
   but flagging the alternative reading in case the reviewer wants the Hilbert-space bridge
   noted in the docstring.
5. **k = 1 coherence**: nothing ties `ObservableAction.slice` to `ObservableMultilinear.mmap`
   at `k = 1`, though KS's "the same argument shows" implies the single-point slice operator
   *is* the k = 1 case. Should a coherence field (or a lemma-shaped placeholder) be added, or
   is that additional structure beyond what the paper states? The proposal leaves it out
   (adding it would need `ObservableAction` and `ObservableMultilinear` to share a context)
   and flags it here.
6. **Collateral edits the fix will require** (not part of this artifact, listed so the
   reviewer can scope the commit): the module header comment of `ObservableAction.lean`
   (lines 1-136) argues at length that `slice_factors` is faithful (CHECK 1, "float-free
   ties") — it must be rewritten, not just the structure; `docs/project_status.md` must record
   the restatement; grep confirms no other file references `actAtSlice`/`slice_factors`
   (`SpacelikeCommutativity.lean`, `VacuumDomain.lean`, `KontsevichSegal.lean`,
   `WickRotation.lean` reference only the structure names / other decls — to be re-verified at
   fix time with `lake build`); the blueprint `\lean{}` list is unchanged (it names no
   removed field).
7. **Does deleting the only propositional field of `ObservableAction` make the node's
   "proposition" too thin?** After the fix the single-observable half is pure carried data.
   An alternative faithful strengthening — a *statement-level* existence claim ("for every
   tensorial unitary theory there exists an `ObservableAction`...") as a sorry'd theorem —
   was considered and rejected here because the standalone existence claim is not provable or
   even fully statable against the axiomatized (opaque-`Mor`) cobordism category, the same
   reason the Vk-contains-Uk restatement (node 1-B) is hard; but the reviewer should confirm
   that rejection rather than inherit it silently.
