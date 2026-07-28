# Restatement proposal: `def:wick-rotation` (node 4/5)

**Status: PROPOSAL for human review. Nothing applied — no `.lean` or `.tex` edited, no marker
flipped, no build or regen run.** Audit provenance: Pass 1-B, verdict **OVERSTATED** — the
node's `\lean{}` list includes the hypothesis-free alias `WickRotation.EuclideanSpace`, which
names the definiendum `E_Σ` while carrying none of the content that makes it a WICK ROTATION.
This artifact classifies the alias (vacuous, not wrong), decides the fix shape (**hybrid:
small additive Lean hardening + marker demotion**, with pure-subtractive as the flagged
runner-up), and predicts the gate deltas exactly.

**A framing correction, stated up front (do not let it silently pass):** the restatement
brief quotes KSTeX:321-323 (the Appendix-to-2.3 linear rotation `exp(iΘ/2)(𝔼)`) as "KS's
Wick-rotation content". That passage is the paper's *linear-algebra* Wick rotation, part of
the Prop 2.3 appendix — which this project has explicitly deferred (CLAUDE.md: "Props 2.3,
2.6, Lemma 2.8 are deferred"). The node `def:wick-rotation` encodes a *different* passage:
KS Section 5's Wick rotation of a time-symmetric germ (KSTeX:614). Both are quoted below;
the audit finding (the hypothesis-free alias) stands the same either way, but the faithful
statement must be measured against KSTeX:614, not 321-323.

---

## KS claim (quoted)

**The node's actual source — the germ rotation, `docs/KSTeX.tex:614` (verbatim):**

> $\Sigma \subset U$, with $\Sigma$ co-oriented in $U$. We can identify $U$ with
> $\Sigma \times (-\varepsilon, \varepsilon)$ by exponentiating the geodesic curves emanating
> perpendicularly from $\Sigma$. The metric then takes the form $h_t - {\rm d}t^2$, where
> $t \mapsto h_t$ is a smooth map from $(-\varepsilon,\varepsilon)$ to the manifold of
> Riemannian metrics on $\Sigma$. If the germ is time-symmetric then we can define
> $E_{\Sigma}$ by replacing the Lorentzian metric by the `Wick rotated' Riemannian metric
> $h_{{\rm i}t} + {\rm d}t^2$, which makes sense because if $h_t = h_{-t}$ then $h_t$ is a
> function of $t^2$, so that $h_{{\rm i}t}$ is defined and real. But this does not help for
> a general hypersurface, and in any case seems rather arbitrary: we shall return to this
> point in Remark 5.3 below.

The definitional content: (a) the normal form $h_t - dt^2$; (b) time-symmetry ⟹ even family
⟹ $h_t = H(t^2)$, so $h_{it} = H(-t^2)$ is defined and real; (c) the rotated metric
$h_{it} + dt^2$ is Riemannian; (d) **$E_\Sigma$ is what the field theory assigns to THAT
Wick-rotated Riemannian germ** — the "THAT" is the load-bearing part for the alias.

**The brief's quoted passage — the linear rotation, `docs/KSTeX.tex:321-323` (Appendix to
2.3, verbatim):**

> If $V$ is a real vector space with an allowable complex metric then the preceding
> discussion shows that it can be identified with the subspace
> $$V \ = \ \exp({\rm i}\Theta/2)(\mathbb E)$$
> of $\mathbb m_{\mathbb C}$. Here $\mathbb E = \mathbb R^d$ is the standard Euclidean
> subspace of $\mathbb m_{\mathbb C}$, and $\Theta$ is a real diagonal matrix whose entries
> $\theta_1,\ldots,\theta_d$ belong to the `generalized octahedron' $\Pi_0 \subset \mathbb R^d$
> consisting of those $\Theta$ whose diagonal entries $\theta_1,\ldots,\theta_d$ satisfy the
> inequality (4).

This is the linear model of the same idea (allowable $V$ = rotated Euclidean subspace,
rotation angles constrained by condition (4)); it belongs to the deferred Prop 2.3 material
and is NOT what `def:wick-rotation` states. The Lean alias's name `EuclideanSpace` evokes
$\mathbb E$, but the node's $E_\Sigma$ is the field-theory state SPACE, not the subspace
$\mathbb E \subset \mathbb m_{\mathbb C}$. No `exp(iΘ/2)`/`Π_0` content is missing from THIS
node, because this node never claimed it; that content's home would be the deferred Prop 2.3
/ `found:minkowski-linear` orbit (node 5/5 territory).

---

## Current blueprint statement + Lean (verbatim)

Blueprint block, `blueprint/src/section5.tex:179-236` (statement `\leanok` at 186; a
definition node, no proof block; committed graph state:
`NODE def:wick-rotation fill=#B0ECA3 border=green`):

```latex
\begin{definition}[Wick rotation of a time-symmetric germ; KS Section 5]
  \label{def:wick-rotation}
  \lean{WickRotation.RiemannianField, WickRotation.assembleNormalForm,
    WickRotation.GeodesicNormalForm, WickRotation.TimeSymmetricRotation,
    WickRotation.TimeSymmetricRotation.wickRotatedFamily,
    WickRotation.TimeSymmetricRotation.wickMetric, WickRotation.IsEuclideanObject,
    WickRotation.EuclideanSpace}
  \leanok
  \uses{def:lorentzian-cobordism-category, def:unitarity, def:field-theory,
    found:lorentzian-causal-geometry, found:real-analytic-complexification,
    found:wick-correspondence}
  For a \emph{time-symmetric} Lorentzian germ the Wick rotation continues the
  Lorentzian metric to a Riemannian one and uses it to define the Euclidean space
  $E_{\Sigma}$.
  [...normal form h_t - dt²; time-symmetry ⟹ h_t = H(t²), h_{it} = H(-t²) real;
   rotated metric h_{it} + dt² Riemannian; E_Σ := the space the field theory assigns
   to this Riemannian germ; the limitation paragraph; and a closing paragraph
   "Stating this in Lean requires Lorentzian-manifold geometry not developed here: ..."]
\end{definition}
```

(The full prose was read in place; it is a faithful paraphrase of KSTeX:614 and already
carries an explicit deferral paragraph.)

The Lean (`KontsevichSegal/WickRotation/TimeSymmetricRotation.lean`), all eight `\lean`
names — seven are genuine content:

```lean
def IsRiemannian ... : Prop := (∀ v w, φ v w = φ w v) ∧ (∀ v, v ≠ 0 → 0 < φ v v)
def RiemannianField (M : Type*) [TangentStructure M] : Type _ := ...     -- (line 106)
noncomputable def assembleNormalForm ... (B ...) (sgn : ℝ) : ... :=      -- (line 119) B ⊞ sgn·dt²
theorem isRiemannian_assembleNormalForm ... (hB) (hsgn : 0 < sgn) : ...  -- (line 132) PROVED

structure GeodesicNormalForm [G : LorentzianCobordismGeometry] (o : G.Obj) where  -- (line 179)
  Slice ; [sliceTangent] ; ε ; εpos : 0 < ε
  chart : Slice × ↥(Set.Ioo (-ε) ε) ≃ G.Ambient o
  tangentSplit : ∀ σ t, Tangent (chart (σ,t)) ≃ₗ[ℝ] (Tangent σ × ℝ)
  h : ℝ → RiemannianField Slice
  assembles : ∀ σ t ξ η,                                    -- THE TIE to node 1's metric
    (G.metric o (chart (σ,t))).1 ξ η
      = assembleNormalForm (h t σ).1 (-1) (tangentSplit σ t ξ) (tangentSplit σ t η)

structure TimeSymmetricRotation [G] [IsRealAnalytic] (o : G.Obj)
    extends GeodesicNormalForm o where                       -- (line 234)
  H : ℝ → RiemannianField Slice
  factor : ∀ t : ℝ, h t = H (t ^ 2)                          -- Whitney factor (assumed)

theorem even_family (W) (t) : W.h (-t) = W.h t := ...        -- (line 250) PROVED from factor
def wickRotatedFamily (W) (t : ℝ) := W.H (-(t ^ 2))          -- (line 259) h_{it} = H(-t²)
noncomputable def wickMetric (W) (σ) (t) := assembleNormalForm (W.wickRotatedFamily t σ).1 1
theorem isRiemannian_wickMetric (W) (σ) (t) : IsRiemannian (W.wickMetric σ t) := ...  -- PROVED
theorem wickRotatedFamily_zero (W) : W.wickRotatedFamily 0 = W.h 0 := ...             -- PROVED

def IsEuclideanObject (oℂ : g.Obj) : Prop :=                 -- (line 304) NON-VACUOUS
  (∀ x v w, (AllowableComplexMetric.toForm (g.metric oℂ x) v w).im = 0) ∧
  (∀ x v, v ≠ 0 → 0 < (AllowableComplexMetric.toForm (g.metric oℂ x) v v).re)
```

And the eighth — **the finding** (`TimeSymmetricRotation.lean:321`, verbatim, complete):

```lean
def EuclideanSpace (T : FieldTheory) (oℂ : g.Obj) : Type _ := T.E oℂ
```

In symbols: for an **arbitrary** complex object `oℂ` (any object of `C_d^ℂ`, Euclidean or
not), `EuclideanSpace T oℂ` is definitionally `T.E oℂ`. No `IsEuclideanObject` hypothesis,
no `TimeSymmetricRotation` parameter, no tie to `wickMetric`, no Lorentzian germ anywhere in
the type.

### Consumers (1d, every hit)

* Blueprint `\uses` of `def:wick-rotation`: `thm:unitary-gh` (statement, section5.tex:306,
  and proof, :330), `prop:lorentzian-E-welldefined` (:395), `def:observables` (:450); prose
  `\ref`s at :282, :348, :380, :458. Graph edges (committed): in-edges from
  `def:lorentzian-cobordism-category`, `def:unitarity`, `found:wick-correspondence`;
  out-edges to `thm:unitary-gh`, `prop:lorentzian-E-welldefined`, `def:observables`.
* Lean consumers of `WickRotation.EuclideanSpace`: **NONE in code.** Every hit is a comment
  (`InvariancePrinciple.lean:68,97`, `UnitaryGH.lean:60,109` — prose "node 3 deferred for
  `EuclideanSpace`"). A signature change to the alias breaks nothing.
* `lean_decls:69-76` lists all eight names, `WickRotation.EuclideanSpace` at line 76.

---

## The gap (audit finding)

**What the alias asserts: nothing.** `EuclideanSpace T oℂ := T.E oℂ` is a type synonym for
`FieldTheory.E`, hypothesis-free, defined for every object of the complex category. It
typechecks for a Lorentzian-boundary object, for any allowable-metric object, for anything.
As a *statement of KS's definition* it carries zero content: the definiendum is "$E_\Sigma$
:= the theory's space at **the Wick-rotated Riemannian germ**", and the alias captures only
"the theory's space at **some object**".

**What is missing** (relative to KSTeX:614(d)): the tie between the alias's `oℂ` and the
rotation — at minimum that `oℂ` is Euclidean (`IsEuclideanObject`, which exists eight lines
above and is *not used*), at full strength that `oℂ`'s metric is the rotated
`wickMetric` of the given germ's `TimeSymmetricRotation` data (the Riemannian-germ-into-
`C_d^ℂ` embedding — genuinely deferred infrastructure, the same `C_d^{Lor} → C_d^ℂ` gap as
nodes 5/6; the module header names it honestly at lines 63-64).

**Classification: VACUOUS (1-B-style empty statement), not WRONG, node PARTIAL.**

* Not WRONG: nothing in the alias contradicts KS — for the intended `oℂ` it is exactly KS's
  "$E_\Sigma$ = the space the theory assigns". Unlike node 1's `slice_factors`, it excludes
  no intended inhabitant.
* VACUOUS as an annotated claim: under the `\leanok` it stands in for the node's
  definiendum, and it says nothing a bare `T.E` doesn't.
* The NODE is PARTIAL, not hollow: seven of the eight `\lean` names carry genuine, tied,
  partially-proved content — `assembles` pins `h_t` to node 1's invariant metric,
  `factor`/`even_family` capture time-symmetry, `wickRotatedFamily`/`wickMetric` ARE the
  rotation with `isRiemannian_wickMetric` proved. Clauses (a)-(c) of KSTeX:614 are honestly
  encoded; only (d), the definiendum $E_\Sigma$ itself, is vacuous.

---

## Proposed faithful statement (Lean and/or blueprint)

**Recommended fix shape: HYBRID — a small ADDITIVE Lean hardening of the alias, plus a
marker demotion. No new node** (unlike node 3: there is no lost *claim* to re-house — the
blueprint prose already states everything including the deferral; the defect is in the Lean
annotation's coverage, not in missing blueprint content).

**Lean edit** (`TimeSymmetricRotation.lean`; no consumers break — the alias has none):

```lean
/-- **The Euclidean space `E_Σ` of a (Wick-rotated) germ (KS Section 5, blueprint
`def:wick-rotation`).** For a complex object `oℂ` that is Euclidean (`hE` — real,
positive-definite metric: the kind of object a Wick-rotated Riemannian germ defines),
`E_Σ` is the space the field theory `T` of `def:field-theory` assigns to it: `T.E oℂ`.
A reuse of `FieldTheory.E` restricted to its intended domain.

The hypothesis `hE` is not consumed by the definiens (the space does not depend on the
proof); it pins the DOMAIN: `EuclideanSpace` cannot be formed at a non-Euclidean object.
What remains deferred, named: that `oℂ` is THE object of the given germ's Wick-rotated
metric (`TimeSymmetricRotation.wickMetric`) — the Riemannian-germ-into-`C_d^ℂ` embedding,
the same `C_d^{Lor} → C_d^ℂ` correspondence gap as nodes 5/6. This def does NOT claim that
identification. -/
def EuclideanSpace (T : FieldTheory) (oℂ : g.Obj) (hE : IsEuclideanObject oℂ) : Type _ :=
  T.E oℂ
```

**Blueprint edit** (`section5.tex`, the node): keep the prose (already faithful to
KSTeX:614, including the limitation paragraph); keep the full `\lean{}` list (all eight
names survive, same names); flip the statement marker `\leanok → \notready`; extend the
existing "Stating this in Lean requires..." paragraph with one sentence naming the specific
residual, e.g.:

```latex
  ... which realizes the rotated metric as real. The identification of the rotated
  Riemannian germ with a specific Euclidean object of $\mathcal C_d^{\mathbb C}$, whose
  $E$-space is $E_\Sigma$, is likewise not yet expressible: the Lean records the rotation
  data and restricts $E_\Sigma$ to Euclidean objects, but cannot yet tie the object to the
  germ.
```

**Why the "harmless notation vs vacuous theorem" question resolves this way:** as *plain
notation*, `E_ℂ := T.E oℂ` unannotated would be harmless but pointless (dead code with no
call sites). As a `\leanok`'d *claim* standing in for $E_\Sigma$'s definition it is
dishonest. The hardened form is in between and honest about being so: it is notation **with
a pinned domain** — a definition (the #B0ECA3 ceiling for definitions applies; nothing here
pretends to be a theorem), whose docstring names exactly what it does not claim.

**Per-item inventory after the fix** (what each encodes / what it rules out):

| item | encodes | rules out |
|---|---|---|
| `RiemannianField`, `IsRiemannian` | Riemannian metric fields on the slice | the zero/degenerate form (positive-definiteness) |
| `assembleNormalForm` + `isRiemannian_assembleNormalForm` | `h ± dt²` assembly; Euclidean signature PROVED for `sgn > 0` | asserted-not-proved signature claims |
| `GeodesicNormalForm.assembles` | `h_t` = spatial block of node 1's invariant metric through the chart differential | a free `h_t` unrelated to the germ's metric |
| `TimeSymmetricRotation.factor` + `even_family` | Whitney factor `h_t = H(t²)`; evenness PROVED from it | a non-even family (cannot satisfy `factor`) |
| `wickRotatedFamily`, `wickMetric`, `isRiemannian_wickMetric` | the rotation `H(-t²)` and `h_{it} + dt²`, Riemannian PROVED | a non-real or non-Riemannian "rotation" |
| `IsEuclideanObject` | Euclidean-signature complex objects, against the real `g.metric` | non-real / non-positive-definite metrics |
| `EuclideanSpace` (hardened) | `E_Σ = T.E` at a certified-Euclidean object | forming `E_Σ` at a non-Euclidean object (call-site bite) |
| — deferred, named | `oℂ` = THE rotated germ's object | (not claimed; the honest gap that keeps the node `\notready`) |

Phantom disclosure: `hE` is a phantom in the definiens (the type `T.E oℂ` does not depend on
it). Precedent: the node-1 reviewed decision kept `M`/`ht` as documentation parameters; this
is the same pattern, with the same honesty requirement (the docstring says so explicitly).

**Runner-up (pure SUBTRACTIVE), flagged for your call:** delete the `EuclideanSpace` def and
drop its name from `\lean{}` (lean_decls 132 → 131; checkdecls fine after regen), demote the
node the same way. Cleaner (zero phantom hypotheses), but it removes the one statable piece
of (d) from Lean entirely — and unlike node 2 there is no falsity forcing the retreat;
`IsEuclideanObject`-restricted notation is statable and true. Recommend the hybrid.

---

## Fidelity check

**(a)** After the fix, KSTeX:614's four content pieces stand as: (a) normal form — stated,
tied (`assembles`); (b) time-symmetry/evenness/Whitney — stated (`factor`, assumed per the
Mathlib gap) with evenness proved; (c) rotated metric real Riemannian — stated and PROVED
(`isRiemannian_wickMetric`); (d) $E_\Sigma$ — stated as `T.E` restricted to Euclidean
objects, with the germ-to-object identification recorded as deferred in both docstring and
blueprint prose. Nothing is claimed that is not carried; the one uncarried tie is named, not
faked. The `\notready` marker makes the graph agree with that state.

**(b) Adversarial pass:**

* The hardened `hE` is phantom in the definiens — the fix does NOT make `EuclideanSpace`
  compute anything new; it only forbids forming it without a Euclidean certificate. If the
  reviewer considers a domain-pinning phantom hypothesis to be cosmetic rather than content,
  the subtractive runner-up is the consistent alternative. What the fix genuinely changes is
  the *annotation honesty*: the node no longer claims (via `\leanok`) that $E_\Sigma$'s
  definition is formalized.
* Degenerate inhabitants: a degenerate assumed geometry can make `IsEuclideanObject` easy or
  everywhere-true (e.g. all metrics real positive-definite) — inhabitation-degeneracy of the
  assumed `CobordismGeometry`, the standard deferral, not statement-vacuity. Conversely
  nothing forces ANY Euclidean object to exist; `EuclideanSpace` is then just never
  formable, which is honest.
* `TimeSymmetricRotation`'s own assumed fields (`chart`, `H`/`factor`) remain assumed — this
  fix does not touch them and does not upgrade their epistemic status; they were already
  documented as the Whitney/Mathlib gap.

---

## Build & graph implications

* **Touches Lean: YES** (the alias's signature + docstring) → `lake build` REQUIRED (unlike
  node 3). Expected green: the alias has zero code consumers (comments only), the other
  seven decls are untouched, and the edit adds a hypothesis to a def — no proof obligations.
* **NO sorry introduced** (definition-only edit; nothing TRUE-but-unproven is being stated
  as a theorem). sorry = 0 / axiom = 0 / True = 5 all preserved — no maintainer fork this
  time.
* **lean_decls: UNCHANGED (132)** — all eight `\lean` names survive with the same names
  (`EuclideanSpace` changes signature, not name). `lake exe checkdecls`: expect PASS.
  (Runner-up variant instead gives 132 → 131 with the name dropped; also checkdecls-clean.)
* **Graph delta — back to the strict regime (node 3's inversion does NOT apply): ZERO
  node/edge changes expected.** Nodes 57 → 57, edges 85 → 85, sorted edge set IDENTICAL
  (`\uses` untouched, no new node). The ONLY expected change:
  `def:wick-rotation  #B0ECA3-fill/green-border  →  no-fill/#FFAA33-border` (the `\notready`
  flip). Tallies: #B0ECA3 16 → 15; no-fill 31 → 32; orange-border 31 → 32.
* **Dark-green 7 → 7**: def:wick-rotation is not dark-green, and none of its dependents
  (`thm:unitary-gh`, `prop:lorentzian-E-welldefined` — both already orange — and
  `def:observables`, #B0ECA3) is dark-green, so no dark-green node can lose ancestry status.
  Any other node changing color is a STOP condition.
* Commit surface: `TimeSymmetricRotation.lean` + `section5.tex` + regenerated
  `dep_graph_document.html` (+ this artifact). Watch the tracked-render allowlist: section5's
  page render is NOT tracked (nodes 1-2 precedent), so no `index.html`/`sect000*.html` churn
  is expected this time — if `git status` shows web files beyond the dep graph, flag rather
  than assume.

---

## Proposed post-fix marking

**`def:wick-rotation`: statement `\leanok → \notready`.** Faithful-rule reasoning: the
node's definiendum ($E_\Sigma$ of the rotated germ) is not yet expressible — the Lean
carries the rotation data (much of it tied and proved) and a domain-restricted `E_Σ`
notation, but cannot state "the space at THE rotated germ". That is exactly the
"faithful statement not yet expressible" state, and it is the demotion-batch standard
(thm:unitary-gh precedent: substantial genuine content, untied definiendum, `\notready`).
The counter-reading — convention 1b's "statement-complete over assumed structures" — would
keep `\leanok` only if the missing tie were *routed through an assumed structure* (as
flip-3's `def:isomorphism-action` routes through `GermIsoGeometry`); here it is not routed
through anything, merely absent. The `\lean{}` list stays (the `\lean`+`\notready` state is
established precedent: rigged-triple, pre-flip isomorphism-action). Proof-side: n/a
(definition node).

---

## Open questions for human review

1. **Hybrid vs pure-subtractive:** keep the hardened `EuclideanSpace (T) (oℂ) (hE :
   IsEuclideanObject oℂ)` (recommended — keeps the statable piece of (d) in Lean, node-1
   documentation-parameter precedent) or delete the alias + drop from `\lean{}` (zero
   phantoms, lean_decls 132 → 131)? The phantom-`hE` disclosure above is the honest cost of
   the recommendation.
2. **The marker call:** `\notready` (recommended, demotion-batch consistency) vs keeping
   `\leanok` under a broad reading of convention 1b. This is the same convention tension
   node 1 flagged (its Open question 1); if you rule the other way here, the node-1 marking
   should be revisited under the same rule.
3. **A third shape not chosen:** route the tie through a NEW assumed structure (e.g. a
   `RiemannianGermEmbedding` class providing `euclObj : TimeSymmetricRotation o → g.Obj`
   with a metric-identification field) — that WOULD license `\leanok` under 1b and would be
   the additive analogue of node 3. Not recommended now: it manufactures an assumed class
   solely to re-earn a marker, and its metric-identification field skirts assuming the very
   correspondence content nodes 5/6 defer. Flagged in case you want it as future
   infrastructure alongside `found:wick-correspondence`.
4. **The framing correction:** confirm you accept that KSTeX:614 (not the brief's
   KSTeX:321-323 appendix passage) is the fidelity yardstick for THIS node, and that the
   `exp(iΘ/2)(𝔼)`/`Π_0` content belongs to the deferred Prop 2.3 orbit (relevant to node 5/5
   `found:minkowski-linear`, where the octahedron constraint genuinely lives).
5. **Blueprint prose addition:** the one-sentence residual-naming extension to the node's
   closing paragraph — confirm wording (kept mathematical, no Lean-status recap beyond the
   existing paragraph's own style).
6. **Graph expectation:** confirm the ZERO-edge-delta prediction (this fix returns to
   "edges changed = STOP"; only def:wick-rotation's fill/border moves).
