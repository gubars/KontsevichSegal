# Restatement proposal: `prop:Vk-contains-Uk` (node 2/5)

**Status: PROPOSAL for human review. Nothing applied — no `.lean` or `.tex` edited, no marker
flipped, no build or regen run.** Audit provenance: read-only classification of 2026-07-27,
verdict **(b) RESTATEMENT** — the `\leanok`'d theorem `Uk_subset_Vk` conditions on a structure
whose field `uk_subset_vcheck` carries KS's own Proposition 5.4 content ("never axiomatize
KS's own theorem"). This artifact resolves the central question that classification left open:
**sorry'd theorem vs `\notready` prose node**. The recommendation is **(B): `\notready` prose
node** — the standalone faithful statement is FALSE in the current axiomatized geometry's
generality, so a sorry under it would misstate, not merely defer.

---

## KS claim (quoted)

The proposition, `docs/KSTeX.tex:803` (verbatim):

> **Proposition 5.4**  *$\mathcal V_k$ contains the Wightman domain $\mathcal U_k$.*

Its PROOF — KS prove this; that is the point — `docs/KSTeX.tex:811-813` (verbatim):

> **Proof of 5.4**  First, $\mathcal V_k$ is invariant under the complex orthogonal group of
> $\mathbb m_{\mathbb C}$, and under reorderings of the points ${\bf x} = \{x_1,\ldots,x_k\}$.
> So it is enough to consider ${\bf x}$ such that the imaginary part of $x_{i+1} - x_i$
> belongs to the forward light-cone $C \subset \mathbb m$ for each $i$.
>
> Smoothing the obvious polygonal path joing the points, we can thus assume that the $x_i$
> lie on a curve $x: \mathbb R \to \mathbb m_{\mathbb C}$ whose derivative Im$(x'(t))$ belongs
> to $C$ for all $t$. But then we can choose, smoothly in $t$, a set of $d-1$ orthonormal
> vectors $e_j(t)$ in $\mathbb m_{\mathbb C}$ which are all orthogonal to $x'(t)$. Let $M_t$
> be the *real* vector subspace of $\mathbb m_{\mathbb C}$ spanned by the vectors $e_j(t)$.
> The points ${\bf x}$ lie on the $d$-dimensional real ruled manifold $M$ swept out by the
> affine $d-1$-planes $x(t)+M_t$, and the metric of $M$ is clearly allowable. $\spadesuit$

Contrast, `docs/KSTeX.tex:799`: "Unfortunately we have no proof that $\mathcal V_k$ is a
domain of holomorphy, but at least we can assert [Prop 5.4]" — Prop 5.4 is the part KS
**establish**, by the ruled-manifold construction. It is a theorem of the paper, not an
assumption, and the current encoding assumes it.

The definitions the statement rests on, `docs/KSTeX.tex:769-775` (verbatim):

> The ideas of this paper suggest a candidate for $\mathcal V_k$. It sits over the open
> subset $\check{\mathcal V}_k$ of all $k$-tuples ${\bf x} = \{x_1,\ldots,x_k\}$ of distinct
> points in $\mathbb m_{\mathbb C}$ which lie on some totally-real submanifold $M$ with two
> properties:
>
> (i) the metric on $M$ induced from $\mathbb m_{\mathbb C}$ is allowable, and
>
> (ii) $M$ projects surjectively onto the usual real Euclidean subspace
> $\mathbb E = \mathbb R^d$ of $\mathbb m_{\mathbb C} = \mathbb E \oplus i\mathbb E$.

with $\mathcal V_k$ the largest Hausdorff quotient of the pair-space $\mathcal F_k$ through
which $\pi$ factors by a local diffeomorphism (`KSTeX:777-778`). $\mathcal U_k$, the permuted
extended tube (`KSTeX:186` footnote): "A set of points $x_1,\ldots,x_k$ belongs to
$\mathcal U_k$ if, after ordering them suitably, there is an element $\gamma$ of the
complexified Lorentz group such that the imaginary part of $\gamma(x_i - x_{i+1})$ belongs to
the forward light-cone for each $i$." At $k=2$ (`KSTeX:765`): all $(x_1,x_2)$ such that
$\|x_1-x_2\|^2$ is not real and negative.

The blueprint block (`blueprint/src/section5.tex:621-628`, statement `\leanok` at 624; proof
block 630-642 reproduces KS's ruled-manifold proof as prose):

```latex
\begin{proposition}[Proposition 5.4; KS Section 5]
  \label{prop:Vk-contains-Uk}
  \lean{WickRotation.VacuumExpectationData.Uk_subset_Vk}
  \leanok
  \uses{def:vacuum-domain, def:allowable, found:minkowski-linear, found:scv-tube-domain}
  The domain $\mathcal V_k$ contains the Wightman domain $\mathcal U_k$.
\end{proposition}
```

---

## Current Lean (verbatim)

All from `KontsevichSegal/WickRotation/VacuumDomain.lean`.

The ambient geometry class (lines 164-192; `extends MinkowskiLinear`, the BUILT linear
foundation with genuine model `MinkowskiModel.minkowskiLinear` — `mC`, `bilin`, `Eucl`,
`projE`, and the forward light-cone live there):

```lean
class MinkowskiComplexGeometry extends MinkowskiLinear where
  TotallyRealSub : Type u
  carrier : TotallyRealSub → Set mC
  tangentSpace : TotallyRealSub → Type u
  [tacg : ∀ M, AddCommGroup (tangentSpace M)]
  [tmod : ∀ M, Module ℝ (tangentSpace M)]
  [tfin : ∀ M, FiniteDimensional ℝ (tangentSpace M)]
  inducedForm : ∀ M, tangentSpace M →ₗ[ℝ] tangentSpace M →ₗ[ℝ] ℂ
  Uk : ∀ {k : ℕ}, (Fin k → mC) → Prop
  uk_two : ∀ x : Fin 2 → mC,
    Uk x ↔ ¬ ((bilin (x 0 - x 1) (x 0 - x 1)).im = 0 ∧ (bilin (x 0 - x 1) (x 0 - x 1)).re ≤ 0)
  isDomainOfHolomorphy : ∀ {k : ℕ} {D : Type u}, (D → (Fin k → mC)) → Prop
```

The base domain `V̌_k` (lines 210-216):

```lean
def Vcheck [geom : MinkowskiComplexGeometry] {k : ℕ} (x : Fin k → geom.mC) : Prop :=
  Function.Injective x ∧
    ∃ M : geom.TotallyRealSub,
      (∀ i, x i ∈ geom.carrier M) ∧
      (∃ G : AllowableComplexMetric (geom.tangentSpace M),
          ∀ v w, G.toForm v w = geom.inducedForm M v w) ∧
      (∀ e : geom.Eucl, ∃ v, v ∈ geom.carrier M ∧ geom.projE v = e)
```

The witness structure, ALL fields (lines 232-268):

```lean
structure VacuumExpectationData [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [CobordismRealization] [geom : MinkowskiComplexGeometry]
    (T : FieldTheory) (hI : IsInvariant T)
    {o : gl.Obj} [MetCManifold (gl.Ambient o)] {xpt : gl.Ambient o} (O : Observables o xpt)
    (k : ℕ) where
  Fk : Type u
  basePts : Fk → (Fin k → geom.mC)
  basePts_mem : ∀ p : Fk, Vcheck (basePts p)
  basePts_surj : ∀ x : Fin k → geom.mC, Vcheck x → ∃ p : Fk, basePts p = x
  vkSetoid : Setoid Fk
  basePts_respects : ∀ p p' : Fk, vkSetoid.r p p' → basePts p = basePts p'
  Ek : Fk → MultilinearMap ℂ (fun _ : Fin k => O.Ox) ℂ
  Ek_respects : ∀ p p' : Fk, vkSetoid.r p p' → Ek p = Ek p'
  uk_subset_vcheck : ∀ x : Fin k → geom.mC, geom.Uk x → Vcheck x        -- ← Prop 5.4
```

The quotient and descents (lines 284-294):

```lean
def Vk (W : VacuumExpectationData T hI O k) : Type u :=
  Quotient W.vkSetoid

def projVk (W : VacuumExpectationData T hI O k) : W.Vk → (Fin k → geom.mC) :=
  Quotient.lift (s := W.vkSetoid) W.basePts W.basePts_respects

@[simp] theorem projVk_mk (W : VacuumExpectationData T hI O k) (p : W.Fk) :
    W.projVk (Quotient.mk W.vkSetoid p) = W.basePts p :=
  rfl
```

The `\leanok`'d theorem, statement + full proof (lines 323-326):

```lean
theorem Uk_subset_Vk (W : VacuumExpectationData T hI O k) (x : Fin k → geom.mC)
    (hx : geom.Uk x) : ∃ q : W.Vk, W.projVk q = x := by
  obtain ⟨p, hp⟩ := W.basePts_surj x (W.uk_subset_vcheck x hx)
  exact ⟨Quotient.mk W.vkSetoid p, by rw [W.projVk_mk]; exact hp⟩
```

---

## Why the current statement is wrong

`uk_subset_vcheck : ∀ x : Fin k → geom.mC, geom.Uk x → Vcheck x` **is** Proposition 5.4.
`Vcheck` is V̌_k, and by `basePts_mem` + `basePts_surj` the image of `basePts` is exactly
V̌_k, so the V̌_k-level inclusion and the V_k-level covering (`∃ q : Vk, projVk q = x`) are
the same claim up to quotient bookkeeping. The proof of `Uk_subset_Vk` consumes exactly the
assumed field, the surjection, and `Quotient.mk` — its two lines contain zero geometric
content. The file's own docstring says it outright (line 263-267): "**Proposition 5.4's
asserted content (KS PROVE this; Lean proof deferred PROSE)** ... CARRIED here as an asserted
field; the `V_k`-level inclusion `Uk_subset_Vk` is PROVED from it."

So the `\leanok`'d declaration does not state KS's proposition; it assumes KS's own theorem
as a hypothesis field of the structure and re-derives its trivial residue. That is precisely
the "never axiomatize KS's OWN theorems" violation — the axiomatize-infrastructure license
covers what KS *cite*, never what KS *prove*, and the ruled-manifold construction is KS's
proof. A marker flip cannot cure this: the statement/structure must change.

---

## THE CENTRAL QUESTION — sorry'd theorem vs `\notready` prose node

The faithful statement would be the inclusion KS's proof establishes:

```lean
theorem uk_subset_vcheck [geom : MinkowskiComplexGeometry] {k : ℕ}
    (x : Fin k → geom.mC) (hx : geom.Uk x) : Vcheck x := sorry   -- CANDIDATE (A)
```

(whence the V_k covering follows by the quotient bookkeeping, as now). The decision turns on
Q1 (is this TRUE at the encoding's generality?) and Q2 (can the proof's geometry even be
stated?).

### Q1: the standalone statement is FALSE in the axiomatized generality

The degeneracy from the 1-B finding is NOT an artifact of the field shape; it falsifies the
standalone statement too. Instance-level reasoning (meta-level — see the caveat below):

* Take the genuine built linear foundation `MinkowskiModel.minkowskiLinear` for the
  `MinkowskiLinear` part (`mC`, `bilin`, `Eucl`, `projE` all real and nondegenerate).
* Extend it to `MinkowskiComplexGeometry` degenerately:
  `TotallyRealSub := PEmpty`; `carrier`, `tangentSpace`, `inducedForm` by `PEmpty.elim`
  (the three bracketed instance fields are `∀ M, ...` over an empty type — vacuously
  satisfied); `Uk` defined at `k = 2` to be *exactly* `uk_two`'s right-hand side (which makes
  `uk_two` true by `Iff.rfl`) and `False` at every other `k`;
  `isDomainOfHolomorphy := fun _ => True`.
* This is a legal instance: no field of the class excludes it. `TotallyRealSub` has no
  pinning field (no nonemptiness, no "the graph of a smooth map E → iE is one", no
  constructor).
* In it, for every `x`: `Vcheck x = Function.Injective x ∧ ∃ M : PEmpty, ...` is **False**
  (empty existential). But `Uk`-true configurations **exist** at `k = 2`: in the genuine
  model take `x 0 - x 1 = a + ib` with `⟨a,b⟩ ≠ 0`, so `bilin(ξ,ξ) = ‖a‖² - ‖b‖² + 2i⟨a,b⟩`
  has nonzero imaginary part, and `uk_two`'s right-hand side holds.
* Hence `∀ x, geom.Uk x → Vcheck x` is **false** in this instance, so the typeclass-general
  candidate (A) is not a theorem — it is a false statement at that generality. A `sorry`
  under it would be permanently unclosable and, worse, would present as pending a claim the
  encoding actually refutes. Under the project's honesty rules that is a misstatement, not a
  deferral.

**Caveat (flagged, not settled):** this falsification is careful meta-reasoning, not a
compiled Lean counterexample — compiling one would require writing a concrete instance of an
assumed class, which the project's own constraints prohibit. I checked every field of
`MinkowskiComplexGeometry` against the degenerate assignments above; the reviewer should
re-check `uk_two`'s satisfiability reading (defining `Uk` at `k = 2` *as* the RHS is the
forced-consistent choice) before signing off.

### Q2: the ruled-manifold proof cannot be stated against the current geometry

The goal `geom.Uk x → Vcheck x` is *syntactically* statable (both predicates exist). But
KS's proof is not even attemptable, and the reasons show the geometry is too thin for the
statement to be the *faithful* one:

1. **No way to produce a totally-real submanifold.** `TotallyRealSub` is an opaque `Type u`
   with no constructor and no pinning field. Proving `Vcheck x` requires exhibiting
   `M : TotallyRealSub` — impossible in the abstract class (and in the degenerate instance
   there is none at all). The proof's central object, the ruled manifold swept by
   `x(t) + M_t`, has no counterpart: there is no "sweep" former taking a curve and a frame to
   a `TotallyRealSub` with computed `carrier`/`tangentSpace`/`inducedForm`.
2. **The reduction step is unusable.** "V_k is invariant under the complex orthogonal group
   ... so it is enough to consider Im(x_{i+1}-x_i) ∈ C" needs the complex orthogonal group
   (absent — the module header itself lists it as deferred) and the *general* definition of
   `Uk` (present only as an opaque predicate pinned at `k = 2` by `uk_two`; the
   suitably-ordered-γ characterization is prose-cited, not a field).
3. **Partially present:** the forward light-cone exists in the built `MinkowskiLinear`
   (nonempty, open, proper, a cone), but its convexity — needed for the polygonal-path
   smoothing — is explicitly left to `found:lorentzian-causal-geometry`.

So the typeclass-general sentence `Uk x → Vcheck x` is a *different, false* claim, not KS's
claim about the genuine Minkowski geometry. The faithful statement cannot currently be
truthfully written.

### RECOMMENDATION: (B) — `\notready` prose node

* Remove `uk_subset_vcheck` from `VacuumExpectationData`.
* Remove the theorem `Uk_subset_Vk` (its proof consumes the removed field; see build section).
  OPTIONALLY replace it with the honestly-named residue that *is* provable and assumes no KS
  content — the quotient bookkeeping alone:

  ```lean
  /-- Every base configuration in `V̌_k` is covered by a point of `V_k` — the quotient
  bookkeeping (`basePts_surj` + descent). NOT Proposition 5.4: no `U_k` appears; the
  inclusion `U_k ⊆ V̌_k` is the deferred ruled-manifold content (blueprint prose). -/
  theorem vcheck_covered (W : VacuumExpectationData T hI O k) (x : Fin k → geom.mC)
      (hx : Vcheck x) : ∃ q : W.Vk, W.projVk q = x := by
    obtain ⟨p, hp⟩ := W.basePts_surj x hx
    exact ⟨Quotient.mk W.vkSetoid p, by rw [W.projVk_mk]; exact hp⟩
  ```

* Blueprint: `prop:Vk-contains-Uk` keeps its faithful prose statement and proof sketch,
  drops `\leanok` for `\notready`, and its `\lean{}` annotation is either removed or
  repointed (open question 3). Record in the node's prose (or the status doc) the named
  missing pinning that would later enable option (A) against an honest geometry:
  (i) the complex orthogonal group of `m_C` + the general suitably-ordered-γ tube definition
  (unlocks KS's reduction), (ii) a ruled-submanifold former
  `sweep : (curve, frame) → TotallyRealSub` with computation rules for
  `carrier`/`tangentSpace`/`inducedForm` (infrastructure — smooth-manifold geometry KS cite),
  (iii) cone convexity (`found:lorentzian-causal-geometry`). The *allowability of the swept
  metric* must NOT be a field of any such extension — "the metric of M is clearly allowable"
  is a step of KS's proof, and assuming it would re-smuggle proof content exactly as
  `uk_subset_vcheck` did; it must be left as the (then-provable, Section-2-adjacent) proof
  obligation.

Option (A) as a typeclass-general sorry'd theorem is **rejected** on Q1 grounds (false, not
merely unproven). Option (A) against a future pinned geometry is possible later work, gated
on the maintainer's sorry-invariant decision (below).

---

## What happens to the existing theorem + structure (build implications)

**THIS IS THE KEY DIFFERENCE FROM NODE 1: the fix cannot leave the Lean surface unchanged
minus two fields — a green theorem loses its proof, and annotation/CI surfaces are hit.**

* **Consumers** (grep -rn over `KontsevichSegal/`, `blueprint/src/`, `blueprint/lean_decls`):
  every `.lean` hit for `uk_subset_vcheck` / `Uk_subset_Vk` is inside `VacuumDomain.lean`
  itself (header prose lines 27, 30, 69, 76-77, 93, 95, 108-109, 229; field docstring +
  declaration 263-268; theorem docstring + declaration 310-326). NO other `.lean` file
  references either name. Outside Lean: `blueprint/src/section5.tex:623` (`\lean{...}` names
  `WickRotation.VacuumExpectationData.Uk_subset_Vk`) and `blueprint/lean_decls:112` (same
  name).
* **Field removal**: `VacuumExpectationData` itself still builds (no other field mentions
  `uk_subset_vcheck`); `Vk`/`projVk`/`projVk_mk`/`EkOnVk`/`EkOnVk_mk`/`VkIsDomainOfHolomorphy`
  are all independent of it and still build.
* **`Uk_subset_Vk` does NOT still build** — line 325 consumes `W.uk_subset_vcheck`. The edit
  must delete the theorem (recommended, with the optional `vcheck_covered` residue above) or
  sorry it (rejected: Q1 — the sorry would sit under a statement false at this generality,
  and the theorem's current statement conditions on `W`, which after the field removal no
  longer implies the inclusion at all).
* **Sorry count — LOUD FLAG**: under recommendation (B) the build stays green with
  **sorry = 0 preserved** (deletion + a fully-proved residue). Under any (A) variant a
  `sorry` appears and the project's standing "sorry = 0" invariant breaks (0 → 1) — README /
  status-doc surfaces that advertise sorry-free-ness would need updating, and per the
  faithful rule the (A)-typeclass variant is barred anyway; only an (A)-with-pinned-geometry
  variant could ever carry an honest sorry. That trade is a maintainer call, not mine.
* **checkdecls / lean_decls**: `checkdecls` is a real lake dependency (`lakefile.toml:19-20`),
  and `blueprint/lean_decls:112` lists `WickRotation.VacuumExpectationData.Uk_subset_Vk`.
  Deleting the theorem without fixing `section5.tex:623` and regenerating
  `blueprint/lean_decls` (via `leanblueprint web`) leaves a dangling name → `lake exe
  checkdecls` fails. The fix commit must therefore touch: `VacuumDomain.lean` +
  `section5.tex` (marker AND `\lean{}` line) + regenerated `lean_decls` (133 → 132 lines, or
  same count if repointed to `vcheck_covered`) + regenerated graph.
* **Module header surgery** (as in node 1): the header's "TWO UNPROVEN STATEMENTS OF
  DIFFERENT EPISTEMIC STATUS" block (lines 22-41), discipline #2/#4/#5 narrations (90-110),
  the deferral list (128-130), and CONSTRAINTS (132-136) all defend the asserted-field +
  proved-corollary encoding and must be rewritten to record the restatement. Note
  discipline #2 currently claims "`Uk_subset_Vk` then forces `V̌_k` nonempty wherever `U_k`
  is" — that non-vacuity interlock DISAPPEARS with the field and must not survive in prose.
* **`def:vacuum-domain` (adjacent node)**: its `\lean{}` names the structure/defs, not the
  field, so its annotation is untouched; removing an asserted theorem-content field from what
  is supposed to be a *definition* structure arguably improves that node's own fidelity. Its
  marker is not this fix's business (flagged for the reviewer to confirm no change).

---

## Fidelity check

**(a) The recommended shape states Prop 5.4 — where it can.** Under (B) the claim "V_k
contains U_k" lives exactly once: in the blueprint node's prose (which quotes the paper's
statement and reproduces the ruled-manifold proof as the proof sketch), marked `\notready` =
"faithful statement not yet expressible" — which is the true situation, per Q1/Q2 the honest
reading of the no-approximations policy ("use a placeholder ONLY when the faithful statement
cannot be expressed at all", with the real claim + the missing infrastructure named). The
Lean keeps everything that IS honestly statable: `Vcheck` (a real def matching KSTeX
769-775's (i)+(ii)), the quotient `V_k` with its descents, and (optionally) the
`vcheck_covered` bookkeeping. No Lean declaration any longer *assumes* the inclusion.

**(b) Adversarial pass.**

* The honest cost of (B), stated plainly: after the fix the repo contains **no Lean assertion
  of Proposition 5.4 at all** — strictly less Lean content than today. But today's Lean
  content is an *assumption* dressed as a theorem; removing a false credential is not a loss
  of formalization. The alternative that keeps a Lean assertion (A-typeclass) states a
  falsehood; there is no third option that keeps both honesty and a Lean statement today.
* `vcheck_covered` degeneracy: it is genuinely proved, but it is bookkeeping — its PROVED
  status must not leak into the node's marking or prose as if Prop 5.4 were partially proved.
  Its docstring (above) says "NOT Proposition 5.4" explicitly.
* Statement-vacuity vs inhabitation-degeneracy: the (B) blueprint prose is a statement about
  the genuine geometry and is not inhabited at all in Lean, so the degeneracy axis does not
  arise; the residue lemma is non-vacuous relative to its own (modest) claim (`basePts_surj`
  makes it bite against "π misses part of V̌_k").

---

## Proof status / marking after restatement

**Recommendation: `\notready` on the statement** (necessarily: no `\leanok` is available for
a claim with no faithful Lean statement), proof side unmarked. This is forced by the faithful
rule, not chosen for convenience — but note the tension explicitly: (B) preserves the
"sorry = 0" invariant *because* it retreats to prose; the only path that ever puts Prop 5.4
back in Lean as a statement (pinned-geometry (A)) breaks sorry = 0 the day it lands unless
the ruled-manifold proof is completed at the same time. The maintainer should decide now
which is the standing preference, so node 2/5's fix doesn't get re-litigated later.

---

## Open questions for human review

1. **The sorry-count decision (the big one):** does the project accept, in the future, a
   sorry'd Prop 5.4 against a properly pinned geometry (sorry 0 → 1, honest and closeable),
   or must the node stay `\notready` prose until the proof can land whole? This artifact
   recommends (B) *today* on falsity grounds; it deliberately does not decide the future
   policy.
2. **Residue lemma:** keep `vcheck_covered` (preserves the genuinely-proved quotient
   bookkeeping under an honest name) or delete `Uk_subset_Vk` with no replacement? I
   recommend keeping it; it is the only part of today's "proof" that was ever real.
3. **The `\lean{}` annotation on the `\notready` node:** drop it entirely (cleanest —
   `lean_decls` shrinks by one and `checkdecls` stays green) or repoint to
   `WickRotation.VacuumExpectationData.vcheck_covered` (rigged-triple precedent exists for
   `\lean` + `\notready`, but the residue does not state the node — risk of the same
   misattribution this fix removes). I lean toward DROP; flagged, not decided.
4. **Geometry pinning in scope?** Whether building the (A)-enabling extension — complex
   orthogonal group + general tube definition, the `sweep` former with computation rules,
   cone convexity — is in scope (b) at all, and if so where it sits in the roadmap
   (`found:lorentzian-causal-geometry` / `found:scv-tube-domain` walls). Also confirm my
   red line that the swept metric's *allowability* must remain a proof obligation, never a
   field.
5. **The Q1 falsification is meta-level** (no compiled counterexample; compiling one would
   need a concrete instance of an assumed class, which the project bans). Confirm this
   standard of evidence suffices for the restatement decision.
6. **`def:vacuum-domain`:** confirm its marker/annotation is untouched by this fix (my
   reading: yes — the field removal only improves that node's definitional purity).
7. **Header discipline #2 rewrite:** the non-vacuity interlock narrative loses its
   "`Uk_subset_Vk` forces V̌_k nonempty" leg; confirm the rewritten header may simply record
   the weaker true interlock (`uk_two` pins `U_k`; `basePts_mem/surj` pin `im(π) = V̌_k`)
   without inventing a substitute bite.
