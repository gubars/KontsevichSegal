/- The domain of holomorphicity of the vacuum expectation values: the ELEVENTH and LAST Lean node
of Section 5 of the Kontsevich-Segal paper (arXiv:2105.10161). Encodes blueprint nodes
`def:vacuum-domain` and `prop:Vk-contains-Uk`. This is the paper's closing conjecture, the only node
that leaves the cobordism picture for the traditional Minkowski-space treatment of Wightman vacuum
expectation values; it reuses Section 2's allowable metrics, node 5's invariance principle, and node
8's observables.

KS, "The domain of holomorphicity of the vacuum expectation values" (KSTeX 759-813). The Wightman
axioms make the `k`-point functions boundary values of holomorphic functions on the `permuted
extended tube` `U_k ⊂ (m_C)^k` (Section 2; for `k = 2`, the pairs `(x,y)` with `‖x−y‖²` not a real
number `≤ 0`). For `k > 2`, `U_k` is not holomorphically convex, so it is not the largest manifold
`V_k` to which the expectation values continue; describing `V_k` is an old open problem. This paper's
candidate: `V_k` sits over the open set `V̌_k` of distinct `k`-tuples `x` of `m_C` lying on some
totally-real submanifold `M` with (i) the induced metric on `M` ALLOWABLE (Section 2), and (ii) `M`
surjecting onto the Euclidean `E = ℝ^d ⊂ m_C = E ⊕ iE`. `F_k` is the space of pairs `(M, x)`, an
infinite-dim complex manifold with open projection `π : F_k → V̌_k`; `V_k` is the largest Hausdorff
quotient of `F_k` through which `π` factors by a local diffeomorphism. A holomorphic theory with a
Lorentz-invariant vacuum has vacuum expectation values `E_k : F_k → Hom(O^⊗k; ℂ)` (`O` the
observables at a point of `E`); by Principle 5.1 `E_k` is constant on the connected components of the
fibres of `π`, so it descends to `V_k`.

THE DEFINING REQUIREMENT: TWO UNPROVEN STATEMENTS OF DIFFERENT EPISTEMIC STATUS.
* **Proposition 5.4 (`prop:Vk-contains-Uk`): `U_k ⊆ V_k`.** KS PROVE this (the ruled-manifold
  construction, KSTeX 811-813). It is NOT formalized here: it lives as `\notready` blueprint prose
  (statement + proof sketch), because no faithful Lean statement of it is currently expressible —
  see RESTATEMENT below. Nothing in this file asserts, assumes, or proves it.
* **The domain-of-holomorphy claim: `V_k` is a domain of holomorphy.** KS explicitly have NO proof —
  "Unfortunately we have no proof that `V_k` is a domain of holomorphy" (KSTeX 799). This is an OPEN
  CONJECTURE, not a theorem of the paper. Encoded as the stand-alone `def
  VacuumExpectationData.VkIsDomainOfHolomorphy : Prop`, which is NEVER asserted, NEVER a `theorem`,
  and NEVER `sorry`'d (a `sorry`'d theorem would falsely claim a provable-in-principle result; it is
  not one). It is a SEPARATE declaration from the witness data, marked in its docstring as KS's open
  conjecture.
The reader sees at a glance: Prop 5.4 = unformalized paper theorem (`\notready` blueprint prose —
KS have a proof; the encoding cannot yet state it); domain-of-holomorphy = conjecture (a
`def : Prop`, never asserted — KS have none).

RESTATEMENT (2026-07-27). The previous encoding carried Proposition 5.4 as the ASSERTED field
`uk_subset_vcheck : ∀ x, geom.Uk x → Vcheck x` of `VacuumExpectationData`, and "proved" the
`V_k`-level inclusion `Uk_subset_Vk` from it (field + `basePts_surj` + `Quotient.mk` — zero
geometric content of its own). That axiomatized KS's OWN theorem (audit verdict (b) RESTATEMENT,
2026-07-27): the field IS Prop 5.4 at the `V̌_k` level, and `basePts_mem`/`basePts_surj` make
`V̌_k` exactly the image of `π`, so the `V̌_k`-inclusion and the `V_k`-covering are the same claim
up to quotient bookkeeping. Both the field and the theorem were REMOVED. A standalone sorry'd
`∀ x, Uk x → Vcheck x` was REJECTED: at the axiomatized generality it is FALSE (a degenerate
instance with `TotallyRealSub := PEmpty` over the genuine built linear model has `Uk`-true
configurations at `k = 2` by `uk_two`, while `Vcheck` is everywhere false), and the ruled-manifold
proof is not attemptable (no complex orthogonal group; `Uk` opaque beyond `k = 2`; no constructor
produces a `TotallyRealSub`; cone convexity deferred). What remains in Lean is the honest residue
`vcheck_covered` (the quotient bookkeeping "`V̌_k` is covered by `V_k`", fully proved, NOT
Prop 5.4). Reviewed proposal: `blueprint/restatements/prop-Vk-contains-Uk.md`. The blueprint node
is `\notready` with its `\lean` annotation DROPPED. When Prop 5.4 is later formalized against a
pinned geometry (complex orthogonal group + the general suitably-ordered-γ tube definition; a
ruled-submanifold former with carrier/tangent/inducedForm computation rules; cone convexity), the
swept metric's ALLOWABILITY must remain a PROOF OBLIGATION, never an assumed field — assuming it
would re-import proof content exactly as `uk_subset_vcheck` did.

THE ENCODING (scope (a): STATE the data; the infinite-dim-manifold / ruled-manifold constructions are
deferred prose, never `sorry`'d).

* `MinkowskiComplexGeometry` — the ambient geometry of complexified Minkowski space `m_C`. Its
  LINEAR-ALGEBRA part (the complex vector space `m_C`, the ℂ-bilinear Minkowski form `bilin`, the
  Euclidean `Eucl = ℝ^d` with the splitting `m_C = E ⊕ iE` and the projection `projE`) is the BUILT
  foundation `MinkowskiLinear` (blueprint `found:minkowski-linear`, `MinkowskiLinear.lean`), realized
  by the genuine model `MinkowskiModel.minkowskiLinear`; this class `extends` it. What remains
  assumed is the deferred geometry: the totally-real submanifolds with their real tangent and induced
  complex form (`found:real-analytic-complexification`), the opaque permuted-extended-tube predicate
  `Uk` with its `k = 2` characterization, and the domain-of-holomorphy predicate
  (`found:scv-tube-domain`). Infrastructure-to-axiomatize (KS cite the tube-domain and Stein-manifold
  material as known; Section 2 deferred it): no `axiom` keyword, no instance.

* `Vcheck x` (`V̌_k`) — the base predicate: `x` is a tuple of DISTINCT points (`Function.Injective x`,
  Conf_k) lying on some totally-real `M` with (i) `∃ G : AllowableComplexMetric (tangent M), G.toForm =
  inducedForm M` (the TIE to Section 2, node-8 `IsAllowableSubspace` pattern), and (ii) `M` surjecting
  onto `Eucl` via `projE`. KS's content, built as a real `def`.

* `VacuumExpectationData T hI O k` — the witness data: `Fk` (the pairs `(M, x)`, an assumed
  infinite-dim complex manifold), `basePts : Fk → (Fin k → m_C)` (the projection `π`, forgetting `M`)
  with `basePts_mem`/`basePts_surj` (`π` lands in and surjects onto `V̌_k`); `vkSetoid : Setoid Fk`
  (the "same image in `V_k`" equivalence — same fibre-component / path-covering — carried as the
  EQUATE); `Ek : Fk → MultilinearMap ℂ (fun _ : Fin k => O.Ox) ℂ` (the vacuum expectation `E_k`,
  target `Hom(O^⊗k; ℂ)` via the node-9 tensor-as-multilinear pattern, `O = O.Ox` node 8) with
  `Ek_respects` (E_k constant on the quotient classes, by Principle 5.1 / `hI`). Proposition 5.4
  is NOT a field (RESTATEMENT above).

* `VacuumExpectationData.Vk := Quotient vkSetoid` — `V_k` as the Hausdorff quotient of `F_k` by the
  same-image relation. `projVk := Quotient.lift basePts basePts_respects` and `EkOnVk := Quotient.lift
  Ek Ek_respects` are PROVED (axiom-clean) descents of `π` and `E_k` to `V_k`: `E_k` descends because
  it is invariant on the classes (`Ek_respects`, tied to Principle 5.1).

* `VacuumExpectationData.vcheck_covered` (the honest residue, PROVED) — `∀ x, Vcheck x →
  ∃ q : Vk, projVk q = x`: every base configuration in `V̌_k` is covered by a point of `V_k`. Pure
  quotient bookkeeping (`basePts_surj` + the descent). NOT Proposition 5.4: no `U_k` appears; the
  inclusion `U_k ⊆ V̌_k` is the deferred ruled-manifold content (blueprint prose).

* `VacuumExpectationData.VkIsDomainOfHolomorphy` (the CONJECTURE) — `geom.isDomainOfHolomorphy
  projVk`: the assertion that the spread `V_k → (m_C)^k` is a domain of holomorphy. A `def : Prop`,
  NEVER asserted/proved/`sorry`'d.

THE FIVE STANDING DISCIPLINES.
1. FLOAT-FREE JOIN. `V̌_k`'s "lies on a totally-real `M` with allowable metric" ties to Section 2's
   `AllowableComplexMetric` via the carried existential `∃ G, G.toForm = inducedForm M` (not a free
   "some manifold"). `E_k`'s fibre-constancy (`Ek_respects`) ties to node 5's `IsInvariant` (carried
   `hI`, Principle 5.1; not a free "is constant"). `basePts`/`basePts_mem` tie `F_k`'s base map to the
   projection landing in `V̌_k`. The `Hom(O^⊗k; ℂ)` target ties `O` to node 8's `Observables.Ox`.
2. NON-VACUITY (WEAKENED by the restatement, honestly). `uk_two` pins `Uk` (at `k = 2`) to the
   SATISFIABLE bilinear condition (`‖x₀−x₁‖²` not real-and-`≤ 0`), so `U_k` is not free-empty;
   `basePts_mem` forces `π`'s image into `V̌_k` (so `V_k` does NOT map onto all of `(m_C)^k`);
   `basePts_mem`+`basePts_surj` tie `F_k`'s image EXACTLY to `V̌_k`. The former further interlock,
   "`Uk_subset_Vk` forces `V̌_k` nonempty wherever `U_k` is", DISAPPEARED with the removed field:
   nothing in Lean now relates `U_k` to `V̌_k`, and `V̌_k = ∅` (e.g. `Fk` empty) is a legal
   degenerate model. That gap IS Proposition 5.4, deferred to blueprint prose, not papered over
   with a substitute field.
3. EQUATE-vs-DISTINGUISH. `V_k`'s quotient equivalence (same image iff same fibre-component /
   path-joined) is the EQUATE — carried as `vkSetoid : Setoid Fk`, sameness. The local-diffeomorphism
   / Hausdorff-maximality is the DISTINGUISHING property of which setoid; the opaque quotient blocks
   stating it, so it is DEFERRED (named reason below). No distinctness field is added that would
   contradict the quotient identification.
4. TRIVIAL-SATISFIABILITY NUANCE. Unlike the identity-content nodes 5/7/9/10 (where the symmetric /
   trivial model is the CORRECT one), Prop 5.4 is a genuine INCLUSION/containment (`U_k ⊆ V_k`), NOT
   an identity assertion, so a Lean statement of it must BITE against "`V_k` too small". The
   current geometry cannot support that bite: `TotallyRealSub` is opaque and constructor-free, so
   the inclusion is FALSE in degenerate instances and no faithful biting statement exists yet. That
   is why the node retreats to `\notready` prose rather than to a sorry'd theorem.
5. VERIFICATION POSTURE. The conjecture is VISIBLY a conjecture (a `def : Prop`, never asserted, never
   `sorry`'d, docstring-marked), not a deferred-proof theorem. Prop 5.4 is VISIBLY unformalized
   (`\notready` blueprint prose; no Lean declaration states, assumes, or proves it). What is PROVED
   is only the genuinely provable: the descents (`projVk`, `EkOnVk`) and the quotient bookkeeping
   (`vcheck_covered`) — axiom-clean, like `eval_orderIndep` / `propCheck_eq`.

GEOMETRY / DEFERRALS (assumed, documented; no concrete instance, never the `axiom` keyword, never
`sorry`). NOW BUILT (no longer deferred): `m_C` (complexified Minkowski) with the splitting
`m_C = E ⊕ iE`, the ℂ-bilinear Minkowski form, the Euclidean `E = ℝ^d`, and the projection
`m_C → E` — all the linear algebra of the built foundation `MinkowskiLinear` (`MinkowskiLinear.lean`,
blueprint `found:minkowski-linear`), realized by `MinkowskiModel.minkowskiLinear`; the forward
light-cone is also exhibited there (nonempty, open, proper, a cone), its convexity left to
`found:lorentzian-causal-geometry`. STILL DEFERRED, each named: totally-real submanifolds with their
real tangent and induced complex form (the manifold geometry deferred, the induced metric TIED to
`AllowableComplexMetric`); the complex orthogonal group of `m_C` (used in
the general permuted-tube definition of `Uk`, carried opaque with the explicit `k = 2`
characterization, the general one in prose); `U_k` and Proposition 2.3 (Section-2 tube-domain
material, not formalized, prose-cited); `F_k` as an infinite-dim complex manifold and `V_k` as the
Hausdorff local-diffeo quotient (Mathlib gap: infinite-dim complex manifolds + the local-diffeo /
Hausdorff-maximality of the quotient, the latter the distinguishing property of `vkSetoid`); `E_k`'s
holomorphicity (the Section-3 holomorphicity gap); the notion "domain of holomorphy" (Stein manifolds
/ holomorphic envelopes, Mathlib gap, carried as the assumed predicate `isDomainOfHolomorphy`); and
Proposition 5.4 itself with its ruled-manifold proof (complex-orthogonal + reordering invariance
reduce to `Im(x_{i+1} − x_i)` in the forward cone, smooth the polygonal path, sweep the ruled `M`
from orthonormal frames orthogonal to `x'(t)`, its metric allowable) — since the 2026-07-27
restatement the STATEMENT as well as the proof is deferred, to `\notready` blueprint prose.

CONSTRAINTS: no `axiom` keyword, no concrete instance of an assumed class, no `sorry` (the conjecture
is a stated `def : Prop` never asserted; Prop 5.4 is `\notready` blueprint prose, neither stated nor
assumed in Lean; the descents and the quotient bookkeeping are PROVED axiom-clean). Reuses Section 2's
`AllowableComplexMetric`, node 5's `IsInvariant`, node 8's `Observables.Ox`, and `Function.Injective`
for `Conf_k`, with their real signatures.

Blueprint: `def:vacuum-domain` (annotated) and `prop:Vk-contains-Uk` (`\notready`, its `\lean`
annotation dropped with the 2026-07-27 restatement) in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.ObservableAction
import KontsevichSegal.WickRotation.MinkowskiLinear

namespace WickRotation

open Cobordism

universe u

/-! ## The complexified-Minkowski ambient geometry (assumed; deferred) -/

/-- **The complexified-Minkowski ambient geometry of the closing conjecture.** The LINEAR-ALGEBRA
part (complexified Minkowski space `m_C = ℝ^{d-1,1} ⊗ ℂ` with its ℂ-bilinear Minkowski form, the
Euclidean subspace `E = ℝ^d` of `m_C = E ⊕ iE`, and the projection `projE`) is the BUILT foundation
`MinkowskiLinear` (blueprint `found:minkowski-linear`, realized by the model
`MinkowskiModel.minkowskiLinear`), extended here. What remains ASSUMED is the deferred geometry: the
totally-real submanifolds with their real tangent and induced complex metric
(`found:real-analytic-complexification`), the Wightman permuted extended tube `Uk`, and the notion
of a domain of holomorphy (`found:scv-tube-domain`). KS cite the latter as known and Section 2
deferred
the tube-domain material; encoded as a `class` extending the built linear algebra with assumed
operations (never the `axiom` keyword, no instance). -/
class MinkowskiComplexGeometry extends MinkowskiLinear where
  /-- The totally-real `d`-submanifolds `M ⊂ m_C` (deferred geometry). -/
  TotallyRealSub : Type u
  /-- The point set of a totally-real submanifold. -/
  carrier : TotallyRealSub → Set mC
  /-- The real tangent model of `M`: a finite-dimensional real vector space `V` (the space on which
  the induced complex metric, an `AllowableComplexMetric`, lives). -/
  tangentSpace : TotallyRealSub → Type u
  [tacg : ∀ M, AddCommGroup (tangentSpace M)]
  [tmod : ∀ M, Module ℝ (tangentSpace M)]
  [tfin : ∀ M, FiniteDimensional ℝ (tangentSpace M)]
  /-- The complex bilinear form induced on `M`'s tangent from `bilin` (the induced metric data;
  condition (i) of `V̌_k` ties this to `AllowableComplexMetric`). -/
  inducedForm : ∀ M, tangentSpace M →ₗ[ℝ] tangentSpace M →ₗ[ℝ] ℂ
  /-- The Wightman **permuted extended tube** `U_k` (opaque): `x ∈ U_k` iff, after a suitable
  reordering, some element `γ` of the complex orthogonal group puts `Im(γ(x_i − x_{i+1}))` in the
  forward light-cone for each `i` (Section 2, prose-cited; the complex orthogonal group + cone are
  deferred geometry). The explicit `k = 2` case is pinned by `uk_two`. -/
  Uk : ∀ {k : ℕ}, (Fin k → mC) → Prop
  /-- The `k = 2` characterization of `U_k` (Section 2): `‖x₀ − x₁‖²` is NOT a real number `≤ 0`,
  i.e. its imaginary part is nonzero or its real part is positive. This pins `U_k` to a satisfiable
  concrete condition (non-vacuity). -/
  uk_two : ∀ x : Fin 2 → mC,
    Uk x ↔ ¬ ((bilin (x 0 - x 1) (x 0 - x 1)).im = 0 ∧ (bilin (x 0 - x 1) (x 0 - x 1)).re ≤ 0)
  /-- **Assumed (Mathlib gap): the "domain of holomorphy" property** of a spread `p : D → (m_C)^k`
  (a complex manifold `D` mapping to `(m_C)^k` by a local biholomorphism). Stein manifolds /
  holomorphic envelopes / domains of holomorphy at this generality are not in Mathlib; KS cite the
  notion as known. Carried as an assumed predicate, used ONLY to STATE the closing conjecture. -/
  isDomainOfHolomorphy : ∀ {k : ℕ} {D : Type u}, (D → (Fin k → mC)) → Prop

attribute [instance] MinkowskiComplexGeometry.tacg
  MinkowskiComplexGeometry.tmod MinkowskiComplexGeometry.tfin

/-! ## The base configuration domain `V̌_k` -/

/-- **The base configuration domain `V̌_k` (KS Section 5, blueprint `def:vacuum-domain`).** A tuple
`x` of `k` points of `m_C` is in `V̌_k` when the points are DISTINCT (`Function.Injective x`, the
configuration space `Conf_k(m_C)`) and lie on some totally-real submanifold `M` with

* (i) the induced metric on `M` ALLOWABLE — `∃ G : AllowableComplexMetric (tangentSpace M)` whose
  `toForm` is the `inducedForm` of `M` (the load-bearing TIE to Section 2's allowable metrics, the
  node-8 `IsAllowableSubspace` pattern), and
* (ii) `M` projecting surjectively onto the Euclidean `E` (`projE` hits every point of `Eucl`).

The totally-real submanifold geometry is deferred; condition (i) is tied to
`AllowableComplexMetric`, not a free "some manifold". -/
def Vcheck [geom : MinkowskiComplexGeometry] {k : ℕ} (x : Fin k → geom.mC) : Prop :=
  Function.Injective x ∧
    ∃ M : geom.TotallyRealSub,
      (∀ i, x i ∈ geom.carrier M) ∧
      (∃ G : AllowableComplexMetric (geom.tangentSpace M),
          ∀ v w, G.toForm v w = geom.inducedForm M v w) ∧
      (∀ e : geom.Eucl, ∃ v, v ∈ geom.carrier M ∧ geom.projE v = e)

/-! ## The witness data: `F_k`, `π`, the quotient relation, `E_k`, and Proposition 5.4's content -/

/-- **The vacuum-expectation witness data (KS Section 5, blueprint `def:vacuum-domain`).** For a
field theory `T` with Principle 5.1 (`hI : IsInvariant T`) and the observables `O` at a point of
`E` (node 8), the data of `F_k`, the projection `π`, the quotient relation defining `V_k`, and the
vacuum expectation `E_k`.

`Fk` is the space of pairs `(M, x)` (an infinite-dim complex manifold, deferred); `basePts` is `π`
(forget `M`), landing in (`basePts_mem`) and surjecting onto (`basePts_surj`) `V̌_k`; `vkSetoid` is
the "same image in `V_k`" equivalence (the EQUATE); `Ek` is the vacuum expectation valued in
`Hom(O^⊗k; ℂ) = MultilinearMap ℂ (fun _ => O.Ox) ℂ`, constant on the quotient classes by Principle
5.1 (`Ek_respects`, by `hI`). Proposition 5.4 is NOT a field: the former `uk_subset_vcheck`
axiomatized KS's own theorem and was removed (RESTATEMENT 2026-07-27, module header). Not
constructed for any concrete theory. -/
structure VacuumExpectationData [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
    [HolomorphicComplexification] [CobordismRealization] [geom : MinkowskiComplexGeometry]
    (T : FieldTheory) (hI : IsInvariant T)
    {o : gl.Obj} [MetCManifold (gl.Ambient o)] {xpt : gl.Ambient o} (O : Observables o xpt)
    (k : ℕ) where
  /-- `F_k`: the pairs `(M, x)` satisfying (i),(ii); an infinite-dim complex manifold (deferred). -/
  Fk : Type u
  /-- The projection `π : F_k → V̌_k ⊂ Conf_k(m_C)`, forgetting `M` (the marked points). -/
  basePts : Fk → (Fin k → geom.mC)
  /-- `π` lands in `V̌_k`: each pair's configuration lies in the base domain. -/
  basePts_mem : ∀ p : Fk, Vcheck (basePts p)
  /-- `π` surjects onto `V̌_k`: every base configuration lifts to a pair `(M, x)`. (`V̌_k` IS the
  image of `π`, by definition; load-bearing for the `V_k`-level inclusion.) -/
  basePts_surj : ∀ x : Fin k → geom.mC, Vcheck x → ∃ p : Fk, basePts p = x
  /-- The "same image in `V_k`" equivalence on `F_k`: two pairs `(M, x), (M', x)` are identified
  when in one connected component of the fibre, or joined to a common third pair by paths covering
  the same path in `V̌_k` (the further identifications making the quotient Hausdorff). The EQUATE
  (sameness); the local-diffeo / Hausdorff-maximality of which setoid is deferred. -/
  vkSetoid : Setoid Fk
  /-- The base map respects the quotient: pairs with the same `V_k` image have the same marked
  points (since `V_k → V̌_k` is a local diffeomorphism). Lets `π` descend to `V_k`. -/
  basePts_respects : ∀ p p' : Fk, vkSetoid.r p p' → basePts p = basePts p'
  /-- The vacuum expectation `E_k : F_k → Hom(O^⊗k; ℂ)`, with `Hom(O^⊗k; ℂ)` encoded as the
  multilinear maps `O.Ox^k → ℂ` (node 9's tensor-as-multilinear pattern; `O = O.Ox` is node 8's
  observables). Construction (holomorphic section trivialized by `M → E`) deferred. -/
  Ek : Fk → MultilinearMap ℂ (fun _ : Fin k => O.Ox) ℂ
  /-- **E_k is constant on the quotient classes (Principle 5.1).** Pairs with the same `V_k` image
  have the same vacuum expectation: moving `M` in the allowable class with `x` fixed does not change
  `E_k`. The fibre-constancy KS derive from Principle 5.1 (node 5); carried, tied to `hI`. It lets
  `E_k` descend to `V_k`. -/
  Ek_respects : ∀ p p' : Fk, vkSetoid.r p p' → Ek p = Ek p'

namespace VacuumExpectationData

variable [gc : CobordismGeometry] [gl : LorentzianCobordismGeometry]
  [HolomorphicComplexification] [CobordismRealization] [geom : MinkowskiComplexGeometry]
  {T : FieldTheory} {hI : IsInvariant T} {o : gl.Obj} [MetCManifold (gl.Ambient o)]
  {xpt : gl.Ambient o} {O : Observables o xpt} {k : ℕ}

/-! ## `V_k` as the Hausdorff quotient, and the descents of `π` and `E_k` -/

/-- **`V_k` (KS Section 5, blueprint `def:vacuum-domain`).** The largest Hausdorff quotient of `F_k`
through which `π` factors by a local diffeomorphism, encoded as the quotient of `F_k` by the
same-image relation `vkSetoid`. The local-diffeomorphism / Hausdorff-maximality characterization of
the relation is deferred (it is the distinguishing property of `vkSetoid`); the quotient itself is
the genuine object. -/
def Vk (W : VacuumExpectationData T hI O k) : Type u :=
  Quotient W.vkSetoid

/-- The projection `V_k → V̌_k ⊂ (m_C)^k` (the local diffeomorphism), the descent of `π` to `V_k`.
PROVED: `π` factors through the quotient because it respects the relation (`basePts_respects`). -/
def projVk (W : VacuumExpectationData T hI O k) : W.Vk → (Fin k → geom.mC) :=
  Quotient.lift (s := W.vkSetoid) W.basePts W.basePts_respects

@[simp] theorem projVk_mk (W : VacuumExpectationData T hI O k) (p : W.Fk) :
    W.projVk (Quotient.mk W.vkSetoid p) = W.basePts p :=
  rfl

/-- **The vacuum expectation `E_k` descends to `V_k` (PROVED).** Because `E_k` is constant on the
quotient classes (`Ek_respects`, by Principle 5.1), it factors through the quotient `V_k = F_k /
vkSetoid` as a holomorphic function on `V_k`. This is the descent KS describe ("`E_k` is constant on
the connected components of the fibres of `π`, so it descends"). -/
def EkOnVk (W : VacuumExpectationData T hI O k) :
    W.Vk → MultilinearMap ℂ (fun _ : Fin k => O.Ox) ℂ :=
  Quotient.lift (s := W.vkSetoid) W.Ek W.Ek_respects

@[simp] theorem EkOnVk_mk (W : VacuumExpectationData T hI O k) (p : W.Fk) :
    W.EkOnVk (Quotient.mk W.vkSetoid p) = W.Ek p :=
  rfl

/-! ## The `V̌_k`-covering residue (quotient bookkeeping; Prop 5.4 itself is unformalized) -/

/-- Every base configuration in `V̌_k` is covered by a point of `V_k` — the quotient
bookkeeping (`basePts_surj` + descent). NOT Proposition 5.4: no `U_k` appears; the
inclusion `U_k ⊆ V̌_k` is the deferred ruled-manifold content (blueprint prose). -/
theorem vcheck_covered (W : VacuumExpectationData T hI O k) (x : Fin k → geom.mC)
    (hx : Vcheck x) : ∃ q : W.Vk, W.projVk q = x := by
  obtain ⟨p, hp⟩ := W.basePts_surj x hx
  exact ⟨Quotient.mk W.vkSetoid p, by rw [W.projVk_mk]; exact hp⟩

/-! ## The closing conjecture (stated, NEVER asserted) -/

/-- **KS's OPEN CONJECTURE (KS Section 5, KSTeX 799): `V_k` is a domain of holomorphy.** The closing
question of the paper. KS write: "Unfortunately we have no proof that `V_k` is a domain of
holomorphy." This is a CONJECTURE, NOT a theorem of the paper, and it is encoded as a stated
`Prop` — the assertion that the spread `projVk : V_k → (m_C)^k` is a domain of holomorphy — that is
**never asserted, never a `theorem`, and never `sorry`'d**. A `sorry`'d theorem would falsely
present it as a provable-in-principle result awaiting a proof; KS have no proof and do not claim it
is provable. It is deliberately a separate `def` from the asserted witness data and from
Proposition 5.4 (which KS DO prove). The notion "domain of holomorphy" is the assumed
`isDomainOfHolomorphy` predicate (Mathlib gap). -/
def VkIsDomainOfHolomorphy (W : VacuumExpectationData T hI O k) : Prop :=
  geom.isDomainOfHolomorphy W.projVk

end VacuumExpectationData

end WickRotation
