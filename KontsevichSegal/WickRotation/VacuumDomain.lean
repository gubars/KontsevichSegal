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

THE DEFINING REQUIREMENT: TWO UNPROVEN STATEMENTS OF DIFFERENT EPISTEMIC STATUS, encoded as VISIBLY
DISTINCT declarations.
* **Proposition 5.4 (`prop:Vk-contains-Uk`): `U_k ⊆ V_k`.** KS PROVE this (the ruled-manifold
  construction, KSTeX 811-813). In scope (a) it is a STATED theorem whose Lean proof is
  deferred-additive PROSE (exactly like Theorem 5.2 / Principle 5.1). It IS claimed to hold. Encoded
  as the CARRIED/ASSERTED field `VacuumExpectationData.uk_subset_vcheck` (the geometric content KS
  prove, at the provable `V̌_k` level: every `U_k` configuration lies on an allowable totally-real
  ruled `M`), with the ruled-manifold proof recorded as prose; the `V_k`-level inclusion theorem
  `Uk_subset_Vk` is then PROVED from it (axiom-clean). So Prop 5.4 appears as: an asserted field +
  a proved corollary.
* **The domain-of-holomorphy claim: `V_k` is a domain of holomorphy.** KS explicitly have NO proof —
  "Unfortunately we have no proof that `V_k` is a domain of holomorphy" (KSTeX 799). This is an OPEN
  CONJECTURE, not a theorem of the paper. Encoded as the stand-alone `def
  VacuumExpectationData.VkIsDomainOfHolomorphy : Prop`, which is NEVER asserted, NEVER a `theorem`,
  and NEVER `sorry`'d (a `sorry`'d theorem would falsely claim a provable-in-principle result; it is
  not one). It is a SEPARATE declaration from the witness data, marked in its docstring as KS's open
  conjecture.
The reader sees at a glance: Prop 5.4 = stated theorem (asserted field + proved corollary, proof
deferred — KS have one); domain-of-holomorphy = conjecture (a `def : Prop`, never asserted — KS have
none).

THE ENCODING (scope (a): STATE the data; the infinite-dim-manifold / ruled-manifold constructions are
deferred prose, never `sorry`'d).

* `MinkowskiComplexGeometry` — the assumed ambient geometry of complexified Minkowski space `m_C`
  (a complex vector space with the ℂ-bilinear Minkowski form `bilin`, the Euclidean `Eucl = ℝ^d` with
  the projection `projE`, the totally-real submanifolds with their real tangent and induced complex
  form, the opaque permuted-extended-tube predicate `Uk` with its `k = 2` characterization, and the
  assumed domain-of-holomorphy predicate). Infrastructure-to-axiomatize (KS cite the tube-domain and
  Stein-manifold material as known; Section 2 deferred it): a `class` of assumed operations, no
  `axiom` keyword, no instance.

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
  `Ek_respects` (E_k constant on the quotient classes, by Principle 5.1 / `hI`); and
  `uk_subset_vcheck` (Prop 5.4's asserted `V̌_k`-level content).

* `VacuumExpectationData.Vk := Quotient vkSetoid` — `V_k` as the Hausdorff quotient of `F_k` by the
  same-image relation. `projVk := Quotient.lift basePts basePts_respects` and `EkOnVk := Quotient.lift
  Ek Ek_respects` are PROVED (axiom-clean) descents of `π` and `E_k` to `V_k`: `E_k` descends because
  it is invariant on the classes (`Ek_respects`, tied to Principle 5.1).

* `VacuumExpectationData.Uk_subset_Vk` (Prop 5.4, PROVED) — `∀ x, Uk x → ∃ q : Vk, projVk q = x`:
  every `U_k` configuration is covered by a point of `V_k`. Reduces to the carried `uk_subset_vcheck`
  (the ruled-manifold content) + `basePts_surj` (`π` surjects onto `V̌_k`) + the quotient descent.

* `VacuumExpectationData.VkIsDomainOfHolomorphy` (the CONJECTURE) — `geom.isDomainOfHolomorphy
  projVk`: the assertion that the spread `V_k → (m_C)^k` is a domain of holomorphy. A `def : Prop`,
  NEVER asserted/proved/`sorry`'d.

THE FIVE STANDING DISCIPLINES.
1. FLOAT-FREE JOIN. `V̌_k`'s "lies on a totally-real `M` with allowable metric" ties to Section 2's
   `AllowableComplexMetric` via the carried existential `∃ G, G.toForm = inducedForm M` (not a free
   "some manifold"). `E_k`'s fibre-constancy (`Ek_respects`) ties to node 5's `IsInvariant` (carried
   `hI`, Principle 5.1; not a free "is constant"). `basePts`/`basePts_mem` tie `F_k`'s base map to the
   projection landing in `V̌_k`. The `Hom(O^⊗k; ℂ)` target ties `O` to node 8's `Observables.Ox`.
2. NON-VACUITY. The degenerate satisfiers are `U_k = ∅`, `V̌_k = ∅`, `V_k = everything`. `uk_two` pins
   `Uk` (at `k = 2`) to the SATISFIABLE bilinear condition (`‖x₀−x₁‖²` not real-and-`≤ 0`), so `U_k`
   is not free-empty; `basePts_mem` forces `π`'s image into `V̌_k` (so `V_k` does NOT map onto all of
   `(m_C)^k`); `basePts_mem`+`basePts_surj` tie `F_k`'s image EXACTLY to `V̌_k`, and `Uk_subset_Vk`
   then forces `V̌_k` nonempty wherever `U_k` is (for `k = 2`, by `uk_two`). The fields interlock to
   exclude the hollows; `Uk_subset_Vk` has genuine content (excludes `V_k` too small / `U_k` empty).
3. EQUATE-vs-DISTINGUISH. `V_k`'s quotient equivalence (same image iff same fibre-component /
   path-joined) is the EQUATE — carried as `vkSetoid : Setoid Fk`, sameness. The local-diffeomorphism
   / Hausdorff-maximality is the DISTINGUISHING property of which setoid; the opaque quotient blocks
   stating it, so it is DEFERRED (named reason below). No distinctness field is added that would
   contradict the quotient identification.
4. TRIVIAL-SATISFIABILITY NUANCE. Unlike the identity-content nodes 5/7/9/10 (where the symmetric /
   trivial model is the CORRECT one), Prop 5.4 is a genuine INCLUSION/containment (`U_k ⊆ V_k`), NOT
   an identity assertion. So the empty model (`U_k = ∅`) is a VACUITY to EXCLUDE, not a correct
   trivial model: the inclusion must bite against "`V_k` too small", which `uk_two` (the nonempty
   `k = 2` tube) and the `basePts_mem`/`_surj` interlock secure.
5. VERIFICATION POSTURE. The conjecture is VISIBLY a conjecture (a `def : Prop`, never asserted, never
   `sorry`'d, docstring-marked), not a deferred-proof theorem. Prop 5.4 is STATED (the carried field
   `uk_subset_vcheck`, ruled-manifold proof deferred prose) and its genuinely-reducible part is PROVED
   (`Uk_subset_Vk` from the carried `V̌_k`-level field; `EkOnVk` the descent of `E_k` from the
   invariance field) — axiom-clean, like `eval_orderIndep` / `propCheck_eq`.

GEOMETRY / DEFERRALS (assumed, documented; no concrete instance, never the `axiom` keyword, never
`sorry`). Each named: `m_C` (complexified Minkowski) with the splitting `m_C = E ⊕ iE` and the
ℂ-bilinear form; the Euclidean `E = ℝ^d` and the projection `m_C → E` (carried as the plain map
`projE`, its real-linearity/along-`iE` structure deferred); totally-real submanifolds with their real
tangent and induced complex form (the manifold geometry deferred, the induced metric TIED to
`AllowableComplexMetric`); the complex orthogonal group of `m_C` and the forward light-cone (used in
the general permuted-tube definition of `Uk`, carried opaque with the explicit `k = 2`
characterization, the general one in prose); `U_k` and Proposition 2.3 (Section-2 tube-domain
material, not formalized, prose-cited); `F_k` as an infinite-dim complex manifold and `V_k` as the
Hausdorff local-diffeo quotient (Mathlib gap: infinite-dim complex manifolds + the local-diffeo /
Hausdorff-maximality of the quotient, the latter the distinguishing property of `vkSetoid`); `E_k`'s
holomorphicity (the Section-3 holomorphicity gap); the notion "domain of holomorphy" (Stein manifolds
/ holomorphic envelopes, Mathlib gap, carried as the assumed predicate `isDomainOfHolomorphy`); and
the Proposition 5.4 ruled-manifold proof (complex-orthogonal + reordering invariance reduce to
`Im(x_{i+1} − x_i)` in the forward cone, smooth the polygonal path, sweep the ruled `M` from
orthonormal frames orthogonal to `x'(t)`, its metric allowable — deferred prose).

CONSTRAINTS: no `axiom` keyword, no concrete instance of an assumed class, no `sorry` (the conjecture
is a stated `def : Prop` never asserted; Prop 5.4 is a stated theorem with prose proof; the descents
and the inclusion that genuinely reduce to carried fields are PROVED axiom-clean). Reuses Section 2's
`AllowableComplexMetric`, node 5's `IsInvariant`, node 8's `Observables.Ox`, and `Function.Injective`
for `Conf_k`, with their real signatures.

Blueprint: `def:vacuum-domain` and `prop:Vk-contains-Uk` in `blueprint/src/section5.tex` (their
`\lean` annotations land with the content-node annotation batch, like nodes 5-10).
-/

import KontsevichSegal.WickRotation.ObservableAction

namespace WickRotation

open Cobordism

universe u

/-! ## The complexified-Minkowski ambient geometry (assumed; deferred) -/

/-- **Assumed (KS Section 5 / Section 2 infrastructure): complexified Minkowski space `m_C` and the
tube-domain data.** The ambient geometry of the closing conjecture: `m_C = ℝ^{d-1,1} ⊗ ℂ` with its
ℂ-bilinear Minkowski form, the Euclidean subspace `E = ℝ^d` of the splitting `m_C = E ⊕ iE`, the
totally-real submanifolds with their real tangent and induced complex metric, the Wightman permuted
extended tube `Uk`, and the notion of a domain of holomorphy. Infrastructure-to-axiomatize: KS cite
this as known and Section 2 deferred the tube-domain material; encoded as a `class` of assumed
operations (never the `axiom` keyword, no instance). -/
class MinkowskiComplexGeometry where
  /-- Complexified Minkowski space `m_C` (a complex vector space, ℂ-dimension `d`). -/
  mC : Type u
  [acg : AddCommGroup mC]
  [mod : Module ℂ mC]
  /-- The ℂ-bilinear extension of the Minkowski form; `‖v‖² := bilin v v`. -/
  bilin : mC →ₗ[ℂ] mC →ₗ[ℂ] ℂ
  /-- The Minkowski form is symmetric. -/
  bilin_symm : ∀ v w, bilin v w = bilin w v
  /-- The real Euclidean subspace `E = ℝ^d` of `m_C = E ⊕ iE` (where the observables live). -/
  Eucl : Type u
  [eacg : AddCommGroup Eucl]
  [emod : Module ℝ Eucl]
  /-- The projection `m_C → E` along `iE` (its real-linearity is deferred geometry; the plain map
  suffices to state the surjectivity condition (ii) of `V̌_k`). -/
  projE : mC → Eucl
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

attribute [instance] MinkowskiComplexGeometry.acg MinkowskiComplexGeometry.mod
  MinkowskiComplexGeometry.eacg MinkowskiComplexGeometry.emod MinkowskiComplexGeometry.tacg
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

/-- **The vacuum-expectation witness data (KS Section 5, blueprint `def:vacuum-domain` /
`prop:Vk-contains-Uk`).** For a field theory `T` with Principle 5.1 (`hI : IsInvariant T`) and the
observables `O` at a point of `E` (node 8), the data of `F_k`, the projection `π`, the quotient
relation defining `V_k`, the vacuum expectation `E_k`, and the asserted content of Proposition 5.4.

`Fk` is the space of pairs `(M, x)` (an infinite-dim complex manifold, deferred); `basePts` is `π`
(forget `M`), landing in (`basePts_mem`) and surjecting onto (`basePts_surj`) `V̌_k`; `vkSetoid` is
the "same image in `V_k`" equivalence (the EQUATE); `Ek` is the vacuum expectation valued in
`Hom(O^⊗k; ℂ) = MultilinearMap ℂ (fun _ => O.Ox) ℂ`, constant on the quotient classes by Principle
5.1 (`Ek_respects`, by `hI`); `uk_subset_vcheck` is Proposition 5.4's asserted `V̌_k`-level content
(the ruled-manifold construction, proof deferred prose). Not constructed for any concrete
theory. -/
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
  /-- **Proposition 5.4's asserted content (KS PROVE this; Lean proof deferred PROSE).** The
  `V̌_k`-level inclusion `U_k ⊆ V̌_k`: every permuted-extended-tube configuration lies on an
  allowable totally-real ruled manifold, hence is in `V̌_k`. This is the geometric content KS
  establish by the ruled-manifold construction (KSTeX 811-813), CARRIED here as an asserted field;
  the `V_k`-level inclusion `Uk_subset_Vk` is PROVED from it. -/
  uk_subset_vcheck : ∀ x : Fin k → geom.mC, geom.Uk x → Vcheck x

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

/-! ## Proposition 5.4 (PROVED from the carried content) -/

/-- **Proposition 5.4 (KS Section 5, blueprint `prop:Vk-contains-Uk`): `U_k ⊆ V_k` (PROVED).** Every
Wightman permuted-extended-tube configuration is covered by a point of `V_k`: for `x ∈ U_k` there is
`q : V_k` with `projVk q = x`.

PROVED by reducing to the carried `uk_subset_vcheck` (Proposition 5.4's `V̌_k`-level geometric
content — the ruled-manifold construction, KS's proof, deferred prose) together with `basePts_surj`
(`π` surjects onto `V̌_k`) and the quotient descent: `uk_subset_vcheck` puts `x` in `V̌_k`,
`basePts_surj` lifts it to a pair `p : F_k`, and `⟦p⟧ : V_k` projects back to `x`.

This is a genuine INCLUSION (not an identity), so the empty model is a vacuity to exclude, not a
trivial model: with `uk_two` pinning `U_k` to the nonempty `k = 2` tube, the inclusion bites against
"`V_k` too small". The ruled-manifold construction itself stays deferred prose (KS have the proof;
the Lean proof is additive, scope (a)). -/
theorem Uk_subset_Vk (W : VacuumExpectationData T hI O k) (x : Fin k → geom.mC)
    (hx : geom.Uk x) : ∃ q : W.Vk, W.projVk q = x := by
  obtain ⟨p, hp⟩ := W.basePts_surj x (W.uk_subset_vcheck x hx)
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
