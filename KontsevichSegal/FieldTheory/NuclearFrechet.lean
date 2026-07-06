/- Nuclear Fréchet spaces and nuclear (trace-class) maps: the first analytic
infrastructure object for Section 3 of the Kontsevich-Segal paper
(arXiv:2105.10161).

This is INFRASTRUCTURE-TO-AXIOMATIZE, in the sense of CLAUDE.md's "Deliverable
scope and Section 3 strategy": Kontsevich and Segal cite the theory of nuclear
spaces as known and do not develop it. We therefore encode the assumed
properties as `class` declarations (never the `axiom` keyword), reusing Mathlib
for the parts it genuinely provides, and we construct no instance.

Blueprint: `def:nuclear-frechet` in `blueprint/src/section3.tex`. The blueprint
node lists four assumed properties of these spaces:
  (1) inverse limits of nuclear maps of Fréchet spaces stay nuclear Fréchet;
  (2) a unique natural tensor product (projective = injective);
  (3) the strong dual of a nuclear Fréchet space is nuclear and reflexive;
  (4) a nuclear endomorphism has a well-defined trace.

What Mathlib provides and what is assumed here:
  - Fréchet space: Mathlib has no single `FrechetSpace` class, but it has all
    the ingredients (`CompleteSpace`, `TopologicalSpace.MetrizableSpace`,
    `LocallyConvexSpace`, `IsUniformAddGroup`, `ContinuousSMul`). We bundle
    them into `FrechetSpace`. This is reuse, not assumption.
  - Nuclear (trace-class) map: not in Mathlib. We give the faithful
    representation-based definition `IsNuclearMap` (it is a genuine definition,
    not an assumption).
  - Nuclear space / nuclear Fréchet space: not in Mathlib. Defined faithfully
    (`IsNuclearSpace`, `IsNuclearFrechetSpace`) via the standard criterion that
    every continuous linear map into a Banach space is nuclear.
  - Property (3): encoded as the assumed `class NuclearFrechetDuality`, using
    Mathlib's `StrongDual`.
  - Properties (1), (2): encoded below as assumed-property classes over genuine
    system data (blueprint node `found:tvs-limits-tensor`): countable inverse
    and direct systems of nuclear maps of Fréchet spaces
    (`CountableNuclearInverseSystem`, `CountableNuclearDirectSystem`, genuine
    definitions) with assumed limits (`HasNuclearInverseLimit`,
    `HasNuclearDirectLimit`) and the assumed completed tensor product
    (`HasCompletedNuclearTensor`), each pinned float-free by a universal
    property. No instance is constructed.
  - Property (4), the trace: DEFERRED, not encoded. A faithful encoding needs a
    partial functional with a characterizing law whose consistency must be set
    up with care (a total trace on all of `E →L[ℂ] E` would be inconsistent in
    infinite dimension). Per CLAUDE.md we note this rather than assume it. See
    `docs/project_status.md`.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Analysis.LocallyConvex.Bounded

/-! ## Fréchet spaces -/

/-- A **complex Fréchet space**: a complete, metrizable, locally convex
topological `ℂ`-vector space (KS paper Section 3).

Mathlib has no single `FrechetSpace` class, so this bundles the existing Mathlib
conditions. Local convexity is the real-scalar notion `LocallyConvexSpace ℝ E`,
so the carrier is required to be a real vector space compatibly with its complex
structure (`Module ℝ E`, `IsScalarTower ℝ ℂ E`), as is standard in Mathlib for
locally convex complex spaces. This is reuse of Mathlib, not an assumption. -/
class FrechetSpace (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [UniformSpace E] : Prop extends
    IsUniformAddGroup E, ContinuousSMul ℂ E, LocallyConvexSpace ℝ E,
    CompleteSpace E, TopologicalSpace.MetrizableSpace E

/-! ## Nuclear maps -/

/-- A continuous linear map `T : E → F` between topological `ℂ`-vector spaces is
**nuclear** (trace-class) if it admits a representation
`T x = ∑ₙ λₙ · φₙ(x) · yₙ` with `∑ₙ ‖λₙ‖ < ∞`, the functionals `φₙ`
equicontinuous, and the vectors `yₙ` von Neumann bounded (KS paper Section 3).

This is the faithful definition, not an assumption; Mathlib has no notion of
nuclear map for general topological vector spaces. -/
def IsNuclearMap {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (T : E →L[ℂ] F) : Prop :=
  ∃ (lam : ℕ → ℂ) (φ : ℕ → (E →L[ℂ] ℂ)) (y : ℕ → F),
    Summable (fun n => ‖lam n‖) ∧
    Equicontinuous (fun n => (φ n : E → ℂ)) ∧
    Bornology.IsVonNBounded ℂ (Set.range y) ∧
    ∀ x, T x = ∑' n, (lam n * φ n x) • y n

/-- A topological `ℂ`-vector space is **nuclear** if every continuous linear map
from it into a Banach space is nuclear (KS paper Section 3, the standard
criterion). Stated for Banach targets in `Type`; this is the usual testing
class. Faithful definition, not an assumption. -/
def IsNuclearSpace (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] :
    Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F), IsNuclearMap T

/-- A **nuclear Fréchet space**: a Fréchet space that is nuclear (KS paper
Section 3). The downstream limit spaces `Ê_Σ` of a field theory are of this
kind. Faithful definition; only `FrechetSpace` reuses Mathlib, and `nuclear`
is the standard nuclearity criterion. -/
class IsNuclearFrechetSpace (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [UniformSpace E] : Prop extends FrechetSpace E where
  /-- Every continuous linear map into a Banach space is nuclear. -/
  nuclear : IsNuclearSpace E

/-! ## Assumed property: duality

Blueprint property (3): the strong dual of a nuclear Fréchet space is nuclear,
and the space is reflexive. This is a known theorem in the theory of nuclear
spaces, assumed here (not proved). It is encoded as a `class` of assumed
properties, never the `axiom` keyword, and we construct no instance. -/

/-- **Assumed (KS paper Section 3, blueprint `def:nuclear-frechet` property 3).**
For a nuclear Fréchet space `E`, the strong dual `StrongDual ℂ E` is again a
nuclear space (though in general not metrizable, hence not Fréchet), and `E` is
reflexive: it is topologically isomorphic to its strong bidual.

The reflexivity field assumes the existence of a topological linear isomorphism
to the bidual; the sharper statement that the canonical evaluation map is an
isomorphism is the intended content. This `class` records assumed theorems; it
is not constructed for any concrete space. -/
class NuclearFrechetDuality (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [UniformSpace E] [IsNuclearFrechetSpace E] : Prop where
  /-- The strong dual of a nuclear Fréchet space is nuclear. -/
  dual_isNuclear : IsNuclearSpace (StrongDual ℂ E)
  /-- A nuclear Fréchet space is reflexive: it is topologically isomorphic to
  its strong bidual. -/
  reflexive : Nonempty (E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E))

/-! ## Assumed structures: countable limits and the completed tensor product

Blueprint node `found:tvs-limits-tensor` (KS paper Section 3): the three
operations the paper uses but cites as known — countable inverse limits
`Ê_Σ = varprojlim E_{Σ''}`, countable direct limits `Ě_Σ = varinjlim E_{Σ'}`,
and the unique completed tensor product of nuclear spaces. Mathlib provides
none of them (it has only algebraic tensor products, algebraic direct limits,
and finite-rank traces), so each is encoded as a `class` of assumed properties
(never the `axiom` keyword) pinned float-free by a universal property, with no
instance constructed. The system carriers below are genuine definitions; only
the `Has...` classes are assumed. -/

/-- **A countable inverse system of nuclear maps of Fréchet spaces** (KS paper
Section 3). A tower `⋯ → X_{n+1} → X_n → ⋯ → X_0` of Fréchet spaces whose
connecting maps are nuclear: the shape of the downstream system `E_{Σ''}` of a
field theory, whose inverse limit is `Ê_Σ`. Genuine data, not an assumption. -/
structure CountableNuclearInverseSystem where
  /-- The tower of spaces. -/
  X : ℕ → Type*
  [addCommGroup : ∀ n, AddCommGroup (X n)]
  [moduleComplex : ∀ n, Module ℂ (X n)]
  [moduleReal : ∀ n, Module ℝ (X n)]
  [tower : ∀ n, IsScalarTower ℝ ℂ (X n)]
  [uniform : ∀ n, UniformSpace (X n)]
  [frechet : ∀ n, FrechetSpace (X n)]
  /-- The connecting maps of the tower. -/
  d : ∀ n, X (n + 1) →L[ℂ] X n
  /-- Each connecting map is nuclear (trace-class). -/
  d_nuclear : ∀ n, IsNuclearMap (d n)

attribute [instance] CountableNuclearInverseSystem.addCommGroup
  CountableNuclearInverseSystem.moduleComplex CountableNuclearInverseSystem.moduleReal
  CountableNuclearInverseSystem.tower CountableNuclearInverseSystem.uniform
  CountableNuclearInverseSystem.frechet

/-- **Assumed (KS paper Section 3, blueprint `found:tvs-limits-tensor`).** The
inverse limit `L = varprojlim S.X` of a countable inverse system of nuclear
maps of Fréchet spaces. The `nuclearFrechet` field is the paper's nuclearity
preservation — "`Ê_Σ`, being the inverse limit of a countable sequence of
nuclear maps of Fréchet spaces, is a nuclear Fréchet space" (blueprint
`def:nuclear-frechet` property 1) — ASSUMED, not proved.

The limit itself is pinned float-free by the universal property `isLimit`:
every compatible cone of continuous linear maps out of a topological
`ℂ`-module factors uniquely through `L`. The test class is all topological
`ℂ`-modules, the broadest available: the intended model (the closed subspace of
the product `Π n, S.X n` with the initial topology) factors cones from
arbitrary topological modules, and testing against `L` itself makes the pin
unique up to the usual isomorphism. This `class` records assumed structure
(never the `axiom` keyword); no instance is constructed for any concrete
tower. -/
class HasNuclearInverseLimit (S : CountableNuclearInverseSystem) where
  /-- The limit space `varprojlim S.X`. -/
  L : Type*
  [addCommGroup : AddCommGroup L]
  [moduleComplex : Module ℂ L]
  [moduleReal : Module ℝ L]
  [tower : IsScalarTower ℝ ℂ L]
  [uniform : UniformSpace L]
  /-- ASSUMED nuclearity preservation: the countable inverse limit of nuclear
  maps of Fréchet spaces is a nuclear Fréchet space. -/
  [nuclearFrechet : IsNuclearFrechetSpace L]
  /-- The limit projections. -/
  π : ∀ n, L →L[ℂ] S.X n
  /-- The projections form a cone over the tower. -/
  π_compat : ∀ n, (S.d n).comp (π (n + 1)) = π n
  /-- The universal property: every compatible cone out of a topological
  `ℂ`-module factors uniquely through `L`. -/
  isLimit : ∀ (C : Type*) [AddCommGroup C] [Module ℂ C] [TopologicalSpace C]
    (c : ∀ n, C →L[ℂ] S.X n), (∀ n, (S.d n).comp (c (n + 1)) = c n) →
    ∃! h : C →L[ℂ] L, ∀ n, (π n).comp h = c n

attribute [instance] HasNuclearInverseLimit.addCommGroup
  HasNuclearInverseLimit.moduleComplex HasNuclearInverseLimit.moduleReal
  HasNuclearInverseLimit.tower HasNuclearInverseLimit.uniform
  HasNuclearInverseLimit.nuclearFrechet

/-- **A countable direct system of nuclear maps of Fréchet spaces** (KS paper
Section 3). A chain `X_0 → X_1 → ⋯ → X_n → X_{n+1} → ⋯` of Fréchet spaces
whose connecting maps are nuclear: the shape of the upstream system `E_{Σ'}`
of a field theory, whose direct limit is `Ě_Σ`. Genuine data, not an
assumption. -/
structure CountableNuclearDirectSystem where
  /-- The chain of spaces. -/
  X : ℕ → Type*
  [addCommGroup : ∀ n, AddCommGroup (X n)]
  [moduleComplex : ∀ n, Module ℂ (X n)]
  [moduleReal : ∀ n, Module ℝ (X n)]
  [tower : ∀ n, IsScalarTower ℝ ℂ (X n)]
  [uniform : ∀ n, UniformSpace (X n)]
  [frechet : ∀ n, FrechetSpace (X n)]
  /-- The connecting maps of the chain. -/
  i : ∀ n, X n →L[ℂ] X (n + 1)
  /-- Each connecting map is nuclear (trace-class). -/
  i_nuclear : ∀ n, IsNuclearMap (i n)

attribute [instance] CountableNuclearDirectSystem.addCommGroup
  CountableNuclearDirectSystem.moduleComplex CountableNuclearDirectSystem.moduleReal
  CountableNuclearDirectSystem.tower CountableNuclearDirectSystem.uniform
  CountableNuclearDirectSystem.frechet

/-- **Assumed (KS paper Section 3, blueprint `found:tvs-limits-tensor`).** The
direct (inductive) limit `L = varinjlim S.X` of a countable direct system of
nuclear maps of Fréchet spaces, in the locally convex sense. Mirroring the
paper's `Ě_Σ` (and the `ECheck` treatment in `FieldTheory.lean`), `L` is
assumed NUCLEAR (`nuclear`, a plain field since `IsNuclearSpace` is a
`Prop`-valued definition, not a class) but carries only the bare complex-TVS
instances: `Ě_Σ` is in general not metrizable, so `L` is NOT asserted Fréchet.
The paper alternatively reaches `Ě_Σ` as the strong dual `(Ê_{Σ*})*` (KS paper
Section 3 Appendix); that identification is stated on the field theory in
`DualConjugate.lean` and `ConjugateDualDuality.lean`.

The universal property `isColimit` quantifies over locally convex complex TVS,
NOT over all topological modules: the locally convex inductive-limit topology
is the finest LOCALLY CONVEX topology making the inclusions continuous, which
is in general coarser than the plain final linear topology, so compatible
cocones factor continuously through locally convex targets only — quantifying
over all TVS would be false of the intended model. Uniqueness needs no
separation hypothesis because the algebraic colimit is the union of the images
of the `ι n`. This `class` records assumed structure (never the `axiom`
keyword); no instance is constructed for any concrete chain. -/
class HasNuclearDirectLimit (S : CountableNuclearDirectSystem) where
  /-- The colimit space `varinjlim S.X`. -/
  L : Type*
  [addCommGroup : AddCommGroup L]
  [moduleComplex : Module ℂ L]
  [topology : TopologicalSpace L]
  /-- ASSUMED: the countable direct limit of nuclear maps of Fréchet spaces is
  nuclear (in general not metrizable, hence NOT asserted Fréchet). -/
  nuclear : IsNuclearSpace L
  /-- The colimit inclusions. -/
  ι : ∀ n, S.X n →L[ℂ] L
  /-- The inclusions form a cocone over the chain. -/
  ι_compat : ∀ n, (ι (n + 1)).comp (S.i n) = ι n
  /-- The universal property: every compatible cocone into a locally convex
  complex TVS factors uniquely through `L`. -/
  isColimit : ∀ (C : Type*) [AddCommGroup C] [Module ℂ C] [Module ℝ C]
    [IsScalarTower ℝ ℂ C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    [ContinuousSMul ℂ C] [LocallyConvexSpace ℝ C]
    (c : ∀ n, S.X n →L[ℂ] C), (∀ n, (c (n + 1)).comp (S.i n) = c n) →
    ∃! h : L →L[ℂ] C, ∀ n, h.comp (ι n) = c n

attribute [instance] HasNuclearDirectLimit.addCommGroup
  HasNuclearDirectLimit.moduleComplex HasNuclearDirectLimit.topology

/-- **Assumed (KS paper Section 3, blueprint `found:tvs-limits-tensor`).** The
completed tensor product `T = E ⊗̂ F` of two nuclear spaces: "there is a unique
natural concept of tensor product here, because all the vector spaces are
nuclear" (KS paper Section 3). The factors' nuclearity is carried as the
fields `nuclearE`, `nuclearF` (rather than as hypotheses on the parameters)
because `IsNuclearSpace` is a `Prop`-valued definition, not a class. `T` is
assumed nuclear (`nuclear`) and COMPLETE (`complete`): completeness is what
"completed" means, and without it the uncompleted tensor product would wrongly
satisfy this interface.

The universal property `isTensor` pins `T` and encodes the uniqueness of the
tensor product: every curried continuous bilinear map into a complete
Hausdorff locally convex complex TVS factors uniquely through `tmul`.
Completeness of the target is needed to extend the factorization from the
dense image of the algebraic tensor product, and Hausdorffness makes that
extension unique; both match the completed tensor product's actual universal
property. On the intended arguments — the nuclear Fréchet spaces `Ê_Σ` and
their duals `Ě_Σ` — separately continuous bilinear maps are jointly
continuous, so the curried form agrees with the paper's bilinear one. This
`class` records assumed structure (never the `axiom` keyword); no instance is
constructed for any concrete pair. -/
class HasCompletedNuclearTensor (E F : Type*)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] where
  /-- The left factor is nuclear. -/
  nuclearE : IsNuclearSpace E
  /-- The right factor is nuclear. -/
  nuclearF : IsNuclearSpace F
  /-- The completed tensor product `E ⊗̂ F`. -/
  T : Type*
  [addCommGroup : AddCommGroup T]
  [moduleComplex : Module ℂ T]
  [uniform : UniformSpace T]
  [uniformAddGroup : IsUniformAddGroup T]
  [continuousSMul : ContinuousSMul ℂ T]
  /-- ASSUMED: the completed tensor product is complete. -/
  [complete : CompleteSpace T]
  /-- ASSUMED: the completed tensor product of nuclear spaces is nuclear. -/
  nuclear : IsNuclearSpace T
  /-- The canonical continuous bilinear map `(x, y) ↦ x ⊗ y`, curried. -/
  tmul : E →L[ℂ] F →L[ℂ] T
  /-- The universal property: every curried continuous bilinear map into a
  complete Hausdorff locally convex complex TVS factors uniquely through
  `tmul`. This is also what makes the tensor product unique. -/
  isTensor : ∀ (G : Type*) [AddCommGroup G] [Module ℂ G] [Module ℝ G]
    [IsScalarTower ℝ ℂ G] [UniformSpace G] [IsUniformAddGroup G]
    [ContinuousSMul ℂ G] [LocallyConvexSpace ℝ G] [CompleteSpace G] [T2Space G]
    (b : E →L[ℂ] F →L[ℂ] G),
    ∃! h : T →L[ℂ] G, ∀ x y, h (tmul x y) = b x y

attribute [instance] HasCompletedNuclearTensor.addCommGroup
  HasCompletedNuclearTensor.moduleComplex HasCompletedNuclearTensor.uniform
  HasCompletedNuclearTensor.uniformAddGroup HasCompletedNuclearTensor.continuousSMul
  HasCompletedNuclearTensor.complete

/-! ## Deferred assumed property: the trace

Of the four assumed properties of blueprint `def:nuclear-frechet`, the trace
(property 4) remains NOT encoded, to avoid faking or risking inconsistency: a
nuclear endomorphism has a well-defined trace, but a faithful, non-vacuous, and
consistent encoding requires a partial functional on the nuclear endomorphisms
together with a characterizing law (for example its value on rank-one maps); a
total trace on all of `E →L[ℂ] E` would be inconsistent in infinite dimension.
This is deferred rather than assumed, and recorded in
`docs/project_status.md`. -/
