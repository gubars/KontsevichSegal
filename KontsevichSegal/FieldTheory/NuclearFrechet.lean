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
  - Properties (1), (2), (4): DEFERRED, not encoded here. Stating them
    faithfully needs infrastructure Mathlib lacks (the inverse limit of a tower
    of topological vector spaces; the completed/projective topological tensor
    product of topological vector spaces), and, for the trace, a partial
    functional with a characterizing law whose consistency must be set up with
    care (a total trace on all of `E →L[ℂ] E` would be inconsistent in infinite
    dimension). Per CLAUDE.md we note these rather than assume them. See
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

/-! ## Deferred assumed properties

The remaining three properties of the blueprint node are NOT encoded here, to
avoid faking or risking inconsistency:

* **Inverse-limit closure** (property 1): the inverse limit of a countable tower
  of nuclear maps of Fréchet spaces is again nuclear Fréchet. Stating this needs
  the inverse limit of a diagram of topological vector spaces, which Mathlib
  does not provide for this setting.

* **Unique tensor product** (property 2): nuclear spaces have a unique natural
  tensor product, the projective and injective topological tensor products
  coinciding. Mathlib has only the algebraic `TensorProduct` and normed-space
  tensor seminorms; the completed topological tensor product of general
  topological vector spaces is not available.

* **Trace** (property 4): a nuclear endomorphism has a well-defined trace. A
  faithful, non-vacuous, and consistent encoding requires a partial functional
  on the nuclear endomorphisms together with a characterizing law (for example
  its value on rank-one maps); a total trace on all of `E →L[ℂ] E` would be
  inconsistent in infinite dimension. This is deferred rather than assumed.

These are recorded in `docs/project_status.md`. -/
