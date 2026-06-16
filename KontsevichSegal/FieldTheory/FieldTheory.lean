/- A field theory as a (holomorphic) functor: the central node of Section 3 of
the Kontsevich-Segal paper (arXiv:2105.10161).

This node states the BARE functor and its induced limit structure ONLY. The four
conditions of the boxed definition (holomorphicity, continuity, tensor,
unitarity) are encoded in their own later nodes, NOT here. Per the
Category vs. functor boundary (CLAUDE.md), in particular the
injective-dense-image "continuity" condition belongs on the functor's continuity
node, not here and not on the cobordism category.

CONTENT vs. INFRASTRUCTURE. Like the cobordism-category node, the categorical
content (the functor: object-map, morphism-map, composition preservation) is
CONSTRUCTED, while what rests on missing Mathlib infrastructure is deferred.

Mathlib's `CategoryTheory.Functor` does NOT apply here: it is a functor between
`Category` instances, and a `Category` requires identity morphisms (its
`CategoryStruct` parent has `id : X ⟶ X`) and a `map_id` law. The cobordism
source is a `Semicategory` (no identities; see `Cobordism/Category.lean`), and
the target category of Fréchet spaces and nuclear maps also has no identities
(the identity of an infinite-dimensional space is not nuclear). So we build the
honest `SemicategoryFunctor`: object-map + composition-preserving morphism-map,
with NO identity law, just as `Semicategory` itself was built for lack of a
Mathlib equivalent.

Spaces (faithful to the blueprint `def:field-theory`):
  - `E_Σ` is a Fréchet space, PROVISIONAL, and is NOT asserted nuclear. It exists
    to construct the limit spaces between which it is sandwiched.
  - `Ê_Σ = lim←` is a NUCLEAR FRÉCHET space.
  - `Ě_Σ = lim→` is NUCLEAR but in general NOT metrizable, hence not Fréchet
    (we do not assert `FrechetSpace` on it).
The actual limit CONSTRUCTION (`Ê_Σ = varprojlim E_Σ''`, `Ě_Σ = varinjlim E_Σ'`)
needs inverse/direct limits of topological vector spaces, which Mathlib lacks
(the same gap the nuclear node found). It is DEFERRED; the asserted structure
(which space is nuclear-Fréchet, which is nuclear-non-metrizable, and the
canonical maps `Ě_Σ → E_Σ → Ê_Σ`) is recorded as data. The injective-dense-image
property of those maps is the continuity condition, deferred to its own node.

Blueprint: `def:field-theory` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.Cobordism.Category
import KontsevichSegal.FieldTheory.NuclearFrechet
import KontsevichSegal.FieldTheory.HolomorphicBundle

open Cobordism

/-! ## Functors from a semicategory -/

/-- **A functor from a `Semicategory`** (content, constructed). An object-map
together with a morphism-map preserving composition, with NO identity law, since
the source `Semicategory` has no identity morphisms.

Mathlib's `CategoryTheory.Functor` does not apply: it is between `Category`
instances (which require identities and a `map_id` law). A field theory maps out
of the cobordism `Semicategory`, so this is the honest notion. -/
structure SemicategoryFunctor (C D : Type*) [Semicategory C] [Semicategory D] where
  /-- The object map. -/
  obj : C → D
  /-- The morphism map. -/
  map : ∀ {a b : C}, (a ⟶ b) → (obj a ⟶ obj b)
  /-- Composition is preserved (no identity law: the source has no identities). -/
  map_comp : ∀ {a b c : C} (f : a ⟶ b) (h : b ⟶ c),
    map (Semicategory.comp f h) = Semicategory.comp (map f) (map h)

/-! ## Fibre families for the target and limit spaces -/

/-- A family of nuclear Fréchet spaces, indexed by a type. Used for the
downstream limit spaces `Ê_Σ`. Anchored to `IsNuclearFrechetSpace` from the
nuclear-Fréchet node. -/
class NuclearFrechetFibres {B : Type*} (F : B → Type*) where
  [addCommGroup : ∀ b, AddCommGroup (F b)]
  [moduleComplex : ∀ b, Module ℂ (F b)]
  [moduleReal : ∀ b, Module ℝ (F b)]
  [tower : ∀ b, IsScalarTower ℝ ℂ (F b)]
  [uniform : ∀ b, UniformSpace (F b)]
  [nuclearFrechet : ∀ b, IsNuclearFrechetSpace (F b)]

attribute [instance] NuclearFrechetFibres.addCommGroup NuclearFrechetFibres.moduleComplex
  NuclearFrechetFibres.moduleReal NuclearFrechetFibres.tower NuclearFrechetFibres.uniform
  NuclearFrechetFibres.nuclearFrechet

/-- A family of complex topological vector spaces, indexed by a type, with no
metrizability or completeness assumed. Used for the upstream limit spaces `Ě_Σ`,
which are nuclear but in general not metrizable, hence not Fréchet. -/
class ComplexTVSFibres {B : Type*} (F : B → Type*) where
  [addCommGroup : ∀ b, AddCommGroup (F b)]
  [moduleComplex : ∀ b, Module ℂ (F b)]
  [topology : ∀ b, TopologicalSpace (F b)]

attribute [instance] ComplexTVSFibres.addCommGroup ComplexTVSFibres.moduleComplex
  ComplexTVSFibres.topology

/-! ## Field theories -/

/-- **A `d`-dimensional field theory** (KS Section 3, blueprint `def:field-theory`),
bare functor together with its induced limit structure. Given the assumed
cobordism geometry `g`:

Bare functor:
* `E` assigns to each object a space `E_Σ`, a Fréchet space (`FrechetFibres`),
  PROVISIONAL and NOT asserted nuclear;
* `Z` assigns to each cobordism `M : Σ₀ ⤳ Σ₁` a continuous linear map
  `Z_M : E_Σ₀ → E_Σ₁`, which is nuclear/trace-class (`Z_nuclear`, via
  `IsNuclearMap`);
* `Z_comp` is functoriality: `Z` preserves composition (concatenation). There is
  no identity law, as `C_d^ℂ` has no identities (this is a `SemicategoryFunctor`
  into the Fréchet/nuclear target; that target is a large category of spaces and
  is not bundled as a `Semicategory` instance here).

Induced limit structure (asserted; the limit construction is deferred):
* `EHat` is the downstream limit `Ê_Σ = lim←`, a NUCLEAR FRÉCHET space
  (`NuclearFrechetFibres`);
* `ECheck` is the upstream limit `Ě_Σ = lim→`, NUCLEAR (`echeck_nuclear`) but a
  general complex TVS not asserted Fréchet (`ComplexTVSFibres`);
* `toEHat`, `fromECheck` are the canonical maps `Ě_Σ → E_Σ → Ê_Σ`. Their
  injective-dense-image property is the CONTINUITY condition, deferred to its own
  node.

The holomorphicity, continuity, tensor, and unitarity conditions are NOT here;
each is its own node. This `structure` is not constructed for any concrete theory. -/
structure FieldTheory [g : CobordismGeometry] where
  /-- `E_Σ`: the provisional Fréchet space assigned to an object. -/
  E : g.Obj → Type*
  [eFrechet : FrechetFibres E]
  /-- `Z_M : E_Σ₀ → E_Σ₁`: the linear map assigned to a cobordism. -/
  Z : ∀ {a b}, g.Mor a b → (E a →L[ℂ] E b)
  /-- Each `Z_M` is nuclear (trace-class). -/
  Z_nuclear : ∀ {a b} (M : g.Mor a b), IsNuclearMap (Z M)
  /-- Functoriality: composition (concatenation) is preserved. No identity law. -/
  Z_comp : ∀ {a b c} (f : g.Mor a b) (h : g.Mor b c),
    Z (g.concat f h) = (Z h).comp (Z f)
  /-- `Ê_Σ = lim←`: the downstream limit, a nuclear Fréchet space. -/
  EHat : g.Obj → Type*
  [ehatFibres : NuclearFrechetFibres EHat]
  /-- `Ě_Σ = lim→`: the upstream limit, a complex TVS (not asserted Fréchet). -/
  ECheck : g.Obj → Type*
  [echeckFibres : ComplexTVSFibres ECheck]
  /-- `Ě_Σ` is nuclear (but in general not metrizable, hence not Fréchet). -/
  echeck_nuclear : ∀ o, IsNuclearSpace (ECheck o)
  /-- The canonical map `E_Σ → Ê_Σ`. -/
  toEHat : ∀ o, E o →L[ℂ] EHat o
  /-- The canonical map `Ě_Σ → E_Σ`. -/
  fromECheck : ∀ o, ECheck o →L[ℂ] E o

/-! ## Deferred

The limit CONSTRUCTION is deferred. The asserted structure above records that
`Ê_Σ` is nuclear Fréchet, `Ě_Σ` is nuclear-non-metrizable, and the canonical maps
`Ě_Σ → E_Σ → Ê_Σ` exist. But the identifications `Ê_Σ = varprojlim E_Σ''` and
`Ě_Σ = varinjlim E_Σ'` need inverse/direct limits of topological vector spaces,
which Mathlib does not provide (the same gap recorded for the nuclear-Fréchet
node's inverse-limit property). They are deferred rather than faked.

The four conditions of the boxed definition are each their own node and are NOT
encoded here: holomorphicity (`def:holomorphicity`), continuity
(`def:continuity`, the injective-dense-image property of the maps above), the
tensor / disjoint-union condition (`def:tensor-axiom`), and unitarity
(`def:unitarity`). -/
