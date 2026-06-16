/- The tensor / disjoint-union condition on a field theory: the third of the four
functor-axiom nodes of Section 3 of the Kontsevich-Segal paper
(arXiv:2105.10161).

This is a PROPERTY OF THE FUNCTOR (a `FieldTheory`), encoded without the `axiom`
keyword and without exhibiting any concrete field theory, and it is a condition
on the field theory, NOT on the cobordism category (Category vs. functor
boundary, CLAUDE.md).

This node is MIXED:

STATABLE (encoded concretely):
* `E_∅ = ℂ`: the space assigned to the empty object is `ℂ` (`IsTensorial.empty_eq`,
  a type equality; see the caveat note below).
* The partition function: for a closed `d`-manifold `M`, i.e. a cobordism
  `∅ ⤳ ∅`, the endomorphism `Z_M ∈ End(E_∅) = ℂ` is a scalar (`partitionFunction`),
  the consequence the paper draws. This genuinely uses `T.Z`.

DEFERRED (documented, NOT faked):
* The tensor isomorphism `Ě_Σ ⊗ Ě_Σ' ≅ Ě_{Σ⊔Σ'}` (and the `Ê` version) and the
  functoriality `Z_M ⊗ Z_{M'} = Z_{M⊔M'}`. These need the completed
  topological/nuclear tensor product of topological vector spaces, which Mathlib
  does NOT provide (Loogle finds no `TopologicalTensorProduct`; only the algebraic
  `Module.TensorProduct` exists). The algebraic tensor product is the WRONG object
  for these Fréchet/nuclear spaces, so per No-approximations it is NOT used as a
  stand-in. This is the same gap the nuclear-Fréchet node recorded (its
  unique-tensor-product property was deferred for the same reason). The tensor
  isomorphism is deferred, gated on the topological-tensor-product gap.

ASSUMED LAYER-1 GEOMETRY. The empty object `∅` and the disjoint union `⊔` of
objects and cobordisms are not present in `CobordismGeometry`
(`Cobordism/Category.lean`). They are assumed geometry of the cobordism category
(its monoidal structure, which the category genuinely has) and are added here as
`MonoidalCobordism`, not faked. The disjoint union `⊔` is geometry; the tensor
product `⊗` on the spaces is the missing analytic piece (deferred above).

Caveat — `empty_eq` is a type equality (as `fibre_eq` was in `Holomorphicity`):
`T.E ∅ = ℂ` (`Eq` in `Type*`) is faithful and minimal under deliverable scope (a)
and needs no instances on the fibre. It is awkward to transport terms across
(`cast`); `partitionFunction` localizes that to a single `cast` of the
generator `1`. If ever used in scope-(b) proof work it may want upgrading to a
continuous-linear equivalence `T.E ∅ ≃L[ℂ] ℂ`.

Blueprint: `def:tensor-axiom` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.FieldTheory.FieldTheory

open Cobordism

/-! ## Assumed monoidal geometry (Layer 1) -/

/-- **Assumed Layer-1 geometry (KS Section 3).** The monoidal structure of the
cobordism category: an empty object `∅` and a disjoint union `⊔` of objects and
of cobordisms. `CobordismGeometry` does not provide these; the cobordism category
genuinely has them, and they are assumed here (the same status as the rest of the
cobordism geometry), needed to state the tensor axiom. This is geometry on the
category; the tensor product on the spaces is a separate, deferred analytic
piece. Not constructed for any concrete family of manifolds. -/
class MonoidalCobordism [g : CobordismGeometry] where
  /-- The empty `(d-1)`-manifold object `∅`. -/
  empty : g.Obj
  /-- Disjoint union `⊔` of objects. -/
  union : g.Obj → g.Obj → g.Obj
  /-- Disjoint union `⊔` of cobordisms. -/
  unionMor : ∀ {a b a' b'}, g.Mor a b → g.Mor a' b' → g.Mor (union a a') (union b b')

/-! ## The tensor axiom on the functor -/

/-- **The tensor / disjoint-union condition on a field theory** (KS Section 3,
blueprint `def:tensor-axiom`), statable fragment. A condition ON the functor `T`,
not on the category.

`empty_eq` records the consequence `E_∅ = ℂ`: the space assigned to the empty
object is `ℂ`. (Stated as a type equality; see the module caveat.)

DEFERRED, not fields here (see the module comment): the core tensor isomorphism
`Ě_Σ ⊗ Ě_Σ' ≅ Ě_{Σ⊔Σ'}` and the functoriality `Z_M ⊗ Z_{M'} = Z_{M⊔M'}`, which
need the completed topological tensor product that Mathlib lacks. They are not
encoded, to avoid the algebraic-tensor-product stand-in (No-approximations).

This `structure` records the condition; it is not instantiated for any concrete
field theory. -/
structure IsTensorial [g : CobordismGeometry] [m : MonoidalCobordism] (T : FieldTheory) where
  /-- `E_∅ = ℂ`: the space of the empty object is `ℂ`. -/
  empty_eq : T.E (MonoidalCobordism.empty) = ℂ

/-- **The partition function** of a closed `d`-manifold `M` (KS Section 3). A
closed manifold is a cobordism `∅ ⤳ ∅`, so `Z_M : E_∅ → E_∅` is an endomorphism
of `E_∅`; under `E_∅ = ℂ` (from `IsTensorial`), `End(E_∅) = ℂ`, and the partition
function is the corresponding scalar, namely `Z_M` applied to the generator `1`.

This genuinely uses `T.Z`; the single `cast` transports the generator across the
`E_∅ = ℂ` type equality. -/
def partitionFunction [g : CobordismGeometry] [m : MonoidalCobordism] (T : FieldTheory)
    (ht : IsTensorial T) (M : g.Mor MonoidalCobordism.empty MonoidalCobordism.empty) : ℂ :=
  letI := T.eFrechet
  cast ht.empty_eq (T.Z M (cast ht.empty_eq.symm (1 : ℂ)))
