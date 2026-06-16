/- The continuity condition on a field theory: the second of the four
functor-axiom nodes of Section 3 of the Kontsevich-Segal paper
(arXiv:2105.10161).

This is a PROPERTY OF THE FUNCTOR (a `FieldTheory`), encoded as a predicate
(never the `axiom` keyword, never an instance), and it is a condition on the
field theory, NOT on the cobordism category (Category vs. functor boundary,
CLAUDE.md).

This is where the injective-dense-image condition finally lands. It is the
"true replacement for the missing identity morphisms": the cobordism category
`C_d^ℂ` is a `Semicategory` with no identities (`Cobordism/Category.lean`
deferred the identity replacement to here, on the functor). Rather than
adjoining degenerate zero-length cobordisms (whose operators are not nuclear),
one requires the canonical maps `Ě_Σ → E_Σ → Ê_Σ` of the functor to be injective
with dense image.

Unlike holomorphicity, this node is FULLY STATABLE: the maps already exist in the
`FieldTheory` structure as continuous linear maps (`fromECheck : Ě_Σ → E_Σ` and
`toEHat : E_Σ → Ê_Σ`), and injectivity (`Function.Injective`) and dense image
(`DenseRange`) are directly expressible against the real `T.fromECheck` /
`T.toEHat` (the codomains carry the TVS/Fréchet topologies from the fibre
bundlings). Nothing is deferred.

The condition is stated as a `Prop`-valued predicate rather than a `class` of
fields, because `DenseRange` needs the codomain's `TopologicalSpace` instance,
which here comes from the field theory's fibre bundlings (`eFrechet`,
`echeckFibres`, `ehatFibres`); bringing those into scope needs `letI`, which a
structure/`class` field cannot do but a `def` body can (the same pattern used for
`BundleMorphism`).

Blueprint: `def:continuity` in `blueprint/src/section3.tex`.
-/

import KontsevichSegal.FieldTheory.FieldTheory
import Mathlib.Topology.DenseEmbedding

open Cobordism

/-- **The continuity property of a field theory** (KS Section 3, blueprint
`def:continuity`). A condition ON the functor `T`: for every object, the
canonical maps `Ě_Σ → E_Σ → Ê_Σ` are each injective with dense image.

This is the true replacement for the identity morphisms that the cobordism
`Semicategory` lacks; it is imposed on the field theory, not the category.

Fully statable against the real maps of `T`:
* `T.fromECheck o : Ě_Σ → E_Σ` is injective with dense range;
* `T.toEHat o : E_Σ → Ê_Σ` is injective with dense range.

(The composite `Ě_Σ → Ê_Σ` is then injective with dense image as well, being a
composition of injective, dense-range continuous maps.) -/
def IsContinuous [g : CobordismGeometry] (T : FieldTheory) : Prop :=
  letI := T.eFrechet
  letI := T.echeckFibres
  letI := T.ehatFibres
  (∀ o, Function.Injective (T.fromECheck o)) ∧
  (∀ o, DenseRange (T.fromECheck o)) ∧
  (∀ o, Function.Injective (T.toEHat o)) ∧
  (∀ o, DenseRange (T.toEHat o))
