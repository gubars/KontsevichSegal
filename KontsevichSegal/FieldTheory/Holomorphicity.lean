/- The holomorphicity condition on a field theory: the first of the four
functor-axiom nodes of Section 3 of the Kontsevich-Segal paper
(arXiv:2105.10161).

This is a PROPERTY OF THE FUNCTOR (a `FieldTheory`), encoded as a `class`
(never the `axiom` keyword, never an instance), and it is a condition on the
field theory, NOT on the cobordism category (Category vs. functor boundary,
CLAUDE.md). It adds no new structure to the category.

Blueprint: `def:holomorphicity` in `blueprint/src/section3.tex`. For a fixed
germ `Σ ⊂ U` the spaces `E_Σ` form a locally trivial holomorphic vector bundle
over the complex manifold `Met_ℂ(U)`; for a cobordism `M : Σ₀ ⤳ Σ₁` the maps
`Z_M` form a morphism of holomorphic vector bundles over `Met_ℂ(M)`, the end
bundles being pulled back along the restriction maps.

ANCHOR vs. DEFER (exactly as the bundle node split it):

* ANCHORED (statable now, genuinely tied to `T.E`): the spaces `E_Σ` extend, as
  the metric varies, to a holomorphic vector bundle over `Met_ℂ(U)` with Fréchet
  fibres. We reuse `HolomorphicBundle` (the fibre family with Fréchet structure)
  and tie it to the field theory: the object's complex metric is a point of
  `Met_ℂ(U)` (`basepoint`, `basepoint_metric`, via `MetCManifold.toField` and
  the real `CobordismGeometry.metric`), and the bundle's fibre over that point is
  `E_Σ` (`fibre_eq`). So `E_Σ` is genuinely the fibre of the bundle at the
  object's metric.

* DEFERRED (documented, not faked): the load-bearing content, namely the
  HOLOMORPHY and local triviality of the bundle over the base, and the
  `Z_M`-as-holomorphic-bundle-morphism (holomorphic dependence on the base point,
  pullback along the restriction maps). These rest on the complex-manifold
  structure of `Met_ℂ(M)` that `MetCManifold` deferred and the base-holomorphy
  that `HolomorphicBundle` deferred, i.e. on the same Fréchet-manifold gap
  (Mathlib's manifolds/bundles require normed models; `Met_ℂ` is Fréchet). Per
  No-approximations we do not substitute a normed/finite-dimensional stand-in.
  The `Z_M` morphism adds nothing statable beyond `T.Z` here: its fibrewise data
  at the metric IS `T.Z M`, and the new content (a morphism over the varying
  base, with pullback along the deferred restriction maps) is exactly the
  deferred holomorphy.

This node is honestly mostly deferred: holomorphicity is defined against the
deferred complex-manifold structure, so its real content is gated on that gap.
The anchored part (the `E_Σ` bundle and the fibre tie) is non-vacuous.
-/

import KontsevichSegal.FieldTheory.FieldTheory
import KontsevichSegal.FieldTheory.HolomorphicBundle
import KontsevichSegal.FieldTheory.MetCManifold

open Cobordism

/-- **Holomorphicity of a field theory** (KS Section 3, blueprint
`def:holomorphicity`). A condition ON the functor `T`, requiring each ambient
manifold to carry a `Met_ℂ` structure (`[∀ o, MetCManifold (Ambient o)]`).

Anchored fields (genuinely tied to `T.E`):

* `bundle o` — the holomorphic vector bundle of the spaces `E_Σ` over
  `Met_ℂ(U)`, with Fréchet fibres (reusing `HolomorphicBundle`).
* `basepoint o` — the carrier point of `Met_ℂ(U)` at which the object sits, and
  `basepoint_metric` records that it is the object's actual complex metric
  (`CobordismGeometry.metric o`, via `MetCManifold.toField`).
* `fibre_eq o` — the bundle's fibre over that point is `E_Σ` (`= T.E o`).

DEFERRED (see the module comment): the holomorphy and local triviality of
`bundle o` over the base, and the `Z_M`-as-holomorphic-bundle-morphism, rest on
the deferred complex-manifold structure of `Met_ℂ` (the Fréchet-manifold gap)
and the deferred restriction maps. They are not encoded here, to avoid faking.

This `class` records the condition; it is not instantiated for any concrete
field theory. -/
class IsHolomorphic [g : CobordismGeometry]
    [hM : ∀ o, MetCManifold (CobordismGeometry.Ambient o)] (T : FieldTheory) where
  /-- The holomorphic vector bundle of `E_Σ` over `Met_ℂ(U)` (Fréchet fibres). -/
  bundle : ∀ o, HolomorphicBundle (CobordismGeometry.Ambient o)
  /-- The carrier point of `Met_ℂ(U)` at which the object sits. -/
  basepoint : ∀ o, MetCManifold.carrier (CobordismGeometry.Ambient o)
  /-- The basepoint is the object's actual complex metric. -/
  basepoint_metric : ∀ o,
    MetCManifold.toField (basepoint o) = CobordismGeometry.metric o
  /-- `E_Σ` is the fibre of the bundle at the object's metric. -/
  fibre_eq : ∀ o, (bundle o).Fibre (basepoint o) = T.E o
