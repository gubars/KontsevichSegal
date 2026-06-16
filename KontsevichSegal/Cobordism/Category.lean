/- The cobordism category C_d^ℂ (KS paper Section 3, arXiv:2105.10161).

This is the first CONTENT-to-BUILD node of Section 3 (CLAUDE.md, "Deliverable
scope and Section 3 strategy", gray-zone note): the cobordism category's
CATEGORICAL SKELETON is constructed as a real category-theoretic structure,
while the SMOOTH-MANIFOLD GEOMETRY underneath it is the assumed infrastructure
layer. The file is organized into two explicit layers.

LAYER 1 — assumed smooth-manifold geometry (`CobordismGeometry`). The germs of
d-manifolds, two-sidedness, co-orientation, the boundary-fixing isometries, and
the gluing of cobordisms are geometry KS cite as known and Mathlib does not
provide (the same gap the `MetCManifold` node hit). They are ASSUMED here as the
fields of a `class` of geometric data (never the `axiom` keyword), with the
complex metric on each object anchored to Section 2 via `MetCField`.

LAYER 2 — the categorical skeleton (`Semicategory`, `instSemicategory`). From the
assumed geometry we CONSTRUCT a genuine category-theoretic structure on the
objects: a `Quiver` (objects + morphisms) with an associative composition given
by concatenation. This is real content, parametric over any `CobordismGeometry`;
no concrete cobordism category (no concrete geometry) is exhibited.

IDENTITY SUBTLETY (blueprint `def:cobordism-category`; Category vs. functor
boundary). C_d^ℂ has NO genuine identity morphisms, so it is NOT a Mathlib
`Category` (whose `CategoryStruct` parent requires an `id : X ⟶ X` and the
identity laws). We do not fake identities. Mathlib has no identity-free category
class, so we build the honest `Semicategory` (a quiver with associative
composition, no identities). The injective-dense-image replacement for the
missing identities is a condition on the FIELD THEORY / functor, encoded in a
later node, never here on the category.

Blueprint: `def:cobordism-category` in `blueprint/src/section3.tex`.
-/

import Mathlib.CategoryTheory.Category.Basic
import KontsevichSegal.FieldTheory.MetCManifold

namespace Cobordism

universe u v

/-! ## Layer 1: assumed smooth-manifold geometry -/

/-- **Assumed (LAYER 1, smooth-manifold geometry; KS Section 3).** The geometric
data underlying the cobordism category `C_d^ℂ`, cited by KS as known and not
available in Mathlib (same gap as `MetCManifold`):

* `Obj` — the type of objects: germs of `d`-manifolds along closed two-sided
  `(d-1)`-manifolds with co-orientation and complex metric. The two-sidedness and
  co-orientation are part of this assumed object data; they are not broken out as
  separate predicates (deferred, as the geometry is not in Mathlib).
* `Ambient o` with `metric o` — each object's underlying `d`-manifold (the germ's
  thickening `U`) and the complex metric germ it carries. `metric` lands in
  `MetCField`, anchoring the objects to the Section 2 domain `QC` of allowable
  complex metrics.
* `Mor a b` — the cobordisms `a ⤳ b` carrying complex metrics, already taken up
  to boundary-fixing isometry (the morphism type is the isometry quotient).
* `concat` — concatenation/gluing of cobordisms.
* `concat_assoc` — gluing is associative. This holds strictly on morphisms
  because gluing is associative up to canonical isometry and morphisms are
  isometry classes; it is a genuine assumed property of the geometry.

This `class` records the assumed geometry; it is NOT constructed for any concrete
family of manifolds. -/
class CobordismGeometry where
  /-- Objects: germs of `d`-manifolds along closed two-sided `(d-1)`-manifolds
  with co-orientation and complex metric. -/
  Obj : Type u
  /-- The underlying `d`-manifold (the germ's thickening) of an object. -/
  Ambient : Obj → Type*
  [ambientTangent : ∀ o, TangentStructure (Ambient o)]
  /-- The complex metric germ carried by an object, anchored to Section 2 `QC`. -/
  metric : ∀ o, MetCField (Ambient o)
  /-- Cobordisms `a ⤳ b`, up to boundary-fixing isometry. -/
  Mor : Obj → Obj → Type v
  /-- Concatenation / gluing of cobordisms. -/
  concat : ∀ {a b c}, Mor a b → Mor b c → Mor a c
  /-- Gluing is associative (strictly, on isometry classes of cobordisms). -/
  concat_assoc : ∀ {a b c d} (f : Mor a b) (g : Mor b c) (h : Mor c d),
    concat (concat f g) h = concat f (concat g h)

attribute [instance] CobordismGeometry.ambientTangent

/-! ## Layer 2: the categorical skeleton -/

/-- **A semicategory**: a quiver with an associative composition but NO identity
morphisms. This is the honest identity-free analogue of Mathlib's `Category`,
which Mathlib does not provide (`CategoryStruct`, the parent of `Category`,
requires an `id : X ⟶ X`).

The cobordism category `C_d^ℂ` is of this kind: it has composable morphisms
(concatenation) but no identity morphisms. -/
class Semicategory (C : Type u) extends Quiver C where
  /-- Composition of morphisms. -/
  comp : ∀ {a b c : C}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)
  /-- Composition is associative. -/
  assoc : ∀ {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h)

/-- **The categorical skeleton of `C_d^ℂ` (LAYER 2, constructed).** Given any
assumed `CobordismGeometry`, its objects form a `Semicategory`: the morphisms are
the cobordisms (`Mor`), and composition is concatenation (`concat`), associative
by `concat_assoc`.

This is genuine content built on the assumed geometry, parametric over
`CobordismGeometry`; it exhibits no concrete cobordism category. It is a
`Semicategory` and deliberately NOT a Mathlib `Category`, because `C_d^ℂ` has no
identity morphisms; the replacement for them is a condition on the field-theory
functor (a later node), not on the category. -/
instance instSemicategory [g : CobordismGeometry] : Semicategory g.Obj where
  Hom a b := g.Mor a b
  comp f h := g.concat f h
  assoc f h k := g.concat_assoc f h k

end Cobordism
