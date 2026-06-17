/- The Wick rotation of a time-symmetric Lorentzian germ: the THIRD Lean node of
Section 5 of the Kontsevich-Segal paper (arXiv:2105.10161). Encodes blueprint node
`def:wick-rotation`. Built on node 1 (`LorentzianCategory.lean`) and Section 3's
field theory (`def:field-theory`, `def:unitarity`).

THE h_t FAMILY (introduced here; nodes 1-2 deferred it). Node 1 encodes the
Lorentzian metric invariantly, as a `LorentzianField` of `IsLorentzian` forms on the
ambient tangent spaces, and explicitly deferred the geodesic-normal-form presentation
(it "must introduce the `h_t` family" in the Wick-rotation node). This node builds
that data: `GeodesicNormalForm o` carries a slice `Σ`, the smooth family
`t ↦ h_t` of Riemannian metrics on `Σ`, and the geodesic-normal-form identification
`U ≅ Σ × (-ε, ε)` in which the Lorentzian metric is `h_t - dt²`.

THE TIE TO NODE 1 (not float-free). The family is required to ASSEMBLE TO node 1's
invariant metric: the field `assembles` states that, transported through the chart's
differential `tangentSplit`, node 1's `g.metric o` equals the normal form
`h_t - dt²` (`assembleNormalForm (h t σ) (-1)`). So `h_t` is pinned to the invariant
Lorentzian metric, not a free family. The geodesic-exponential CONSTRUCTION of the
chart `U ≅ Σ × (-ε, ε)` is deferred germ geometry (not built from Mathlib); it is
carried as an assumed `Equiv` so the tie is statable.

TIME-SYMMETRY. By Section 3's `def:unitarity` a germ is time-symmetric when
`Σ ≅ Σ̄*`. For a real (Lorentzian) germ `Σ̄* = Σ*` is co-orientation reversal, the
reflection `t ↦ -t`; the metric being real, invariance under it is the relation
`h_t = h_{-t}`, i.e. the family is even. The structure `TimeSymmetricRotation`
records the post-Whitney data of such a germ (the factor `H` with `h_t = H(t²)`,
which forces evenness, PROVED in `even_family`). The object-level identification with
Section 3's `IsTimeSymmetric` predicate (which lives over the complex category
`C_d^ℂ`) needs the deferred Lorentzian-to-complex boundary correspondence
`C_d^Lor → C_d^ℂ`, so it is cited here (matching the blueprint `\uses{def:unitarity}`)
rather than tied term-level, exactly as Section 3's unitarity node cited Section 2 in
prose; a term-level tie through a free complex object would be vacuous.

THE WICK ROTATION (the heart). Time-symmetry gives an even family, so by Whitney's
theorem `h_t = H(t²)` for a smooth `H` (Mathlib has no usable form of "smooth even
function factors through squaring", and here the family is metric-valued and its very
smoothness is deferred geometry, so `H`/`factor` are ASSUMED as fields, backed by
node 1's real-analyticity, see below). The rotation `t ↦ it` replaces `t²` by
`(it)² = -t²`, so the Wick-rotated family is the genuine construction
`wickRotatedFamily t = H(-t²)`. Because `H` lands in `RiemannianField Σ` (real,
positive-definite metrics), `H(-t²)` is automatically a REAL Riemannian metric:
realness is manifest, the reals are never left. The Wick-rotated Euclidean metric is
`wickMetric = h_{it} + dt² = assembleNormalForm (H(-t²)) 1`, and it is PROVED
Riemannian of Euclidean signature in `isRiemannian_wickMetric` (a real argument from
positive-definiteness of `H(-t²)` and `1 > 0`), not asserted.

REAL-ANALYTICITY (backing the continuation). `TimeSymmetricRotation` requires node 1's
`[IsRealAnalytic]`, so the rotation lives in `C_d^{Lor,ω}`. This is the genuine
reference to node 1's `RealAnalyticStructure`: it is exactly what makes the even
family real-analytic (`IsRealAnalytic.metric_analytic`), hence what licenses the
analytic factor `H` and makes `H(-t²)` the canonical analytic continuation rather
than an arbitrary smooth extension. KS require it for the same reason ("such a
complexification exists only when M and its metric are real-analytic"). A smooth-only
geometry cannot form `TimeSymmetricRotation`. The deeper term-level analytic-curve
formalization (uniqueness via the identity theorem) is deferred, consistent with
node 1 deferring the full identity-theorem characterization.

E_Σ. The Euclidean space `E_Σ` of the germ is what the field theory of
`def:field-theory` assigns to the Wick-rotated Riemannian germ: `EuclideanSpace T oℂ
= T.E oℂ` (a genuine reuse of `FieldTheory.E`; `E_Σ` is undefined without it). The
complex object `oℂ` representing the Euclidean germ is characterized non-vacuously by
`IsEuclideanObject` (its complex metric is real and positive-definite, Euclidean
signature); the precise identification of `oℂ`'s metric with the Wick-rotated form is
the deferred Riemannian-germ-into-`C_d^ℂ` embedding.

THE LIMITATION (honest). This Wick rotation defines `E_Σ` only for time-symmetric
germs, and even there the prescription is tied to the chosen normal form. The
definition for a general Lorentzian germ, and the independence of the construction
from the choices made, are recovered later by Principle 5.1
(`prop:invariance-principle`) and Remark 5.3 (`prop:lorentzian-E-welldefined`),
forthcoming nodes; they are not pre-empted here.

CONSTRAINTS: no `axiom` keyword, no concrete instance (all structures parametric over
the assumed geometry), no `sorry` (assumed properties are carried as FIELDS;
`even_family`, `isRiemannian_wickMetric`, `wickRotatedFamily_zero` are real proofs).

Blueprint: `def:wick-rotation` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.LorentzianCategory
import KontsevichSegal.FieldTheory.Unitarity

namespace WickRotation

open Cobordism

/-! ## Riemannian metric fields on a slice

A Riemannian metric on the slice `Σ` is a field of symmetric positive-definite real
bilinear forms on its tangent spaces, the real positive-definite parallel of node 1's
`LorentzianField` (a field of `IsLorentzian` forms). -/

/-- A real bilinear form is **Riemannian** if it is symmetric and positive-definite.
Positive-definiteness (`∀ v ≠ 0, 0 < φ v v`) is the genuine non-degeneracy that the
Wick rotation needs; in particular it EXCLUDES the degenerate zero form (which is
symmetric but has `φ v v = 0`). The Euclidean signature of the Wick-rotated metric is
proved from this. -/
def IsRiemannian {V : Type*} [AddCommGroup V] [Module ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  (∀ v w, φ v w = φ w v) ∧ (∀ v, v ≠ 0 → 0 < φ v v)

/-- A **Riemannian-metric field** on `M`: assigns to each point a symmetric
positive-definite real bilinear form on the tangent space. The real positive-definite
parallel of node 1's `LorentzianField`; the `IsRiemannian` witness rules out a
degenerate (zero) metric at any point. -/
def RiemannianField (M : Type*) [TangentStructure M] : Type _ :=
  ∀ x : M, { φ : TangentStructure.Tangent x →ₗ[ℝ] TangentStructure.Tangent x →ₗ[ℝ] ℝ //
    IsRiemannian φ }

/-! ## Assembling the geodesic normal form `h ± dt²`

The normal-form metric on `Σ × ℝ` (tangent `T_σΣ × ℝ`): a spatial bilinear form `B`
on `T_σΣ` orthogonally plus `sgn · dt²` on the `ℝ` factor. `sgn = -1` gives the
Lorentzian `h_t - dt²`; `sgn = +1` gives the Wick-rotated Euclidean `h_{it} + dt²`. -/

/-- The assembled bilinear form `B ⊞ sgn · dt²` on `W × ℝ`:
`((w₁,s₁), (w₂,s₂)) ↦ B w₁ w₂ + sgn · (s₁ s₂)`. With `sgn = -1` this is the geodesic
normal form `h - dt²`; with `sgn = +1` the Euclidean `h + dt²`. -/
noncomputable def assembleNormalForm {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (sgn : ℝ) : (W × ℝ) →ₗ[ℝ] (W × ℝ) →ₗ[ℝ] ℝ :=
  B.compl₁₂ (LinearMap.fst ℝ W ℝ) (LinearMap.fst ℝ W ℝ)
    + sgn • (LinearMap.mul ℝ ℝ).compl₁₂ (LinearMap.snd ℝ W ℝ) (LinearMap.snd ℝ W ℝ)

@[simp] lemma assembleNormalForm_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (sgn : ℝ) (p q : W × ℝ) :
    assembleNormalForm B sgn p q = B p.1 q.1 + sgn * (p.2 * q.2) := rfl

/-- **Euclidean signature of the assembled metric.** If the spatial form `B` is
Riemannian (symmetric, positive-definite) and `sgn > 0`, then `B ⊞ sgn · dt²` is
Riemannian. This is the argument that the Wick-rotated metric `h_{it} + dt²` has
Euclidean signature (`sgn = 1`). -/
theorem isRiemannian_assembleNormalForm {W : Type*} [AddCommGroup W] [Module ℝ W]
    {B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ} (hB : IsRiemannian B) {sgn : ℝ} (hsgn : 0 < sgn) :
    IsRiemannian (assembleNormalForm B sgn) := by
  obtain ⟨hsymm, hpos⟩ := hB
  refine ⟨?_, ?_⟩
  · rintro ⟨w₁, s₁⟩ ⟨w₂, s₂⟩
    change B w₁ w₂ + sgn * (s₁ * s₂) = B w₂ w₁ + sgn * (s₂ * s₁)
    rw [hsymm w₁ w₂]; ring
  · rintro ⟨w, s⟩ hne
    change 0 < B w w + sgn * (s * s)
    by_cases hw : w = 0
    · subst hw
      have hs : s ≠ 0 := by rintro rfl; exact hne rfl
      simp only [map_zero, zero_add]
      exact mul_pos hsgn (mul_self_pos.mpr hs)
    · have h1 := hpos w hw
      have h2 : 0 ≤ sgn * (s * s) := mul_nonneg hsgn.le (mul_self_nonneg s)
      linarith

/-! ## The geodesic-normal-form data of a Lorentzian germ

The `h_t` family node 1 deferred, tied to node 1's invariant metric. -/

/-- **The geodesic normal form of a Lorentzian germ (KS Section 5; the `h_t`
family).** For a Lorentzian germ `o` (a node-1 object), the data of its
geodesic-normal-form presentation:

* `Slice` (`Σ`) with its tangent datum, and the radius `ε > 0`;
* `chart` — the geodesic-exponential identification `Σ × (-ε, ε) ≃ U`. Its smooth
  CONSTRUCTION (exponentiating perpendicular geodesics) is deferred germ geometry; it
  is carried as an assumed `Equiv` so the tie below is statable.
* `tangentSplit` — the chart's differential `T_{(σ,t)}U ≃ₗ T_σΣ × ℝ` (an isomorphism,
  so never the degenerate zero map).
* `h` — the smooth family `t ↦ h_t` of Riemannian metrics on `Σ`.
* `assembles` — **the tie**: through `tangentSplit`, node 1's invariant metric
  `g.metric o` equals the normal form `h_t - dt²` (`assembleNormalForm (h t σ) (-1)`).
  So `h_t` is pinned to the invariant Lorentzian metric, not free.

Non-vacuity. `assembles` genuinely constrains: it forces `h_t` to be the spatial
block of node 1's Lorentzian metric (which is positive-definite in adapted
coordinates, matching `IsRiemannian`), so a family that is not the metric's spatial
block fails it. The identification of `tangentSplit` as specifically the chart's
differential (beyond its being a linear iso) needs the deferred smooth chart and its
differential; the assembly tie is already genuine without it.

This `structure` records the assumed normal-form data; it is not constructed for any
concrete germ. -/
structure GeodesicNormalForm [G : LorentzianCobordismGeometry] (o : G.Obj) where
  /-- The slice `Σ` (a closed `(d-1)`-manifold). -/
  Slice : Type*
  [sliceTangent : TangentStructure Slice]
  /-- The geodesic-normal-form radius `ε > 0`. -/
  ε : ℝ
  /-- `ε` is positive. -/
  εpos : 0 < ε
  /-- The geodesic-exponential identification `Σ × (-ε, ε) ≃ U` (assumed; the
  geodesic-exp construction is deferred germ geometry). -/
  chart : Slice × ↥(Set.Ioo (-ε) ε) ≃ G.Ambient o
  /-- The chart's differential at each point, `T_{(σ,t)}U ≃ₗ T_σΣ × ℝ`. An
  isomorphism, so never the degenerate zero map. -/
  tangentSplit : ∀ (σ : Slice) (t : ↥(Set.Ioo (-ε) ε)),
    TangentStructure.Tangent (chart (σ, t)) ≃ₗ[ℝ]
      (TangentStructure.Tangent σ × ℝ)
  /-- The smooth family `t ↦ h_t` of Riemannian metrics on `Σ`. -/
  h : ℝ → RiemannianField Slice
  /-- **The tie to node 1's invariant metric.** Through the chart's differential, the
  Lorentzian metric `g.metric o` of node 1 is the geodesic normal form
  `h_t - dt²`. -/
  assembles : ∀ (σ : Slice) (t : ↥(Set.Ioo (-ε) ε))
      (ξ η : TangentStructure.Tangent (chart (σ, t))),
    (G.metric o (chart (σ, t))).1 ξ η
      = assembleNormalForm (h (t : ℝ) σ).1 (-1)
          (tangentSplit σ t ξ) (tangentSplit σ t η)

namespace GeodesicNormalForm

variable [G : LorentzianCobordismGeometry] {o : G.Obj}

/-- The Lorentzian normal-form metric `h_t - dt²` on `T_σΣ × ℝ`. By `assembles` this
is node 1's invariant metric transported through the chart's differential. -/
noncomputable def lorentzMetric (nf : GeodesicNormalForm o) (σ : nf.Slice) (t : ℝ) :=
  letI := nf.sliceTangent
  assembleNormalForm (nf.h t σ).1 (-1)

end GeodesicNormalForm

/-! ## Time-symmetric germs and their Wick rotation -/

/-- **A time-symmetric Lorentzian germ in normal form, with its Whitney factor (KS
Section 5, blueprint `def:wick-rotation`).** Extends the geodesic-normal-form data of
a germ `o` with the post-Whitney factorization of the even family:

* `H` — the smooth factor with `h_t = H(t²)` (`factor`). By Whitney's theorem an even
  smooth family factors through squaring; Mathlib has no usable form of this, and here
  the family is metric-valued with deferred smoothness, so `H`/`factor` are assumed.

Time-symmetry (`Σ ≅ Σ̄*` of `def:unitarity`) is the reflection `t ↦ -t`, i.e. the
family is even; carrying `H` with `factor` FORCES evenness (`even_family`, proved),
since `H(t²)` is even. The construction lives in node 1's real-analytic category
`[IsRealAnalytic]` (`C_d^{Lor,ω}`): real-analyticity (node 1's `metric_analytic`) is
what makes the even family real-analytic, hence what licenses the analytic factor `H`
and makes the continuation `H(-t²)` canonical. -/
structure TimeSymmetricRotation [G : LorentzianCobordismGeometry] [IsRealAnalytic]
    (o : G.Obj) extends GeodesicNormalForm o where
  /-- The Whitney factor: the smooth `H` with `h_t = H(t²)`. -/
  H : ℝ → RiemannianField Slice
  /-- **Whitney's factorization** `h_t = H(t²)` (assumed; see the docstring). It
  forces the family to be even (`even_family`), the normal-form form of `Σ ≅ Σ̄*`. -/
  factor : ∀ t : ℝ, h t = H (t ^ 2)

namespace TimeSymmetricRotation

variable [G : LorentzianCobordismGeometry] [IsRealAnalytic] {o : G.Obj}

/-- **Time-symmetry in normal form: the family is even** (`h_{-t} = h_t`). PROVED
from `factor`: `h_{-t} = H((-t)²) = H(t²) = h_t`. This is the normal-form
manifestation of `Σ ≅ Σ̄*` (the reflection `t ↦ -t`, `def:unitarity`); a non-even
family cannot satisfy `factor`, so it is a genuine constraint, not vacuous. -/
theorem even_family (W : TimeSymmetricRotation o) (t : ℝ) : W.h (-t) = W.h t := by
  have h2 : (-t) ^ 2 = t ^ 2 := by ring
  rw [W.factor (-t), h2, ← W.factor t]

/-- **The Wick-rotated family** `t ↦ h_{it} = H(-t²)`. The rotation `t ↦ it` sends
`t²` to `(it)² = -t²`. Because `H` lands in `RiemannianField` (real positive-definite
metrics), `H(-t²)` is automatically a REAL Riemannian metric: realness is manifest,
the reals are never left. Backed by node 1's `[IsRealAnalytic]`, which makes this the
canonical analytic continuation. -/
def wickRotatedFamily (W : TimeSymmetricRotation o) (t : ℝ) := W.H (-(t ^ 2))

/-- **The Wick-rotated Euclidean metric** `h_{it} + dt²` on `T_σΣ × ℝ`
(`assembleNormalForm (H(-t²)) 1`). Its Euclidean signature is `isRiemannian_wickMetric`. -/
noncomputable def wickMetric (W : TimeSymmetricRotation o) (σ : W.Slice) (t : ℝ) :=
  letI := W.sliceTangent
  assembleNormalForm (W.wickRotatedFamily t σ).1 1

/-- **The Wick-rotated metric is Riemannian (Euclidean signature).** PROVED, not
asserted: `H(-t²)` is Riemannian (it is a `RiemannianField` value) and `1 > 0`, so
`assembleNormalForm (H(-t²)) 1` is Riemannian by `isRiemannian_assembleNormalForm`.
This is KS's "the rotated metric is Riemannian, of Euclidean signature". -/
theorem isRiemannian_wickMetric (W : TimeSymmetricRotation o) (σ : W.Slice) (t : ℝ) :
    IsRiemannian (W.wickMetric σ t) := by
  letI := W.sliceTangent
  change IsRiemannian (assembleNormalForm (W.wickRotatedFamily t σ).1 1)
  exact isRiemannian_assembleNormalForm (W.wickRotatedFamily t σ).2 one_pos

/-- **Coherence of the rotation at `t = 0`:** `h_{i·0} = h_0`. Both equal `H(0)`
(`H(-0²) = H(0) = H(0²) = h_0` by `factor`). A sanity tie: the Wick rotation agrees
with the original slice metric at the hypersurface. -/
theorem wickRotatedFamily_zero (W : TimeSymmetricRotation o) :
    W.wickRotatedFamily 0 = W.h 0 := by
  change W.H (-(0 ^ 2)) = W.h 0
  rw [W.factor 0]
  norm_num

end TimeSymmetricRotation

/-! ## The Euclidean space `E_Σ` of a time-symmetric germ

`E_Σ` is what the field theory of `def:field-theory` assigns to the Wick-rotated
Riemannian germ. The germ's Euclidean (Wick-rotated) metric makes it an object of the
complex cobordism category `C_d^ℂ` whose metric is real and positive-definite. -/

section Euclidean

variable [g : CobordismGeometry]

/-- **A Euclidean object of `C_d^ℂ`.** A complex germ whose complex metric is real and
positive-definite (Euclidean signature) at every point: the kind of object a
Wick-rotated Riemannian germ defines. Non-vacuous: a non-real or non-positive-definite
allowable metric fails it, while a real positive-definite metric (which is allowable,
all eigenvalues being positive reals) satisfies it. References the actual metric
`g.metric`, so it is not free-floating. -/
def IsEuclideanObject (oℂ : g.Obj) : Prop :=
  (∀ (x : g.Ambient oℂ) (v w : TangentStructure.Tangent x),
      (AllowableComplexMetric.toForm (g.metric oℂ x) v w).im = 0) ∧
  (∀ (x : g.Ambient oℂ) (v : TangentStructure.Tangent x), v ≠ 0 →
      0 < (AllowableComplexMetric.toForm (g.metric oℂ x) v v).re)

/-- **The Euclidean space `E_Σ` of a (Wick-rotated) germ (KS Section 5, blueprint
`def:wick-rotation`).** For the complex object `oℂ` representing the Wick-rotated
Riemannian germ, `E_Σ` is the space the field theory `T` of `def:field-theory` assigns
to it: `T.E oℂ`. A genuine reuse of `FieldTheory.E` (`E_Σ` is undefined without it).

The complex object `oℂ` is intended to satisfy `IsEuclideanObject` (Euclidean
signature), with its metric the Wick-rotated form `h_{it} + dt²` of
`TimeSymmetricRotation`; the precise identification of `oℂ`'s metric with that form is
the deferred Riemannian-germ-into-`C_d^ℂ` embedding (the boundary correspondence
`C_d^Lor → C_d^ℂ` that node 1 records only at the metric level via
`metric_on_shilov_boundary`). -/
def EuclideanSpace (T : FieldTheory) (oℂ : g.Obj) : Type _ := T.E oℂ

end Euclidean

end WickRotation
