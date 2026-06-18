/- Remark 5.3 (well-definedness of the Lorentzian space `Ê_Σ`): the SEVENTH Lean node of
Section 5 of the Kontsevich-Segal paper (arXiv:2105.10161). Encodes blueprint node
`prop:lorentzian-E-welldefined`. It RESOLVES the arbitrariness node 3 (`def:wick-rotation`)
left open: the Wick rotation's choice of path does not matter. It leans on Principle 5.1
(node 5, `IsInvariant`) for the interleaving-rays coherence, reuses Section 3's reality
condition `IsReal` for the conjugate-space structure, and its time-symmetric payoff IS the
C1-fixed reflection-positivity pairing of `def:unitarity` (node 6's `pairing`).

KS REMARK 5.3 (KSTeX 713–725). For a real-analytic Lorentzian metric on `U`, the complex
theory gives a holomorphic bundle `{Ê_f}` over the space `𝒥` of embedding-germs
`f : (-ε,ε) → ℂ` with `f(0)=0` and `Re f'(t) > 0`; the radial paths `f_λ(t) = λt` (`λ ∈ ℂ₊`)
lie in `𝒥`, and `Ê_f` is the inverse limit of the spaces at the germs of `f` at `f(t_k)`,
`t_k ↓ 0`.
* PATH-INDEPENDENCE (the content): any smooth path `f ∈ 𝒥` defines the SAME `Ê_Σ` — for any
  two paths a canonical isomorphism `Ê_f ≅ Ê_{f'}` of the inverse limits, mutually inverse,
  and COHERENT for three rays. The interleaving-rays argument and the coherence are by
  Principle 5.1.
* CONJUGATE-SPACE: `Ê_{f̄}` is the complex-conjugate space to `Ê_f`, so reversing the complex
  time-direction conjugates the identification of `Ê_Σ` with the Euclidean choice `Ê_{f_1}`.
* TIME-SYMMETRIC (AND ONLY THEN): a hermitian inner product on `Ě_Σ`, the reflection-positivity
  pairing of `def:unitarity`.

THE ENCODING (scope (a): STATE the results; the interleaving proof is deferred-additive prose).
`PathGerm` is `𝒥` (the `Re f' > 0` condition reuses node 4's `deriv`-based curve constraint).
`LorentzianEWelldefined T hReal o` bundles, for a real theory and a real-analytic germ `o`:

* `EHatPath`/`ehatPathFibres` — the bundle `{Ê_f}` (nuclear-Fréchet fibres; the inverse-limit
  CONSTRUCTION inherits Section 3's deferred TVS-limit, documented).
* `euclideanPath`/`euclideanPath_eq`/`euclidean_iso` — the Euclidean choice `Ê_{f_1}` (`f_1(t)=t`)
  is the field theory's `Ê` at the (Euclidean) complex object: `EHatPath f_1 ≃L T.EHat (cplx o)`.
  This ANCHORS the bundle to the actual field theory (`Ê_Σ ≅ T.EHat (cplx o)`), not a free bundle.
* `pathIso`/`pathIso_symm`/`pathIso_coh` — PATH-INDEPENDENCE: canonical `≃L` isos, mutually
  inverse (`symm`) and coherent (the cocycle `pathIso f f'' = pathIso f f' ≫ pathIso f' f''`).
  EQUATE-able (identities); the coherence holds by Principle 5.1 (node 5; prose, deferred proof).
  This is exactly "the choice of path doesn't matter", resolving node 3's arbitrariness.
* `conjPath`/`conjPath_eq`/`conjSpace` — CONJUGATE-SPACE: `conjPath` is the conjugate path
  (`conjPath_eq` ties its `f` to `t ↦ conj (f t)`), and `Ê_{f̄} ≃SL[starRingEnd ℂ] Ê_f` is the
  conjugate-linear iso — the SAME `starRingEnd ℂ` semilinearity as `IsReal` (the bundle's
  conjugate structure is induced by the theory's reality `hReal`).

`timeSymmetricHermitianInner` — the TIME-SYMMETRIC payoff (C), PROVED: for a time-symmetric germ
(`IsTimeSymmetric (cplx o)`) AND ONLY THEN, the reflection-positivity hermitian pairing on `Ě_Σ`
exists — it is LITERALLY `IsUnitary`'s condition (ii) (`hU.2 (cplx o) hts`), the same pairing
node 6's `pairing_reflectionPositive` proves valid. Gated on `IsTimeSymmetric` (a non-time-
symmetric germ does not get it: `hU.2` does not apply).

EQUATE-vs-DISTINGUISH (node-5 lesson). This node's content is path-INDEPENDENCE — "the spaces
are canonically isomorphic, the choice doesn't matter". The isos are EQUATE-carried (`≃L` +
`symm` + cocycle); NO injectivity/distinctness field is added on `pathIso` (it would CONTRADICT
"same space"). Likewise `conjSpace` is the conjugate-linear identification, not a distinctness.

DEFERRED (documented): the interleaving-path CONSTRUCTION and the inverse-limit `Ê` (Section 3's
TVS-limit gap); the holomorphic bundle `{Ê_f}` / `𝒥`'s holomorphic structure (no Mathlib
holomorphic-bundle infra); the proof that path-independence/coherence hold (Principle 5.1, prose).

CONSTRAINTS: no `axiom` keyword, no concrete instance, no `sorry` (results STATED as
structure/≃L/∃; the interleaving proof is prose, never a `sorry`'d theorem;
`timeSymmetricHermitianInner` is PROVED from `hU.2`, axiom-clean). Reuses node 5's `IsInvariant`
(prose), Section 3's `IsReal`/`IsUnitary`/`E`/`Ě`/`Ê`, node 6's `WickObjectCorrespondence`.

Blueprint: `prop:lorentzian-E-welldefined` in `blueprint/src/section5.tex`.
-/

import KontsevichSegal.WickRotation.UnitaryGH

namespace WickRotation

open Cobordism

/-! ## The space `𝒥` of embedding-germs -/

/-- **The space `𝒥` of embedding-germs (KS Remark 5.3).** A germ `f : ℝ → ℂ` (the germ at `0`)
with `f(0) = 0` and `Re f'(t) > 0` for all `t`. The `Re f' > 0` condition reuses node 4's
`deriv`-based curve constraint (`CurveSubmanifold.f_deriv_re_pos`): it is a real constraint —
a curve with non-positive real derivative anywhere (or a non-differentiable / constant one,
where `deriv = 0`) is excluded. -/
structure PathGerm where
  /-- The embedding-germ `f : ℝ → ℂ` (the germ at `0`). -/
  f : ℝ → ℂ
  /-- `f(0) = 0`. -/
  f_zero : f 0 = 0
  /-- `Re f'(t) > 0` for all `t` (forces `f` differentiable with positive-real derivative). -/
  f_deriv_re_pos : ∀ t : ℝ, 0 < (deriv f t).re

/-! ## The bundle `{Ê_f}` over `𝒥`, path-independence, and conjugate-space -/

/-- **Remark 5.3, the well-definedness of `Ê_Σ` (KS Section 5, blueprint
`prop:lorentzian-E-welldefined`).** For a real field theory `T` (`hReal : IsReal T`) and a
real-analytic Lorentzian germ `o`, the holomorphic bundle `{Ê_f}` over `𝒥` together with the
path-independence isos and the conjugate-space structure.

PATH-INDEPENDENCE (`pathIso`, `pathIso_symm`, `pathIso_coh`): any two paths give a canonical
`≃L` iso of the inverse limits, mutually inverse and coherent (the cocycle). The
interleaving-rays argument and the three-ray coherence hold by Principle 5.1 (node 5,
`IsInvariant`) — recorded as prose (scope (a)), not a `sorry`'d proof. This is exactly KS's "any
smooth path defines the same `Ê_Σ`", RESOLVING the arbitrariness `def:wick-rotation` (node 3)
left open.

CONJUGATE-SPACE (`conjPath`, `conjPath_eq`, `conjSpace`): `Ê_{f̄}` is the complex-conjugate space
to `Ê_f`, the conjugate-linear `≃SL[starRingEnd ℂ]` iso — the same semilinearity as `IsReal`,
induced by the theory's reality `hReal`.

ANCHORED to the field theory (`euclidean_iso`): the Euclidean choice `Ê_{f_1}` is `T.EHat (cplx o)`,
so the bundle is not free-floating. Not constructed for any concrete germ (the bundle and the
interleaving paths are assumed; their construction is deferred). -/
structure LorentzianEWelldefined [gc : CobordismGeometry] [dc : DualConjugateGeometry]
    [gl : LorentzianCobordismGeometry] [WOC : WickObjectCorrespondence]
    (T : FieldTheory) (hReal : IsReal T) (o : gl.Obj) where
  /-- The bundle `{Ê_f}`: the inverse-limit space `Ê_f` for each path (assumed; the
  inverse-limit construction inherits Section 3's deferred TVS-limit). -/
  EHatPath : PathGerm → Type*
  [ehatPathFibres : NuclearFrechetFibres EHatPath]
  /-- The Euclidean path `f_1(t) = t` (`λ = 1`). -/
  euclideanPath : PathGerm
  /-- `f_1` is the radial path at `λ = 1`. -/
  euclideanPath_eq : euclideanPath.f = fun (t : ℝ) => (t : ℂ)
  /-- The Euclidean choice `Ê_{f_1}` IS the field theory's `Ê` at the (Euclidean) complex
  object — anchoring the bundle to `T` (so `Ê_Σ ≅ T.EHat (cplx o)`). -/
  euclidean_iso : EHatPath euclideanPath ≃L[ℂ] T.EHat (WOC.cplx o)
  /-- **PATH-INDEPENDENCE:** a canonical `≃L` iso `Ê_f ≅ Ê_{f'}` for any two paths. -/
  pathIso : ∀ f f' : PathGerm, EHatPath f ≃L[ℂ] EHatPath f'
  /-- The isos are mutually inverse. -/
  pathIso_symm : ∀ f f' : PathGerm, pathIso f' f = (pathIso f f').symm
  /-- The isos are COHERENT (the cocycle condition, holding by Principle 5.1). -/
  pathIso_coh : ∀ f f' f'' : PathGerm,
    pathIso f f'' = (pathIso f f').trans (pathIso f' f'')
  /-- The conjugate path `f̄`. -/
  conjPath : PathGerm → PathGerm
  /-- `conjPath` is the conjugate path: `(f̄)(t) = conj (f t)` (the tie). -/
  conjPath_eq : ∀ p : PathGerm, (conjPath p).f = fun t => (starRingEnd ℂ) (p.f t)
  /-- **CONJUGATE-SPACE:** `Ê_{f̄}` is the complex-conjugate space to `Ê_f` (conjugate-linear
  iso; the same `starRingEnd ℂ` semilinearity as `IsReal`, induced by `hReal`). -/
  conjSpace : ∀ f : PathGerm, EHatPath (conjPath f) ≃SL[starRingEnd ℂ] EHatPath f

attribute [instance] LorentzianEWelldefined.ehatPathFibres

/-! ## The time-symmetric hermitian inner product (the payoff) -/

/-- **The time-symmetric hermitian inner product on `Ě_Σ` (KS Remark 5.3, the payoff).** For a
time-symmetric germ `o` (`IsTimeSymmetric (cplx o)`) AND ONLY THEN, the conjugate-space property
yields a hermitian inner product on `Ě_Σ = T.ECheck (cplx o)` — the reflection-positivity pairing
`B(x,y) = J(κ x) y` of `def:unitarity`. PROVED: this is LITERALLY `IsUnitary`'s condition (ii)
applied at the germ's complex object, `hU.2 (cplx o) hts`. So it is the SAME pairing node 6's
`InducesUnitaryGH.pairing_reflectionPositive` proves hermitian + positive-definite. Gated on
`IsTimeSymmetric`: a non-time-symmetric germ has no such `hts`, hence no hermitian form ("and only
then"). -/
theorem timeSymmetricHermitianInner [gc : CobordismGeometry] [dc : DualConjugateGeometry]
    [gl : LorentzianCobordismGeometry] [WOC : WickObjectCorrespondence]
    {T : FieldTheory} (hU : IsUnitary T) (o : gl.Obj)
    (hts : IsTimeSymmetric (WOC.cplx o)) :
    ∃ J : T.EHat (WOC.cplx o) ≃L[ℂ] (T.ECheck (WOC.cplx o) →SL[starRingEnd ℂ] ℂ),
      (∀ (x y : T.ECheck (WOC.cplx o)),
          (starRingEnd ℂ) (J (T.toEHat (WOC.cplx o) (T.fromECheck (WOC.cplx o) y)) x)
            = J (T.toEHat (WOC.cplx o) (T.fromECheck (WOC.cplx o) x)) y) ∧
      (∀ (x : T.ECheck (WOC.cplx o)),
          0 ≤ (J (T.toEHat (WOC.cplx o) (T.fromECheck (WOC.cplx o) x)) x).re) ∧
      (∀ (x : T.ECheck (WOC.cplx o)),
          J (T.toEHat (WOC.cplx o) (T.fromECheck (WOC.cplx o) x)) x = 0 → x = 0) :=
  hU.2 (WOC.cplx o) hts

end WickRotation
