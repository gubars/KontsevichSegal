/- The positive-definite retraction machinery for the contractibility clause of
KS Proposition 2.4 (KSTeX 220-222).

This file builds the deformation-retraction machinery intended to prove
`QC_contractible`: the continuous map g ↦ g₀(g) = Re((det g)^{-1/2}·g) onto the real
positive-definite cone, the segment angle bound making the straight-line homotopy
angle-contracting, and the supporting positivity/diagonality/continuity lemmas.

ROUTE DIVERGENCE, recorded plainly. KS derive contractibility from Proposition 2.4's
fibre-bundle description (contractible convex fibres Π(V, g₀) over the contractible
space of positive-definite inner products). This file takes a DIFFERENT route: a
deformation retraction of QC(V) onto the positive-definite cone, which is convex and
hence contractible. Faithfulness attaches to the THEOREM, not the proof — the
precedents are Run 7's spectral-theorem assembly for the reverse direction of
Theorem 2.2 (`ComplexMetrics/Equivalence.lean`) and `restrict_nondegenerate`'s
codim-free rotation route. The theorem stated is KS's; the argument need not be.

This route does NOT prove Proposition 2.4 itself: foundation F2 (the associated
bundle GL(V) ×_{O(V)} Π(V)) remains owed for `prop:parametrization` regardless. The
retraction is additive, never a substitute.

Everything in this file is proved (no sorry). Checkpoint 2 added the assembly —
allowability of the segment at each t (`segMetric`), joint (t, g)-continuity of the
homotopies, the two `ContinuousMap.Homotopy` stages, and the endpoint contraction of
the convex positive-definite cone — and `QC_contractible` itself now lives, PROVED,
at the bottom of this file. It MOVED here from `Domain.lean`: its proof depends on
this file, which imports `Domain.lean`, so the theorem could not stay there. The
general-purpose supports (`nondegenerate_of_angle_cond`,
`AllowableComplexMetric.ofRealPosDef`, `AllowableComplexMetric.euclid`) live in
`ComplexMetrics/EigenvalueMinmax.lean` per the import-direction rule.

Blueprint: `lem:posdef-retraction` in `blueprint/src/content.tex`. Reviewed artifact:
`blueprint/restatements/retraction-checkpoint1.md`.
-/

import KontsevichSegal.ComplexMetrics.Domain
import KontsevichSegal.ComplexMetrics.Equivalence
import KontsevichSegal.ComplexMetrics.EigenvalueMinmax
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

namespace KontsevichSegal.Retraction

open Complex Set KontsevichSegal.Hodge

/-! ## The segment angle bound -/

private theorem sq_norm_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

set_option maxHeartbeats 1000000 in
-- the sign-split `nlinarith` calls in `hkey` exceed the default heartbeat limit
/-- Core case of `seg_arg`: `lam` in the open upper half-plane, `0 < t < 1`. The
comparison reduces along `Complex.cos_arg` to `lam.re * ‖z‖ ≤ z.re * ‖lam‖`, which
sign-splits and closes from the identity
`(z.re·‖lam‖)² − (lam.re·‖z‖)² = lam.im²·(t·r)·(z.re + (1−t)·lam.re)`. -/
theorem aux_upper {lam : ℂ} (him : 0 < lam.im) {r t : ℝ} (hr : 0 < r)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 - t) • lam + t • (r : ℂ) ≠ 0) ∧
      |((1 - t) • lam + t • (r : ℂ)).arg| ≤ |lam.arg| := by
  set z : ℂ := (1 - t) • lam + t • (r : ℂ) with hzdef
  have hzre : z.re = (1 - t) * lam.re + t * r := by
    simp [hzdef, Complex.add_re, Complex.ofReal_re]
  have hzim : z.im = (1 - t) * lam.im := by
    simp [hzdef, Complex.add_im, Complex.ofReal_im]
  have h1t : 0 < 1 - t := by linarith
  have hzim0 : 0 < z.im := by rw [hzim]; exact mul_pos h1t him
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzim0; simp at hzim0
  have hlam0 : lam ≠ 0 := by intro h; rw [h] at him; simp at him
  have hargLpos : 0 < lam.arg :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le)
      (fun h => him.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
  have hargZpos : 0 < z.arg :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hzim0.le)
      (fun h => hzim0.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
  have hnl : 0 < ‖lam‖ := norm_pos_iff.mpr hlam0
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnl2 := sq_norm_eq lam
  have hnz2 := sq_norm_eq z
  have hkey : lam.re * ‖z‖ ≤ z.re * ‖lam‖ := by
    rcases le_total lam.re 0 with hA | hA
    · rcases le_total 0 z.re with hC | hC
      · have h1 : lam.re * ‖z‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA hnz.le
        have h2 : 0 ≤ z.re * ‖lam‖ := mul_nonneg hC hnl.le
        linarith
      · have hexp : (lam.re * ‖z‖) ^ 2 - (z.re * ‖lam‖) ^ 2
            = -(lam.im ^ 2 * (t * r) * (z.re + (1 - t) * lam.re)) := by
          rw [mul_pow, mul_pow, hnl2, hnz2, hzim, hzre]; ring
        have hsum : z.re + (1 - t) * lam.re ≤ 0 :=
          add_nonpos hC (mul_nonpos_of_nonneg_of_nonpos h1t.le hA)
        have hneg : lam.im ^ 2 * (t * r) * (z.re + (1 - t) * lam.re) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (sq_nonneg _) (mul_pos ht0 hr).le) hsum
        have hsq : (z.re * ‖lam‖) ^ 2 ≤ (lam.re * ‖z‖) ^ 2 := by linarith
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hA hnz.le,
          mul_nonpos_of_nonpos_of_nonneg hC hnl.le, hsq]
    · have hC : 0 < z.re := by
        rw [hzre]
        nlinarith [mul_nonneg h1t.le hA, mul_pos ht0 hr]
      have hexp : (z.re * ‖lam‖) ^ 2 - (lam.re * ‖z‖) ^ 2
          = lam.im ^ 2 * (t * r) * (z.re + (1 - t) * lam.re) := by
        rw [mul_pow, mul_pow, hnl2, hnz2, hzim, hzre]; ring
      have hpos2 : 0 ≤ lam.im ^ 2 * (t * r) * (z.re + (1 - t) * lam.re) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (mul_pos ht0 hr).le)
          (by nlinarith [mul_nonneg h1t.le hA])
      have hsq : (lam.re * ‖z‖) ^ 2 ≤ (z.re * ‖lam‖) ^ 2 := by linarith
      nlinarith [mul_nonneg hA hnz.le, mul_pos hC hnl, hsq]
  have hcos : Real.cos lam.arg ≤ Real.cos z.arg := by
    rw [Complex.cos_arg hlam0, Complex.cos_arg hz0, div_le_div_iff₀ hnl hnz]
    linarith [hkey]
  have harg : z.arg ≤ lam.arg := by
    by_contra hcon
    push_neg at hcon
    have hlt := Real.strictAntiOn_cos
      (Set.mem_Icc.mpr ⟨hargLpos.le, Complex.arg_le_pi lam⟩)
      (Set.mem_Icc.mpr ⟨hargZpos.le, Complex.arg_le_pi z⟩) hcon
    linarith
  exact ⟨hz0, by rw [abs_of_pos hargZpos, abs_of_pos hargLpos]; exact harg⟩

/-- **The segment angle bound.** For `lam ≠ 0` off the closed negative real axis
(`|arg lam| < π`), a positive real `r`, and `t ∈ [0, 1]`, the segment point
`(1 - t) • lam + t • r` is nonzero and its argument shrinks in absolute value:
`|arg ((1-t)·lam + t·r)| ≤ |arg lam|`. Geometrically: the point lies in the convex
cone spanned by `lam` and the positive real axis, of aperture `|arg lam| < π`.

Mathlib has NO support for the argument of a sum, a convex combination, or a point
of a convex cone (verified by search), so this is a from-scratch addition and a
plausible upstreaming candidate. It is the engine of the retraction route: applied
entrywise on a diagonalizing basis (`g0_diag`), it makes the straight-line homotopy
from an allowable metric to its positive-definite part angle-contracting. -/
theorem seg_arg (lam : ℂ) (hlam : lam ≠ 0) (harg : |lam.arg| < Real.pi)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - t) • lam + t • (r : ℂ) ≠ 0) ∧
      |((1 - t) • lam + t • (r : ℂ)).arg| ≤ |lam.arg| := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact ⟨hlam, le_rfl⟩
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1
    have hz : (1 - (1 : ℝ)) • lam + (1 : ℝ) • (r : ℂ) = (r : ℂ) := by simp
    rw [hz]
    refine ⟨Complex.ofReal_ne_zero.mpr hr.ne', ?_⟩
    have h0arg : (r : ℂ).arg = 0 :=
      Complex.arg_eq_zero_iff.mpr ⟨by simp [hr.le], by simp⟩
    rw [h0arg]
    simp
  rcases lt_trichotomy lam.im 0 with hB | hB | hB
  · -- lower half-plane: conjugate and use `aux_upper`
    have hmu : 0 < ((starRingEnd ℂ) lam).im := by simpa using neg_pos.mpr hB
    obtain ⟨hz', harg'⟩ := aux_upper hmu hr h0 h1
    have hcz : (starRingEnd ℂ) ((1 - t) • lam + t • (r : ℂ))
        = (1 - t) • (starRingEnd ℂ) lam + t • (r : ℂ) := by
      simp [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
    have hz0 : (1 - t) • lam + t • (r : ℂ) ≠ 0 := by
      intro h; apply hz'; rw [← hcz, h, map_zero]
    have hzim : ((1 - t) • lam + t • (r : ℂ)).im = (1 - t) * lam.im := by
      simp [Complex.add_im, Complex.ofReal_im]
    have hzimneg : ((1 - t) • lam + t • (r : ℂ)).im < 0 := by
      rw [hzim]; exact mul_neg_of_pos_of_neg (by linarith) hB
    have hargz_ne : ((1 - t) • lam + t • (r : ℂ)).arg ≠ Real.pi := by
      intro h
      have h2 := (Complex.arg_eq_pi_iff.mp h).2
      rw [h2] at hzimneg
      exact lt_irrefl _ hzimneg
    have hargl_ne : lam.arg ≠ Real.pi := by
      intro h
      rw [h, abs_of_pos Real.pi_pos] at harg
      exact lt_irrefl _ harg
    have e1 : |((starRingEnd ℂ) ((1 - t) • lam + t • (r : ℂ))).arg|
        = |((1 - t) • lam + t • (r : ℂ)).arg| := by
      rw [Complex.arg_conj, if_neg hargz_ne, abs_neg]
    have e2 : |((starRingEnd ℂ) lam).arg| = |lam.arg| := by
      rw [Complex.arg_conj, if_neg hargl_ne, abs_neg]
    refine ⟨hz0, ?_⟩
    calc |((1 - t) • lam + t • (r : ℂ)).arg|
        = |((starRingEnd ℂ) ((1 - t) • lam + t • (r : ℂ))).arg| := e1.symm
      _ = |((1 - t) • (starRingEnd ℂ) lam + t • (r : ℂ)).arg| := by rw [hcz]
      _ ≤ |((starRingEnd ℂ) lam).arg| := harg'
      _ = |lam.arg| := e2
  · -- real case: `lam` is forced to be a positive real
    have hA : 0 < lam.re := by
      rcases lt_trichotomy lam.re 0 with h | h | h
      · exfalso
        have hpi : lam.arg = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨h, hB⟩
        rw [hpi, abs_of_pos Real.pi_pos] at harg
        exact lt_irrefl _ harg
      · exact absurd (Complex.ext (by simpa using h) (by simpa using hB)) hlam
      · exact h
    have hzre : ((1 - t) • lam + t • (r : ℂ)).re = (1 - t) * lam.re + t * r := by
      simp [Complex.add_re, Complex.ofReal_re]
    have hzim : ((1 - t) • lam + t • (r : ℂ)).im = 0 := by
      simp [Complex.add_im, Complex.ofReal_im, hB]
    have hzrepos : 0 < ((1 - t) • lam + t • (r : ℂ)).re := by
      rw [hzre]
      nlinarith [mul_pos (show (0 : ℝ) < 1 - t by linarith) hA, mul_pos h0 hr]
    refine ⟨fun h => by rw [h] at hzrepos; simp at hzrepos, ?_⟩
    have h0arg : ((1 - t) • lam + t • (r : ℂ)).arg = 0 :=
      Complex.arg_eq_zero_iff.mpr ⟨hzrepos.le, hzim⟩
    rw [h0arg]
    simp
  · -- upper half-plane
    exact aux_upper hB hr h0 h1

/-! ## The retraction map g₀ -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The retraction map `g₀(g) = Re((det g)^{-1/2} · g)`: the real part of `g`
normalized by the principal square root of its real-coframe Gram determinant
(`detSqrtReal`, via the bridge `AllowableComplexMetric.toComplexMetric`). Choice-free
as a map: the scalar multiplies the FORM, and `detSqrtReal`'s branch is pinned by
`detSqrtReal_eq_of_sq`. -/
noncomputable def g0 (g : AllowableComplexMetric V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  ((detSqrtReal g.toComplexMetric)⁻¹ • g.toForm).compr₂ Complex.reLm

/-- Evaluation of `g0`, definitionally. -/
theorem g0_apply (g : AllowableComplexMetric V) (v w : V) :
    g0 g v w = ((detSqrtReal g.toComplexMetric)⁻¹ * g.toForm v w).re := rfl

/-- The ℂ-valued coercion of `g0`, addable to `g.toForm` (the homotopy's endpoint):
postcomposition with `Algebra.linearMap ℝ ℂ`. -/
noncomputable def g0C (g : AllowableComplexMetric V) : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
  (g0 g).compr₂ (Algebra.linearMap ℝ ℂ)

/-- Evaluation of `g0C`, definitionally. -/
theorem g0C_apply (g : AllowableComplexMetric V) (v w : V) :
    g0C g v w = (((detSqrtReal g.toComplexMetric)⁻¹ * g.toForm v w).re : ℂ) := rfl

/-- **`g0` is positive definite** — the p = 1 case of Definition 2.1 (KSTeX 199),
already proved en route to Theorem 2.2: chain `g.angle_cond` (consumed as a Prop) →
`isAllowableHodge_of_diag` → `re_normalized_toForm_pos`. -/
theorem g0_posDef (g : AllowableComplexMetric V) (v : V) (hv : v ≠ 0) :
    0 < g0 g v v := by
  obtain ⟨b, eig, hAC, hdiag⟩ := g.angle_cond
  have hAH : IsAllowableHodge g.toComplexMetric :=
    isAllowableHodge_of_diag g.toComplexMetric hAC hdiag
  exact re_normalized_toForm_pos g.toComplexMetric hAH v hv

/-- **Same-basis diagonality**: on any diagonalizing basis `(b, eig)` of `g`, the
retraction `g0 g` is diagonal with entries `Re(c·λ_k)`, where
`c = (detSqrtReal ĝ)⁻¹`. This is what lets `seg_arg` apply per-entry: the straight
segment from `g` to `g0 g` is diagonal in `g`'s OWN real basis. The witness is `g`'s
own `angle_cond` basis, so the diagonalization is consumed as a proposition, never as
extracted data — nothing here depends on KS Proposition 2.4. -/
theorem g0_diag (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2) (v : V) :
    g0 g v v
      = ∑ i, ((detSqrtReal g.toComplexMetric)⁻¹ * eig i).re * (b.repr v i) ^ 2 := by
  rw [g0_apply, hdiag v, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-! ## Continuity of g₀ -/

/-- The principal square root as an explicit, choice-free formula:
`exp((1/2) • log w)`. -/
noncomputable def sqrtFormula (w : ℂ) : ℂ := Complex.exp ((2⁻¹ : ℝ) • Complex.log w)

theorem sqrtFormula_sq {w : ℂ} (hw : w ≠ 0) : sqrtFormula w ^ 2 = w := by
  rw [sqrtFormula, pow_two, ← Complex.exp_add, ← add_smul]
  norm_num
  exact Complex.exp_log hw

theorem sqrtFormula_re_pos {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    0 < (sqrtFormula w).re := by
  rw [sqrtFormula, Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have him : ((2⁻¹ : ℝ) • Complex.log w).im = w.arg / 2 := by
    rw [Complex.smul_im, Complex.log_im, smul_eq_mul]; ring
  rw [him]
  constructor
  · have := Complex.neg_pi_lt_arg w
    linarith
  · have h1 : w.arg ≤ Real.pi := Complex.arg_le_pi w
    have h2 : w.arg ≠ Real.pi := by
      intro h
      obtain ⟨hre, him0⟩ := Complex.arg_eq_pi_iff.mp h
      rcases hw with hpos | hne
      · exact absurd hpos (not_lt.mpr hre.le)
      · exact hne him0
    have : w.arg < Real.pi := lt_of_le_of_ne h1 h2
    linarith

theorem sqrtFormula_continuousAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContinuousAt sqrtFormula w :=
  Complex.continuous_exp.continuousAt.comp
    ((continuousAt_clog hw).const_smul (2⁻¹ : ℝ))

/-- **The pin**: `detSqrtReal` IS the explicit formula `exp((1/2) • log (detGramReal g))`.
`detSqrtReal` is defined by `Exists.choose`; this lemma routes the choice around via the
uniqueness characterization `detSqrtReal_eq_of_sq` (a square root with positive real part
is unique), which is the load-bearing step for continuity. -/
theorem detSqrtReal_eq_formula (g : ComplexMetric V) :
    detSqrtReal g = sqrtFormula (detGramReal g) := by
  have hslit : detGramReal g ∈ Complex.slitPlane := by
    rcases detGramReal_not_nonpos_real g with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact detSqrtReal_eq_of_sq g (sqrtFormula_re_pos hslit)
    (sqrtFormula_sq (detGramReal_ne_zero g))

/-- The real-coframe Gram determinant of an allowable metric lies off the closed
negative real axis. -/
theorem detGram_slitPlane (g : AllowableComplexMetric V) :
    detGramReal g.toComplexMetric ∈ Complex.slitPlane := by
  rcases detGramReal_not_nonpos_real g.toComplexMetric with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Continuity of the normalizing scalar** `g ↦ detSqrtReal ĝ`, from F1's induced
topology on QC(V). `detSqrtReal` is defined by `Exists.choose` and is therefore opaque
to direct continuity arguments; the choice is routed around by rewriting it, via the
uniqueness pin `detSqrtReal_eq_of_sq` (`detSqrtReal_eq_formula`), as
`exp((1/2) • log (detGramReal g))` — continuous at every point because the Gram
determinant stays in the slit plane. The Gram entries are continuous by
`IsModuleTopology.continuous_of_linearMap`, the determinant by
`Continuous.matrix_det`. A reader extending this file should reuse the pin, not fight
the `choose`. -/
theorem detSqrt_comp_continuous :
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    Continuous (fun g : AllowableComplexMetric V => detSqrtReal g.toComplexMetric) := by
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional
  have h0 : Continuous
      (AllowableComplexMetric.toForm : AllowableComplexMetric V → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) :=
    continuous_induced_dom
  have hdet : Continuous (fun B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ =>
      (Matrix.of fun i j =>
        B (Module.finBasis ℝ V i) (Module.finBasis ℝ V j)).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact IsModuleTopology.continuous_of_linearMap
      ({ toFun := fun B =>
            B (Module.finBasis ℝ V i) (Module.finBasis ℝ V j)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) →ₗ[ℝ] ℂ)
  have hgram : Continuous
      (fun g : AllowableComplexMetric V => detGramReal g.toComplexMetric) :=
    hdet.comp h0
  have hfun : (fun g : AllowableComplexMetric V => detSqrtReal g.toComplexMetric)
      = fun g => sqrtFormula (detGramReal g.toComplexMetric) := by
    funext g; exact detSqrtReal_eq_formula g.toComplexMetric
  rw [hfun, continuous_iff_continuousAt]
  intro g
  exact ContinuousAt.comp (g := sqrtFormula)
    (f := fun g : AllowableComplexMetric V => detGramReal g.toComplexMetric) (x := g)
    (sqrtFormula_continuousAt (detGram_slitPlane g)) hgram.continuousAt

/-- ℝ-bilinear smul `ℂ × FormC → FormC`, packaged for
`IsModuleTopology.continuous_bilinear_of_finite_left` (ℂ is module-finite over ℝ). -/
noncomputable def smulBilin :
    ℂ →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) where
  toFun c :=
    { toFun := fun B => c • B
      map_add' := fun B C => smul_add c B C
      map_smul' := fun r B => smul_comm c r B }
  map_add' c d := by
    ext B v w
    simp [add_smul]
  map_smul' r c := by
    ext B v w
    simp [Complex.real_smul]
    ring

/-- **Continuity of the retraction map** `g0`, from F1's induced topology on QC(V) to
the real form space with its canonical `moduleTopology`. Factored as
(compr₂ with `Complex.reLm`, linear) ∘ (the ℝ-bilinear smul, continuous by
`IsModuleTopology.continuous_bilinear_of_finite_left`) ∘ (the pair of the normalizing
scalar and `toForm`). Requires `IsModuleTopology ℝ ℂ`, which Mathlib provides only as
a `@[local instance]` (`isModuleTopologyOfFiniteDimensional`). -/
theorem g0_continuous :
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) := moduleTopology ℝ _
    Continuous (fun g : AllowableComplexMetric V => g0 g) := by
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) := moduleTopology ℝ _
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :=
    IsModuleTopology.toContinuousAdd ℝ _
  haveI : ContinuousAdd (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) :=
    IsModuleTopology.toContinuousAdd ℝ _
  have hc : Continuous
      (fun g : AllowableComplexMetric V => (detSqrtReal g.toComplexMetric)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro g
    exact (detSqrt_comp_continuous.continuousAt).inv₀ (detSqrtReal_ne_zero _)
  have h0 : Continuous
      (AllowableComplexMetric.toForm : AllowableComplexMetric V → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) :=
    continuous_induced_dom
  have hsmul : Continuous (fun p : ℂ × (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) =>
      (smulBilin (V := V) p.1) p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left (smulBilin (V := V))
  have hre : Continuous (fun B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ => B.compr₂ Complex.reLm) :=
    IsModuleTopology.continuous_of_linearMap
      ({ toFun := fun B => B.compr₂ Complex.reLm
         map_add' := fun B C => by
           ext v w
           simp
         map_smul' := fun r B => by
           ext v w
           simp [LinearMap.compr₂_apply, LinearMap.smul_apply, smul_eq_mul] } :
        (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℝ))
  have hfac : (fun g : AllowableComplexMetric V => g0 g)
      = (fun B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ => B.compr₂ Complex.reLm)
        ∘ (fun p : ℂ × (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) => (smulBilin (V := V) p.1) p.2)
        ∘ (fun g => ((detSqrtReal g.toComplexMetric)⁻¹, g.toForm)) := by
    funext g; rfl
  rw [hfac]
  exact hre.comp (hsmul.comp (hc.prodMk h0))

/-! ## Checkpoint 2: the assembly -/

/-- Entry positivity: on `g`'s own diagonalizing basis, every retracted eigenvalue
`Re(c·λ_k)` is positive — `g0_posDef` evaluated at basis vectors through `g0_diag`. -/
theorem entry_pos (g : AllowableComplexMetric V)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (k : Fin (Module.finrank ℝ V)) :
    0 < ((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re := by
  have h1 := g0_posDef g (b k) (b.ne_zero k)
  have h2 := g0_diag g hdiag (b k)
  rw [h2] at h1
  have hsum : ∑ i, ((detSqrtReal g.toComplexMetric)⁻¹ * eig i).re * (b.repr (b k) i) ^ 2
      = ((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re := by
    rw [Finset.sum_eq_single k]
    · simp [Module.Basis.repr_self]
    · intro j _ hj
      simp [Module.Basis.repr_self, Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ k) h
  rwa [hsum] at h1

/-- Diagonal identity of the stage-1 segment form on `g`'s own basis. -/
theorem segForm_diag (g : AllowableComplexMetric V) (t : ℝ)
    {b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig : Fin (Module.finrank ℝ V) → ℂ}
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2) :
    ∀ v, ((1 - t) • g.toForm + t • g0C g) v v
      = ∑ k, ((1 - t) • eig k
          + t • ((((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re : ℝ) : ℂ))
        * (b.repr v k : ℂ) ^ 2 := by
  intro v
  have e1 : ((1 - t) • g.toForm + t • g0C g) v v
      = (1 - t) • g.toForm v v + t • (((g0 g v v : ℝ) : ℂ)) := rfl
  rw [e1, hdiag v, g0_diag g hdiag v]
  push_cast
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.real_smul]
  ring

/-- **The stage-1 segment is allowable**: the straight line from `g` to its retraction,
as an allowable metric. The `angle_cond` witness is `g`'s OWN basis with eigenvalues
`(1-t)·λ_k + t·Re(c·λ_k)`, exactly the shape `seg_arg` controls. -/
noncomputable def segMetric (g : AllowableComplexMetric V) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : AllowableComplexMetric V where
  toForm := (1 - t) • g.toForm + t • g0C g
  symmetric' := fun v w => by
    change (1 - t) • g.toForm v w + t • g0C g v w
        = (1 - t) • g.toForm w v + t • g0C g w v
    rw [g0C_apply, g0C_apply, g.symmetric' v w]
  nondegenerate := by
    obtain ⟨b, eig, hAC, hdiag⟩ := g.angle_cond
    have hseg := fun k => seg_arg (eig k) (hAC.nonzero k) (hAC.abs_arg_lt_pi k)
      (((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re) (entry_pos g hdiag k) t ht
    exact nondegenerate_of_angle_cond ((1 - t) • g.toForm + t • g0C g)
      (b := b)
      (eig := fun k => (1 - t) • eig k
        + t • ((((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re : ℝ) : ℂ))
      ⟨fun k => (hseg k).1,
       fun k => not_nonpos_of_abs_arg_lt_pi (hseg k).1
         (lt_of_le_of_lt (hseg k).2 (hAC.abs_arg_lt_pi k)),
       lt_of_le_of_lt (Finset.sum_le_sum fun k _ => (hseg k).2) hAC.sum_arg_lt_pi⟩
      (segForm_diag g t hdiag)
  angle_cond := by
    obtain ⟨b, eig, hAC, hdiag⟩ := g.angle_cond
    have hseg := fun k => seg_arg (eig k) (hAC.nonzero k) (hAC.abs_arg_lt_pi k)
      (((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re) (entry_pos g hdiag k) t ht
    exact ⟨b,
      fun k => (1 - t) • eig k
        + t • ((((detSqrtReal g.toComplexMetric)⁻¹ * eig k).re : ℝ) : ℂ),
      ⟨fun k => (hseg k).1,
       fun k => not_nonpos_of_abs_arg_lt_pi (hseg k).1
         (lt_of_le_of_lt (hseg k).2 (hAC.abs_arg_lt_pi k)),
       lt_of_le_of_lt (Finset.sum_le_sum fun k _ => (hseg k).2) hAC.sum_arg_lt_pi⟩,
      segForm_diag g t hdiag⟩

@[simp] theorem segMetric_toForm (g : AllowableComplexMetric V) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (segMetric g t ht).toForm = (1 - t) • g.toForm + t • g0C g := rfl

/-- Positive combination of positives, in the convex-combination shape. `nlinarith`
alone does not close `0 < a·X + c·Y`; the explicit case split does. -/
theorem convex_pos_combo {s X Y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hX : 0 < X) (hY : 0 < Y) : 0 < (1 - s) * X + s * Y := by
  rcases eq_or_lt_of_le hs1 with heq | hlt
  · rw [heq]; simpa using hY
  · have h1 := mul_pos (show (0 : ℝ) < 1 - s by linarith) hX
    have h2 := mul_nonneg hs0 hY.le
    linarith

omit [FiniteDimensional ℝ V] in
/-- The set of positive-definite real bilinear forms is convex. -/
theorem posDef_convex :
    Convex ℝ {P : LinearMap.BilinForm ℝ V | ∀ v, v ≠ 0 → 0 < P v v} := by
  intro P hP Q hQ a c ha hc hac v hv
  have e : (a • P + c • Q) v v = a * P v v + c * Q v v := by
    simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  change 0 < (a • P + c • Q) v v
  rw [e, show a = 1 - c by linarith]
  exact convex_pos_combo hc (by linarith) (hP v hv) (hQ v hv)

/-! ## Joint continuity and the two homotopy stages -/

theorem g0C_symm (g : AllowableComplexMetric V) (v w : V) : g0C g v w = g0C g w v := by
  rw [g0C_apply, g0C_apply, g.symmetric' v w]

/-- `g ↦ g0C g` is continuous: `g0_continuous` composed with the linear coercion
`B ↦ B.compr₂ (Algebra.linearMap ℝ ℂ)`. -/
theorem g0C_continuous :
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    Continuous (fun g : AllowableComplexMetric V => g0C g) := by
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) := moduleTopology ℝ _
  haveI : ContinuousAdd (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := IsModuleTopology.toContinuousAdd ℝ _
  have hco : Continuous
      (fun B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ => B.compr₂ (Algebra.linearMap ℝ ℂ)) :=
    IsModuleTopology.continuous_of_linearMap
      ({ toFun := fun B => B.compr₂ (Algebra.linearMap ℝ ℂ)
         map_add' := fun B C => by ext v w; simp
         map_smul' := fun r B => by ext v w; simp } :
        (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℂ))
  have hfac : (fun g : AllowableComplexMetric V => g0C g)
      = (fun B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ => B.compr₂ (Algebra.linearMap ℝ ℂ))
        ∘ (fun g => g0 g) := rfl
  rw [hfac]
  exact hco.comp g0_continuous

/-- Joint `(t, g)`-continuity of the stage-1 segment form. The ℝ-`smul` and addition
come DIRECTLY from `ModuleTopology.continuousSMul` and
`IsModuleTopology.toContinuousAdd` — no bilinear lemma is needed here, unlike the
ℂ-`smul` in `g0_continuous`. -/
theorem seg_jointly_continuous :
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    Continuous (fun p : ℝ × AllowableComplexMetric V =>
      (1 - p.1) • p.2.toForm + p.1 • g0C p.2) := by
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
  haveI : ContinuousAdd (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := IsModuleTopology.toContinuousAdd ℝ _
  haveI : ContinuousSMul ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) :=
    ModuleTopology.continuousSMul ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
  have htoForm : Continuous (fun p : ℝ × AllowableComplexMetric V => p.2.toForm) :=
    continuous_induced_dom.comp continuous_snd
  have hg0C : Continuous (fun p : ℝ × AllowableComplexMetric V => g0C p.2) :=
    g0C_continuous.comp continuous_snd
  exact ((continuous_const.sub continuous_fst).smul htoForm).add
    (continuous_fst.smul hg0C)

/-- The retraction, as a `ContinuousMap`. -/
noncomputable def retractCM :
    C(AllowableComplexMetric V, AllowableComplexMetric V) where
  toFun := fun g => segMetric g 1 ⟨zero_le_one, le_refl 1⟩
  continuous_toFun := by
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    apply continuous_induced_rng.mpr
    have hfac : (AllowableComplexMetric.toForm
        ∘ fun g : AllowableComplexMetric V => segMetric g 1 ⟨zero_le_one, le_refl 1⟩)
        = (fun p : ℝ × AllowableComplexMetric V =>
            (1 - p.1) • p.2.toForm + p.1 • g0C p.2)
          ∘ (fun g : AllowableComplexMetric V => ((1 : ℝ), g)) := rfl
    rw [hfac]
    exact seg_jointly_continuous.comp (Continuous.prodMk continuous_const continuous_id)

/-- Stage 1: the straight-line homotopy from the identity to the retraction. -/
noncomputable def stage1 :
    ContinuousMap.Homotopy (ContinuousMap.id (AllowableComplexMetric V)) retractCM where
  toFun := fun p => segMetric p.2 (p.1 : ℝ) p.1.2
  continuous_toFun := by
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    apply continuous_induced_rng.mpr
    have hfac : (AllowableComplexMetric.toForm
        ∘ fun p : unitInterval × AllowableComplexMetric V =>
          segMetric p.2 (p.1 : ℝ) p.1.2)
        = (fun q : ℝ × AllowableComplexMetric V =>
            (1 - q.1) • q.2.toForm + q.1 • g0C q.2)
          ∘ (fun p : unitInterval × AllowableComplexMetric V => ((p.1 : ℝ), p.2)) := rfl
    rw [hfac]
    exact seg_jointly_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left := fun g => by
    apply AllowableComplexMetric.ext
    simp
  map_one_left := fun g => by
    apply AllowableComplexMetric.ext
    simp [retractCM]

/-- The stage-2 segment: the straight line from the retraction's value to the Euclidean
basepoint, allowable because it is real and positive definite throughout. -/
noncomputable def seg2Metric (g : AllowableComplexMetric V) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : AllowableComplexMetric V :=
  AllowableComplexMetric.ofRealPosDef ((1 - s) • g0C g + s • euclidForm)
    (fun v w => by
      change (1 - s) • g0C g v w + s • euclidForm v w
          = (1 - s) • g0C g w v + s • euclidForm w v
      rw [g0C_symm g v w, euclidForm_symm v w])
    (fun v w => by
      change ((1 - s) • g0C g v w + s • euclidForm v w).im = 0
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, g0C_apply,
        euclidForm_apply, Complex.ofReal_im, Complex.ofReal_im]
      simp)
    (fun v hv => by
      change 0 < ((1 - s) • g0C g v v + s • euclidForm v v).re
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, g0C_apply,
        euclidForm_apply, Complex.ofReal_re, Complex.ofReal_re]
      have h1 : 0 < ((detSqrtReal g.toComplexMetric)⁻¹ * g.toForm v v).re := by
        have h := g0_posDef g v hv
        rwa [g0_apply] at h
      have h2 : 0 < (∑ i, (Module.finBasis ℝ V).repr v i
          * (Module.finBasis ℝ V).repr v i : ℝ) := by
        have h := euclidForm_re_pos v hv
        rwa [euclidForm_apply, Complex.ofReal_re] at h
      obtain ⟨hs0, hs1⟩ := hs
      exact convex_pos_combo hs0 hs1 h1 h2)

@[simp] theorem seg2Metric_toForm (g : AllowableComplexMetric V) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (seg2Metric g s hs).toForm = (1 - s) • g0C g + s • euclidForm := rfl

theorem seg2_jointly_continuous :
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    Continuous (fun p : ℝ × AllowableComplexMetric V =>
      (1 - p.1) • g0C p.2 + p.1 • euclidForm) := by
  letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
  haveI : ContinuousAdd (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := IsModuleTopology.toContinuousAdd ℝ _
  haveI : ContinuousSMul ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) :=
    ModuleTopology.continuousSMul ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
  have hg0C : Continuous (fun p : ℝ × AllowableComplexMetric V => g0C p.2) :=
    g0C_continuous.comp continuous_snd
  exact ((continuous_const.sub continuous_fst).smul hg0C).add
    (continuous_fst.smul continuous_const)

/-- Stage 2: the straight-line homotopy from the retraction to the constant map at the
Euclidean basepoint, staying inside the positive-definite (hence allowable) cone. -/
noncomputable def stage2 :
    ContinuousMap.Homotopy (retractCM (V := V))
      (ContinuousMap.const (AllowableComplexMetric V) AllowableComplexMetric.euclid) where
  toFun := fun p => seg2Metric p.2 (p.1 : ℝ) p.1.2
  continuous_toFun := by
    letI : TopologicalSpace (V →ₗ[ℝ] V →ₗ[ℝ] ℂ) := moduleTopology ℝ _
    apply continuous_induced_rng.mpr
    have hfac : (AllowableComplexMetric.toForm
        ∘ fun p : unitInterval × AllowableComplexMetric V =>
          seg2Metric p.2 (p.1 : ℝ) p.1.2)
        = (fun q : ℝ × AllowableComplexMetric V =>
            (1 - q.1) • g0C q.2 + q.1 • euclidForm)
          ∘ (fun p : unitInterval × AllowableComplexMetric V => ((p.1 : ℝ), p.2)) := rfl
    rw [hfac]
    exact seg2_jointly_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left := fun g => by
    apply AllowableComplexMetric.ext
    simp [retractCM]
  map_one_left := fun g => by
    apply AllowableComplexMetric.ext
    simp [AllowableComplexMetric.euclid]

end KontsevichSegal.Retraction

open KontsevichSegal.Retraction in
/-- **KS paper Proposition 2.4 (contractibility; KSTeX 220-222), PROVED.** QC(V) is
contractible.

History: this statement carried the project's first (and only) tracked `sorry`, from
`32bffa2` (F1, which supplied the topology and made it statable) until the present
commit. The three conditions that made that sorry honest — statable, true, not then
provable — are discharged in order: the F1 topology still carries the statement, KS's
claim is unchanged, and the proof now exists below.

Proof route: a deformation retraction onto the real positive-definite cone, NOT KS's
fibre bundle. The straight-line homotopy `stage1` takes `g` to its normalized real
part `g₀(g) = Re((det g)^{-1/2}·g)` — allowable at every `t` because, in `g`'s own
diagonalizing basis, each eigenvalue moves along the segment from `λ_k` to
`Re(c·λ_k) > 0`, on which `|arg|` only shrinks (`seg_arg`); `stage2` then contracts
the positive-definite image to the Euclidean basepoint inside the convex cone, and
`Homotopy.trans` composes the stages.

QC(V) is NOT itself convex, so `Convex.contractibleSpace` does not apply directly —
witness at d = 1: for `V = ℝ` the allowable set is ℂ ∖ (-∞, 0], and the segment from
-1 + εi to -1 - εi passes through -1. That is exactly why the route retracts to the
positive-definite cone first.

This proves the contractibility clause of KS Proposition 2.4 WITHOUT proving
Proposition 2.4 itself (the fibre-bundle parametrization); foundation F2 is still
owed for `prop:parametrization`.

Stated on `AllowableComplexMetric V`, not `QC V`: the types are equal by definition,
but `QC` is a `def` and instance search does not unfold it to find the topology
instance. -/
theorem QC_contractible (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    ContractibleSpace (AllowableComplexMetric V) := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨AllowableComplexMetric.euclid, ⟨(stage1 (V := V)).trans stage2⟩⟩
