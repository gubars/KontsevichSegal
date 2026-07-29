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

Everything in this file is proved (no sorry). The remaining assembly — allowability
of the homotopy at each t, joint (t, g)-continuity, the `ContinuousMap.Homotopy`
packaging, and the endpoint contraction of the convex positive-definite cone — is
checkpoint 2 and lives with `QC_contractible`'s tracked sorry in `Domain.lean`.

Blueprint: `lem:posdef-retraction` in `blueprint/src/content.tex`. Reviewed artifact:
`blueprint/restatements/retraction-checkpoint1.md`.
-/

import KontsevichSegal.ComplexMetrics.Domain
import KontsevichSegal.ComplexMetrics.Equivalence
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

end KontsevichSegal.Retraction
