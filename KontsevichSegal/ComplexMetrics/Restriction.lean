/- Proposition 2.5: restriction to subspaces preserves allowability.

This file formalizes KS paper Proposition 2.5 (arXiv:2105.10161, p. 13):
if g ∈ QC(V) and W is any vector subspace of V, then g|_W ∈ QC(W).
-/

import KontsevichSegal.ComplexMetrics.Defs
import KontsevichSegal.ComplexMetrics.EigenvalueMinmax

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-! ## Restricting the bilinear form to a submodule -/

/-- Restrict an allowable complex metric's bilinear form to a submodule `W ≤ V`.
Maps `(w₁, w₂) ↦ g(↑w₁, ↑w₂)` using the subtype coercion `W → V`.

KS paper Proposition 2.5: this is the first step in showing that the restriction
of an allowable metric to a subspace is again allowable. -/
noncomputable def AllowableComplexMetric.restrict (g : AllowableComplexMetric V)
    (W : Submodule ℝ V) : W →ₗ[ℝ] W →ₗ[ℝ] ℂ where
  toFun w₁ :=
    { toFun := fun w₂ => g.toForm (w₁ : V) (w₂ : V)
      map_add' := fun w₂ w₃ => by simp [map_add]
      map_smul' := fun r w₂ => by simp [map_smul] }
  map_add' := fun w₁ w₂ => by
    ext w₃
    simp [map_add]
  map_smul' := fun r w₁ => by
    ext w₂
    simp [map_smul]

/-- The restricted form is symmetric: `g|_W(w₁, w₂) = g|_W(w₂, w₁)`.
Follows directly from the symmetry of `g`. -/
lemma AllowableComplexMetric.restrict_symmetric (g : AllowableComplexMetric V)
    (W : Submodule ℝ V) (w₁ w₂ : W) :
    g.restrict W w₁ w₂ = g.restrict W w₂ w₁ := by
  change g.toForm (w₁ : V) (w₂ : V) = g.toForm (w₂ : V) (w₁ : V)
  exact g.symmetric' _ _

/-! ## KS paper Proposition 2.5: restriction preserves allowability -/

/-- The restricted form detects every nonzero vector by pairing it with itself:
for nonzero `w : W` the value `g|_W(w, w)` is nonzero. The rotation `phi`
produced by the angle condition of the ambient metric makes
`Re(e^{-i phi} * g(v, v))` strictly positive for every nonzero `v : V`
(`exists_rotation_posDef`), and `g|_W(w, w)` is the ambient value `g(w, w)`,
so it cannot vanish.

KS paper Proposition 2.5: nondegeneracy of `g|_W` (the codimension-free part
of the proposition; the angle bound for `g|_W` is the remaining part). -/
lemma AllowableComplexMetric.restrict_nondegenerate (g : AllowableComplexMetric V)
    (W : Submodule ℝ V) (w : W) (hw : w ≠ 0) :
    ∃ w', g.restrict W w w' ≠ 0 := by
  obtain ⟨phi, -, hpos⟩ := exists_rotation_posDef g
  have hne : (w : V) ≠ 0 := fun h => hw (by exact_mod_cast h)
  refine ⟨w, fun h0 => ?_⟩
  have hlt := hpos (w : V) hne
  rw [g.rotatedRe_apply] at hlt
  have hzero : g.toForm (w : V) (w : V) = 0 := h0
  rw [hzero, mul_zero, Complex.zero_re] at hlt
  exact lt_irrefl 0 hlt

/-- **KS paper Proposition 2.5.** If `g` is an allowable complex metric on `V` and
`W` is any vector subspace of `V`, then the restriction `g|_W` is an allowable
complex metric on `W`.

**Proof strategy from [KS].** The proof proceeds by induction on codimension. For a
codimension-1 subspace `W`, the critical values of `arg(g|_W)` interleave those of
`arg(g)`, giving `θₖ ≥ θ'ₖ ≥ θ_{k+1}`. This implies `∑|θ'ₖ| ≤ ∑|θₖ| < π`.
The general case follows by induction, restricting one dimension at a time. -/
noncomputable def restrict_allowable (g : AllowableComplexMetric V)
    (W : Submodule ℝ V) [FiniteDimensional ℝ W] :
    AllowableComplexMetric W where
  toForm := g.restrict W
  symmetric' := g.restrict_symmetric W
  nondegenerate := g.restrict_nondegenerate W
  angle_cond := by sorry
