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

/-- **KS paper Proposition 2.5, codimension one** (checkpoint 4c): the restriction
of an allowable metric to a hyperplane admits a full `angle_cond` witness. The
diagonal witness comes from `exists_diag_witness_of_rotated_posDef` (rotated
positivity is inherited from the ambient rotation through the coercion), and its
angle-sum bound follows the chain: witness sum = bare `ksAngleOfForm` sum
(`sum_abs_ksAngle_eq_of_form`) = `ksAngleOn` sum (`ksAngleOn_eq_ksAngleOfForm`)
<= ambient `ksAngle` sum (`sum_abs_ksAngleOn_le_sum_abs_ksAngle`, the interlacing
sign-split) = ambient witness sum (`sum_abs_ksAngle_eq_sum_abs_angle_cond`) < pi. -/
theorem restrict_angle_cond_codim_one {U : Type*} [AddCommGroup U] [Module ℝ U]
    [FiniteDimensional ℝ U] (h : AllowableComplexMetric U) (S : Submodule ℝ U)
    (hcodim : Module.finrank ℝ ↥S + 1 = Module.finrank ℝ U) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ ↥S)) ℝ ↥S)
      (eig : Fin (Module.finrank ℝ ↥S) → ℂ),
      AngleCondition eig ∧
      ∀ y, h.restrict S y y = ∑ i, eig i * (b.repr y i : ℂ) ^ 2 := by
  obtain ⟨phi, hphi, hposV⟩ := exists_rotation_posDef h
  have hposS : ∀ y : ↥S, y ≠ 0 → 0 < rotatedReOfForm (h.restrict S) phi y y := by
    intro y hy
    have hne : (y : U) ≠ 0 := fun hc => hy (by exact_mod_cast hc)
    exact hposV (y : U) hne
  obtain ⟨bS, eigS, hnz, hnpr, hang, hposI, hdiagS⟩ :=
    exists_diag_witness_of_rotated_posDef (h.restrict S) (h.restrict_symmetric S)
      phi hphi hposS
  obtain ⟨bU, eigU, hACU, hdiagU⟩ := h.angle_cond
  have hsum : ∑ i, |Complex.arg (eigS i)| < Real.pi := by
    have h1 : ∑ k, |ksAngleOfForm (h.restrict S) k| = ∑ i, |Complex.arg (eigS i)| :=
      sum_abs_ksAngle_eq_of_form (h.restrict S) (h.restrict_symmetric S) phi hphi
        bS eigS hnz hang hdiagS hposI hposS
    have h2 : ∀ k, ksAngleOn h S k = ksAngleOfForm (h.restrict S) k :=
      ksAngleOn_eq_ksAngleOfForm h S (h.restrict S) (fun y => rfl)
    have h3 : ∑ j, |ksAngleOn h S j| ≤ ∑ k, |ksAngle h k| :=
      sum_abs_ksAngleOn_le_sum_abs_ksAngle h S hcodim
    have h4 : ∑ k, |ksAngle h k| = ∑ i, |Complex.arg (eigU i)| :=
      sum_abs_ksAngle_eq_sum_abs_angle_cond h bU hACU hdiagU
    calc ∑ i, |Complex.arg (eigS i)|
        = ∑ k, |ksAngleOfForm (h.restrict S) k| := h1.symm
      _ = ∑ j, |ksAngleOn h S j| :=
          Finset.sum_congr rfl fun j _ => by rw [h2 j]
      _ ≤ ∑ k, |ksAngle h k| := h3
      _ = ∑ i, |Complex.arg (eigU i)| := h4
      _ < Real.pi := hACU.sum_arg_lt_pi
  exact ⟨bS, eigS, ⟨hnz, hnpr, hsum⟩, hdiagS⟩

/-- **The codimension induction** for KS paper Proposition 2.5 (checkpoint 4c, the
flag route): for any subspace `W` of codimension `m`, the restricted form `g|_W`
admits a full `angle_cond` witness. Base case: `W = ⊤`, transport of the ambient
witness along `Submodule.topEquiv`. Step: the codimension-one case
`restrict_angle_cond_codim_one`, applied inside the stage carrier `↥W'` to the
stage metric assembled from the induction hypothesis (a real, sorry-free
`angle_cond` — the sound black-box reuse the flag route was chosen for), then
transported along `Submodule.comapSubtypeEquivOfLe`. -/
theorem restrict_angle_cond_of_codim (m : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
      (g : AllowableComplexMetric V) (W : Submodule ℝ V),
      Module.finrank ℝ V - Module.finrank ℝ ↥W = m →
      ∃ (b : Module.Basis (Fin (Module.finrank ℝ ↥W)) ℝ ↥W)
        (eig : Fin (Module.finrank ℝ ↥W) → ℂ),
        AngleCondition eig ∧
        ∀ w, g.restrict W w w = ∑ i, eig i * (b.repr w i : ℂ) ^ 2 := by
  induction m with
  | zero =>
    intro V _ _ _ g W hm
    have hW : W = ⊤ := Submodule.eq_top_of_finrank_eq (by
      have h1 := Submodule.finrank_le W
      omega)
    subst hW
    exact angle_cond_witness_transport g.toForm (g.restrict ⊤)
      Submodule.topEquiv.symm (fun u => rfl) g.angle_cond
  | succ m IH =>
    intro V _ _ _ g W hm
    have hWtop : W ≠ ⊤ := by
      intro hWeq
      rw [hWeq, finrank_top] at hm
      omega
    obtain ⟨W', hWW', hfrW'⟩ := exists_hyperplane_above W hWtop
    have hle : W ≤ W' := le_of_lt hWW'
    have hm' : Module.finrank ℝ V - Module.finrank ℝ ↥W' = m := by
      have h1 := Submodule.finrank_le W'
      omega
    obtain ⟨bW', eigW', hACW', hdiagW'⟩ := IH g W' hm'
    let gW' : AllowableComplexMetric ↥W' :=
      { toForm := g.restrict W'
        symmetric' := g.restrict_symmetric W'
        nondegenerate := g.restrict_nondegenerate W'
        angle_cond := ⟨bW', eigW', hACW', hdiagW'⟩ }
    have hcodimS : Module.finrank ℝ ↥(Submodule.comap W'.subtype W) + 1
        = Module.finrank ℝ ↥W' := by
      rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, hfrW']
    obtain ⟨bS, eigS, hACS, hdiagS⟩ :=
      restrict_angle_cond_codim_one gW' (Submodule.comap W'.subtype W) hcodimS
    exact angle_cond_witness_transport
      (gW'.restrict (Submodule.comap W'.subtype W)) (g.restrict W)
      (Submodule.comapSubtypeEquivOfLe hle) (fun u => rfl)
      ⟨bS, eigS, hACS, hdiagS⟩

/-- **The `angle_cond` witness for any restriction** (KS paper Proposition 2.5,
checkpoint 4c): `g|_W` admits a diagonalizing basis whose coefficients satisfy
`AngleCondition`, by the flag induction on the codimension of `W`. -/
theorem restrict_angle_cond (g : AllowableComplexMetric V) (W : Submodule ℝ V) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ ↥W)) ℝ ↥W)
      (eig : Fin (Module.finrank ℝ ↥W) → ℂ),
      AngleCondition eig ∧
      ∀ w, g.restrict W w w = ∑ i, eig i * (b.repr w i : ℂ) ^ 2 :=
  restrict_angle_cond_of_codim (Module.finrank ℝ V - Module.finrank ℝ ↥W) g W rfl

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
  angle_cond := restrict_angle_cond g W
