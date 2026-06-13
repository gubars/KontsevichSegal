/- The Shilov boundary of QC(V): real Lorentzian metrics of signature (d-1, 1) —
and no other nondegenerate real metrics — belong to the Shilov boundary. This is
the key result explaining why Lorentzian signature is special.
KS paper Section 2, pages 8-9.

A real metric has each |arg(λᵢ)| equal to 0 (positive eigenvalue) or π (negative
eigenvalue), so the angle condition ∑ᵢ |arg λᵢ| < π fails for every real metric
that is not positive-definite. A real Lorentzian metric — exactly one negative
eigenvalue — sits exactly at the threshold ∑ᵢ |arg λᵢ| = π: it is the limit of
allowable metrics in which the negative eigenvalue is perturbed off the negative
real axis (|arg| = π - δ) while the positive eigenvalues stay real positive.
Real metrics with two or more negative eigenvalues would need ∑ᵢ |arg λᵢ| ≥ 2π in
the limit and so are not even in the closure of QC(V).

The Shilov boundary contains two disjoint copies of Lorentzian metrics,
corresponding to the two ways the negative eigenvalue can approach the negative
real axis (from the upper or lower half-plane). These two copies are interchanged
by complex conjugation; the nondegenerate points of the Shilov boundary are the
time-oriented Lorentzian metrics. (Distinguishing the two copies as boundary
*points* requires the bounded affine-variety realization of QC(V) from the proof
of Prop 2.7 — the branch of √det(g) differs in the two limits — which is beyond
the current formalization; see `two_copies_on_boundary` below.)
-/

import KontsevichSegal.ComplexMetrics.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul

variable {d : ℕ}

/-! ## Lorentzian signature -/

/-- A real bilinear form on `V` has *Lorentzian signature* `(d-1, 1)` if there
exists a basis in which it diagonalizes as `∑ᵢ sᵢ · xᵢ · yᵢ` where each
`sᵢ ∈ {+1, -1}` and exactly one `sᵢ` equals `-1`.

KS paper Section 2, page 9: real Lorentzian metrics are characterized as the
nondegenerate real metrics on the Shilov boundary of QC(V). -/
def IsLorentzian {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    (sign : Fin (Module.finrank ℝ V) → ℝ),
    -- Each sign is ±1.
    (∀ i, sign i = 1 ∨ sign i = -1) ∧
    -- Exactly one sign equals -1 (Lorentzian signature).
    (∃! i, sign i = -1) ∧
    -- The form diagonalizes as ∑ᵢ sᵢ · xᵢ · yᵢ in this basis.
    (∀ v w, φ v w = ∑ i, sign i * (b.repr v i) * (b.repr w i))

/-! ## KS paper Section 2, page 9: Shilov boundary results -/

/-- **KS paper Section 2, page 9 — Lorentzian metrics on the boundary.**
A real Lorentzian metric `φ` on `V` lies on the boundary of QC(V):

1. φ is a *limit of allowable metrics*: there is a basis `b` such that for
   every `ε > 0` some allowable complex metric is entry-wise within `ε` of φ
   on `b`. (Closeness of the entries on a fixed basis is the canonical topology
   on the finite-dimensional space of forms.)
2. φ is *not itself allowable*: no allowable metric has the same quadratic
   form as φ.

Proof sketch: diagonalize φ as `∑ sᵢ yᵢ²` with exactly one `sᵢ = -1`, and
perturb the negative eigenvalue to `exp(i(π - δ))`, giving angle sum `π - δ < π`.
For (2), φ takes a real negative value on the timelike basis vector, which an
allowable metric cannot (`not_neg_real_axis`).

KS paper, paragraph after Theorem 2.2: the Lorentzian metrics are approached as
`∑ᵢ |arg λᵢ| → π` from below. -/
theorem lorentzian_on_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hL : IsLorentzian φ) :
    (∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ ε : ℝ, 0 < ε →
        ∃ g : AllowableComplexMetric V,
          ∀ i j, ‖g.toForm (b i) (b j) - ↑(φ (b i) (b j))‖ < ε) ∧
    (∀ g : AllowableComplexMetric V, ∃ v, g.toForm v v ≠ ↑(φ v v)) := by
  classical
  obtain ⟨b, sign, hsign, hone, hφ⟩ := hL
  obtain ⟨i₀, hi₀, huniq⟩ := hone
  have hsign_iff : ∀ i, sign i = -1 ↔ i = i₀ :=
    fun i => ⟨huniq i, fun h => h ▸ hi₀⟩
  -- Coordinates of basis vectors are Kronecker deltas.
  have hreprbR : ∀ i k, b.repr (b i) k = if i = k then (1 : ℝ) else 0 := by
    intro i k
    rw [Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  have hreprbC : ∀ i k, ((b.repr (b i) k : ℝ) : ℂ) = if i = k then (1 : ℂ) else 0 := by
    intro i k
    rw [hreprbR]
    split_ifs <;> simp
  -- φ on pairs of basis vectors.
  have hφb : ∀ i j, φ (b i) (b j) = if i = j then sign i else 0 := by
    intro i j
    rw [hφ]
    calc ∑ k, sign k * b.repr (b i) k * b.repr (b j) k
        = ∑ k, if i = k then (if j = k then sign k else 0) else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hreprbR, hreprbR]
          split_ifs <;> ring
      _ = if i ∈ Finset.univ then (if j = i then sign i else 0) else 0 :=
          Finset.sum_ite_eq _ _ _
      _ = if j = i then sign i else 0 := if_pos (Finset.mem_univ i)
      _ = if i = j then sign i else 0 := if_congr eq_comm rfl rfl
  constructor
  · -- φ is an entry-wise limit of allowable metrics on the basis `b`.
    refine ⟨b, fun ε hε => ?_⟩
    -- The perturbation parameter.
    set δ : ℝ := min 1 (ε / 4) with hδdef
    have hδpos : 0 < δ := lt_min one_pos (by linarith)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδπ : δ < Real.pi := by linarith [Real.two_le_pi]
    have hδε : 2 * δ < ε := by
      have h4 : δ ≤ ε / 4 := min_le_right _ _
      linarith
    -- Perturbed eigenvalues: the timelike direction moves to exp(i(π-δ)).
    set eig : Fin (Module.finrank ℝ V) → ℂ := fun i =>
      if i = i₀ then Complex.exp (((Real.pi - δ : ℝ) : ℂ) * Complex.I) else 1
      with heig
    have heignz : ∀ i, eig i ≠ 0 := by
      intro i
      simp only [heig]
      split_ifs
      · exact Complex.exp_ne_zero _
      · exact one_ne_zero
    -- The angle condition for the perturbed eigenvalues.
    have hAC : AngleCondition eig := by
      refine ⟨heignz, ?_, ?_⟩
      · intro i
        by_cases h : i = i₀
        · refine Or.inr ?_
          simp only [heig, h, if_true]
          rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub]
          exact (Real.sin_pos_of_pos_of_lt_pi hδpos hδπ).ne'
        · refine Or.inl ?_
          simp [heig, h]
      · have hargeig : ∀ i, |Complex.arg (eig i)|
            = if i = i₀ then Real.pi - δ else 0 := by
          intro i
          by_cases h : i = i₀
          · simp only [heig, h, if_true]
            have harg : Complex.arg (Complex.exp (((Real.pi - δ : ℝ) : ℂ) * Complex.I))
                = Real.pi - δ := by
              rw [Complex.exp_mul_I]
              exact Complex.arg_cos_add_sin_mul_I
                ⟨by linarith [Real.pi_pos], by linarith⟩
            rw [harg, abs_of_pos (by linarith [Real.two_le_pi])]
          · simp [heig, h, Complex.arg_one]
        calc ∑ i, |Complex.arg (eig i)|
            = ∑ i, if i = i₀ then Real.pi - δ else 0 :=
              Finset.sum_congr rfl fun i _ => hargeig i
          _ = if i₀ ∈ Finset.univ then Real.pi - δ else 0 :=
              Finset.sum_ite_eq' _ _ _
          _ = Real.pi - δ := if_pos (Finset.mem_univ i₀)
          _ < Real.pi := by linarith
    -- Bilinearity of the perturbed form.
    have hadd₁ : ∀ (m₁ m₂ n : V),
        (∑ i, eig i * (b.repr (m₁ + m₂) i : ℂ) * (b.repr n i : ℂ))
          = (∑ i, eig i * (b.repr m₁ i : ℂ) * (b.repr n i : ℂ))
            + ∑ i, eig i * (b.repr m₂ i : ℂ) * (b.repr n i : ℂ) := by
      intro m₁ m₂ n
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, Finsupp.add_apply, Complex.ofReal_add]
      ring
    have hsmul₁ : ∀ (c : ℝ) (m n : V),
        (∑ i, eig i * (b.repr (c • m) i : ℂ) * (b.repr n i : ℂ))
          = c • ∑ i, eig i * (b.repr m i : ℂ) * (b.repr n i : ℂ) := by
      intro c m n
      rw [Complex.real_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      ring
    have hadd₂ : ∀ (m n₁ n₂ : V),
        (∑ i, eig i * (b.repr m i : ℂ) * (b.repr (n₁ + n₂) i : ℂ))
          = (∑ i, eig i * (b.repr m i : ℂ) * (b.repr n₁ i : ℂ))
            + ∑ i, eig i * (b.repr m i : ℂ) * (b.repr n₂ i : ℂ) := by
      intro m n₁ n₂
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, Finsupp.add_apply, Complex.ofReal_add]
      ring
    have hsmul₂ : ∀ (c : ℝ) (m n : V),
        (∑ i, eig i * (b.repr m i : ℂ) * (b.repr (c • n) i : ℂ))
          = c • ∑ i, eig i * (b.repr m i : ℂ) * (b.repr n i : ℂ) := by
      intro c m n
      rw [Complex.real_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      ring
    -- Assemble the allowable complex metric.
    refine ⟨⟨LinearMap.mk₂ ℝ
        (fun v w => ∑ i, eig i * (b.repr v i : ℂ) * (b.repr w i : ℂ))
        hadd₁ hsmul₁ hadd₂ hsmul₂, ?_, ?_, ?_⟩, ?_⟩
    · -- Symmetry.
      intro v w
      simp only [LinearMap.mk₂_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    · -- Nondegeneracy: pair with the basis vector of a nonzero coordinate.
      intro v hv
      have hrepr : b.repr v ≠ 0 := fun h => hv (b.repr.map_eq_zero_iff.mp h)
      obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hrepr
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
      refine ⟨b j, ?_⟩
      simp only [LinearMap.mk₂_apply]
      have hval : (∑ k, eig k * (b.repr v k : ℂ) * (b.repr (b j) k : ℂ))
          = eig j * (b.repr v j : ℂ) := by
        calc ∑ k, eig k * (b.repr v k : ℂ) * (b.repr (b j) k : ℂ)
            = ∑ k, if j = k then eig k * (b.repr v k : ℂ) else 0 := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hreprbC]
              split_ifs <;> ring
          _ = if j ∈ Finset.univ then eig j * (b.repr v j : ℂ) else 0 :=
              Finset.sum_ite_eq _ _ _
          _ = eig j * (b.repr v j : ℂ) := if_pos (Finset.mem_univ j)
      rw [hval]
      exact mul_ne_zero (heignz j) (Complex.ofReal_ne_zero.mpr hj)
    · -- The angle condition, witnessed by `b` and `eig` themselves.
      refine ⟨b, eig, hAC, fun v => ?_⟩
      simp only [LinearMap.mk₂_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    · -- Entry-wise closeness to φ on the basis `b`.
      intro i j
      simp only [LinearMap.mk₂_apply]
      have hentry : (∑ k, eig k * (b.repr (b i) k : ℂ) * (b.repr (b j) k : ℂ))
          = if i = j then eig i else 0 := by
        calc ∑ k, eig k * (b.repr (b i) k : ℂ) * (b.repr (b j) k : ℂ)
            = ∑ k, if i = k then (if j = k then eig k else 0) else 0 := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hreprbC, hreprbC]
              split_ifs <;> ring
          _ = if i ∈ Finset.univ then (if j = i then eig i else 0) else 0 :=
              Finset.sum_ite_eq _ _ _
          _ = if j = i then eig i else 0 := if_pos (Finset.mem_univ i)
          _ = if i = j then eig i else 0 := if_congr eq_comm rfl rfl
      rw [hentry, hφb]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        by_cases h0 : i = i₀
        · subst h0
          rw [hi₀]
          simp only [heig, if_true]
          -- ‖exp(i(π-δ)) - (-1)‖ = ‖exp(-iδ) - 1‖ ≤ 2δ < ε.
          have hexpval : Complex.exp (((Real.pi - δ : ℝ) : ℂ) * Complex.I)
              = -Complex.exp (((-δ : ℝ) : ℂ) * Complex.I) := by
            rw [show ((Real.pi - δ : ℝ) : ℂ) * Complex.I
                  = (Real.pi : ℂ) * Complex.I + ((-δ : ℝ) : ℂ) * Complex.I by
                push_cast; ring,
              Complex.exp_add, Complex.exp_pi_mul_I]
            ring
          rw [hexpval,
            show -Complex.exp (((-δ : ℝ) : ℂ) * Complex.I) - (((-1 : ℝ)) : ℂ)
                = -(Complex.exp (((-δ : ℝ) : ℂ) * Complex.I) - 1) by push_cast; ring,
            norm_neg]
          have hnorm : ‖((-δ : ℝ) : ℂ) * Complex.I‖ = δ := by
            rw [norm_mul, Complex.norm_I, Complex.norm_real]
            simp [abs_of_pos hδpos]
          calc ‖Complex.exp (((-δ : ℝ) : ℂ) * Complex.I) - 1‖
              ≤ 2 * ‖((-δ : ℝ) : ℂ) * Complex.I‖ :=
                Complex.norm_exp_sub_one_le (by rw [hnorm]; exact hδ1)
            _ = 2 * δ := by rw [hnorm]
            _ < ε := hδε
        · -- Spacelike direction: the entry is unchanged.
          have hs1 : sign i = 1 := by
            rcases hsign i with h | h
            · exact h
            · exact absurd ((hsign_iff i).mp h) h0
          simp only [heig, if_neg h0, hs1]
          simpa using hε
      · rw [if_neg hij, if_neg hij]
        simpa using hε
  · -- φ itself is not allowable: it is real and negative on the timelike vector.
    intro g
    refine ⟨b i₀, fun hgφ => ?_⟩
    have hφneg : φ (b i₀) (b i₀) = -1 := by
      rw [hφb, if_pos rfl, hi₀]
    refine not_neg_real_axis g (b i₀) (b.ne_zero i₀) ⟨?_, ?_⟩
    · rw [hgφ, Complex.ofReal_im]
    · rw [hgφ, hφneg, Complex.ofReal_re]
      norm_num

/-- **KS paper Section 2, page 9 — only Lorentzian on the boundary.**
If a real nondegenerate bilinear form lies on the boundary of QC(V) — it is a
limit of allowable complex metrics (entry-wise on a fixed basis `b`) but is not
positive-definite (the positive-definite forms are the *interior* real points
of QC(V), not boundary points) — then it has Lorentzian signature `(d-1, 1)`.

If the metric is real, each `|arg(λᵢ)|` is either `0` (positive eigenvalue)
or `π` (negative eigenvalue). For a limit of allowable metrics, at most one
`|arg(λᵢ)|` can reach `π` (a 2-dimensional negative-definite subspace would
force `∑ᵢ |arg(λᵢ)| → 2π`, contradicting the angle condition under restriction).
Nondegeneracy plus failure of positive-definiteness then force exactly one
negative eigenvalue — Lorentzian signature.

KS paper, paragraph after Theorem 2.2. -/
theorem only_lorentzian_on_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V)
    /- Nondegeneracy of the real form. -/
    (hnd : ∀ v, v ≠ 0 → ∃ w, φ v w ≠ 0)
    /- The form is a limit of allowable complex metrics, entry-wise on `b`. -/
    (hbdy : ∀ ε : ℝ, 0 < ε →
      ∃ g : AllowableComplexMetric V,
        ∀ i j, ‖g.toForm (b i) (b j) - ↑(φ (b i) (b j))‖ < ε)
    /- The form is not positive-definite (otherwise it lies in the interior of
       QC(V), not on the boundary). -/
    (hnotpos : ¬ ∀ v, v ≠ 0 → 0 < φ v v) :
    IsLorentzian φ := by
  classical
  -- STEP 1: φ is symmetric. Each entry `φ(bᵢ,bⱼ)` is within `2ε` of the
  -- symmetric entry `φ(bⱼ,bᵢ)` (via a symmetric allowable `g` close to both),
  -- for every `ε`, hence they are equal; extend bilinearly through `φ = φ.flip`.
  have hsymm : ∀ v w, φ v w = φ w v := by
    have hbasis : ∀ i j, φ (b i) (b j) = φ (b j) (b i) := by
      intro i j
      by_contra hne
      set cst : ℝ := |φ (b i) (b j) - φ (b j) (b i)| with hcst
      have hcpos : 0 < cst := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨g, hg⟩ := hbdy (cst / 2) (by linarith)
      have h1 := hg i j
      have h2 := hg j i
      have hsg : g.toForm (b i) (b j) = g.toForm (b j) (b i) := g.symmetric' _ _
      have hrw : ((φ (b i) (b j) : ℂ)) - (φ (b j) (b i) : ℂ)
          = ((φ (b i) (b j) : ℂ) - g.toForm (b i) (b j))
            + (g.toForm (b j) (b i) - (φ (b j) (b i) : ℂ)) := by
        rw [hsg]; ring
      have key : ‖((φ (b i) (b j) : ℂ)) - (φ (b j) (b i) : ℂ)‖ < cst := by
        calc ‖((φ (b i) (b j) : ℂ)) - (φ (b j) (b i) : ℂ)‖
            = ‖((φ (b i) (b j) : ℂ) - g.toForm (b i) (b j))
                + (g.toForm (b j) (b i) - (φ (b j) (b i) : ℂ))‖ := by rw [hrw]
          _ ≤ ‖(φ (b i) (b j) : ℂ) - g.toForm (b i) (b j)‖
                + ‖g.toForm (b j) (b i) - (φ (b j) (b i) : ℂ)‖ := norm_add_le _ _
          _ < cst / 2 + cst / 2 := by
              apply add_lt_add
              · rw [norm_sub_rev]; exact h1
              · exact h2
          _ = cst := by ring
      have heq : ‖((φ (b i) (b j) : ℂ)) - (φ (b j) (b i) : ℂ)‖ = cst := by
        rw [hcst, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [heq] at key
      exact lt_irrefl cst key
    have hflip : φ = φ.flip := by
      apply b.ext; intro i; apply b.ext; intro j
      simp only [LinearMap.flip_apply]
      exact hbasis i j
    intro v w
    have h := LinearMap.congr_fun (LinearMap.congr_fun hflip v) w
    rw [LinearMap.flip_apply] at h
    exact h
  -- General double-sum expansion of `φ` in any basis.
  have expand : ∀ (e : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) (v w : V),
      φ v w = ∑ i, ∑ j, (e.repr v i) * (e.repr w j) * φ (e i) (e j) := by
    intro e v w
    conv_lhs => rw [← e.sum_repr v, ← e.sum_repr w]
    simp_rw [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- STEP 2: diagonalize φ over ℝ with ±1 signs.
  -- Orthogonal basis `c` for the symmetric form (Mathlib; char ≠ 2).
  obtain ⟨c, hcortho⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (B := φ) ⟨fun v w => hsymm v w⟩
  have hoff : ∀ i j, i ≠ j → φ (c i) (c j) = 0 := fun i j hij => hcortho hij
  -- Each diagonal entry is nonzero, else `c i` is undetected by `φ`,
  -- contradicting nondegeneracy.
  have hdne : ∀ i, φ (c i) (c i) ≠ 0 := by
    intro i hdi
    obtain ⟨w, hw⟩ := hnd (c i) (c.ne_zero i)
    apply hw
    have hexp : φ (c i) w = ∑ j, (c.repr w j) * φ (c i) (c j) := by
      conv_lhs => rw [← c.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    rw [hexp, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hji => by rw [hoff i j (Ne.symm hji), mul_zero]), hdi, mul_zero]
  -- Rescale each `c i` by `(√|φ(cᵢ,cᵢ)|)⁻¹` to normalize the diagonal to ±1.
  have hrpos : ∀ i, 0 < (Real.sqrt |φ (c i) (c i)|)⁻¹ :=
    fun i => inv_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr (hdne i)))
  set r : Fin (Module.finrank ℝ V) → ℝ := fun i => (Real.sqrt |φ (c i) (c i)|)⁻¹ with hr
  set e : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    c.unitsSMul (fun i => Units.mk0 (r i) (hrpos i).ne') with he_def
  have he : ∀ i, e i = r i • c i := by
    intro i
    simp only [he_def, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hephi : ∀ i j, φ (e i) (e j) = r i * r j * φ (c i) (c j) := by
    intro i j
    simp only [he, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  -- The signs, and the diagonal value of `φ` in the rescaled basis.
  set sign : Fin (Module.finrank ℝ V) → ℝ :=
    fun i => φ (c i) (c i) / |φ (c i) (c i)| with hsign_def
  have hdiag_val : ∀ i, φ (e i) (e i) = sign i := by
    intro i
    have hx : (0 : ℝ) < |φ (c i) (c i)| := abs_pos.mpr (hdne i)
    have hsq : r i * r i = |φ (c i) (c i)|⁻¹ := by
      simp only [hr]
      rw [← mul_inv, Real.mul_self_sqrt hx.le]
    rw [hephi i i, hsq]
    simp only [hsign_def]
    rw [div_eq_inv_mul]
  have hsign_pm : ∀ i, sign i = 1 ∨ sign i = -1 := by
    intro i
    simp only [hsign_def]
    rcases lt_or_gt_of_ne (hdne i) with h | h
    · right; rw [abs_of_neg h, div_neg, div_self (hdne i)]
    · left; rw [abs_of_pos h, div_self (hdne i)]
  have heoff : ∀ i j, i ≠ j → φ (e i) (e j) = 0 :=
    fun i j hij => by rw [hephi i j, hoff i j hij, mul_zero]
  -- The bilinear diagonalization required by `IsLorentzian`.
  have hdiag : ∀ v w, φ v w = ∑ i, sign i * (e.repr v i) * (e.repr w i) := by
    intro v w
    rw [expand e v w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hji => by rw [heoff i j (Ne.symm hji), mul_zero]), hdiag_val i]
    ring
  -- STEP 3: at least one sign is negative. If all signs were +1 then
  -- `φ v v = ∑ (e.repr v i)² > 0` for `v ≠ 0`, i.e. φ is positive-definite,
  -- contradicting `hnotpos`.
  have hneg : ∃ i, sign i = -1 := by
    by_contra hcon
    push_neg at hcon
    have hallpos : ∀ i, sign i = 1 := fun i => (hsign_pm i).resolve_right (hcon i)
    apply hnotpos
    intro v hv
    rw [hdiag v v]
    have hterm : ∀ i, sign i * (e.repr v i) * (e.repr v i) = (e.repr v i) ^ 2 :=
      fun i => by rw [hallpos i]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have hrepr : e.repr v ≠ 0 := fun h => hv (e.repr.map_eq_zero_iff.mp h)
    obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hrepr
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi₀
    exact Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨i₀, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi₀))⟩
  obtain ⟨i₀, hi₀⟩ := hneg
  refine ⟨e, sign, hsign_pm, ⟨i₀, hi₀, ?_⟩, hdiag⟩
  -- STEP 4 (remaining): at most one negative sign, i.e. the negative direction
  -- is unique. PROOF OBLIGATION: given `j` with `sign j = -1` and `j ≠ i₀`,
  -- derive a contradiction. The intended route (docs/only_lorentzian_plan.md
  -- step 4): the 2-plane `W = span {e i₀, e j}` is φ-negative-definite
  -- (`φ v v = -((e.repr v i₀)² + (e.repr v j)²) < 0` for nonzero `v ∈ W`);
  -- transferring the entry-wise ε-closeness of `hbdy` to a uniform bound on
  -- `W` gives, for small ε, an allowable `g` with `Re (g.toForm v v) < 0` for
  -- all nonzero `v ∈ W`; a dimension count of `W` against
  -- `P = span {c k : 0 ≤ (eigᵧ k).re}` (using
  -- `Submodule.finrank_sup_add_finrank_inf_eq` and
  -- `Module.Basis.repr_support_subset_of_mem_span`) produces a nonzero
  -- `v ∈ W ⊓ P` with `Re (g.toForm v v) ≥ 0`, contradiction; equivalently two
  -- eigenvalues of `g` with `Re < 0` give, via `Complex.abs_arg_lt_pi_div_two_iff`,
  -- `∑ |arg| ≥ π`, contradicting `AngleCondition.sum_arg_lt_pi`.
  intro j hj
  sorry

/-- **KS paper Section 2, page 9 — two copies on the Shilov boundary.**
PLACEHOLDER (`True` conclusion). The paper's actual claim, quoted:

"In fact the Shilov boundary of Q_C(V) contains *two* disjoint copies of the
space of Lorentzian metrics on V, for an eigenvalue λ can approach the
negative real axis either from above or from below. The two copies are
interchanged by the complex-conjugation map on Q_C(V). Because of our choice
to make the orientation-reversing elements of GL(V) act antilinearly on the
orientation-line of V, we can say that the nondegenerate points of the Shilov
boundary are the *time-oriented* Lorentzian metrics."

The subject of the claim is the **Shilov boundary** of QC(V) "regarded as a
bounded domain in an affine variety (cf. the proof of 2.7)". This cannot be
faithfully expressed with current infrastructure. Precisely missing:

1. **Induced forms on exterior powers / Hodge star `∗_g`** (same Mathlib gap
   blocking `Equivalence.lean`): needed for the embedding of QC(V) into the
   product `∏_{0 ≤ p ≤ d/2} U(⋀ᵖ V)` of Siegel domains from the proof of
   Prop 2.7. The p = 0 factor is `vol_g = (det g)^(1/2)`, whose branch is
   what separates the two copies — in the naive closure of QC(V) inside
   S²(V*_ℂ) the two copies coincide, so no statement about subsets of the
   space of forms can express the disjointness.
2. **Siegel domain theory and the Cayley transform** ("unit disc"
   realization): needed to regard the image as a *bounded* domain, without
   which sup-norm characterizations degenerate.
3. **The Shilov boundary itself**: the smallest compact subset of the closure
   on which every holomorphic function defined near the closure attains its
   sup ([Hör] p. 67). Statable from Mathlib's holomorphy + topology once
   (1)–(2) exist, but meaningless before.

(A partial double-cover formulation — the closure of the graph
`{(g, √det g) : g ∈ QC(V)}` having exactly two conjugate-swapped points over
each Lorentzian metric — *is* expressible today, but its subject is not the
Shilov boundary, so per the project's no-approximations policy it is not used
as a stand-in.)

KS paper, paragraph after Theorem 2.2. -/
theorem two_copies_on_boundary (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    -- PLACEHOLDER: True stands for the Shilov-boundary claim quoted in the
    -- docstring, which cannot yet be expressed (see items 1-3 above).
    True := by
  trivial
