/- F2 / KS Proposition 2.4 (KSTeX 214-222): the parametrization of QC(V) — checkpoint B.

This file starts the F2 build: the contractible base of positive-definite real forms,
and the modulus form ∑|λ_k| y_k² built from a diagonalizing witness, together with the
Θ-precursor `sinPencil`, a function of `g` alone.

IMPORT NOTE. The `Contractibility` import is for REUSE of two convexity lemmas
(`KontsevichSegal.Retraction.posDef_convex` and `convex_pos_combo`); it is NOT a logical
dependence of Proposition 2.4 on the retraction proof of `QC_contractible`.

HONESTY CONSTRAINT, recorded up front. `modulusForm`'s witness-independence is UNPROVED:
it is carried as the tracked sorry `modulus_welldef`. Until that closes, `modulusForm`
is only known to equal ∑|λ_k| y_k² FOR THE CHOSEN WITNESS — a positive-definite form
built from a diagonalizing witness, asserted by KS (KSTeX 214-216) to be
witness-independent. It must NOT be called canonical, and must not be identified with
KS's g₀, until `modulus_welldef` is proved.

Blueprint: `lem:posdef-base` and `lem:modulus-form` in `blueprint/src/content.tex`.
Reviewed artifact: `blueprint/restatements/f2-checkpointB.md`.
-/

import KontsevichSegal.ComplexMetrics.Contractibility
import KontsevichSegal.ComplexMetrics.EigenvalueMinmax
import KontsevichSegal.ComplexMetrics.Domain
import Mathlib.Analysis.Convex.Contractible

namespace KontsevichSegal.Parametrization

open KontsevichSegal.Hodge

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-! ## The base: symmetric positive-definite real forms, and its contractibility -/

/-- The base of KS Proposition 2.4's fibre bundle: symmetric positive-definite real
bilinear forms on `V` (the `BilinForm` spelling — norm-free, and finite-dimensionality
synthesizes), with the topology induced from the canonical module topology. -/
def PosDefForm (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    Type _ :=
  {g₀ : LinearMap.BilinForm ℝ V //
    (∀ v w, g₀ v w = g₀ w v) ∧ ∀ v, v ≠ 0 → 0 < g₀ v v}

noncomputable instance : TopologicalSpace (PosDefForm V) :=
  letI : TopologicalSpace (LinearMap.BilinForm ℝ V) := moduleTopology ℝ _
  instTopologicalSpaceSubtype

/-- The Euclidean form is symmetric (real-form spelling of `euclidForm_symm`). -/
theorem euclidR_symm (v w : V) : euclidR v w = euclidR w v := by
  change (∑ i, (Module.finBasis ℝ V).repr v i * (Module.finBasis ℝ V).repr w i)
      = ∑ i, (Module.finBasis ℝ V).repr w i * (Module.finBasis ℝ V).repr v i
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The Euclidean form is positive definite (real-form spelling of
`euclidForm_re_pos`). -/
theorem euclidR_posDef (v : V) (hv : v ≠ 0) : 0 < euclidR v v := by
  have h := euclidForm_re_pos v hv
  rwa [euclidForm_apply, Complex.ofReal_re] at h

omit [FiniteDimensional ℝ V] in
/-- The set of symmetric positive-definite forms is convex: symmetry is a linear
condition, and positive-definiteness is closed under positive combinations. -/
theorem symmPosDef_convex :
    Convex ℝ {P : LinearMap.BilinForm ℝ V |
      (∀ v w, P v w = P w v) ∧ ∀ v, v ≠ 0 → 0 < P v v} := by
  intro P hP Q hQ a c ha hc hac
  refine ⟨fun v w => ?_, fun v hv => ?_⟩
  · have e1 : (a • P + c • Q) v w = a * P v w + c * Q v w := by
      simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have e2 : (a • P + c • Q) w v = a * P w v + c * Q w v := by
      simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e1, e2, hP.1 v w, hQ.1 v w]
  · have e : (a • P + c • Q) v v = a * P v v + c * Q v v := by
      simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change 0 < (a • P + c • Q) v v
    rw [e, show a = 1 - c by linarith]
    exact KontsevichSegal.Retraction.convex_pos_combo hc (by linarith)
      (hP.2 v hv) (hQ.2 v hv)

set_option maxHeartbeats 1000000 in
-- unifying the declared subtype topology with the proof-side instance grinds through
-- `moduleTopology`'s sInf at whnf; the default heartbeat limit is not enough
/-- **The base is contractible** (one of KS's two ingredients for the contractibility
clause of Proposition 2.4, KSTeX 220-222): the symmetric positive-definite forms are a
nonempty convex set in the space of real bilinear forms. -/
theorem base_contractible : ContractibleSpace (PosDefForm V) := by
  letI : TopologicalSpace (LinearMap.BilinForm ℝ V) := moduleTopology ℝ _
  haveI : ContinuousAdd (LinearMap.BilinForm ℝ V) :=
    IsModuleTopology.toContinuousAdd ℝ _
  haveI : ContinuousSMul ℝ (LinearMap.BilinForm ℝ V) :=
    ModuleTopology.continuousSMul ℝ _
  have hne : {P : LinearMap.BilinForm ℝ V |
      (∀ v w, P v w = P w v) ∧ ∀ v, v ≠ 0 → 0 < P v v}.Nonempty :=
    ⟨euclidR, euclidR_symm, euclidR_posDef⟩
  exact Convex.contractibleSpace symmPosDef_convex hne

/-! ## The modulus form, from the chosen diagonalizing witness -/

/-- The chosen diagonalizing basis of `g` (the `angle_cond` witness). -/
noncomputable def modBasis (g : AllowableComplexMetric V) :
    Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
  g.angle_cond.choose

/-- The chosen eigenvalue tuple of `g`. -/
noncomputable def modEig (g : AllowableComplexMetric V) :
    Fin (Module.finrank ℝ V) → ℂ :=
  g.angle_cond.choose_spec.choose

theorem modEig_angleCondition (g : AllowableComplexMetric V) :
    AngleCondition (modEig g) :=
  g.angle_cond.choose_spec.choose_spec.1

theorem modEig_diag (g : AllowableComplexMetric V) :
    ∀ v, g.toForm v v = ∑ i, modEig g i * ((modBasis g).repr v i : ℂ) ^ 2 :=
  g.angle_cond.choose_spec.choose_spec.2

/-- The modulus form `∑ |λ_k| y_k²`, built from the CHOSEN `angle_cond` witness of `g`.
Witness-independence — KS's assertion that this form is canonically associated to `g`
(KSTeX 214-216) — is UNPROVED and carried as the tracked sorry `modulus_welldef`; until
that closes, this form is not known to be KS's `g₀`. -/
noncomputable def modulusForm (g : AllowableComplexMetric V) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ
    (fun v w => ∑ k, ‖modEig g k‖ * ((modBasis g).repr v k * (modBasis g).repr w k))
    (fun v₁ v₂ w => by
      simp only [map_add, Finsupp.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum,
        mul_assoc, mul_left_comm])
    (fun v w₁ w₂ => by
      simp only [map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum,
        mul_left_comm])

theorem modulusForm_apply (g : AllowableComplexMetric V) (v w : V) :
    modulusForm g v w
      = ∑ k, ‖modEig g k‖ * ((modBasis g).repr v k * (modBasis g).repr w k) := rfl

/-- The modulus form is positive definite. Witness-local: it needs no canonicity, only
that the chosen eigenvalues are nonzero. -/
theorem modulusForm_posDef (g : AllowableComplexMetric V) :
    ∀ v, v ≠ 0 → 0 < modulusForm g v v := by
  intro v hv
  rw [modulusForm_apply]
  have hrepr : (modBasis g).repr v ≠ 0 :=
    fun h => hv ((modBasis g).repr.map_eq_zero_iff.mp h)
  obtain ⟨i0, hi0⟩ := Finsupp.ne_iff.mp hrepr
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hi0
  refine Finset.sum_pos'
    (fun k _ => mul_nonneg (norm_nonneg _) (mul_self_nonneg _))
    ⟨i0, Finset.mem_univ _, ?_⟩
  exact mul_pos (norm_pos_iff.mpr ((modEig_angleCondition g).nonzero i0))
    (mul_self_pos.mpr hi0)

theorem modulusForm_nondegenerate (g : AllowableComplexMetric V) :
    (modulusForm g).Nondegenerate :=
  nondegenerate_of_posDef _ (modulusForm_posDef g)

/-! ## The transfer lemmas: witness angle data is shared -/

/-- The argument of any eigenvalue of one witness occurs among the arguments of the
other — via the choice-free `ksAngle` multiset bridge. -/
theorem arg_mem_transfer (g : AllowableComplexMetric V)
    {b b' : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig eig' : Fin (Module.finrank ℝ V) → ℂ}
    (hAC : AngleCondition eig)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (hAC' : AngleCondition eig')
    (hdiag' : ∀ v, g.toForm v v = ∑ i, eig' i * (b'.repr v i : ℂ) ^ 2)
    (j : Fin (Module.finrank ℝ V)) :
    ∃ k, Complex.arg (eig' j) = Complex.arg (eig k) := by
  have h1 := ksAngle_multiset_eq_angle_cond g b hAC hdiag
  have h2 := ksAngle_multiset_eq_angle_cond g b' hAC' hdiag'
  have heq : Multiset.map (fun i => Complex.arg (eig' i)) Finset.univ.val
      = Multiset.map (fun i => Complex.arg (eig i)) Finset.univ.val := by
    rw [← h2, h1]
  have hmem : Complex.arg (eig' j)
      ∈ Multiset.map (fun i => Complex.arg (eig i)) Finset.univ.val := by
    rw [← heq]
    exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
  obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp hmem
  exact ⟨k, hk.symm⟩

/-- A rotation valid for one witness is valid for the other. -/
theorem rotation_transfer (g : AllowableComplexMetric V)
    {b b' : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig eig' : Fin (Module.finrank ℝ V) → ℂ}
    (hAC : AngleCondition eig)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (hAC' : AngleCondition eig')
    (hdiag' : ∀ v, g.toForm v v = ∑ i, eig' i * (b'.repr v i : ℂ) ^ 2)
    {φ : ℝ} (hφ : ∀ k, |Complex.arg (eig k) - φ| < Real.pi / 2) :
    ∀ j, |Complex.arg (eig' j) - φ| < Real.pi / 2 := by
  intro j
  obtain ⟨k, hk⟩ := arg_mem_transfer g hAC hdiag hAC' hdiag' j
  rw [hk]
  exact hφ k

/-! ## Canonicity: the tracked sorry -/

/-- **Witness-independence of the modulus sum** (KS's canonicity assertion). The three
conditions that make this sorry honest: (i) STATABLE — it compiles, over data the repo
already has; (ii) TRUE — KS assert it (KSTeX 214-216: "the subspace
P = ⊕ e^{−iθ_k/2}V_k is canonically associated to the form g"), and it is the statement
that makes the (g₀, Θ) parametrization well defined; (iii) NOT YET PROVED — the precise
remaining subgoal: both witnesses are eigenbases of the SAME pencil operator
(`pencilOperator_eigen_basis_of_form`, with P-orthogonality and diagonal values from
`bilin_basis_eq_zero_of_ne` / `bilin_basis_apply_self`, and a common valid rotation from
`rotation_transfer`), so what remains is uniqueness of the eigenspace decomposition —
that the `ker(T − s)`-components of `v` are witness-independent — plus
`Finset.sum_fiberwise` regrouping and the sec·cos collapse. Estimated 150-250 lines.
NO choice-dependence failure was found in the probe: this is a focused gap, not an
in-principle obstruction. -/
theorem modulus_welldef (g : AllowableComplexMetric V)
    {b b' : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V}
    {eig eig' : Fin (Module.finrank ℝ V) → ℂ}
    (hAC : AngleCondition eig)
    (hdiag : ∀ v, g.toForm v v = ∑ i, eig i * (b.repr v i : ℂ) ^ 2)
    (hAC' : AngleCondition eig')
    (hdiag' : ∀ v, g.toForm v v = ∑ i, eig' i * (b'.repr v i : ℂ) ^ 2)
    (v : V) :
    ∑ k, ‖eig k‖ * (b.repr v k) ^ 2 = ∑ k, ‖eig' k‖ * (b'.repr v k) ^ 2 := by
  sorry

/-! ## The Θ-precursor -/

/-- The sine-pencil: the operator representing `Im g` in the modulus form. A function of
`g` ALONE — no rotation `φ`, no chosen basis, no existential — which is exactly the
de-choicing the F2 scoping probe found missing from every previous route. Its
eigenvalues are `sin θ_k`. KS's `Θ` proper (eigenvalues `θ_k/π`) is one
functional-calculus layer beyond this (arcsin on `sinPencil`, or a per-eigenspace
definition) and is not built here. -/
noncomputable def sinPencil (g : AllowableComplexMetric V) : V →ₗ[ℝ] V :=
  pencilOperator (modulusForm g) (imForm g.toComplexMetric)
    (modulusForm_nondegenerate g)

/-- **`sinPencil` is self-adjoint with respect to the modulus form** (tracked sorry).
Route: `pencilOperator_pairing` gives the defining identity, `imForm` is symmetric, and
`isSymmetric_of_pairing` transports through the `posDefCore` instances of `modulusForm`.
Independent of canonicity: this is a statement about the chosen witness's form, so it is
statable and true regardless of how `modulus_welldef` goes. -/
theorem sinPencil_selfAdjoint (g : AllowableComplexMetric V) (x y : V) :
    modulusForm g (sinPencil g x) y = modulusForm g x (sinPencil g y) := by
  sorry

end KontsevichSegal.Parametrization
