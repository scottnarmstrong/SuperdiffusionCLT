/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.ShearB
public import SuperdiffusionCLT.Section7.Analytic.Change.Linear

/-!
# Calculus for the shear

Let `G z = ψ (P z)` with `P z = z - ⟨e,z⟩ e`. We record the facts about `G` and the shear
`Φ = shear e ψ`, `Ψ = shear e (-ψ)` needed for the `H¹` pullback: smoothness, the bound on the
partial derivatives of `G`, invariance of `∇G` along `e`, and the chain rule for `χ ∘ Φ`.

## Main results

* `Section7.shearHomeo`: the shear as a homeomorphism.
* `Section7.fderiv_comp_shear_apply`: the chain rule `∂ᵢ(χ ∘ Φ) = (∂ᵢχ - ∂ᵢG ∂_eχ) ∘ Φ`.
* `Section7.exists_bound_projGrad`: `∂ᵢG` is bounded.
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The continuous linear functional `z ↦ ⟨e,z⟩`. -/
noncomputable def dotCLM (e : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, e i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i

theorem dotCLM_apply (e z : Vec d) : dotCLM e z = vecDot e z := by
  simp [dotCLM, vecDot]

/-- The orthogonal projection `P z = z - ⟨e,z⟩ e` as a continuous linear map. -/
noncomputable def projCLM (e : Vec d) : Vec d →L[ℝ] Vec d :=
  ContinuousLinearMap.id ℝ (Vec d) - (dotCLM e).smulRight e

theorem projCLM_apply (e z : Vec d) : projCLM e z = z - vecDot e z • e := by
  simp [projCLM, dotCLM_apply]

/-- The function `z ↦ ψ(Pz)`. -/
noncomputable def projComp (e : Vec d) (ψ : Vec d → ℝ) : Vec d → ℝ :=
  fun z => ψ (z - vecDot e z • e)

theorem projComp_eq (e : Vec d) (ψ : Vec d → ℝ) :
    projComp e ψ = ψ ∘ projCLM e := by
  funext z; simp [projComp, projCLM_apply]

theorem contDiff_projComp {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (projComp e ψ) := by
  rw [projComp_eq]; exact hψ.comp (projCLM e).contDiff

theorem contDiff_shear {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (shear e ψ) := by
  have : shear e ψ = fun y => y - projComp e ψ y • e := rfl
  rw [this]
  exact contDiff_id.sub ((contDiff_projComp hψ).smul contDiff_const)

theorem differentiable_shear {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Differentiable ℝ (shear e ψ) :=
  (contDiff_shear hψ).differentiable (by simp)

/-- The shear as a homeomorphism, with inverse the shear by `-ψ`. -/
noncomputable def shearHomeo {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : Vec d ≃ₜ Vec d where
  toFun := shear e ψ
  invFun := shear e (-ψ)
  left_inv := fun y => congrFun (shear_neg_left_inverse he ψ) y
  right_inv := fun y => congrFun (shear_neg_right_inverse he ψ) y
  continuous_toFun := (differentiable_shear hψ).continuous
  continuous_invFun := (differentiable_shear hψ.neg).continuous

@[simp]
theorem shearHomeo_apply {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec d) : shearHomeo he hψ y = shear e ψ y := rfl

@[simp]
theorem shearHomeo_symm_apply {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec d) :
    (shearHomeo he hψ).symm y = shear e (-ψ) y := rfl

theorem shear_neg_shear {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (y : Vec d) :
    shear e (-ψ) (shear e ψ y) = y := congrFun (shear_neg_left_inverse he ψ) y

theorem shear_shear_neg {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (y : Vec d) :
    shear e ψ (shear e (-ψ) y) = y := congrFun (shear_neg_right_inverse he ψ) y

/-- A function constant along the line `y + t e` has vanishing derivative in the direction `e`. -/
theorem fderiv_apply_eq_zero_of_line_const {e : Vec d} {F : Vec d → ℝ} {y : Vec d}
    (hF : DifferentiableAt ℝ F y) (hc : ∀ t : ℝ, F (y + t • e) = F y) :
    fderiv ℝ F y e = 0 := by
  have hF' : DifferentiableAt ℝ F (y + (0 : ℝ) • e) := by simpa using hF
  have hline : HasDerivAt (fun t : ℝ => y + t • e) e 0 := by
    simpa using (HasDerivAt.const_add y (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) e))
  have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF'.hasFDerivAt hline
  have h2 : HasDerivAt (fun t : ℝ => F (y + t • e)) 0 0 := by
    have : (fun t : ℝ => F (y + t • e)) = fun _ => F y := funext hc
    rw [this]
    exact hasDerivAt_const _ _
  have h3 := h1.unique h2
  simpa using h3

/-- `∇G` is invariant under translation along `e`. -/
theorem fderiv_projComp_add_smul {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ)
    (y : Vec d) (t : ℝ) :
    fderiv ℝ (projComp e ψ) (y + t • e) = fderiv ℝ (projComp e ψ) y := by
  have hfun : (fun x => projComp e ψ (x + t • e)) = projComp e ψ := by
    funext x
    simp only [projComp, proj_add_smul he]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := projComp e ψ) (x := y) (t • e)
  rw [hfun] at this
  exact this.symm

/-- The `i`-th partial derivative of `G`. -/
noncomputable def projGrad (e : Vec d) (ψ : Vec d → ℝ) (i : Fin d) (y : Vec d) : ℝ :=
  fderiv ℝ (projComp e ψ) y (Pi.single i 1)

theorem contDiff_projGrad {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (projGrad e ψ i) := by
  have h := (contDiff_projComp (e := e) hψ).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact h.clm_apply (contDiff_const (c := (Pi.single i 1 : Vec d)))

theorem projGrad_add_smul {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (i : Fin d)
    (y : Vec d) (t : ℝ) : projGrad e ψ i (y + t • e) = projGrad e ψ i y := by
  simp only [projGrad, fderiv_projComp_add_smul he]

/-- `∇G` is orthogonal to `e`. -/
theorem fderiv_projComp_self {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : Differentiable ℝ ψ) (y : Vec d) :
    fderiv ℝ (projComp e ψ) y e = 0 := fderiv_proj_comp_self he hψ y

/-- The `i`-th partial derivative of `G`, transported by `Ψ = shear e (-ψ)`. -/
noncomputable def projGradPush (e : Vec d) (ψ : Vec d → ℝ) (i : Fin d) (x : Vec d) : ℝ :=
  projGrad e ψ i (shear e (-ψ) x)

theorem contDiff_projGradPush {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (projGradPush e ψ i) :=
  (contDiff_projGrad hψ i).comp (contDiff_shear hψ.neg)

theorem projGradPush_shear {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (i : Fin d)
    (y : Vec d) : projGradPush e ψ i (shear e ψ y) = projGrad e ψ i y := by
  simp [projGradPush, shear_neg_shear he]

theorem shear_neg_add_smul {e : Vec d} (he : vecNormSq e = 1) (ψ : Vec d → ℝ) (x : Vec d)
    (t : ℝ) : shear e (-ψ) (x + t • e) = shear e (-ψ) x + t • e := by
  have hP := proj_add_smul he x t
  unfold shear
  simp only [Pi.neg_apply, hP]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, neg_mul]
  ring

theorem fderiv_projGradPush_self {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) (x : Vec d) :
    fderiv ℝ (projGradPush e ψ i) x e = 0 := by
  refine fderiv_apply_eq_zero_of_line_const
    (((contDiff_projGradPush hψ i).differentiable (by simp)) x) fun t => ?_
  simp only [projGradPush, shear_neg_add_smul he, projGrad_add_smul he]

/-- The partial derivatives of `G` are bounded when those of `ψ` are. -/
theorem exists_bound_projGrad {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ ψ y (Pi.single i 1)| ≤ M) :
    ∃ C : ℝ, ∀ y i, |projGrad e ψ i y| ≤ C := by
  choose M hM using hb
  refine ⟨∑ i, (|M i| + |e i| * ∑ j, |e j| * |M j|), fun y i => ?_⟩
  have hchain : fderiv ℝ (projComp e ψ) y = (fderiv ℝ ψ (projCLM e y)).comp (projCLM e) := by
    rw [projComp_eq]
    rw [fderiv_comp y ((hψ.differentiable (by simp)) _) (projCLM e).differentiableAt,
      ContinuousLinearMap.fderiv]
  have hcoord : projCLM e (Pi.single i 1) = Pi.single i 1 - e i • e := by
    rw [projCLM_apply]
    have : vecDot e (Pi.single i (1 : ℝ) : Vec d) = e i := by
      simp [vecDot, Pi.single_apply]
    rw [this]
  have hval : projGrad e ψ i y = fderiv ℝ ψ (projCLM e y) (Pi.single i 1) -
      e i * ∑ j, e j * fderiv ℝ ψ (projCLM e y) (Pi.single j 1) := by
    unfold projGrad
    rw [hchain, ContinuousLinearMap.comp_apply, hcoord, map_sub, map_smul, smul_eq_mul,
      clm_apply_eq_sum (fderiv ℝ ψ (projCLM e y)) e]
    rfl
  have hterm : ∀ j, |e j * fderiv ℝ ψ (projCLM e y) (Pi.single j 1)| ≤ |e j| * |M j| := by
    intro j
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hM j _).trans (le_abs_self _)) (abs_nonneg _)
  have hsum : |∑ j, e j * fderiv ℝ ψ (projCLM e y) (Pi.single j 1)| ≤ ∑ j, |e j| * |M j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
  have h1 : |fderiv ℝ ψ (projCLM e y) (Pi.single i 1)| ≤ |M i| :=
    (hM i _).trans (le_abs_self _)
  have h2 : |projGrad e ψ i y| ≤ |M i| + |e i| * ∑ j, |e j| * |M j| := by
    rw [hval]
    refine (abs_sub _ _).trans (add_le_add h1 ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  exact h2.trans (Finset.single_le_sum (f := fun i => |M i| + |e i| * ∑ j, |e j| * |M j|)
    (fun k _ => add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))) (Finset.mem_univ i))

/-- Chain rule for `χ ∘ Φ`: `∂ᵢ(χ ∘ Φ) = (∂ᵢχ - ∂ᵢG ∂_eχ) ∘ Φ`. -/
theorem fderiv_comp_shear_apply {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {χ : Vec d → ℝ} (hχ : Differentiable ℝ χ) (y : Vec d) (i : Fin d) :
    fderiv ℝ (fun z => χ (shear e ψ z)) y (Pi.single i 1) =
      fderiv ℝ χ (shear e ψ y) (Pi.single i 1) -
        projGrad e ψ i y * fderiv ℝ χ (shear e ψ y) e := by
  have hΦ : HasFDerivAt (shear e ψ) (ContinuousLinearMap.id ℝ (Vec d) -
      (fderiv ℝ (projComp e ψ) y).smulRight e) y :=
    hasFDerivAt_shear (e := e) (hψ.differentiable (by simp)) y
  have hcomp := (hχ (shear e ψ y)).hasFDerivAt.comp y hΦ
  rw [show (fun z => χ (shear e ψ z)) = χ ∘ shear e ψ from rfl, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_sub, map_smul,
    smul_eq_mul, projGrad]

/-- Satisfiability: `ψ = 0`, `e = e₀` in dimension `2` meets all hypotheses of the bound. -/
example : ∃ C : ℝ, ∀ y i, |projGrad (Pi.single (0 : Fin 2) (1 : ℝ)) (0 : Vec 2 → ℝ) i y| ≤ C :=
  exists_bound_projGrad contDiff_const (fun _ => ⟨0, fun y => by simp⟩)

end SuperdiffusionCLT.Section7
