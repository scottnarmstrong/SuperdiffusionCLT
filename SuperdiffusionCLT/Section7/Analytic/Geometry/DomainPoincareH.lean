/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# Poincare inequalities: shear preimages

`Section7.a10_poincare_shear`: if `H` is a star-ball domain and `W = {y | shear e Ψ y ∈ H}`, then every
`u ∈ H¹(W)` satisfies the mean-value Poincare inequality with a constant depending only on `d`,
`D / s` and the slope bound of `Ψ`. The pullback `u ∘ shear e (-Ψ)` lies in `H¹(H)`, the shear
preserves volume, and the gradient changes by the factor `1 + 2 d K`.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_norm_proj_single_le {e : Vec d} (he : vecNormSq e = 1) (i : Fin d) :
    ‖projCLM e (Pi.single i (1 : ℝ))‖ ≤ 2 := by
  rw [projCLM_apply]
  have h1 : ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have h2 : ‖vecDot e (Pi.single i (1 : ℝ)) • e‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    have : vecDot e (Pi.single i (1 : ℝ)) = e i := by
      have := vecDot_basisVec_left i e
      simpa [basisVec, vecDot, mul_comm] using this
    rw [this]
    calc |e i| * ‖e‖ ≤ 1 * 1 :=
          mul_le_mul (abs_apply_le_one he i) (norm_le_one_of_vecNormSq he) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ‖(Pi.single i (1 : ℝ) : Vec d) - vecDot e (Pi.single i (1 : ℝ)) • e‖
      ≤ ‖(Pi.single i (1 : ℝ) : Vec d)‖ + ‖vecDot e (Pi.single i (1 : ℝ)) • e‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith only [h1, h2]

theorem a10_projGrad_bound {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ ψ y‖ ≤ K) (i : Fin d) (y : Vec d) :
    |projGrad e ψ i y| ≤ 2 * K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  unfold projGrad
  rw [projComp_eq, fderiv_comp y ((hψ.differentiable (by simp)) _) (projCLM e).differentiableAt,
    (projCLM e).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  calc ‖fderiv ℝ ψ (projCLM e y)‖ * ‖projCLM e (Pi.single i (1 : ℝ))‖ ≤ K * 2 :=
        mul_le_mul (hK _) (a10_norm_proj_single_le he i) (norm_nonneg _) hK0
    _ = 2 * K := mul_comm _ _

theorem a10_H1_congr {U V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    ∃ v : H1Function V, v.toFun = u.toFun ∧ v.grad = u.grad := by
  subst h
  exact ⟨u, rfl, rfl⟩

theorem a10_aesm_norm_grad {W : Set (Vec d)} (u : H1Function W) :
    AEStronglyMeasurable (fun x => ‖u.grad x‖) (volume.restrict W) := by
  have : AEMeasurable u.grad (volume.restrict W) :=
    aemeasurable_pi_iff.2 fun i => (u.gradMemL2 i).aestronglyMeasurable.aemeasurable
  exact this.norm.aestronglyMeasurable

/-- **Poincare inequality on a shear preimage of a star-ball domain.** The constant depends only
on `d`, `D / s` and the slope bound `K` of the shear function. -/
theorem a10_poincare_shear {H : Set (Vec d)} {x0 : Vec d} {s D : ℝ}
    (hH : IsStarBallDomain H x0 s D) {e : Vec d} (he : vecNormSq e = 1) {Ψ : Vec d → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ Ψ y‖ ≤ K)
    {W : Set (Vec d)} (hWdef : W = shear e Ψ ⁻¹' H) (u : H1Function W) :
    eLpNorm (fun x => u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) 2
        (volume.restrict W) ≤
      ENNReal.ofReal (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) * D *
        (1 + 2 * d * K)) *
        eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (-Ψ) := hΨ.neg
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hK' : ∀ y, ‖fderiv ℝ (-Ψ) y‖ ≤ K := fun y => by
    have : fderiv ℝ (-Ψ) y = -fderiv ℝ Ψ y := fderiv_neg (f := Ψ) (x := y)
    rw [this, norm_neg]
    exact hK y
  have hb : ∀ i, ∃ M, ∀ y, |fderiv ℝ (-Ψ) y (Pi.single i 1)| ≤ M := fun i => by
    refine ⟨K, fun y => ?_⟩
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h1 : ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    calc ‖fderiv ℝ (-Ψ) y‖ * ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ K * 1 :=
          mul_le_mul (hK' y) h1 (norm_nonneg _) hK0
      _ = K := mul_one K
  have hsetH : shear e (-Ψ) ⁻¹' W = H := by
    ext y
    rw [hWdef]
    simp only [Set.mem_preimage]
    rw [shear_shear_neg he]
  obtain ⟨v0, hv0f, hv0g⟩ := shearPullbackH1 he hψ hb u
  obtain ⟨v, hvf, hvg⟩ := a10_H1_congr hsetH v0
  have hmain := a10_poincare_starBall hH v
  have hmp : MeasurePreserving (shear e (-Ψ)) (volume.restrict H) (volume.restrict W) := by
    have := measurePreserving_restrict_shear he hψ W
    rwa [hsetH] at this
  have hemb : MeasurableEmbedding (shear e (-Ψ)) := (shearHomeo he hψ).measurableEmbedding
  have hvT : ∀ y, v.toFun y = u.toFun (shear e (-Ψ) y) := fun y => by
    rw [hvf, hv0f]
  have hmean : (∫ y in H, v.toFun y) = ∫ x in W, u.toFun x := by
    have := hmp.integral_comp hemb u.toFun
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall hvT)
  have hvol : volume H = volume W := by
    have := hmp.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    simpa using this
  have hf : AEStronglyMeasurable (fun x => u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal)
      (volume.restrict W) := u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hL : eLpNorm (fun x => v.toFun x - (∫ y in H, v.toFun y) / (volume H).toReal) 2
      (volume.restrict H) = eLpNorm (fun x => u.toFun x -
        (∫ y in W, u.toFun y) / (volume W).toReal) 2 (volume.restrict W) := by
    rw [hmean, hvol]
    have := eLpNorm_comp_measurePreserving (p := 2) hf hmp
    rw [← this]
    refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.comp, hvT]
  have hgbound : ∀ y, ‖v.grad y‖ ≤ (1 + 2 * d * K) * ‖u.grad (shear e (-Ψ) y)‖ := by
    intro y
    rw [hvg, hv0g y]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    set g := u.grad (shear e (-Ψ) y) with hg
    have hq := a10_projGrad_bound he hψ hK' i y
    have hdot := abs_vecDot_le he g
    have hgi : |g i| ≤ ‖g‖ := by simpa using norm_le_pi_norm g i
    calc |g i - vecDot e g * fderiv ℝ (fun z => (-Ψ) (z - vecDot e z • e)) y (Pi.single i 1)|
        ≤ |g i| + |vecDot e g| * |projGrad e (-Ψ) i y| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul]
          rfl
      _ ≤ ‖g‖ + (d * ‖g‖) * (2 * K) := by
          gcongr
      _ = (1 + 2 * d * K) * ‖g‖ := by ring
  have hgeq : eLpNorm (fun y => ‖u.grad (shear e (-Ψ) y)‖) 2 (volume.restrict H) =
      eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W) := by
    have := eLpNorm_comp_measurePreserving (p := 2) (a10_aesm_norm_grad u) hmp
    exact this
  have hG : eLpNorm (fun x => ‖v.grad x‖) 2 (volume.restrict H) ≤
      ENNReal.ofReal (1 + 2 * d * K) * eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W) := by
    rw [← hgeq]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (a10_aesm_norm_grad v) ?_ 2
    refine Filter.Eventually.of_forall fun y => ?_
    simpa using hgbound y
  rw [← hL]
  refine hmain.trans ?_
  calc ENNReal.ofReal (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) * D) *
        eLpNorm (fun x => ‖v.grad x‖) 2 (volume.restrict H)
      ≤ ENNReal.ofReal (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) * D) *
        (ENNReal.ofReal (1 + 2 * d * K) * eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W)) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul]
        have hD : 0 ≤ D := by
          obtain ⟨-, hs, hBW, -, hdiam⟩ := hH
          simpa using hdiam x0 (hBW (Metric.mem_ball_self hs)) x0 (hBW (Metric.mem_ball_self hs))
        positivity

end SuperdiffusionCLT.Section7
