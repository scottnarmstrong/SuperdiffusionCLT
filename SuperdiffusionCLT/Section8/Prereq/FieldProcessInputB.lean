/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInput

/-!
# Local constants of the split for the marginal field

For `FieldInputData d nu k` the localized split data of the whole-space exhaustion has the
rough part `ks = 0` and the smooth part `kl = k`.  The divergence of `k` is bounded on a
Euclidean ball by a logarithm of the observation radius, and the normalized coefficient is
within `delta` of the identity on the ball of radius `amplitude / (1 + |x|)` about `x`, because
the gradient of `k` is bounded by a logarithm and hence by `3 G (1 + |x|)` on the unit ball
about `x`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open SuperdiffusionCLT.Section8.Common.Regularity.Freezing
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} {nu : ℝ} {k : Vec d → Mat d}

theorem fieldInput_euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  have hnorm : ∀ w : Vec d, euclideanNorm w = ‖HilbertVec.ofVecL d w‖ := by
    intro w
    rw [HilbertVec.ofVecL_apply, euclideanNorm_eq_norm_ofVec]
  rw [hnorm, hnorm x, hnorm y, map_add]
  exact norm_add_le _ _

/-- The logarithmic weight `1 + log R`. -/
def fieldInput_logWeight (R : ℝ) : ℝ := 1 + Real.log R

theorem fieldInput_logWeight_pos {R : ℝ} (hR : 1 ≤ R) : 0 < fieldInput_logWeight R := by
  have h : 0 ≤ Real.log R := Real.log_nonneg hR
  unfold fieldInput_logWeight
  linarith only [h]

/-- An origin-centred observation radius containing `euclideanBall x r`. -/
def fieldInput_obsRadius (x : Vec d) (r : ℝ) : ℝ := 1 + euclideanNorm x + r

theorem fieldInput_one_le_obsRadius {x : Vec d} {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ fieldInput_obsRadius x r := by
  have hx := euclideanNorm_nonneg x
  unfold fieldInput_obsRadius
  linarith only [hx, hr]

theorem fieldInput_euclideanNorm_lt_obsRadius {x y : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ euclideanBall x r) : euclideanNorm y < fieldInput_obsRadius x r := by
  have hdist := DivergenceForm.Decay.euclideanNorm_sub_lt_of_mem_euclideanBall hr hy
  have htri : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
    have h := fieldInput_euclideanNorm_add_le (y - x) x
    simpa only [sub_add_cancel] using h
  unfold fieldInput_obsRadius
  linarith only [hdist, htri]

namespace FieldInputData

/-- The gradient bound at a point in terms of the logarithmic weight of a radius dominating
the point's norm. -/
theorem grad_le_weight (D : FieldInputData d nu k) {y : Vec d} {R : ℝ} (hR : 1 ≤ R)
    (hy : ‖y‖ ≤ R) :
    ‖fderiv ℝ k y‖ ≤ 3 * D.gradConst * fieldInput_logWeight R := by
  have h0 := D.grad_le y
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hpos : 0 < 2 + ‖y‖ := by linarith only [hy0]
  have hlog : Real.log (2 + ‖y‖) ≤ Real.log (3 * R) :=
    Real.log_le_log hpos (by linarith only [hy, hR])
  have h3 : Real.log (3 * R) = Real.log 3 + Real.log R :=
    Real.log_mul (by norm_num) (by linarith only [hR])
  have h3le : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith only [this]
  have hR0 : 0 ≤ Real.log R := Real.log_nonneg hR
  have hG := D.gradConst_nonneg
  have hmul : D.gradConst * (1 + Real.log (2 + ‖y‖)) ≤
      D.gradConst * (3 * fieldInput_logWeight R) := by
    refine mul_le_mul_of_nonneg_left ?_ hG
    unfold fieldInput_logWeight
    linarith only [hlog, h3, h3le, hR0]
  calc ‖fderiv ℝ k y‖ ≤ _ := h0
    _ ≤ _ := hmul
    _ = 3 * D.gradConst * fieldInput_logWeight R := by ring

end FieldInputData

/-! ## The divergence of the smooth part -/

theorem fieldInput_vecNormSq_le_dim_mul_sq_norm (v : Vec d) :
    vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
  simp only [vecNormSq, vecDot]
  calc
    ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
      gcongr with i
      calc
        v i * v i = |v i| ^ 2 := by rw [sq_abs]; ring
        _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i) 2
    _ = (d : ℝ) * ‖v‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Each coordinate of the divergence of a `C¹` matrix field is bounded by `d` times the norm
of the gradient. -/
theorem fieldInput_abs_skewFieldDiv_le (hk : ContDiff ℝ 1 k) (y : Vec d) (j : Fin d) :
    |DivergenceForm.Decay.skewFieldDiv k y j| ≤ (d : ℝ) * ‖fderiv ℝ k y‖ := by
  have hdiff : DifferentiableAt ℝ k y := (hk.differentiable one_ne_zero).differentiableAt
  have hterm : ∀ i : Fin d,
      |euclideanCoordDeriv i (fun z => k z i j) y| ≤ ‖fderiv ℝ k y‖ := by
    intro i
    let pj : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    let pi' : Mat d →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.proj i
    have hi : HasFDerivAt (fun z => k z i j)
        (pj.comp (pi'.comp (fderiv ℝ k y))) y :=
      pj.hasFDerivAt.comp y (pi'.hasFDerivAt.comp y hdiff.hasFDerivAt)
    have hval : euclideanCoordDeriv i (fun z => k z i j) y =
        fderiv ℝ k y (basisVec i) i j := by
      unfold euclideanCoordDeriv
      rw [hi.fderiv]
      rfl
    rw [hval]
    have h1 := (Matrix.norm_entry_le_entrywise_sup_norm _ :
      ‖(fderiv ℝ k y (basisVec i)) i j‖ ≤ ‖fderiv ℝ k y (basisVec i)‖)
    have h2 : ‖fderiv ℝ k y (basisVec i)‖ ≤ ‖fderiv ℝ k y‖ * ‖(basisVec i : Vec d)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖(basisVec i : Vec d)‖ = 1 := by
      unfold basisVec
      rw [Pi.norm_single]
      simp
    rw [h3, mul_one] at h2
    simpa only [Real.norm_eq_abs] using h1.trans h2
  calc |DivergenceForm.Decay.skewFieldDiv k y j|
      ≤ ∑ i : Fin d, |euclideanCoordDeriv i (fun z => k z i j) y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖fderiv ℝ k y‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * ‖fderiv ℝ k y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem fieldInput_vecNormSq_skewFieldDiv_le (hk : ContDiff ℝ 1 k) (y : Vec d) :
    vecNormSq (DivergenceForm.Decay.skewFieldDiv k y) ≤
      (Real.sqrt d * (d : ℝ) * ‖fderiv ℝ k y‖) ^ 2 := by
  have hD : 0 ≤ ‖fderiv ℝ k y‖ := norm_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnorm : ‖DivergenceForm.Decay.skewFieldDiv k y‖ ≤ (d : ℝ) * ‖fderiv ℝ k y‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hd0 hD)).2 fun j => by
      simpa only [Real.norm_eq_abs] using fieldInput_abs_skewFieldDiv_le hk y j
  have hsq : ‖DivergenceForm.Decay.skewFieldDiv k y‖ ^ 2 ≤
      ((d : ℝ) * ‖fderiv ℝ k y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc vecNormSq (DivergenceForm.Decay.skewFieldDiv k y)
      ≤ (d : ℝ) * ‖DivergenceForm.Decay.skewFieldDiv k y‖ ^ 2 :=
        fieldInput_vecNormSq_le_dim_mul_sq_norm _
    _ ≤ (d : ℝ) * ((d : ℝ) * ‖fderiv ℝ k y‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hd0
    _ = (Real.sqrt d * (d : ℝ) * ‖fderiv ℝ k y‖) ^ 2 := by
        calc (d : ℝ) * ((d : ℝ) * ‖fderiv ℝ k y‖) ^ 2
            = Real.sqrt d ^ 2 * ((d : ℝ) * ‖fderiv ℝ k y‖) ^ 2 := by
              rw [Real.sq_sqrt hd0]
          _ = _ := by ring

namespace FieldInputData

/-- The local divergence constant of the smooth part: `sqrt d * d * 3 G` times the logarithmic
weight of the observation radius. -/
def smoothDivBound (D : FieldInputData d nu k) (x : Vec d) (r : ℝ) : ℝ :=
  Real.sqrt d * (d : ℝ) * (3 * D.gradConst) * fieldInput_logWeight (fieldInput_obsRadius x r)

theorem smoothDivBound_nonneg (D : FieldInputData d nu k) {x : Vec d} {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ D.smoothDivBound x r := by
  unfold smoothDivBound
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg d))
      (mul_nonneg (by norm_num) D.gradConst_nonneg))
    (fieldInput_logWeight_pos (fieldInput_one_le_obsRadius hr)).le

/-- The divergence of `k` has the local squared-size bound required by the localized estimate. -/
theorem vecNormSq_skewFieldDiv_le (D : FieldInputData d nu k) {x y : Vec d} {r : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ euclideanBall x r) :
    vecNormSq (DivergenceForm.Decay.skewFieldDiv k y) ≤ D.smoothDivBound x r ^ 2 := by
  have hR := fieldInput_one_le_obsRadius (x := x) hr
  have hyR : ‖y‖ ≤ fieldInput_obsRadius x r :=
    (norm_le_euclideanNorm y).trans (fieldInput_euclideanNorm_lt_obsRadius hr hy).le
  have hgrad := D.grad_le_weight hR hyR
  have hbase : 0 ≤ Real.sqrt d * (d : ℝ) := mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg d)
  have hmul : Real.sqrt d * (d : ℝ) * ‖fderiv ℝ k y‖ ≤ D.smoothDivBound x r := by
    unfold smoothDivBound
    calc Real.sqrt d * (d : ℝ) * ‖fderiv ℝ k y‖
        ≤ Real.sqrt d * (d : ℝ) * (3 * D.gradConst * fieldInput_logWeight
            (fieldInput_obsRadius x r)) := mul_le_mul_of_nonneg_left hgrad hbase
      _ = _ := by ring
  refine (fieldInput_vecNormSq_skewFieldDiv_le D.contDiff y).trans ?_
  exact pow_le_pow_left₀ (mul_nonneg hbase (norm_nonneg _)) hmul 2

end FieldInputData

/-! ## The freezing radius -/

namespace FieldInputData

/-- On the unit ball about `x`, the logarithmic gradient bound makes `k` Lipschitz with the
constant `3 G (1 + |x|)`. -/
theorem norm_sub_le (D : FieldInputData d nu k) {x y : Vec d} (hxy : ‖y - x‖ ≤ 1) :
    ‖k y - k x‖ ≤ 3 * D.gradConst * (1 + ‖x‖) * ‖y - x‖ := by
  have hG := D.gradConst_nonneg
  have hbound : ∀ z ∈ Metric.closedBall x 1,
      ‖fderiv ℝ k z‖ ≤ 3 * D.gradConst * (1 + ‖x‖) := by
    intro z hz
    have hzx : ‖z - x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hz' : ‖z‖ ≤ ‖x‖ + 1 := by
      have := norm_sub_norm_le z x
      linarith only [this, hzx]
    have hlog : Real.log (2 + ‖z‖) ≤ 1 + ‖z‖ := by
      have := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖z‖ by
        linarith only [norm_nonneg z])
      linarith only [this]
    have hx0 := norm_nonneg x
    calc ‖fderiv ℝ k z‖ ≤ D.gradConst * (1 + Real.log (2 + ‖z‖)) := D.grad_le z
      _ ≤ D.gradConst * (3 * (1 + ‖x‖)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hlog, hz', hx0]) hG
      _ = 3 * D.gradConst * (1 + ‖x‖) := by ring
  have hdiff : ∀ z ∈ Metric.closedBall x 1, DifferentiableAt ℝ k z := fun z _ =>
    (D.contDiff.differentiable one_ne_zero).differentiableAt
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall x 1)
    (Metric.mem_closedBall_self zero_le_one)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hxy)

theorem matrixOperatorNorm_sub_le (D : FieldInputData d nu k) {x y : Vec d}
    (hxy : ‖y - x‖ ≤ 1) :
    matrixOperatorNorm (k y - k x) ≤
      (d : ℝ) * (3 * D.gradConst * (1 + ‖x‖) * ‖y - x‖) := by
  have hnn : 0 ≤ 3 * D.gradConst * (1 + ‖x‖) * ‖y - x‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) D.gradConst_nonneg)
      (by linarith only [norm_nonneg x])) (norm_nonneg _)
  refine SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_le_of_entry_bound
    _ hnn fun i j => ?_
  have h1 := (Matrix.norm_entry_le_entrywise_sup_norm (k y - k x) :
    ‖(k y - k x) i j‖ ≤ ‖k y - k x‖)
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (D.norm_sub_le hxy)

/-- The amplitude of the freezing radius. -/
def freezingAmplitude (D : FieldInputData d nu k) (delta : ℝ) : ℝ :=
  min 1 (delta * nu / (1 + 3 * ((d : ℝ) * D.gradConst)))

/-- The radius on which the freezing of the coefficient at `x` has contrast at most `delta`. -/
def freezingRadius (D : FieldInputData d nu k) (delta : ℝ) (x : Vec d) : ℝ :=
  D.freezingAmplitude delta / (1 + euclideanNorm x)

theorem freezingAmplitude_pos (D : FieldInputData d nu k) {delta : ℝ} (hdelta : 0 < delta) :
    0 < D.freezingAmplitude delta := by
  have hG := D.gradConst_nonneg
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hden : 0 < 1 + 3 * ((d : ℝ) * D.gradConst) := by
    have := mul_nonneg hd hG
    linarith only [this]
  exact lt_min one_pos (div_pos (mul_pos hdelta D.nu_pos) hden)

theorem freezingAmplitude_le_one (D : FieldInputData d nu k) (delta : ℝ) :
    D.freezingAmplitude delta ≤ 1 :=
  min_le_left _ _

theorem freezingRadius_pos (D : FieldInputData d nu k) {delta : ℝ} (hdelta : 0 < delta)
    (x : Vec d) : 0 < D.freezingRadius delta x := by
  unfold freezingRadius
  exact div_pos (D.freezingAmplitude_pos hdelta)
    (by linarith only [euclideanNorm_nonneg x])

theorem freezingRadius_le_one (D : FieldInputData d nu k) (delta : ℝ) (x : Vec d) : D.freezingRadius delta x ≤ 1 := by
  unfold freezingRadius
  have hx := euclideanNorm_nonneg x
  rw [div_le_one (by linarith only [hx])]
  linarith only [D.freezingAmplitude_le_one delta, hx]

theorem matrixOperatorNorm_eq_applyMat_norm (A : Mat d) :
    matrixOperatorNorm A = ‖HilbertVec.applyMat A‖ := by
  rw [matrixOperatorNorm]
  congr 1

/-- The normalized freezing of the coefficient minus the identity is `nu⁻¹` times the increment
of `k`. -/
theorem normalizedFrozenCoeff_sub_one (D : FieldInputData d nu k) (x y : Vec d) :
    normalizedFrozenCoeff nu (fun z => nu • (1 : Mat d) + k z) x y - (1 : Mat d) =
      nu⁻¹ • (k y - k x) := by
  have h1 : nu⁻¹ • (nu • (1 : Mat d)) = 1 := by
    rw [smul_smul, inv_mul_cancel₀ D.nu_pos.ne', one_smul]
  have h2 : nu • (1 : Mat d) + k y - (nu • (1 : Mat d) + k x - nu • (1 : Mat d)) =
      nu • (1 : Mat d) + (k y - k x) := by abel
  unfold normalizedFrozenCoeff
  simp only
  rw [h2, smul_add, h1]
  abel

/-- The explicit radius gives the small normalized contrast at every point of the ball. -/
theorem contrast_le (D : FieldInputData d nu k) {delta : ℝ} (hdelta : 0 < delta) (x : Vec d)
    {y : Vec d} (hy : y ∈ euclideanBall x (D.freezingRadius delta x)) :
    ‖HilbertVec.applyMat
        (normalizedFrozenCoeff nu (fun z => nu • (1 : Mat d) + k z) x y - (1 : Mat d))‖ ≤
      delta := by
  have hrpos := D.freezingRadius_pos hdelta x
  have hdist : euclideanNorm (y - x) < D.freezingRadius delta x :=
    DivergenceForm.Decay.euclideanNorm_sub_lt_of_mem_euclideanBall hrpos.le hy
  have hxy : ‖y - x‖ ≤ 1 :=
    ((norm_le_euclideanNorm (y - x)).trans hdist.le).trans (D.freezingRadius_le_one delta x)
  have hx0 := euclideanNorm_nonneg x
  have hnx : ‖x‖ ≤ euclideanNorm x := norm_le_euclideanNorm x
  have hG := D.gradConst_nonneg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hyx : ‖y - x‖ ≤ D.freezingRadius delta x :=
    (norm_le_euclideanNorm (y - x)).trans hdist.le
  have hop := D.matrixOperatorNorm_sub_le hxy
  have hamp : (1 + 3 * ((d : ℝ) * D.gradConst)) * D.freezingAmplitude delta ≤ delta * nu := by
    have h := min_le_right 1 (delta * nu / (1 + 3 * ((d : ℝ) * D.gradConst)))
    have hden : 0 < 1 + 3 * ((d : ℝ) * D.gradConst) := by
      have := mul_nonneg hd0 hG
      linarith only [this]
    have h' : D.freezingAmplitude delta ≤ delta * nu / (1 + 3 * ((d : ℝ) * D.gradConst)) := h
    calc (1 + 3 * ((d : ℝ) * D.gradConst)) * D.freezingAmplitude delta
        ≤ (1 + 3 * ((d : ℝ) * D.gradConst)) *
            (delta * nu / (1 + 3 * ((d : ℝ) * D.gradConst))) :=
          mul_le_mul_of_nonneg_left h' hden.le
      _ = delta * nu := by field_simp
  have hbudget : (d : ℝ) * (3 * D.gradConst * (1 + ‖x‖) * ‖y - x‖) ≤ delta * nu := by
    have hrad : (1 + euclideanNorm x) * D.freezingRadius delta x = D.freezingAmplitude delta := by
      unfold freezingRadius
      field_simp
    have h1 : (1 + ‖x‖) * ‖y - x‖ ≤ (1 + euclideanNorm x) * D.freezingRadius delta x :=
      mul_le_mul (by linarith only [hnx]) hyx (norm_nonneg _) (by linarith only [hx0])
    rw [hrad] at h1
    have h2 : 3 * ((d : ℝ) * D.gradConst) * ((1 + ‖x‖) * ‖y - x‖) ≤
        3 * ((d : ℝ) * D.gradConst) * D.freezingAmplitude delta :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) (mul_nonneg hd0 hG))
    have h3 : 3 * ((d : ℝ) * D.gradConst) * D.freezingAmplitude delta ≤
        (1 + 3 * ((d : ℝ) * D.gradConst)) * D.freezingAmplitude delta :=
      mul_le_mul_of_nonneg_right (by linarith only) (D.freezingAmplitude_pos hdelta).le
    calc (d : ℝ) * (3 * D.gradConst * (1 + ‖x‖) * ‖y - x‖)
        = 3 * ((d : ℝ) * D.gradConst) * ((1 + ‖x‖) * ‖y - x‖) := by ring
      _ ≤ delta * nu := by linarith only [h2, h3, hamp]
  rw [normalizedFrozenCoeff_sub_one D x y, ← matrixOperatorNorm_eq_applyMat_norm,
    fieldReg_matrixOperatorNorm_smul, abs_of_pos (inv_pos.mpr D.nu_pos)]
  apply (inv_mul_le_iff₀ D.nu_pos).2
  calc matrixOperatorNorm (k y - k x) ≤ _ := hop
    _ ≤ delta * nu := hbudget
    _ = nu * delta := mul_comm _ _

end FieldInputData

/-! ## The localized split datum -/

section Split

variable [NeZero d]

theorem fieldInput_smallContrastThreshold_half_pos (d : ℕ) :
    0 < smallContrastThreshold d (1 / 2 : ℝ) := by
  unfold smallContrastThreshold
  positivity

omit [NeZero d] in
theorem fieldInput_symmPart_rough (nu : ℝ) (y : Vec d) :
    symmPart (nu • (1 : Mat d) + (fun _ : Vec d => (0 : Mat d)) y) = nu • (1 : Mat d) :=
  DivergenceForm.Decay.symmPart_scalar_add_skew rfl (by simp [matTranspose])

omit [NeZero d] in
theorem fieldInput_continuousOn_rough (nu : ℝ) (S : Set (Vec d)) :
    ContinuousOn (fun y : Vec d =>
      nu • (1 : Mat d) + (fun _ : Vec d => (0 : Mat d)) y - nu • (1 : Mat d)) S := by
  simp only [add_sub_cancel_left]
  exact continuousOn_const

/-- **The localized split datum of the marginal field**: `a = nu Id + 0 + k`, with the rough
part zero, the divergence bound `smoothDivBound` and the explicit freezing radius. -/
def FieldInputData.splitData (D : FieldInputData d nu k) :
    DivergenceForm.WholeSpaceLocalizedSplitData D.analyticData where
  ks := fun _ => 0
  kl := k
  split := fun y => by
    change nu • (1 : Mat d) + k y = nu • (1 : Mat d) + 0 + k y
    rw [add_zero]
  ksSkew := fun y => by simp [matTranspose]
  klSkew := D.skew
  klContDiff := D.contDiff_entry
  roughEllipticityUpper := fun m =>
    axisCubeEllipticUpper (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m) D.nu_pos
      (a := fun y => nu • (1 : Mat d) + (fun _ : Vec d => (0 : Mat d)) y)
      (fieldInput_symmPart_rough nu) (fieldInput_continuousOn_rough nu _)
  roughEllipticity := fun m =>
    isEllipticFieldOn_axisCubeEllipticUpper (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m)
      D.nu_pos (a := fun y => nu • (1 : Mat d) + (fun _ : Vec d => (0 : Mat d)) y)
      (fieldInput_symmPart_rough nu) (fieldInput_continuousOn_rough nu _)
  holderExponent := 1 / 2
  holderExponent_mem := by constructor <;> norm_num
  delta := smallContrastThreshold d (1 / 2 : ℝ)
  delta_nonneg := (fieldInput_smallContrastThreshold_half_pos d).le
  delta_le := le_rfl
  freezingRadius := D.freezingRadius (smallContrastThreshold d (1 / 2 : ℝ))
  freezingRadius_pos := D.freezingRadius_pos (fieldInput_smallContrastThreshold_half_pos d)
  smallContrast := fun x => by
    filter_upwards [ae_restrict_mem
      (isOpen_euclideanBall x
        (D.freezingRadius (smallContrastThreshold d (1 / 2 : ℝ)) x)).measurableSet] with y hy
    exact D.contrast_le (fieldInput_smallContrastThreshold_half_pos d) x hy
  roughBound := fun _ _ => 0
  smoothDivBound := D.smoothDivBound
  roughBound_nonneg := fun _ _ _ => le_rfl
  smoothDivBound_nonneg := fun _ _ hr => D.smoothDivBound_nonneg hr
  roughBound_spec := fun x r hr y hy v => by
    simp [vecNormSq, vecDot, matVecMul]
  smoothDivBound_spec := fun x r hr y hy => D.vecNormSq_skewFieldDiv_le hr hy

theorem FieldInputData.splitData_roughBound (D : FieldInputData d nu k) (x : Vec d) (r : ℝ) :
    D.splitData.roughBound x r = 0 :=
  rfl

theorem FieldInputData.splitData_freezingRadius (D : FieldInputData d nu k) :
    D.splitData.freezingRadius = D.freezingRadius (smallContrastThreshold d (1 / 2 : ℝ)) :=
  rfl

end Split

/-- **The split datum of the marginal coefficient, almost surely.**  Almost surely there is an
analytic coefficient datum whose coefficient is `fullCoefficientRecentered nu omega` and whose
exhaustion carries the localized split datum with vanishing rough part. -/
theorem fieldInput_ae_splitData [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ A : DivergenceForm.WholeSpaceAnalyticData d,
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          ∃ L : DivergenceForm.WholeSpaceLocalizedSplitData A,
            (∀ x r, L.roughBound x r = 0) := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu] with omega hD
  obtain ⟨D⟩ := hD
  exact ⟨D.analyticData, rfl, rfl, D.splitData, fun x r => rfl⟩

/-! ## Satisfiability witnesses -/

example [NeZero d] (hd : 2 ≤ d) :
    ∃ (D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d))),
      0 < D.freezingRadius (smallContrastThreshold d (1 / 2 : ℝ)) 0 :=
  ⟨{ two_le := hd
     nu_pos := one_pos
     skew := fun _ => by simp [matTranspose]
     contDiff := contDiff_const
     gradConst := 0
     gradConst_nonneg := le_rfl
     grad_le := fun y => by simp }, FieldInputData.freezingRadius_pos _
    (fieldInput_smallContrastThreshold_half_pos d) 0⟩

example [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ A : DivergenceForm.WholeSpaceAnalyticData d,
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          ∃ L : DivergenceForm.WholeSpaceLocalizedSplitData A,
            (∀ x r, L.roughBound x r = 0) :=
  fieldInput_ae_splitData
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end

end SuperdiffusionCLT.Section8
