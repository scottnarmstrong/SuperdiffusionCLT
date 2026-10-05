/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputC

/-!
# The rough split of the marginal field

For the shift `mu < 1` the diffusive rate of the localized tail needs the field in the rough slot:
`a = nu Id + ks + kl` with `ks = k` bounded on balls by a power of the logarithm of the
observation radius and `kl = 0`.  This file records the bounds of such a split datum
(`RoughLogBounds`) and builds the datum for a field `k` with the pointwise growth bound
`|k y| <= c0 (log (K^2 + |y|^2)) ^ n`.
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

/-- Bounds of a rough split datum: the rough bound is `c0` times the `n`-th power of the logarithm
of `K ^ 2 + (|x| + r) ^ 2`, the smooth part vanishes, and the freezing radius is `amp / (1 + |x|)`. -/
structure RoughLogBounds {d : ℕ} [NeZero d] {A : DivergenceForm.WholeSpaceAnalyticData d}
    (L : DivergenceForm.WholeSpaceLocalizedSplitData A) where
  c0 : ℝ
  c0_nonneg : 0 ≤ c0
  Kc : ℝ
  two_le_Kc : 2 ≤ Kc
  n : ℕ
  two_le_n : 2 ≤ n
  amp : ℝ
  amp_pos : 0 < amp
  amp_le_one : amp ≤ 1
  holder_eq : L.holderExponent = 1 / 2
  rough_eq : ∀ (x : Vec d) (r : ℝ),
    L.roughBound x r = c0 * Real.log (Kc ^ 2 + (euclideanNorm x + r) ^ 2) ^ n
  smooth_eq : ∀ (x : Vec d) (r : ℝ), L.smoothDivBound x r = 0
  freeze_eq : ∀ x : Vec d, L.freezingRadius x = amp / (1 + euclideanNorm x)

variable {d : ℕ} {nu : ℝ} {k : Vec d → Mat d}

theorem crudeMomL_euclideanNorm_le_of_mem {x y : Vec d} {r : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ euclideanBall x r) : euclideanNorm y ≤ euclideanNorm x + r := by
  have h1 := DivergenceForm.Decay.euclideanNorm_sub_lt_of_mem_euclideanBall hr hy
  have h2 := fieldInput_euclideanNorm_add_le x (y - x)
  rw [add_sub_cancel] at h2
  linarith only [h1, h2]

theorem crudeMomL_one_le_log {K : ℝ} (hK : 2 ≤ K) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ Real.log (K ^ 2 + u) := by
  have h4 : (4 : ℝ) ≤ K ^ 2 + u := by nlinarith only [hK, hu]
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith only [this]
  rw [Real.le_log_iff_exp_le (by linarith only [h4])]
  linarith only [he, h4]

section Split

variable [NeZero d]

/-- **The rough split datum of the marginal field**: `a = nu Id + k + 0`, the rough part is the
whole field, bounded on balls by the logarithmic bound `c0 (log (K^2 + (|x|+r)^2)) ^ n`. -/
def FieldInputData.roughSplitData (D : FieldInputData d nu k) (c0 Kc : ℝ) (n : ℕ)
    (hc0 : 0 ≤ c0) (hKc : 2 ≤ Kc)
    (hk : ∀ y, matrixOperatorNorm (k y) ≤ c0 * Real.log (Kc ^ 2 + vecNormSq y) ^ n) :
    DivergenceForm.WholeSpaceLocalizedSplitData D.analyticData where
  ks := k
  kl := fun _ => 0
  split := fun y => by
    change nu • (1 : Mat d) + k y = nu • (1 : Mat d) + k y + 0
    rw [add_zero]
  ksSkew := D.skew
  klSkew := fun y => by simp [matTranspose]
  klContDiff := fun p q => contDiff_const
  roughEllipticityUpper := fun m =>
    axisCubeEllipticUpper (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m) D.nu_pos
      (a := fun y => nu • (1 : Mat d) + k y)
      (fun y => DivergenceForm.Decay.symmPart_scalar_add_skew rfl (D.skew y))
      (D.continuous.continuousOn.congr (fun y _ => by simp))
  roughEllipticity := fun m =>
    isEllipticFieldOn_axisCubeEllipticUpper (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m)
      D.nu_pos (a := fun y => nu • (1 : Mat d) + k y)
      (fun y => DivergenceForm.Decay.symmPart_scalar_add_skew rfl (D.skew y))
      (D.continuous.continuousOn.congr (fun y _ => by simp))
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
  roughBound := fun x r => c0 * Real.log (Kc ^ 2 + (euclideanNorm x + r) ^ 2) ^ n
  smoothDivBound := fun _ _ => 0
  roughBound_nonneg := fun x r _ =>
    mul_nonneg hc0 (pow_nonneg (zero_le_one.trans
      (crudeMomL_one_le_log hKc (sq_nonneg _))) n)
  smoothDivBound_nonneg := fun _ _ _ => le_rfl
  roughBound_spec := fun x r hr y hy v => by
    have hnorm := crudeMomL_euclideanNorm_le_of_mem hr hy
    have hy0 := euclideanNorm_nonneg y
    have hlog : Real.log (Kc ^ 2 + vecNormSq y) ≤
        Real.log (Kc ^ 2 + (euclideanNorm x + r) ^ 2) := by
      apply Real.log_le_log (by nlinarith only [hKc, vecNormSq_nonneg y])
      have : vecNormSq y ≤ (euclideanNorm x + r) ^ 2 := by
        rw [← euclideanNorm_sq y]
        exact pow_le_pow_left₀ hy0 hnorm 2
      linarith only [this]
    have hl0 : 0 ≤ Real.log (Kc ^ 2 + vecNormSq y) :=
      zero_le_one.trans (crudeMomL_one_le_log hKc (vecNormSq_nonneg y))
    have hb : matrixOperatorNorm (k y) ≤ c0 * Real.log (Kc ^ 2 + (euclideanNorm x + r) ^ 2) ^ n :=
      (hk y).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hlog n) hc0)
    calc vecNormSq (matVecMul (k y) v) ≤ ‖HilbertVec.applyMat (k y)‖ ^ 2 * vecNormSq v :=
          vecNormSq_matVecMul_le_applyMat_opNorm_sq_mul (k y) v
      _ ≤ (c0 * Real.log (Kc ^ 2 + (euclideanNorm x + r) ^ 2) ^ n) ^ 2 * vecNormSq v := by
          apply mul_le_mul_of_nonneg_right _ (vecNormSq_nonneg v)
          rw [← matrixOperatorNorm_eq_applyMat_norm]
          exact pow_le_pow_left₀ (by simp [matrixOperatorNorm]) hb 2
  smoothDivBound_spec := fun x r hr y hy => by
    have : DivergenceForm.Decay.skewFieldDiv (fun _ : Vec d => (0 : Mat d)) y = 0 := by
      ext j
      simp [DivergenceForm.Decay.skewFieldDiv_apply, euclideanCoordDeriv]
    simp [this, vecNormSq, vecDot]

/-- The rough split datum satisfies the rough logarithmic bounds. -/
def FieldInputData.roughLogBounds (D : FieldInputData d nu k) (c0 Kc : ℝ) (n : ℕ)
    (hc0 : 0 ≤ c0) (hKc : 2 ≤ Kc) (hn : 2 ≤ n)
    (hk : ∀ y, matrixOperatorNorm (k y) ≤ c0 * Real.log (Kc ^ 2 + vecNormSq y) ^ n) :
    RoughLogBounds (D.roughSplitData c0 Kc n hc0 hKc hk) where
  c0 := c0
  c0_nonneg := hc0
  Kc := Kc
  two_le_Kc := hKc
  n := n
  two_le_n := hn
  amp := D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))
  amp_pos := D.freezingAmplitude_pos (fieldInput_smallContrastThreshold_half_pos d)
  amp_le_one := D.freezingAmplitude_le_one _
  holder_eq := rfl
  rough_eq := fun _ _ => rfl
  smooth_eq := fun _ _ => rfl
  freeze_eq := fun _ => rfl

/-- The rough bounds are satisfiable: the zero field with `c0 = 0`. -/
example (hd : 2 ≤ d) :
    ∃ D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)),
      ∃ h : ∀ y : Vec d, matrixOperatorNorm ((fun _ : Vec d => (0 : Mat d)) y) ≤
          (0 : ℝ) * Real.log ((2 : ℝ) ^ 2 + vecNormSq y) ^ 2,
        (D.roughLogBounds 0 2 2 le_rfl le_rfl le_rfl h).c0 = 0 := by
  refine ⟨{ two_le := hd
            nu_pos := one_pos
            skew := fun _ => by simp [matTranspose]
            contDiff := contDiff_const
            gradConst := 0
            gradConst_nonneg := le_rfl
            grad_le := fun y => by simp }, fun y => ?_, rfl⟩
  simp [matrixOperatorNorm]

end Split

end

end SuperdiffusionCLT.Section8
