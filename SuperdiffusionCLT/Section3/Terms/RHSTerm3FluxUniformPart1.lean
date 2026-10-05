/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Deterministic.WeakNormInterfaces.Localization
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Analytic
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscNormSwap
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Filter
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (vecHatNegENormOrderOne vecHatNegENormOrderOne_le_vecCubeLpENorm)

noncomputable section

variable {d : ℕ}

/-- The scale weight at depth `k+1`, factored as `3^scale · 3^{-k}`. Under
`j = R.scale - 1 - k` this is `3` times the printed weight `3^j`; that fixed
factor is absorbed into the dimension-only constant. -/
def fluxMsp_depthTerm (R : TriadicCube d) (F : Vec d → Vec d) (k : ℕ) : ℝ :=
  (3 : ℝ) ^ (R.scale : ℝ) * ((3 : ℝ)⁻¹) ^ k * vecDepthMoment R (k + 1) F

/-- The dimension-only constant in the centred multiscale Poincaré estimate. -/
def fluxMspConst (d : ℕ) : ℝ :=
  2 * (((originCubeMeanZeroH1CoerciveEstimate d 0).constant + 3) *
    multiscaleOrderOneConst d)

theorem fluxMspConst_nonneg (d : ℕ) : 0 ≤ fluxMspConst d := by
  have hC : 0 ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hP : 0 ≤ multiscaleOrderOneConst d := by
    have h := one_le_multiscaleOrderOneConst d
    linarith only [h]
  unfold fluxMspConst
  positivity

theorem fluxMsp_depthMoment_le_L2 (R : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet R) F) (j : ℕ) :
    vecDepthMoment R j F ≤ Real.sqrt (vecSqAvg R F) := by
  rw [vecDepthMoment]
  exact Real.sqrt_le_sqrt (vecDepthSqMoment_le_vecSqAvg_of_memVectorL2 R j hF)

theorem fluxMsp_depthTerm_nonneg (R : TriadicCube d) (F : Vec d → Vec d) (k : ℕ) :
    0 ≤ fluxMsp_depthTerm R F k := by
  unfold fluxMsp_depthTerm
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹) _))
    (vecDepthMoment_nonneg R (k + 1) F)

theorem fluxMsp_depthTerm_summable (R : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet R) F) :
    Summable (fluxMsp_depthTerm R F) := by
  let A : ℝ := (3 : ℝ) ^ (R.scale : ℝ) * Real.sqrt (vecSqAvg R F)
  have hterm : ∀ k : ℕ, 0 ≤ fluxMsp_depthTerm R F k :=
    fun k => fluxMsp_depthTerm_nonneg R F k
  have hle : ∀ k : ℕ,
      fluxMsp_depthTerm R F k ≤ A * ((3 : ℝ)⁻¹) ^ k := by
    intro k
    change (3 : ℝ) ^ (R.scale : ℝ) * ((3 : ℝ)⁻¹) ^ k *
        vecDepthMoment R (k + 1) F ≤ A * ((3 : ℝ)⁻¹) ^ k
    calc (3 : ℝ) ^ (R.scale : ℝ) * ((3 : ℝ)⁻¹) ^ k *
          vecDepthMoment R (k + 1) F
        ≤ (3 : ℝ) ^ (R.scale : ℝ) * ((3 : ℝ)⁻¹) ^ k *
            Real.sqrt (vecSqAvg R F) := by
              exact mul_le_mul_of_nonneg_left
                (fluxMsp_depthMoment_le_L2 R F hF (k + 1))
                (mul_nonneg
                  (Real.rpow_nonneg (show 0 ≤ (3 : ℝ) by norm_num) _)
                  (pow_nonneg (show 0 ≤ (3 : ℝ)⁻¹ by positivity) k))
      _ = ((3 : ℝ) ^ (R.scale : ℝ) * Real.sqrt (vecSqAvg R F)) *
            ((3 : ℝ)⁻¹) ^ k := by ring
      _ = A * ((3 : ℝ)⁻¹) ^ k := by rfl
  refine Summable.of_nonneg_of_le hterm hle ?_
  exact Summable.mul_left A
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- Jensen across the first descendant partition: the first depth controls the
mean on the parent cube. -/
theorem fluxMsp_mean_le_firstDepth (R : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet R) F) :
    vecDepthMoment R 0 F ≤ vecDepthMoment R 1 F := by
  have hmem := memLp_hilbertifyVecField_of_memVectorL2 hF
  have hvec : MemLp F 2 (normalizedCubeMeasure R) :=
    memLp_hilbertifyVecField_iff.1 hmem
  have hJ := Homogenization.vecNormSq_cubeAverageVec_le_descendantsAverage_vecNormSq_cubeAverageVec_one_of_memLp
    R F hvec
  have havg : ∀ Q : TriadicCube d,
      Homogenization.cubeAverageVec Q F = volumeAverageVec (cubeSet Q) F := by
    intro Q
    funext i
    change Homogenization.cubeAverage Q (fun x => F x i) =
      Homogenization.volumeAverage (cubeSet Q) (fun x => F x i)
    exact SuperdiffusionCLT.Section2.Estimates.Stream.cubeAverage_eq_volumeAverage Q _
  have hJ' : vecNormSq (volumeAverageVec (cubeSet R) F) ≤
      descendantsAverage R 1
        (fun R' => vecNormSq (volumeAverageVec (cubeSet R') F)) := by
    calc vecNormSq (volumeAverageVec (cubeSet R) F)
        = vecNormSq (Homogenization.cubeAverageVec R F) := by rw [havg]
      _ ≤ descendantsAverage R 1
          (fun R' => vecNormSq (Homogenization.cubeAverageVec R' F)) := hJ
      _ = descendantsAverage R 1
          (fun R' => vecNormSq (volumeAverageVec (cubeSet R') F)) := by
            congr 1
            funext R'
            rw [havg]
  rw [vecDepthMoment_zero, vecDepthMoment, vecDepthSqMoment]
  have hleft : vecNorm (volumeAverageVec (cubeSet R) F) =
      Real.sqrt (vecNormSq (volumeAverageVec (cubeSet R) F)) := by
    rw [← Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq,
      Real.sqrt_sq (vecNorm_nonneg _)]
  rw [hleft]
  exact Real.sqrt_le_sqrt hJ'

/-- The centred negative norm is controlled by the first `J+1` printed scales
plus the vanishing order-one endpoint remainder. -/
theorem fluxMsp_truncated (hd : 0 < d) (R : TriadicCube d)
    (F : Vec d → Vec d) (hF : MemVectorL2 (openCubeSet R) F) (J : ℕ) :
    (centredSeminormNegNorm R F).toReal ≤ fluxMspConst d *
      ((∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) +
        (3 : ℝ) ^ (R.scale : ℝ) * ((3 : ℝ)⁻¹) ^ (J + 1) *
          Real.sqrt (vecSqAvg R F)) := by
  let hFmem := memLp_hilbertifyVecField_of_memVectorL2 hF
  let S : ℝ := (3 : ℝ) ^ (R.scale : ℝ)
  let B : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant + 3
  let C : ℝ := multiscaleOrderOneConst d
  let L : ℝ := Real.sqrt (vecSqAvg R F)
  have hS : 0 < S := by
    dsimp [S]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hS0 : 0 ≤ S := hS.le
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have h := (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
    linarith only [h]
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have h := one_le_multiscaleOrderOneConst d
    linarith only [h]
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hK0 : 0 ≤ S * B := mul_nonneg hS0 hB0
  have hhatFinite : vecHatNegENormOrderOne R F ≠ ⊤ :=
    ne_top_of_le_ne_top hFmem.eLpNorm_lt_top.ne
      (vecHatNegENormOrderOne_le_vecCubeLpENorm hFmem)
  have hcomp := centredSeminormNegNorm_le_vecHatNegENormOrderOne hFmem
  have hcompR : (centredSeminormNegNorm R F).toReal ≤
      (S * B) * (vecHatNegENormOrderOne R F).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hhatFinite) hcomp
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at h
  have hEnd := vecHatNegENormOrderOne_le_depthSum_memLp hd R hFmem (J + 1)
  let T : ℝ := ∑ j ∈ Finset.range (J + 1 + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment R j F
  let E : ℝ := ((3 : ℝ) ^ (J + 1))⁻¹ * L
  have hT0 : 0 ≤ T := by
    dsimp [T]
    refine Finset.sum_nonneg fun j hj => mul_nonneg (by positivity)
      (vecDepthMoment_nonneg R j F)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEndRhs0 : 0 ≤ C * (T + E) := mul_nonneg hC0 (add_nonneg hT0 hE0)
  have hEndR : (vecHatNegENormOrderOne R F).toReal ≤ C * (T + E) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEnd
    rw [ENNReal.toReal_ofReal hEndRhs0] at h
    simpa only [T, E, L, Nat.cast_add, Nat.cast_one] using h
  have hbase : (centredSeminormNegNorm R F).toReal ≤ (S * B) * (C * (T + E)) :=
    le_trans hcompR (mul_le_mul_of_nonneg_left hEndR hK0)
  have hsplit : T =
      (∑ k ∈ Finset.range (J + 1), ((3 : ℝ) ^ (k + 1))⁻¹ *
        vecDepthMoment R (k + 1) F) + vecDepthMoment R 0 F := by
    dsimp [T]
    simpa only [pow_zero, inv_one, one_mul] using
      (Finset.sum_range_succ' (fun j => ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment R j F)
        (J + 1))
  have hchild : ∀ k : ℕ,
      S * (((3 : ℝ) ^ (k + 1))⁻¹ * vecDepthMoment R (k + 1) F) ≤
        fluxMsp_depthTerm R F k := by
    intro k
    have hw : ((3 : ℝ) ^ (k + 1))⁻¹ =
        (3 : ℝ)⁻¹ * ((3 : ℝ)⁻¹) ^ k := by
      rw [pow_succ, mul_inv, ← inv_pow]
      ring
    rw [hw, fluxMsp_depthTerm]
    have hprod : 0 ≤ S * ((3 : ℝ)⁻¹) ^ k * vecDepthMoment R (k + 1) F := by
      exact mul_nonneg (mul_nonneg hS0 (pow_nonneg (by norm_num) _))
        (vecDepthMoment_nonneg R (k + 1) F)
    calc S * ((3 : ℝ)⁻¹ * ((3 : ℝ)⁻¹) ^ k * vecDepthMoment R (k + 1) F)
        = (3 : ℝ)⁻¹ *
            (S * ((3 : ℝ)⁻¹) ^ k * vecDepthMoment R (k + 1) F) := by ring
      _ ≤ 1 * (S * ((3 : ℝ)⁻¹) ^ k * vecDepthMoment R (k + 1) F) :=
        mul_le_mul_of_nonneg_right (by norm_num) hprod
      _ = S * ((3 : ℝ)⁻¹) ^ k * vecDepthMoment R (k + 1) F := by ring
  have htop : S * vecDepthMoment R 0 F ≤ fluxMsp_depthTerm R F 0 := by
    rw [fluxMsp_depthTerm, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (fluxMsp_mean_le_firstDepth R F hF) hS0
  have hfinite : S * T ≤ 2 * (∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) := by
    rw [hsplit]
    calc S * ((∑ k ∈ Finset.range (J + 1),
          ((3 : ℝ) ^ (k + 1))⁻¹ * vecDepthMoment R (k + 1) F) +
          vecDepthMoment R 0 F)
        = (∑ k ∈ Finset.range (J + 1),
            S * (((3 : ℝ) ^ (k + 1))⁻¹ * vecDepthMoment R (k + 1) F)) +
          S * vecDepthMoment R 0 F := by rw [mul_add, Finset.mul_sum]
      _ ≤ (∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) +
          fluxMsp_depthTerm R F 0 := by
            exact add_le_add (Finset.sum_le_sum fun k hk => hchild k) htop
      _ ≤ 2 * (∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) := by
            have hfirst : fluxMsp_depthTerm R F 0 ≤
                ∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k :=
              Finset.single_le_sum (fun k hk => fluxMsp_depthTerm_nonneg R F k)
                (Finset.mem_range.mpr (Nat.zero_lt_succ J))
            linarith only [hfirst]
  have hrem : 0 ≤ S * E := mul_nonneg hS0 hE0
  have hsumrem : S * (T + E) ≤
      2 * ((∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) + S * E) := by
    calc S * (T + E) = S * T + S * E := by ring
      _ ≤ 2 * (∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) + 2 * (S * E) :=
        add_le_add hfinite (by linarith only [hrem])
      _ = 2 * ((∑ k ∈ Finset.range (J + 1), fluxMsp_depthTerm R F k) + S * E) := by ring
  have hEeq : S * E =
      S * ((3 : ℝ)⁻¹) ^ (J + 1) * Real.sqrt (vecSqAvg R F) := by
    dsimp [E, L]
    rw [← inv_pow]
    ring
  calc (centredSeminormNegNorm R F).toReal
      ≤ (S * B) * (C * (T + E)) := hbase
    _ = (B * C) * (S * (T + E)) := by ring
    _ ≤ (B * C) * (2 * ((∑ k ∈ Finset.range (J + 1),
          fluxMsp_depthTerm R F k) + S * E)) :=
        mul_le_mul_of_nonneg_left hsumrem (mul_nonneg hB0 hC0)
    _ = fluxMspConst d * ((∑ k ∈ Finset.range (J + 1),
          fluxMsp_depthTerm R F k) + S * E) := by
        dsimp [fluxMspConst, B, C]
        ring
    _ = fluxMspConst d * ((∑ k ∈ Finset.range (J + 1),
          fluxMsp_depthTerm R F k) +
            (3 : ℝ) ^ (R.scale : ℝ) * ((3 : ℝ)⁻¹) ^ (J + 1) *
              Real.sqrt (vecSqAvg R F)) := by
        rw [hEeq]

theorem fluxMsp_main (hd : 0 < d) (R : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet R) F) :
    (centredSeminormNegNorm R F).toReal ≤ fluxMspConst d *
      ∑' k : ℕ, fluxMsp_depthTerm R F k := by
  let S : ℝ := (3 : ℝ) ^ (R.scale : ℝ)
  let L : ℝ := Real.sqrt (vecSqAvg R F)
  let b : ℕ → ℝ := fluxMsp_depthTerm R F
  have hb : Summable b := by
    dsimp [b]
    exact fluxMsp_depthTerm_summable R F hF
  have hpartial : Tendsto
      (fun J : ℕ => ∑ k ∈ Finset.range (J + 1), b k) Filter.atTop
      (nhds (∑' k : ℕ, b k)) := by
    have h := hb.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact h
  have hgeom : Summable (fun J : ℕ => ((3 : ℝ)⁻¹) ^ J) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hpow : Tendsto (fun J : ℕ => ((3 : ℝ)⁻¹) ^ (J + 1)) Filter.atTop (nhds 0) :=
    hgeom.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have hrem : Tendsto (fun J : ℕ =>
      S * (((3 : ℝ)⁻¹) ^ (J + 1)) * L) Filter.atTop (nhds 0) := by
    have hSconst : Tendsto (fun _ : ℕ => S) Filter.atTop (nhds S) := tendsto_const_nhds
    have hLconst : Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) := tendsto_const_nhds
    simpa only [mul_zero, zero_mul] using (hSconst.mul hpow).mul hLconst
  have hlim : Tendsto
      (fun J : ℕ => fluxMspConst d *
        ((∑ k ∈ Finset.range (J + 1), b k) +
          S * (((3 : ℝ)⁻¹) ^ (J + 1)) * L)) Filter.atTop
      (nhds (fluxMspConst d * ∑' k : ℕ, b k)) := by
    have hadd := hpartial.add hrem
    have hCconst : Tendsto (fun _ : ℕ => fluxMspConst d) Filter.atTop
        (nhds (fluxMspConst d)) := tendsto_const_nhds
    have hmul := hCconst.mul hadd
    simpa only [Nat.add_comm, add_zero, S, L, b] using hmul
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun J => by
    have h := fluxMsp_truncated hd R F hF J
    simpa only [S, L, b, fluxMsp_depthTerm] using h

/-- The cutoff coefficient preserves `MemVectorL2` of a vector field, which
supplies the generic input to `fluxMsp_main` at flux carriers. -/
theorem fluxMsp_memVectorL2_fluxFieldCarrier {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (uMgrad uNGlued : Vec d → Vec d) (R : TriadicCube d)
    (hV : MemVectorL2 (openCubeSet R) (fun y => uMgrad y - uNGlued y)) :
    MemVectorL2 (openCubeSet R)
      (fluxFieldCarrier nu S omega uMgrad uNGlued) := by
  unfold fluxFieldCarrier
  exact memVectorL2_matVecMul_coefficientCutoff (d := d) (nu := nu)
    hnu omega S.LPrime R hV

/-- The `MemVectorL2` input for a flux of two glued gradients is supplied by
`memVectorL2_openCubeSet_gluedGradientField` and the cutoff product bound. -/
theorem fluxMsp_memVectorL2_fluxFieldCarrier_gluedDiff {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (L₁ L₂ k₁ k₂ m : ℕ) (F : Vec d) (R : TriadicCube d) :
    MemVectorL2 (openCubeSet R)
      (fluxFieldCarrier nu S omega
        (gluedGradientField hnu L₁ k₁ m F omega)
        (gluedGradientField hnu L₂ k₂ m F omega)) :=
  fluxMsp_memVectorL2_fluxFieldCarrier hnu S omega
    (gluedGradientField hnu L₁ k₁ m F omega)
    (gluedGradientField hnu L₂ k₂ m F omega) R
    ((memVectorL2_openCubeSet_gluedGradientField hnu L₁ k₁ m F omega R).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k₂ m F omega R))

end

end SuperdiffusionCLT.Section3.Terms
