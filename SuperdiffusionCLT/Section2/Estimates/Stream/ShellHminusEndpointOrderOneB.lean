/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOne
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellSpatialAverage
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellValueLargeCube

/-!
# The truncated multiscale bound and the order-one shell endpoint

The estimate `e.jk.Hminus.endpoint`,
continued from `ShellHminusEndpointOrderOne`: on a triadic cube `Q` of scale
`l`, for a continuous vector field `F` and every truncation depth `J`,
`‖F‖_{Ĥ̲^{-1}(Q)} ≤ C(d)(∑_{j ≤ J} 3^{-j}(avsum_{R∈D_j}|(F)_R|²)^{1/2}
+ 3^{-J}‖F‖_{L̲²(Q)})`, and its shell instance at `J = l - k`, with the `Γ₂`
tail of the resulting envelope at amplitude `C(d)|p|(1 + (l-k))3^{-(l-k)}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Elementary algebra of descendant averages -/

/-! ## The depth-`j` truncation of the pairing -/

/-- **The depth-`J` truncation error of the pairing.** The pairing of a
continuous field against an admissible order-one test gradient differs from its
depth-`J` sub-cube truncation by at most
`C(d) 3^{l-J} ‖F‖_{L̲²(Q)} ‖∇²g‖_{L̲²(Q)}`. -/
theorem abs_volumeAverage_vecDot_sub_depthPairing_le (hd : 0 < d)
    (Q : TriadicCube d) (j : ℕ) {F : Vec d → Vec d} (hF : Continuous F)
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (euclideanGradient g x)) -
        descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) (euclideanGradient g)))| ≤
      Real.sqrt (vecSqAvg Q F) *
        (poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) *
          Real.sqrt (matSqAvg Q (euclideanGradientJacobian g))) := by
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  have hGcont : Continuous G := continuous_euclideanGradient' hg
  set K : ℝ := poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) with hKdef
  have hKnn : 0 ≤ K :=
    mul_nonneg (poincareCubeConst_nonneg d) (by positivity)
  have hid : volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x)) -
      descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
        (volumeAverageVec (cubeSet R) G)) =
      descendantsAverage Q j (fun R => volumeAverage (cubeSet R)
        (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G))) := by
    rw [volumeAverage_eq_descendantsAverage Q j (continuous_vecDot hF hGcont),
      descendantsAverage_sub]
    exact congrArg (descendantsAverage Q j)
      (funext fun R => volumeAverage_vecDot_sub_average R hF hGcont)
  rw [hid]
  refine le_trans (abs_descendantsAverage_le Q j _) ?_
  have hCS : ∀ R ∈ descendantsAtDepth Q j,
      |volumeAverage (cubeSet R)
          (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G))| ≤
        Real.sqrt (vecSqAvg R F) *
          Real.sqrt (vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)) :=
    fun R _ => abs_volumeAverage_vecDot_le_sqrt_mul_sqrt R hF
      (hGcont.sub continuous_const)
  refine le_trans (descendantsAverage_le_descendantsAverage Q j hCS) ?_
  refine le_trans (descendantsAverage_mul_le_sqrt_mul_sqrt Q j _ _) ?_
  have hA : descendantsAverage Q j (fun R => Real.sqrt (vecSqAvg R F) ^ 2) =
      vecSqAvg Q F := by
    rw [show (fun R : TriadicCube d => Real.sqrt (vecSqAvg R F) ^ 2)
        = fun R : TriadicCube d => vecSqAvg R F from
      funext fun R => Real.sq_sqrt (vecSqAvg_nonneg R F)]
    exact (vecSqAvg_eq_descendantsAverage Q j hF).symm
  have hB : descendantsAverage Q j (fun R =>
        Real.sqrt (vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)) ^ 2) =
      descendantsAverage Q j (fun R =>
        vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)) :=
    congrArg (descendantsAverage Q j)
      (funext fun R => Real.sq_sqrt (vecSqAvg_nonneg R _))
  rw [hA, hB]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hKP := descendantsAverage_vecSqAvg_sub_average_le hd Q j hg
  rw [← hKdef] at hKP
  calc Real.sqrt (descendantsAverage Q j (fun R =>
        vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G)))
      ≤ Real.sqrt (K ^ 2 * matSqAvg Q (euclideanGradientJacobian g)) :=
        Real.sqrt_le_sqrt hKP
    _ = K * Real.sqrt (matSqAvg Q (euclideanGradientJacobian g)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKnn]

/-! ## The telescoping increment -/

/-- **The depth-`j` increment of the truncated pairing.** -/
theorem abs_depthPairing_succ_sub_le (hd : 0 < d) (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : Continuous F) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    |descendantsAverage Q (j + 1) (fun R => vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) (euclideanGradient g))) -
        descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) (euclideanGradient g)))| ≤
      vecDepthMoment Q (j + 1) F *
        (poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) *
          Real.sqrt (matSqAvg Q (euclideanGradientJacobian g))) := by
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  have hGcont : Continuous G := continuous_euclideanGradient' hg
  set K : ℝ := poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) with hKdef
  have hKnn : 0 ≤ K :=
    mul_nonneg (poincareCubeConst_nonneg d) (by positivity)
  -- the increment as an iterated average
  have hid : descendantsAverage Q (j + 1) (fun R => vecDot
        (volumeAverageVec (cubeSet R) F) (volumeAverageVec (cubeSet R) G)) -
      descendantsAverage Q j (fun R => vecDot (volumeAverageVec (cubeSet R) F)
        (volumeAverageVec (cubeSet R) G)) =
      descendantsAverage Q j (fun R => descendantsAverage R 1 (fun R' =>
        vecDot (volumeAverageVec (cubeSet R') F)
          (volumeAverageVec (cubeSet R') G - volumeAverageVec (cubeSet R) G))) := by
    rw [descendantsAverage_succ_eq_descendantsAverage_descendantsAverage,
      descendantsAverage_sub]
    refine congrArg (descendantsAverage Q j) (funext fun R => ?_)
    rw [vecDot_volumeAverageVec_eq_descendantsAverage R 1 hF
      (volumeAverageVec (cubeSet R) G), descendantsAverage_sub]
    exact congrArg (descendantsAverage R 1)
      (funext fun R' => (vecDot_sub_right _ _ _).symm)
  rw [hid]
  -- two absolute values and the pointwise Cauchy-Schwarz
  refine le_trans (abs_descendantsAverage_le Q j _) ?_
  have hinner : ∀ R ∈ descendantsAtDepth Q j,
      |descendantsAverage R 1 (fun R' => vecDot (volumeAverageVec (cubeSet R') F)
          (volumeAverageVec (cubeSet R') G - volumeAverageVec (cubeSet R) G))| ≤
        Real.sqrt (descendantsAverage R 1
            (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2)) *
          Real.sqrt (descendantsAverage R 1 (fun R' =>
            vecNorm (volumeAverageVec (cubeSet R') G -
              volumeAverageVec (cubeSet R) G) ^ 2)) := by
    intro R _
    refine le_trans (abs_descendantsAverage_le R 1 _) ?_
    refine le_trans (descendantsAverage_le_descendantsAverage R 1
      (fun R' _ => abs_vecDot_le_vecNorm_mul_vecNorm _ _)) ?_
    exact descendantsAverage_mul_le_sqrt_mul_sqrt R 1 _ _
  refine le_trans (descendantsAverage_le_descendantsAverage Q j hinner) ?_
  refine le_trans (descendantsAverage_mul_le_sqrt_mul_sqrt Q j _ _) ?_
  -- identify the two factors
  have hnnA : ∀ R : TriadicCube d, 0 ≤ descendantsAverage R 1
      (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2) :=
    fun R => descendantsAverage_nonneg R 1 _ fun _ _ => by positivity
  have hnnB : ∀ R : TriadicCube d, 0 ≤ descendantsAverage R 1 (fun R' =>
      vecNorm (volumeAverageVec (cubeSet R') G -
        volumeAverageVec (cubeSet R) G) ^ 2) :=
    fun R => descendantsAverage_nonneg R 1 _ fun _ _ => by positivity
  have hA : descendantsAverage Q j (fun R => Real.sqrt (descendantsAverage R 1
        (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2)) ^ 2) =
      vecDepthSqMoment Q (j + 1) F := by
    rw [show (fun R : TriadicCube d => Real.sqrt (descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2)) ^ 2)
        = fun R : TriadicCube d => descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') F) ^ 2) from
      funext fun R => Real.sq_sqrt (hnnA R)]
    rw [vecDepthSqMoment,
      descendantsAverage_succ_eq_descendantsAverage_descendantsAverage]
    exact congrArg (descendantsAverage Q j) (funext fun R =>
      congrArg (descendantsAverage R 1) (funext fun R' => Book.Ch02.vecNorm_sq_eq_vecNormSq _))
  have hB : descendantsAverage Q j (fun R => Real.sqrt (descendantsAverage R 1
        (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
          volumeAverageVec (cubeSet R) G) ^ 2)) ^ 2) ≤
      K ^ 2 * matSqAvg Q (euclideanGradientJacobian g) := by
    rw [show (fun R : TriadicCube d => Real.sqrt (descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
            volumeAverageVec (cubeSet R) G) ^ 2)) ^ 2)
        = fun R : TriadicCube d => descendantsAverage R 1
          (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
            volumeAverageVec (cubeSet R) G) ^ 2) from
      funext fun R => Real.sq_sqrt (hnnB R)]
    have hstep : ∀ R ∈ descendantsAtDepth Q j,
        descendantsAverage R 1 (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
            volumeAverageVec (cubeSet R) G) ^ 2) ≤
          vecSqAvg R (fun x => G x - volumeAverageVec (cubeSet R) G) := by
      intro R _
      have hcent : Continuous (fun x => G x - volumeAverageVec (cubeSet R) G) :=
        hGcont.sub continuous_const
      have hpt : ∀ R' : TriadicCube d,
          vecNorm (volumeAverageVec (cubeSet R') G -
              volumeAverageVec (cubeSet R) G) ^ 2 ≤
            vecSqAvg R' (fun x => G x - volumeAverageVec (cubeSet R) G) := by
        intro R'
        rw [Book.Ch02.vecNorm_sq_eq_vecNormSq, ← volumeAverageVec_sub_const R' hGcont
          (volumeAverageVec (cubeSet R) G)]
        exact vecNormSq_volumeAverageVec_le R' hcent
      refine le_trans (descendantsAverage_le_descendantsAverage R 1
        (fun R' _ => hpt R')) ?_
      exact le_of_eq (vecSqAvg_eq_descendantsAverage R 1 hcent).symm
    refine le_trans (descendantsAverage_le_descendantsAverage Q j hstep) ?_
    have hKP := descendantsAverage_vecSqAvg_sub_average_le hd Q j hg
    rw [← hKdef] at hKP
    exact hKP
  rw [hA]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (descendantsAverage Q j (fun R => Real.sqrt (descendantsAverage R 1
        (fun R' => vecNorm (volumeAverageVec (cubeSet R') G -
          volumeAverageVec (cubeSet R) G) ^ 2)) ^ 2))
      ≤ Real.sqrt (K ^ 2 * matSqAvg Q (euclideanGradientJacobian g)) :=
        Real.sqrt_le_sqrt hB
    _ = K * Real.sqrt (matSqAvg Q (euclideanGradientJacobian g)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKnn]

/-! ## The truncated multiscale bound -/

/-- **The truncated multiscale Poincare inequality at order one**, for one
admissible test potential: the pairing `⨍_Q F·∇g` is at most the printed `ℓ¹`
depth sum down to depth `J`, plus the truncation remainder
`3^{-J}‖F‖_{L̲²(Q)}`. -/
theorem volumeAverage_vecGradientPairingDensity_le (hd : 0 < d)
    (Q : TriadicCube d) {F : Vec d → Vec d} (hF : Continuous F) (J : ℕ)
    {g : Vec d → ℝ} (hg : IsVecHatTestFieldOrderOne Q g) :
    volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) ≤
      multiscaleOrderOneConst d *
        ((∑ j ∈ Finset.range (J + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F) +
          ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
  classical
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  set H : Vec d → Mat d := euclideanGradientJacobian g with hHdef
  have hGcont : Continuous G := continuous_euclideanGradient' hg.contDiff
  set C : ℝ := poincareCubeConst d with hCdef
  have hCnn : 0 ≤ C := poincareCubeConst_nonneg d
  set S : ℝ := (3 : ℝ) ^ Q.scale * Real.sqrt (matSqAvg Q H) with hSdef
  have hS1 : S ≤ 1 := threePow_mul_sqrt_matSqAvg_le_one hg
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    positivity
  set P : ℕ → ℝ := fun j => descendantsAverage Q j
    (fun R => vecDot (volumeAverageVec (cubeSet R) F)
      (volumeAverageVec (cubeSet R) G)) with hPdef
  set I : ℝ := volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x)) with hIdef
  have hdens : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) = I := by
    rw [hIdef]
    exact congrArg (volumeAverage (cubeSet Q))
      (funext fun x =>
        SuperdiffusionCLT.Section2.Norms.vecGradientPairingDensity_eq_vecDot F g x)
  rw [hdens]
  -- the weights
  have hw : ∀ j : ℕ, (0 : ℝ) ≤ ((3 : ℝ) ^ j)⁻¹ := fun j => by positivity
  have hterm : ∀ j : ℕ, (0 : ℝ) ≤ ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F :=
    fun j => mul_nonneg (hw j) (vecDepthMoment_nonneg Q j F)
  set T : ℝ := ∑ j ∈ Finset.range (J + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F
    with hTdef
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun j _ => hterm j
  -- the three pieces
  have hP0 : P 0 = vecDot (volumeAverageVec (cubeSet Q) F)
      (volumeAverageVec (cubeSet Q) G) := descendantsAverage_zero Q _
  have h0 : |P 0| ≤ vecDepthMoment Q 0 F := by
    rw [hP0, vecDepthMoment_zero]
    refine le_trans (abs_vecDot_le_vecNorm_mul_vecNorm _ _) ?_
    have hG1 : vecNorm (volumeAverageVec (cubeSet Q) G) ≤ 1 :=
      le_trans (vecNorm_volumeAverageVec_le_sqrt Q hGcont)
        (sqrt_vecSqAvg_euclideanGradient_le_one hg)
    calc vecNorm (volumeAverageVec (cubeSet Q) F) *
          vecNorm (volumeAverageVec (cubeSet Q) G)
        ≤ vecNorm (volumeAverageVec (cubeSet Q) F) * 1 :=
          mul_le_mul_of_nonneg_left hG1 (vecNorm_nonneg _)
      _ = vecNorm (volumeAverageVec (cubeSet Q) F) := mul_one _
  have hstep : ∀ j : ℕ, |P (j + 1) - P j| ≤
      3 * C * (((3 : ℝ) ^ (j + 1))⁻¹ * vecDepthMoment Q (j + 1) F) := by
    intro j
    refine le_trans (abs_depthPairing_succ_sub_le hd Q j hF hg.contDiff) ?_
    have hrw : vecDepthMoment Q (j + 1) F *
        (C * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) * Real.sqrt (matSqAvg Q H)) =
        (C * (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q (j + 1) F)) * S := by
      rw [hSdef]; ring
    rw [hrw]
    have hle : (C * (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q (j + 1) F)) * S ≤
        (C * (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q (j + 1) F)) * 1 :=
      mul_le_mul_of_nonneg_left hS1
        (mul_nonneg hCnn (mul_nonneg (hw j) (vecDepthMoment_nonneg Q (j + 1) F)))
    refine le_trans hle (le_of_eq ?_)
    have h3 : ((3 : ℝ) ^ (j + 1))⁻¹ = ((3 : ℝ) ^ j)⁻¹ / 3 := by
      rw [pow_succ, mul_inv]
      ring
    rw [h3]
    ring
  have hrem : |I - P J| ≤ C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
    refine le_trans (abs_volumeAverage_vecDot_sub_depthPairing_le hd Q J hF hg.contDiff) ?_
    have hrw : Real.sqrt (vecSqAvg Q F) *
        (C * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ J)⁻¹) * Real.sqrt (matSqAvg Q H)) =
        (C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) * S := by
      rw [hSdef]; ring
    rw [hrw]
    have hle : (C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) * S ≤
        (C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) * 1 :=
      mul_le_mul_of_nonneg_left hS1
        (mul_nonneg hCnn (mul_nonneg (hw J) (Real.sqrt_nonneg _)))
    rw [mul_one] at hle
    exact hle
  -- the telescoping identity
  have htel : I = P 0 + (∑ j ∈ Finset.range J, (P (j + 1) - P j)) + (I - P J) := by
    rw [Finset.sum_range_sub P J]
    ring
  have hchain : I ≤ |P 0| + (∑ j ∈ Finset.range J, |P (j + 1) - P j|) +
      |I - P J| := by
    have h1 : P 0 ≤ |P 0| := le_abs_self _
    have h2 : (∑ j ∈ Finset.range J, (P (j + 1) - P j)) ≤
        ∑ j ∈ Finset.range J, |P (j + 1) - P j| :=
      Finset.sum_le_sum fun j _ => le_abs_self _
    have h3 : I - P J ≤ |I - P J| := le_abs_self _
    linarith only [htel, h1, h2, h3]
  -- the sum of the increments
  have hsumstep : (∑ j ∈ Finset.range J, |P (j + 1) - P j|) ≤ 3 * C * T := by
    have hb : (∑ j ∈ Finset.range J, |P (j + 1) - P j|) ≤
        ∑ j ∈ Finset.range J,
          3 * C * (((3 : ℝ) ^ (j + 1))⁻¹ * vecDepthMoment Q (j + 1) F) :=
      Finset.sum_le_sum fun j _ => hstep j
    refine le_trans hb ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsplit : T = (∑ j ∈ Finset.range J,
        ((3 : ℝ) ^ (j + 1))⁻¹ * vecDepthMoment Q (j + 1) F) +
        ((3 : ℝ) ^ 0)⁻¹ * vecDepthMoment Q 0 F := by
      rw [hTdef]
      exact Finset.sum_range_succ' (fun j => ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F) J
    have h0nn : (0 : ℝ) ≤ ((3 : ℝ) ^ 0)⁻¹ * vecDepthMoment Q 0 F := hterm 0
    linarith only [hsplit, h0nn]
  -- the depth-zero term
  have hzero : vecDepthMoment Q 0 F ≤ T := by
    have hmem : (0 : ℕ) ∈ Finset.range (J + 1) := Finset.mem_range.2 (Nat.succ_pos J)
    have hle := Finset.single_le_sum
      (f := fun j => ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F)
      (fun j _ => hterm j) hmem
    simpa using hle
  -- assemble
  have hfinal : I ≤ T + 3 * C * T + C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
    have := le_trans h0 hzero
    linarith only [hchain, this, hsumstep, hrem]
  have hCle : C ≤ multiscaleOrderOneConst d :=
    poincareCubeConst_le_multiscaleOrderOneConst d
  have hRnn : (0 : ℝ) ≤ ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F) :=
    mul_nonneg (hw J) (Real.sqrt_nonneg _)
  have hexp : multiscaleOrderOneConst d * (T + ((3 : ℝ) ^ J)⁻¹ *
      Real.sqrt (vecSqAvg Q F)) =
      (1 + 3 * C) * T + multiscaleOrderOneConst d *
        (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) := by
    rw [multiscaleOrderOneConst, hCdef]
    ring
  rw [hexp]
  have hlast : C * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) ≤
      multiscaleOrderOneConst d * (((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F)) :=
    mul_le_mul_of_nonneg_right hCle hRnn
  linarith only [hfinal, hlast]

/-- **The truncated multiscale Poincare inequality at order one.**  For a
continuous field `F` on a triadic cube `Q` of scale `l` and every truncation
depth `J`,

`‖F‖_{Ĥ̲^{-1}(Q)} ≤ C(d) ( ∑_{j ≤ J} 3^{-j} (avsum_{R ∈ D_j} |(F)_R|²)^{1/2}
    + 3^{-J} ‖F‖_{L̲²(Q)} )`.

This is the endpoint `s = 1`, `p = 2` of `e.apply.multiscale.Poincare` in the
order-one carrier `vecHatNegENormOrderOne`, in
the `ℓ¹` form the paper states, with the printed infinite tail replaced by
the explicit `L̲²` remainder. -/
theorem vecHatNegENormOrderOne_le_depthSum (hd : 0 < d) (Q : TriadicCube d)
    {F : Vec d → Vec d} (hF : Continuous F) (J : ℕ) :
    vecHatNegENormOrderOne Q F ≤ ENNReal.ofReal (multiscaleOrderOneConst d *
      ((∑ j ∈ Finset.range (J + 1), ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j F) +
        ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q F))) :=
  vecHatNegENormOrderOne_le fun _g hg => ENNReal.ofReal_le_ofReal
    (volumeAverage_vecGradientPairingDensity_le hd Q hF J hg)

/-! ## The centred shell flux -/

theorem continuous_shellValue (omega : ShellSeq d) (k : ℕ) :
    Continuous (fun x : Vec d => (omega k) x) := (omega k).1.1.continuous

theorem continuous_shellFlux' (omega : ShellSeq d) (k : ℕ) (p : Vec d) :
    Continuous (shellFlux omega k p) := by
  refine continuous_pi fun i => ?_
  have h : Continuous (fun x : Vec d => ∑ j : Fin d, (omega k) x i j * p j) :=
    continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp
        ((continuous_apply i).comp (continuous_shellValue omega k))).mul continuous_const
  exact h

/-- The cube average of a matrix field applied to a fixed direction. -/
theorem volumeAverageVec_matVecMul (R : TriadicCube d) {M : Vec d → Mat d}
    (hM : Continuous M) (p : Vec d) :
    volumeAverageVec (cubeSet R) (fun x => matVecMul (M x) p) =
      matVecMul (volumeAverageMat (cubeSet R) M) p := by
  funext i
  have hcont : ∀ j : Fin d, Continuous (fun x : Vec d => M x i j * p j) := fun j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hM)).mul continuous_const
  have hstep : volumeAverage (cubeSet R) (fun x => ∑ j : Fin d, M x i j * p j) =
      ∑ j : Fin d, volumeAverage (cubeSet R) (fun x => M x i j * p j) :=
    volumeAverage_cubeSet_finset_sum R (fun j x => M x i j * p j) hcont
  show volumeAverage (cubeSet R) (fun x => ∑ j : Fin d, M x i j * p j) =
    ∑ j : Fin d, volumeAverage (cubeSet R) (fun x => M x i j) * p j
  rw [hstep]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun x : Vec d => M x i j * p j) = fun x : Vec d => p j * M x i j from
    funext fun x => mul_comm _ _,
    SuperdiffusionCLT.Section2.Norms.volumeAverage_const_mul, mul_comm]

/-- **The depth moment of a shell flux** is the direction length times the
matrix depth moment of `MultiscalePoincare`. -/
theorem vecDepthMoment_shellFlux_le (Q : TriadicCube d) (j : ℕ)
    (omega : ShellSeq d) (k : ℕ) (p : Vec d) :
    vecDepthMoment Q j (shellFlux omega k p) ≤
      vecNorm p *
        cubeDepthPthMoment Q j 2 (fun x => (omega k) x) ^ (2 : ℝ)⁻¹ := by
  have hM : Continuous (fun x : Vec d => (omega k) x) := continuous_shellValue omega k
  have hpt : ∀ R : TriadicCube d,
      vecNormSq (volumeAverageVec (cubeSet R) (shellFlux omega k p)) ≤
        vecNorm p ^ 2 *
          ‖volumeAverageMat (cubeSet R) (fun x => (omega k) x)‖ ^ (2 : ℝ) := by
    intro R
    have hav : volumeAverageVec (cubeSet R) (shellFlux omega k p) =
        matVecMul (volumeAverageMat (cubeSet R) (fun x => (omega k) x)) p := by
      rw [show shellFlux omega k p =
          fun x => matVecMul ((fun y => (omega k) y) x) p from rfl]
      exact volumeAverageVec_matVecMul R hM p
    have hop := vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
      (volumeAverageMat (cubeSet R) (fun x => (omega k) x)) p
    have hsq := mul_self_le_mul_self (vecNorm_nonneg _) hop
    rw [hav, ← Book.Ch02.vecNorm_sq_eq_vecNormSq, pow_two]
    refine le_trans hsq (le_of_eq ?_)
    rw [Real.rpow_two, matrixOperatorNorm_eq_l2_opNorm]
    ring
  have hbase : vecDepthSqMoment Q j (shellFlux omega k p) ≤
      vecNorm p ^ 2 * cubeDepthPthMoment Q j 2 (fun x => (omega k) x) := by
    rw [vecDepthSqMoment,
      show cubeDepthPthMoment Q j 2 (fun x => (omega k) x) =
        descendantsAverage Q j (fun R =>
          ‖volumeAverageMat (cubeSet R) (fun x => (omega k) x)‖ ^ (2 : ℝ)) from rfl,
      ← descendantsAverage_mul_left]
    exact descendantsAverage_le_descendantsAverage Q j fun R _ => hpt R
  have hmom : 0 ≤ cubeDepthPthMoment Q j 2 (fun x => (omega k) x) :=
    cubeDepthPthMoment_nonneg Q j 2 _
  rw [vecDepthMoment]
  have hroot : Real.sqrt (vecNorm p ^ 2 *
      cubeDepthPthMoment Q j 2 (fun x => (omega k) x)) =
      vecNorm p * cubeDepthPthMoment Q j 2 (fun x => (omega k) x) ^ (2 : ℝ)⁻¹ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (vecNorm_nonneg p),
      Real.sqrt_eq_rpow]
    norm_num
  rw [← hroot]
  exact Real.sqrt_le_sqrt hbase

/-- **The `L̲²` size of a shell flux on the large cube**, through the
value envelope. -/
theorem sqrt_vecSqAvg_shellFlux_le (omega : ShellSeq d) {k l : ℕ} (hkl : k ≤ l)
    (p : Vec d) :
    Real.sqrt (vecSqAvg (originCube d (l : ℤ)) (shellFlux omega k p)) ≤
      vecNorm p * shellValueLargeCubeSupBound k l omega := by
  set B : ℝ := shellValueLargeCubeSupBound k l omega with hB
  have hBnn : 0 ≤ B := shellValueLargeCubeSupBound_nonneg k l omega
  have hpt : ∀ x ∈ cubeSet (originCube d (l : ℤ)),
      ‖hilbertifyVecField (shellFlux omega k p) x‖ ^ 2 ≤ (vecNorm p * B) ^ 2 := by
    intro x hx
    have hop := vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
      ((omega k) x) p
    have hval := matrixOperatorNorm_shellValue_le_shellValueLargeCubeSupBound
      omega hkl hx
    have hle : vecNorm (shellFlux omega k p x) ≤ vecNorm p * B := by
      refine le_trans hop ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hval (vecNorm_nonneg p)
    have h0 : 0 ≤ vecNorm (shellFlux omega k p x) := vecNorm_nonneg _
    exact pow_le_pow_left₀ h0 hle 2
  have hmono : vecSqAvg (originCube d (l : ℤ)) (shellFlux omega k p) ≤
      (vecNorm p * B) ^ 2 := by
    have hvol : (0 : ℝ) < (volume (cubeSet (originCube d (l : ℤ)))).toReal :=
      volume_cubeSet_toReal_pos _
    rw [vecSqAvg, cubeSquareAverage, volumeAverage]
    rw [inv_mul_le_iff₀ hvol]
    have hint : IntegrableOn
        (fun x : Vec d => ‖hilbertifyVecField (shellFlux omega k p) x‖ ^ 2)
        (cubeSet (originCube d (l : ℤ))) volume :=
      integrableOn_cubeSet_of_continuous _
        ((continuous_hilbertifyVecField (continuous_shellFlux' omega k p)).norm.pow 2)
    have hconst : IntegrableOn (fun _ : Vec d => (vecNorm p * B) ^ 2)
        (cubeSet (originCube d (l : ℤ))) volume :=
      integrableOn_const (volume_cubeSet_lt_top _).ne
    have hle := setIntegral_mono_on hint hconst
      (measurableSet_cubeSet (originCube d (l : ℤ))) hpt
    rw [setIntegral_const, measureReal_def, smul_eq_mul] at hle
    linarith only [hle]
  calc Real.sqrt (vecSqAvg (originCube d (l : ℤ)) (shellFlux omega k p))
      ≤ Real.sqrt ((vecNorm p * B) ^ 2) := Real.sqrt_le_sqrt hmono
    _ = vecNorm p * B := Real.sqrt_sq (mul_nonneg (vecNorm_nonneg p) hBnn)

/-! ## The deterministic endpoint bound for one shell -/

/-- The envelope of `e.jk.Hminus.endpoint` in the order-one carrier: the
multiscale depth sum of the shell down to the shell scale, its `L̲²`
truncation remainder, and the centring constant. -/
def shellHminusBound (k l : ℕ) (p : Vec d) (omega : ShellSeq d) : ℝ :=
  multiscaleOrderOneConst d * (vecNorm p *
      ((∑ j ∈ Finset.range (l - k + 1), ((3 : ℝ) ^ j)⁻¹ *
          cubeDepthPthMoment (originCube d (l : ℤ)) j 2
            (fun x => (omega k) x) ^ (2 : ℝ)⁻¹) +
        ((3 : ℝ) ^ (l - k))⁻¹ * shellValueLargeCubeSupBound k l omega)) +
    vecNorm (shellFluxAverage (l : ℤ) omega k p)

theorem shellHminusBound_nonneg (k l : ℕ) (p : Vec d) (omega : ShellSeq d) :
    0 ≤ shellHminusBound k l p omega := by
  have hc : (0 : ℝ) ≤ multiscaleOrderOneConst d :=
    le_trans zero_le_one (one_le_multiscaleOrderOneConst d)
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (l - k + 1), ((3 : ℝ) ^ j)⁻¹ *
      cubeDepthPthMoment (originCube d (l : ℤ)) j 2 (fun x => (omega k) x) ^ (2 : ℝ)⁻¹ :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
      (Real.rpow_nonneg (cubeDepthPthMoment_nonneg _ j 2 _) _)
  have hsup : (0 : ℝ) ≤ ((3 : ℝ) ^ (l - k))⁻¹ * shellValueLargeCubeSupBound k l omega :=
    mul_nonneg (by positivity) (shellValueLargeCubeSupBound_nonneg k l omega)
  have hbr : (0 : ℝ) ≤ vecNorm p * ((∑ j ∈ Finset.range (l - k + 1),
      ((3 : ℝ) ^ j)⁻¹ * cubeDepthPthMoment (originCube d (l : ℤ)) j 2
        (fun x => (omega k) x) ^ (2 : ℝ)⁻¹) +
      ((3 : ℝ) ^ (l - k))⁻¹ * shellValueLargeCubeSupBound k l omega) := by
    refine mul_nonneg (vecNorm_nonneg p) ?_
    linarith only [hsum, hsup]
  have hlast : (0 : ℝ) ≤ vecNorm (shellFluxAverage (l : ℤ) omega k p) :=
    vecNorm_nonneg _
  rw [shellHminusBound]
  have := mul_nonneg hc hbr
  linarith only [this, hlast]

/-- **`e.jk.Hminus.endpoint`, deterministic half, in the order-one carrier.**
For `k ≤ l` the order-one hatted negative norm of the centred shell flux on
`cu_l` is at most the envelope `shellHminusBound`. -/
theorem vecHatNegENormOrderOne_centeredShellFlux_le (hd : 0 < d) (omega : ShellSeq d)
    {k l : ℕ} (hkl : k ≤ l) (p : Vec d) :
    vecHatNegENormOrderOne (originCube d (l : ℤ))
        (fun x => shellFlux omega k p x -
          volumeAverageVec (cubeSet (originCube d (l : ℤ)))
            (shellFlux omega k p)) ≤
      ENNReal.ofReal (shellHminusBound k l p omega) := by
  set Q : TriadicCube d := originCube d (l : ℤ) with hQ
  have hFc : Continuous (shellFlux omega k p) := continuous_shellFlux' omega k p
  have hc : (0 : ℝ) ≤ multiscaleOrderOneConst d :=
    le_trans zero_le_one (one_le_multiscaleOrderOneConst d)
  have hbrnn : (0 : ℝ) ≤ (∑ j ∈ Finset.range (l - k + 1), ((3 : ℝ) ^ j)⁻¹ *
        vecDepthMoment Q j (shellFlux omega k p)) +
      ((3 : ℝ) ^ (l - k))⁻¹ * Real.sqrt (vecSqAvg Q (shellFlux omega k p)) := by
    have h1 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (l - k + 1), ((3 : ℝ) ^ j)⁻¹ *
        vecDepthMoment Q j (shellFlux omega k p) :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (by positivity) (vecDepthMoment_nonneg Q j _)
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (l - k))⁻¹ *
        Real.sqrt (vecSqAvg Q (shellFlux omega k p)) :=
      mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    linarith only [h1, h2]
  refine le_trans (vecHatNegENormOrderOne_sub_const_le Q hFc _) ?_
  refine le_trans (add_le_add (vecHatNegENormOrderOne_le_depthSum hd Q hFc (l - k))
    (le_refl (ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q)
      (shellFlux omega k p)))))) ?_
  rw [← ENNReal.ofReal_add (mul_nonneg hc hbrnn) (vecNorm_nonneg _),
    volumeAverageVec_shellFlux (l : ℤ) k omega p]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [shellHminusBound]
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ hc) le_rfl
  rw [mul_add, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) ?_
  · have hj := vecDepthMoment_shellFlux_le Q j omega k p
    calc ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j (shellFlux omega k p)
        ≤ ((3 : ℝ) ^ j)⁻¹ * (vecNorm p *
            cubeDepthPthMoment Q j 2 (fun x => (omega k) x) ^ (2 : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hj (by positivity)
      _ = vecNorm p * (((3 : ℝ) ^ j)⁻¹ *
            cubeDepthPthMoment Q j 2 (fun x => (omega k) x) ^ (2 : ℝ)⁻¹) := by ring
  · have hsup := sqrt_vecSqAvg_shellFlux_le omega hkl p
    calc ((3 : ℝ) ^ (l - k))⁻¹ * Real.sqrt (vecSqAvg Q (shellFlux omega k p))
        ≤ ((3 : ℝ) ^ (l - k))⁻¹ *
            (vecNorm p * shellValueLargeCubeSupBound k l omega) :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = vecNorm p * (((3 : ℝ) ^ (l - k))⁻¹ *
            shellValueLargeCubeSupBound k l omega) := by ring

/-! ## The `Γ₂` tail of the endpoint envelope -/

theorem measurable_shellHminusBound (k l : ℕ) (p : Vec d) :
    Measurable (shellHminusBound k l p : ShellSeq d → ℝ) := by
  classical
  refine Measurable.add (measurable_const.mul (measurable_const.mul
    (Measurable.add (Finset.measurable_sum _ fun j _ => ?_)
      (measurable_const.mul (measurable_shellValueLargeCubeSupBound k l)))))
    (measurable_vecNorm_shellFluxAverage (l : ℤ) k p)
  exact measurable_const.mul
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)).measurable.comp
      (measurable_cubeDepthPthMoment_shell (originCube d (l : ℤ)) j k (by norm_num)))

/-- The printed weight of the depth-`j` term is at most `3^{-(l-k)}` in every
dimension `d ≥ 2`. -/
theorem depthWeight_le (hd2 : 2 ≤ d) {k l j : ℕ} (hkl : k ≤ l)
    (hj : j ≤ l - k) :
    ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ (-((d : ℝ) / 2) *
        ((max ((l : ℤ) - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)) ≤
      (3 : ℝ) ^ (-(((l - k : ℕ)) : ℝ)) := by
  have hcast : ((max ((l : ℤ) - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ) =
      ((l - k : ℕ) : ℝ) - (j : ℝ) := by
    have hmax : max ((l : ℤ) - (j : ℤ) - (k : ℤ)) 0 = ((l - k : ℕ) : ℤ) - (j : ℤ) := by
      omega
    rw [hmax]
    push_cast
    ring
  have ht : (0 : ℝ) ≤ ((l - k : ℕ) : ℝ) - (j : ℝ) := by
    have : (j : ℝ) ≤ ((l - k : ℕ) : ℝ) := by exact_mod_cast hj
    linarith only [this]
  have h3 : ((3 : ℝ) ^ j)⁻¹ = (3 : ℝ) ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h3, hcast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hd2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hone : (1 : ℝ) ≤ (d : ℝ) / 2 := by linarith only [hd2']
  have hkey := mul_le_mul_of_nonneg_right hone ht
  rw [one_mul] at hkey
  linarith only [hkey]

/-- The dimension-only constant of the order-one endpoint amplitude. -/
def shellHminusConst (d : ℕ) : ℝ :=
  gammaTriangleConst 2 * (multiscaleOrderOneConst d * gammaTriangleConst 2 *
      (gammaTriangleConst 2 * cubeDepthMomentTailConst d 2 +
        shellValueLargeCubeConst d) + spatialAverageTailConst d)

/-- **`e.jk.Hminus.endpoint` in the order-one carrier.** -/
theorem isBigO_gammaSigma_shellHminusBound
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hd2 : 2 ≤ d) {k l : ℕ} (hkl : k ≤ l) {p : Vec d}
    (hp : 0 < vecNorm p) :
    IsBigO P.toMeasure (gammaSigma 2) (shellHminusBound k l p)
      (shellHminusConst d * vecNorm p *
        ((1 + ((l - k : ℕ) : ℝ)) * (3 : ℝ) ^ (-(((l - k : ℕ)) : ℝ)))) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  set J : ℕ := l - k with hJ
  set W : ℝ := (1 + (J : ℝ)) * (3 : ℝ) ^ (-((J : ℕ) : ℝ)) with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hCdm : 0 < cubeDepthMomentTailConst d 2 :=
    Section2.Norms.cubeDepthMomentTailConst_pos hd 2
  have hCsv : 0 < shellValueLargeCubeConst d := shellValueLargeCubeConst_pos_of_pos hd
  have hCav : 0 < spatialAverageTailConst d :=
    Section2.Norms.spatialAverageTailConst_pos hd
  have hCms : 0 < multiscaleOrderOneConst d :=
    lt_of_lt_of_le zero_lt_one (one_le_multiscaleOrderOneConst d)
  -- the depth sum
  set X1 : ShellSeq d → ℝ := fun omega => ∑ j ∈ Finset.range (J + 1),
    ((3 : ℝ) ^ j)⁻¹ * cubeDepthPthMoment (originCube d (l : ℤ)) j 2
      (fun x => (omega k) x) ^ (2 : ℝ)⁻¹ with hX1def
  have hmeas1 : ∀ j : ℕ, Measurable (fun omega : ShellSeq d =>
      ((3 : ℝ) ^ j)⁻¹ * cubeDepthPthMoment (originCube d (l : ℤ)) j 2
        (fun x => (omega k) x) ^ (2 : ℝ)⁻¹) := fun j =>
    measurable_const.mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)).measurable.comp
        (Section2.Norms.measurable_cubeDepthPthMoment_shell
          (originCube d (l : ℤ)) j k (by norm_num)))
  have hX1 : IsBigO P.toMeasure (gammaSigma 2) X1
      (gammaTriangleConst 2 * (cubeDepthMomentTailConst d 2 * W)) := by
    have hterm : ∀ j ∈ Finset.range (J + 1), IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => ((3 : ℝ) ^ j)⁻¹ *
          cubeDepthPthMoment (originCube d (l : ℤ)) j 2
            (fun x => (omega k) x) ^ (2 : ℝ)⁻¹)
        (((3 : ℝ) ^ j)⁻¹ * (cubeDepthMomentTailConst d 2 *
          (3 : ℝ) ^ (-((d : ℝ) / 2) *
            ((max ((originCube d (l : ℤ)).scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ)))) :=
      fun j _ => (Section2.Norms.isBigO_gammaSigma_rpow_cubeDepthPthMoment_shell
        hPrefix hJ1 hJ3 hJ4 k (originCube d (l : ℤ)) j (by norm_num)).const_mul
          (by positivity)
    have hsum := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := P.toMeasure) (Finset.range (J + 1)) (by norm_num : (0 : ℝ) < 2)
      ⟨0, Finset.mem_range.2 (Nat.succ_pos J)⟩
      (fun j _ => by positivity) hterm (fun j _ => hmeas1 j)
    refine hsum.mono_scale ?_
    refine mul_le_mul_of_nonneg_left ?_ htri.le
    have hstep : ∀ j ∈ Finset.range (J + 1),
        ((3 : ℝ) ^ j)⁻¹ * (cubeDepthMomentTailConst d 2 *
          (3 : ℝ) ^ (-((d : ℝ) / 2) *
            ((max ((originCube d (l : ℤ)).scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ))) ≤
          cubeDepthMomentTailConst d 2 * (3 : ℝ) ^ (-((J : ℕ) : ℝ)) := by
      intro j hj
      have hjle : j ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hw := depthWeight_le hd2 hkl hjle
      have hrw : ((3 : ℝ) ^ j)⁻¹ * (cubeDepthMomentTailConst d 2 *
          (3 : ℝ) ^ (-((d : ℝ) / 2) *
            ((max ((l : ℤ) - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ))) =
          cubeDepthMomentTailConst d 2 * (((3 : ℝ) ^ j)⁻¹ *
            (3 : ℝ) ^ (-((d : ℝ) / 2) *
              ((max ((l : ℤ) - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ))) := by ring
      rw [show ((originCube d (l : ℤ)).scale : ℤ) = (l : ℤ) from rfl, hrw]
      exact mul_le_mul_of_nonneg_left hw hCdm.le
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hW]
    push_cast
    ring
  -- the truncation remainder
  set X2 : ShellSeq d → ℝ := fun omega =>
    ((3 : ℝ) ^ J)⁻¹ * shellValueLargeCubeSupBound k l omega with hX2def
  have hX2 : IsBigO P.toMeasure (gammaSigma 2) X2
      (shellValueLargeCubeConst d * W) := by
    have hbase : IsBigO P.toMeasure (gammaSigma 2)
        (shellValueLargeCubeSupBound k l)
        (shellValueLargeCubeConst d * Real.sqrt (1 + ((l - k : ℕ) : ℝ))) :=
      (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (fun omega => shellValueLargeCubeSupBound_nonneg k l omega)).1
        (isBigOWith_gammaSigma_shellValueLargeCubeSupBound hPrefix hJ3 hkl)
    refine (hbase.const_mul (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ J)⁻¹)).mono_scale ?_
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have h1 : (1 : ℝ) ≤ 1 + (J : ℝ) := by linarith only [hJ0]
    have hsq : Real.sqrt (1 + (J : ℝ)) ≤ 1 + (J : ℝ) := by
      have hsq2 : 1 + (J : ℝ) ≤ (1 + (J : ℝ)) ^ 2 := by
        rw [pow_two]
        exact le_mul_of_one_le_left (by linarith only [h1]) h1
      calc Real.sqrt (1 + (J : ℝ)) ≤ Real.sqrt ((1 + (J : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt hsq2
        _ = 1 + (J : ℝ) := Real.sqrt_sq (by linarith only [h1])
    have hpow : ((3 : ℝ) ^ J)⁻¹ = (3 : ℝ) ^ (-((J : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [hW, hpow, ← hJ]
    have := mul_le_mul_of_nonneg_left hsq hCsv.le
    calc (3 : ℝ) ^ (-((J : ℕ) : ℝ)) *
          (shellValueLargeCubeConst d * Real.sqrt (1 + ((l - k : ℕ) : ℝ)))
        ≤ (3 : ℝ) ^ (-((J : ℕ) : ℝ)) *
            (shellValueLargeCubeConst d * (1 + (J : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hJ]
          exact this
      _ = shellValueLargeCubeConst d * ((1 + (J : ℝ)) *
            (3 : ℝ) ^ (-((J : ℕ) : ℝ))) := by ring
  -- the two halves of the multiscale envelope
  have hmeasX1 : Measurable X1 := Finset.measurable_sum _ fun j _ => hmeas1 j
  have hmeasX2 : Measurable X2 :=
    measurable_const.mul (measurable_shellValueLargeCubeSupBound k l)
  have hX12 := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (mu := P.toMeasure) (sigma := 2) (by norm_num)
    (by positivity : (0 : ℝ) < gammaTriangleConst 2 * (cubeDepthMomentTailConst d 2 * W))
    (by positivity : (0 : ℝ) < shellValueLargeCubeConst d * W)
    hX1 hX2 hmeasX1 hmeasX2
  have hscaled := hX12.const_mul
    (le_of_lt (mul_pos hCms hp) : (0 : ℝ) ≤ multiscaleOrderOneConst d * vecNorm p)
  have hZ := isBigO_gammaSigma_vecNorm_shellFluxAverage hPrefix hJ1 hJ3 hJ4 l k p
  have hfun : (shellHminusBound k l p : ShellSeq d → ℝ) =
      fun omega => (multiscaleOrderOneConst d * vecNorm p) * (X1 omega + X2 omega) +
        vecNorm (shellFluxAverage (l : ℤ) omega k p) := by
    funext omega
    rw [shellHminusBound, hX1def, hX2def]
    ring
  rw [hfun]
  have hfinal := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (mu := P.toMeasure) (sigma := 2) (by norm_num)
    (by positivity : (0 : ℝ) < multiscaleOrderOneConst d * vecNorm p *
      (gammaTriangleConst 2 * (gammaTriangleConst 2 * (cubeDepthMomentTailConst d 2 * W) +
        shellValueLargeCubeConst d * W)))
    (by positivity : (0 : ℝ) < spatialAverageTailConst d * vecNorm p *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - k : ℕ) : ℝ)))
    hscaled hZ (measurable_const.mul (hmeasX1.add hmeasX2))
    (measurable_vecNorm_shellFluxAverage (l : ℤ) k p)
  refine hfinal.mono_scale ?_
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hdecay : (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - k : ℕ) : ℝ)) ≤ W := by
    have hd2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hone : (1 : ℝ) ≤ (d : ℝ) / 2 := by linarith only [hd2']
    have hkey := mul_le_mul_of_nonneg_right hone hJ0
    rw [one_mul] at hkey
    have hstep : (3 : ℝ) ^ (-((d : ℝ) / 2) * (J : ℝ)) ≤ (3 : ℝ) ^ (-((J : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hkey])
    have hlast : (3 : ℝ) ^ (-((J : ℕ) : ℝ)) ≤ W := by
      rw [hW]
      exact le_mul_of_one_le_left (by positivity) (by linarith only [hJ0])
    exact le_trans hstep hlast
  have hle : spatialAverageTailConst d * vecNorm p *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - k : ℕ) : ℝ)) ≤
      spatialAverageTailConst d * vecNorm p * W :=
    mul_le_mul_of_nonneg_left hdecay (by positivity)
  calc gammaTriangleConst 2 * (multiscaleOrderOneConst d * vecNorm p *
        (gammaTriangleConst 2 * (gammaTriangleConst 2 *
          (cubeDepthMomentTailConst d 2 * W) + shellValueLargeCubeConst d * W)) +
        spatialAverageTailConst d * vecNorm p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - k : ℕ) : ℝ)))
      ≤ gammaTriangleConst 2 * (multiscaleOrderOneConst d * vecNorm p *
          (gammaTriangleConst 2 * (gammaTriangleConst 2 *
            (cubeDepthMomentTailConst d 2 * W) + shellValueLargeCubeConst d * W)) +
          spatialAverageTailConst d * vecNorm p * W) := by
        refine mul_le_mul_of_nonneg_left ?_ htri.le
        linarith only [hle]
    _ = shellHminusConst d * vecNorm p * W := by
        rw [shellHminusConst]
        ring

end

end SuperdiffusionCLT.Section2.Estimates.Stream
