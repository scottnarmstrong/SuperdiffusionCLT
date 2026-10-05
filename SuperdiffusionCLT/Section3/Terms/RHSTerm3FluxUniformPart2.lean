/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart0
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart1
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscSeminormClose
public import SuperdiffusionCLT.Section3.Terms.EnergyMapsNonsymm
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlockCentering
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart2B
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The pointwise flux estimate in the term-3 chain

This file proves the pointwise clause of `hGap` at the fixed Part 0 block
weight.  The generic centered multiscale Poincare estimate is supplied by
`fluxMsp_main` of Part 1; energy is compared cube by cube through the Chapter 2
flux estimate and the local maximizers underlying the glued fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Filter
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- The pointwise square of an averaged flux is controlled by the coarse block
and the energy whenever a local solution has the stated gradient. -/
theorem fluxPointwise_localFluxEnergy [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : ShellSeq d) (uMgrad uNGlued : Vec d → Vec d)
    (Q : TriadicCube d) {C : ℝ}
    (hentry : ∀ x ∈ openCubeSet Q, ∀ i j,
      |(coefficientCutoff nu omega S.LPrime).toCoeffField x i j| ≤ C)
    (w : Book.Ch02.Solution (Book.Ch02.cubeDomain Q)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain Q) hnu omega S.LPrime hentry))
    (hgrad : w.toH1.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun y => uMgrad y - uNGlued y)) :
    vecNormSq (volumeAverageVec (openCubeSet Q)
      (fluxFieldCarrier nu S omega uMgrad uNGlued)) ≤
      translatedBlockNorm nu S.LPrime omega Q *
        volumeAverage (openCubeSet Q) (fun y => nu * vecNormSq (uMgrad y - uNGlued y)) := by
  let a := coefficientCutoffCoeffOn (Book.Ch02.cubeDomain Q) hnu omega S.LPrime hentry
  have hfl : fluxFieldCarrier nu S omega uMgrad uNGlued =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => matVecMul (a.toCoeffField x) (w.toH1.grad x)) := by
    refine hgrad.mono fun x hx => ?_
    simp only [fluxFieldCarrier, hx]
    rfl
  have havg : volumeAverageVec (openCubeSet Q)
      (fluxFieldCarrier nu S omega uMgrad uNGlued) = Book.Ch02.averageFlux
        (Book.Ch02.cubeDomain Q) a w := by
    funext i
    exact volumeAverage_congr_ae (hfl.mono fun x hx => congrArg (fun v : Vec d => v i) hx)
  have henergy : Book.Ch02.variationEnergyValue (Book.Ch02.cubeDomain Q) a w =
      volumeAverage (openCubeSet Q) (fun y => nu * vecNormSq (uMgrad y - uNGlued y)) := by
    show volumeAverage (openCubeSet Q)
        (fun x => vecDot (w.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (w.toH1.grad x))) = _
    refine volumeAverage_congr_ae (hgrad.mono fun y hy => ?_)
    beta_reduce
    rw [hy]
    exact vecDot_symmPart_eq_mul_vecNormSq (by
      show symmPart ((coefficientCutoff nu omega S.LPrime).toCoeffField y) = nu • 1
      exact symmPart_coefficientCutoff nu omega S.LPrime y) _
  have hbook := Book.Ch02.vecNormSq_averageFlux_le_matrixNorm_bCoarse_mul_variationEnergyValue
    (Book.Ch02.cubeDomain Q) a w
  have hblock := translatedCoarseBlock_eq_bCoarse hnu S.LPrime omega Q hentry
  calc
    vecNormSq (volumeAverageVec (openCubeSet Q)
        (fluxFieldCarrier nu S omega uMgrad uNGlued)) =
        vecNormSq (Book.Ch02.averageFlux (Book.Ch02.cubeDomain Q) a w) := by rw [havg]
    _ ≤ Book.Ch02.matrixNorm (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) a) *
        Book.Ch02.variationEnergyValue (Book.Ch02.cubeDomain Q) a w := hbook
    _ = translatedBlockNorm nu S.LPrime omega Q *
        volumeAverage (openCubeSet Q) (fun y => nu * vecNormSq (uMgrad y - uNGlued y)) := by
          rw [henergy, ← hblock, translatedBlockNorm, Book.Ch02.matrixNorm_eq_matrixOperatorNorm]

/-- The local energy estimate on an arbitrary descendant of a selected cube.
The two glued gradients restrict to the root maximizer and to the maximizer on
the selected cube, so their difference is harmonic on every smaller cube. -/
theorem fluxPointwise_childFluxEnergy [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (omega : ShellSeq d) {R Q : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d S.n S.m) {j : ℕ}
    (hQ : Q ∈ descendantsAtDepth R j) :
    vecNormSq (volumeAverageVec (openCubeSet Q)
        (fluxFieldCarrier nu S omega
          (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega)
          (gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega))) ≤
      translatedBlockNorm nu S.LPrime omega Q *
        volumeAverage (openCubeSet Q) (fun y => nu * vecNormSq
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y)) := by
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  let root := originCube d (S.m : ℤ)
  have hRroot : R ∈ descendantsAtDepth root (S.m - S.n) := by
    rw [← largeCubeSubcubes_eq_descendantsAtDepth]
    exact hR
  have hQroot : Q ∈ descendantsAtDepth root ((S.m - S.n) + j) :=
    mem_descendantsAtDepth_trans hRroot hQ
  have hroot : root ∈ largeCubeSubcubes d S.m S.m := by
    rw [largeCubeSubcubes_self]
    exact Finset.mem_singleton_self _
  obtain ⟨lamM, LamM, hEllM⟩ :=
    exists_isEllipticFieldOn_coefficientCutoff_openCubeSet hnu omega S.LPrime root
  obtain ⟨lamR, LamR, hEllR⟩ :=
    exists_isEllipticFieldOn_coefficientCutoff_openCubeSet hnu omega S.LPrime R
  obtain ⟨C, hC⟩ := exists_entryBound_coefficientCutoff nu omega S.LPrime Q
  have hentry : ∀ x ∈ openCubeSet Q, ∀ i k,
      |(coefficientCutoff nu omega S.LPrime).toCoeffField x i k| ≤ C :=
    fun x hx i k => hC x (openCubeSet_subset_cubeSet Q hx) i k
  set w : Book.Ch02.Solution (Book.Ch02.cubeDomain Q)
      (coefficientCutoffCoeffOn (Book.Ch02.cubeDomain Q) hnu omega S.LPrime hentry) :=
    subSolution
      (Homogenization.AHarmonicFunction.restrictToOpenSubcube
        (cubeMaximizer hnu omega S.LPrime
          (fluxSlot nu S.LPrime P S.n e) root).toSolution hEllM hQroot)
      (Homogenization.AHarmonicFunction.restrictToOpenSubcube
        (cubeMaximizer hnu omega S.LPrime
          (fluxSlot nu S.LPrime P S.n e) R).toSolution hEllR hQ) with hwdef
  have hgrad : w.toH1.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun y => gluedGradientField hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e) omega y -
        gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega y) := by
    rw [hwdef]
    erw [subSolution_toH1]
    rw [H1Function.sub_grad]
    refine (MeasureTheory.ae_restrict_iff' (measurableSet_openCubeSet Q)).2
      (Filter.Eventually.of_forall fun y hy => ?_)
    have hyRoot : y ∈ cubeSet root :=
      (cubeSet_subset_of_mem_descendantsAtDepth hQroot)
        (openCubeSet_subset_cubeSet Q hy)
    have hyR : y ∈ cubeSet R :=
      (cubeSet_subset_of_mem_descendantsAtDepth hQ)
        (openCubeSet_subset_cubeSet Q hy)
    change cubeMaximizerGradient hnu omega S.LPrime
        (fluxSlot nu S.LPrime P S.n e) root y -
      cubeMaximizerGradient hnu omega S.LPrime
        (fluxSlot nu S.LPrime P S.n e) R y =
      gluedGradientField hnu S.LPrime S.m S.m
        (fluxSlot nu S.LPrime P S.n e) omega y -
      gluedGradientField hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega y
    rw [gluedGradientField_apply_of_mem_cubeSet hnu S.LPrime S.m S.m
        (fluxSlot nu S.LPrime P S.n e) omega hroot hyRoot,
      gluedGradientField_apply_of_mem_cubeSet hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega hR hyR]
  exact fluxPointwise_localFluxEnergy hnu S omega
    (gluedGradientField hnu S.LPrime S.m S.m
      (fluxSlot nu S.LPrime P S.n e) omega)
    (gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega) Q
    hentry w hgrad

/-- Averaging the cube energy bound across a depth gives the block maximum
times the parent energy. -/
theorem fluxPointwise_depthMoment_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) (j : ℕ) :
    vecDepthMoment R (j + 1)
      (fluxFieldCarrier nu S omega
          (oscGluedGradM nu hnu S P e omega)
          (oscGluedGradN nu hnu S P e omega)) ≤
      Real.sqrt ((fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
        oscEnergy nu hnu S P e omega R) := by
  let uM := oscGluedGradM nu hnu S P e omega
  let uN := oscGluedGradN nu hnu S P e omega
  let G : Vec d → Vec d := fun x => uM x - uN x
  let F : Vec d → Vec d := fluxFieldCarrier nu S omega uM uN
  have hG : MemVectorL2 (openCubeSet R) G := by
    dsimp [G, uM, uN]
    exact (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
      (fluxSlot nu S.LPrime P S.n e) omega R).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega R)
  have hF : MemVectorL2 (openCubeSet R) F := by
    dsimp [F, uM, uN]
    exact fluxMsp_memVectorL2_fluxFieldCarrier_gluedDiff hnu S omega
      S.LPrime S.LPrime S.m S.n S.m (fluxSlot nu S.LPrime P S.n e) R
  have hAvg : vecSqAvg R G = descendantsAverage R (j + 1)
      (fun Q => vecSqAvg Q G) := by
    unfold G
    exact vecSqAvg_eq_descendantsAverage_memLp R (j + 1)
      (memLp_hilbertifyVecField_of_memVectorL2 hG)
  have hsq : ∀ Q : TriadicCube d,
      vecSqAvg Q G = volumeAverage (cubeSet Q) (fun x => vecNormSq (G x)) := by
    intro Q
    unfold vecSqAvg cubeSquareAverage
    have hpt : (fun x : Vec d => ‖hilbertifyVecField G x‖ ^ 2) =
        fun x => vecNormSq (G x) := by
      funext x
      rw [norm_hilbertifyVecField_apply,
        Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]
    rw [hpt]
  have hEnergyAvg : ∀ Q : TriadicCube d,
      volumeAverage (openCubeSet Q) (fun x => nu * vecNormSq (G x)) =
        nu * vecSqAvg Q G := by
    intro Q
    calc volumeAverage (openCubeSet Q) (fun x => nu * vecNormSq (G x))
        = nu * volumeAverage (openCubeSet Q) (fun x => vecNormSq (G x)) :=
          SuperdiffusionCLT.Section2.Norms.volumeAverage_const_mul _ _ _
      _ = nu * volumeAverage (cubeSet Q) (fun x => vecNormSq (G x)) := by
          rw [← SuperdiffusionCLT.Section3.ResponseFields.volumeAverage_cubeSet_eq_openCubeSet Q]
      _ = nu * vecSqAvg Q G := by rw [← hsq Q]
  have hMoment : vecDepthSqMoment R (j + 1) F ≤
      (fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
        (nu * vecSqAvg R G) := by
    unfold vecDepthSqMoment F
    calc descendantsAverage R (j + 1)
          (fun Q => vecNormSq (volumeAverageVec (cubeSet Q)
            (fluxFieldCarrier nu S omega uM uN)))
        ≤ descendantsAverage R (j + 1)
            (fun Q => (fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
              (nu * vecSqAvg Q G)) := by
                apply descendantsAverage_le_descendantsAverage
                intro Q hQ
                have hlocal := fluxPointwise_childFluxEnergy hnu S hSorder P e omega hR hQ
                have havg : volumeAverageVec (cubeSet Q)
                    (fluxFieldCarrier nu S omega uM uN) =
                    volumeAverageVec (openCubeSet Q)
                      (fluxFieldCarrier nu S omega uM uN) :=
                  volumeAverageVec_cubeSet_eq_openCubeSet Q _
                rw [havg]
                have hblock := translatedBlockNorm_le_fluxUniformBlockMax
                  nu S.LPrime omega R hQ
                have hlocal' : vecNormSq (volumeAverageVec (openCubeSet Q)
                    (fluxFieldCarrier nu S omega uM uN)) ≤
                    translatedBlockNorm nu S.LPrime omega Q *
                      volumeAverage (openCubeSet Q)
                        (fun x => nu * vecNormSq (G x)) := by
                  simp only [G, uM, uN, oscGluedGradM, oscGluedGradN] at hlocal ⊢
                  exact hlocal
                have hE0 : 0 ≤ nu * vecSqAvg Q G :=
                  mul_nonneg hnu.le (vecSqAvg_nonneg Q G)
                calc vecNormSq (volumeAverageVec (openCubeSet Q)
                      (fluxFieldCarrier nu S omega uM uN)) ≤
                    translatedBlockNorm nu S.LPrime omega Q *
                      volumeAverage (openCubeSet Q)
                        (fun x => nu * vecNormSq (G x)) := hlocal'
                  _ = translatedBlockNorm nu S.LPrime omega Q *
                      (nu * vecSqAvg Q G) := by rw [hEnergyAvg Q]
                  _ ≤ (fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
                      (nu * vecSqAvg Q G) := mul_le_mul_of_nonneg_right hblock hE0
      _ = (fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
          (nu * vecSqAvg R G) := by
            rw [show (fun Q => (fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
                (nu * vecSqAvg Q G)) =
                (fun Q => ((fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) * nu) *
                  vecSqAvg Q G) by funext Q; ring,
              Homogenization.descendantsAverage_mul_left, ← hAvg]
            ring
  have hMoment' : vecDepthSqMoment R (j + 1) F ≤
      (fluxUniformBlockMax nu S.LPrime omega R (j + 1) : ℝ) *
        oscEnergy nu hnu S P e omega R := by
    rw [show oscEnergy nu hnu S P e omega R = nu * vecSqAvg R G by
      unfold oscEnergy energyL2Carrier G uM uN oscGluedGradM oscGluedGradN
      rfl]
    exact hMoment
  rw [vecDepthMoment]
  exact Real.sqrt_le_sqrt hMoment'

/-- Countable weighted Jensen at the geometric weights used by the centred
multiscale Poincare estimate. -/
theorem fluxPointwise_weightedTsumJensen {x : ℕ → ℝ} {B : ℝ}
    (hx : ∀ k, 0 ≤ x k) (hxB : ∀ k, x k ≤ B) :
    (∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k * x k) ^ ((3 : ℝ) / 2) ≤
      Real.sqrt ((3 : ℝ) / 2) *
        ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k * x k ^ ((3 : ℝ) / 2) := by
  let w : ℕ → ℝ := fun k => ((3 : ℝ)⁻¹) ^ k
  let g : ℕ → ℝ := fun k => w k * x k
  let q : ℕ → ℝ := fun k => w k * x k ^ ((3 : ℝ) / 2)
  have hw : ∀ k, 0 ≤ w k := fun k => pow_nonneg (by norm_num) _
  have hgeom : Summable w := by
    dsimp [w]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg (hw k) (hx k)
  have hq0 : ∀ k, 0 ≤ q k := fun k => mul_nonneg (hw k)
    (Real.rpow_nonneg (hx k) _)
  have hgdom : ∀ k, g k ≤ B * w k := by
    intro k
    dsimp [g]
    calc w k * x k ≤ w k * B := mul_le_mul_of_nonneg_left (hxB k) (hw k)
      _ = B * w k := mul_comm _ _
  have hqdom : ∀ k, q k ≤ B ^ ((3 : ℝ) / 2) * w k := by
    intro k
    have hp := Real.rpow_le_rpow (hx k) (hxB k) (by norm_num : 0 ≤ (3 : ℝ) / 2)
    dsimp [q]
    calc w k * x k ^ ((3 : ℝ) / 2) ≤ w k * B ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hp (hw k)
      _ = B ^ ((3 : ℝ) / 2) * w k := mul_comm _ _
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le hg0 hgdom
    simpa only [mul_comm] using Summable.mul_left B hgeom
  have hq : Summable q := by
    apply Summable.of_nonneg_of_le hq0 hqdom
    simpa only [mul_comm] using
      Summable.mul_left (B ^ ((3 : ℝ) / 2)) hgeom
  have hwSum : (∑' k : ℕ, w k) = (3 : ℝ) / 2 := by
    dsimp [w]
    exact tsum_inv_three_pow_eq_three_halves
  have hpartialG : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), g k) atTop
      (nhds (∑' k : ℕ, g k)) := by
    exact hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hpartialQ : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), q k) atTop
      (nhds (∑' k : ℕ, q k)) := by
    exact hq.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have htotalG0 : 0 ≤ ∑' k : ℕ, g k := tsum_nonneg hg0
  have hlimit : Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range (N + 1), g k) ^ ((3 : ℝ) / 2)) atTop
      (nhds ((∑' k : ℕ, g k) ^ ((3 : ℝ) / 2))) := by
    exact (Real.continuousAt_rpow_const _ _
      (Or.inr (by norm_num : 0 ≤ (3 : ℝ) / 2))).tendsto.comp hpartialG
  apply le_of_tendsto_of_tendsto' hlimit tendsto_const_nhds
  intro N
  have hWpos : 0 < ∑ k ∈ Finset.range (N + 1), w k := by
    have hfirst : w 0 ≤ ∑ k ∈ Finset.range (N + 1), w k := by
      apply Finset.single_le_sum (fun k hk => hw k)
      exact Finset.mem_range.mpr (Nat.zero_lt_succ N)
    rw [show w 0 = 1 by simp [w]] at hfirst
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hfirst
  have hJ := weighted_rpow_three_halves_le (Finset.range (N + 1)) w x
    (fun k _ => hw k) hWpos (fun k _ => hx k)
  have hWle : ∑ k ∈ Finset.range (N + 1), w k ≤ (3 : ℝ) / 2 := by
    rw [← hwSum]
    exact hgeom.sum_le_tsum (Finset.range (N + 1)) (fun k _ => hw k)
  have hQle : (∑ k ∈ Finset.range (N + 1), q k) ≤ ∑' k : ℕ, q k :=
    hq.sum_le_tsum (Finset.range (N + 1)) (fun k _ => hq0 k)
  have hBound : (∑ k ∈ Finset.range (N + 1), g k) ^ ((3 : ℝ) / 2) ≤
      Real.sqrt ((3 : ℝ) / 2) * ∑' k : ℕ, q k := by
    calc (∑ k ∈ Finset.range (N + 1), g k) ^ ((3 : ℝ) / 2)
        ≤ (∑ k ∈ Finset.range (N + 1), w k) ^ ((1 : ℝ) / 2) *
            ∑ k ∈ Finset.range (N + 1), q k := by
              simpa only [g, q] using hJ
      _ = Real.sqrt (∑ k ∈ Finset.range (N + 1), w k) *
          ∑ k ∈ Finset.range (N + 1), q k := by rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt ((3 : ℝ) / 2) *
          ∑ k ∈ Finset.range (N + 1), q k :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hWle)
              (Finset.sum_nonneg fun k hk => hq0 k)
      _ ≤ Real.sqrt ((3 : ℝ) / 2) * ∑' k : ℕ, q k :=
            mul_le_mul_of_nonneg_left hQle (Real.sqrt_nonneg _)
  exact hBound

/-- The power of each averaged flux is bounded by the corresponding powered
block maximum and the parent energy. -/
theorem fluxPointwise_depthMoment_rpow_le [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) (k : ℕ) :
    vecDepthMoment R (k + 1)
        (fluxFieldCarrier nu S omega
          (oscGluedGradM nu hnu S P e omega)
          (oscGluedGradN nu hnu S P e omega)) ^ ((3 : ℝ) / 2) ≤
      (fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) ^ ((3 : ℝ) / 4) *
        (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) := by
  have hdepth := fluxPointwise_depthMoment_le hnu S hSorder P e omega hR k
  have hmax : 0 ≤ (fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) :=
    NNReal.coe_nonneg _
  have henergy : 0 ≤ oscEnergy nu hnu S P e omega R := oscEnergy_nonneg hnu S P e omega R
  have hprod : 0 ≤ (fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) *
      oscEnergy nu hnu S P e omega R := mul_nonneg hmax henergy
  have hmoment : 0 ≤ vecDepthMoment R (k + 1)
      (fluxFieldCarrier nu S omega
        (oscGluedGradM nu hnu S P e omega)
        (oscGluedGradN nu hnu S P e omega)) :=
    vecDepthMoment_nonneg R (k + 1) _
  calc vecDepthMoment R (k + 1)
        (fluxFieldCarrier nu S omega
          (oscGluedGradM nu hnu S P e omega)
          (oscGluedGradN nu hnu S P e omega)) ^ ((3 : ℝ) / 2)
      ≤ (Real.sqrt ((fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) *
          oscEnergy nu hnu S P e omega R)) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hmoment hdepth (by norm_num)
    _ = ((fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) *
          oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) := by
            rw [Real.sqrt_eq_rpow,
              ← Real.rpow_mul hprod ((1 : ℝ) / 2) ((3 : ℝ) / 2)]
            congr 1
            norm_num
    _ = (fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) ^ ((3 : ℝ) / 4) *
        (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow hmax henergy

private theorem fluxPointwise_tsum_succ_le {f : ℕ → ℝ}
    (hf : Summable f) (h0 : ∀ k, 0 ≤ f k) :
    (∑' k : ℕ, f (k + 1)) ≤ ∑' k : ℕ, f k := by
  have htail : Summable (fun k => f (k + 1)) :=
    (summable_nat_add_iff (f := f) 1).2 hf
  have hdecomp := htail.sum_add_tsum_nat_add' (f := f) (k := 1)
  have hfirst : 0 ≤ ∑ k ∈ Finset.range 1, f k :=
    Finset.sum_nonneg fun k hk => h0 k
  rw [← hdecomp]
  exact le_add_of_nonneg_left hfirst

/-- The powered depth series is controlled by the one-step shift of the
printed block-weight series. -/
theorem fluxPointwise_poweredDepthSeries_le [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (hBlockSumm : Summable (fun k : ℕ => ((3 : ℝ)⁻¹) ^ k *
      (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4))) :
    Summable (fun k : ℕ => ((3 : ℝ)⁻¹) ^ k *
      (vecDepthMoment R (k + 1)
        (fluxFieldCarrier nu S omega
          (oscGluedGradM nu hnu S P e omega)
          (oscGluedGradN nu hnu S P e omega))) ^ ((3 : ℝ) / 2)) ∧
    (∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
      (vecDepthMoment R (k + 1)
        (fluxFieldCarrier nu S omega
          (oscGluedGradM nu hnu S P e omega)
          (oscGluedGradN nu hnu S P e omega))) ^ ((3 : ℝ) / 2)) ≤
      3 * (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) *
        ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
          (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
  let b : ℕ → ℝ := fun k => ((3 : ℝ)⁻¹) ^ k *
    (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)
  let tail : ℕ → ℝ := fun k => b (k + 1)
  let shift : ℕ → ℝ := fun k => ((3 : ℝ)⁻¹) ^ k *
    (fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) ^ ((3 : ℝ) / 4)
  let q : ℕ → ℝ := fun k => ((3 : ℝ)⁻¹) ^ k *
    (vecDepthMoment R (k + 1)
      (fluxFieldCarrier nu S omega
        (oscGluedGradM nu hnu S P e omega)
        (oscGluedGradN nu hnu S P e omega))) ^ ((3 : ℝ) / 2)
  have hb : Summable b := by simpa only [b] using hBlockSumm
  have htail : Summable tail := by
    dsimp [tail]
    exact (summable_nat_add_iff (f := b) 1).2 hb
  have hshiftEq : shift = fun k => (3 : ℝ) * tail k := by
    funext k
    dsimp [shift, tail, b]
    rw [pow_succ]
    field_simp
  have hshift : Summable shift := by
    rw [hshiftEq]
    exact Summable.mul_left 3 htail
  have htailLe : (∑' k : ℕ, tail k) ≤ ∑' k : ℕ, b k := by
    dsimp [tail]
    exact fluxPointwise_tsum_succ_le hb fun k => by
      dsimp [b]
      positivity
  have hshiftTsum : (∑' k : ℕ, shift k) ≤
      3 * ∑' k : ℕ, b k := by
    rw [hshiftEq, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htailLe (by norm_num)
  let E : ℝ := (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4)
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact Real.rpow_nonneg (oscEnergy_nonneg hnu S P e omega R) _
  have hq0 : ∀ k, 0 ≤ q k := by
    intro k
    dsimp [q]
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (vecDepthMoment_nonneg R (k + 1) _) _)
  have hqle : ∀ k, q k ≤ E * shift k := by
    intro k
    have hpower := fluxPointwise_depthMoment_rpow_le hnu S hSorder P e omega hR k
    dsimp [q, E, shift]
    calc ((3 : ℝ)⁻¹) ^ k *
          (vecDepthMoment R (k + 1)
            (fluxFieldCarrier nu S omega
              (oscGluedGradM nu hnu S P e omega)
              (oscGluedGradN nu hnu S P e omega))) ^ ((3 : ℝ) / 2)
        ≤ ((3 : ℝ)⁻¹) ^ k *
          ((fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) ^ ((3 : ℝ) / 4) *
            (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_left hpower (pow_nonneg (by norm_num) _)
      _ = (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) *
          (((3 : ℝ)⁻¹) ^ k *
            (fluxUniformBlockMax nu S.LPrime omega R (k + 1) : ℝ) ^ ((3 : ℝ) / 4)) := by
              ring
  have hq : Summable q :=
    Summable.of_nonneg_of_le hq0 hqle (Summable.mul_left E hshift)
  have hqTsum : (∑' k : ℕ, q k) ≤ E * ∑' k : ℕ, shift k := by
    calc ∑' k : ℕ, q k ≤ ∑' k : ℕ, E * shift k :=
          Summable.tsum_le_tsum hqle hq (Summable.mul_left E hshift)
      _ = E * ∑' k : ℕ, shift k := tsum_mul_left
  have hqTsum' : (∑' k : ℕ, q k) ≤ 3 * E * ∑' k : ℕ, b k := by
    calc ∑' k : ℕ, q k ≤ E * ∑' k : ℕ, shift k := hqTsum
      _ ≤ E * (3 * ∑' k : ℕ, b k) :=
        mul_le_mul_of_nonneg_left hshiftTsum hE0
      _ = 3 * E * ∑' k : ℕ, b k := by ring
  exact ⟨hq, by simpa only [q, b, E] using hqTsum'⟩

/-- Clause (1) at the fixed block weight, assuming the real block series has
the finiteness certificate supplied by Part 2B. -/
theorem fluxPointwise_of_blockSeries [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (hBlockSumm : Summable (fun k : ℕ => ((3 : ℝ)⁻¹) ^ k *
      (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)))
    (hWeight : fluxUniformBlockWeight nu S P e omega R =
      ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) :
    seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
      (fluxMspConst d ^ ((3 : ℝ) / 2) * Real.sqrt ((3 : ℝ) / 2) * 3) *
        (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
            fluxUniformBlockWeight nu S P e omega R) := by
  let F : Vec d → Vec d := fluxFieldCarrier nu S omega
    (oscGluedGradM nu hnu S P e omega) (oscGluedGradN nu hnu S P e omega)
  let w : ℕ → ℝ := fun k => ((3 : ℝ)⁻¹) ^ k
  let x : ℕ → ℝ := fun k => vecDepthMoment R (k + 1) F
  let g : ℕ → ℝ := fun k => w k * x k
  let q : ℕ → ℝ := fun k => w k * x k ^ ((3 : ℝ) / 2)
  let B : ℝ := Real.sqrt (vecSqAvg R F)
  let C : ℝ := fluxMspConst d
  let T : ℝ := (3 : ℝ) ^ ((S.n : ℕ) : ℝ)
  have hF : MemVectorL2 (openCubeSet R) F := by
    dsimp [F]
    exact fluxMsp_memVectorL2_fluxFieldCarrier_gluedDiff hnu S omega
      S.LPrime S.LPrime S.m S.n S.m (fluxSlot nu S.LPrime P S.n e) R
  have hx0 : ∀ k, 0 ≤ x k := by
    intro k
    exact vecDepthMoment_nonneg R (k + 1) F
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hxB : ∀ k, x k ≤ B := by
    intro k
    dsimp [x, B]
    exact fluxMsp_depthMoment_le_L2 R F hF (k + 1)
  have hJensen := fluxPointwise_weightedTsumJensen hx0 hxB
  have hDepthSeries := fluxPointwise_poweredDepthSeries_le hnu S hSorder P e omega hR hBlockSumm
  have hqSum : (∑' k : ℕ, q k) ≤
      3 * (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) *
        ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
          (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
    simpa only [q, w, x] using hDepthSeries.2
  have hG0 : 0 ≤ ∑' k : ℕ, g k := by
    apply tsum_nonneg
    intro k
    exact mul_nonneg (pow_nonneg (by norm_num) _) (hx0 k)
  have hJensen' : (∑' k : ℕ, g k) ^ ((3 : ℝ) / 2) ≤
      Real.sqrt ((3 : ℝ) / 2) * ∑' k : ℕ, q k := by
    simpa only [g, q, w, x] using hJensen
  have hsumTerm : (∑' k : ℕ, fluxMsp_depthTerm R F k) =
      (3 : ℝ) ^ ((R.scale : ℤ) : ℝ) * ∑' k : ℕ, g k := by
    have hterms : (fun k : ℕ => fluxMsp_depthTerm R F k) =
        (fun k => (3 : ℝ) ^ ((R.scale : ℤ) : ℝ) * g k) := by
      funext k
      dsimp [fluxMsp_depthTerm, g, w, x]
      ring
    rw [hterms, tsum_mul_left]
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  have hScale : (3 : ℝ) ^ ((R.scale : ℤ) : ℝ) = T := by
    rw [scale_eq_of_mem_largeCubeSubcubes hnm hR]
    rfl
  have hG0' : 0 ≤ (∑' k : ℕ, g k) := hG0
  have hTpos : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hT0 : 0 ≤ T := hTpos.le
  have hC0 : 0 ≤ C := by dsimp [C]; exact fluxMspConst_nonneg d
  have hSemBound : seminormFluxNeg nu hnu S P e omega R ≤ C * T * ∑' k : ℕ, g k := by
    have hmsp := fluxMsp_main (NeZero.pos d) R F hF
    have hscaleEq : (3 : ℝ) ^ ((S.n : ℕ) : ℝ) = T := rfl
    change (centredSeminormNegNorm R F).toReal ≤ C * T * ∑' k : ℕ, g k
    calc (centredSeminormNegNorm R F).toReal ≤
          fluxMspConst d * ∑' k : ℕ, fluxMsp_depthTerm R F k := hmsp
      _ = C * T * ∑' k : ℕ, g k := by
          rw [hsumTerm, hScale]
          dsimp [C]
          ring
  have hSem0 : 0 ≤ seminormFluxNeg nu hnu S P e omega R :=
    seminormFluxNeg_nonneg nu hnu S P e omega R
  have hSemPow := Real.rpow_le_rpow hSem0 hSemBound (by norm_num : 0 ≤ (3 : ℝ) / 2)
  have hEnergy0 : 0 ≤ oscEnergy nu hnu S P e omega R :=
    oscEnergy_nonneg hnu S P e omega R
  have hCpow0 : 0 ≤ C ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hC0 _
  have hTpow0 : 0 ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hT0 _
  have hGpowBound : (∑' k : ℕ, g k) ^ ((3 : ℝ) / 2) ≤
      Real.sqrt ((3 : ℝ) / 2) * ∑' k : ℕ, q k := hJensen'
  have hCseries : (C * T * ∑' k : ℕ, g k) ^ ((3 : ℝ) / 2) =
      C ^ ((3 : ℝ) / 2) * T ^ ((3 : ℝ) / 2) *
        (∑' k : ℕ, g k) ^ ((3 : ℝ) / 2) := by
    rw [show C * T * (∑' k : ℕ, g k) = C * (T * (∑' k : ℕ, g k)) by ring,
      Real.mul_rpow hC0 (mul_nonneg hT0 hG0'),
      Real.mul_rpow hT0 hG0']
    ring
  have hTpow : T ^ ((3 : ℝ) / 2) =
      (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) := by
    dsimp [T]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)
      ≤ (C * T * ∑' k : ℕ, g k) ^ ((3 : ℝ) / 2) := hSemPow
    _ = C ^ ((3 : ℝ) / 2) * T ^ ((3 : ℝ) / 2) *
        (∑' k : ℕ, g k) ^ ((3 : ℝ) / 2) := hCseries
    _ ≤ C ^ ((3 : ℝ) / 2) * T ^ ((3 : ℝ) / 2) *
        (Real.sqrt ((3 : ℝ) / 2) * ∑' k : ℕ, q k) :=
          mul_le_mul_of_nonneg_left hGpowBound (mul_nonneg hCpow0 hTpow0)
    _ ≤ C ^ ((3 : ℝ) / 2) * T ^ ((3 : ℝ) / 2) *
        (Real.sqrt ((3 : ℝ) / 2) *
          (3 * (oscEnergy nu hnu S P e omega R) ^ ((3 : ℝ) / 4) *
            ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
              (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4))) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hqSum (Real.sqrt_nonneg _)
          · exact mul_nonneg hCpow0 hTpow0
    _ = (fluxMspConst d ^ ((3 : ℝ) / 2) * Real.sqrt ((3 : ℝ) / 2) * 3) *
        (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
            fluxUniformBlockWeight nu S P e omega R) := by
          rw [hTpow, ← hWeight]
          dsimp [C]
          ring

/-- Clause (1) of the flux gap at the fixed Part 0 block weight. -/
theorem fluxPointwise_main (d : ℕ) [NeZero d] :
    ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤
            ((S.a : ℕ) : ℝ))
        (e : Vec d) (_he : vecNormSq e = 1),
        ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
          seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
            C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
              (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
                fluxUniformBlockWeight nu S P e omega R) := by
  refine ⟨fluxMspConst d ^ ((3 : ℝ) / 2) *
    Real.sqrt ((3 : ℝ) / 2) * 3, ?_, ?_⟩
  · have hC : 0 ≤ fluxMspConst d := fluxMspConst_nonneg d
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hC _)
      (Real.sqrt_nonneg _)) (by norm_num)
  · intro nu hnu _hnu1 P _hPrefix _hJ1V2 _hJ2 _hJ3 _hJ4 S hSorder
      _hTwoHLeM _hHundredALeH _hWindowVsOffset _hOffsetLower e _he omega R hR
    obtain ⟨hWeight, hBlockSumm⟩ :=
      fluxBlockFinite_weight_eq_tsum hnu S P e omega hR
    have hcoef (k : ℕ) : (3 : ℝ) ^ (-(k : ℝ)) = ((3 : ℝ)⁻¹) ^ k := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (k : ℝ),
        Real.rpow_natCast, ← inv_pow]
    have hWeight' : fluxUniformBlockWeight nu S P e omega R =
        ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
          (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
      calc fluxUniformBlockWeight nu S P e omega R =
            ∑' k : ℕ, (3 : ℝ) ^ (-(k : ℝ)) *
              (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) :=
                hWeight
        _ = ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k *
              (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
                apply tsum_congr
                intro k
                rw [hcoef]
    have hBlockSumm' : Summable (fun k : ℕ => ((3 : ℝ)⁻¹) ^ k *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
      simpa only [hcoef] using hBlockSumm
    exact fluxPointwise_of_blockSeries hnu S hSorder P e omega hR
      hBlockSumm' hWeight'

end

end SuperdiffusionCLT.Section3.Terms
