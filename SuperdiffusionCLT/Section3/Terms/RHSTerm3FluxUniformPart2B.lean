/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart0
public import SuperdiffusionCLT.Section3.HighContrast.EllipticityMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import Homogenization.Besov.Poincare.Projection
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- A sample-dependent bound for the coarse block norm on every descendant of
the scale-selection subcubes. -/
def fluxBlockFinite_sampleBound (nu : ℝ) (S : ScaleSelection)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) : ℝ :=
  nu + 2 * nu⁻¹ *
    (SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound
      S.LPrime S.m omega) ^ 2

theorem fluxBlockFinite_sampleBound_nonneg {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    0 ≤ fluxBlockFinite_sampleBound nu S omega := by
  have hH := SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound_nonneg
    S.LPrime S.m omega
  unfold fluxBlockFinite_sampleBound
  positivity

private theorem fluxBlockFinite_scaleWeight_eq_geometric (k : ℕ) :
    (3 : ℝ) ^ (-(k : ℝ)) = ((3 : ℝ)⁻¹) ^ k := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (k : ℝ),
    Real.rpow_natCast, inv_pow]

/-- On descendants of a scale-`S.n` cube inside `cu_{S.m}`, the stream cutoff
is bounded on the enclosing cube. The Chapter 2 coarse block estimate then
gives one bound valid at every descendant depth. -/
theorem fluxBlockFinite_blockMax_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {R : TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
      d S.n S.m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∀ Q : TriadicCube d,
      Q ∈ descendantsAtDepth R k → translatedBlockNorm nu S.LPrime omega Q ≤ B := by
  let B := fluxBlockFinite_sampleBound nu S omega
  have hB : 0 ≤ B := fluxBlockFinite_sampleBound_nonneg hnu S omega
  refine ⟨B, hB, fun k Q hQ => ?_⟩
  have hparent : Q ∈ descendantsAtDepth (originCube d (S.m : ℤ))
      (S.m - S.n + k) := by
    simpa only [SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes] using
      Homogenization.mem_descendantsAtDepth_add hR hQ
  have hsub : openCubeSet Q ⊆ openCubeSet (originCube d (S.m : ℤ)) :=
    Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hparent
  have hH : ∀ x ∈ openCubeSet Q,
      Book.Ch02.matrixOperatorNorm
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x) ≤
        SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound
          S.LPrime S.m omega := by
    intro x hx
    exact SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_streamCutoff_le_streamCutoffLargeCubeSupBound omega
      (Homogenization.openCubeSet_subset_cubeSet _ (hsub hx))
  have hfinite : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (Homogenization.volume_openCubeSet_lt_top Q).ne
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 :=
    (ENNReal.toReal_pos
      (SuperdiffusionCLT.Section2.Annealed.volume_openCubeSet_ne_zero Q)
      (Homogenization.volume_openCubeSet_lt_top Q).ne).ne'
  have hmean : volumeAverage (openCubeSet Q)
      (fun x => Book.Ch02.matrixOperatorNorm
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x) ^ 2) ≤
      (SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound
        S.LPrime S.m omega) ^ 2 := by
    calc
      volumeAverage (openCubeSet Q)
          (fun x => Book.Ch02.matrixOperatorNorm
            (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x) ^ 2) ≤
        volumeAverage (openCubeSet Q) (fun _ =>
          (SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound
            S.LPrime S.m omega) ^ 2) :=
        Homogenization.volumeAverage_le_volumeAverage_of_le_on
          (Homogenization.isOpen_openCubeSet Q).measurableSet
          (SuperdiffusionCLT.Section2.Annealed.integrableOn_matrixOperatorNorm_sq_streamCutoff
            omega S.LPrime Q)
          (integrableOn_const (Homogenization.volume_openCubeSet_lt_top Q).ne)
          (fun x hx =>
            pow_le_pow_left₀ (Book.Ch02.matrixOperatorNorm_nonneg _)
              (hH x hx) 2)
      _ = (SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound
          S.LPrime S.m omega) ^ 2 :=
        Homogenization.volumeAverage_const hvol
  have hlocal :=
    SuperdiffusionCLT.Section3.HighContrast.matrixNorm_upperLeft_coarseBlockMatrix_coefficientCutoff_le
      hnu omega S.LPrime Q
  have hconvert : translatedBlockNorm nu S.LPrime omega Q =
      Book.Ch02.matrixNorm
        (Homogenization.coarseBlockMatrix (cubeSet Q)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
            nu omega S.LPrime).toCoeffField).upperLeft := by
    rw [translatedBlockNorm, translatedCoarseBlock, translatedBlockMat_eq_cubeSet,
      Book.Ch02.matrixNorm_eq_matrixOperatorNorm]
  dsimp [B, fluxBlockFinite_sampleBound]
  calc
    translatedBlockNorm nu S.LPrime omega Q ≤
      nu + 2 * nu⁻¹ * volumeAverage (openCubeSet Q)
        (fun x => Book.Ch02.matrixOperatorNorm
          (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x) ^ 2) := by
            rw [hconvert]
            exact hlocal
    _ ≤ nu + 2 * nu⁻¹ *
        (SuperdiffusionCLT.Section2.Estimates.Stream.streamCutoffLargeCubeSupBound
          S.LPrime S.m omega) ^ 2 :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left hmean
              (show (0 : ℝ) ≤ 2 * nu⁻¹ by positivity)) nu

private theorem fluxBlockFinite_realSeries_summable [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (S : ScaleSelection)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {R : TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
      d S.n S.m) :
    Summable (fun k : ℕ => (3 : ℝ) ^ (-(k : ℝ)) *
      (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
  obtain ⟨B, hB, hblock⟩ := fluxBlockFinite_blockMax_le hnu S omega hR
  have hgeom : Summable (fun k : ℕ => ((3 : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hterm_nonneg : ∀ k : ℕ,
      0 ≤ (3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
    intro k
    positivity
  have hmax : ∀ k : ℕ, (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ≤ B := by
    intro k
    have hnn : fluxUniformBlockMax nu S.LPrime omega R k ≤ Real.toNNReal B := by
      unfold fluxUniformBlockMax
      refine Finset.sup_le ?_
      intro Q hQ
      have hq := hblock k Q hQ
      have hq' : ((translatedBlockNorm nu S.LPrime omega Q).toNNReal : ℝ) ≤ B := by
        change ((Real.toNNReal
          (Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu S.LPrime omega Q)) :
            ℝ≥0) : ℝ) ≤ B
        rw [Real.coe_toNNReal _ (Book.Ch02.matrixOperatorNorm_nonneg _)]
        simpa only [translatedBlockNorm] using hq
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal B hB]
      exact hq'
    rw [← Real.coe_toNNReal B hB]
    exact_mod_cast hnn
  have hpow : ∀ k : ℕ,
      (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) ≤
        B ^ ((3 : ℝ) / 4) := by
    intro k
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (hmax k) (by norm_num)
  have hle : ∀ k : ℕ,
      (3 : ℝ) ^ (-(k : ℝ)) *
          (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) ≤
        ((3 : ℝ)⁻¹) ^ k * B ^ ((3 : ℝ) / 4) := by
    intro k
    rw [fluxBlockFinite_scaleWeight_eq_geometric]
    exact mul_le_mul_of_nonneg_left (hpow k) (pow_nonneg (by norm_num) k)
  exact Summable.of_nonneg_of_le hterm_nonneg hle
    (hgeom.mul_right (B ^ ((3 : ℝ) / 4)))

private theorem fluxBlockFinite_weightE_eq_ofReal_tsum [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (S : ScaleSelection)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {R : TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
      d S.n S.m) :
    fluxUniformBlockWeightE nu S.LPrime omega R =
        ENNReal.ofReal (∑' k : ℕ, (3 : ℝ) ^ (-(k : ℝ)) *
          (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) ∧
      Summable (fun k : ℕ => (3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
  let f : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℝ)) *
    (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)
  have hsum : Summable f := fluxBlockFinite_realSeries_summable hnu S omega hR
  have hf0 : ∀ k : ℕ, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hterm : ∀ k : ℕ,
      ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ))) *
        ((fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4)) =
      ENNReal.ofReal (f k) := by
    intro k
    have hpow :
        ((fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4)) =
          ENNReal.ofReal
            ((fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
      calc
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4) =
            ↑((fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0) ^ ((3 : ℝ) / 4)) :=
          (ENNReal.coe_rpow_of_nonneg _ (by norm_num)).symm
        _ = ENNReal.ofReal
            (↑((fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0) ^ ((3 : ℝ) / 4)) : ℝ) := by
          rw [ENNReal.ofReal_coe_nnreal]
        _ = ENNReal.ofReal
            ((fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
          rw [NNReal.coe_rpow]
    change ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ))) *
        ((fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4)) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4))
    rw [hpow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ (-(k : ℝ)))]
  have hweight : fluxUniformBlockWeightE nu S.LPrime omega R =
      ENNReal.ofReal (∑' k : ℕ, f k) := by
    rw [fluxUniformBlockWeightE]
    calc
      ∑' k : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ))) *
          ((fluxUniformBlockMax nu S.LPrime omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4)) =
        ∑' k : ℕ, ENNReal.ofReal (f k) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' k : ℕ, f k) :=
        (ENNReal.ofReal_tsum_of_nonneg hf0 hsum).symm
  refine ⟨hweight, ?_⟩
  simpa only [f] using hsum

/-- The real block weight equals the summable real series in the printed block
weight. -/
theorem fluxBlockFinite_weight_eq_tsum [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (e : Vec d) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {R : TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
      d S.n S.m) :
    fluxUniformBlockWeight nu S P e omega R =
        ∑' k : ℕ, (3 : ℝ) ^ (-(k : ℝ)) *
          (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) ∧
      Summable (fun k : ℕ => (3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4)) := by
  obtain ⟨hweight, hsum⟩ := fluxBlockFinite_weightE_eq_ofReal_tsum hnu S omega hR
  have hf0 : ∀ k : ℕ, 0 ≤
      (3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
    intro k
    positivity
  have hsum0 : 0 ≤ ∑' k : ℕ,
      (3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) :=
    tsum_nonneg hf0
  have hreal : fluxUniformBlockWeight nu S P e omega R = ∑' k : ℕ,
      (3 : ℝ) ^ (-(k : ℝ)) *
        (fluxUniformBlockMax nu S.LPrime omega R k : ℝ) ^ ((3 : ℝ) / 4) := by
    unfold fluxUniformBlockWeight
    rw [hweight, ENNReal.toReal_ofReal hsum0]
  exact ⟨hreal, hsum⟩

end

end SuperdiffusionCLT.Section3.Terms
