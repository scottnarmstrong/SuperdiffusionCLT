/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearTailAssemblyB
public import SuperdiffusionCLT.Section4.NewMixing.ParamStatement
public import SuperdiffusionCLT.Section2.Localization.CutoffLoewnerClauses
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeEllipticity
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# Near-tail assembly: the Loewner comparison and its reduction to the scalar `J`

Steps 3 to 6 of the near-tail uniformity step of `p.new.mixing.attempt`, for a Chapter 2
domain `U` inside an averaging domain `V ⊆ cu_n` and the shell interval `(mm, L]` with
`n ≤ mm + 1`.

* `srootN3_nearTail_clauses`: the two-sided Loewner comparison of the block matrices of the
  recentered cutoff field and of `a_mm`.
* `srootN3_blockForm_le_envelope`: the energy of the cutoff field is dominated by the
  envelope bfE_mm times the random factor `envelopeRatioOn` (`l.bfAm.ellip`).
* `srootN3_isBigO_nearTailY`: the assembled `Γ_{1/2}` bound on the random factor
  `srootN3_nearTailY`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

/-- **The energy of the cutoff field against the envelope** (`l.bfAm.ellip`, first
assertion on a general domain): `X · bfA_mm(U) X ≤ ρ (u |x|² + l |y|²)` with `ρ` the random factor
`envelopeRatioOn` and `(u, l)` the two scalars of bfE_mm. -/
theorem srootN3_blockForm_le_envelope {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (U : Domain d) (omega : ShellSeq d) (mm : ℕ) (x y : Vec d) :
    blockVecDot (x, y) (blockMatVecMul (Homogenization.coarseBlockMatrix (U : Set (Vec d))
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega mm).toCoeffField)
        (x, y)) ≤
      envelopeRatioOn mm (U : Set (Vec d)) omega *
        (envelopeUpperScalar d nu mm * vecNormSq x + envelopeLowerScalar d nu * vecNormSq y) := by
  have hu := envelopeUpperScalar_pos hnu d mm
  have hl := envelopeLowerScalar_pos hnu d
  have hsu : 0 < Real.sqrt (envelopeUpperScalar d nu mm) := Real.sqrt_pos.2 hu
  have hsl : 0 < Real.sqrt (envelopeLowerScalar d nu) := Real.sqrt_pos.2 hl
  have hLoew := blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix_domain U hnu omega mm
    (Real.sqrt (envelopeUpperScalar d nu mm) • x, Real.sqrt (envelopeLowerScalar d nu) • y)
  rw [blockVecDot_envelopeRescale] at hLoew
  simp only [inv_smul_smul₀ hsu.ne', inv_smul_smul₀ hsl.ne',
    blockMatVecMul_blockSMul, blockMatVecMul_blockIdentity, blockVecDot_smul_right,
    SuperdiffusionCLT.Section2.Carriers.blockVecDot_self, vecNormSq_smul,
    Real.sq_sqrt hu.le, Real.sq_sqrt hl.le] at hLoew
  have h := hLoew
  linarith only [h]

theorem srootN3_cutoffDomainCoeffOn_toCoeffField {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (U : Domain d) (omega : ShellSeq d) (mm : ℕ) (x : Vec d) :
    (cutoffDomainCoeffOn U hnu omega mm).toCoeffField x =
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega mm).toCoeffField x := by
  unfold cutoffDomainCoeffOn
  rw [SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField]

/-- **The two-sided Loewner comparison (step 3)**: on `U ⊆ V ⊆ cu_n`, if `b` is the cutoff `a_L`
recentered by the volume average over `V` of the shell increment `k_L - k_mm`, and the centered
increment has operator norm at most `M` on `V`, then `bfA(U; b)` is within
`D = ν⁻¹ M + ν⁻² M²` of `bfA(U; a_mm)` in the block Loewner order
(`l.localization.A`, scalar form). -/
theorem srootN3_nearTail_clauses {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {mm L : ℕ} (hmL : mm ≤ L) (V U : Domain d)
    (hUV : (U : Set (Vec d)) ⊆ (V : Set (Vec d))) {M : ℝ}
    (hM : ∀ x ∈ (V : Set (Vec d)),
      matrixOperatorNorm (finiteShellIncrement omega mm L x -
        volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y)) ≤ M)
    (b : CoeffOn U)
    (hb : ∀ x ∈ (U : Set (Vec d)), b.toCoeffField x =
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x -
        volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y)) :
    BlockMatLoewnerLE
        ((-(nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2)) •
          Book.Ch02.coarseBlockMatrix U (cutoffDomainCoeffOn U hnu omega mm))
        (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U (cutoffDomainCoeffOn U hnu omega mm)))) ∧
      BlockMatLoewnerLE
        (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
          toFullBlockMat (Book.Ch02.coarseBlockMatrix U (cutoffDomainCoeffOn U hnu omega mm))))
        ((nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2) •
          Book.Ch02.coarseBlockMatrix U (cutoffDomainCoeffOn U hnu omega mm)) := by
  obtain ⟨x0, hx0⟩ := U.nonempty
  have hM0 : 0 ≤ M := le_trans (matrixOperatorNorm_nonneg _) (hM x0 (hUV hx0))
  have hincr_sub : ∀ x : Vec d,
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x -
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega mm).toCoeffField x =
      finiteShellIncrement omega mm L x :=
    SuperdiffusionCLT.Section2.Localization.coefficientCutoff_toCoeffField_sub nu omega hmL
  have hskewAvg : matTranspose (volumeAverageMat (V : Set (Vec d))
      (fun y => finiteShellIncrement omega mm L y)) =
    -(volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y)) :=
    matTranspose_volumeAverageMat (V : Set (Vec d))
      (fun y => finiteShellIncrement omega mm L y)
      (fun y i k => by
        have hsk := congrFun (congrFun (finiteShellIncrement_skew omega mm L y) k) i
        simpa only [Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply] using hsk)
  have hae : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))), x ∈ (U : Set (Vec d)) :=
    ae_restrict_mem U.measurableSet
  refine SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_localization_scalar_two_sided
    (U := U) (a := cutoffDomainCoeffOn U hnu omega mm) (b := b)
    (h := fun x => finiteShellIncrement omega mm L x -
      volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y))
    hnu hM0 ?_ ?_ ?_ ?_
  · filter_upwards with x
    rw [srootN3_cutoffDomainCoeffOn_toCoeffField]
    exact SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega mm x
  · filter_upwards [hae] with x hx
    rw [hb x hx, srootN3_cutoffDomainCoeffOn_toCoeffField, ← hincr_sub x]
    abel
  · filter_upwards with x
    show Matrix.transpose (finiteShellIncrement omega mm L x -
        volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y)) =
      -(finiteShellIncrement omega mm L x -
        volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y))
    have h1 : Matrix.transpose (finiteShellIncrement omega mm L x) =
        -finiteShellIncrement omega mm L x := finiteShellIncrement_skew omega mm L x
    have h2 : Matrix.transpose (volumeAverageMat (V : Set (Vec d))
        (fun y => finiteShellIncrement omega mm L y)) =
      -(volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y)) :=
      hskewAvg
    rw [Matrix.transpose_sub, h1, h2]
    abel
  · filter_upwards [hae] with x hx w
    refine (vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq _ w).trans ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) (hM x (hUV hx)) 2) (vecNormSq_nonneg w)

/-! ## The random witness -/

/-- The relative size `ν⁻¹ M` of the centered increment, with `M = diamConst · 3^n · tailGauge`. -/
def srootN3_nearTailW (d : ℕ) (nu : ℝ) (n mm : ℕ) (omega : ShellSeq d) : ℝ :=
  nu⁻¹ * (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n * srootN3_tailGauge d n mm omega)

/-- The random witness of step 6: `ρ (W + W²)` with `ρ` the envelope factor on `U`. -/
def srootN3_nearTailY (d : ℕ) (nu : ℝ) (n mm : ℕ) (U : Set (Vec d)) (omega : ShellSeq d) : ℝ :=
  srootN3_nearTailW d nu n mm omega * envelopeRatioOn mm U omega +
    (srootN3_nearTailW d nu n mm omega * srootN3_nearTailW d nu n mm omega) *
      envelopeRatioOn mm U omega

/-- The dimensional constant of the `Γ_{1/2}` amplitude of the witness. -/
def srootN3_tailConst (d : ℕ) : ℝ :=
  gammaTriangleConst (1 / 2) *
    (SuperdiffusionCLT.Probability.orliczProductConst 2 1 *
        (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * 16384) +
      SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
        SuperdiffusionCLT.Probability.orliczProductConst 2 2 *
        (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * 16384) ^ 2)

theorem srootN3_measurable_nearTailW (d : ℕ) (nu : ℝ) (n mm : ℕ) :
    Measurable (srootN3_nearTailW d nu n mm : ShellSeq d → ℝ) :=
  measurable_const.mul ((srootN3_measurable_tailGauge n mm).const_mul _)

theorem srootN3_measurable_envelopeRatioOn {d : ℕ} (mm : ℕ) (U : Set (Vec d)) :
    Measurable (fun omega : ShellSeq d => envelopeRatioOn mm U omega) :=
  measurable_const.max
    ((measurable_volumeAverage_sq_streamCutoff (d := d) mm U).div_const
      (cutoffEnvelopeConst d * max 1 (mm : ℝ)))

theorem srootN3_nearTailW_nonneg {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (n mm : ℕ)
    (omega : ShellSeq d) : 0 ≤ srootN3_nearTailW d nu n mm omega := by
  unfold srootN3_nearTailW
  have h1 := srootN3_tailGauge_nonneg n mm omega
  have h2 := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst_nonneg d
  positivity

theorem srootN3_nearTailY_nonneg {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (n mm : ℕ) (U : Set (Vec d))
    (omega : ShellSeq d) : 0 ≤ srootN3_nearTailY d nu n mm U omega := by
  unfold srootN3_nearTailY
  have h1 := srootN3_nearTailW_nonneg hnu n mm omega
  have h2 := one_le_envelopeRatioOn mm U omega
  have h3 : 0 ≤ envelopeRatioOn mm U omega := le_trans zero_le_one h2
  positivity

/-- **Steps 4 to 6, stochastic half**: the witness `ρ (W + W²)` is measurable and `Γ_{1/2}`-bounded.
The linear part `W ρ` is a `Γ₂ · Γ₁` product, hence `Γ_{2/3}`; the quadratic part `W² ρ` is
`Γ₁ · Γ₁`, hence `Γ_{1/2}`; the sum is `Γ_{1/2}`, which weakens to the manuscript's `Γ_{1/3}`. -/
theorem srootN3_isBigO_nearTailY {d : ℕ} [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) {mm n : ℕ} (hnm : n ≤ mm + 1) (U : Domain d) :
    Measurable (srootN3_nearTailY d nu n mm (U : Set (Vec d))) ∧
      IsBigO P.toMeasure (gammaSigma (1 / 2))
        (srootN3_nearTailY d nu n mm (U : Set (Vec d)))
        (srootN3_tailConst d *
          (nu⁻¹ * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) +
            nu⁻¹ ^ 2 * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) ^ 2)) := by
  have hdpos : 0 < SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d := by
    unfold SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst
    have : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
    positivity
  set q : ℝ := (3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹ with hq
  have hqpos : 0 < q := by positivity
  set kap : ℝ := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * 16384 with hkap
  have hkappos : 0 < kap := by positivity
  set a0 : ℝ := nu⁻¹ * (kap * q) with ha0
  have ha0pos : 0 < a0 := by positivity
  have hWmeas := srootN3_measurable_nearTailW d nu n mm
  have hrmeas := srootN3_measurable_envelopeRatioOn (d := d) mm (U : Set (Vec d))
  -- the Γ₂ bound of `W`
  have hW : IsBigO P.toMeasure (gammaSigma 2) (srootN3_nearTailW d nu n mm) a0 := by
    have h := (srootN3_isBigO_tailGauge hJ3 hnm).const_mul
      (c := nu⁻¹ * (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n)) (by positivity)
    have heq : (fun omega : ShellSeq d => (nu⁻¹ * (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d *
        (3 : ℝ) ^ n)) * srootN3_tailGauge d n mm omega) = srootN3_nearTailW d nu n mm :=
      funext fun omega => by unfold srootN3_nearTailW; ring
    rw [heq] at h
    refine h.mono_scale (le_of_eq ?_)
    rw [ha0, hkap, hq]
    ring
  -- the Γ₁ bound of `ρ`
  have hrho : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega => envelopeRatioOn mm (U : Set (Vec d)) omega) 1 :=
    (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := gammaSigma 1)
      (X := fun omega => envelopeRatioOn mm (U : Set (Vec d)) omega) (A := 1)
      (fun omega => le_trans zero_le_one
        (one_le_envelopeRatioOn mm (U : Set (Vec d)) omega))).1
      (isBigOWith_gammaSigma_envelopeRatioOn hPrefix hJ2 hJ3 hJ4 mm
        (volume_domain_ne_zero U) (volume_domain_ne_top U))
  -- the linear part, `Γ_{2/3}`, weakened to `Γ_{1/2}`
  have hY1 : IsBigO P.toMeasure (gammaSigma (1 / 2))
      (fun omega => srootN3_nearTailW d nu n mm omega *
        envelopeRatioOn mm (U : Set (Vec d)) omega)
      (SuperdiffusionCLT.Probability.orliczProductConst 2 1 * (a0 * 1)) := by
    have h := SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul (by norm_num)
      (by norm_num) ha0pos.le zero_le_one hW hrho
    exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_of_exponent_le
      (by norm_num) h
  -- the quadratic part: `Γ₂ · Γ₂ = Γ₁`, then `Γ₁ · Γ₁ = Γ_{1/2}`
  have hW2 : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega => srootN3_nearTailW d nu n mm omega * srootN3_nearTailW d nu n mm omega)
      (SuperdiffusionCLT.Probability.orliczProductConst 2 2 * (a0 * a0)) := by
    have h := SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul (by norm_num)
      (by norm_num) ha0pos.le ha0pos.le hW hW
    have h22 : (2 : ℝ) * 2 / (2 + 2) = 1 := by norm_num
    rwa [h22] at h
  have hY2 : IsBigO P.toMeasure (gammaSigma (1 / 2))
      (fun omega => (srootN3_nearTailW d nu n mm omega * srootN3_nearTailW d nu n mm omega) *
        envelopeRatioOn mm (U : Set (Vec d)) omega)
      (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
        ((SuperdiffusionCLT.Probability.orliczProductConst 2 2 * (a0 * a0)) * 1)) := by
    have h := SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul (by norm_num)
      (by norm_num)
      (mul_nonneg (SuperdiffusionCLT.Probability.orliczProductConst_pos 2 2).le
        (mul_nonneg ha0pos.le ha0pos.le)) zero_le_one hW2 hrho
    have h11 : (1 : ℝ) * 1 / (1 + 1) = 1 / 2 := by norm_num
    rwa [h11] at h
  have hA1 : 0 < SuperdiffusionCLT.Probability.orliczProductConst 2 1 * (a0 * 1) :=
    mul_pos (SuperdiffusionCLT.Probability.orliczProductConst_pos 2 1) (by positivity)
  have hA2 : 0 < SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
      ((SuperdiffusionCLT.Probability.orliczProductConst 2 2 * (a0 * a0)) * 1) :=
    mul_pos (SuperdiffusionCLT.Probability.orliczProductConst_pos 1 1)
      (by have := SuperdiffusionCLT.Probability.orliczProductConst_pos 2 2; positivity)
  have hm1 : Measurable fun omega => srootN3_nearTailW d nu n mm omega *
      envelopeRatioOn mm (U : Set (Vec d)) omega := hWmeas.mul hrmeas
  have hm2 : Measurable fun omega => (srootN3_nearTailW d nu n mm omega *
      srootN3_nearTailW d nu n mm omega) *
      envelopeRatioOn mm (U : Set (Vec d)) omega := (hWmeas.mul hWmeas).mul hrmeas
  refine ⟨hm1.add hm2, ?_⟩
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (mu := P.toMeasure) (by norm_num) hA1 hA2 hY1 hY2 hm1 hm2
  refine hsum.mono_scale ?_
  unfold srootN3_tailConst
  have ho1 := SuperdiffusionCLT.Probability.orliczProductConst_pos 2 1
  have ho2 := SuperdiffusionCLT.Probability.orliczProductConst_pos 2 2
  have ho3 := SuperdiffusionCLT.Probability.orliczProductConst_pos 1 1
  have ht := gammaTriangleConst_pos (σ := (1 / 2 : ℝ))
  have hs1 : 0 ≤ nu⁻¹ * q := by positivity
  have hs2 : 0 ≤ nu⁻¹ ^ 2 * q ^ 2 := by positivity
  have hal : 0 ≤ SuperdiffusionCLT.Probability.orliczProductConst 2 1 * kap := by positivity
  have hbe : 0 ≤ SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
      SuperdiffusionCLT.Probability.orliczProductConst 2 2 * kap ^ 2 := by positivity
  have hrew : SuperdiffusionCLT.Probability.orliczProductConst 2 1 * (a0 * 1) +
      SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
        ((SuperdiffusionCLT.Probability.orliczProductConst 2 2 * (a0 * a0)) * 1) =
      (SuperdiffusionCLT.Probability.orliczProductConst 2 1 * kap) * (nu⁻¹ * q) +
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
          SuperdiffusionCLT.Probability.orliczProductConst 2 2 * kap ^ 2) *
          (nu⁻¹ ^ 2 * q ^ 2) := by
    rw [ha0]; ring
  rw [hrew, ← hkap]
  have key : (SuperdiffusionCLT.Probability.orliczProductConst 2 1 * kap) * (nu⁻¹ * q) +
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
          SuperdiffusionCLT.Probability.orliczProductConst 2 2 * kap ^ 2) *
          (nu⁻¹ ^ 2 * q ^ 2) ≤
      ((SuperdiffusionCLT.Probability.orliczProductConst 2 1 * kap) +
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
          SuperdiffusionCLT.Probability.orliczProductConst 2 2 * kap ^ 2)) *
        (nu⁻¹ * q + nu⁻¹ ^ 2 * q ^ 2) := by
    nlinarith only [mul_nonneg hal hs2, mul_nonneg hbe hs1]
  calc _ ≤ gammaTriangleConst (1 / 2) * (((SuperdiffusionCLT.Probability.orliczProductConst 2 1 * kap) +
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
          SuperdiffusionCLT.Probability.orliczProductConst 2 2 * kap ^ 2)) *
        (nu⁻¹ * q + nu⁻¹ ^ 2 * q ^ 2)) := mul_le_mul_of_nonneg_left key ht.le
    _ = _ := by ring

/-- The test vector `bfAhom_r^{-1/2} η` of `newMixParam_bfAhomPow` in the scalar form
`(sa η₁, sb η₂)`, `sa = σ^{-1/2}`, `sb = σ^{1/2}`. -/
theorem srootN3_bfAhomPow_neg_half {d : ℕ} [NeZero d] (nu : ℝ) (r : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (eta : BlockVec d) :
    SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta =
      ((sigmaBarInfinite nu r P) ^ (-(1 : ℝ) / 2) • eta.1,
        (sigmaBarInfinite nu r P) ^ ((1 : ℝ) / 2) • eta.2) := by
  unfold SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow
  rw [show -(-(1 : ℝ) / 2) = (1 : ℝ) / 2 by ring]

/-- The test vector `bfAhom_r^{1/2} η` of `newMixParam_bfAhomPow`, as `(sb η₁, sa η₂)`. -/
theorem srootN3_bfAhomPow_half {d : ℕ} [NeZero d] (nu : ℝ) (r : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (eta : BlockVec d) :
    SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta =
      ((sigmaBarInfinite nu r P) ^ ((1 : ℝ) / 2) • eta.1,
        (sigmaBarInfinite nu r P) ^ (-(1 : ℝ) / 2) • eta.2) := by
  unfold SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow
  rw [show -((1 : ℝ) / 2) = -(1 : ℝ) / 2 by ring]

/-! ## Satisfiability of the non-law hypotheses -/

end

end SuperdiffusionCLT.Section4.MinimalScales
