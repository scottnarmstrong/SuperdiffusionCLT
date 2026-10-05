/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearTailAssembly
public import SuperdiffusionCLT.Section4.NewMixing.Splitting

/-!
# Near-tail comparison of `J` at a skew-shifted pair of fields

The uniform-in-`h0` form of the unshifted near-tail comparison of `NearTailAssembly.lean`:
for every constant skew matrix `h0`, the comparison of `J(U; b + h0)` against
`J(U; a_mm + h0)` at the scalar test vectors costs
`(u sa² + 2 l sb² + 2 l sa² ‖h0‖²) · Y`, with the same `h0`-free `Γ_{1/2}` witness `Y`.

The gauge identity `bfA(U; a + h0) = G_{-h0}ᵗ bfA(U; a) G_{-h0}`
(`coarseBlockMatrix_addConstSkewCoeffOn`) carries the Loewner sandwich unchanged, and the
energy of the shifted field is the energy of the unshifted one at `G_{-h0}` applied to the test
vector.
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

/-- The gauge matrix `G_{-h0}` acts on a block vector by `(x, y) ↦ (x, y - h0 x)`. -/
theorem srootNS_blockG_neg_apply {d : ℕ} (h0 : Mat d) (x y : Vec d) :
    blockMatVecMul (blockG (-h0)) (x, y) = (x, y - matVecMul h0 x) := by
  have h1 : ∀ x : Vec d, matVecMul (1 : Mat d) x = x := fun x => by
    funext i
    simp [matVecMul, Matrix.one_apply]
  have h2 : ∀ y : Vec d, matVecMul (0 : Mat d) y = 0 := fun y => by
    funext i
    simp [matVecMul]
  refine Prod.ext ?_ ?_
  · simp [blockMatVecMul, blockG, h1, h2]
  · simp [blockMatVecMul, blockG, h1, neg_matVecMul, sub_eq_add_neg, add_comm]

/-- **The `J` comparison from a key inequality on the quadratic forms.** The same conclusion as
the Loewner-hypothesis `J` comparison of `NearTailAssembly.lean`, with the Loewner
hypotheses replaced by their quadratic-form consequence. -/
theorem srootNS_doubledResponseJ_sub_le_of_key {d : ℕ} (U : Domain d) (a b : CoeffOn U) {D : ℝ}
    (key : ∀ X : BlockVec d,
      |blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U b) X) -
          blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) X)| ≤
        D * blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) X))
    (P Q : BlockVec d) :
    |doubledResponseJ U b P Q - doubledResponseJ U a P Q| ≤
      D * ((1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) +
        (1 / 2 : ℝ) * blockVecDot (Q.2, Q.1)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (Q.2, Q.1))) := by
  have hb := (blockCoarseMatrixTheory U b).doubled_response_splitting P Q
  have ha := (blockCoarseMatrixTheory U a).doubled_response_splitting P Q
  have hR : ∀ c : CoeffOn U,
      blockVecDot Q (blockMatVecMul (Book.Ch02.coarseStarredBlockMatrixInv U c) Q) =
        blockVecDot (Q.2, Q.1) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U c) (Q.2, Q.1)) :=
    fun c => blockVecDot_blockMatVecMul_blockReflect (Book.Ch02.coarseBlockMatrix U c) Q
  rw [hb, ha, hR a, hR b]
  have k1 := abs_le.1 (key P)
  have k2 := abs_le.1 (key (Q.2, Q.1))
  rw [abs_le]
  constructor <;> nlinarith only [k1.1, k1.2, k2.1, k2.2]

/-- The Loewner sandwich transported by the gauge: the quadratic-form key inequality for the
shifted pair `(b + h0, a + h0)` follows from the two Loewner clauses of the unshifted pair. -/
theorem srootNS_shift_key {d : ℕ} (U : Domain d) (a b : CoeffOn U) {D : ℝ}
    (hlo : BlockMatLoewnerLE ((-D) • Book.Ch02.coarseBlockMatrix U a)
      (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
        toFullBlockMat (Book.Ch02.coarseBlockMatrix U a))))
    (hhi : BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (Book.Ch02.coarseBlockMatrix U b) -
        toFullBlockMat (Book.Ch02.coarseBlockMatrix U a)))
      (D • Book.Ch02.coarseBlockMatrix U a))
    {h0 : Mat d} (hh0 : matTranspose h0 = -h0) (X : BlockVec d) :
    |blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
          (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn b hh0)) X) -
        blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
          (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn a hh0)) X)| ≤
      D * blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U
          (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn a hh0)) X) := by
  rw [SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn,
    SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn,
    SuperdiffusionCLT.Section2.Localization.blockVecDot_conj_blockMatMul,
    SuperdiffusionCLT.Section2.Localization.blockVecDot_conj_blockMatMul]
  set Z : BlockVec d := blockMatVecMul (blockG (-h0)) X
  have h1 := hlo Z
  have h2 := hhi Z
  simp only [blockMatVecMul_blockSMul, blockVecDot_smul_right,
    blockVecDot_blockMatVecMul_ofFullBlockMat_sub] at h1 h2
  rw [abs_le]
  constructor <;> linarith only [h1, h2]

/-- **The energy of the cutoff field at a gauge-shifted block vector**: for the point
`(x, y)`, the energy of `bfA_mm(U)` at `G_{-h0}(x, y) = (x, y - h0 x)` is at most
`ρ (u |x|² + 2 l |y|² + 2 l ‖h0‖² |x|²)`. -/
theorem srootNS_blockForm_shift_le_envelope {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (U : Domain d) (omega : ShellSeq d) (mm : ℕ) (h0 : Mat d) (x y : Vec d) :
    blockVecDot (blockMatVecMul (blockG (-h0)) (x, y))
        (blockMatVecMul (Homogenization.coarseBlockMatrix (U : Set (Vec d))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega mm).toCoeffField)
          (blockMatVecMul (blockG (-h0)) (x, y))) ≤
      envelopeRatioOn mm (U : Set (Vec d)) omega *
        (envelopeUpperScalar d nu mm * vecNormSq x +
          2 * envelopeLowerScalar d nu * vecNormSq y +
          2 * envelopeLowerScalar d nu * matrixOperatorNorm h0 ^ 2 * vecNormSq x) := by
  rw [srootNS_blockG_neg_apply]
  refine (srootN3_blockForm_le_envelope hnu U omega mm x (y - matVecMul h0 x)).trans ?_
  have hρ := le_trans zero_le_one (one_le_envelopeRatioOn mm (U : Set (Vec d)) omega)
  have hl := envelopeLowerScalar_pos hnu d
  have h1 := vecNormSq_sub_le y (matVecMul h0 x)
  have h2 := vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq h0 x
  refine mul_le_mul_of_nonneg_left ?_ hρ
  have h3 : vecNormSq (y - matVecMul h0 x) ≤
      2 * (vecNormSq y + matrixOperatorNorm h0 ^ 2 * vecNormSq x) := by
    linarith only [h1, h2]
  have h4 := mul_le_mul_of_nonneg_left h3 hl.le
  linarith only [h4]

/-- **The energy of the shifted field at the scalar test vectors**: the average of the two
energies of `bfA_mm(U)` at `G_{-h0}` applied to `(sa η₁, sb η₂)` and `(sa η₂, sb η₁)` is at most
`ρ (u sa² + 2 l sb² + 2 l sa² ‖h0‖²) / 2`. -/
theorem srootNS_probe_energy_shift_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (U : Domain d) (omega : ShellSeq d) (mm : ℕ) (h0 : Mat d) (sa sb : ℝ) (eta : BlockVec d)
    (heta : SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1) :
    (1 / 2 : ℝ) * blockVecDot (blockMatVecMul (blockG (-h0)) (sa • eta.1, sb • eta.2))
        (blockMatVecMul (Homogenization.coarseBlockMatrix (U : Set (Vec d))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega mm).toCoeffField)
          (blockMatVecMul (blockG (-h0)) (sa • eta.1, sb • eta.2))) +
      (1 / 2 : ℝ) * blockVecDot (blockMatVecMul (blockG (-h0)) (sa • eta.2, sb • eta.1))
        (blockMatVecMul (Homogenization.coarseBlockMatrix (U : Set (Vec d))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega mm).toCoeffField)
          (blockMatVecMul (blockG (-h0)) (sa • eta.2, sb • eta.1))) ≤
      (1 / 2 : ℝ) * (envelopeRatioOn mm (U : Set (Vec d)) omega *
        (envelopeUpperScalar d nu mm * sa ^ 2 + 2 * envelopeLowerScalar d nu * sb ^ 2 +
          2 * envelopeLowerScalar d nu * sa ^ 2 * matrixOperatorNorm h0 ^ 2)) := by
  have hnorm : vecNormSq eta.1 + vecNormSq eta.2 = 1 := by
    have h := heta
    unfold SuperdiffusionCLT.Section2.Carriers.blockVecNorm at h
    exact Real.sqrt_eq_one.1 h
  have h1 := srootNS_blockForm_shift_le_envelope hnu U omega mm h0 (sa • eta.1) (sb • eta.2)
  have h2 := srootNS_blockForm_shift_le_envelope hnu U omega mm h0 (sa • eta.2) (sb • eta.1)
  rw [vecNormSq_smul, vecNormSq_smul] at h1 h2
  have e1 : envelopeRatioOn mm (U : Set (Vec d)) omega *
        (envelopeUpperScalar d nu mm * (sa ^ 2 * vecNormSq eta.1) +
          2 * envelopeLowerScalar d nu * (sb ^ 2 * vecNormSq eta.2) +
          2 * envelopeLowerScalar d nu * matrixOperatorNorm h0 ^ 2 *
            (sa ^ 2 * vecNormSq eta.1)) +
      envelopeRatioOn mm (U : Set (Vec d)) omega *
        (envelopeUpperScalar d nu mm * (sa ^ 2 * vecNormSq eta.2) +
          2 * envelopeLowerScalar d nu * (sb ^ 2 * vecNormSq eta.1) +
          2 * envelopeLowerScalar d nu * matrixOperatorNorm h0 ^ 2 *
            (sa ^ 2 * vecNormSq eta.2)) =
      1 * (envelopeRatioOn mm (U : Set (Vec d)) omega *
        (envelopeUpperScalar d nu mm * sa ^ 2 + 2 * envelopeLowerScalar d nu * sb ^ 2 +
          2 * envelopeLowerScalar d nu * sa ^ 2 * matrixOperatorNorm h0 ^ 2)) := by
    have : vecNormSq eta.2 = 1 - vecNormSq eta.1 := by linarith only [hnorm]
    rw [this]
    ring
  linarith only [h1, h2, e1]

/-- **Near-tail comparison of `J` at a skew shift** (uniform in `h0`): the same
hypotheses and the same `h0`-free `Γ_{1/2}` witness `Y` as the unshifted comparison;
for every constant skew `h0` simultaneously, the shifted fields `b + h0`, `a_mm + h0` have `J`
values at the scalar test vectors within `(u sa² + 2 l sb² + 2 l sa² ‖h0‖²) · Y`. -/
theorem srootNS_nearTail_J_comparison_shift {d : ℕ} [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) {mm n : ℕ} (hnm : n ≤ mm + 1) (V U : Domain d)
    (hV : (V : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (hUV : (U : Set (Vec d)) ⊆ (V : Set (Vec d))) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧
      IsBigO P.toMeasure (gammaSigma (1 / 2)) Y
        (srootN3_tailConst d *
          (nu⁻¹ * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) +
            nu⁻¹ ^ 2 * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) ^ 2)) ∧
      ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, mm < L → ∀ b : CoeffOn U,
        (∀ x ∈ (U : Set (Vec d)), b.toCoeffField x =
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x -
            volumeAverageMat (V : Set (Vec d))
              (fun y => finiteShellIncrement omega mm L y)) →
        ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0) (sa sb : ℝ) (eta : BlockVec d),
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
          |doubledResponseJ U
                (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn b hh0)
                (sa • eta.1, sb • eta.2) (sb • eta.1, sa • eta.2) -
              doubledResponseJ U
                (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
                  (cutoffDomainCoeffOn U hnu omega mm) hh0)
                (sa • eta.1, sb • eta.2) (sb • eta.1, sa • eta.2)| ≤
            (envelopeUpperScalar d nu mm * sa ^ 2 + 2 * envelopeLowerScalar d nu * sb ^ 2 +
              2 * envelopeLowerScalar d nu * sa ^ 2 * matrixOperatorNorm h0 ^ 2) *
              Y omega := by
  obtain ⟨hmeas, hbig⟩ := srootN3_isBigO_nearTailY hPrefix hJ2 hJ3 hJ4 hnu hnm U
  refine ⟨srootN3_nearTailY d nu n mm (U : Set (Vec d)), hmeas, hbig, ?_⟩
  filter_upwards [srootN3_ae_summable_shellCubeDerivNorm hJ3 n] with omega hsum
  intro L hL b hb h0 hh0 sa sb eta heta
  set M : ℝ := SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst d *
    (3 : ℝ) ^ n * srootN3_tailGauge d n mm omega with hMdef
  have hM : ∀ x ∈ (V : Set (Vec d)),
      matrixOperatorNorm (finiteShellIncrement omega mm L x -
        volumeAverageMat (V : Set (Vec d)) (fun y => finiteShellIncrement omega mm L y)) ≤ M := by
    intro x hx
    refine (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le
      omega mm L n V hV x hx).trans ?_
    exact mul_le_mul_of_nonneg_left (srootN3_upperShellDerivGauge_le_tailGauge n mm L omega hsum)
      (mul_nonneg (SuperdiffusionCLT.Section2.Localization.matrixOperatorNorm_diamConst_nonneg d)
        (by positivity))
  obtain ⟨hlo, hhi⟩ := srootN3_nearTail_clauses hnu omega hL.le V U hUV hM b hb
  have hJ := srootNS_doubledResponseJ_sub_le_of_key U
    (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
      (cutoffDomainCoeffOn U hnu omega mm) hh0)
    (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn b hh0)
    (srootNS_shift_key U (cutoffDomainCoeffOn U hnu omega mm) b hlo hhi hh0)
    (sa • eta.1, sb • eta.2) (sb • eta.1, sa • eta.2)
  have hen := srootNS_probe_energy_shift_le hnu U omega mm h0 sa sb eta heta
  dsimp only at hJ
  rw [SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn,
    SuperdiffusionCLT.Section2.Localization.blockVecDot_conj_blockMatMul,
    SuperdiffusionCLT.Section2.Localization.blockVecDot_conj_blockMatMul,
    ← coarseBlockMatrix_domain_coefficientCutoff_eq_ch02 U hnu omega mm] at hJ
  have hW : srootN3_nearTailW d nu n mm omega = nu⁻¹ * M := rfl
  have hD : nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2 =
      srootN3_nearTailW d nu n mm omega + srootN3_nearTailW d nu n mm omega *
        srootN3_nearTailW d nu n mm omega := by
    rw [hW]; ring
  have hD0 : 0 ≤ nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2 := by
    rw [hD]
    have := srootN3_nearTailW_nonneg hnu n mm omega
    positivity
  have hY0 := srootN3_nearTailY_nonneg hnu n mm (U : Set (Vec d)) omega
  have hT0 : 0 ≤ envelopeUpperScalar d nu mm * sa ^ 2 + 2 * envelopeLowerScalar d nu * sb ^ 2 +
      2 * envelopeLowerScalar d nu * sa ^ 2 * matrixOperatorNorm h0 ^ 2 := by
    have := envelopeUpperScalar_pos hnu d mm
    have := envelopeLowerScalar_pos hnu d
    positivity
  have hρ0 := le_trans zero_le_one (one_le_envelopeRatioOn mm (U : Set (Vec d)) omega)
  refine hJ.trans ?_
  have h2 := mul_le_mul_of_nonneg_left hen hD0
  refine h2.trans ?_
  have hYeq : srootN3_nearTailY d nu n mm (U : Set (Vec d)) omega =
      (nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2) * envelopeRatioOn mm (U : Set (Vec d)) omega := by
    rw [hD]; unfold srootN3_nearTailY; ring
  rw [hYeq]
  have hprod : 0 ≤ (nu⁻¹ * M + nu⁻¹ ^ 2 * M ^ 2) * envelopeRatioOn mm (U : Set (Vec d)) omega *
      (envelopeUpperScalar d nu mm * sa ^ 2 + 2 * envelopeLowerScalar d nu * sb ^ 2 +
        2 * envelopeLowerScalar d nu * sa ^ 2 * matrixOperatorNorm h0 ^ 2) := by
    positivity
  nlinarith only [hprod]

/-- The two scalars of `newMixParam_bfAhomPow` at `σ = shom_r`, squared. -/
theorem srootNS_probe_sq_neg_half {sg : ℝ} (hpos : 0 < sg) :
    (sg ^ (-(1 : ℝ) / 2)) ^ 2 = sg⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
    show (-(1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]

theorem srootNS_probe_sq_half {sg : ℝ} (hpos : 0 < sg) :
    (sg ^ ((1 : ℝ) / 2)) ^ 2 = sg := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
    show ((1 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one]

/-- **The shifted near-tail comparison at the test vectors of the paper**, split by the
`h0`-dependence: two `h0`-free measurable `Γ_{1/3}` variables `X1`, `X2` with amplitudes
`(u σ⁻¹ + 2 l σ) · c` and `2 l σ⁻¹ · c` (`c` the amplitude of the unshifted comparison,
`σ = shom_r`), such that for every skew `h0` the shifted `J` difference is at most
`X1 ω + ‖h0‖² X2 ω`. -/
theorem srootNS_nearTail_J_comparison_shift_sigmaBar {d : ℕ} [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) {mm n : ℕ} (hnm : n ≤ mm + 1) (r : ℕ) (V U : Domain d)
    (hV : (V : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (hUV : (U : Set (Vec d)) ⊆ (V : Set (Vec d))) :
    ∃ X1 X2 : ShellSeq d → ℝ, Measurable X1 ∧ Measurable X2 ∧
      IsBigO P.toMeasure (gammaSigma (1 / 3)) X1
        ((envelopeUpperScalar d nu mm * (sigmaBarInfinite nu r P)⁻¹ +
            2 * envelopeLowerScalar d nu * sigmaBarInfinite nu r P) *
          (srootN3_tailConst d *
            (nu⁻¹ * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) +
              nu⁻¹ ^ 2 * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) ^ 2))) ∧
      IsBigO P.toMeasure (gammaSigma (1 / 3)) X2
        ((2 * envelopeLowerScalar d nu * (sigmaBarInfinite nu r P)⁻¹) *
          (srootN3_tailConst d *
            (nu⁻¹ * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) +
              nu⁻¹ ^ 2 * ((3 : ℝ) ^ n * ((3 : ℝ) ^ mm)⁻¹) ^ 2))) ∧
      ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, mm < L → ∀ b : CoeffOn U,
        (∀ x ∈ (U : Set (Vec d)), b.toCoeffField x =
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x -
            volumeAverageMat (V : Set (Vec d))
              (fun y => finiteShellIncrement omega mm L y)) →
        ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0) (eta : BlockVec d),
          SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
          |doubledResponseJ U
                (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn b hh0)
                (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P
                  (-(1 : ℝ) / 2) eta)
                (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P
                  ((1 : ℝ) / 2) eta) -
              doubledResponseJ U
                (SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
                  (cutoffDomainCoeffOn U hnu omega mm) hh0)
                (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P
                  (-(1 : ℝ) / 2) eta)
                (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P
                  ((1 : ℝ) / 2) eta)| ≤
            X1 omega + matrixOperatorNorm h0 ^ 2 * X2 omega := by
  obtain ⟨Y, hYm, hYbig, hae⟩ :=
    srootNS_nearTail_J_comparison_shift hPrefix hJ2 hJ3 hJ4 hnu hnm V U hV hUV
  have hsg := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  have hu := envelopeUpperScalar_pos hnu d mm
  have hl := envelopeLowerScalar_pos hnu d
  have hT1 : 0 ≤ envelopeUpperScalar d nu mm * (sigmaBarInfinite nu r P)⁻¹ +
      2 * envelopeLowerScalar d nu * sigmaBarInfinite nu r P := by positivity
  have hT2 : 0 ≤ 2 * envelopeLowerScalar d nu * (sigmaBarInfinite nu r P)⁻¹ := by positivity
  refine ⟨fun omega => (envelopeUpperScalar d nu mm * (sigmaBarInfinite nu r P)⁻¹ +
      2 * envelopeLowerScalar d nu * sigmaBarInfinite nu r P) * Y omega,
    fun omega => (2 * envelopeLowerScalar d nu * (sigmaBarInfinite nu r P)⁻¹) * Y omega,
    hYm.const_mul _, hYm.const_mul _, ?_, ?_, ?_⟩
  · exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_of_exponent_le (by norm_num)
      (hYbig.const_mul hT1)
  · exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_of_exponent_le (by norm_num)
      (hYbig.const_mul hT2)
  · filter_upwards [hae] with omega hom L hL b hb h0 hh0 eta heta
    rw [srootN3_bfAhomPow_neg_half, srootN3_bfAhomPow_half]
    have h := hom L hL b hb h0 hh0 (sigmaBarInfinite nu r P ^ (-(1 : ℝ) / 2))
      (sigmaBarInfinite nu r P ^ ((1 : ℝ) / 2)) eta heta
    rw [srootNS_probe_sq_neg_half hsg, srootNS_probe_sq_half hsg] at h
    refine h.trans (le_of_eq ?_)
    ring

/-! ## Satisfiability of the non-law hypotheses -/

end

end SuperdiffusionCLT.Section4.MinimalScales
