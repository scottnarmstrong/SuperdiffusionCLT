/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayB
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayD
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import Homogenization.CoarseGraining.OriginCubeOpenBridge
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageFinal

/-!
# The half-open / open cube passage, `hY` closed, and the degenerate `hR`

The localization-average carriers of this development are stated on the
half-open triadic cube `Homogenization.cubeSet Q`, while the ellipticity
statement that `hY` invokes -- the printed display `e.Enaught.vs.A.and.Ahom`
-- is stated on the open cube `Homogenization.openCubeSet Q`.  This
module proves the passage between the two.

## Part 1: the passage, and `hY` with no residual

`cubeSet Q` and `openCubeSet Q` differ only on the boundary of the cube, a
Lebesgue-null set.  Two consequences are proved in full generality:

* `localizationCubePassage_volumeAverage`: the `volumeAverage` of *any*
  real-valued function agrees on the two cubes;
* `localizationCubePassage_coarseBlockMatrix`: the coarse block matrix of *any*
  coefficient field agrees on the two cubes, for `d >= 1`.

The second is the form the printed statement needs: the carrier `localizationY nu l R` and
its open-cube twin `localizationYOnOpenCube nu l R` are the *same function of the shell
sequence*, because they evaluate the same coarse block matrix at sets that differ by a null
boundary.  Hence `Y_z^2` is `Γ_{1/2}` at the explicit constant `orliczProductConst 1 1` from
the four shell-law binders alone.

## Part 2: `hR` in the degenerate case

The printed display `hR` is
`R_z <= O_{Γ_{1/2}}(C nu^{-2}((1 v l)^2 + (L-l)^2)|P|^4)`.  In the degenerate case `L <= l`
the gauge vector `G_{-h_z}P` collapses to `P` (the finite shell increment over
`(l, L]` vanishes), and `hR` then holds *unconditionally* at the `d`-only
constant `(1 + 2 C)^2` (`localizationR_isBigO_of_not_lt`), with no printed input
at all -- the case in which the printed proof says the `(L-l)` term vanishes.

## Main results

* `localizationCubePassage_volumeAverage`, `localizationCubePassage_coarseBlockMatrix`,
  `localizationCubePassage_coarseBlockMatrix_toCoeffField`: the cube passage.
* `localizationCubePassage_localizationY`: the carrier identification.
* `localizationY_isBigO_gammaSigma_one_of_lawBinders`,
  `localizationY_sq_isBigO_gammaSigma_half_of_lawBinders`,
  `localizationY_sq_isBigO_on_grid_of_lawBinders`: `hY` from the law binders.
* `localizationR_isBigO_of_not_lt`: `hR` for `L <= l`.

No statement here is stronger than the print.  The index `1/2` is the printed
one, produced by the printed multiplication rule at `(1,1)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## Part 1: the general half-open / open cube passage -/

/-- **The cube passage for volume averages.**  The half-open cube `cubeSet Q` and
the open cube `openCubeSet Q` differ by the boundary of the cube, which is
Lebesgue-null, so the `volumeAverage` of an arbitrary real-valued function agrees
on the two sets:

  `volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f`.

The statement is general in the cube `Q` and the function `f`, and needs no
condition on `d`.  It is the measure-theoretic half of the passage; the coarse
block matrix is the application below. -/
theorem localizationCubePassage_volumeAverage (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  simp [volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- **The cube passage for the coarse block matrix.**  For a triadic cube `Q` and
an arbitrary coefficient field `a`, the coarse block matrix is the same at the
half-open and at the open cube:

  `coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a`.

Every entry is a volume average of a product of entries of the coefficient field
times centred coordinates, so the previous passage applies entrywise -- the
centred coordinate vanishes on the boundary of the cube anyway.  This is the
form in which the passage is needed: `localizationY` and `localizationYOnOpenCube`
differ only in this argument. -/
theorem localizationCubePassage_coarseBlockMatrix [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) :
    coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a :=
  coarseBlockMatrix_eq_of_mu_eq
    (U := cubeSet Q) (V := openCubeSet Q) (a := a) (b := a)
    (fun P => Mu_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) P a)

/-- **The passage at a `toCoeffField`-shaped argument**, the exact form in which
the carriers of this development present their coefficient field. -/
theorem localizationCubePassage_coarseBlockMatrix_toCoeffField [NeZero d]
    (Q : TriadicCube d) (a : RegCoeffField d) :
    coarseBlockMatrix (cubeSet Q) a.toCoeffField =
      coarseBlockMatrix (openCubeSet Q) a.toCoeffField :=
  localizationCubePassage_coarseBlockMatrix Q a.toCoeffField

/-! ## Part 1: the carrier identification that discharges `hY`'s residual -/

/-- **The half-open / open identification of the `hY` carrier.**  The carrier
`localizationY nu l R` of this development and the open-cube twin
`localizationYOnOpenCube nu l R` at which the ellipticity statement is stated
are the *same function*: both are the operator norm of the envelope rescaling of
the same coarse block matrix, evaluated at sets that differ by a null boundary.

The half-open and open cubes differ only by a null boundary, so no cube-passage hypothesis
is needed. -/
theorem localizationCubePassage_localizationY [NeZero d] (nu : ℝ) (l : ℕ)
    (R : TriadicCube d) (omega : ShellSeq d) :
    localizationY nu l R omega = localizationYOnOpenCube (d := d) nu l R omega :=
  congrArg (fun M => blockMatrixOperatorNorm (envelopeRescale d nu l M))
    (localizationCubePassage_coarseBlockMatrix_toCoeffField R
      (coefficientCutoff nu omega l))

/-- **The printed `Γ₁` display of `e.Enaught.vs.A.and.Ahom` at
the carrier `localizationY`, unconditionally.**  The open-cube statement
`isBigO_gammaSigma_one_localizationYOnOpenCube` transported along the passage. -/
theorem localizationY_isBigO_gammaSigma_one_of_lawBinders [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l : ℕ) (R : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (localizationY nu l R) 1 :=
  IndependentSums.IsBigO.of_abs_le
    (isBigO_gammaSigma_one_localizationYOnOpenCube P hnu hPrefix hJ2 hJ3 hJ4 l R)
    (fun omega => by rw [localizationCubePassage_localizationY nu l R omega])

/-- **`hY` with no residual: `Y_z^2 = O_{Gamma_{1/2}}(orliczProductConst 1 1)`**.
The four shell-law binders and `0 < nu` are the entire
hypothesis list; the amplitude is the explicit `orliczProductConst 1 1` produced
by the printed multiplication rule `e.multGammasig` at `(1,1)` from the printed
`Γ₁` amplitude `1`. -/
theorem localizationY_sq_isBigO_gammaSigma_half_of_lawBinders [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l : ℕ) (R : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (fun omega : ShellSeq d => localizationY nu l R omega ^ 2)
      (SuperdiffusionCLT.Probability.orliczProductConst 1 1) := by
  have h := localizationY_sq_isBigO_gammaSigma_half P l R
    (by norm_num : (0 : ℝ) ≤ 1)
    (localizationY_isBigO_gammaSigma_one_of_lawBinders P hnu hPrefix hJ2 hJ3 hJ4 l R)
  simpa using h

/-- **`hY` on the printed lattice, from the law binders.**  The exact binder
shape of the assembly's `hY` hypothesis, with the per-cube cube
passage no longer a hypothesis and no numeric comparison to be supplied: any
envelope `KY >= orliczProductConst 1 1` works, and `KY` is a constant, not a
function of the scales. -/
theorem localizationY_sq_isBigO_on_grid_of_lawBinders [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l m n : ℕ) {KY : ℝ}
    (hAmp : SuperdiffusionCLT.Probability.orliczProductConst 1 1 ≤ KY) :
    ∀ R ∈ localizationAverageGrid d m n,
      IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2))
        (fun omega : ShellSeq d => localizationY nu l R omega ^ 2) KY :=
  fun R _ => IndependentSums.IsBigO.mono_scale
    (localizationY_sq_isBigO_gammaSigma_half_of_lawBinders P hnu hPrefix hJ2 hJ3 hJ4
      l R) hAmp

/-- The assembly's `hY` binder at the rule's own constant `KY = 4`. -/
theorem localizationY_sq_isBigO_on_grid_of_lawBinders_four [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) {nu : ℝ} (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (l m n : ℕ) :
    ∀ R ∈ localizationAverageGrid d m n,
      IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2))
        (fun omega : ShellSeq d => localizationY nu l R omega ^ 2)
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1) :=
  localizationY_sq_isBigO_on_grid_of_lawBinders P hnu hPrefix hJ2 hJ3 hJ4 l m n le_rfl

/-! ## Part 2: a deterministic amplitude is a tail bound at that amplitude -/

/-- **A random variable bounded by a constant is `Gamma_sigma` at that constant.**
The tail event `{|X| > A t}` is empty for `t >= 1` because `|X| <= A <= A t`, so
the tail inequality holds at every index and every exponent.

This is the `hR`-side analogue of a bounded-function Orlicz bound, which the
weak-Orlicz API does not provide: `IsBigOWith.of_le` and `mono_scale`
compare two *tail bounds*, never a deterministic bound against a tail.  The
statement is general in `sigma`, the measure and `X`. -/
theorem isBigO_gammaSigma_of_abs_le_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {σ A : ℝ} {X : Ω → ℝ} (hA : 0 ≤ A)
    (hX : ∀ ω, |X ω| ≤ A) :
    IndependentSums.IsBigO μ (IndependentSums.gammaSigma σ) X A := by
  intro t ht
  have hAt : A ≤ A * t := by nlinarith only [hA, ht]
  have hempty : IndependentSums.upperTailEvent (fun ω => |X ω|) (A * t) = ∅ := by
    ext ω
    refine iff_false_intro ?_
    rw [IndependentSums.mem_upperTailEvent]
    exact not_lt.mpr (le_trans (hX ω) hAt)
  rw [hempty]
  simp only [MeasureTheory.Measure.real, MeasureTheory.measure_empty, ENNReal.toReal_zero]
  exact inv_nonneg.mpr (Real.exp_pos _).le

/-! ## Part 2: `hR` at the constant determined by its own route -/

/-- **The printed envelope scalar folds into `(1 + 2C) nu^{-1} (1 v l)`.**  The
printed bound `|bfE_l| <= nu + 2C nu^{-1}(1 v l)` (`envelopeUpperScalar`) is
dominated by the unified form with `(1 v l)` rather than `(l)`, for `nu <= 1`.
This is the arithmetic half of the printed enlargement `C -> (1 + 2C)`; it
differs from `envelopeUpperScalar_le_nuInv_mul` only in keeping the `1 v l`
that `l = 0` needs. -/
theorem envelopeUpperScalar_le_nuInv_mul_max {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (l : ℕ) :
    envelopeUpperScalar d nu l ≤
      (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ) := by
  have hmaxl : (1 : ℝ) ≤ max 1 (l : ℝ) := le_max_left _ _
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hnu_le : nu ≤ nu⁻¹ * max 1 (l : ℝ) := by
    calc nu ≤ nu⁻¹ := le_trans hnu1 hnuinv1
      _ = nu⁻¹ * 1 := (mul_one _).symm
      _ ≤ nu⁻¹ * max 1 (l : ℝ) := mul_le_mul_of_nonneg_left hmaxl (by positivity)
  have hsplit : envelopeUpperScalar d nu l ≤
      (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ) := by
    unfold envelopeUpperScalar
    have hrearr : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (l : ℝ) =
        (2 * cutoffEnvelopeConst d) * (nu⁻¹ * max 1 (l : ℝ)) := by ring
    rw [hrearr]
    nlinarith only [hnu_le, hnu]
  exact hsplit

/-! ## Part 2: `hR` unconditionally in the degenerate case `L <= l`

The printed proof reads `hR` off `e.Enaught.mixing` in two cases, and in the case
`L = l` the `(L-l)` term of the amplitude vanishes.  That case is not merely
simpler: the finite shell increment over the empty index set `(l, L]` is zero, so
the gauge vector `G_{-h_z}P` *is* `P`, and `R_z = W_z^2` is bounded by the
envelope scalar squared times `|P|^4` with no randomness left.  The result below
therefore needs no printed input at all, and its constant is `d`-only. -/

/-- **The gauge vector is `P` when the shell increment is empty.**  For `L <= l`
the finite shell increment over `(l, L]` vanishes, hence so does its volume
average `h_z`, and the gauge `G_{-h_z}` is the identity:
`G_{-h_z}P = G_0 P = P`. -/
theorem localizationGaugeVector_eq_self_of_not_lt {l L : ℕ} (hlL : ¬ l < L)
    (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationGaugeVector l L R Pvec omega = Pvec := by
  have hinc : finiteShellIncrement omega l L = 0 := by
    rw [finiteShellIncrement, Finset.Ioc_eq_empty_iff.mpr hlL]
    simp
  have havg : volumeAverageMat (cubeSet R) (fun y => finiteShellIncrement omega l L y) = 0 := by
    have hzero : (fun y => finiteShellIncrement omega l L y) = (0 : Vec d → Mat d) := by
      funext y
      rw [hinc]
      exact RegCoeffField.zero_apply y
    rw [hzero]
    ext i j
    simp [volumeAverageMat, volumeAverage]
  unfold localizationGaugeVector
  rw [havg, neg_zero, blockG_zero, Carriers.blockMatVecMul_blockIdentity]

/-- **`W_z` is bounded by the envelope scalar times `|P|^2` in the degenerate
case.**  With the gauge vector equal to `P`, the envelope bound of
`e.Enaught.mixing` alone gives `W_z = |bfE_l^{1/2}P|^2 <= |bfE_l| |P|^2`; no
gauge-vector input is consumed. -/
theorem localizationW_le_of_not_lt {nu : ℝ} (hnu : 0 < nu) {l L : ℕ} (hlL : ¬ l < L)
    (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationW nu l L R Pvec omega ≤ envelopeUpperScalar d nu l * blockVecDot Pvec Pvec := by
  have hPnn : 0 ≤ blockVecNorm Pvec := blockVecNorm_nonneg Pvec
  rw [localizationW_eq_envelopeBlockMat hnu l L R Pvec omega,
    localizationGaugeVector_eq_self_of_not_lt hlL R Pvec omega]
  calc blockVecDot Pvec (blockMatVecMul (envelopeBlockMat d nu l) Pvec)
      ≤ |blockVecDot Pvec (blockMatVecMul (envelopeBlockMat d nu l) Pvec)| := le_abs_self _
    _ ≤ blockVecNorm Pvec * blockVecNorm (blockMatVecMul (envelopeBlockMat d nu l) Pvec) :=
        abs_blockVecDot_le_blockVecNorm_mul _ _
    _ ≤ blockVecNorm Pvec *
          (blockMatrixOperatorNorm (envelopeBlockMat d nu l) * blockVecNorm Pvec) :=
        mul_le_mul_of_nonneg_left (blockVecNorm_blockMatVecMul_le _ _) hPnn
    _ ≤ blockVecNorm Pvec * (envelopeUpperScalar d nu l * blockVecNorm Pvec) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (blockMatrixOperatorNorm_envelopeBlockMat_le hnu d l) hPnn)
          hPnn
    _ = envelopeUpperScalar d nu l * blockVecDot Pvec Pvec := by
        rw [← blockVecNorm_sq]
        ring

/-- **The degenerate amplitude comparison.**  Squaring the envelope bound gives
`(nu + 2C nu^{-1}(1 v l))^2 |P|^4`, dominated by the printed `hR` amplitude at the
`d`-only constant `(1 + 2C)^2` once `(L-l)` is zero.  No hypothesis on the scales
beyond `L <= l`. -/
theorem envelopeUpperScalar_sq_mul_le_fourthAmplitude_of_not_lt {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {l L : ℕ} (hlL : ¬ l < L) (Pvec : BlockVec d) :
    envelopeUpperScalar d nu l ^ 2 * (blockVecDot Pvec Pvec) ^ 2 ≤
      localizationAverageT1FourthAmplitude ((1 + 2 * cutoffEnvelopeConst d) ^ 2) nu l L Pvec := by
  have hsub : ((L - l : ℕ) : ℝ) = 0 := by
    rw [Nat.sub_eq_zero_of_le (not_lt.mp hlL)]
    simp
  have hsub2 : ((L - l : ℕ) : ℝ) ^ 2 = 0 := by
    rw [hsub]
    simp
  have henv := envelopeUpperScalar_le_nuInv_mul_max (d := d) hnu hnu1 l
  have hk : 0 ≤ (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith only [cutoffEnvelopeConst_pos d]) (inv_nonneg.mpr hnu.le))
      (le_trans zero_le_one (le_max_left _ _))
  have henv0 : 0 ≤ envelopeUpperScalar d nu l := (envelopeUpperScalar_pos hnu d l).le
  have hle2 : envelopeUpperScalar d nu l ^ 2 ≤
      ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ)) ^ 2 := by
    simpa [pow_two] using mul_le_mul henv henv henv0 hk
  calc envelopeUpperScalar d nu l ^ 2 * (blockVecDot Pvec Pvec) ^ 2
      ≤ ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ)) ^ 2 *
          (blockVecDot Pvec Pvec) ^ 2 :=
        mul_le_mul_of_nonneg_right hle2 (sq_nonneg _)
    _ = localizationAverageT1FourthAmplitude ((1 + 2 * cutoffEnvelopeConst d) ^ 2) nu l L Pvec := by
        unfold localizationAverageT1FourthAmplitude
        rw [hsub2, add_zero, Real.rpow_neg hnu.le 2, Real.rpow_two, ← inv_pow]
        ring

/-- **`hR` unconditionally when `L <= l`, at a `d`-only constant.**  In the
degenerate case the fourth power of the gauge length is deterministically bounded
by `(1 + 2C)^2 nu^{-2}(1 v l)^2|P|^4`, which is the printed `hR` amplitude with
the `(L-l)` term vanished.  By `isBigO_gammaSigma_of_abs_le_const` this
deterministic bound *is* the `Gamma_{1/2}` tail bound: no printed input, no
gauge-vector display and no scale-dependent constant is consumed here.

This is the case in which the printed proof says the `(L-l)`
term disappears; the `d`-only constant is the printed `C` of
`e.Enaught.mixing` enlarged to `1 + 2C` and squared. -/
theorem localizationR_isBigO_of_not_lt (P : ProbabilityMeasure (ShellSeq d))
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {l L : ℕ} (hlL : ¬ l < L)
    (R : TriadicCube d) (Pvec : BlockVec d) :
    IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma ((1 : ℝ) / 2)) (localizationR nu l L R Pvec)
      (localizationAverageT1FourthAmplitude ((1 + 2 * cutoffEnvelopeConst d) ^ 2) nu l L Pvec) := by
  refine isBigO_gammaSigma_of_abs_le_const
    (localizationAverageT1FourthAmplitude_nonneg (sq_nonneg _) hnu.le l L Pvec)
    (fun omega => ?_)
  rw [abs_of_nonneg (show 0 ≤ localizationR nu l L R Pvec omega from sq_nonneg _)]
  unfold localizationR
  have hW := localizationW_le_of_not_lt hnu hlL R Pvec omega
  have hW0 : 0 ≤ localizationW nu l L R Pvec omega := localizationW_nonneg nu l L R Pvec omega
  have hmul := mul_self_le_mul_self hW0 hW
  have heq : (envelopeUpperScalar d nu l * blockVecDot Pvec Pvec) *
      (envelopeUpperScalar d nu l * blockVecDot Pvec Pvec) =
      envelopeUpperScalar d nu l ^ 2 * (blockVecDot Pvec Pvec) ^ 2 := by ring
  rw [heq] at hmul
  simpa [pow_two] using hmul.trans
    (envelopeUpperScalar_sq_mul_le_fourthAmplitude_of_not_lt hnu hnu1 hlL Pvec)

end SuperdiffusionCLT.Section2.Localization
