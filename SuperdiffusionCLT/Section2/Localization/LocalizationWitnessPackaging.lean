/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.ShellWindowDomination
public import SuperdiffusionCLT.Section2.Cutoff.CoefficientCutoffAPI
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.OrliczPower

/-!
# The witness packaging of the first two conjuncts of the cutoff localization estimate

The packaging step of the printed proof of `l.localization`:
the pointwise relative bound `theta = nu⁻¹ M` of the volume-average-centered
cutoff perturbation (`relSkewBound_centeredCutoffPair` of
`CenteredIncrementQuadratic`, with `M` the operator-norm bound of
`ShellWindowDomination` and the gauge of `e.nabla.kmn.Linfty`) is turned into
the two random witnesses of the statement
`Frozen.Section2.cutoff_localization`: the gauge
`theta = nu⁻¹ (d³ √d) 3^n G`, the printed bookkeeping constant
`D = theta (1 + theta)`, the sandwich witness
`X := 2 D`, and its square root `Y := sqrt X`, of the size
`sqrt c` that the `e.skbounds` reading produces from the
same `D`.

Proved here:

* measurability of the sandwich witness, from the measurable carrier
  `measurable_upperShellDerivGauge` of `e.nabla.kmn.Linfty`;
* the `Γ₁` tail bound of `X` at the rate
  `localizationConst d * nu^(-2) * 3^(-(m-n))` and of `Y` at the rate
  `localizationSkewConst d * nu^(-2) * 3^(-(m-n)/2)`, by the `O_{Γ_σ}`
  algebra: the `Γ₂` gauge bound `isBigOWith_gammaSigma_upperShellDerivGauge`,
  the index weakening `isBigO_gammaSigma_of_exponent_le`, the power rule
  `isBigO_gammaSigma_rpow_fwd` / `isBigOWith_gammaSigma_rpow_rev` and the
  two-term triangle `isBigO_gammaSigma_add_of_isBigO`;
* the packaging statement `localizationConjunct1`, which assembles the first conjunct
  (witness, measurability, tail bound, and the Loewner clauses) of the statement, with the
  Loewner clauses supplied as a hypothesis.

Not treated here: the production of the four `MatLoewnerLE` clauses and of the
bilinear clause from the block-sandwich engine (`BlockSandwichExtraction`,
`BlockLoewnerCongruence`) at the cutoff pair, the instantiation of
`e.localization.A` in the proof of `l.localization`.  In the packaging
statement those clauses are hypotheses about the witnesses of this file.

## Main definitions

* `gaugeAmplitudeConst`, `localizationConst`, `localizationSkewConst`: the
  explicit constants of the two rates.
* `localizationTheta`, `localizationD`, `localizationWitness`,
  `localizationSkewWitness`: the witnesses.

## Main results

* `measurable_localizationWitness`.
* `localizationWitness_pair_isBigO`: the two `Γ₁` tail bounds at the
  rates `localizationConst` and `localizationSkewConst`.
* `localizationConjunct1`: the first conjunct of the statement, from the corresponding
  clauses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The real-arithmetic helpers -/

/-- `3^(-a) ≤ 1` in the `ℝ`-power notation of the rates. -/
private theorem three_rpow_sub_le_one (a : ℕ) :
    (3 : ℝ) ^ (-((a : ℕ) : ℝ)) ≤ 1 := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  exact (inv_le_one₀ (pow_pos (by norm_num : (0 : ℝ) < 3) a)).2
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))

/-- `(3^m)⁻¹ · 3^n = 3^(-(m-n))`, the absorption of the `3^n` prefactor of the
increment-level bound into the printed rate `3^(-(m-n))`. -/
private theorem three_pow_nat_sub_of_le {n m : ℕ} (hnm : n ≤ m) :
    ((3 : ℝ) ^ m)⁻¹ * (3 : ℝ) ^ n = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hexp : ((n : ℕ) : ℝ) - ((m : ℕ) : ℝ) = -(((m - n : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hnm]
    ring
  rw [← Real.rpow_natCast 3 m, ← Real.rpow_natCast 3 n, inv_mul_eq_div,
    ← Real.rpow_sub h3, hexp]

/-- The `3^n`-first form of `three_pow_nat_sub_of_le`. -/
private theorem three_pow_nat_sub {n m : ℕ} (hnm : n ≤ m) :
    (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹ = (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ))) := by
  rw [mul_comm, three_pow_nat_sub_of_le hnm]

/-- `sqrt (3^(-a)) = 3^(-a/2)`. -/
private theorem sqrt_three_rpow_sub (a : ℕ) :
    Real.sqrt ((3 : ℝ) ^ (-((a : ℕ) : ℝ))) = (3 : ℝ) ^ (-(((a : ℕ) : ℝ) / 2)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h3]
  rw [show ((-((a : ℕ) : ℝ)) * (1 / 2 : ℝ)) = -(((a : ℕ) : ℝ) / 2) from by ring]

/-- `nu^(-2) = nu⁻¹ · nu⁻¹`. -/
private theorem rpow_neg_two_of_pos {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
  rw [Real.rpow_neg hnu.le, Real.rpow_two, pow_two, mul_inv]

/-! ## The bookkeeping inequalities -/

/-- The key bookkeeping inequality of the printed step `e.mclDsizebounds`: the `theta²` term is
absorbed into the printed rate
because `3^(-(m-n)) ≤ 1` and `nu ≤ 1`. -/
private theorem ampSum_le (nu K T : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hK : 0 ≤ K) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ) ≤
      (nu⁻¹ * nu⁻¹) * (K + K ^ 2) * T := by
  have hB1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hB1' : nu⁻¹ ≤ nu⁻¹ * nu⁻¹ := by
    have q : nu⁻¹ * 1 ≤ nu⁻¹ * nu⁻¹ :=
      mul_le_mul_of_nonneg_left hB1 (inv_nonneg.2 hnu.le)
    rwa [mul_one] at q
  have hTT : T * T ≤ T :=
    (mul_le_mul_of_nonneg_right hT1 hT0).trans (by rw [one_mul])
  have h1 : nu⁻¹ * K * T ≤ (nu⁻¹ * nu⁻¹) * K * T := by
    refine mul_le_mul_of_nonneg_right ?_ hT0
    exact mul_le_mul_of_nonneg_right hB1' hK
  have h2 : (nu⁻¹ * K * T) ^ (2 : ℝ) ≤ (nu⁻¹ * nu⁻¹) * (K * K) * T := by
    rw [Real.rpow_two,
      show (nu⁻¹ * K * T) ^ 2 = (nu⁻¹ * nu⁻¹) * (K * K) * (T * T) from by ring]
    exact mul_le_mul_of_nonneg_left hTT
      (mul_nonneg (mul_nonneg (inv_nonneg.2 hnu.le) (inv_nonneg.2 hnu.le))
        (mul_nonneg hK hK))
  linarith only [h1, h2]

/-- The scalar-factor form of `ampSum_le`, in the `2 * (gammaTriangleConst 1 * _)`
association of the triangle output. -/
private theorem amp_le (nu K T : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hK : 0 ≤ K) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    2 * (gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ))) ≤
      2 * gammaTriangleConst 1 * (K + K ^ 2) * (nu⁻¹ * nu⁻¹) * T := by
  have key := ampSum_le nu K T hnu hnu1 hK hT0 hT1
  have hg0 : 0 ≤ 2 * gammaTriangleConst 1 :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) gammaTriangleConst_pos.le
  have hassoc : 2 * (gammaTriangleConst 1 *
        (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)))
      = 2 * gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)) := by ring
  rw [hassoc]
  calc 2 * gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ))
      ≤ 2 * gammaTriangleConst 1 * ((nu⁻¹ * nu⁻¹) * (K + K ^ 2) * T) :=
        mul_le_mul_of_nonneg_left key hg0
    _ = 2 * gammaTriangleConst 1 * (K + K ^ 2) * (nu⁻¹ * nu⁻¹) * T := by ring

/-- The squared form of the same bookkeeping, for the square-root route to the
witness `Y = sqrt X`: the square of the printed skew rate dominates the
triangle amplitude, because `3^(-(m-n)) ≤ 1` and `nu ≤ 1`. -/
private theorem ampSq_le (nu K T : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hK : 0 ≤ K) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    2 * (gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ))) ≤
      (2 * gammaTriangleConst 1 * (K + K ^ 2)) * ((nu⁻¹ * nu⁻¹) ^ 2) * T := by
  have key := ampSum_le nu K T hnu hnu1 hK hT0 hT1
  have hg0 : 0 ≤ 2 * gammaTriangleConst 1 :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) gammaTriangleConst_pos.le
  have hB1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hB2 : (1 : ℝ) ≤ (nu⁻¹ * nu⁻¹) := by
    have q : (1 : ℝ) * 1 ≤ nu⁻¹ * nu⁻¹ :=
      mul_le_mul hB1 hB1 zero_le_one (inv_nonneg.2 hnu.le)
    rwa [one_mul] at q
  have hB2' : (nu⁻¹ * nu⁻¹) ≤ (nu⁻¹ * nu⁻¹) ^ 2 := by
    have q : (nu⁻¹ * nu⁻¹) * 1 ≤ (nu⁻¹ * nu⁻¹) * (nu⁻¹ * nu⁻¹) :=
      mul_le_mul_of_nonneg_left hB2
        (mul_nonneg (inv_nonneg.2 hnu.le) (inv_nonneg.2 hnu.le))
    rw [mul_one] at q
    rwa [pow_two]
  have hQ : (nu⁻¹ * nu⁻¹) * (K + K ^ 2) * T ≤ (nu⁻¹ * nu⁻¹) ^ 2 * (K + K ^ 2) * T := by
    refine mul_le_mul_of_nonneg_right ?_ hT0
    exact mul_le_mul_of_nonneg_right hB2' (add_nonneg hK (sq_nonneg K))
  have hassoc : 2 * (gammaTriangleConst 1 *
        (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)))
      = 2 * gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)) := by ring
  rw [hassoc]
  calc 2 * gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ))
      ≤ 2 * gammaTriangleConst 1 * ((nu⁻¹ * nu⁻¹) * (K + K ^ 2) * T) :=
        mul_le_mul_of_nonneg_left key hg0
    _ ≤ 2 * gammaTriangleConst 1 * ((nu⁻¹ * nu⁻¹) ^ 2 * (K + K ^ 2) * T) :=
        mul_le_mul_of_nonneg_left hQ hg0
    _ = (2 * gammaTriangleConst 1 * (K + K ^ 2)) * ((nu⁻¹ * nu⁻¹) ^ 2) * T := by ring

/-! ## The constants -/

/-- The `d`-part of the amplitude of `theta`: the operator-norm diameter
constant of the increment-level volume-average oscillation
(`matrixOperatorNorm_diamConst`, the deterministic half of `e.Tsizebounds`)
times the `Γ₂` triangle constant of `e.nabla.kmn.Linfty`. -/
def gaugeAmplitudeConst (d : ℕ) : ℝ :=
  matrixOperatorNorm_diamConst d * gammaTriangleConst 2

theorem gaugeAmplitudeConst_nonneg (d : ℕ) : 0 ≤ gaugeAmplitudeConst d :=
  mul_nonneg (matrixOperatorNorm_diamConst_nonneg d) gammaTriangleConst_pos.le

/-- The operator-norm diameter constant is positive in positive dimension. -/
private theorem matrixOperatorNorm_diamConst_pos {d : ℕ} (hd : 0 < d) :
    0 < matrixOperatorNorm_diamConst d := by
  unfold matrixOperatorNorm_diamConst
  exact mul_pos (pow_pos (by exact_mod_cast hd) 3)
    (Real.sqrt_pos.mpr (by exact_mod_cast hd))

theorem gaugeAmplitudeConst_pos {d : ℕ} (hd : 0 < d) : 0 < gaugeAmplitudeConst d :=
  mul_pos (matrixOperatorNorm_diamConst_pos hd) gammaTriangleConst_pos

/-- The printed constant of `e.localization.s.star`: twice the `Γ₁` triangle
constant times the square-completed amplitude `K + K²` of `theta (1 + theta)`,
with `K = gaugeAmplitudeConst d` the `d`-part.  It depends only on the
dimension, as the outermost binder of the statement demands. -/
def localizationConst (d : ℕ) : ℝ :=
  2 * gammaTriangleConst 1 *
    (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2)

theorem localizationConst_nonneg (d : ℕ) : 0 ≤ localizationConst d := by
  have h := gaugeAmplitudeConst_nonneg d
  unfold localizationConst
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) gammaTriangleConst_pos.le)
    (add_nonneg h (sq_nonneg (gaugeAmplitudeConst d)))

/-- The printed constant of `e.skbounds`, the square root of the printed
constant of `e.localization.s.star`: the witness `Y = sqrt X` has exactly the
square-root rate. -/
def localizationSkewConst (d : ℕ) : ℝ :=
  Real.sqrt (2 * gammaTriangleConst 1 *
    (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2))

theorem localizationSkewConst_nonneg (d : ℕ) : 0 ≤ localizationSkewConst d :=
  Real.sqrt_nonneg _

/-! ## The witnesses -/

/-- The pointwise relative bound `theta` of the printed proof:
`nu⁻¹` times the operator-norm bound of the
volume-average-centered finite shell increment, the latter being `d³ √d · 3^n`
times the upper-shell gauge `G = ∑_{k ∈ (m, L]} ‖∇ j_k‖_{L^∞(cu_n)}` of
`e.nabla.kmn.Linfty`. -/
def localizationTheta (nu : ℝ) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
    upperShellDerivGauge n m L omega)

/-- The printed bookkeeping constant `D = theta (1 + theta)`,
as a function of the shell sequence. -/
def localizationD (nu : ℝ) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  localizationTheta nu n m L omega * (1 + localizationTheta nu n m L omega)

/-- The sandwich witness of `e.localization.s.star`: `X := 2 D`. -/
def localizationWitness (nu : ℝ) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  2 * localizationD nu n m L omega

/-- The skew witness of `e.skbounds`: `Y := sqrt X`, the square root of the
sandwich witness, matching the printed reading `Y = √c` of the `ħ`-bound.
The final scale of `Y` inside the bilinear clause is
fixed by the `ħ`-absorption step, which is supplied as a hypothesis of the
packaging statement below. -/
def localizationSkewWitness (nu : ℝ) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  Real.sqrt (localizationWitness nu n m L omega)

theorem localizationTheta_nonneg (nu : ℝ) (hnu : 0 ≤ nu) (n m L : ℕ)
    (omega : ShellSeq d) : 0 ≤ localizationTheta nu n m L omega := by
  unfold localizationTheta
  exact mul_nonneg (inv_nonneg.2 hnu)
    (mul_nonneg (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (upperShellDerivGauge_nonneg n m L omega))

theorem measurable_localizationTheta (nu : ℝ) (n m L : ℕ) :
    Measurable (localizationTheta nu n m L : ShellSeq d → ℝ) := by
  unfold localizationTheta
  exact measurable_const.mul
    ((measurable_upperShellDerivGauge n m L).const_mul _)

theorem measurable_localizationWitness (nu : ℝ) (n m L : ℕ) :
    Measurable (localizationWitness nu n m L : ShellSeq d → ℝ) := by
  have h : Measurable (localizationTheta nu n m L : ShellSeq d → ℝ) :=
    measurable_localizationTheta nu n m L
  unfold localizationWitness localizationD
  exact measurable_const.mul (h.mul (measurable_const.add h))

/-! ## The degenerate cases -/

/-- At `m = L` the upper-shell gauge is the empty sum. -/
private theorem upperShellDerivGauge_self (n m : ℕ) (omega : ShellSeq d) :
    upperShellDerivGauge n m m omega = 0 := by
  rw [upperShellDerivGauge, Finset.Ioc_self, Finset.sum_empty]

/-- At `d = 0` the operator-norm diameter constant vanishes. -/
private theorem matrixOperatorNorm_diamConst_zero :
    matrixOperatorNorm_diamConst 0 = 0 := by
  unfold matrixOperatorNorm_diamConst
  norm_num

/-- The two witnesses vanish at every point where `theta` vanishes. -/
private theorem localizationWitness_zero_of_theta_zero (nu : ℝ) (n m L : ℕ)
    (omega : ShellSeq d) (h : localizationTheta nu n m L omega = 0) :
    localizationWitness nu n m L omega = 0 ∧
      localizationSkewWitness nu n m L omega = 0 := by
  constructor
  · unfold localizationWitness localizationD
    rw [h]
    ring
  · unfold localizationSkewWitness localizationWitness localizationD
    rw [h]
    norm_num

/-- The tail bound of the zero function, at any nonnegative amplitude, used in
the two degenerate cases `d = 0` and `m = L`. -/
private theorem isBigOWith_gammaSigma_const_zero (mu : Measure (ShellSeq d))
    (sigma A : ℝ) (hA : 0 ≤ A) :
    IsBigOWith mu (gammaSigma sigma) (fun _ : ShellSeq d => (0 : ℝ)) A := by
  rw [IsBigOWith]
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hempty : upperTailEvent (fun _ : ShellSeq d => (0 : ℝ)) (A * t) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    simp only [upperTailEvent, Set.mem_ofPred_eq] at hω
    exact absurd hω (not_lt.mpr (mul_nonneg hA ht0))
  rw [hempty, measureReal_empty]
  exact (inv_pos.mpr (Real.exp_pos _)).le

/-! ## The abstract tail-bound package -/

/-- **The base step of the abstract tail-bound package**: from a `Γ₂` bound of
a pointwise nonnegative measurable gauge `theta` at the amplitude
`nu⁻¹ · K · T`, the index weakening and the two-term triangle produce the
`Γ₁` bound of the scaled bookkeeping expression
`2 (theta + theta²)` at the amplitude `2 (gammaTriangleConst 1 * (nu⁻¹ K T +
(nu⁻¹ K T)²))`.  This is the printed step `e.mclDsizebounds` before its amplitude bookkeeping. -/
private theorem isBigO_pair_base
    (mu : Measure (ShellSeq d)) [IsFiniteMeasure mu]
    (theta : ShellSeq d → ℝ) (hθnn : ∀ ω, 0 ≤ theta ω) (hθm : Measurable theta)
    (nu K T : ℝ) (hnu : 0 < nu) (hKpos : 0 < K) (hT0 : 0 ≤ T) (hTpos : 0 < T)
    (hθ : IsBigO mu (gammaSigma 2) theta (nu⁻¹ * K * T)) :
    IsBigOWith mu (gammaSigma 1) (fun ω => 2 * (theta ω + theta ω ^ (2 : ℝ)))
      (2 * (gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)))) := by
  have hA0 : 0 ≤ nu⁻¹ * K * T :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hnu.le) hKpos.le) hT0
  have hApos : 0 < nu⁻¹ * K * T :=
    mul_pos (mul_pos (inv_pos.mpr hnu) hKpos) hTpos
  have hθ1 : IsBigO mu (gammaSigma 1) theta (nu⁻¹ * K * T) :=
    isBigO_gammaSigma_of_exponent_le (by norm_num) hθ
  have hθsq : IsBigO mu (gammaSigma 1) (fun ω => theta ω ^ (2 : ℝ))
      ((nu⁻¹ * K * T) ^ (2 : ℝ)) := by
    have hidx : ((2 : ℝ) / 2) = 1 := by norm_num
    have h2 := isBigO_gammaSigma_rpow_fwd (σ := (2 : ℝ)) (p := (2 : ℝ))
      (K := nu⁻¹ * K * T) (by norm_num) hA0 hθnn hθ
    rwa [hidx] at h2
  have hD : IsBigO mu (gammaSigma 1) (fun ω => theta ω + theta ω ^ (2 : ℝ))
      (gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ))) :=
    isBigO_gammaSigma_add_of_isBigO (by norm_num) hApos
      (Real.rpow_pos_of_pos hApos 2) hθ1 hθsq
      hθm (hθm.pow measurable_const)
  have hXwith : IsBigOWith mu (gammaSigma 1) (fun ω => theta ω + theta ω ^ (2 : ℝ))
      (gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ))) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (fun ω => add_nonneg (hθnn ω) (Real.rpow_nonneg (hθnn ω) 2))).2 hD
  exact hXwith.const_mul (c := (2 : ℝ)) (by norm_num)

/-- **The `Γ₁` bound of the sandwich witness** (the first component of the
abstract tail-bound package): the amplitude bookkeeping of the printed step
`e.mclDsizebounds` turns the base `Γ₁` bound of
`2 (theta + theta²)` into the printed rate
`2 gammaTriangleConst 1 * (K + K²) · nu⁻² · T`. -/
private theorem isBigO_pair_X
    (mu : Measure (ShellSeq d)) [IsFiniteMeasure mu]
    (theta : ShellSeq d → ℝ) (hθnn : ∀ ω, 0 ≤ theta ω) (hθm : Measurable theta)
    (nu K T : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hKpos : 0 < K)
    (hT0 : 0 ≤ T) (hTpos : 0 < T) (hT1 : T ≤ 1)
    (hθ : IsBigO mu (gammaSigma 2) theta (nu⁻¹ * K * T)) :
    IsBigO mu (gammaSigma 1) (fun ω => 2 * (theta ω + theta ω ^ (2 : ℝ)))
      (2 * gammaTriangleConst 1 * (K + K ^ 2) * (nu⁻¹ * nu⁻¹) * T) := by
  refine (isBigOWith_iff_isBigO_of_nonneg
    (mu := mu) (Psi := gammaSigma 1)
    (X := fun ω => 2 * (theta ω + theta ω ^ (2 : ℝ)))
    (A := 2 * gammaTriangleConst 1 * (K + K ^ 2) * (nu⁻¹ * nu⁻¹) * T)
    (fun ω => mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (add_nonneg (hθnn ω) (Real.rpow_nonneg (hθnn ω) 2)))).1
    ((isBigO_pair_base mu theta hθnn hθm nu K T hnu hKpos hT0 hTpos hθ).mono_scale
      (amp_le nu K T hnu hnu1 hKpos.le hT0 hT1))

/-- **The squared intermediate step of the skew-witness route** (the second
component of the abstract tail-bound package, first half): squaring the
pointwise identity for `Y = sqrt (2 (theta + theta²))` and scaling the square
of the printed skew rate turns the base `Γ₁` bound into the squared `Γ₁` bound
of `Y²`. -/
private theorem isBigO_pair_Y_sq
    (mu : Measure (ShellSeq d)) [IsFiniteMeasure mu]
    (theta : ShellSeq d → ℝ) (hθnn : ∀ ω, 0 ≤ theta ω) (hθm : Measurable theta)
    (nu K T T2 : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hKpos : 0 < K)
    (hT0 : 0 ≤ T) (hTpos : 0 < T) (hT1 : T ≤ 1)
    (hT2sq : T2 ^ 2 = T)
    (hθ : IsBigO mu (gammaSigma 2) theta (nu⁻¹ * K * T)) :
    IsBigOWith mu (gammaSigma 1)
      (fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ 2)
      ((Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
        (nu⁻¹ * nu⁻¹) * T2) ^ 2) := by
  have hX2with : IsBigOWith mu (gammaSigma 1)
      (fun ω => 2 * (theta ω + theta ω ^ (2 : ℝ)))
      (2 * (gammaTriangleConst 1 * (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)))) :=
    isBigO_pair_base mu theta hθnn hθm nu K T hnu hKpos hT0 hTpos hθ
  -- the square-root route: square the pointwise identity for `Y`
  have hsq : ∀ ω : ShellSeq d,
      Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ 2
        = 2 * (theta ω + theta ω ^ (2 : ℝ)) :=
    fun ω => Real.sq_sqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (add_nonneg (hθnn ω) (Real.rpow_nonneg (hθnn ω) 2)))
  have hfun2 : (fun ω : ShellSeq d =>
        Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ 2)
      = fun ω => 2 * (theta ω + theta ω ^ (2 : ℝ)) := funext hsq
  have hYwith : IsBigOWith mu (gammaSigma 1)
      (fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ 2)
      (2 * (gammaTriangleConst 1 *
        (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)))) := by
    rw [hfun2]
    exact hX2with
  have hK2sq : (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
      (nu⁻¹ * nu⁻¹) * T2) ^ 2
      = (2 * gammaTriangleConst 1 * (K + K ^ 2)) * ((nu⁻¹ * nu⁻¹) ^ 2) * T := by
    have hsqK : (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2))) ^ 2
        = 2 * gammaTriangleConst 1 * (K + K ^ 2) :=
      Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        gammaTriangleConst_pos.le) (add_nonneg hKpos.le (sq_nonneg K)))
    rw [show (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
          (nu⁻¹ * nu⁻¹) * T2) ^ 2
        = (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2))) ^ 2
          * ((nu⁻¹ * nu⁻¹) ^ 2 * T2 ^ 2) from by ring, hsqK, hT2sq]
    ring
  have hamp2 : 2 * (gammaTriangleConst 1 *
      (nu⁻¹ * K * T + (nu⁻¹ * K * T) ^ (2 : ℝ)))
      ≤ (2 * gammaTriangleConst 1 * (K + K ^ 2)) * ((nu⁻¹ * nu⁻¹) ^ 2) * T :=
    ampSq_le nu K T hnu hnu1 hKpos.le hT0 hT1
  have hY2 : IsBigOWith mu (gammaSigma 1)
      (fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ 2)
      ((Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
        (nu⁻¹ * nu⁻¹) * T2) ^ 2) := by
    rw [hK2sq]
    exact hYwith.mono_scale hamp2
  exact hY2

/-- **The reverse power rule of the skew-witness route** (the second component
of the abstract tail-bound package): the reverse power rule at
`sigma = 1, p = 2`, fed with the `Γ_{1/2}` weakening of the square bound,
produces the `Γ₁` bound of `Y = sqrt (2 (theta + theta²))` at the printed
skew rate. -/
private theorem isBigO_pair_Y_rev
    (mu : Measure (ShellSeq d)) [IsFiniteMeasure mu]
    (theta : ShellSeq d → ℝ) (hθnn : ∀ ω, 0 ≤ theta ω) (hθm : Measurable theta)
    (nu K T T2 : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hKpos : 0 < K)
    (hT0 : 0 ≤ T) (hTpos : 0 < T) (hT1 : T ≤ 1)
    (hT2 : 0 ≤ T2) (hT2sq : T2 ^ 2 = T)
    (hθ : IsBigO mu (gammaSigma 2) theta (nu⁻¹ * K * T)) :
    IsBigO mu (gammaSigma 1)
      (fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))))
      (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
        (nu⁻¹ * nu⁻¹) * T2) := by
  have hY2 := isBigO_pair_Y_sq mu theta hθnn hθm nu K T T2 hnu hnu1 hKpos hT0
    hTpos hT1 hT2sq hθ
  -- the reverse power rule at `sigma = 1, p = 2`, fed with the `Γ_{1/2}`
  -- weakening of the square bound
  have hY2R : IsBigOWith mu (gammaSigma 1)
      (fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ (2 : ℝ))
      ((Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
        (nu⁻¹ * nu⁻¹) * T2) ^ (2 : ℝ)) := by
    have hfunR : (fun ω : ShellSeq d =>
        Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ (2 : ℝ))
        = fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))) ^ 2 :=
      funext fun ω => Real.rpow_two _
    rw [hfunR, Real.rpow_two (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
      (nu⁻¹ * nu⁻¹) * T2)]
    exact hY2
  have hY3rev : IsBigOWith mu (gammaSigma 1)
      (fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))))
      (Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) * (nu⁻¹ * nu⁻¹) * T2) :=
    isBigOWith_gammaSigma_rpow_rev
      (σ := (1 : ℝ)) (p := (2 : ℝ))
      (X := fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))))
      (K := Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) * (nu⁻¹ * nu⁻¹) * T2)
      (by norm_num)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (inv_nonneg.2 hnu.le) (inv_nonneg.2 hnu.le))) hT2)
      (fun ω => Real.sqrt_nonneg _)
      (isBigOWith_gammaSigma_of_exponent_le
        (show ((1 : ℝ) / 2) ≤ (1 : ℝ) from by norm_num) hY2R)
  exact (isBigOWith_iff_isBigO_of_nonneg
    (mu := mu) (Psi := gammaSigma 1)
    (X := fun ω => Real.sqrt (2 * (theta ω + theta ω ^ (2 : ℝ))))
    (A := Real.sqrt (2 * gammaTriangleConst 1 * (K + K ^ 2)) *
      (nu⁻¹ * nu⁻¹) * T2)
    (fun ω => Real.sqrt_nonneg _)).1 hY3rev

/-! ## The two rates at the witnesses -/

/-- **The two `Γ₁` tail bounds of the localization witnesses** (the
`IsBigO`-parts of the first two conjuncts of `e.localization`):
the sandwich witness
`X = 2 theta (1 + theta)` with `theta = nu⁻¹ (d³ √d) 3^n G` is
`O_{Γ₁}(C(d) ν⁻² 3^{-(m-n)})`, and its square root `Y = sqrt X` is
`O_{Γ₁}(sqrt C ν⁻² 3^{-(m-n)/2})`, with the explicit dimensional constants
`localizationConst d` and `localizationSkewConst d`.

The main case (`0 < d`, `m < L`) feeds the `Γ₂` gauge bound
`isBigOWith_gammaSigma_upperShellDerivGauge` into the private pair lemmas of this file; in
the two degenerate cases (`d = 0`, so that the operator-norm diameter constant vanishes, and
`m = L`, so that the upper-shell gauge is the empty sum) both witnesses vanish
identically. -/
theorem localizationWitness_pair_isBigO
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (hJ3 : ShellLawJ3 d P)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (n m L : ℕ) (hnm : n ≤ m)
    (hmL : m ≤ L) :
    IsBigO P.toMeasure (gammaSigma 1) (localizationWitness nu n m L)
        (localizationConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ∧
      IsBigO P.toMeasure (gammaSigma 1) (localizationSkewWitness nu n m L)
        (localizationSkewConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2))) := by
  have hA0X : 0 ≤ localizationConst d * nu ^ (-(2 : ℝ)) *
      (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg (localizationConst_nonneg d)
      (Real.rpow_nonneg (le_of_lt hnu) _)) (Real.rpow_nonneg (by norm_num) _)
  have hA0Y : 0 ≤ localizationSkewConst d * nu ^ (-(2 : ℝ)) *
      (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (localizationSkewConst_nonneg d)
      (Real.rpow_nonneg (le_of_lt hnu) _)) (Real.rpow_nonneg (by norm_num) _)
  by_cases hcase : 0 < d ∧ m < L
  · -- the main case
    obtain ⟨hd, hmLlt⟩ := hcase
    -- the `Γ₂` gauge bound, scaled to the pointwise relative bound `theta`
    have hθ0 : IsBigO P.toMeasure (gammaSigma 2) (upperShellDerivGauge n m L)
        (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹) :=
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := gammaSigma 2)
        (X := upperShellDerivGauge n m L)
        (A := gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹)
        (upperShellDerivGauge_nonneg n m L)).1
        (isBigOWith_gammaSigma_upperShellDerivGauge hJ3 (by omega) hmLlt)
    have hθ1 : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => nu⁻¹ * (matrixOperatorNorm_diamConst d *
            (3 : ℝ) ^ n * upperShellDerivGauge n m L omega))
        (nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
          (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹))) :=
      hθ0.const_mul (c := matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n)
          (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
        |>.const_mul (c := nu⁻¹) (inv_nonneg.2 hnu.le)
    have hnpow : (3 : ℝ) ^ n * ((3 : ℝ) ^ m)⁻¹ = (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
      three_pow_nat_sub hnm
    have hkey : nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        (gammaTriangleConst 2 * ((3 : ℝ) ^ m)⁻¹))
        = nu⁻¹ * gaugeAmplitudeConst d * (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by
      simp only [gaugeAmplitudeConst]
      linear_combination (norm := ring_nf)
        (nu⁻¹ * (matrixOperatorNorm_diamConst d * gammaTriangleConst 2)) * hnpow
    have hθ2 : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => nu⁻¹ * (matrixOperatorNorm_diamConst d *
            (3 : ℝ) ^ n * upperShellDerivGauge n m L omega))
        (nu⁻¹ * gaugeAmplitudeConst d * (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) :=
      hθ1.mono_scale (le_of_eq hkey)
    -- the abstract package at the printed time parameters
    have hT0 : 0 ≤ (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hTpos : 0 < (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hT1 : (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) ≤ 1 := three_rpow_sub_le_one (m - n)
    have hX := isBigO_pair_X P.toMeasure
      (fun omega : ShellSeq d => localizationTheta nu n m L omega)
      (localizationTheta_nonneg nu hnu.le n m L)
      (measurable_localizationTheta nu n m L) nu (gaugeAmplitudeConst d)
      ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) hnu hnu1 (gaugeAmplitudeConst_pos hd)
      hT0 hTpos hT1 hθ2
    have hY := isBigO_pair_Y_rev P.toMeasure
      (fun omega : ShellSeq d => localizationTheta nu n m L omega)
      (localizationTheta_nonneg nu hnu.le n m L)
      (measurable_localizationTheta nu n m L) nu (gaugeAmplitudeConst d)
      ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))
      (Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) hnu hnu1
      (gaugeAmplitudeConst_pos hd) hT0 hTpos hT1
      (Real.sqrt_nonneg _) (Real.sq_sqrt hT0) hθ2
    -- the witness functions and rates
    have hfunX : (fun omega : ShellSeq d => localizationWitness nu n m L omega)
        = fun omega => 2 * (localizationTheta nu n m L omega +
            localizationTheta nu n m L omega ^ (2 : ℝ)) := by
      funext omega
      unfold localizationWitness localizationD
      rw [Real.rpow_two]
      ring
    have hfunY : (fun omega : ShellSeq d => localizationSkewWitness nu n m L omega)
        = fun omega => Real.sqrt (2 * (localizationTheta nu n m L omega +
            localizationTheta nu n m L omega ^ (2 : ℝ))) := by
      funext omega
      unfold localizationSkewWitness localizationWitness localizationD
      rw [Real.rpow_two]
      congr 1
      ring
    have hampX : 2 * gammaTriangleConst 1 *
          (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2) * (nu⁻¹ * nu⁻¹) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))
        = localizationConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) := by
      simp only [localizationConst]
      rw [rpow_neg_two_of_pos hnu]
    have hampY : Real.sqrt (2 * gammaTriangleConst 1 *
          (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2)) * (nu⁻¹ * nu⁻¹) *
          Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))
        = localizationSkewConst d * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2)) := by
      simp only [localizationSkewConst]
      rw [rpow_neg_two_of_pos hnu, sqrt_three_rpow_sub]
    have hXw : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => localizationWitness nu n m L omega)
        (2 * gammaTriangleConst 1 *
          (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2) * (nu⁻¹ * nu⁻¹) *
          (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) := by
      rw [hfunX]
      exact hX
    have hYw : IsBigO P.toMeasure (gammaSigma 1)
        (fun omega : ShellSeq d => localizationSkewWitness nu n m L omega)
        (Real.sqrt (2 * gammaTriangleConst 1 *
          (gaugeAmplitudeConst d + gaugeAmplitudeConst d ^ 2)) * (nu⁻¹ * nu⁻¹) *
          Real.sqrt ((3 : ℝ) ^ (-((m - n : ℕ) : ℝ)))) := by
      rw [hfunY]
      exact hY
    exact ⟨hXw.mono_scale (le_of_eq hampX), hYw.mono_scale (le_of_eq hampY)⟩
  · -- the two degenerate cases: `d = 0` and `m = L`
    have hzero : ∀ omega : ShellSeq d, localizationTheta nu n m L omega = 0 := by
      rcases Nat.lt_or_ge d 1 with hdl | hd1
      · have hdz : d = 0 := Nat.lt_one_iff.mp hdl
        subst hdz
        intro omega
        unfold localizationTheta
        rw [matrixOperatorNorm_diamConst_zero]
        ring
      · have hme : m = L := by omega
        subst hme
        intro omega
        unfold localizationTheta
        rw [upperShellDerivGauge_self n m omega]
        ring
    have hwit : ∀ omega : ShellSeq d, localizationWitness nu n m L omega = 0 ∧
        localizationSkewWitness nu n m L omega = 0 :=
      fun omega => localizationWitness_zero_of_theta_zero nu n m L omega
        (hzero omega)
    have habsX : (fun omega : ShellSeq d => |localizationWitness nu n m L omega|)
        = fun _ : ShellSeq d => (0 : ℝ) :=
      funext fun omega => by rw [(hwit omega).1, abs_zero]
    have habsY : (fun omega : ShellSeq d => |localizationSkewWitness nu n m L omega|)
        = fun _ : ShellSeq d => (0 : ℝ) :=
      funext fun omega => by rw [(hwit omega).2, abs_zero]
    exact ⟨by
      rw [IsBigO, habsX]
      exact isBigOWith_gammaSigma_const_zero P.toMeasure 1 _ hA0X, by
      rw [IsBigO, habsY]
      exact isBigOWith_gammaSigma_const_zero P.toMeasure 1 _ hA0Y⟩

/-! ## The conjuncts, from the corresponding clauses -/

/-- **The first conjunct of `e.localization.s.star`** (`Frozen.Section2.cutoff_localization`,
conjunct 1), from the four `MatLoewnerLE` clauses of the
sandwich about the witness `X = 2 theta (1 + theta)`.  The clauses are the
hypothesis `hLoewner`; producing them from the block-sandwich engine is not
done in this file. -/
theorem localizationConjunct1
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (hJ3 : ShellLawJ3 d P)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (n m L : ℕ) (hnm : n ≤ m)
    (hmL : m ≤ L) (U : Book.Ch02.Domain d)
    (hLoewner : ∀ omega : ShellSeq d,
        Homogenization.MatLoewnerLE
          ((1 - localizationWitness nu n m L omega) •
            sigmaCoarse (U : Set (Vec d))
              (coefficientCutoff nu omega L).toCoeffField)
          (sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        (sigmaCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField)
        ((1 + localizationWitness nu n m L omega) •
          sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        ((1 - localizationWitness nu n m L omega) •
          sigmaStarInvCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField)
        (sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        (sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField)
        ((1 + localizationWitness nu n m L omega) •
          sigmaStarInvCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField)) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma 1) X
          (localizationConst d * nu ^ (-(2 : ℝ)) *
            (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ∧
      ∀ omega : ShellSeq d,
        Homogenization.MatLoewnerLE
          ((1 - X omega) •
            sigmaCoarse (U : Set (Vec d))
              (coefficientCutoff nu omega L).toCoeffField)
          (sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        (sigmaCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega m).toCoeffField)
        ((1 + X omega) •
          sigmaCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega L).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        ((1 - X omega) •
          sigmaStarInvCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField)
        (sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField) ∧
      Homogenization.MatLoewnerLE
        (sigmaStarInvCoarse (U : Set (Vec d))
          (coefficientCutoff nu omega L).toCoeffField)
        ((1 + X omega) •
          sigmaStarInvCoarse (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField) :=
  ⟨localizationWitness nu n m L, measurable_localizationWitness nu n m L,
    (localizationWitness_pair_isBigO P hJ3 nu hnu hnu1 n m L hnm hmL).1,
    hLoewner⟩

end

end SuperdiffusionCLT.Section2.Localization