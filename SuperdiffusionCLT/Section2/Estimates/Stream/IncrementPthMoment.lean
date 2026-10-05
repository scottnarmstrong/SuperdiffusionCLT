/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Probability.VolumeAverageOrlicz
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLpLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.TranslatedIncrementLinfty

/-!
# The marginal finite-increment `p`-th moment display

This module assembles the two size displays of the finite-increment block of
the manuscript's Section 2 that precede the `L^p` and `L∞` clauses:

* the origin display `e.k.ell.upscales`: for `n < m`,
  `|(k_m - k_n)(0)| = O_{Gamma_2}(C (m-n)^{1/2})`;
* the normalized moment display `e.kmn.bounds`: for
  `p >= 1` and every cube,
  `⨍_{cu_l} |(k_m - k_n)(x)|^p dx = O_{Gamma_{2/p}}(C^p (m-n)^{p/2})`.

The two are assembled from previously proved estimates. The origin display is the
translated supremum envelope of `TranslatedIncrementLinfty` read at one point:
the deterministic domination
`matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound`
controls the increment at the center of the translated cube by the translated
envelope, so the envelope's `Gamma_2` bound transports to the point at every
center `z`, and `z = 0` is the printed display. The power rule for
stretched-exponential tails (`SuperdiffusionCLT.Probability.OrliczPower`)
raises the pointwise display to the `p`-th power at index `2/p`, and Jensen
averaging (`SuperdiffusionCLT.Probability.VolumeAverageOrlicz`) transfers
it to the normalized volume average over any cube.

The printed displays quantify an amplitude `C (m-n)^{1/2}` and `C^p (m-n)^{p/2}`
with one dimension-only constant `C(d) < ∞`, uniform in `p` and in `m - n`. The
assembly carried out here realizes `C^p (m-n)^{p/2}` with

`C = (e * gammaMomentConst (2/p))^{1/p} * streamLinftyConst d`,

so the realized constant does depend on `p` through the Chapter 4 moment
constant `gammaMomentConst (2/p)`; this is recorded honestly at the folded
display `isBigO_gammaSigma_finiteShellIncrementPthMoment` below. The Chapter 4
constant is `gammaMomentConst sigma = 2e * max 1 ((2 / (sigma e))^{1/sigma})`,
which grows without bound as `sigma → 0` (like `(p / e)^{p/2}` at
`sigma = 2/p`), so the realized `C` is not uniform in `p`: it tends to
infinity as `p → ∞`. For every fixed `p >= 1` the display is a finite
dimension-dependent constant.

## Main results

* `isBigOWith_gammaSigma_matrixOperatorNorm_finiteShellIncrement_apply`: the
  pointwise display at every center `z`, `|(k_m - k_n)(z)| ≤ O_{Gamma_2}(C (m-n)^{1/2})`.
* `isBigOWith_gammaSigma_matrixOperatorNorm_rpow_finiteShellIncrement_apply`:
  the `p`-th power of the pointwise display at index `2/p`.
* `measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement`: the joint
  measurability of the `p`-th power on `Vec d × ShellSeq d`.
* `isBigOWith_gammaSigma_finiteShellIncrementPthMoment`: the normalized moment
  display `e.kmn.bounds`.
* `isBigO_gammaSigma_finiteShellIncrementPthMoment`: the folded display with
  the constant `C^p (m-n)^{p/2}`.

## References

* `e.k.ell.upscales`, `e.kmn.bounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Geometry of the natural origin cube -/

/-- The origin lies in the natural origin cube. -/
theorem zero_mem_openCubeSet_originCube (n : ℕ) :
    (0 : Vec d) ∈ openCubeSet (originCube d (n : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) :=
    zpow_pos (by norm_num) (n : ℤ)
  exact ⟨mul_neg_of_neg_of_pos (by norm_num) hpow, mul_pos (by norm_num) hpow⟩

/-! ## Measurability of the pointwise increment size -/

/-- The matrix operator norm of the finite increment at a fixed point is
measurable in the shell sequence. -/
theorem measurable_matrixOperatorNorm_finiteShellIncrement (n m : ℕ) (z : Vec d) :
    Measurable (fun omega : ShellSeq d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m z)) := by
  have hmatrix : Measurable (fun omega : ShellSeq d ↦
      finiteShellIncrement omega n m z) :=
    measurable_matrix_of_entries fun i l ↦
      (measurable_apply_entry z i l).comp (measurable_finiteShellIncrement n m)
  exact ShellField.continuous_matrixOperatorNorm.measurable.comp hmatrix

/-- Joint measurability of the pointwise increment size in the sample and the
point: the map is continuous in the point, because every shell of the carrier
stores a continuous value map, and measurable in the sample, so it is a
Caratheodory function. -/
theorem measurable_uncurry_matrixOperatorNorm_finiteShellIncrement (n m : ℕ) :
    Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) ↦
        matrixOperatorNorm (finiteShellIncrement omega n m x))) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega ↦ continuous_matrixOperatorNorm_finiteShellIncrement omega n m)
    (fun z ↦ measurable_matrixOperatorNorm_finiteShellIncrement n m z)

/-- Joint measurability of the `p`-th power of the pointwise increment size
for every real exponent `p ≥ 0`. -/
theorem measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement
    (n m : ℕ) {p : ℝ} (hp : (0 : ℝ) ≤ p) :
    Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) ↦
        matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)) :=
  (Real.continuous_rpow_const hp).measurable.comp
    (measurable_uncurry_matrixOperatorNorm_finiteShellIncrement n m)

/-! ## The pointwise display at an arbitrary center -/

/-- The increment at the center of the translated cube is dominated by the
translated finite-increment envelope. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound_zero
    (z : Vec d) (omega : ShellSeq d) (n m : ℕ) :
    matrixOperatorNorm (finiteShellIncrement omega n m z) ≤
      translatedIncrementSupBound z n m omega := by
  have h := matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
    z omega n m (x := 0) (zero_mem_openCubeSet_originCube n)
  simpa only [add_zero] using h

/-- **The pointwise increment display at every center**, the transport of the
manuscript display `e.k.ell.upscales` to an arbitrary
deterministic center `z`: for `n < m`,

`|(k_m - k_n)(z)| ≤ O_{Gamma_2}(C (m-n)^{1/2})`

with the explicit dimension-only constant `streamLinftyConst d` of the
translated supremum envelope. The proof reads the envelope tail at the
center `z` and transports it through the deterministic pointwise domination by
the translated envelope; no sequence law is used beyond the stationarity
observables already consumed by the envelope. -/
theorem isBigOWith_gammaSigma_matrixOperatorNorm_finiteShellIncrement_apply
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m z))
      (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) :=
  (isBigOWith_gammaSigma_translatedIncrementSupBound hPrefix hJ2 hJ3 hJ4 hnm z).of_le
    (fun omega ↦
      matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound_zero
        z omega n m)

/-! ## The `p`-th power of the pointwise display -/

/-- **The `p`-th power of the pointwise increment display at every center**: the
manuscript display `e.k.ell.upscales` read through the power
rule for stretched-exponential tails (`e.powerofGammasigma`):
for `1 ≤ p`, `n < m` and every center `z`,

`|(k_m - k_n)(z)|^p ≤ O_{Gamma_{2/p}}(C^p (m-n)^{p/2})`

with the amplitude `C^p (m-n)^{p/2}` written as
`(streamLinftyConst d * √(m-n))^p`, since `(m-n)^{1/2} = √(m-n)`. -/
theorem isBigOWith_gammaSigma_matrixOperatorNorm_rpow_finiteShellIncrement_apply
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ShellSeq d ↦
        matrixOperatorNorm (finiteShellIncrement omega n m z) ^ p)
      ((streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) ^ p) := by
  have hpos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  exact SuperdiffusionCLT.Probability.isBigOWith_gammaSigma_rpow_fwd
    (mu := P.toMeasure)
    (X := fun omega : ShellSeq d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m z))
    (K := streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) (σ := 2) (p := p)
    hpos
    (mul_nonneg (streamLinftyConst_pos hPrefix).le (Real.sqrt_nonneg _))
    (fun omega ↦ matrixOperatorNorm_nonneg _)
    (isBigOWith_gammaSigma_matrixOperatorNorm_finiteShellIncrement_apply
      hPrefix hJ2 hJ3 hJ4 hnm z)

/-! ## The normalized moment display -/

/-- **The normalized `p`-th moment display `e.kmn.bounds`**: for `1 ≤ p`, `n < m`
and every cube `Q`,

`⨍_{Q} |(k_m - k_n)(x)|^p dx ≤ O_{Gamma_{2/p}}(C^p (m-n)^{p/2})`

with the amplitude `C^p (m-n)^{p/2}` written as
`e * (gammaMomentConst (2/p) * (streamLinftyConst d * √(m-n))^p)`, so the
constant of the display is realized as
`C^p = e * gammaMomentConst (2/p) * streamLinftyConst d ^ p`. The proof is the
manuscript's Jensen step: the pointwise display at every center is raised to
the `p`-th power at index `2/p` by the power rule for stretched-exponential
tails, and the joint measurability of the `p`-th power on `Vec d × ShellSeq d`
lets the averaging lemma transfer the common tail to the normalized volume
average over the cube. -/
theorem isBigOWith_gammaSigma_finiteShellIncrementPthMoment
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ShellSeq d ↦
        volumeAverage (cubeSet Q)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p))
      (Real.exp 1 * (IndependentSums.gammaMomentConst (2 / p) *
        (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) ^ p)) := by
  have hgap : 0 < ((m - n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hnm
  have hA : 0 < (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) ^ p :=
    Real.rpow_pos_of_pos
      (mul_pos (streamLinftyConst_pos hPrefix) (Real.sqrt_pos.2 hgap)) p
  have hvolpos : 0 < (volume (cubeSet Q)).toReal := by
    rw [volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  have hU0 : volume (cubeSet Q) ≠ 0 := by
    intro h
    rw [h] at hvolpos
    simp at hvolpos
  have hUtop : volume (cubeSet Q) ≠ ⊤ := ne_of_lt (volume_cubeSet_lt_top Q)
  exact SuperdiffusionCLT.Probability.isBigOWith_gammaSigma_volumeAverage
    (mu := P.toMeasure) (U := cubeSet Q)
    (Y := fun (x : Vec d) (omega : ShellSeq d) ↦
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
    (div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)) hA hU0 hUtop
    (fun x omega ↦ Real.rpow_nonneg (matrixOperatorNorm_nonneg _) p)
    (measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement n m
      (le_trans (by norm_num) hp))
    (fun x ↦ isBigOWith_gammaSigma_matrixOperatorNorm_rpow_finiteShellIncrement_apply
      hPrefix hJ2 hJ3 hJ4 hp hnm x)

/-! ## The folded display -/

/-- The constant of the folded `p`-th moment display: the manuscript's `C`,
realized as `(e * gammaMomentConst (2/p))^{1/p} * streamLinftyConst d`. It
depends on `p` through the Chapter 4 moment constant `gammaMomentConst (2/p)`,
which grows without bound as `p → ∞`. -/
def finiteShellIncrementPthMomentConst (d : ℕ) (p : ℝ) : ℝ :=
  (Real.exp 1 * IndependentSums.gammaMomentConst (2 / p)) ^ (p⁻¹) *
    streamLinftyConst d

/-- **The folded normalized `p`-th moment display**: the manuscript display
`e.kmn.bounds` with the
constant folded into the manuscript's shape

`⨍_{Q} |(k_m - k_n)(x)|^p dx = O_{Gamma_{2/p}}(C^p (m-n)^{p/2})`,

`C := (e * gammaMomentConst (2/p))^{1/p} * streamLinftyConst d` (the definition
`finiteShellIncrementPthMomentConst`), and `(m-n)^{p/2}` written as
`√(m-n)^p`.

Honesty note on the constant. The printed display quantifies one
dimension-only constant `C(d) < ∞` uniform in `p`; the constant realized here
is dimension-dependent only through `streamLinftyConst d` but *does* depend on
`p` through the Chapter 4 moment constant `gammaMomentConst (2/p)`, which enters
the tail-to-moment conversion of the Jensen step. That constant is
`gammaMomentConst sigma = 2e * max 1 ((2 / (sigma * e))^{1/sigma})`, which
grows without bound as `sigma → 0`: at `sigma = 2/p` its growth is like
`(p / e)^{p/2}`, so the realized `C` tends to infinity as `p → ∞`. For every
fixed `p ≥ 1` the realized constant is finite, and the display holds in the
manuscript's shape; what is not achieved is the uniformity of `C` in `p`. -/
theorem isBigO_gammaSigma_finiteShellIncrementPthMoment
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m) (Q : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ShellSeq d ↦
        volumeAverage (cubeSet Q)
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p))
      (finiteShellIncrementPthMomentConst d p ^ p *
        Real.sqrt ((m - n : ℕ) : ℝ) ^ p) := by
  have hnonneg : ∀ omega : ShellSeq d,
      0 ≤ volumeAverage (cubeSet Q)
        (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) := by
    intro omega
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x ↦ Real.rpow_nonneg (matrixOperatorNorm_nonneg _) p)
  have hsigma : 0 < 2 / p := div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hpne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hS0 : 0 ≤ streamLinftyConst d := (streamLinftyConst_pos hPrefix).le
  have hr0 : 0 ≤ Real.sqrt ((m - n : ℕ) : ℝ) := Real.sqrt_nonneg _
  have heg : 0 ≤ Real.exp 1 * IndependentSums.gammaMomentConst (2 / p) :=
    mul_nonneg (Real.exp_pos 1).le (IndependentSums.gammaMomentConst_pos hsigma).le
  have hpowroot :
      ((Real.exp 1 * IndependentSums.gammaMomentConst (2 / p)) ^ (p⁻¹)) ^ p =
        Real.exp 1 * IndependentSums.gammaMomentConst (2 / p) := by
    rw [← Real.rpow_mul heg, inv_mul_cancel₀ hpne, Real.rpow_one]
  have hscale :
      Real.exp 1 * (IndependentSums.gammaMomentConst (2 / p) *
          (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) ^ p) =
        (finiteShellIncrementPthMomentConst d p) ^ p *
          Real.sqrt ((m - n : ℕ) : ℝ) ^ p := by
    have h1 : (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) ^ p
        = streamLinftyConst d ^ p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p :=
      Real.mul_rpow hS0 hr0
    have h2 : ((Real.exp 1 * IndependentSums.gammaMomentConst (2 / p)) ^ (p⁻¹) *
          streamLinftyConst d) ^ p
        = (Real.exp 1 * IndependentSums.gammaMomentConst (2 / p)) *
            streamLinftyConst d ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg heg (p⁻¹)) hS0, hpowroot]
    rw [finiteShellIncrementPthMomentConst, h1, h2]
    ring
  refine (isBigOWith_iff_isBigO_of_nonneg hnonneg).1 ?_
  exact (isBigOWith_gammaSigma_finiteShellIncrementPthMoment
    hPrefix hJ2 hJ3 hJ4 hp hnm Q).mono_scale (le_of_eq hscale)

end

end SuperdiffusionCLT.Section2.Estimates.Stream