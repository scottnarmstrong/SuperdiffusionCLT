/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Probability.OrliczTriangle

/-!
# The level decay `3^{-(d/2)((l-m) ∨ 0)}` of the normalized square average

**The level decay is derivable from the five shell laws**, at the
rate `envelopeLevelDecayConst d * 3^{-(d/2)((l-m) ∨ 0)}`, where
`envelopeLevelDecayConst d` is an explicit constant depending only on the
dimension.

The display `e.km.square.bound` reads, for a triadic cube `Q` of scale `l` and cutoff scale `m ∈ ℕ`,
`(C (1 ∨ m))^{-1} ⨍_Q |k_m|^2 - 1 ≤ O_{Γ_1}(C 3^{-(d/2)((l-m) ∨ 0)})` with
`C = cutoffEnvelopeConst d` and `⨍_Q` the normalized average of
`e.Enaught.vs.A.and.Ahom`. That is exactly
`isBigOWith_gammaSigma_cutoffCubeSquareNormalized`, at the amplitude
`envelopeLevelDecayConst d * levelDecayFactor d m l`.

## The mechanism

`⨍_Q |k_m|^2` is the plain average of the normalized averages over the
`3^{d(l-m)}` scale-`m` descendants of `Q`. Each is an observable of its own
cube's restriction lane (`measurable_blockCubeLane_cutoffCubeSquare`), so
`ShellLawJ1Restriction` (range of dependence `3^m √d`) with `ShellLawJ2` makes one colour
class of them independent, and `Book.Ch04` concentration gives amplitude `√N`;
the `(⌊√d⌋+2)^d` colour classes are recombined by the finite triangle
inequality, and dividing by `N` turns `√N / N` into `3^{-(d/2)(l-m)}`. The
deterministic `1` is the mean bound `integral_volumeAverage_sq_le`, which
caps every sub-cube mean at `cutoffEnvelopeConst d (1 ∨ m)`.

The bound is one-sided (the symmetric form is false: the zero shell sequence
gives `-1` at every scale), and the decay needs `l ≥ m` — on `l < m` the level
factor is `1`, there is no partition into scale-`m` descendants, and the
`Γ_1` tail `isBigOWith_gammaSigma_cutoffCubeSquare` supplies the constant
amplitude `envelopeLevelDecayConst d` directly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Positivity of the constants -/

private theorem gammaTriangleConst_pos (sigma : ℝ) :
    0 < IndependentSums.gammaTriangleConst sigma := by
  have hg : (2 : ℝ) ≤ IndependentSums.gammaGrowthConst sigma := le_max_left _ _
  have hpos : (0 : ℝ) < IndependentSums.gammaGrowthConst sigma := by
    linarith only [hg]
  simp only [IndependentSums.gammaTriangleConst]
  positivity

private theorem gammaSigmaIndependentSumConst_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < Book.Ch04.gammaSigmaIndependentSumConst sigma := by
  rw [Book.Ch04.gammaSigmaIndependentSumConst]
  by_cases hlt : sigma < 1
  · rw [ite_eq_left hlt]
    change 0 < IndependentSums.gammaSigmaHeavyTailEndpointConst sigma
    rw [IndependentSums.gammaSigmaHeavyTailEndpointConst]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (IndependentSums.gammaSigmaHeavyTailConst_pos hsigma)
  · rw [ite_eq_right hlt]
    change 0 < IndependentSums.gammaSigmaExpRegimeEndpointConst sigma
    rw [IndependentSums.gammaSigmaExpRegimeEndpointConst]
    by_cases heq : sigma = 1
    · rw [ite_eq_left heq]
      exact mul_pos (by norm_num) IndependentSums.gammaOneExpRegimeConst_pos
    · rw [ite_eq_right heq]
      refine mul_pos (by norm_num) ?_
      dsimp [IndependentSums.gammaSigmaExpRegimeConst]
      exact lt_of_lt_of_le
        (mul_pos (by positivity) (IndependentSums.gammaMomentConst_pos hsigma))
        (le_max_left _ _)

/-- A bounded deterministic random variable has a `Γ_sigma` tail at its bound. -/
private theorem isBigO_gammaSigma_const {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {sigma c B : ℝ} (hcB : |c| ≤ B) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) (fun _ : Omega ↦ c) B := by
  intro t ht
  have hB : 0 ≤ B := le_trans (abs_nonneg c) hcB
  have hempty : IndependentSums.upperTailEvent (fun _ : Omega ↦ |c|) (B * t) =
      (∅ : Set Omega) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
    calc |c| ≤ B := hcB
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * t := mul_le_mul_of_nonneg_left ht hB
  rw [hempty, measureReal_empty, IndependentSums.gammaSigma_inv]
  exact (Real.exp_pos _).le

/-! ## The normalization and the level factor -/

/-- The normalization scale `C (1 ∨ m)` of `e.km.square.bound`: the envelope
constant of `e.Enaught.mixing` at the cutoff scale `3^m`. -/
def envelopeScale (d : ℕ) (m : ℕ) : ℝ :=
  cutoffEnvelopeConst d * max 1 (m : ℝ)

theorem envelopeScale_pos (d m : ℕ) : 0 < envelopeScale d m :=
  mul_pos (cutoffEnvelopeConst_pos d) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- The level factor `3^{-(d/2)((l-m) ∨ 0)}` of `e.km.square.bound`: the
reciprocal square root of the number `3^{d(l-m)}` of scale-`m` cells in a cube
of scale `l ≥ m`, and `1` for `l ≤ m`. -/
def levelDecayFactor (d : ℕ) (m l : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(((d : ℝ) / 2) * max ((l : ℝ) - (m : ℝ)) 0))

theorem levelDecayFactor_pos (d m l : ℕ) : 0 < levelDecayFactor d m l :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The amplitude constant of the level decay: the colour-class count `(⌊√d⌋+2)^d`,
the triangle and independent-sum constants, and the centring factor `2`. -/
def envelopeLevelDecayConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 1 *
    ((shellColorPeriod d : ℝ) ^ d * Book.Ch04.gammaSigmaIndependentSumConst 1) *
    (2 * IndependentSums.gammaTriangleConst 1)

theorem envelopeLevelDecayConst_pos (d : ℕ) : 0 < envelopeLevelDecayConst d := by
  rw [envelopeLevelDecayConst]
  exact mul_pos (mul_pos (gammaTriangleConst_pos 1)
    (mul_pos (pow_pos (Nat.cast_pos.2 (shellColorPeriod_pos d)) d)
      (gammaSigmaIndependentSumConst_pos one_pos)))
    (mul_pos (by norm_num) (gammaTriangleConst_pos 1))

/-- The level-decay constant is at least `1`, which is what the range `l < m`
of the display needs, where the level factor is `1`. -/
theorem one_le_envelopeLevelDecayConst (d : ℕ) : 1 ≤ envelopeLevelDecayConst d := by
  have hΓ : (1 : ℝ) ≤ IndependentSums.gammaTriangleConst 1 := by
    rw [SuperdiffusionCLT.Probability.gammaTriangleConst_eq_of_one_le le_rfl]
    norm_num
  have hscp : (1 : ℝ) ≤ (shellColorPeriod d : ℝ) ^ d := by
    have h1 : (1 : ℕ) ≤ shellColorPeriod d :=
      Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (shellColorPeriod_pos d))
    exact one_le_pow₀ (by exact_mod_cast h1)
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hgm : (1 : ℝ) ≤ IndependentSums.gammaMomentConst 1 := by
    rw [IndependentSums.gammaMomentConst]
    have h2e : (1 : ℝ) ≤ 2 * Real.exp 1 := by linarith only [he]
    simpa using mul_le_mul h2e (le_max_left _ _) (by norm_num) (by linarith only [h2e])
  have hC : (1 : ℝ) ≤ Book.Ch04.gammaSigmaIndependentSumConst 1 := by
    rw [Book.Ch04.gammaSigmaIndependentSumConst, ite_eq_right (by norm_num : ¬(1 : ℝ) < 1)]
    change (1 : ℝ) ≤ IndependentSums.gammaSigmaExpRegimeEndpointConst 1
    rw [IndependentSums.gammaSigmaExpRegimeEndpointConst, ite_eq_left rfl,
      IndependentSums.gammaOneExpRegimeConst]
    have h4 : (4 : ℝ) ≤ 4 * Real.exp 1 * IndependentSums.gammaMomentConst 1 := by
      calc (4 : ℝ) = 4 * 1 * 1 := by norm_num
        _ ≤ 4 * Real.exp 1 * IndependentSums.gammaMomentConst 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hgm
            (by norm_num) (by positivity)
    linarith only [h4]
  rw [envelopeLevelDecayConst]
  have h1 : (1 : ℝ) ≤ IndependentSums.gammaTriangleConst 1 *
      ((shellColorPeriod d : ℝ) ^ d * Book.Ch04.gammaSigmaIndependentSumConst 1) := by
    have := mul_le_mul hΓ (mul_le_mul hscp hC (by norm_num) (by linarith only [hscp]))
      (by norm_num) (by linarith only [hΓ])
    simpa using this
  have h2 : (1 : ℝ) ≤ 2 * IndependentSums.gammaTriangleConst 1 := by linarith only [hΓ]
  have hfin := mul_le_mul h1 h2 (by norm_num) (by linarith only [h1])
  simpa using hfin

/-! ## The normalized square average on a cube -/

/-- The normalized average over the open and the half-open realization of a
triadic cube agree: the two differ by a null set. -/
theorem volumeAverage_openCubeSet_eq_cubeSet (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = volumeAverage (cubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

/-- The normalized `L²` size of the cutoff on a triadic cube, read on the
half-open realization: the manuscript's `⨍_Q |k_m|^2`. -/
def cutoffCubeSquare (m : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) : ℝ :=
  volumeAverage (cubeSet Q) (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2)

theorem cutoffCubeSquare_nonneg (m : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) :
    0 ≤ cutoffCubeSquare m Q omega := by
  rw [cutoffCubeSquare, volumeAverage]
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun x ↦ sq_nonneg _)

/-- The same average read on the open realization, which is the cube the random
factor of `e.Enaught.vs.A.and.Ahom` is defined on. -/
theorem cutoffCubeSquare_eq_openCubeSet (m : ℕ) (Q : TriadicCube d)
    (omega : ShellSeq d) :
    cutoffCubeSquare m Q omega = volumeAverage (openCubeSet Q)
      (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
  (volumeAverage_openCubeSet_eq_cubeSet Q _).symm

theorem measurable_cutoffCubeSquare (m : ℕ) (Q : TriadicCube d) :
    Measurable (cutoffCubeSquare m Q) :=
  measurable_volumeAverage_sq_streamCutoff m (cubeSet Q)

/-- The expectation of the normalized square average on a cube. -/
def cutoffCubeSquareMean (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ)
    (Q : TriadicCube d) : ℝ :=
  ∫ omega, cutoffCubeSquare m Q omega ∂P.toMeasure

theorem integrable_cutoffCubeSquare (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    Integrable (cutoffCubeSquare m Q) P.toMeasure :=
  integrable_volumeAverage_sq_streamCutoff hPrefix hJ2 hJ3 hJ4 m
    (SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero Q)
    (volume_cubeSet_lt_top Q).ne

theorem cutoffCubeSquareMean_nonneg (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ)
    (Q : TriadicCube d) : 0 ≤ cutoffCubeSquareMean P m Q :=
  integral_nonneg fun omega ↦ cutoffCubeSquare_nonneg m Q omega

/-- **The deterministic scale is the mean of the normalized square average**:
the mean bound `e.km.Ltwo.size` read at the scale of the envelope
constant. -/
theorem cutoffCubeSquareMean_le (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    cutoffCubeSquareMean P m Q ≤ envelopeScale d m := by
  have hfun : (fun omega : ShellSeq d ↦ cutoffCubeSquare m Q omega) =
      fun omega : ShellSeq d ↦ volumeAverage (openCubeSet Q)
        (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
    funext fun omega ↦ cutoffCubeSquare_eq_openCubeSet m Q omega
  rw [cutoffCubeSquareMean, envelopeScale, hfun]
  exact integral_volumeAverage_sq_le hPrefix hJ2 hJ3 hJ4 m Q

/-- **`e.km.Ltwo.size` on the half-open cube.** The upper-tail bound of
`Envelope.isBigOWith_gammaSigma_volumeAverage_sq_envelopeScale`, transposed to
the internal half-open realization of the average. -/
theorem isBigOWith_gammaSigma_cutoffCubeSquare (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (cutoffCubeSquare m Q) (envelopeScale d m) := by
  have hfun : cutoffCubeSquare m Q = fun omega : ShellSeq d ↦
      volumeAverage (openCubeSet Q)
        (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
    funext fun omega ↦ cutoffCubeSquare_eq_openCubeSet m Q omega
  rw [hfun]
  exact isBigOWith_gammaSigma_volumeAverage_sq_envelopeScale hPrefix hJ2 hJ3 hJ4 m Q

/-! ## The average is an observable of the cube's restriction lane -/

/-- The cutoff at a point of a cube is an observable of the cube's lane: it is
a finite sum of shell evaluations, each read through a shell no coarser than the
cutoff scale. -/
theorem measurable_blockCubeLane_streamCutoff (m : ℕ) (Q : TriadicCube d)
    {x : Vec d} (hx : x ∈ cubeSet Q) :
    Measurable[blockCubeLane m Q] (fun omega : ShellSeq d ↦ streamCutoff omega m x) := by
  refine @measurable_matrix_of_entries d (ShellSeq d) (blockCubeLane m Q) _ ?_
  intro i j
  have hentry : (fun omega : ShellSeq d ↦ streamCutoff omega m x i j) =
      fun omega : ShellSeq d ↦ ∑ l ∈ Finset.range (m + 1), (omega l) x i j := by
    funext omega
    exact streamCutoff_apply_entry omega m x i j
  rw [hentry]
  exact Finset.measurable_sum _ fun l hl ↦
    measurable_blockCubeLane_apply_entry Q (Nat.lt_succ_iff.mp (Finset.mem_range.1 hl)) hx i j

/-- **The normalized square average is an observable of the cube's lane**: the
Riemann sums over the centres of the cube's descendants are lane observables and
converge to the average. -/
theorem measurable_blockCubeLane_cutoffCubeSquare (m : ℕ) (Q : TriadicCube d) :
    Measurable[blockCubeLane m Q] (cutoffCubeSquare m Q) := by
  classical
  have hstep : ∀ i : ℕ, Measurable[blockCubeLane m Q]
      (fun omega : ShellSeq d ↦ descendantCenterAverage Q i
        (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2)) := by
    intro i
    refine Measurable.const_mul (Finset.measurable_sum _ fun R hR ↦ ?_) _
    have hcenter : cubeCenter R ∈ cubeSet Q :=
      cubeSet_subset_of_mem_descendantsAtDepth hR (cubeCenter_mem_cubeSet R)
    exact (((continuous_pow 2).measurable.comp
      ShellField.continuous_matrixOperatorNorm.measurable).comp
      (measurable_blockCubeLane_streamCutoff m Q hcenter))
  have hlim : cutoffCubeSquare m Q = fun omega : ShellSeq d ↦ Filter.limsup
      (fun i : ℕ ↦ descendantCenterAverage Q i
        (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2)) Filter.atTop := by
    funext omega
    refine (Filter.Tendsto.limsup_eq ?_).symm
    exact tendsto_descendantCenterAverage Q
      ((ShellField.continuous_matrixOperatorNorm.comp
        (continuous_streamCutoff_apply omega m)).pow 2)
  rw [hlim]
  exact Measurable.limsup hstep

/-! ## Independence of the sub-cube variables -/

/-- **The normalized square averages of a same-colour family of scale-`m` cubes
are mutually independent**: the range of dependence `ShellLawJ1Restriction` at
`√d 3^m`, read through the lane observability of the average. -/
theorem iIndepFun_cutoffCubeSquare {iota : Type*}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (m : ℕ) {Q : iota → TriadicCube d}
    (hscale : ∀ i, (Q i).scale = (m : ℤ)) (hne : Function.Injective Q)
    (hcolor : ∀ i j, cubeShellColor (Q i) = cubeShellColor (Q j)) :
    iIndepFun (fun (i : iota) (omega : ShellSeq d) ↦ cutoffCubeSquare m (Q i) omega)
      P.toMeasure := by
  refine iIndepFun_of_blockLane_shellRestrictionSigma hJ1 hJ2 m
    (U := fun i ↦ cubeSet (Q i)) (fun i ↦ measurableSet_cubeSet (Q i))
    (fun i ↦ measurable_blockCubeLane_cutoffCubeSquare m (Q i)) ?_
  intro i j hij
  exact ShellField.areShellSeparated_cubeSet_of_cubeShellColor_eq (hscale i) (hscale j)
    (hcolor i j) (fun hcon ↦ hij (hne hcon))

/-! ## The centred sub-cube variable -/

/-- The normalized square average of a cube, centred by its expectation. -/
def centeredCutoffCubeSquare (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ)
    (Q : TriadicCube d) (omega : ShellSeq d) : ℝ :=
  cutoffCubeSquare m Q omega - cutoffCubeSquareMean P m Q

theorem measurable_centeredCutoffCubeSquare (P : ProbabilityMeasure (ShellSeq d))
    (m : ℕ) (Q : TriadicCube d) : Measurable (centeredCutoffCubeSquare P m Q) :=
  (measurable_cutoffCubeSquare m Q).sub measurable_const

theorem integral_centeredCutoffCubeSquare_eq_zero
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    ∫ omega, centeredCutoffCubeSquare P m Q omega ∂P.toMeasure = 0 := by
  have hint := integrable_cutoffCubeSquare hPrefix hJ2 hJ3 hJ4 m Q
  simp only [centeredCutoffCubeSquare]
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, smul_eq_mul,
    one_mul, cutoffCubeSquareMean, sub_self]

/-- The centred sub-cube variable has a `Γ_1` tail at the deterministic scale,
inflated by the two-term triangle constant and the centring cost. -/
theorem isBigO_gammaSigma_centeredCutoffCubeSquare
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (centeredCutoffCubeSquare P m Q)
      (IndependentSums.gammaTriangleConst 1 * (2 * envelopeScale d m)) := by
  have hSpos : 0 < envelopeScale d m := envelopeScale_pos d m
  have hmean := cutoffCubeSquareMean_le hPrefix hJ2 hJ3 hJ4 m Q
  have hZ : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (cutoffCubeSquare m Q) (envelopeScale d m) :=
    (isBigOWith_iff_isBigO_of_nonneg fun omega ↦ cutoffCubeSquare_nonneg m Q omega).1
      (isBigOWith_gammaSigma_cutoffCubeSquare hPrefix hJ2 hJ3 hJ4 m Q)
  have hM : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun _ : ShellSeq d ↦ -cutoffCubeSquareMean P m Q) (envelopeScale d m) :=
    isBigO_gammaSigma_const P.toMeasure (by
      rw [abs_neg, abs_of_nonneg (cutoffCubeSquareMean_nonneg P m Q)]
      exact hmean)
  have hsum := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) one_pos hSpos hSpos hZ
    hM (measurable_cutoffCubeSquare m Q) measurable_const
  have hfun : (fun omega : ShellSeq d ↦
      cutoffCubeSquare m Q omega + -cutoffCubeSquareMean P m Q) =
      centeredCutoffCubeSquare P m Q := by
    funext omega
    rw [centeredCutoffCubeSquare, ← sub_eq_add_neg]
  rw [hfun] at hsum
  refine hsum.mono_scale (le_of_eq ?_)
  ring

/-! ## Concentration of the colour-class sums -/

/-- **Concentration of one colour-class sum of centred sub-cube variables**:
`Book.Ch04`'s centred independent-sum concentration (the manuscript's
`p.concentration`) at `Γ_1`, fed by `iIndepFun_cutoffCubeSquare`. -/
theorem isBigO_gammaSigma_centeredCutoffCubeSquareColorClassSum
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ} (hml : m ≤ l)
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) (c : ShellCubeColor d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦
        ∑ R ∈ (descendantsAtDepth Q (l - m)).filter fun S ↦ cubeShellColor S = c,
          centeredCutoffCubeSquare P m R omega)
      (Book.Ch04.gammaSigmaIndependentSumConst 1 *
        Real.sqrt (((descendantsAtDepth Q (l - m)).card : ℕ) : ℝ) *
        (IndependentSums.gammaTriangleConst 1 * (2 * envelopeScale d m))) := by
  classical
  set Dc : Finset (TriadicCube d) :=
    (descendantsAtDepth Q (l - m)).filter fun S ↦ cubeShellColor S = c with hDc
  set K : ℝ := IndependentSums.gammaTriangleConst 1 * (2 * envelopeScale d m) with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (gammaTriangleConst_pos 1) (mul_pos (by norm_num) (envelopeScale_pos d m))
  have hCpos : 0 < Book.Ch04.gammaSigmaIndependentSumConst 1 :=
    gammaSigmaIndependentSumConst_pos one_pos
  by_cases hne : Dc.Nonempty
  · have hattach : Dc.attach.Nonempty := by simpa using hne
    have hscale : ∀ R : {R : TriadicCube d // R ∈ Dc}, (R.1).scale = (m : ℤ) := by
      intro R
      have hR : R.1 ∈ descendantsAtDepth Q (l - m) := (Finset.mem_filter.mp R.2).1
      rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hQ, Nat.cast_sub hml]
      omega
    have hcolor : ∀ R S : {R : TriadicCube d // R ∈ Dc},
        cubeShellColor R.1 = cubeShellColor S.1 := by
      intro R S
      exact (Finset.mem_filter.mp R.2).2.trans (Finset.mem_filter.mp S.2).2.symm
    have hindepY := iIndepFun_cutoffCubeSquare (P := P) hJ1 hJ2 m
      (Q := fun R : {R : TriadicCube d // R ∈ Dc} ↦ R.1) hscale
      Subtype.coe_injective hcolor
    have hindep : iIndepFun
        (fun (R : {R : TriadicCube d // R ∈ Dc}) (omega : ShellSeq d) ↦
          centeredCutoffCubeSquare P m R.1 omega) P.toMeasure :=
      hindepY.comp (fun R : {R : TriadicCube d // R ∈ Dc} ↦
        fun y : ℝ ↦ y - cutoffCubeSquareMean P m R.1)
        (fun _ ↦ measurable_id.sub_const _)
    have hmeas : ∀ R : {R : TriadicCube d // R ∈ Dc},
        Measurable (fun omega : ShellSeq d ↦ centeredCutoffCubeSquare P m R.1 omega) :=
      fun R ↦ measurable_centeredCutoffCubeSquare P m R.1
    have htail : ∀ R ∈ Dc.attach,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
          (fun omega : ShellSeq d ↦ centeredCutoffCubeSquare P m R.1 omega) K :=
      fun R _ ↦ by
        rw [hK]
        exact isBigO_gammaSigma_centeredCutoffCubeSquare hPrefix hJ2 hJ3 hJ4 m R.1
    have hmean : ∀ R ∈ Dc.attach,
        ∫ omega, centeredCutoffCubeSquare P m R.1 omega ∂P.toMeasure = 0 :=
      fun R _ ↦ integral_centeredCutoffCubeSquare_eq_zero hPrefix hJ2 hJ3 hJ4 m R.1
    have hsum :=
      Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := P.toMeasure)
        (X := fun (R : {R : TriadicCube d // R ∈ Dc}) (omega : ShellSeq d) ↦
          centeredCutoffCubeSquare P m R.1 omega)
        (s := Dc.attach) (σ := 1) (K := K)
        hindep hmeas hattach one_pos (by norm_num) hKpos htail hmean
    have hattach_eq : (fun omega : ShellSeq d ↦
        ∑ R ∈ Dc.attach, centeredCutoffCubeSquare P m R.1 omega) =
        fun omega : ShellSeq d ↦
          ∑ R ∈ Dc, centeredCutoffCubeSquare P m R omega := by
      funext omega
      exact Finset.sum_attach Dc fun R ↦ centeredCutoffCubeSquare P m R omega
    rw [hattach_eq] at hsum
    rw [hDc] at hsum
    refine hsum.mono_scale ?_
    rw [Finset.card_attach]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_filter_le _ _)) hCpos.le) hKpos.le
  · have hempty : Dc = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : (fun omega : ShellSeq d ↦
        ∑ R ∈ Dc, centeredCutoffCubeSquare P m R omega) =
        fun _ : ShellSeq d ↦ (0 : ℝ) := by
      funext omega
      rw [hempty, Finset.sum_empty]
    rw [hzero]
    refine isBigO_gammaSigma_const P.toMeasure ?_
    rw [abs_zero]
    exact mul_nonneg (mul_nonneg hCpos.le (Real.sqrt_nonneg _)) hKpos.le

/-! ## The average over the sub-cubes -/

/-- **The centred sub-cube average carries the printed decay.** The colour
classes are recombined by the finite triangle inequality, and dividing by the
number `3^{d(l-m)}` of sub-cubes turns `√N / N` into `3^{-(d/2)(l-m)}`. -/
theorem isBigO_gammaSigma_centeredCutoffCubeSquareSubcubeAverage
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ} (hml : m ≤ l)
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ (((descendantsAtDepth Q (l - m)).card : ℕ) : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q (l - m), centeredCutoffCubeSquare P m R omega)
      (envelopeScale d m * (envelopeLevelDecayConst d * levelDecayFactor d m l)) := by
  classical
  set D : Finset (TriadicCube d) := descendantsAtDepth Q (l - m) with hD
  set K : ℝ := IndependentSums.gammaTriangleConst 1 * (2 * envelopeScale d m) with hK
  have hneColor : Nonempty (ShellCubeColor d) :=
    ⟨fun _ ↦ ⟨0, shellColorPeriod_pos d⟩⟩
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (gammaTriangleConst_pos 1) (mul_pos (by norm_num) (envelopeScale_pos d m))
  have hCpos : 0 < Book.Ch04.gammaSigmaIndependentSumConst 1 :=
    gammaSigmaIndependentSumConst_pos one_pos
  have hcard : D.card = (3 ^ d) ^ (l - m) := by
    rw [hD]
    exact descendantsAtDepth_card Q (l - m)
  have hNpos : (0 : ℝ) < ((D.card : ℕ) : ℝ) := by
    have hpos : 0 < D.card := by
      rw [hcard]
      positivity
    exact_mod_cast hpos
  have hclass : ∀ c ∈ (Finset.univ : Finset (ShellCubeColor d)),
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
        (fun omega : ShellSeq d ↦
          ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
            centeredCutoffCubeSquare P m R omega)
        (Book.Ch04.gammaSigmaIndependentSumConst 1 *
          Real.sqrt ((D.card : ℕ) : ℝ) * K) :=
    fun c _ ↦ by
      rw [hD, hK]
      exact isBigO_gammaSigma_centeredCutoffCubeSquareColorClassSum
        hPrefix hJ1 hJ2 hJ3 hJ4 hml hQ c
  have hclassMeas : ∀ c ∈ (Finset.univ : Finset (ShellCubeColor d)),
      Measurable (fun omega : ShellSeq d ↦
        ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
          centeredCutoffCubeSquare P m R omega) :=
    fun c _ ↦ Finset.measurable_sum _ fun R _ ↦
      measurable_centeredCutoffCubeSquare P m R
  have htriangle := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (ShellCubeColor d))
    (X := fun c omega ↦
      ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
        centeredCutoffCubeSquare P m R omega)
    (a := fun _ : ShellCubeColor d ↦
      Book.Ch04.gammaSigmaIndependentSumConst 1 *
        Real.sqrt ((D.card : ℕ) : ℝ) * K)
    (σ := 1) one_pos Finset.univ_nonempty
    (fun _ _ ↦ mul_pos (mul_pos hCpos (Real.sqrt_pos.2 hNpos)) hKpos)
    hclass hclassMeas
  have hfiber : (fun omega : ShellSeq d ↦
      ∑ c : ShellCubeColor d, ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
        centeredCutoffCubeSquare P m R omega) =
      fun omega : ShellSeq d ↦
        ∑ R ∈ D, centeredCutoffCubeSquare P m R omega := by
    funext omega
    exact Finset.sum_fiberwise D cubeShellColor
      fun R ↦ centeredCutoffCubeSquare P m R omega
  rw [hfiber] at htriangle
  have hscaled := htriangle.const_mul (c := ((D.card : ℕ) : ℝ)⁻¹)
    (inv_nonneg.2 hNpos.le)
  have hsumconst : ∑ _c : ShellCubeColor d,
      (Book.Ch04.gammaSigmaIndependentSumConst 1 *
        Real.sqrt ((D.card : ℕ) : ℝ) * K) =
      ((shellColorPeriod d : ℝ) ^ d) *
        (Book.Ch04.gammaSigmaIndependentSumConst 1 *
          Real.sqrt ((D.card : ℕ) : ℝ) * K) := by
    have hcolorcard : (Finset.univ : Finset (ShellCubeColor d)).card =
        shellColorPeriod d ^ d := by simp
    rw [Finset.sum_const, nsmul_eq_mul, hcolorcard]
    push_cast
    ring
  have hdecay : ((D.card : ℕ) : ℝ)⁻¹ * Real.sqrt ((D.card : ℕ) : ℝ) =
      levelDecayFactor d m l := by
    have hNval : ((D.card : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((l - m : ℕ) : ℝ)) := by
      rw [hcard]
      push_cast
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (d : ℕ)) (l - m),
        ← Real.rpow_natCast (3 : ℝ) d, ← Real.rpow_mul (by norm_num)]
    have hmain : ((D.card : ℕ) : ℝ)⁻¹ * Real.sqrt ((D.card : ℕ) : ℝ) =
        ((D.card : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hNpos]
      congr 1
      norm_num
    have hk : max ((l : ℝ) - (m : ℝ)) 0 = ((l - m : ℕ) : ℝ) := by
      rw [Nat.cast_sub hml]
      exact max_eq_left (sub_nonneg.2 (Nat.cast_le.2 hml))
    rw [hmain, hNval, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), levelDecayFactor, hk]
    congr 1
    ring
  refine hscaled.mono_scale (le_of_eq ?_)
  rw [hsumconst, hK, envelopeLevelDecayConst, ← hdecay]
  ring

/-! ## The display `e.km.square.bound` -/

/-- The range `m ≤ l` of `e.km.square.bound` at the half-open realization: the
partition identity writes `⨍_Q |k_m|^2` as the average of the sub-cube averages,
whose means are bounded by the deterministic scale and whose centred parts are
controlled by the colour-class concentration. -/
private theorem cutoffCubeFluctuation_of_le
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ} (hml : m ≤ l)
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ (envelopeScale d m)⁻¹ * cutoffCubeSquare m Q omega - 1)
      (envelopeLevelDecayConst d * levelDecayFactor d m l) := by
  classical
  set D : Finset (TriadicCube d) := descendantsAtDepth Q (l - m) with hD
  set S : ℝ := envelopeScale d m with hS
  set M : ShellSeq d → ℝ := fun omega ↦ ((D.card : ℕ) : ℝ)⁻¹ *
    ∑ R ∈ D, centeredCutoffCubeSquare P m R omega with hM
  have hSpos : 0 < S := by
    rw [hS]
    exact envelopeScale_pos d m
  have hNpos : (0 : ℝ) < ((D.card : ℕ) : ℝ) := by
    have hcard : D.card = (3 ^ d) ^ (l - m) := by
      rw [hD]
      exact descendantsAtDepth_card Q (l - m)
    have hpos : 0 < D.card := by
      rw [hcard]
      positivity
    exact_mod_cast hpos
  have hMtail : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) M
      (S * (envelopeLevelDecayConst d * levelDecayFactor d m l)) := by
    rw [hM, hS, hD]
    exact isBigO_gammaSigma_centeredCutoffCubeSquareSubcubeAverage
      hPrefix hJ1 hJ2 hJ3 hJ4 hml hQ
  have hOneSided : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      M (S * (envelopeLevelDecayConst d * levelDecayFactor d m l)) :=
    IndependentSums.IsBigOWith.of_le hMtail fun omega ↦ le_abs_self (M omega)
  have hScaled : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ M omega / S)
      (envelopeLevelDecayConst d * levelDecayFactor d m l) := by
    have hc := hOneSided.const_mul (c := S⁻¹) (inv_nonneg.2 hSpos.le)
    have hfun : (fun omega : ShellSeq d ↦ S⁻¹ * M omega) =
        fun omega : ShellSeq d ↦ M omega / S := by
      funext omega
      rw [div_eq_inv_mul]
    rw [hfun] at hc
    refine hc.mono_scale (le_of_eq ?_)
    rw [← mul_assoc, inv_mul_cancel₀ hSpos.ne', one_mul]
  refine IndependentSums.IsBigOWith.of_le hScaled ?_
  intro omega
  have hcont : Continuous
      (fun x : Vec d ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) :=
    (ShellField.continuous_matrixOperatorNorm.comp
      (continuous_streamCutoff_apply omega m)).pow 2
  have hpart : cutoffCubeSquare m Q omega =
      ((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquare m R omega := by
    rw [hD]
    simp only [cutoffCubeSquare]
    exact volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants Q (l - m)
      (fun R _ ↦
        SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_cubeSet_of_continuous
          R hcont)
  have hsplit : ∑ R ∈ D, cutoffCubeSquare m R omega =
      (∑ R ∈ D, centeredCutoffCubeSquare P m R omega) +
        ∑ R ∈ D, cutoffCubeSquareMean P m R := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun R _ ↦ by
      rw [centeredCutoffCubeSquare, sub_add_cancel]
  have hmbar : ((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquareMean P m R ≤ S := by
    have hterm : ∀ R ∈ D, cutoffCubeSquareMean P m R ≤ S := fun R _ ↦ by
      rw [hS]
      exact cutoffCubeSquareMean_le hPrefix hJ2 hJ3 hJ4 m R
    have hsum : ∑ R ∈ D, cutoffCubeSquareMean P m R ≤ ((D.card : ℕ) : ℝ) * S := by
      calc ∑ R ∈ D, cutoffCubeSquareMean P m R ≤ ∑ _R ∈ D, S := Finset.sum_le_sum hterm
        _ = ((D.card : ℕ) : ℝ) * S := by rw [Finset.sum_const, nsmul_eq_mul]
    calc ((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquareMean P m R
        ≤ ((D.card : ℕ) : ℝ)⁻¹ * (((D.card : ℕ) : ℝ) * S) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNpos.le)
      _ = S := by rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
  have hZ : cutoffCubeSquare m Q omega =
      M omega + ((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquareMean P m R := by
    simp only [hpart, hsplit, hM]
    ring
  rw [hZ, mul_add]
  have hdiv : S⁻¹ * (((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquareMean P m R) =
      (((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquareMean P m R) / S :=
    (div_eq_inv_mul _ _).symm
  rw [hdiv, ← div_eq_inv_mul]
  have hle : (((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cutoffCubeSquareMean P m R) / S ≤ 1 :=
    (div_le_one hSpos).2 hmbar
  linarith only [hle]

/-- The range `l < m` of `e.km.square.bound`: the level factor is `1`, so the
amplitude is the constant `envelopeLevelDecayConst d`, which the envelope
tail `e.km.Ltwo.size` supplies once the average is centred by `1` and scaled by
`envelopeScale d m`. -/
private theorem cutoffCubeFluctuation_of_lt
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ} (hmlt : l < m)
    {Q : TriadicCube d} :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ (envelopeScale d m)⁻¹ * cutoffCubeSquare m Q omega - 1)
      (envelopeLevelDecayConst d * levelDecayFactor d m l) := by
  have hfac : levelDecayFactor d m l = 1 := by
    rw [levelDecayFactor]
    have hmax : max ((l : ℝ) - (m : ℝ)) 0 = 0 :=
      max_eq_right (sub_nonpos.2 (Nat.cast_le.2 (le_of_lt hmlt)))
    rw [hmax, mul_zero, neg_zero, Real.rpow_zero]
  have hSpos : 0 < envelopeScale d m := envelopeScale_pos d m
  have hZ : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (cutoffCubeSquare m Q) (envelopeScale d m) :=
    IndependentSums.IsBigOWith.of_le
      ((isBigOWith_iff_isBigO_of_nonneg fun omega ↦ cutoffCubeSquare_nonneg m Q omega).1
        (isBigOWith_gammaSigma_cutoffCubeSquare hPrefix hJ2 hJ3 hJ4 m Q))
      fun omega ↦ le_abs_self (cutoffCubeSquare m Q omega)
  have hone : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ (envelopeScale d m)⁻¹ * cutoffCubeSquare m Q omega) 1 :=
    (hZ.const_mul (c := (envelopeScale d m)⁻¹) (inv_nonneg.2 hSpos.le)).mono_scale
      (le_of_eq (inv_mul_cancel₀ hSpos.ne'))
  refine (IndependentSums.IsBigOWith.of_le hone
    fun omega ↦ sub_le_self _ zero_le_one).mono_scale ?_
  rw [hfac, mul_one]
  exact one_le_envelopeLevelDecayConst d

/-- **The normalized square average stays within the level decay of `1`.** The
printed level factor `3^{-(d/2)((l-m) ∨ 0)}` is read in both ranges: for `m ≤ l`
by the sub-cube concentration, and for `l < m`, where the factor is `1`, by the
envelope tail at the constant amplitude. This is the pointwise input of
`e.km.square.bound`, in the internal half-open realization of the average. -/
theorem isBigOWith_gammaSigma_cutoffCubeFluctuation
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ}
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ (envelopeScale d m)⁻¹ * cutoffCubeSquare m Q omega - 1)
      (envelopeLevelDecayConst d * levelDecayFactor d m l) := by
  rcases le_or_gt m l with hml | hmlt
  · exact cutoffCubeFluctuation_of_le hPrefix hJ1 hJ2 hJ3 hJ4 hml hQ
  · exact cutoffCubeFluctuation_of_lt hPrefix hJ2 hJ3 hJ4 hmlt

/-- **The display `e.km.square.bound`**: for a triadic cube `Q` of scale `l`, the normalized
`L²` size of the cutoff, less its deterministic value `1`, has a `Γ_1` upper tail at the
printed amplitude `C 3^{-(d/2)((l-m) ∨ 0)}`, `C = envelopeLevelDecayConst d`. -/
theorem isBigOWith_gammaSigma_cutoffCubeSquareNormalized
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ}
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d ↦ (cutoffEnvelopeConst d * max 1 (m : ℝ))⁻¹ *
        volumeAverage (openCubeSet Q)
          (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) - 1)
      (envelopeLevelDecayConst d * levelDecayFactor d m l) := by
  have hfun : (fun omega : ShellSeq d ↦ (cutoffEnvelopeConst d * max 1 (m : ℝ))⁻¹ *
      volumeAverage (openCubeSet Q)
        (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) - 1) =
      fun omega : ShellSeq d ↦ (envelopeScale d m)⁻¹ * cutoffCubeSquare m Q omega - 1 := by
    funext omega
    rw [envelopeScale, cutoffCubeSquare_eq_openCubeSet]
  rw [hfun]
  exact isBigOWith_gammaSigma_cutoffCubeFluctuation hPrefix hJ1 hJ2 hJ3 hJ4 hQ

/-! ## The per-scale tail of the random factor -/

/-- **The per-scale tail of `envelopeRatio` with the level decay.** The random
factor of `e.Enaught.vs.A.and.Ahom` is the maximum of `1` and the normalized
square average, so the level decay transfers to it at the threshold
`1 + C levelDecayFactor d m l * t`, with the tail `exp (-t)`. -/
theorem measureReal_envelopeRatio_gt_levelDecay_le
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ}
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) {t : ℝ} (ht : 1 ≤ t) :
    P.toMeasure.real {omega : ShellSeq d |
        1 + (envelopeLevelDecayConst d * levelDecayFactor d m l) * t <
          envelopeRatio m Q omega} ≤ Real.exp (-t) := by
  have hApos : 0 < envelopeLevelDecayConst d * levelDecayFactor d m l :=
    mul_pos (envelopeLevelDecayConst_pos d) (levelDecayFactor_pos d m l)
  have hAt : 0 ≤ (envelopeLevelDecayConst d * levelDecayFactor d m l) * t :=
    mul_nonneg hApos.le (le_trans zero_le_one ht)
  have h := isBigOWith_gammaSigma_cutoffCubeSquareNormalized (m := m) (l := l)
    hPrefix hJ1 hJ2 hJ3 hJ4 hQ ht
  refine (measureReal_mono ?_).trans (h.trans (le_of_eq ?_))
  · intro omega hom
    have hmax : 1 + (envelopeLevelDecayConst d * levelDecayFactor d m l) * t <
        max 1 (volumeAverage (openCubeSet Q)
          (fun x ↦ matrixOperatorNorm (streamCutoff omega m x) ^ 2) /
            (cutoffEnvelopeConst d * max 1 (m : ℝ))) := hom
    rcases lt_max_iff.1 hmax with h1 | h2
    · exfalso
      linarith only [h1, hAt]
    · rw [div_eq_inv_mul] at h2
      rw [IndependentSums.mem_upperTailEvent]
      linarith only [h2]
  · rw [IndependentSums.gammaSigma_apply, Real.rpow_one, ← Real.exp_neg]

/-- The per-scale tail in the threshold form used by the union bound over the
sub-cubes of `cu_n`: the scale-`l` cube carries the threshold `s` and the tail
`exp (-(s - 1) / (C levelDecayFactor d m l))`. -/
theorem measureReal_envelopeRatio_gt_le_levelDecay
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {m l : ℕ}
    {Q : TriadicCube d} (hQ : Q.scale = (l : ℤ)) {s : ℝ}
    (hs : 1 + envelopeLevelDecayConst d * levelDecayFactor d m l ≤ s) :
    P.toMeasure.real {omega : ShellSeq d | s < envelopeRatio m Q omega} ≤
      Real.exp (-((s - 1) / (envelopeLevelDecayConst d * levelDecayFactor d m l))) := by
  have hApos : 0 < envelopeLevelDecayConst d * levelDecayFactor d m l :=
    mul_pos (envelopeLevelDecayConst_pos d) (levelDecayFactor_pos d m l)
  have ht : 1 ≤ (s - 1) / (envelopeLevelDecayConst d * levelDecayFactor d m l) := by
    rw [one_le_div hApos]
    linarith only [hs]
  refine (measureReal_mono ?_).trans
    (measureReal_envelopeRatio_gt_levelDecay_le (m := m) (l := l)
      hPrefix hJ1 hJ2 hJ3 hJ4 hQ ht)
  intro omega hom
  have hmul : (envelopeLevelDecayConst d * levelDecayFactor d m l) *
      ((s - 1) / (envelopeLevelDecayConst d * levelDecayFactor d m l)) = s - 1 := by
    calc (envelopeLevelDecayConst d * levelDecayFactor d m l) *
          ((s - 1) / (envelopeLevelDecayConst d * levelDecayFactor d m l))
        = (s - 1) * ((envelopeLevelDecayConst d * levelDecayFactor d m l) /
            (envelopeLevelDecayConst d * levelDecayFactor d m l)) := by ring
      _ = s - 1 := by rw [div_self hApos.ne', mul_one]
  have : 1 + (envelopeLevelDecayConst d * levelDecayFactor d m l) *
      ((s - 1) / (envelopeLevelDecayConst d * levelDecayFactor d m l)) = s := by
    rw [hmul]
    ring
  rw [this]
  exact hom

end

end SuperdiffusionCLT.Section2.Annealed
