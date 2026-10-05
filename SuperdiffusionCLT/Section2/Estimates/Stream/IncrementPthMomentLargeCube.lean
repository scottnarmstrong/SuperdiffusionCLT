/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Estimates.Stream.SpatialAverageTail

/-!
# The improved `p`-th moment display on cubes above the cutoff scale

Display `e.kl.bounds.large` of the paper: for `p ≥ 1` and `n < m ≤ l`,

`⨍_{cu_l} |(k_m - k_n)(x)|^p dx
  ≤ C (m-n)^{p/2} + O_{Γ_{2/p}}((Cp)^{p/2} (m-n)^{p/2} 3^{-(d/2)(l-m)})`.

This improves the uniform display `e.kmn.bounds`
(`isBigO_gammaSigma_finiteShellIncrementPthMoment`), whose
amplitude `C^p (m-n)^{p/2}` carries no decay in `l - m`, on every cube above
the cutoff scale `3^m`.

## The proof

The average over `cu_l` is the plain average over the `3^{d(l-m)}` sub-cubes of
scale `m` of the averages over those sub-cubes
(`volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants`). Each sub-cube
average carries the uniform `Γ_{2/p}` tail, which is available on an
arbitrary cube, so each has a finite expectation bounded by the same amplitude
times the Chapter 4 moment constant; subtracting it centres the variable and
costs only the two-term triangle inequality.

The centred sub-cube variables of one colour class are mutually independent:
by the restriction-lane range of dependence (`ShellLawJ1Restriction`) and the shell
independence (`ShellLawJ2`), the joined
restriction lanes of pairwise separated cubes are independent, and the sub-cube
moment is an observable of its own lane
(`measurable_blockCubeLane_finiteShellIncrementCubePthMoment`). Distinct
scale-`m` cubes of one colour of `ShellField.cubeShellColor` are separated at
the range `sqrt d 3^m`, which is exactly the printed range of dependence of
`k_m - k_n`.

`CoarseGraining`'s concentration inequality for centred independent
`Γ_σ` variables (the paper's Proposition `p.concentration`) bounds each
colour-class sum by `C_σ √(class card)` times the common amplitude; the finite
triangle inequality over the `(⌊√d⌋+2)^d` colours and the
division by the number of sub-cubes turn `√N / N = N^{-1/2}` into the printed
decay `3^{-(d/2)(l-m)}`.

## Why the display is not a single tail bound

One might try to state this display in the folded
form `IsBigO (gammaSigma (2/p)) (⨍_{cu_l} |k_m - k_n|^p) (amplitude with the
decay)`. That folded form is not the printed display and is not provable: the
moment is a nonnegative variable whose expectation is of order `(m-n)^{p/2}`
and does not decay in `l - m`, whereas `IsBigO μ Ψ X A` forces
`μ{|X| > A} ≤ exp(-1)`, which fails once `A` is small. The printed display
keeps the deterministic leading term `C (m-n)^{p/2}` outside the tail, and that
is the shape proved here, in the witness form used for the clauses of the
"Moreover" block.

## Main definitions

* `largeCubePthMomentMeanConst`: the deterministic leading constant.
* `largeCubePthMomentTailConst`: the explicit tail constant.

## Main results

* `isBigO_gammaSigma_centeredCubePthMomentColorClassSum`: concentration of one
  colour-class sum.
* `isBigO_gammaSigma_centeredCubePthMomentSubcubeAverage`: the average over all
  sub-cubes of the centred moments, at the printed decay.
* `exists_witness_finiteShellIncrementPthMomentLargeCube`: the display
  `e.kl.bounds.large`.

## References

* `e.kl.bounds.large`, `p.concentration`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff

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

private theorem finiteShellIncrementPthMomentConst_pos
    (hPrefix : ShellLawPrefix d P) {p : ℝ} (hp : (1 : ℝ) ≤ p) :
    0 < finiteShellIncrementPthMomentConst d p := by
  have hsigma : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hbase : (0 : ℝ) < Real.exp 1 * IndependentSums.gammaMomentConst (2 / p) :=
    mul_pos (Real.exp_pos 1) (IndependentSums.gammaMomentConst_pos hsigma)
  rw [finiteShellIncrementPthMomentConst]
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (streamLinftyConst_pos hPrefix)

/-! ## The constants of the display -/

/-- The deterministic leading constant of display `e.kl.bounds.large`: the
Chapter 4 moment constant at index `2/p` times the amplitude constant of the
uniform display `e.kmn.bounds`. -/
def largeCubePthMomentMeanConst (d : ℕ) (p : ℝ) : ℝ :=
  IndependentSums.gammaMomentConst (2 / p) *
    finiteShellIncrementPthMomentConst d p ^ p

/-- The amplitude constant of the tail of display `e.kl.bounds.large`: one
colour triangle constant, the number of colours, `CoarseGraining`'s
independent-sum constant at index `2/p`, and the centring cost applied to the
amplitude constant of the uniform display. -/
def largeCubePthMomentTailConst (d : ℕ) (p : ℝ) : ℝ :=
  IndependentSums.gammaTriangleConst (2 / p) *
    ((ShellField.shellColorPeriod d : ℝ) ^ d *
      Book.Ch04.gammaSigmaIndependentSumConst (2 / p)) *
    (IndependentSums.gammaTriangleConst (2 / p) *
      ((1 + IndependentSums.gammaMomentConst (2 / p)) *
        finiteShellIncrementPthMomentConst d p ^ p))

/-! ## The centred sub-cube moment -/

/-- The amplitude of the uniform sub-cube moment display `e.kmn.bounds`
at exponent `p` and gap `m - n`. -/
def cubePthMomentAmplitude (d : ℕ) (p : ℝ) (n m : ℕ) : ℝ :=
  finiteShellIncrementPthMomentConst d p ^ p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p

theorem cubePthMomentAmplitude_pos (hPrefix : ShellLawPrefix d P) {p : ℝ}
    (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m) :
    0 < cubePthMomentAmplitude d p n m := by
  have hgap : 0 < ((m - n : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hnm
  rw [cubePthMomentAmplitude]
  exact mul_pos
    (Real.rpow_pos_of_pos (finiteShellIncrementPthMomentConst_pos hPrefix hp) p)
    (Real.rpow_pos_of_pos (Real.sqrt_pos.2 hgap) p)

/-- The sub-cube moment is measurable for the canonical sequence sigma-field. -/
theorem measurable_finiteShellIncrementCubePthMoment (n m : ℕ) {p : ℝ}
    (hp : (0 : ℝ) ≤ p) (Q : TriadicCube d) :
    Measurable (finiteShellIncrementCubePthMoment n m p Q) :=
  (measurable_blockCubeLane_finiteShellIncrementCubePthMoment n m hp Q).mono
    (Section3.HighContrast.blockLane_le
      (ShellField.shellRestrictionSigma_le (cubeSet Q) (measurableSet_cubeSet Q)))
    le_rfl

/-- The uniform display `e.kmn.bounds` read on one sub-cube. -/
theorem isBigO_gammaSigma_finiteShellIncrementCubePthMoment
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m)
    (Q : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (finiteShellIncrementCubePthMoment n m p Q)
      (cubePthMomentAmplitude d p n m) :=
  isBigO_gammaSigma_finiteShellIncrementPthMoment hPrefix hJ2 hJ3 hJ4 hp hnm Q

/-- The expectation of the sub-cube moment. -/
def cubePthMomentMean (P : ProbabilityMeasure (ShellSeq d)) (n m : ℕ) (p : ℝ)
    (Q : TriadicCube d) : ℝ :=
  ∫ omega, finiteShellIncrementCubePthMoment n m p Q omega ∂P.toMeasure

/-- The sub-cube moment is integrable, with expectation bounded by the Chapter 4
moment constant times the uniform amplitude. -/
theorem integrable_and_abs_cubePthMomentMean_le
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m)
    (Q : TriadicCube d) :
    Integrable (finiteShellIncrementCubePthMoment n m p Q) P.toMeasure ∧
      |cubePthMomentMean P n m p Q| ≤
        IndependentSums.gammaMomentConst (2 / p) * cubePthMomentAmplitude d p n m := by
  have hsigma : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hApos : 0 < cubePthMomentAmplitude d p n m :=
    cubePthMomentAmplitude_pos hPrefix hp hnm
  have hmeas := measurable_finiteShellIncrementCubePthMoment n m
    (le_trans (by norm_num) hp) Q
  have htail := isBigO_gammaSigma_finiteShellIncrementCubePthMoment
    hPrefix hJ2 hJ3 hJ4 hp hnm Q
  have hgrowth := Book.Ch04.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (μ := P.toMeasure) hsigma hApos hmeas.aemeasurable htail
  obtain ⟨hint1, _⟩ := hgrowth (le_refl (1 : ℝ))
  have habs : (fun omega ↦ |finiteShellIncrementCubePthMoment n m p Q omega| ^ (1 : ℝ)) =
      finiteShellIncrementCubePthMoment n m p Q := by
    funext omega
    rw [Real.rpow_one,
      abs_of_nonneg (finiteShellIncrementCubePthMoment_nonneg n m p Q omega)]
  rw [habs] at hint1
  refine ⟨hint1, ?_⟩
  have hmoment := Book.Ch04.integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := P.toMeasure) hsigma hApos (le_refl (1 : ℝ)) hmeas.aemeasurable htail
  rw [habs, Real.one_rpow, mul_one, Real.rpow_one] at hmoment
  rw [cubePthMomentMean,
    abs_of_nonneg (integral_nonneg
      fun omega ↦ finiteShellIncrementCubePthMoment_nonneg n m p Q omega)]
  exact hmoment

/-- The centred sub-cube moment. -/
def centeredCubePthMoment (P : ProbabilityMeasure (ShellSeq d)) (n m : ℕ) (p : ℝ)
    (Q : TriadicCube d) (omega : ShellSeq d) : ℝ :=
  finiteShellIncrementCubePthMoment n m p Q omega - cubePthMomentMean P n m p Q

theorem measurable_centeredCubePthMoment (P : ProbabilityMeasure (ShellSeq d))
    (n m : ℕ) {p : ℝ} (hp : (0 : ℝ) ≤ p) (Q : TriadicCube d) :
    Measurable (centeredCubePthMoment P n m p Q) :=
  (measurable_finiteShellIncrementCubePthMoment n m hp Q).sub measurable_const

/-- A constant random variable has a `Γ_σ` tail at any bound of its size. -/
private theorem isBigO_gammaSigma_const {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {sigma c B : ℝ} (hcB : |c| ≤ B) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun _ : Omega ↦ c) B := by
  intro t ht
  have hB : 0 ≤ B := le_trans (abs_nonneg c) hcB
  have hempty : IndependentSums.upperTailEvent (fun _ : Omega ↦ |c|) (B * t) =
      (∅ : Set Omega) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, Set.mem_empty_iff_false, iff_false,
      not_lt]
    calc |c| ≤ B := hcB
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * t := mul_le_mul_of_nonneg_left ht hB
  rw [hempty, measureReal_empty, IndependentSums.gammaSigma_inv]
  exact (Real.exp_pos _).le

/-- The centred sub-cube moment has a `Γ_{2/p}` tail at the uniform amplitude,
inflated by the two-term triangle constant and the centring cost. -/
theorem isBigO_gammaSigma_centeredCubePthMoment
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m)
    (Q : TriadicCube d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (centeredCubePthMoment P n m p Q)
      (IndependentSums.gammaTriangleConst (2 / p) *
        ((1 + IndependentSums.gammaMomentConst (2 / p)) *
          cubePthMomentAmplitude d p n m)) := by
  have hsigma : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hApos : 0 < cubePthMomentAmplitude d p n m :=
    cubePthMomentAmplitude_pos hPrefix hp hnm
  have hGm : 0 < IndependentSums.gammaMomentConst (2 / p) :=
    IndependentSums.gammaMomentConst_pos hsigma
  obtain ⟨_, hmean⟩ := integrable_and_abs_cubePthMomentMean_le
    hPrefix hJ2 hJ3 hJ4 hp hnm Q
  have hconst : IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma (2 / p))
      (fun _ : ShellSeq d ↦ -cubePthMomentMean P n m p Q)
      (IndependentSums.gammaMomentConst (2 / p) * cubePthMomentAmplitude d p n m) :=
    isBigO_gammaSigma_const P.toMeasure (by rwa [abs_neg])
  have hsum := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) hsigma hApos
    (mul_pos hGm hApos)
    (isBigO_gammaSigma_finiteShellIncrementCubePthMoment hPrefix hJ2 hJ3 hJ4 hp hnm Q)
    hconst
    (measurable_finiteShellIncrementCubePthMoment n m (le_trans (by norm_num) hp) Q)
    measurable_const
  have hfun : (fun omega : ShellSeq d ↦
      finiteShellIncrementCubePthMoment n m p Q omega +
        -cubePthMomentMean P n m p Q) = centeredCubePthMoment P n m p Q := by
    funext omega
    rw [centeredCubePthMoment, ← sub_eq_add_neg]
  rw [hfun] at hsum
  refine hsum.mono_scale (le_of_eq ?_)
  ring

/-- The centred sub-cube moment has expectation zero. -/
theorem integral_centeredCubePthMoment_eq_zero
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m : ℕ} (hnm : n < m)
    (Q : TriadicCube d) :
    ∫ omega, centeredCubePthMoment P n m p Q omega ∂P.toMeasure = 0 := by
  obtain ⟨hint, _⟩ := integrable_and_abs_cubePthMomentMean_le
    hPrefix hJ2 hJ3 hJ4 hp hnm Q
  simp only [centeredCubePthMoment]
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ,
    smul_eq_mul, one_mul, cubePthMomentMean, sub_self]

/-! ## Concentration of the colour-class sums -/

/-- **Concentration of one colour-class sum of centred sub-cube moments.**
Distinct scale-`m` sub-cubes of one colour are separated at the printed range
of dependence `sqrt d 3^m` of `k_m - k_n`, so their centred moments are
mutually independent; `CoarseGraining`'s centred independent-sum concentration
(the paper's Proposition `p.concentration`) applies at
index `2/p`. -/
theorem isBigO_gammaSigma_centeredCubePthMomentColorClassSum
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p)
    {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) (c : ShellCubeColor d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ShellSeq d ↦
        ∑ R ∈ (largeCubeSubcubes d m l).filter fun S ↦ cubeShellColor S = c,
          centeredCubePthMoment P n m p R omega)
      (Book.Ch04.gammaSigmaIndependentSumConst (2 / p) *
        Real.sqrt (((largeCubeSubcubes d m l).card : ℕ) : ℝ) *
        (IndependentSums.gammaTriangleConst (2 / p) *
          ((1 + IndependentSums.gammaMomentConst (2 / p)) *
            cubePthMomentAmplitude d p n m))) := by
  classical
  set Dc : Finset (TriadicCube d) :=
    (largeCubeSubcubes d m l).filter fun S ↦ cubeShellColor S = c with hDc
  set K : ℝ := IndependentSums.gammaTriangleConst (2 / p) *
    ((1 + IndependentSums.gammaMomentConst (2 / p)) *
      cubePthMomentAmplitude d p n m) with hK
  have hsigma : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hsigma2 : 2 / p ≤ 2 := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hp)]
    nlinarith only [hp]
  have hGm : 0 < IndependentSums.gammaMomentConst (2 / p) :=
    IndependentSums.gammaMomentConst_pos hsigma
  have hApos : 0 < cubePthMomentAmplitude d p n m :=
    cubePthMomentAmplitude_pos hPrefix hp hnm
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (gammaTriangleConst_pos (2 / p))
      (mul_pos (by linarith only [hGm]) hApos)
  have hCpos : 0 < Book.Ch04.gammaSigmaIndependentSumConst (2 / p) :=
    gammaSigmaIndependentSumConst_pos hsigma
  by_cases hne : Dc.Nonempty
  · have hattach : Dc.attach.Nonempty := by simpa using hne
    have hscale : ∀ R : {R : TriadicCube d // R ∈ Dc}, (R.1).scale = (m : ℤ) := by
      intro R
      exact scale_of_mem_largeCubeSubcubes hml (Finset.mem_filter.mp R.2).1
    have hcolor : ∀ R S : {R : TriadicCube d // R ∈ Dc},
        cubeShellColor R.1 = cubeShellColor S.1 := by
      intro R S
      exact (Finset.mem_filter.mp R.2).2.trans (Finset.mem_filter.mp S.2).2.symm
    have hindepY := iIndepFun_finiteShellIncrementCubePthMoment
      (P := P) hJ1 hJ2 n m (le_trans (by norm_num) hp)
      (Q := fun R : {R : TriadicCube d // R ∈ Dc} ↦ R.1) hscale
      Subtype.coe_injective hcolor
    have hindep : iIndepFun
        (fun (R : {R : TriadicCube d // R ∈ Dc}) (omega : ShellSeq d) ↦
          centeredCubePthMoment P n m p R.1 omega) P.toMeasure := by
      have hcomp := hindepY.comp
        (fun R : {R : TriadicCube d // R ∈ Dc} ↦
          fun y : ℝ ↦ y - cubePthMomentMean P n m p R.1)
        (fun R ↦ measurable_id.sub_const _)
      exact hcomp
    have hmeas : ∀ R : {R : TriadicCube d // R ∈ Dc},
        Measurable (fun omega : ShellSeq d ↦
          centeredCubePthMoment P n m p R.1 omega) :=
      fun R ↦ measurable_centeredCubePthMoment P n m (le_trans (by norm_num) hp) R.1
    have htail : ∀ R ∈ Dc.attach,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
          (fun omega : ShellSeq d ↦ centeredCubePthMoment P n m p R.1 omega) K :=
      fun R _ ↦ isBigO_gammaSigma_centeredCubePthMoment hPrefix hJ2 hJ3 hJ4 hp hnm R.1
    have hmean : ∀ R ∈ Dc.attach,
        ∫ omega, centeredCubePthMoment P n m p R.1 omega ∂P.toMeasure = 0 :=
      fun R _ ↦ integral_centeredCubePthMoment_eq_zero hPrefix hJ2 hJ3 hJ4 hp hnm R.1
    have hsum :=
      Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := P.toMeasure)
        (X := fun (R : {R : TriadicCube d // R ∈ Dc}) (omega : ShellSeq d) ↦
          centeredCubePthMoment P n m p R.1 omega)
        (s := Dc.attach) (σ := 2 / p) (K := K)
        hindep hmeas hattach hsigma hsigma2 hKpos htail hmean
    have hattach_eq : (fun omega : ShellSeq d ↦
        ∑ R ∈ Dc.attach, centeredCubePthMoment P n m p R.1 omega) =
        fun omega : ShellSeq d ↦
          ∑ R ∈ Dc, centeredCubePthMoment P n m p R omega := by
      funext omega
      exact Finset.sum_attach Dc fun R ↦ centeredCubePthMoment P n m p R omega
    rw [hattach_eq] at hsum
    refine hsum.mono_scale ?_
    rw [Finset.card_attach]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCpos.le) hKpos.le
    exact Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_filter_le _ _)
  · have hempty : Dc = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : (fun omega : ShellSeq d ↦
        ∑ R ∈ Dc, centeredCubePthMoment P n m p R omega) =
        fun _ : ShellSeq d ↦ (0 : ℝ) := by
      funext omega
      rw [hempty, Finset.sum_empty]
    rw [hzero]
    refine isBigO_gammaSigma_const P.toMeasure ?_
    rw [abs_zero]
    exact mul_nonneg (mul_nonneg hCpos.le (Real.sqrt_nonneg _)) hKpos.le

/-! ## The average over all sub-cubes -/

/-- **The centred sub-cube average carries the printed decay.** The `3^d`
colour classes are recombined by the finite triangle inequality, and dividing by
the number `3^{d(l-m)}` of sub-cubes turns `sqrt N / N` into `3^{-(d/2)(l-m)}`. -/
theorem isBigO_gammaSigma_centeredCubePthMomentSubcubeAverage
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p)
    {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ShellSeq d ↦ (((largeCubeSubcubes d m l).card : ℕ) : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d m l, centeredCubePthMoment P n m p R omega)
      (largeCubePthMomentTailConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - m : ℕ) : ℝ))) := by
  classical
  set D : Finset (TriadicCube d) := largeCubeSubcubes d m l with hD
  set K : ℝ := IndependentSums.gammaTriangleConst (2 / p) *
    ((1 + IndependentSums.gammaMomentConst (2 / p)) *
      cubePthMomentAmplitude d p n m) with hK
  have hsigma : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hGm : 0 < IndependentSums.gammaMomentConst (2 / p) :=
    IndependentSums.gammaMomentConst_pos hsigma
  have hApos : 0 < cubePthMomentAmplitude d p n m :=
    cubePthMomentAmplitude_pos hPrefix hp hnm
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (gammaTriangleConst_pos (2 / p))
      (mul_pos (by linarith only [hGm]) hApos)
  have hCpos : 0 < Book.Ch04.gammaSigmaIndependentSumConst (2 / p) :=
    gammaSigmaIndependentSumConst_pos hsigma
  have hcard : D.card = (3 ^ d) ^ (l - m) := largeCubeSubcubes_card d m l
  have hNpos : (0 : ℝ) < ((D.card : ℕ) : ℝ) := by
    rw [hcard]
    positivity
  have hclass : ∀ c ∈ (Finset.univ : Finset (ShellCubeColor d)),
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
        (fun omega : ShellSeq d ↦
          ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
            centeredCubePthMoment P n m p R omega)
        (Book.Ch04.gammaSigmaIndependentSumConst (2 / p) *
          Real.sqrt ((D.card : ℕ) : ℝ) * K) :=
    fun c _ ↦ isBigO_gammaSigma_centeredCubePthMomentColorClassSum
      hPrefix hJ1 hJ2 hJ3 hJ4 hp hnm hml c
  have hclassMeas : ∀ c ∈ (Finset.univ : Finset (ShellCubeColor d)),
      Measurable (fun omega : ShellSeq d ↦
        ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
          centeredCubePthMoment P n m p R omega) :=
    fun c _ ↦ Finset.measurable_sum _ fun R _ ↦
      measurable_centeredCubePthMoment P n m (le_trans (by norm_num) hp) R
  have htriangle := Book.Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (ShellCubeColor d))
    (X := fun c omega ↦
      ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
        centeredCubePthMoment P n m p R omega)
    (a := fun _ : ShellCubeColor d ↦
      Book.Ch04.gammaSigmaIndependentSumConst (2 / p) *
        Real.sqrt ((D.card : ℕ) : ℝ) * K)
    (σ := 2 / p) hsigma Finset.univ_nonempty
    (fun _ _ ↦ mul_pos (mul_pos hCpos (Real.sqrt_pos.2 hNpos)) hKpos)
    hclass hclassMeas
  have hfiber : (fun omega : ShellSeq d ↦
      ∑ c : ShellCubeColor d, ∑ R ∈ D.filter fun S ↦ cubeShellColor S = c,
        centeredCubePthMoment P n m p R omega) =
      fun omega : ShellSeq d ↦
        ∑ R ∈ D, centeredCubePthMoment P n m p R omega := by
    funext omega
    exact Finset.sum_fiberwise D cubeShellColor
      fun R ↦ centeredCubePthMoment P n m p R omega
  rw [hfiber] at htriangle
  have hscaled := htriangle.const_mul (c := ((D.card : ℕ) : ℝ)⁻¹)
    (inv_nonneg.2 hNpos.le)
  refine hscaled.mono_scale (le_of_eq ?_)
  have hcolorcard : (Finset.univ : Finset (ShellCubeColor d)).card =
      shellColorPeriod d ^ d := by simp
  have hsumconst : ∑ _c : ShellCubeColor d,
      (Book.Ch04.gammaSigmaIndependentSumConst (2 / p) *
        Real.sqrt ((D.card : ℕ) : ℝ) * K) =
      ((shellColorPeriod d : ℝ) ^ d) *
        (Book.Ch04.gammaSigmaIndependentSumConst (2 / p) *
          Real.sqrt ((D.card : ℕ) : ℝ) * K) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcolorcard]
    push_cast
    ring
  have hdecay : ((D.card : ℕ) : ℝ)⁻¹ * Real.sqrt ((D.card : ℕ) : ℝ) =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - m : ℕ) : ℝ)) := by
    have hNval : ((D.card : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((l - m : ℕ) : ℝ)) := by
      rw [hcard]
      push_cast
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (d : ℕ)) (l - m),
        ← Real.rpow_natCast (3 : ℝ) d, ← Real.rpow_mul (by norm_num)]
    have hinv : ((D.card : ℕ) : ℝ)⁻¹ * Real.sqrt ((D.card : ℕ) : ℝ) =
        Real.sqrt (((D.card : ℕ) : ℝ))⁻¹ := by
      calc ((D.card : ℕ) : ℝ)⁻¹ * Real.sqrt ((D.card : ℕ) : ℝ)
          = (Real.sqrt ((D.card : ℕ) : ℝ) * Real.sqrt ((D.card : ℕ) : ℝ))⁻¹ *
              Real.sqrt ((D.card : ℕ) : ℝ) := by
            rw [Real.mul_self_sqrt hNpos.le]
        _ = (Real.sqrt ((D.card : ℕ) : ℝ))⁻¹ := by
            rw [mul_inv, mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 hNpos).ne',
              mul_one]
        _ = Real.sqrt ((D.card : ℕ) : ℝ)⁻¹ := (Real.sqrt_inv _).symm

    rw [hinv, hNval, ← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num),
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hsumconst, largeCubePthMomentTailConst, hK, cubePthMomentAmplitude]
  calc ((D.card : ℕ) : ℝ)⁻¹ *
        (IndependentSums.gammaTriangleConst (2 / p) *
          ((shellColorPeriod d : ℝ) ^ d *
            (Book.Ch04.gammaSigmaIndependentSumConst (2 / p) *
              Real.sqrt ((D.card : ℕ) : ℝ) *
              (IndependentSums.gammaTriangleConst (2 / p) *
                ((1 + IndependentSums.gammaMomentConst (2 / p)) *
                  (finiteShellIncrementPthMomentConst d p ^ p *
                    Real.sqrt ((m - n : ℕ) : ℝ) ^ p))))))
      = (IndependentSums.gammaTriangleConst (2 / p) *
          ((shellColorPeriod d : ℝ) ^ d *
            Book.Ch04.gammaSigmaIndependentSumConst (2 / p)) *
          (IndependentSums.gammaTriangleConst (2 / p) *
            ((1 + IndependentSums.gammaMomentConst (2 / p)) *
              finiteShellIncrementPthMomentConst d p ^ p)) *
          Real.sqrt ((m - n : ℕ) : ℝ) ^ p) *
          (((D.card : ℕ) : ℝ)⁻¹ * Real.sqrt ((D.card : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hdecay]

/-! ## The display `e.kl.bounds.large` -/

/-- **The improved `p`-th moment display on a large cube**
(display `e.kl.bounds.large`). For `p ≥ 1` and `n < m ≤ l` there is a measurable witness `X` with a
`Γ_{2/p}` tail at amplitude `C (m-n)^{p/2} 3^{-(d/2)(l-m)}` and, pointwise in
the sample,

`⨍_{cu_l} |(k_m - k_n)(x)|^p dx ≤ C' (m-n)^{p/2} + X`.

The deterministic leading term is the common expectation bound of the
uniform display `e.kmn.bounds`; the witness is the average over the
`3^{d(l-m)}` sub-cubes of scale `m` of the centred sub-cube moments, and its
decay is `CoarseGraining`'s centred independent-sum concentration applied inside
each of the `(⌊√d⌋+2)^d` colour classes of scale-`m` cubes, which are separated
at the printed range of dependence `sqrt d 3^m` of `k_m - k_n`.

Comparison with the printed constants. The printed deterministic constant is
`C(s,d,p)` and the printed amplitude constant is `(Cp)^{p/2}`. The constants
realized here are `largeCubePthMomentMeanConst d p` and
`largeCubePthMomentTailConst d p`. Both contain the factor
`finiteShellIncrementPthMomentConst d p ^ p`, whose honest size is
`e * gammaMomentConst (2/p) * streamLinftyConst d ^ p`; the Chapter 4 moment
constant `gammaMomentConst (2/p)` grows like `(p/e)^{p/2}`. The tail constant
carries in addition `Book.Ch04.gammaSigmaIndependentSumConst (2/p)`, which is
the print's `C_σ` at `σ = 2/p` and is of the printed size `(Cp)^{p/2}`, together
with two triangle constants and the colour count `(⌊√d⌋+2)^d`. So the realized
tail constant is of order `(Cp)^{p}` rather than the printed `(Cp)^{p/2}`: the
extra factor is the moment constant spent on converting the uniform tail
into an expectation bound and back. For every fixed `p ≥ 1` both constants are
finite and depend only on `d` and `p`.

The inputs are the prefix stationarity, the restriction-lane range of
dependence `ShellLawJ1Restriction`, the shell independence
`ShellLawJ2`, the shell size observable `ShellLawJ3` and the negation symmetry
`ShellLawJ4`. -/
theorem exists_witness_finiteShellIncrementPthMomentLargeCube
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {p : ℝ} (hp : (1 : ℝ) ≤ p)
    {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p)) X
        (largeCubePthMomentTailConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - m : ℕ) : ℝ))) ∧
      ∀ omega : ShellSeq d,
        volumeAverage (cubeSet (originCube d (l : ℤ)))
            (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) ≤
          largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p +
            X omega := by
  classical
  set D : Finset (TriadicCube d) := largeCubeSubcubes d m l with hD
  have hDeq : D = descendantsAtDepth (originCube d (l : ℤ)) (l - m) := rfl
  have hNpos : (0 : ℝ) < ((D.card : ℕ) : ℝ) := by
    rw [hD, largeCubeSubcubes_card]
    positivity
  refine ⟨fun omega ↦ ((D.card : ℕ) : ℝ)⁻¹ *
      ∑ R ∈ D, centeredCubePthMoment P n m p R omega, ?_, ?_, ?_⟩
  · exact measurable_const.mul (Finset.measurable_sum _ fun R _ ↦
      measurable_centeredCubePthMoment P n m (le_trans (by norm_num) hp) R)
  · exact isBigO_gammaSigma_centeredCubePthMomentSubcubeAverage
      hPrefix hJ1 hJ2 hJ3 hJ4 hp hnm hml
  · intro omega
    have hcont : Continuous
        (fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) :=
      (continuous_matrixOperatorNorm_finiteShellIncrement omega n m).rpow_const
        fun _ ↦ Or.inr (le_trans (by norm_num) hp)
    have hdec : volumeAverage (cubeSet (originCube d (l : ℤ)))
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) =
        ((D.card : ℕ) : ℝ)⁻¹ *
          ∑ R ∈ D, finiteShellIncrementCubePthMoment n m p R omega := by
      rw [hDeq]
      exact volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants
        (originCube d (l : ℤ)) (l - m)
        (fun R _ ↦ integrableOn_cubeSet_of_continuous R hcont)
    have hsplit : ∑ R ∈ D, finiteShellIncrementCubePthMoment n m p R omega =
        (∑ R ∈ D, centeredCubePthMoment P n m p R omega) +
          ∑ R ∈ D, cubePthMomentMean P n m p R := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun R _ ↦ ?_
      rw [centeredCubePthMoment, sub_add_cancel]
    have hmeanbound : ∑ R ∈ D, cubePthMomentMean P n m p R ≤
        ((D.card : ℕ) : ℝ) *
          (largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p) := by
      have hterm : ∀ R ∈ D, cubePthMomentMean P n m p R ≤
          largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p := by
        intro R _
        obtain ⟨_, hbound⟩ := integrable_and_abs_cubePthMomentMean_le
          hPrefix hJ2 hJ3 hJ4 hp hnm R
        refine le_trans (le_abs_self _) (le_trans hbound (le_of_eq ?_))
        rw [largeCubePthMomentMeanConst, cubePthMomentAmplitude]
        ring
      calc ∑ R ∈ D, cubePthMomentMean P n m p R
          ≤ ∑ _R ∈ D,
              (largeCubePthMomentMeanConst d p *
                Real.sqrt ((m - n : ℕ) : ℝ) ^ p) := Finset.sum_le_sum hterm
        _ = ((D.card : ℕ) : ℝ) *
              (largeCubePthMomentMeanConst d p *
                Real.sqrt ((m - n : ℕ) : ℝ) ^ p) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [hdec, hsplit, mul_add]
    have hfinal : ((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cubePthMomentMean P n m p R ≤
        largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p := by
      calc ((D.card : ℕ) : ℝ)⁻¹ * ∑ R ∈ D, cubePthMomentMean P n m p R
          ≤ ((D.card : ℕ) : ℝ)⁻¹ * (((D.card : ℕ) : ℝ) *
              (largeCubePthMomentMeanConst d p *
                Real.sqrt ((m - n : ℕ) : ℝ) ^ p)) :=
            mul_le_mul_of_nonneg_left hmeanbound (inv_nonneg.2 hNpos.le)
        _ = largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p := by
            rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
    linarith only [hfinal]

end

end SuperdiffusionCLT.Section2.Estimates.Stream
