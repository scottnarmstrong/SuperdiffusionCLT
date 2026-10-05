/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.HighContrast.EllipticityMoments
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Assumptions.ShellLaw.J3OrliczForm
public import SuperdiffusionCLT.Probability.OrliczTriangle

/-!
# The `L^infinity` envelope of the full cutoff on the rebasing cube

The proof of `l.b.ell.homogenization` applies the high-contrast
entry theorem to the cutoff law rebased to the unit cube, and the entry input
`Book.Ch05.QuantitativeCoarseGrainedEllipticity` needs a `Gamma_2` envelope of
the `L^infinity` size of the cutoff `k_m` on the rebasing cube
`cu_{m + t_d}`; the pointwise and supremum bounds are the displays `e.k.ell.upscales`
and `e.kmn.Linfty`. `EllipticityMoments` isolates that input
as the predicate `CutoffLargeCubeLinfty` and proves everything downstream of
it, and `IncrementLinftyLargeCube` proves the
corresponding estimate for the increment `k_m - k_0`, that is for the shells
`j_1, ..., j_m`. What is missing there is the shell `j_0`, and this module
supplies it: the increment estimate plus the single-shell estimate give the full
cutoff.

The single-shell estimate is built exactly as the increment estimate is built
in `IncrementLinftyLargeCube`. The large cube `cu_l` is partitioned into its
`3^{d l}` unit-scale sub-cubes (`largeCubeSubcubes d 0 l`), on each translate
`z + cu_0` of the unit cube the value of `j_0` is dominated by the scale-zero
cube-value observable of the translated shell (`shellCubeValueNorm`), whose
`Gamma_2` tail of amplitude `1` is transported from the origin cube by the
one-shell stationarity of the prefix law, and the finite maximum over the
sub-cube centres costs the factor `(3 log N)^{1/2}` with `N = 3^{d l}`, that is
`sqrt (3 d log 3) * sqrt l`.

## Main definitions

* `shellZeroLargeCubeSupBound`: the measurable large-cube envelope of the
  single shell `j_0`, the finite maximum of the translated cube-value
  observables over the unit-scale sub-cube centres.
* `shellZeroLargeCubeConst`: the explicit dimensional constant of its tail.
* `cutoffLargeCubeSupBound`: the sum of the two envelopes, the `Gamma_2`
  envelope of the full cutoff `k_m` on `cu_{m + t_d}`.

## Main results

* `streamCutoff_eq_shellReg_zero_add_finiteShellIncrement`: the splitting
  identity `k_m = j_0 + (k_m - k_0)`.
* `matrixOperatorNorm_shellZero_le_shellZeroLargeCubeSupBound`: the single
  shell is dominated by its envelope on the whole cube.
* `isBigOWith_gammaSigma_shellZeroLargeCubeSupBound`: the `Gamma_2` tail of the
  single-shell envelope, at the explicit scale
  `shellZeroLargeCubeConst d * sqrt l`.
* `matrixOperatorNorm_streamCutoff_le_cubes`: the deterministic domination of
  the cutoff by the sum of the two envelopes.
* `cutoffLargeCubeLinfty`: the proposition `CutoffLargeCubeLinfty` of
  `EllipticityMoments`, which is the large-cube input of the entry bound for the
  rebased cutoff law.

## References

* `l.b.ell.homogenization` (the high-contrast application), `e.k.ell.upscales` and
  `e.kmn.Linfty` (the pointwise and supremum bounds).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Assumptions.ShellLaw
open SuperdiffusionCLT.Probability
open scoped BigOperators

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The single-shell envelope on a large cube

The value of the shell `j_0` on the large cube `cu_l` is dominated, on each
unit-scale sub-cube, by the cube-value observable of the shell translated to
that sub-cube's centre. The maximum over the finitely many centres is one
measurable random variable. -/

/-- The single random variable dominating the shell `j_0` on the whole large
cube `cu_l`: the finite maximum of the translated cube-value observables over
the `3^{d l}` unit-scale sub-cube centres. -/
def shellZeroLargeCubeSupBound (l : ℕ) (omega : ShellSeq d) : ℝ :=
  (largeCubeSubcubes d 0 l).sup' (largeCubeSubcubes_nonempty d 0 l)
    fun R ↦ ShellField.shellCubeValueNorm 0
      (ShellField.translate (cubeCenter R) (omega 0))

/-- Each translated cube-value observable of the family is dominated by the
single-shell large-cube envelope. -/
theorem le_shellZeroLargeCubeSupBound_of_mem {l : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d 0 l) (omega : ShellSeq d) :
    ShellField.shellCubeValueNorm 0
        (ShellField.translate (cubeCenter R) (omega 0)) ≤
      shellZeroLargeCubeSupBound l omega :=
  Finset.le_sup' (f := fun S : TriadicCube d ↦
    ShellField.shellCubeValueNorm 0
      (ShellField.translate (cubeCenter S) (omega 0))) hR

/-- The single-shell large-cube envelope is nonnegative. -/
theorem shellZeroLargeCubeSupBound_nonneg (l : ℕ) (omega : ShellSeq d) :
    0 ≤ shellZeroLargeCubeSupBound l omega := by
  obtain ⟨R, hR⟩ := largeCubeSubcubes_nonempty d 0 l
  exact (ShellField.shellCubeValueNorm_nonneg 0 _).trans
    (le_shellZeroLargeCubeSupBound_of_mem hR omega)

/-- The single-shell large-cube envelope is measurable. -/
theorem measurable_shellZeroLargeCubeSupBound (l : ℕ) :
    Measurable (shellZeroLargeCubeSupBound l : ShellSeq d → ℝ) := by
  have hmeas := Finset.measurable_sup' (largeCubeSubcubes_nonempty d 0 l)
    (f := fun R (omega : ShellSeq d) ↦
      ShellField.shellCubeValueNorm 0
        (ShellField.translate (cubeCenter R) (omega 0)))
    (fun R _ ↦
      (ShellField.shellCubeValueNorm_measurable 0).comp
        ((ShellField.measurable_translate (cubeCenter R)).comp
          (ShellField.measurable_shellCoordinate 0)))
  have hfun : (largeCubeSubcubes d 0 l).sup'
      (largeCubeSubcubes_nonempty d 0 l)
      (fun R (omega : ShellSeq d) ↦
        ShellField.shellCubeValueNorm 0
          (ShellField.translate (cubeCenter R) (omega 0))) =
      (shellZeroLargeCubeSupBound l : ShellSeq d → ℝ) := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [hfun] at hmeas

/-! ## The deterministic domination of the single shell

The cube-value observable controls the open unit cube; continuity of
the shell extends that control to the half-open representative, and the
half-open sub-cubes cover the half-open large cube exactly. -/

private theorem continuous_matrixOperatorNorm_shell (j : ShellField d) :
    Continuous fun x : Vec d ↦ matrixOperatorNorm (j x) :=
  ShellField.continuous_matrixOperatorNorm.comp j.1.1.continuous

/-- The half-open unit cube is controlled by the cube-value observable: the
open-cube bound extends to the closure by continuity of the shell. -/
private theorem matrixOperatorNorm_shell_le_shellCubeValueNorm_cubeSet
    (j : ShellField d) {x : Vec d} (hx : x ∈ cubeSet (originCube d (0 : ℤ))) :
    matrixOperatorNorm (j x) ≤ ShellField.shellCubeValueNorm 0 j := by
  have hclosed : IsClosed {y : Vec d |
      matrixOperatorNorm (j y) ≤ ShellField.shellCubeValueNorm 0 j} :=
    isClosed_le (continuous_matrixOperatorNorm_shell j) continuous_const
  have hsub : openCubeSet (originCube d (0 : ℤ)) ⊆ {y : Vec d |
      matrixOperatorNorm (j y) ≤ ShellField.shellCubeValueNorm 0 j} := fun y hy ↦
    ShellField.matrixOperatorNorm_apply_le_shellCubeValueNorm 0 j ⟨y, hy⟩
  exact hclosed.closure_subset_iff.2 hsub
    (cubeSet_subset_closure_openCubeSet _ hx)

/-- The single shell is dominated by its large-cube envelope at every point of
the half-open large cube. -/
theorem matrixOperatorNorm_shellZero_le_shellZeroLargeCubeSupBound
    (omega : ShellSeq d) (l : ℕ) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (l : ℤ))) :
    matrixOperatorNorm ((omega 0) x) ≤ shellZeroLargeCubeSupBound l omega := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_largeCubeSubcubes (Nat.zero_le l) hx
  have hval : matrixOperatorNorm
      (ShellField.translate (cubeCenter R) (omega 0) (x - cubeCenter R)) =
      matrixOperatorNorm ((omega 0) x) := by
    rw [ShellField.translate_apply, add_comm, show
      cubeCenter R + (x - cubeCenter R) = x by abel]
  have hcube := matrixOperatorNorm_shell_le_shellCubeValueNorm_cubeSet
    (ShellField.translate (cubeCenter R) (omega 0)) hxR
  rw [hval] at hcube
  exact hcube.trans (le_shellZeroLargeCubeSupBound_of_mem hR omega)

/-! ## The `Gamma₂` tail of the single-shell envelope -/

/-- The explicit dimensional constant of the single-shell large-cube supremum
estimate: the maximum factor `sqrt (3 d log 3)` produced by the `3^{d l}`
sub-cubes at unit scale. -/
def shellZeroLargeCubeConst (d : ℕ) : ℝ :=
  Real.sqrt (3 * (d : ℝ) * Real.log 3)

private theorem three_mul_log_three_pos (hd : 0 < d) :
    0 < 3 * (d : ℝ) * Real.log 3 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact mul_pos (by positivity) hlog

/-- The explicit single-shell dimensional constant is positive in every
positive dimension: it depends on `d` alone, so its positivity needs no
probabilistic data. -/
theorem shellZeroLargeCubeConst_pos_of_pos (hd : 0 < d) :
    0 < shellZeroLargeCubeConst d :=
  Real.sqrt_pos.2 (three_mul_log_three_pos hd)

/-- The explicit single-shell dimensional constant is positive under the
standing dimension condition of the prefix law. -/
theorem shellZeroLargeCubeConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < shellZeroLargeCubeConst d := by
  have hd2 : 2 ≤ d := hPrefix.dimension
  have hd : 0 < d := by omega
  exact shellZeroLargeCubeConst_pos_of_pos hd

private theorem rpow_two_inv_eq_sqrt (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

private theorem shellZeroLargeCubeSubcubes_card (d l : ℕ) :
    (largeCubeSubcubes d 0 l).card = (3 ^ d) ^ l := by
  have h := largeCubeSubcubes_card d 0 l
  rwa [Nat.sub_zero] at h

private theorem log_shellZeroLargeCubeSubcubes_card (d l : ℕ) :
    Real.log ((largeCubeSubcubes d 0 l).card : ℝ) =
      ((l : ℕ) : ℝ) * ((d : ℝ) * Real.log 3) := by
  have hcard : ((largeCubeSubcubes d 0 l).card : ℝ) = ((3 : ℝ) ^ d) ^ (l : ℕ) := by
    rw [shellZeroLargeCubeSubcubes_card]
    push_cast
    ring
  rw [hcard, Real.log_pow, Real.log_pow]

/-- The maximum factor of the finite-maximum rule for the unit-scale sub-cube
family: `(3 log N)^{1/2} = sqrt (3 d log 3) sqrt l` with `N = 3^{d l}`. -/
private theorem rpow_three_mul_log_card_zero (hd : 0 < d) (l : ℕ) :
    (3 * Real.log ((largeCubeSubcubes d 0 l).card : ℝ)) ^ (2 : ℝ)⁻¹ =
      shellZeroLargeCubeConst d * Real.sqrt ((l : ℕ) : ℝ) := by
  have hbase : 3 * Real.log ((largeCubeSubcubes d 0 l).card : ℝ) =
      (3 * (d : ℝ) * Real.log 3) * ((l : ℕ) : ℝ) := by
    rw [log_shellZeroLargeCubeSubcubes_card]
    ring
  rw [shellZeroLargeCubeConst, rpow_two_inv_eq_sqrt, hbase,
    Real.sqrt_mul (three_mul_log_three_pos hd).le]

private theorem two_le_shellZeroLargeCubeSubcubes_card {d l : ℕ} (hd : 0 < d)
    (hl : 0 < l) : 2 ≤ (largeCubeSubcubes d 0 l).card := by
  have hbase : 2 ≤ 3 ^ d := by
    calc (2 : ℕ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  rw [shellZeroLargeCubeSubcubes_card]
  exact hbase.trans (Nat.le_self_pow hl.ne' _)

/-- The translated cube-value observable of the shell `j_0` carries the
unit-amplitude `Gamma₂` bound of the translated shell observable: only the
one-shell stationarity of the prefix law is used. -/
theorem isBigOWith_gammaSigma_shellCubeValueNorm_translate
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦
        ShellField.shellCubeValueNorm 0 (ShellField.translate z (omega 0))) 1 :=
  ShellLawPrefix.isBigOWith_gammaSigma_shellObservable_translate hPrefix 0 z
    (ShellField.shellCubeValueNorm_measurable 0)
    (isBigOWith_gammaSigma_shellCubeValueNorm_coordinate hJ3 0)

/-- The single-shell large-cube envelope obeys the `Gamma₂` bound at the
explicit scale `shellZeroLargeCubeConst d * sqrt l`. -/
theorem isBigOWith_gammaSigma_shellZeroLargeCubeSupBound
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {l : ℕ} (hl : 0 < l) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (shellZeroLargeCubeSupBound l)
      (shellZeroLargeCubeConst d * Real.sqrt ((l : ℕ) : ℝ)) := by
  have hd2 : 2 ≤ d := hPrefix.dimension
  have hd : 0 < d := by omega
  have hsup := IndependentSums.isBigOWith_gammaSigma_finset_sup'
    (μ := P.toMeasure) (largeCubeSubcubes d 0 l)
    (largeCubeSubcubes_nonempty d 0 l)
    (X := fun R (omega : ShellSeq d) ↦
      ShellField.shellCubeValueNorm 0
        (ShellField.translate (cubeCenter R) (omega 0)))
    (A := 1) (σ := 2) (by norm_num)
    (two_le_shellZeroLargeCubeSubcubes_card hd hl)
    (fun R _ ↦ isBigOWith_gammaSigma_shellCubeValueNorm_translate
      hPrefix hJ3 (cubeCenter R))
  rw [rpow_three_mul_log_card_zero hd l, mul_one] at hsup
  exact hsup

/-! ## The splitting identity of the cutoff -/

/-- The splitting identity `k_m = j_0 + (k_m - k_0)`: the large-cube
increment estimate covers the second summand, and the single-shell envelope covers the
first. -/
theorem streamCutoff_eq_shellReg_zero_add_finiteShellIncrement
    (omega : ShellSeq d) (m : ℕ) :
    streamCutoff omega m = shellReg omega 0 + finiteShellIncrement omega 0 m := by
  have h0 : streamCutoff omega 0 = shellReg omega 0 := by
    have hrfl : streamCutoff omega 0 = ∑ n ∈ Finset.range (0 + 1), shellReg omega n := rfl
    rw [hrfl, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
  have h := streamCutoff_add_finiteShellIncrement omega (Nat.zero_le m)
  rw [h0] at h
  exact h.symm

/-! ## The deterministic domination of the full cutoff -/

private theorem matrixOperatorNorm_add_le (A B : Mat d) :
    matrixOperatorNorm (A + B) ≤ matrixOperatorNorm A + matrixOperatorNorm B := by
  simpa only [add_sub_cancel_left] using
    matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub (A + B) A

/-- The full cutoff `k_m` is dominated on the open large cube `cu_l` by the sum
of the single-shell envelope and the increment envelope. -/
theorem matrixOperatorNorm_streamCutoff_le_cubes (omega : ShellSeq d) (m : ℕ)
    {l : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (l : ℤ))) :
    matrixOperatorNorm (streamCutoff omega m x) ≤
      shellZeroLargeCubeSupBound l omega +
        largeCubeIncrementSupBound 0 m l omega := by
  have hcube : x ∈ cubeSet (originCube d (l : ℤ)) := openCubeSet_subset_cubeSet _ hx
  have h1 : matrixOperatorNorm ((omega 0) x) ≤ shellZeroLargeCubeSupBound l omega :=
    matrixOperatorNorm_shellZero_le_shellZeroLargeCubeSupBound omega l hcube
  have h2 : matrixOperatorNorm (finiteShellIncrement omega 0 m x) ≤
      largeCubeIncrementSupBound 0 m l omega :=
    matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound_open omega
      (Nat.zero_le l) hx
  have hval : streamCutoff omega m x =
      shellReg omega 0 x + finiteShellIncrement omega 0 m x := by
    rw [streamCutoff_eq_shellReg_zero_add_finiteShellIncrement]
    simp only [RegCoeffField.add_apply]
  calc matrixOperatorNorm (streamCutoff omega m x)
      = matrixOperatorNorm (shellReg omega 0 x +
          finiteShellIncrement omega 0 m x) := by rw [hval]
    _ ≤ matrixOperatorNorm (shellReg omega 0 x) +
          matrixOperatorNorm (finiteShellIncrement omega 0 m x) :=
        matrixOperatorNorm_add_le _ _
    _ ≤ shellZeroLargeCubeSupBound l omega +
          largeCubeIncrementSupBound 0 m l omega := by
        have hshell : matrixOperatorNorm (shellReg omega 0 x) =
            matrixOperatorNorm ((omega 0) x) := by
          simp only [shellReg, ShellField.forgetShell_apply]
        rw [hshell]
        exact add_le_add h1 h2

/-! ## The vanishing increment envelope at the degenerate scale -/

private theorem translatedIncrementSupBound_eq_zero_of_range_empty (z : Vec d)
    (omega : ShellSeq d) : translatedIncrementSupBound z 0 0 omega = 0 := by
  rw [translatedIncrementSupBound_eq]
  have h1 : (finiteShellIncrement omega 0 0 : RegCoeffField d) = 0 := by
    rw [finiteShellIncrement, Finset.Ioc_self, Finset.sum_empty]
  have h2 : finiteShellDerivGauge 0 0 (ShellField.translateSequence z omega) = 0 := by
    rw [finiteShellDerivGauge, Finset.Ioc_self, Finset.sum_empty]
  simp [h1, h2]

private theorem largeCubeIncrementSupBound_eq_zero_of_left_zero (l : ℕ)
    (omega : ShellSeq d) :
    largeCubeIncrementSupBound 0 0 l omega = 0 := by
  have hnn := largeCubeIncrementSupBound_nonneg 0 0 l omega
  refine le_antisymm ?_ hnn
  refine Finset.sup'_le (largeCubeSubcubes_nonempty d 0 l) _ (fun R _ ↦ ?_)
  rw [translatedIncrementSupBound_eq_zero_of_range_empty (cubeCenter R) omega]

/-- The identically vanishing variable carries every nonnegative `Gamma₂`
amplitude: the upper tail event is empty. -/
private theorem isBigOWith_gammaSigma_const_zero {A : ℝ} (hA : 0 ≤ A) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun _ : ShellSeq d ↦ 0) A := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff]
  intro t ht
  have hAt : (0 : ℝ) ≤ A * t := mul_nonneg hA (zero_le_one.trans ht)
  have hempty : IndependentSums.upperTailEvent (fun _ : ShellSeq d ↦ 0) (A * t) =
      (∅ : Set (ShellSeq d)) := by
    ext omega
    simp only [IndependentSums.upperTailEvent, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_lt]
    exact hAt
  rw [hempty, measureReal_empty]
  exact Real.exp_nonneg _

/-- The increment envelope obeys the `Gamma₂` bound of the
display `e.kmn.Linfty` at `n = 0` in every range, including the degenerate
range `m = 0` where it vanishes identically. -/
theorem isBigOWith_gammaSigma_largeCubeIncrementSupBound_ge_zero
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m l : ℕ) (hml : m ≤ l) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (largeCubeIncrementSupBound 0 m l)
      (largeCubeLinftyConst d *
        (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((l : ℕ) : ℝ))) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hfun : largeCubeIncrementSupBound 0 0 l = (fun _ : ShellSeq d ↦ 0) :=
      funext (largeCubeIncrementSupBound_eq_zero_of_left_zero l)
    rw [hfun]
    exact isBigOWith_gammaSigma_const_zero
      (mul_nonneg (largeCubeLinftyConst_pos hPrefix).le
        (by positivity))
  · have h := isBigOWith_gammaSigma_largeCubeIncrementSupBound hPrefix hJ2 hJ3
      hJ4 hm hml
    rw [Nat.sub_zero] at h
    exact h

/-! ## The envelope of the full cutoff -/

/-- The single random variable dominating the full infrared cutoff `k_m` on the
rebasing cube `cu_{m + t_d}`: the sum of the single-shell envelope and the
increment envelope. -/
def cutoffLargeCubeSupBound (m : ℕ) (omega : ShellSeq d) : ℝ :=
  shellZeroLargeCubeSupBound (m + triadicOffset d) omega +
    largeCubeIncrementSupBound 0 m (m + triadicOffset d) omega

/-- The full-cutoff envelope is measurable. -/
theorem measurable_cutoffLargeCubeSupBound (m : ℕ) :
    Measurable (cutoffLargeCubeSupBound m : ShellSeq d → ℝ) :=
  (measurable_shellZeroLargeCubeSupBound _).add
    (measurable_largeCubeIncrementSupBound 0 m _)

/-- The explicit amplitude of the `Gamma₂` bound of the full-cutoff envelope:
the triangle constant of the sum rule times the two explicit scales. -/
def cutoffLargeCubeAmp (d : ℕ) (m : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) +
      largeCubeLinftyConst d *
        (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)))

private theorem one_le_triadicOffset {d : ℕ} (hd : 2 ≤ d) : 1 ≤ triadicOffset d := by
  by_contra h
  have h0 : triadicOffset d = 0 := by omega
  have h1d : (1 : ℕ) < d := by omega
  have h1 : (1 : ℝ) < Real.sqrt (d : ℝ) := by
    have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast h1d
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hdR
  have hkey := sqrt_natCast_le_pow_triadicOffset d
  rw [h0, pow_zero] at hkey
  linarith only [hkey, h1]

/-- The explicit amplitude of the full-cutoff envelope is positive: it carries
the triangle constant times two positive explicit scales, and the rebasing cube
is nontrivial because the dimensional offset is at least one. -/
theorem cutoffLargeCubeAmp_pos (hPrefix : ShellLawPrefix d P) (m : ℕ) :
    0 < cutoffLargeCubeAmp d m := by
  have hd2 : 2 ≤ d := hPrefix.dimension
  have htd : 1 ≤ triadicOffset d := one_le_triadicOffset hd2
  have hz : 0 < shellZeroLargeCubeConst d := shellZeroLargeCubeConst_pos hPrefix
  have hl : 0 < largeCubeLinftyConst d := largeCubeLinftyConst_pos hPrefix
  have hpos : (0 : ℕ) < m + triadicOffset d := by omega
  have hs1 : (0 : ℝ) < Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hpos)
  have hs2 : (0 : ℝ) ≤ Real.sqrt ((m : ℕ) : ℝ) := Real.sqrt_nonneg _
  unfold cutoffLargeCubeAmp
  exact mul_pos IndependentSums.gammaTriangleConst_pos
    (add_pos_of_pos_of_nonneg (mul_pos hz hs1)
      (mul_nonneg hl.le (mul_nonneg hs2 hs1.le)))

/-- The `Gamma₂` bound of the full-cutoff envelope: the sum rule of the
paper's Lemma `l.Gamma.sigma.triangle` applied to the single-shell
envelope and the increment envelope. -/
theorem isBigO_gammaSigma_cutoffLargeCubeSupBound
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffLargeCubeSupBound m) (cutoffLargeCubeAmp d m) := by
  have hd2 : 2 ≤ d := hPrefix.dimension
  have htd : 1 ≤ triadicOffset d := one_le_triadicOffset hd2
  have hpos : (0 : ℕ) < m + triadicOffset d := by omega
  have hfun : cutoffLargeCubeSupBound m = fun omega : ShellSeq d ↦
      shellZeroLargeCubeSupBound (m + triadicOffset d) omega +
        largeCubeIncrementSupBound 0 m (m + triadicOffset d) omega := rfl
  rw [hfun]
  have hA1 : 0 < shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ) :=
    mul_pos (shellZeroLargeCubeConst_pos hPrefix)
      (Real.sqrt_pos.2 (by exact_mod_cast hpos))
  have h1 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (shellZeroLargeCubeSupBound (m + triadicOffset d))
      (shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
      (X := shellZeroLargeCubeSupBound (m + triadicOffset d))
      (A := shellZeroLargeCubeConst d * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ))
      (fun omega ↦ shellZeroLargeCubeSupBound_nonneg _ omega)).1
      (isBigOWith_gammaSigma_shellZeroLargeCubeSupBound hPrefix hJ3 hpos)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hinc : (fun omega : ShellSeq d ↦
          shellZeroLargeCubeSupBound (0 + triadicOffset d) omega +
            largeCubeIncrementSupBound 0 0 (0 + triadicOffset d) omega) =
        fun omega : ShellSeq d ↦
          shellZeroLargeCubeSupBound (0 + triadicOffset d) omega := by
      funext omega
      simp only [largeCubeIncrementSupBound_eq_zero_of_left_zero, add_zero]
    rw [hinc]
    have hamp : cutoffLargeCubeAmp d 0 =
        IndependentSums.gammaTriangleConst 2 *
          (shellZeroLargeCubeConst d *
            Real.sqrt ((0 + triadicOffset d : ℕ) : ℝ)) := by
      rw [cutoffLargeCubeAmp]
      have hz : Real.sqrt ((0 : ℕ) : ℝ) = 0 := by norm_num
      rw [hz, zero_mul, mul_zero, add_zero]
    rw [hamp]
    have hge : (1 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 := by
      rw [gammaTriangleConst_eq_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]
      norm_num
    exact h1.mono_scale (le_mul_of_one_le_left hA1.le hge)
  · have hA2 : 0 < largeCubeLinftyConst d *
        (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)) :=
      mul_pos (largeCubeLinftyConst_pos hPrefix)
        (mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hm))
          (Real.sqrt_pos.2 (by exact_mod_cast hpos)))
    have h2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (largeCubeIncrementSupBound 0 m (m + triadicOffset d))
        (largeCubeLinftyConst d *
          (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ))) :=
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
        (X := largeCubeIncrementSupBound 0 m (m + triadicOffset d))
        (A := largeCubeLinftyConst d *
          (Real.sqrt ((m : ℕ) : ℝ) * Real.sqrt ((m + triadicOffset d : ℕ) : ℝ)))
        (fun omega ↦ largeCubeIncrementSupBound_nonneg 0 m _ omega)).1
        (isBigOWith_gammaSigma_largeCubeIncrementSupBound_ge_zero hPrefix hJ2 hJ3
          hJ4 m (m + triadicOffset d) (by omega))
    exact isBigO_gammaSigma_add_of_isBigO (by norm_num : (0 : ℝ) < 2) hA1 hA2
      h1 h2 (measurable_shellZeroLargeCubeSupBound _)
      (measurable_largeCubeIncrementSupBound 0 m _)

/-! ## The envelope of the full cutoff -/

/-- **The `L^infinity` size of the cutoff on the rebasing cube.** The display
`e.kmn.Linfty` of the paper read for the full cutoff `k_m` on the
cube `cu_{m + t_d}`: the large-cube increment estimate covers the shells
`j_1, ..., j_m` and the single-shell envelope of this module covers `j_0`, so
there is a random amplitude with a `Gamma_2` tail dominating `|k_m|` everywhere
on that cube. -/
theorem cutoffLargeCubeLinfty (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (m : ℕ) :
    CutoffLargeCubeLinfty m P :=
  ⟨cutoffLargeCubeSupBound m, cutoffLargeCubeAmp d m, cutoffLargeCubeAmp_pos hPrefix m,
    (measurable_cutoffLargeCubeSupBound m).aemeasurable,
    isBigO_gammaSigma_cutoffLargeCubeSupBound hPrefix hJ2 hJ3 hJ4 m,
    fun omega x hx ↦
      matrixOperatorNorm_streamCutoff_le_cubes (omega := omega) (m := m) (x := x) hx⟩

/-! The high-contrast entry bound that consumes `CutoffLargeCubeLinfty` is proved in
`EllipticityMoments`. -/

end

end SuperdiffusionCLT.Section3.HighContrast