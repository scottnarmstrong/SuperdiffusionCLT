/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.SpatialAverageColoring
public import SuperdiffusionCLT.Section2.Estimates.Stream.TranslatedIncrementLinfty
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The finite-increment `L∞` estimate on a large cube

This module proves the paper's large-cube supremum estimate for the
natural-shell increment: for `n < m ≤ l`,

`‖k_m - k_n‖_{L∞(cu_l)} ≤ O_{Γ₂}(C (m-n)^{1/2} (l-n)^{1/2})`.

The cube `cu_l` is partitioned into the `3^{d(l-n)}` triadic sub-cubes of
scale `n`, whose centres form `3^n ℤ^d ∩ cu_l`. Each sub-cube carries the
translated small-cube envelope with the common amplitude
`streamLinftyConst d * √(m-n)`, uniformly in the centre, and the finite
maximum over the family costs the factor `(3 log N)^{1/2}` with
`N = 3^{d(l-n)}`, that is `√(3 d log 3) * √(l-n)`.

No boundary set is discarded. The small-cube envelope controls the
*open* cube; continuity of the increment extends that control to the closure,
hence to the half-open partition representative `cubeSet`, and the half-open
sub-cubes cover the half-open large cube exactly. The resulting pointwise
domination therefore holds at every point of `cubeSet (originCube d l)`, which
contains the open cube `openCubeSet (originCube d l)`.

## Main definitions

* `largeCubeSubcubes`: the scale-`n` triadic sub-cubes of `cu_l`.
* `largeCubeIncrementSupBound`: the measurable large-cube envelope, the finite
  maximum of the translated small-cube envelopes over the sub-cube centres.
* `largeCubeLinftyConst`: the explicit dimensional constant.
* `finiteShellIncrementLinftyNormLargeCube`: the literal `L∞(cu_l)` carrier.

## Main results

* `matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound`.
* `isBigOWith_gammaSigma_largeCubeIncrementSupBound`.
* `isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube`: the printed
  display `e.kmn.Linfty`.
* `isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube_linear`: the
  linear-amplitude special case used in the Section 3 bootstrap.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Set
open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## From the open cube to its half-open partition representative -/

private theorem continuous_matrixOperatorNorm_finiteShellIncrement
    (omega : ShellSeq d) (n m : ℕ) :
    Continuous fun x : Vec d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m x) := by
  have hsum : Continuous fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m, (omega k) x :=
    continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous
  refine ShellField.continuous_matrixOperatorNorm.comp (hsum.congr ?_)
  intro x
  rw [finiteShellIncrement_apply]
  rfl

/-- The half-open partition representative of a triadic cube sits in the
closure of its open realization. -/
theorem cubeSet_subset_closure_openCubeSet (Q : TriadicCube d) :
    cubeSet Q ⊆ closure (openCubeSet Q) := by
  have hclosure : closure (openCubeSet Q) =
      Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact closure_ball (cubeCenter Q) (cubeRadius_pos Q).ne'
  rw [hclosure]
  exact cubeSet_subset_closedBall Q

/-- The small-cube envelope already controls the half-open cube: the
open-cube bound extends to the closure by continuity of the increment. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound_cubeSet
    (omega : ShellSeq d) (n m : ℕ) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      incrementSupBound n m omega := by
  have hclosed : IsClosed {y : Vec d |
      matrixOperatorNorm (finiteShellIncrement omega n m y) ≤
        incrementSupBound n m omega} :=
    isClosed_le (continuous_matrixOperatorNorm_finiteShellIncrement omega n m)
      continuous_const
  have hsub : openCubeSet (originCube d (n : ℤ)) ⊆ {y : Vec d |
      matrixOperatorNorm (finiteShellIncrement omega n m y) ≤
        incrementSupBound n m omega} := fun _ hy ↦
    matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound omega n m hy
  exact (hclosed.closure_subset_iff.2 hsub)
    (cubeSet_subset_closure_openCubeSet _ hx)

/-- The translated small-cube envelope controls every point of the half-open
translated cube `z + cubeSet (originCube d n)`. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound_cubeSet
    (z : Vec d) (omega : ShellSeq d) (n m : ℕ) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m (z + x)) ≤
      translatedIncrementSupBound z n m omega := by
  have h := matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound_cubeSet
    (ShellField.translateSequence z omega) n m hx
  simpa only [translatedIncrementSupBound,
    finiteShellIncrement_translateSequence] using h

/-! ## The scale-`n` sub-cubes of the large cube -/

/-- The scale-`n` triadic sub-cubes of the large cube `cu_l`. Their centres
are exactly the lattice points `3^n ℤ^d ∩ cu_l`. -/
def largeCubeSubcubes (d n l : ℕ) : Finset (TriadicCube d) :=
  descendantsAtDepth (originCube d (l : ℤ)) (l - n)

theorem largeCubeSubcubes_nonempty (d n l : ℕ) :
    (largeCubeSubcubes d n l).Nonempty :=
  descendantsAtDepth_nonempty _ _

/-- The sub-cube family of `cu_l` at scale `n` has exactly `3^{d(l-n)}`
members. -/
theorem largeCubeSubcubes_card (d n l : ℕ) :
    (largeCubeSubcubes d n l).card = (3 ^ d) ^ (l - n) :=
  descendantsAtDepth_card _ _

/-- Every member of the sub-cube family has scale `n`. -/
theorem scale_of_mem_largeCubeSubcubes {n l : ℕ} (hnl : n ≤ l)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n l) :
    R.scale = (n : ℤ) := by
  have hcast : ((l - n : ℕ) : ℤ) = (l : ℤ) - (n : ℤ) := by omega
  have horigin : (originCube d (l : ℤ)).scale = (l : ℤ) := rfl
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
  rw [hscale, horigin, hcast]
  ring

/-- A triadic cube of natural scale `k` is the half-open translate of the
natural scale-`k` cube by its centre. -/
theorem sub_cubeCenter_mem_cubeSet_originCube {k : ℕ} {Q : TriadicCube d}
    (hQ : Q.scale = (k : ℤ)) {x : Vec d} (hx : x ∈ cubeSet Q) :
    x - cubeCenter Q ∈ cubeSet (originCube d (k : ℤ)) := by
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hfactor : cubeScaleFactor Q = (3 : ℝ) ^ (k : ℤ) := by
    rw [cubeScaleFactor, hQ]
  have hxi := hx i
  rw [hfactor] at hxi
  have hcenter : cubeCenter Q i = (Q.index i : ℝ) * (3 : ℝ) ^ (k : ℤ) := by
    rw [cubeCenter, hfactor]
  simp only [Pi.sub_apply, hcenter]
  constructor
  · nlinarith only [hxi.1]
  · nlinarith only [hxi.2]

/-- Every point of the half-open large cube lies in the half-open translate of
`cu_n` centred at one of the sub-cube centres. -/
theorem exists_mem_largeCubeSubcubes {n l : ℕ} (hnl : n ≤ l) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (l : ℤ))) :
    ∃ R ∈ largeCubeSubcubes d n l,
      x - cubeCenter R ∈ cubeSet (originCube d (n : ℤ)) := by
  obtain ⟨R, hR, hxR⟩ :=
    exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := originCube d (l : ℤ))
      (x := x) (l - n) hx
  exact ⟨R, hR,
    sub_cubeCenter_mem_cubeSet_originCube
      (scale_of_mem_largeCubeSubcubes hnl hR) hxR⟩

/-- The open cube of a smaller natural scale sits inside the half-open cube of
any larger natural scale. -/
theorem mem_cubeSet_originCube_of_mem_openCubeSet {l k : ℕ} (hlk : l ≤ k)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (l : ℤ))) :
    x ∈ cubeSet (originCube d (k : ℤ)) := by
  refine openCubeSet_subset_cubeSet _ ?_
  refine ShellField.openCubeSet_originCube_subset_of_le ?_ hx
  exact_mod_cast hlk

/-! ## The large-cube envelope -/

/-- The single random variable dominating the shell increment on the whole
large cube `cu_l`: the finite maximum of the translated small-cube envelopes
over the `3^{d(l-n)}` sub-cube centres. -/
def largeCubeIncrementSupBound (n m l : ℕ) (omega : ShellSeq d) : ℝ :=
  (largeCubeSubcubes d n l).sup' (largeCubeSubcubes_nonempty d n l)
    fun R ↦ translatedIncrementSupBound (cubeCenter R) n m omega

/-- Each translated small-cube envelope of the family is dominated by the
large-cube envelope. -/
theorem le_largeCubeIncrementSupBound_of_mem {n l : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n l) (m : ℕ) (omega : ShellSeq d) :
    translatedIncrementSupBound (cubeCenter R) n m omega ≤
      largeCubeIncrementSupBound n m l omega :=
  Finset.le_sup'
    (fun S : TriadicCube d ↦
      translatedIncrementSupBound (cubeCenter S) n m omega) hR

/-- The large-cube envelope is nonnegative. -/
theorem largeCubeIncrementSupBound_nonneg (n m l : ℕ) (omega : ShellSeq d) :
    0 ≤ largeCubeIncrementSupBound n m l omega := by
  obtain ⟨R, hR⟩ := largeCubeSubcubes_nonempty d n l
  exact (translatedIncrementSupBound_nonneg (cubeCenter R) n m omega).trans
    (le_largeCubeIncrementSupBound_of_mem hR m omega)

/-- The large-cube envelope is measurable. -/
theorem measurable_largeCubeIncrementSupBound (n m l : ℕ) :
    Measurable (largeCubeIncrementSupBound n m l : ShellSeq d → ℝ) := by
  have hmeas := Finset.measurable_sup' (largeCubeSubcubes_nonempty d n l)
    (f := fun R (omega : ShellSeq d) ↦
      translatedIncrementSupBound (cubeCenter R) n m omega)
    (fun R _ ↦ measurable_translatedIncrementSupBound (cubeCenter R) n m)
  have hfun : (largeCubeSubcubes d n l).sup'
      (largeCubeSubcubes_nonempty d n l)
      (fun R (omega : ShellSeq d) ↦
        translatedIncrementSupBound (cubeCenter R) n m omega) =
      (largeCubeIncrementSupBound n m l : ShellSeq d → ℝ) := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [hfun] at hmeas

/-- The deterministic large-cube estimate: at every point of the half-open
large cube the shell increment is dominated by one measurable random
variable. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound
    (omega : ShellSeq d) {n m l : ℕ} (hnl : n ≤ l) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (l : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      largeCubeIncrementSupBound n m l omega := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_largeCubeSubcubes hnl hx
  have hpoint : cubeCenter R + (x - cubeCenter R) = x := by abel
  have h := matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound_cubeSet
    (cubeCenter R) omega n m hxR
  rw [hpoint] at h
  exact h.trans (le_largeCubeIncrementSupBound_of_mem hR m omega)

/-- The deterministic large-cube estimate on the open cube. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound_open
    (omega : ShellSeq d) {n m l : ℕ} (hnl : n ≤ l) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (l : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      largeCubeIncrementSupBound n m l omega :=
  matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound
    omega hnl (openCubeSet_subset_cubeSet _ hx)

/-! ## The `Gamma₂` tail of the large-cube envelope -/

/-- The explicit dimensional constant of the marginal large-cube supremum
estimate: the small-cube constant times the maximum factor `√(3 d log 3)`
produced by the `3^{d(l-n)}` sub-cubes. -/
def largeCubeLinftyConst (d : ℕ) : ℝ :=
  streamLinftyConst d * Real.sqrt (3 * (d : ℝ) * Real.log 3)

private theorem three_mul_log_three_pos (hd : 0 < d) :
    0 < 3 * (d : ℝ) * Real.log 3 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact mul_pos (by positivity) hlog

/-- The explicit large-cube constant is positive in every positive dimension:
it depends on `d` alone, so its positivity needs no probabilistic data. -/
theorem largeCubeLinftyConst_pos_of_pos (hd : 0 < d) :
    0 < largeCubeLinftyConst d := by
  rw [largeCubeLinftyConst]
  exact mul_pos (streamLinftyConst_pos_of_pos hd)
    (Real.sqrt_pos.2 (three_mul_log_three_pos hd))

/-- The explicit large-cube constant is positive under the standing dimension
condition. -/
theorem largeCubeLinftyConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < largeCubeLinftyConst d :=
  largeCubeLinftyConst_pos_of_pos (lt_of_lt_of_le (by norm_num) hPrefix.dimension)

private theorem rpow_two_inv_eq_sqrt (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

private theorem two_le_largeCubeSubcubes_card {n l : ℕ} (hd : 0 < d)
    (hnl : n < l) : 2 ≤ (largeCubeSubcubes d n l).card := by
  have hgap : l - n ≠ 0 := by omega
  have hbase : 2 ≤ 3 ^ d := by
    calc (2 : ℕ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  rw [largeCubeSubcubes_card]
  exact hbase.trans (Nat.le_self_pow hgap _)

private theorem log_largeCubeSubcubes_card (d n l : ℕ) :
    Real.log ((largeCubeSubcubes d n l).card : ℝ) =
      ((l - n : ℕ) : ℝ) * ((d : ℝ) * Real.log 3) := by
  have hcard : ((largeCubeSubcubes d n l).card : ℝ) = ((3 : ℝ) ^ d) ^ (l - n) := by
    rw [largeCubeSubcubes_card]
    push_cast
    ring
  rw [hcard, Real.log_pow, Real.log_pow]

/-- The maximum factor of the finite-maximum rule for the sub-cube family:
`(3 log N)^{1/2} = √(3 d log 3) √(l-n)` with `N = 3^{d(l-n)}`. -/
private theorem rpow_three_mul_log_card (hd : 0 < d) (n l : ℕ) :
    (3 * Real.log ((largeCubeSubcubes d n l).card : ℝ)) ^ (2 : ℝ)⁻¹ =
      Real.sqrt (3 * (d : ℝ) * Real.log 3) * Real.sqrt ((l - n : ℕ) : ℝ) := by
  have hbase : 3 * Real.log ((largeCubeSubcubes d n l).card : ℝ) =
      (3 * (d : ℝ) * Real.log 3) * ((l - n : ℕ) : ℝ) := by
    rw [log_largeCubeSubcubes_card]
    ring
  rw [rpow_two_inv_eq_sqrt, hbase,
    Real.sqrt_mul (three_mul_log_three_pos hd).le]

/-- The marginal large-cube supremum envelope obeys the `Gamma₂` bound of the
source display `e.kmn.Linfty`, at the explicit scale
`largeCubeLinftyConst d * √(m-n) * √(l-n)`. -/
theorem isBigOWith_gammaSigma_largeCubeIncrementSupBound
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (largeCubeIncrementSupBound n m l)
      (largeCubeLinftyConst d *
        (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hnl : n < l := lt_of_lt_of_le hnm hml
  have hsup := IndependentSums.isBigOWith_gammaSigma_finset_sup'
    (μ := P.toMeasure) (largeCubeSubcubes d n l)
    (largeCubeSubcubes_nonempty d n l)
    (X := fun R (omega : ShellSeq d) ↦
      translatedIncrementSupBound (cubeCenter R) n m omega)
    (A := streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) (σ := 2)
    (by norm_num) (two_le_largeCubeSubcubes_card hd hnl)
    (fun R _ ↦ isBigOWith_gammaSigma_translatedIncrementSupBound
      hPrefix hJ2 hJ3 hJ4 hnm (cubeCenter R))
  have hscale :
      (3 * Real.log ((largeCubeSubcubes d n l).card : ℝ)) ^ (2 : ℝ)⁻¹ *
          (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) =
        largeCubeLinftyConst d *
          (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ)) := by
    rw [rpow_three_mul_log_card hd n l, largeCubeLinftyConst]
    ring
  rw [hscale] at hsup
  exact hsup

/-! ## The literal `L∞(cu_l)` carrier -/

/-- The literal `L∞` carrier of the natural-shell increment on the open large
cube `cu_l`, measured in the exact Euclidean matrix operator norm. Zero is
adjoined to the defining range explicitly, so the carrier stays valid in
dimension zero. -/
def finiteShellIncrementLinftyNormLargeCube
    (n m l : ℕ) (omega : ShellSeq d) : ℝ :=
  sSup
    (Set.range fun o :
        Option {x : Vec d // x ∈ openCubeSet (originCube d (l : ℤ))} ↦
      match o with
      | none => 0
      | some x => matrixOperatorNorm (finiteShellIncrement omega n m x.1))

private theorem finiteShellIncrementLinftyNormLargeCube_bddAbove
    (n m l : ℕ) (omega : ShellSeq d) :
    BddAbove
      (Set.range fun o :
          Option {x : Vec d // x ∈ openCubeSet (originCube d (l : ℤ))} ↦
        match o with
        | none => 0
        | some x =>
            matrixOperatorNorm (finiteShellIncrement omega n m x.1)) := by
  refine ⟨largeCubeIncrementSupBound n m (max n l) omega, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact largeCubeIncrementSupBound_nonneg n m (max n l) omega
  | some x =>
      exact matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound
        omega (le_max_left n l)
        (mem_cubeSet_originCube_of_mem_openCubeSet (le_max_right n l) x.2)

/-- The literal large-cube `L∞` carrier is nonnegative. -/
theorem finiteShellIncrementLinftyNormLargeCube_nonneg
    (n m l : ℕ) (omega : ShellSeq d) :
    0 ≤ finiteShellIncrementLinftyNormLargeCube n m l omega :=
  le_csSup (finiteShellIncrementLinftyNormLargeCube_bddAbove n m l omega)
    ⟨none, rfl⟩

/-- The literal large-cube `L∞` carrier dominates the exact matrix operator
norm at every point of the open large cube. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_linftyNormLargeCube
    (omega : ShellSeq d) (n m l : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (l : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      finiteShellIncrementLinftyNormLargeCube n m l omega :=
  le_csSup (finiteShellIncrementLinftyNormLargeCube_bddAbove n m l omega)
    ⟨some ⟨x, hx⟩, rfl⟩

/-- The literal large-cube `L∞` carrier is bounded by the measurable
large-cube envelope. -/
theorem finiteShellIncrementLinftyNormLargeCube_le_largeCubeIncrementSupBound
    (omega : ShellSeq d) {n m l : ℕ} (hnl : n ≤ l) :
    finiteShellIncrementLinftyNormLargeCube n m l omega ≤
      largeCubeIncrementSupBound n m l omega := by
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact largeCubeIncrementSupBound_nonneg n m l omega
  | some x =>
      exact matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound_open
        omega hnl x.2

/-- The literal large-cube `L∞` carrier is monotone in the cube scale. -/
theorem finiteShellIncrementLinftyNormLargeCube_mono
    (omega : ShellSeq d) (n m : ℕ) {l k : ℕ} (hlk : l ≤ k) :
    finiteShellIncrementLinftyNormLargeCube n m l omega ≤
      finiteShellIncrementLinftyNormLargeCube n m k omega := by
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact finiteShellIncrementLinftyNormLargeCube_nonneg n m k omega
  | some x =>
      refine matrixOperatorNorm_finiteShellIncrement_le_linftyNormLargeCube
        omega n m k ?_
      exact ShellField.openCubeSet_originCube_subset_of_le
        (by exact_mod_cast hlk) x.2

/-! ## The source display `e.kmn.Linfty` -/

/-- The manuscript's display `e.kmn.Linfty`: for `n < m ≤ l` the exact
`L∞(cu_l)` norm of the natural-shell increment satisfies

`‖k_m - k_n‖_{L∞(cu_l)} ≤ O_{Γ₂}(C (m-n)^{1/2} (l-n)^{1/2})`

with the explicit dimensional constant `largeCubeLinftyConst d`. -/
theorem isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (finiteShellIncrementLinftyNormLargeCube n m l)
      (largeCubeLinftyConst d *
        (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ))) :=
  (isBigOWith_gammaSigma_largeCubeIncrementSupBound
    hPrefix hJ2 hJ3 hJ4 hnm hml).of_le fun omega ↦
      finiteShellIncrementLinftyNormLargeCube_le_largeCubeIncrementSupBound
        omega (hnm.le.trans hml)

/-- The linear-amplitude special case used in the Section 3 bootstrap: for
`n < l ≤ m` the shell increment from `n` to `m` satisfies

`‖k_m - k_n‖_{L∞(cu_l)} ≤ O_{Γ₂}(C (m-n))`,

since `√(m-n) √(l-n) ≤ m-n` after enlarging the cube to `cu_m`. -/
theorem isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube_linear
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m l : ℕ} (hnl : n < l) (hlm : l ≤ m) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (finiteShellIncrementLinftyNormLargeCube n m l)
      (largeCubeLinftyConst d * ((m - n : ℕ) : ℝ)) := by
  have hnm : n < m := lt_of_lt_of_le hnl hlm
  have hbig := isBigOWith_gammaSigma_finiteShellIncrementLinftyNormLargeCube
    hPrefix hJ2 hJ3 hJ4 hnm (le_refl m)
  have hsq : Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((m - n : ℕ) : ℝ) =
      ((m - n : ℕ) : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [hsq] at hbig
  exact hbig.of_le fun omega ↦
    finiteShellIncrementLinftyNormLargeCube_mono omega n m hlm

end

end SuperdiffusionCLT.Section2.Estimates.Stream
