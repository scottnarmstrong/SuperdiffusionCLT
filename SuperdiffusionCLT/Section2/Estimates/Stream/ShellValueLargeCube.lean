/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Norms.CubeLp

/-!
# One shell's value on a large cube

The proof of the "Moreover" block of `l.ellip.k.scales.estimates` reduces the `L∞`
term of `e.Xm.deff` to a uniform bound on the limiting field over `cu_m`;
the input needed is a supremum bound for the **value of a single shell** `j_k` on a
**larger** cube `cu_m`, `k ≤ m`. The `J3` law controls `j_k` only on its own cube
`cu_k`, and the bound on `cu_m` follows from the stationarity of the prefix law
together with a finite maximum over the `3^{d(m-k)}` scale-`k` sub-cubes of
`cu_m`.

This module proves that bound. The route mirrors the increment
module `IncrementLinftyLargeCube` exactly:

* on each scale-`k` sub-cube of `cu_m` the shell's value norm is the translated
  natural-cube value norm `ShellField.shellCubeValueNorm k (translate z (omega k))`
  with centre `z = cubeCenter R` (the half-open cube is reached through the
  closed-set extension used in `IncrementLinftyLargeCube`);
* each translated value norm has a symmetric `Gamma₂` tail at the **unit**
  amplitude, by `J3` and the one-shell stationarity of the prefix law, with
  no centering or independence hypothesis;
* the finite maximum over the `3^{d(m-k)}` sub-cubes costs the factor
  `(3 log N)^{1/2}` with `N = 3^{d(m-k)}`, that is
  `√(3 d log 3) * √(m-k)`; the amplitude is stated at the honest union-bound
  shape `shellValueLargeCubeConst d * √(1 + (m-k))`, which also covers the
  boundary case `k = m`, where the sub-cube family is the singleton
  `{cu_k}` and the amplitude is the unit constant.

Only the prefix law (dimension and per-shell stationarity) and `J3` are
used; `J1`, `J2` and `J4` are not needed, because no sum, average or centring
of shells is taken.

## Main definitions

* `translatedShellValueSupBound`: the scale-`k` value norm of one shell
  translated by a centre `z`.
* `shellValueLargeCubeSupBound`: the measurable large-cube envelope, the
  finite maximum of the translated value norms over the sub-cube centres.
* `shellValueLargeCubeConst`: the explicit dimensional constant
  `1 + √(3 d log 3)`.

## Main results

* `matrixOperatorNorm_shellValue_le_shellCubeValueNorm_cubeSet` and its
  translated form: the value control reaches the **half-open** cube.
* `matrixOperatorNorm_shellValue_le_shellValueLargeCubeSupBound`: one random
  variable dominates `matrixOperatorNorm (omega k x)` at every point of
  `cubeSet (originCube d m)`, and of the open cube.
* `isBigOWith_gammaSigma_translatedShellValueSupBound`,
  `isBigOWith_gammaSigma_shellValueLargeCubeSupBound`: the `Gamma₂` tails.

## References

* `e.Xm.deff` and the "Moreover" block of `l.ellip.k.scales.estimates`.
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

/-! ## The half-open natural cube -/

/-- The matrix operator norm of one shell's value is continuous, so the
natural-cube value control reaches the closure of the open cube. -/
private theorem continuous_matrixOperatorNorm_shellValue (j : ShellField d) :
    Continuous fun x : Vec d ↦ matrixOperatorNorm (j x) :=
  ShellField.continuous_matrixOperatorNorm.comp j.1.1.continuous

/-- The scale-`k` natural-cube value control bounds the matrix operator norm
at every point of the **half-open** natural cube `cu_k`. The control of
`ShellField.matrixOperatorNorm_apply_le_shellCubeValueNorm` is stated on the
open cube; continuity of the shell value extends it to the closure, hence to
the half-open representative. -/
theorem matrixOperatorNorm_shellValue_le_shellCubeValueNorm_cubeSet
    (k : ℕ) (j : ShellField d) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (k : ℤ))) :
    matrixOperatorNorm (j x) ≤ ShellField.shellCubeValueNorm k j := by
  have hclosed : IsClosed {y : Vec d |
      matrixOperatorNorm (j y) ≤ ShellField.shellCubeValueNorm k j} :=
    isClosed_le (continuous_matrixOperatorNorm_shellValue j) continuous_const
  have hsub : openCubeSet (originCube d (k : ℤ)) ⊆ {y : Vec d |
      matrixOperatorNorm (j y) ≤ ShellField.shellCubeValueNorm k j} :=
    fun _ hy ↦ ShellField.matrixOperatorNorm_apply_le_shellCubeValueNorm k j
      ⟨_, hy⟩
  exact (hclosed.closure_subset_iff.2 hsub)
    (cubeSet_subset_closure_openCubeSet (originCube d (k : ℤ)) hx)

/-- The translated form: the scale-`k` value control of the shell translated
by `z` bounds the matrix operator norm of the shell at every point of the
**half-open** translate `z + cu_k`, that is, at every `x` with `x - z ∈ cu_k`.
This is the deterministic core of the stationarity route. -/
theorem matrixOperatorNorm_shellValue_le_shellCubeValueNorm_translate_cubeSet
    (k : ℕ) (j : ShellField d) (z : Vec d) {x : Vec d}
    (hx : x - z ∈ cubeSet (originCube d (k : ℤ))) :
    matrixOperatorNorm (j x) ≤
      ShellField.shellCubeValueNorm k (ShellField.translate z j) := by
  have h := matrixOperatorNorm_shellValue_le_shellCubeValueNorm_cubeSet k
    (ShellField.translate z j) hx
  simpa only [ShellField.translate_apply, sub_add_cancel] using h

/-! ## The translated value envelope -/

/-- The one-shell value envelope on the translate of the natural cube `cu_k`
by a deterministic centre `z`: the scale-`k` value norm of the shell translated
by `z`. -/
def translatedShellValueSupBound (k : ℕ) (z : Vec d) (omega : ShellSeq d) : ℝ :=
  ShellField.shellCubeValueNorm k (ShellField.translate z (omega k))

/-- The translated value envelope is nonnegative. -/
theorem translatedShellValueSupBound_nonneg (k : ℕ) (z : Vec d)
    (omega : ShellSeq d) :
    0 ≤ translatedShellValueSupBound k z omega :=
  ShellField.shellCubeValueNorm_nonneg k (ShellField.translate z (omega k))

/-- The translated value envelope is measurable in the shell sequence. -/
theorem measurable_translatedShellValueSupBound (k : ℕ) (z : Vec d) :
    Measurable (translatedShellValueSupBound k z : ShellSeq d → ℝ) :=
  ((ShellField.shellCubeValueNorm_measurable k).comp
    (ShellField.measurable_translate z)).comp
      (ShellField.measurable_shellCoordinate k)

/-- The translated value envelope bounds the matrix operator norm of the shell
at every point of the half-open translate of `cu_k`. -/
theorem matrixOperatorNorm_shellValue_le_translatedShellValueSupBound
    (omega : ShellSeq d) (k : ℕ) (z : Vec d) {x : Vec d}
    (hx : x - z ∈ cubeSet (originCube d (k : ℤ))) :
    matrixOperatorNorm ((omega k) x) ≤
      translatedShellValueSupBound k z omega :=
  matrixOperatorNorm_shellValue_le_shellCubeValueNorm_translate_cubeSet k
    (omega k) z hx

/-! ## The large-cube envelope -/

/-- The single random variable dominating the value of the shell `omega k` on
the whole large cube `cu_m`: the finite maximum of the translated value
envelopes over the `3^{d(m-k)}` scale-`k` sub-cubes of `cu_m`. -/
def shellValueLargeCubeSupBound (k m : ℕ) (omega : ShellSeq d) : ℝ :=
  (largeCubeSubcubes d k m).sup' (largeCubeSubcubes_nonempty d k m)
    fun R ↦ translatedShellValueSupBound k (cubeCenter R) omega

/-- Each translated value envelope of the sub-cube family is dominated by the
large-cube envelope. -/
theorem translatedShellValueSupBound_le_shellValueLargeCubeSupBound_of_mem
    {k m : ℕ} {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d k m)
    (omega : ShellSeq d) :
    translatedShellValueSupBound k (cubeCenter R) omega ≤
      shellValueLargeCubeSupBound k m omega :=
  Finset.le_sup'
    (fun S : TriadicCube d ↦
      translatedShellValueSupBound k (cubeCenter S) omega) hR

/-- The large-cube value envelope is nonnegative. -/
theorem shellValueLargeCubeSupBound_nonneg (k m : ℕ) (omega : ShellSeq d) :
    0 ≤ shellValueLargeCubeSupBound k m omega := by
  obtain ⟨R, hR⟩ := largeCubeSubcubes_nonempty d k m
  exact (translatedShellValueSupBound_nonneg k (cubeCenter R) omega).trans
    (translatedShellValueSupBound_le_shellValueLargeCubeSupBound_of_mem hR
      omega)

/-- The large-cube value envelope is measurable. -/
theorem measurable_shellValueLargeCubeSupBound (k m : ℕ) :
    Measurable (shellValueLargeCubeSupBound k m : ShellSeq d → ℝ) := by
  have hmeas := Finset.measurable_sup' (largeCubeSubcubes_nonempty d k m)
    (f := fun R (omega : ShellSeq d) ↦
      translatedShellValueSupBound k (cubeCenter R) omega)
    (fun R _ ↦ measurable_translatedShellValueSupBound k (cubeCenter R))
  have hfun : (largeCubeSubcubes d k m).sup'
      (largeCubeSubcubes_nonempty d k m)
      (fun R (omega : ShellSeq d) ↦
        translatedShellValueSupBound k (cubeCenter R) omega) =
      (shellValueLargeCubeSupBound k m : ShellSeq d → ℝ) := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [hfun] at hmeas

/-- The deterministic large-cube value estimate: at every point of the
half-open large cube `cu_m`, the matrix operator norm of the shell `omega k`
is dominated by one measurable random variable. -/
theorem matrixOperatorNorm_shellValue_le_shellValueLargeCubeSupBound
    (omega : ShellSeq d) {k m : ℕ} (hkm : k ≤ m) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm ((omega k) x) ≤
      shellValueLargeCubeSupBound k m omega := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_largeCubeSubcubes hkm hx
  have hpoint :=
    matrixOperatorNorm_shellValue_le_translatedShellValueSupBound omega k
      (cubeCenter R) hxR
  exact hpoint.trans
    (translatedShellValueSupBound_le_shellValueLargeCubeSupBound_of_mem hR
      omega)

/-! ## The `Gamma₂` tail of the translated value envelope -/

/-- The translated value envelope of one shell has the symmetric `Gamma₂` tail
at the **unit** amplitude. Only the prefix law (dimension and one-shell
stationarity) and `J3` are used: no centering, no independence. -/
theorem isBigOWith_gammaSigma_translatedShellValueSupBound
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (translatedShellValueSupBound k z) 1 := by
  have hOrigin : IndependentSums.IsBigOWith P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ ShellField.shellCubeValueNorm k (omega k)) 1 :=
    (hJ3.isBigOWith_gammaSigma_j3Observable_coordinate k).of_le
      fun F ↦ ShellField.shellCubeValueNorm_le_j3Observable k (F k)
  exact hPrefix.isBigOWith_gammaSigma_shellObservable_translate k z
    (F := ShellField.shellCubeValueNorm k)
    (ShellField.shellCubeValueNorm_measurable k) hOrigin

/-! ## The explicit constant -/

/-- The explicit dimensional constant of the single-shell large-cube value
estimate: the unit amplitude of the translated value envelope plus the maximum
factor `√(3 d log 3)` produced by the `3^{d(m-k)}` sub-cubes of the finite
maximum rule. The unit summand makes the amplitude an honest bound also at the
boundary `k = m`. -/
def shellValueLargeCubeConst (d : ℕ) : ℝ :=
  1 + Real.sqrt (3 * (d : ℝ) * Real.log 3)

private theorem three_mul_log_three_pos (hd : 0 < d) :
    0 < 3 * (d : ℝ) * Real.log 3 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact mul_pos (by positivity) hlog

/-- The explicit large-cube value constant is positive in every positive
dimension: it depends on `d` alone, so its positivity needs no probabilistic
data. -/
theorem shellValueLargeCubeConst_pos_of_pos (hd : 0 < d) :
    0 < shellValueLargeCubeConst d := by
  rw [shellValueLargeCubeConst]
  exact add_pos (by norm_num) (Real.sqrt_pos.2 (three_mul_log_three_pos hd))

/-- The explicit large-cube value constant is positive under the standing
dimension condition. -/
theorem shellValueLargeCubeConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < shellValueLargeCubeConst d :=
  shellValueLargeCubeConst_pos_of_pos (lt_of_lt_of_le (by norm_num)
    hPrefix.dimension)

/-- The explicit large-cube value constant is at least one. -/
theorem one_le_shellValueLargeCubeConst (d : ℕ) :
    1 ≤ shellValueLargeCubeConst d := by
  rw [shellValueLargeCubeConst]
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

private theorem rpow_two_inv_eq_sqrt (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

private theorem two_le_largeCubeSubcubes_card {k m : ℕ} (hd : 0 < d)
    (hkm : k < m) : 2 ≤ (largeCubeSubcubes d k m).card := by
  have hgap : m - k ≠ 0 := by omega
  have hbase : 2 ≤ 3 ^ d := by
    calc (2 : ℕ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  rw [largeCubeSubcubes_card]
  exact hbase.trans (Nat.le_self_pow hgap _)

private theorem log_largeCubeSubcubes_card (d k m : ℕ) :
    Real.log ((largeCubeSubcubes d k m).card : ℝ) =
      ((m - k : ℕ) : ℝ) * ((d : ℝ) * Real.log 3) := by
  have hcard : ((largeCubeSubcubes d k m).card : ℝ) = ((3 : ℝ) ^ d) ^ (m - k) := by
    rw [largeCubeSubcubes_card]
    push_cast
    ring
  rw [hcard, Real.log_pow, Real.log_pow]

/-- The maximum factor of the finite-maximum rule for the sub-cube family:
`(3 log N)^{1/2} = √(3 d log 3) √(m-k)` with `N = 3^{d(m-k)}`. -/
private theorem rpow_three_mul_log_card (hd : 0 < d) (k m : ℕ) :
    (3 * Real.log ((largeCubeSubcubes d k m).card : ℝ)) ^ (2 : ℝ)⁻¹ =
      Real.sqrt (3 * (d : ℝ) * Real.log 3) * Real.sqrt ((m - k : ℕ) : ℝ) := by
  have hbase : 3 * Real.log ((largeCubeSubcubes d k m).card : ℝ) =
      (3 * (d : ℝ) * Real.log 3) * ((m - k : ℕ) : ℝ) := by
    rw [log_largeCubeSubcubes_card]
    ring
  rw [rpow_two_inv_eq_sqrt, hbase,
    Real.sqrt_mul (three_mul_log_three_pos hd).le]

/-! ## The `Gamma₂` tail of the large-cube value envelope -/

/-- The single-shell large-cube value envelope obeys the symmetric `Gamma₂`
bound at the honest union-bound amplitude
`shellValueLargeCubeConst d * √(1 + (m-k))`.

For `k < m` the finite maximum over the `3^{d(m-k)}` sub-cubes costs the
factor `(3 log 3^{d(m-k)})^{1/2} = √(3 d log 3) √(m-k)` on the unit amplitude;
for `k = m` the sub-cube family is the singleton `{cu_k}` and the unit
amplitude itself is bounded by the constant. -/
theorem isBigOWith_gammaSigma_shellValueLargeCubeSupBound
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {k m : ℕ} (hkm : k ≤ m) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (shellValueLargeCubeSupBound k m)
      (shellValueLargeCubeConst d *
        Real.sqrt (1 + ((m - k : ℕ) : ℝ))) := by
  rcases lt_or_eq_of_le hkm with hlt | heq
  · -- `k < m`: the finite maximum over the `3^{d(m-k)}` sub-cubes.
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
    have hsup := IndependentSums.isBigOWith_gammaSigma_finset_sup'
      (μ := P.toMeasure) (largeCubeSubcubes d k m)
      (largeCubeSubcubes_nonempty d k m)
      (X := fun R (omega : ShellSeq d) ↦
        translatedShellValueSupBound k (cubeCenter R) omega)
      (A := 1) (σ := 2) (by norm_num)
      (two_le_largeCubeSubcubes_card hd hlt)
      (fun R _ ↦ isBigOWith_gammaSigma_translatedShellValueSupBound
        hPrefix hJ3 k (cubeCenter R))
    have hfactor :
        ((3 * Real.log ((largeCubeSubcubes d k m).card : ℝ)) ^ (2 : ℝ)⁻¹ * 1) ≤
          shellValueLargeCubeConst d *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ)) := by
      rw [rpow_three_mul_log_card hd k m, mul_one]
      have hconst : 0 < shellValueLargeCubeConst d :=
        shellValueLargeCubeConst_pos_of_pos hd
      have hsq1 : Real.sqrt (3 * (d : ℝ) * Real.log 3) ≤
          shellValueLargeCubeConst d := by
        rw [shellValueLargeCubeConst]
        linarith only [Real.sqrt_nonneg (3 * (d : ℝ) * Real.log 3)]
      have hsq2 : Real.sqrt (((m - k : ℕ) : ℝ)) ≤
          Real.sqrt (1 + ((m - k : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith only [])
      calc Real.sqrt (3 * (d : ℝ) * Real.log 3) * Real.sqrt ((m - k : ℕ) : ℝ) ≤
          shellValueLargeCubeConst d * Real.sqrt ((m - k : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsq1 (Real.sqrt_nonneg _)
      _ ≤ shellValueLargeCubeConst d *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq2 hconst.le
    exact hsup.mono_scale hfactor
  · -- `k = m`: the sub-cube family is the singleton `{cu_k}`.
    have hzero : m - k = 0 := by omega
    have hmem : ∀ R ∈ largeCubeSubcubes d k m, R = originCube d (m : ℤ) := by
      intro R hR
      have hunfold : R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - k) := by
        simpa only [largeCubeSubcubes] using hR
      rwa [hzero, descendantsAtDepth_zero, Finset.mem_singleton] at hunfold
    have hle : ∀ omega : ShellSeq d,
        shellValueLargeCubeSupBound k m omega ≤
          translatedShellValueSupBound k
            (cubeCenter (originCube d (m : ℤ))) omega := by
      intro omega
      show (largeCubeSubcubes d k m).sup'
          (largeCubeSubcubes_nonempty d k m)
          (fun R : TriadicCube d ↦
            translatedShellValueSupBound k (cubeCenter R) omega) ≤ _
      refine Finset.sup'_le _ _ ?_
      intro R hR
      rw [hmem R hR]
    have hmain : IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma 2)
        (shellValueLargeCubeSupBound k m) 1 := by
      refine (isBigOWith_gammaSigma_translatedShellValueSupBound hPrefix hJ3 k
        (cubeCenter (originCube d (m : ℤ)))).of_le ?_
      exact hle
    refine hmain.mono_scale ?_
    have hcast : ((m - k : ℕ) : ℝ) = (0 : ℝ) := by
      rw [hzero, Nat.cast_zero]
    rw [hcast, add_zero, Real.sqrt_one, mul_one]
    exact one_le_shellValueLargeCubeConst d

/-! ## The literal `L∞(cu_m)` carrier -/

section CubeLinfty

open scoped Matrix.Norms.L2Operator

end CubeLinfty

end

end SuperdiffusionCLT.Section2.Estimates.Stream