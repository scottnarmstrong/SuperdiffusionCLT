/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB

/-!
# One shell's derivative on a large cube

The proof of `l.w.basic.regbounds`
bounds the Jacobian of the flux `(k_{L'} - k_{ℓ'})p` on `cu_m` by splitting it
at the scale `m - 1`; the small-cube estimate
`exists_witness_cubeLpENorm_streamFluxWeakGradient` covers the shells `k ≥ m`,
and the shells **below** the cube scale need the display
`‖∇(k_{m−1} − k_{ℓ'})p‖_{L̲^8(cu_m)} = O_{Γ₂}(C|p| 3^{-ℓ'})` of the hypothesis
`hNablaKmnLow` of `l.w.basic.regbounds`. The printed proof
gets those shells from stationarity over the `3^{d(m-k)}` sub-cubes of `cu_m`,
which is exactly the technique of the large-cube clauses.

This module proves that display, as the derivative analogue of the
value module `ShellValueLargeCube`; the route mirrors it exactly:

* on each scale-`k` sub-cube of `cu_m` the shell's derivative norm is the
  translated natural-cube derivative norm
  `ShellField.shellCubeDerivNorm k (ShellField.translate z (omega k))` with
  centre `z = cubeCenter R` (the half-open cube is reached through the
  closed-set extension used in `IncrementLinftyLargeCube`);
* each translated derivative norm has a symmetric `Gamma₂` tail at the
  **derivative scale** `3^{-k}`, by `J3` (through the factor `√d 3^k ‖∇j_k‖` of
  the `j3Observable`) and the one-shell stationarity of the prefix law, with
  no centering or independence hypothesis;
* the finite maximum over the `3^{d(m-k)}` sub-cubes costs the factor
  `(3 log N)^{1/2}` with `N = 3^{d(m-k)}`, that is
  `√(3 d log 3) * √(m-k)`; the amplitude is stated at the honest union-bound
  shape `shellDerivLargeCubeConst d * 3^{-k} * √(1 + (m-k))`, which also covers
  the boundary case `k = m`, where the sub-cube family is the singleton
  `{cu_k}` and the amplitude is the unit constant.

Only the prefix law (dimension and per-shell stationarity) and `J3` are
used; `J1`, `J2` and `J4` are not needed, because no sum, average or centring
of shells is taken.

## Main results

* `matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound` and its open-cube
  form: one random variable dominates
  `matrixDerivativeNorm (ShellField.deriv (omega k) x)` at every point of
  `cubeSet (originCube d m)`, and of the open cube.
* `isBigOWith_gammaSigma_translatedShellDerivSupBound`,
  `isBigOWith_gammaSigma_shellDerivLargeCubeSupBound`: the `Gamma₂` tails.
* `isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound`: the finite-sum tail
  at the amplitude `shellDerivLargeCubeSumConst d * 3^{-a} * √(1 + (m-a))`,
  the envelope of `∑_{k ∈ (a,b]} ∇ j_k` on `cu_m` with the constant
  `shellDerivLargeCubeSumConst d = gammaTriangleConst 2 * shellDerivLargeCubeConst d`.
* `norm_hilbertMat_streamFluxWeakGradient_le_largeCube` and
  `exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube`: the display
  required by the hypothesis `hNablaKmnLow` of `l.w.basic.regbounds`, in the carrier
  `HilbertMat.ofMat ∘ streamFluxWeakGradient` at the amplitude
  `(1 + √d * shellDerivLargeCubeSumConst d * √(1 + (m-a))) * (|p| 3^{-a})`.
  The only difference from the paper's printed amplitude `C |p| 3^{-ℓ'}`
  is the honest union-bound factor `√(1 + (m - a))`, which the printed proof
  absorbs into the dimensional constant `C` of the scale window.

## References

* `l.w.basic.regbounds` and the "Moreover" block of `l.ellip.k.scales.estimates`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Set
open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The half-open natural cube -/

/-- Continuity of the exact induced derivative norm of one shell. -/
private theorem continuous_matrixDerivativeNorm_deriv (j : ShellField d) :
    Continuous fun x : Vec d ↦ ShellField.matrixDerivativeNorm (ShellField.deriv j x) :=
  ShellField.matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous

/-- The scale-`k` derivative control bounds the exact induced derivative norm
at every point of the **half-open** natural cube `cu_k`: the open-cube control
of `ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm` extends over
the closure by continuity. -/
theorem matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_cubeSet
    (k : ℕ) (j : ShellField d) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (k : ℤ))) :
    ShellField.matrixDerivativeNorm (ShellField.deriv j x) ≤
      ShellField.shellCubeDerivNorm k j := by
  have hclosed : IsClosed {y : Vec d |
      ShellField.matrixDerivativeNorm (ShellField.deriv j y) ≤
        ShellField.shellCubeDerivNorm k j} :=
    isClosed_le (continuous_matrixDerivativeNorm_deriv j) continuous_const
  have hsub : openCubeSet (originCube d (k : ℤ)) ⊆ {y : Vec d |
      ShellField.matrixDerivativeNorm (ShellField.deriv j y) ≤
        ShellField.shellCubeDerivNorm k j} :=
    fun _ hy ↦ ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm k j hy
  exact (hclosed.closure_subset_iff.2 hsub)
    (cubeSet_subset_closure_openCubeSet (originCube d (k : ℤ)) hx)

/-- The translated form: the scale-`k` derivative control of the shell
translated by `z` bounds the exact induced derivative norm at every point of
the **half-open** translate `z + cu_k` (the derivative of a translate is the
translate of the derivative). -/
theorem matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_translate_cubeSet
    (k : ℕ) (j : ShellField d) (z : Vec d) {x : Vec d}
    (hx : x - z ∈ cubeSet (originCube d (k : ℤ))) :
    ShellField.matrixDerivativeNorm (ShellField.deriv j x) ≤
      ShellField.shellCubeDerivNorm k (ShellField.translate z j) := by
  have h := matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_cubeSet k
    (ShellField.translate z j) hx
  simpa only [ShellField.translate_deriv, sub_add_cancel] using h

/-! ## The translated derivative envelope -/

/-- The one-shell derivative envelope on the translate of `cu_k` by a
deterministic centre `z`. -/
def translatedShellDerivSupBound (k : ℕ) (z : Vec d) (omega : ShellSeq d) : ℝ :=
  ShellField.shellCubeDerivNorm k (ShellField.translate z (omega k))

/-- The translated derivative envelope is nonnegative. -/
theorem translatedShellDerivSupBound_nonneg (k : ℕ) (z : Vec d)
    (omega : ShellSeq d) :
    0 ≤ translatedShellDerivSupBound k z omega :=
  ShellField.shellCubeDerivNorm_nonneg k (ShellField.translate z (omega k))

/-- The translated derivative envelope is measurable in the shell sequence. -/
theorem measurable_translatedShellDerivSupBound (k : ℕ) (z : Vec d) :
    Measurable (translatedShellDerivSupBound k z : ShellSeq d → ℝ) :=
  ((ShellField.shellCubeDerivNorm_measurable k).comp
    (ShellField.measurable_translate z)).comp
      (ShellField.measurable_shellCoordinate k)

/-- The translated derivative envelope bounds the exact induced derivative
norm on the half-open translate of `cu_k`. -/
theorem matrixDerivativeNorm_deriv_le_translatedShellDerivSupBound
    (omega : ShellSeq d) (k : ℕ) (z : Vec d) {x : Vec d}
    (hx : x - z ∈ cubeSet (originCube d (k : ℤ))) :
    ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) ≤
      translatedShellDerivSupBound k z omega :=
  matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_translate_cubeSet k
    (omega k) z hx

/-! ## The large-cube envelope -/

/-- The one random variable dominating the derivative of the shell `omega k`
on the whole large cube `cu_m`: the finite maximum of the translated
derivative envelopes over the `3^{d(m-k)}` scale-`k` sub-cubes. -/
def shellDerivLargeCubeSupBound (k m : ℕ) (omega : ShellSeq d) : ℝ :=
  (largeCubeSubcubes d k m).sup' (largeCubeSubcubes_nonempty d k m)
    fun R ↦ translatedShellDerivSupBound k (cubeCenter R) omega

/-- Each translated derivative envelope of the sub-cube family is dominated by
the large-cube envelope. -/
theorem translatedShellDerivSupBound_le_shellDerivLargeCubeSupBound_of_mem
    {k m : ℕ} {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d k m)
    (omega : ShellSeq d) :
    translatedShellDerivSupBound k (cubeCenter R) omega ≤
      shellDerivLargeCubeSupBound k m omega :=
  Finset.le_sup'
    (fun S : TriadicCube d ↦
      translatedShellDerivSupBound k (cubeCenter S) omega) hR

/-- The large-cube derivative envelope is nonnegative. -/
theorem shellDerivLargeCubeSupBound_nonneg (k m : ℕ) (omega : ShellSeq d) :
    0 ≤ shellDerivLargeCubeSupBound k m omega := by
  obtain ⟨R, hR⟩ := largeCubeSubcubes_nonempty d k m
  exact (translatedShellDerivSupBound_nonneg k (cubeCenter R) omega).trans
    (translatedShellDerivSupBound_le_shellDerivLargeCubeSupBound_of_mem hR
      omega)

/-- The large-cube derivative envelope is measurable. -/
theorem measurable_shellDerivLargeCubeSupBound (k m : ℕ) :
    Measurable (shellDerivLargeCubeSupBound k m : ShellSeq d → ℝ) := by
  have hmeas := Finset.measurable_sup' (largeCubeSubcubes_nonempty d k m)
    (f := fun R (omega : ShellSeq d) ↦
      translatedShellDerivSupBound k (cubeCenter R) omega)
    (fun R _ ↦ measurable_translatedShellDerivSupBound k (cubeCenter R))
  have hfun : (largeCubeSubcubes d k m).sup'
      (largeCubeSubcubes_nonempty d k m)
      (fun R (omega : ShellSeq d) ↦
        translatedShellDerivSupBound k (cubeCenter R) omega) =
      (shellDerivLargeCubeSupBound k m : ShellSeq d → ℝ) := by
    funext omega
    exact Finset.sup'_apply _ _ omega
  rwa [hfun] at hmeas

/-- The deterministic large-cube derivative estimate: at every point of the
half-open large cube `cu_m` the exact induced norm of the derivative of the
shell `omega k` is dominated by one measurable variable. -/
theorem matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound
    (omega : ShellSeq d) {k m : ℕ} (hkm : k ≤ m) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) ≤
      shellDerivLargeCubeSupBound k m omega := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_largeCubeSubcubes hkm hx
  have hpoint :=
    matrixDerivativeNorm_deriv_le_translatedShellDerivSupBound omega k
      (cubeCenter R) hxR
  exact hpoint.trans
    (translatedShellDerivSupBound_le_shellDerivLargeCubeSupBound_of_mem hR
      omega)

/-- The deterministic large-cube derivative estimate on the open cube. -/
theorem matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound_open
    (omega : ShellSeq d) {k m : ℕ} (hkm : k ≤ m) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ))) :
    ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) ≤
      shellDerivLargeCubeSupBound k m omega :=
  matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound omega hkm
    (openCubeSet_subset_cubeSet _ hx)

/-! ## The `Gamma₂` tail of the translated derivative envelope -/

/-- The translated derivative envelope of one shell has the symmetric `Gamma₂`
tail at the **derivative scale** `3^{-k}`: only the prefix law and `J3` are
used (no centering, no independence), via the one-shell transport
`isBigOWith_gammaSigma_shellCubeDerivNorm_translate`. -/
theorem isBigOWith_gammaSigma_translatedShellDerivSupBound
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (translatedShellDerivSupBound k z) (((3 : ℝ) ^ k)⁻¹) :=
  isBigOWith_gammaSigma_shellCubeDerivNorm_translate hPrefix hJ3 (le_refl k) z

/-! ## The explicit constant -/

/-- The explicit dimensional constant of the single-shell large-cube derivative
estimate: the unit amplitude of the translated envelope plus the maximum
factor `√(3 d log 3)` of the `3^{d(m-k)}` sub-cubes; the unit summand keeps the
amplitude honest also at the boundary `k = m`. -/
def shellDerivLargeCubeConst (d : ℕ) : ℝ :=
  1 + Real.sqrt (3 * (d : ℝ) * Real.log 3)

private theorem three_mul_log_three_pos (hd : 0 < d) :
    0 < 3 * (d : ℝ) * Real.log 3 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact mul_pos (by positivity) hlog

/-- The explicit large-cube derivative constant is positive in every positive
dimension: it depends on `d` alone. -/
theorem shellDerivLargeCubeConst_pos_of_pos (hd : 0 < d) :
    0 < shellDerivLargeCubeConst d := by
  rw [shellDerivLargeCubeConst]
  exact add_pos (by norm_num) (Real.sqrt_pos.2 (three_mul_log_three_pos hd))

/-- The explicit large-cube derivative constant is positive under the standing
dimension condition. -/
theorem shellDerivLargeCubeConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < shellDerivLargeCubeConst d :=
  shellDerivLargeCubeConst_pos_of_pos (lt_of_lt_of_le (by norm_num)
    hPrefix.dimension)

/-- The explicit large-cube derivative constant is at least one. -/
theorem one_le_shellDerivLargeCubeConst (d : ℕ) :
    1 ≤ shellDerivLargeCubeConst d := by
  rw [shellDerivLargeCubeConst]
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

/-! ## The `Gamma₂` tail of the large-cube derivative envelope -/

/-- The maximum factor of the finite-maximum rule is absorbed by the explicit
constant: `√(3 d log 3) √r ≤ (1 + √(3 d log 3)) √(1 + r)`. -/
private theorem sqrt_mul_sqrt_le_const_mul {d : ℕ} (hd : 0 < d) (r : ℝ) :
    Real.sqrt (3 * (d : ℝ) * Real.log 3) * Real.sqrt r ≤
      shellDerivLargeCubeConst d * Real.sqrt (1 + r) := by
  have hconst : 0 < shellDerivLargeCubeConst d :=
    shellDerivLargeCubeConst_pos_of_pos hd
  have hsq1 : Real.sqrt (3 * (d : ℝ) * Real.log 3) ≤
      shellDerivLargeCubeConst d := by
    rw [shellDerivLargeCubeConst]
    linarith only [Real.sqrt_nonneg (3 * (d : ℝ) * Real.log 3)]
  have hsq2 : Real.sqrt r ≤ Real.sqrt (1 + r) :=
    Real.sqrt_le_sqrt (by linarith only [])
  calc Real.sqrt (3 * (d : ℝ) * Real.log 3) * Real.sqrt r ≤
      shellDerivLargeCubeConst d * Real.sqrt r :=
    mul_le_mul_of_nonneg_right hsq1 (Real.sqrt_nonneg r)
  _ ≤ shellDerivLargeCubeConst d * Real.sqrt (1 + r) :=
    mul_le_mul_of_nonneg_left hsq2 hconst.le

/-- The single-shell large-cube derivative envelope obeys the symmetric
`Gamma₂` bound at the honest union-bound amplitude
`shellDerivLargeCubeConst d * 3^{-k} * √(1 + (m-k))`: for `k < m` the finite
maximum over the `3^{d(m-k)}` sub-cubes costs `√(3 d log 3) √(m-k)` on the
derivative scale `3^{-k}`; for `k = m` the family is the singleton `{cu_k}`. -/
theorem isBigOWith_gammaSigma_shellDerivLargeCubeSupBound
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {k m : ℕ} (hkm : k ≤ m) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (shellDerivLargeCubeSupBound k m)
      (shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
        Real.sqrt (1 + ((m - k : ℕ) : ℝ))) := by
  rcases lt_or_eq_of_le hkm with hlt | heq
  · -- `k < m`: the finite maximum over the `3^{d(m-k)}` sub-cubes.
    have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
    have hsup := IndependentSums.isBigOWith_gammaSigma_finset_sup'
      (μ := P.toMeasure) (largeCubeSubcubes d k m)
      (largeCubeSubcubes_nonempty d k m)
      (X := fun R (omega : ShellSeq d) ↦
        translatedShellDerivSupBound k (cubeCenter R) omega)
      (A := ((3 : ℝ) ^ k)⁻¹) (σ := 2) (by norm_num)
      (two_le_largeCubeSubcubes_card hd hlt)
      (fun R _ ↦ isBigOWith_gammaSigma_translatedShellDerivSupBound
        hPrefix hJ3 k (cubeCenter R))
    have hinv : 0 ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
    have hfactor :
        ((3 * Real.log ((largeCubeSubcubes d k m).card : ℝ)) ^ (2 : ℝ)⁻¹ *
            ((3 : ℝ) ^ k)⁻¹) ≤
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ)) := by
      rw [rpow_three_mul_log_card hd k m]
      refine le_trans (mul_le_mul_of_nonneg_right
        (sqrt_mul_sqrt_le_const_mul hd ((m - k : ℕ) : ℝ)) hinv) ?_
      rw [mul_right_comm (shellDerivLargeCubeConst d)
        (Real.sqrt (1 + ((m - k : ℕ) : ℝ))) ((3 : ℝ) ^ k)⁻¹]
    exact hsup.mono_scale hfactor
  · -- `k = m`: the sub-cube family is the singleton `{cu_k}`.
    have hzero : m - k = 0 := by omega
    have hmem : ∀ R ∈ largeCubeSubcubes d k m, R = originCube d (m : ℤ) := by
      intro R hR
      have hunfold : R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - k) := by
        simpa only [largeCubeSubcubes] using hR
      rwa [hzero, descendantsAtDepth_zero, Finset.mem_singleton] at hunfold
    have hle : ∀ omega : ShellSeq d,
        shellDerivLargeCubeSupBound k m omega ≤
          translatedShellDerivSupBound k
            (cubeCenter (originCube d (m : ℤ))) omega := by
      intro omega
      show (largeCubeSubcubes d k m).sup'
          (largeCubeSubcubes_nonempty d k m)
          (fun R : TriadicCube d ↦
            translatedShellDerivSupBound k (cubeCenter R) omega) ≤ _
      refine Finset.sup'_le _ _ ?_
      intro R hR
      rw [hmem R hR]
    have hmain : IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma 2)
        (shellDerivLargeCubeSupBound k m) (((3 : ℝ) ^ k)⁻¹) := by
      refine (isBigOWith_gammaSigma_translatedShellDerivSupBound hPrefix hJ3 k
        (cubeCenter (originCube d (m : ℤ)))).of_le ?_
      exact hle
    refine hmain.mono_scale ?_
    have hcast : ((m - k : ℕ) : ℝ) = (0 : ℝ) := by
      rw [hzero, Nat.cast_zero]
    have hinv : 0 ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
    have htarget : shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
        Real.sqrt (1 + ((m - k : ℕ) : ℝ)) =
        shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ := by
      rw [hcast, add_zero, Real.sqrt_one, mul_one]
    rw [htarget]
    have hle2 : ((3 : ℝ) ^ k)⁻¹ ≤
        shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ := by
      calc ((3 : ℝ) ^ k)⁻¹ = 1 * ((3 : ℝ) ^ k)⁻¹ := (one_mul _).symm
        _ ≤ shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ :=
          mul_le_mul_of_nonneg_right (one_le_shellDerivLargeCubeConst d) hinv
    exact hle2

/-! ## The volume-normalized `L∞(cu_m)` carrier -/

end

end SuperdiffusionCLT.Section2.Estimates.Stream
