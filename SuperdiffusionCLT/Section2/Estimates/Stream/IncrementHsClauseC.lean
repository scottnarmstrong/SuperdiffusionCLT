/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementHsClauseB

/-!
# The one-shell Gagliardo display of the `H̲^s` clause

The paper bounds the Gagliardo part
of one shell on the large cube by

> `[j_k]²_{H̲^s(cu_l)} ≤ C ⨍_{cu_l} ∫_{cu_l} |j_k(x) − j_k(y)|² |x−y|^{−d−2s}`
> `                   ≤ C ⨍_{cu_l} ∫_{cu_l} min{1, 3^{−k}|x−y|}² |x−y|^{−d−2s}`
> `                   ≤ C 3^{−2sk}`,

taking the random bound on `|j_k(x) − j_k(y)|` **pointwise in the pair** and
only then integrating. This module proves that display for the carrier
`Section2.Norms.cubeEuclideanGagliardoESeminorm` at exponent `2`, with a
`Γ₂` amplitude `C(d,s) 3^{−sk}` that is uniform in the cube scale `l`.

## Why the pair bound is integrated over a subdivision

The two inputs are available: the deterministic kernel integral
`lintegral_shifted_le` of `IncrementHsClause` and the two-point random envelope
`shellPairEnvelope` of `IncrementHsClauseB`, whose `Γ₂` tail is uniform in the
pair. What is missing between them is a *joint* measurability of
`(x, omega) ↦ shellCubeValueNorm k (translate x (omega k))` in the spatial and
the probabilistic variable: the regularity of the cube observables is
lower semicontinuity in the field and measurability in the sample at a fixed
translation, not continuity in the translation, so the continuum averaging
lemmas for Orlicz norms of measure averages cannot be applied to the
translated observables directly.

The subdivision of the large cube into its `3^{d(l−r)}` triadic subcubes of
scale `r` supplies a *step* majorant instead, which is measurable in the point
by construction:

`shellStepSq r l omega x = ∑_R 1_{R}(x) · shellPairEnvelope (r+1) c_R c_R omega ²`.

Averaging the step majorant over `cu_l` is a finite convex combination of the
`Γ₁` variables `E_R²`, so the finite `Γ₂` triangle inequality
(`Probability.isBigO_gammaSigma_finset_sum_of_one_le`, amplitude `16384 ∑ a`)
gives an amplitude that does not depend on the number of subcubes, hence not on
`l`. This is the discrete form of the paper's "Jensen's inequality" step.

## Why the subcubes have scale `k − 1`

The near branch of the pair bound needs a derivative supremum over a cube that
contains the segment `[x, y]` *and* is centred at a subcube centre, so that the
supremum is a one-point observable of the shell. With subcubes of scale `r` and
a near threshold `|x − y| < 3^r/2` the segment lies in `x + cu_r`, and
`x + cu_r ⊆ c_R + cu_{r+1}`, so the observable needed is the shell's own cube
norm at scale `r + 1`. Taking `r + 1 = k` keeps the observable at the shell's
own scale, which is exactly what J3 controls (`ShellLawJ3` bounds
`shellCubeValueNorm k (omega k)` and `shellCubeDerivNorm k (omega k)`, not the
norms of `omega k` on a larger cube). Every shell summed by the `H̲^s` clause
has index `k > n ≥ 0`, so `k = r + 1` with `r = k − 1` is available.

## Main definitions

* `shellStepSq`: the step majorant of the squared two-point envelope, a simple
  function of the point.

## Main results

* `sq_matrixOperatorNorm_shell_sub_le_shellStepSq`: the pointwise-in-the-pair
  bound in the step form.
* `lintegral_shellStepSq_le`: the normalized average of the step majorant, the
  finite convex combination that the `Γ₁` triangle inequality consumes.
* `card_mul_subcubeRatio`: the cancellation of the subcube count against the
  subcube volume ratio; this is the source of the `l`-uniformity.
* `enorm_euclideanGagliardoKernel_shell_sq_le`: the squared Gagliardo kernel of
  one shell is dominated pointwise by the step majorant times the radial
  integrand `radialIntegrand` of `IncrementHsClause`.

The `Γ₂` tail of the display, the passage to
`cubeEuclideanGagliardoESeminorm`, the shell sum and the clause itself are in
`IncrementHsClauseD.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Geometry of one triadic refinement -/

/-- The half-open natural cube of scale `r` sits inside the open natural cube
of scale `r + 1`. -/
private theorem mem_openCubeSet_succ_of_mem_cubeSet {r : ℕ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (r : ℤ))) :
    x ∈ openCubeSet (originCube d ((r + 1 : ℕ) : ℤ)) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  rw [mem_cubeSet_originCube_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  rw [zpow_natCast] at hlo hhi
  rw [zpow_natCast, pow_succ]
  constructor <;> linarith only [hlo, hhi, hpow]

/-- Every coordinate of a displacement is dominated by its Euclidean length.
`Vec d` carries the ambient sup norm, and the manuscript's `|·|` is
`euclideanDist`. -/
private theorem abs_sub_le_euclideanDist (x y : Vec d) (i : Fin d) :
    |x i - y i| ≤ euclideanDist x y := by
  have h1 : |x i - y i| ≤ ‖x - y‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - y) i
  exact h1.trans (norm_le_euclideanNorm (x - y))

/-- The second point of a near pair also lies in the open cube of scale
`r + 1` centred at the first point's subcube centre. -/
private theorem sub_mem_openCubeSet_succ_of_near {r : ℕ} {c x y : Vec d}
    (hx : x - c ∈ cubeSet (originCube d (r : ℤ)))
    (hnear : euclideanDist x y < (3 : ℝ) ^ r / 2) :
    y - c ∈ openCubeSet (originCube d ((r + 1 : ℕ) : ℤ)) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  rw [mem_cubeSet_originCube_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  rw [zpow_natCast] at hlo hhi
  simp only [Pi.sub_apply] at hlo hhi
  have hsym : |y i - x i| ≤ euclideanDist x y := by
    rw [abs_sub_comm]
    exact abs_sub_le_euclideanDist x y i
  have habs := abs_lt.mp (lt_of_le_of_lt hsym hnear)
  rw [zpow_natCast, pow_succ]
  simp only [Pi.sub_apply]
  constructor <;> linarith only [hlo, hhi, habs.1, habs.2, hpow]

/-- Translating both points of a pair leaves the Euclidean distance
unchanged. -/
private theorem euclideanDist_sub_right (x y c : Vec d) :
    euclideanDist (x - c) (y - c) = euclideanDist x y := by
  rw [ShellField.euclideanDist_eq_vecNorm_sub, ShellField.euclideanDist_eq_vecNorm_sub,
    sub_sub_sub_cancel_right]

/-! ## The diagonal two-point envelope at a subcube centre -/

/-- The `cu_{r+1}` value norm of the translated shell is one summand of the
diagonal value of the two-point envelope. -/
private theorem shellCubeValueNorm_le_diagEnvelope (r : ℕ) (c : Vec d)
    (omega : ShellSeq d) :
    ShellField.shellCubeValueNorm (r + 1)
        (ShellField.translate c (omega (r + 1))) ≤
      shellPairEnvelope (r + 1) c c omega := by
  have hV := ShellField.shellCubeValueNorm_nonneg (r + 1)
    (ShellField.translate c (omega (r + 1)))
  have hD := ShellField.shellCubeDerivNorm_nonneg (r + 1)
    (ShellField.translate c (omega (r + 1)))
  have hpos : (0 : ℝ) ≤ ((d : ℝ) + 1) * (3 : ℝ) ^ (r + 1) := by positivity
  simp only [shellPairEnvelope]
  linarith only [hV, mul_nonneg hpos hD]

/-- The scaled `cu_{r+1}` derivative norm of the translated shell is dominated
by the diagonal value of the two-point envelope: the envelope carries
the factor `(d+1) 3^{r+1}`, which is at least the factor `d 3^r` the mean value
inequality produces. -/
private theorem mul_shellCubeDerivNorm_le_diagEnvelope (r : ℕ) (c : Vec d)
    (omega : ShellSeq d) :
    (d : ℝ) * (3 : ℝ) ^ r *
        ShellField.shellCubeDerivNorm (r + 1)
          (ShellField.translate c (omega (r + 1))) ≤
      shellPairEnvelope (r + 1) c c omega := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hV := ShellField.shellCubeValueNorm_nonneg (r + 1)
    (ShellField.translate c (omega (r + 1)))
  have hD := ShellField.shellCubeDerivNorm_nonneg (r + 1)
    (ShellField.translate c (omega (r + 1)))
  have hdt : (0 : ℝ) ≤ (d : ℝ) * (3 : ℝ) ^ r :=
    mul_nonneg (Nat.cast_nonneg d) h3.le
  have hcoeff : (d : ℝ) * (3 : ℝ) ^ r ≤ ((d : ℝ) + 1) * (3 : ℝ) ^ (r + 1) := by
    rw [pow_succ]
    linarith only [hdt, h3]
  have hstep : (d : ℝ) * (3 : ℝ) ^ r *
      ShellField.shellCubeDerivNorm (r + 1)
        (ShellField.translate c (omega (r + 1))) ≤
      ((d : ℝ) + 1) * (3 : ℝ) ^ (r + 1) *
        ShellField.shellCubeDerivNorm (r + 1)
          (ShellField.translate c (omega (r + 1))) :=
    mul_le_mul_of_nonneg_right hcoeff hD
  simp only [shellPairEnvelope]
  linarith only [hV, hstep]

/-- The value of the shell at a point of a scale-`r` subcube is dominated by
the diagonal envelope at the subcube centre. -/
private theorem matrixOperatorNorm_apply_le_diagEnvelope (r : ℕ)
    (omega : ShellSeq d) {c x : Vec d}
    (hx : x - c ∈ cubeSet (originCube d (r : ℤ))) :
    matrixOperatorNorm ((omega (r + 1)) x) ≤
      shellPairEnvelope (r + 1) c c omega := by
  have hmem : x - c ∈ openCubeSet (originCube d ((r + 1 : ℕ) : ℤ)) :=
    mem_openCubeSet_succ_of_mem_cubeSet hx
  have h := ShellField.matrixOperatorNorm_apply_le_shellCubeValueNorm (r + 1)
    (ShellField.translate c (omega (r + 1))) ⟨x - c, hmem⟩
  have h' : matrixOperatorNorm ((omega (r + 1)) x) ≤
      ShellField.shellCubeValueNorm (r + 1)
        (ShellField.translate c (omega (r + 1))) := by
    simpa only [ShellField.translate_apply, sub_add_cancel] using h
  exact h'.trans (shellCubeValueNorm_le_diagEnvelope r c omega)

/-- The near branch: both points of a pair at Euclidean distance less than
`3^r/2` lie in the open cube `c + cu_{r+1}` around the subcube centre of the
first, so the two-point mean value inequality applies there with the shell's
own scale-`r+1` derivative norm. -/
private theorem matrixOperatorNorm_shell_sub_le_deriv_near (r : ℕ)
    (omega : ShellSeq d) {c x y : Vec d}
    (hx : x - c ∈ cubeSet (originCube d (r : ℤ)))
    (hnear : euclideanDist x y < (3 : ℝ) ^ r / 2) :
    matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y) ≤
      (d : ℝ) *
        ShellField.shellCubeDerivNorm (r + 1)
          (ShellField.translate c (omega (r + 1))) * euclideanDist x y := by
  have hxm : x - c ∈ openCubeSet (originCube d ((r + 1 : ℕ) : ℤ)) :=
    mem_openCubeSet_succ_of_mem_cubeSet hx
  have hym : y - c ∈ openCubeSet (originCube d ((r + 1 : ℕ) : ℤ)) :=
    sub_mem_openCubeSet_succ_of_near hx hnear
  have hB : ∀ z ∈ openCubeSet (originCube d ((r + 1 : ℕ) : ℤ)),
      ShellField.matrixDerivativeNorm
          (ShellField.deriv (ShellField.translate c (omega (r + 1))) z) ≤
        ShellField.shellCubeDerivNorm (r + 1)
          (ShellField.translate c (omega (r + 1))) := fun _z hz =>
    ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm (r + 1) _ hz
  have h := ShellField.matrixOperatorNorm_sub_le_of_derivNorm_le_on_openCubeSet
    (ShellField.translate c (omega (r + 1))) (originCube d ((r + 1 : ℕ) : ℤ))
    (ShellField.shellCubeDerivNorm (r + 1)
      (ShellField.translate c (omega (r + 1)))) hB hxm hym
  rw [euclideanDist_sub_right] at h
  simpa only [ShellField.translate_apply, sub_add_cancel] using h

/-- **The pointwise-in-the-pair bound at the subcube centres.** For any two
points, each read in a scale-`r` subcube of its own, the increment of the shell
of scale `r + 1` is dominated by the sum of the two diagonal envelopes times
the truncated Lipschitz profile of scale `r`. -/
private theorem matrixOperatorNorm_shell_sub_le_diagEnvelope_pair (r : ℕ)
    (omega : ShellSeq d) {c c' x y : Vec d}
    (hx : x - c ∈ cubeSet (originCube d (r : ℤ)))
    (hy : y - c' ∈ cubeSet (originCube d (r : ℤ))) :
    matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y) ≤
      (shellPairEnvelope (r + 1) c c omega +
          shellPairEnvelope (r + 1) c' c' omega) *
        min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hEc := shellPairEnvelope_nonneg (r + 1) c c omega
  have hEc' := shellPairEnvelope_nonneg (r + 1) c' c' omega
  rcases le_or_gt ((3 : ℝ) ^ r / 2) (euclideanDist x y) with hfar | hnear
  · have hone : min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) = 1 := by
      refine min_eq_left ?_
      have hid : 2 * ((3 : ℝ) ^ r)⁻¹ * ((3 : ℝ) ^ r / 2) = 1 := by
        field_simp
      calc (1 : ℝ) = 2 * ((3 : ℝ) ^ r)⁻¹ * ((3 : ℝ) ^ r / 2) := hid.symm
        _ ≤ 2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y :=
            mul_le_mul_of_nonneg_left hfar (by positivity)
    rw [hone, mul_one]
    have htri : matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y) ≤
        matrixOperatorNorm ((omega (r + 1)) x) +
          matrixOperatorNorm ((omega (r + 1)) y) := by
      simpa only [matrixOperatorNorm_eq_l2_opNorm] using
        norm_sub_le ((omega (r + 1)) x) ((omega (r + 1)) y)
    have hxv := matrixOperatorNorm_apply_le_diagEnvelope r omega hx
    have hyv := matrixOperatorNorm_apply_le_diagEnvelope r omega hy
    linarith only [htri, hxv, hyv]
  · have hmv := matrixOperatorNorm_shell_sub_le_deriv_near r omega hx hnear
    have hu0 : (0 : ℝ) ≤ ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y :=
      mul_nonneg (by positivity) (euclideanDist_nonneg x y)
    have hker : ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y ≤
        min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) := by
      refine le_min ?_ ?_
      · have hstep : ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y ≤
            ((3 : ℝ) ^ r)⁻¹ * ((3 : ℝ) ^ r / 2) :=
          mul_le_mul_of_nonneg_left hnear.le (by positivity)
        have hid : ((3 : ℝ) ^ r)⁻¹ * ((3 : ℝ) ^ r / 2) = 1 / 2 := by
          field_simp
        rw [hid] at hstep
        linarith only [hstep]
      · have hid : 2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y =
            2 * (((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) := by
          rw [mul_assoc]
        rw [hid]
        linarith only [hu0]
    have hid2 : ((d : ℝ) * (3 : ℝ) ^ r *
          ShellField.shellCubeDerivNorm (r + 1)
            (ShellField.translate c (omega (r + 1)))) *
          (((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) =
        (d : ℝ) *
          ShellField.shellCubeDerivNorm (r + 1)
            (ShellField.translate c (omega (r + 1))) * euclideanDist x y := by
      field_simp
    have hbound : (d : ℝ) * (3 : ℝ) ^ r *
        ShellField.shellCubeDerivNorm (r + 1)
          (ShellField.translate c (omega (r + 1))) ≤
        shellPairEnvelope (r + 1) c c omega +
          shellPairEnvelope (r + 1) c' c' omega := by
      have := mul_shellCubeDerivNorm_le_diagEnvelope r c omega
      linarith only [this, hEc']
    calc matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y)
        ≤ (d : ℝ) *
            ShellField.shellCubeDerivNorm (r + 1)
              (ShellField.translate c (omega (r + 1))) * euclideanDist x y := hmv
      _ = ((d : ℝ) * (3 : ℝ) ^ r *
            ShellField.shellCubeDerivNorm (r + 1)
              (ShellField.translate c (omega (r + 1)))) *
            (((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) := hid2.symm
      _ ≤ (shellPairEnvelope (r + 1) c c omega +
            shellPairEnvelope (r + 1) c' c' omega) *
            min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) :=
          mul_le_mul hbound hker hu0 (add_nonneg hEc hEc')

/-! ## The step majorant over the triadic subdivision -/

/-- The scale-`r` subcube of `cu_l` read as the half-open translate of the
natural cube by the subcube centre. This is the form the subdivision lemma
`exists_mem_largeCubeSubcubes` produces, and its Lebesgue measure is exactly
that of the natural cube by translation invariance. -/
def subcubeSlab (r : ℕ) (R : TriadicCube d) : Set (Vec d) :=
  (fun x => x - cubeCenter R) ⁻¹' cubeSet (originCube d (r : ℤ))

private theorem measurableSet_subcubeSlab (r : ℕ) (R : TriadicCube d) :
    MeasurableSet (subcubeSlab r R) :=
  (measurableSet_cubeSet _).preimage (measurable_id.sub_const _)

private theorem volume_subcubeSlab (r : ℕ) (R : TriadicCube d) :
    volume (subcubeSlab r R) = volume (cubeSet (originCube d (r : ℤ))) := by
  simpa only [subcubeSlab, sub_eq_add_neg] using
    measure_preimage_add_right (μ := (volume : Measure (Vec d)))
      (-cubeCenter R) (cubeSet (originCube d (r : ℤ)))

private theorem volume_cubeSet_eq_ofReal (Q : TriadicCube d) :
    volume (cubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
  rw [← volume_cubeSet_toReal Q,
    ENNReal.ofReal_toReal (volume_cubeSet_lt_top Q).ne]

private theorem cubeVolume_originCube_nat (dim r : ℕ) :
    cubeVolume (originCube dim (r : ℤ)) = ((3 : ℝ) ^ r) ^ dim := by
  have hscale : (originCube dim (r : ℤ)).scale = (r : ℤ) := rfl
  rw [cubeVolume_eq_pow_scale, hscale, zpow_natCast]

/-- **The step majorant of the squared two-point envelope.** On the subcube of
`cu_l` containing a point, it is the square of the diagonal envelope at that
subcube's centre; it is a simple function of the point, hence measurable there,
which is what the passage to the Gagliardo integral needs. -/
def shellStepSq (r l : ℕ) (omega : ShellSeq d) (x : Vec d) : ℝ :=
  ∑ R ∈ largeCubeSubcubes d r l,
    Set.indicator (subcubeSlab r R)
      (fun _ => shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) x

theorem shellStepSq_nonneg (r l : ℕ) (omega : ShellSeq d) (x : Vec d) :
    0 ≤ shellStepSq r l omega x :=
  Finset.sum_nonneg fun _R _ =>
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) x

theorem measurable_shellStepSq (r l : ℕ) (omega : ShellSeq d) :
    Measurable (shellStepSq r l omega) :=
  Finset.measurable_sum _ fun R _ =>
    measurable_const.indicator (measurableSet_subcubeSlab r R)

private theorem le_shellStepSq {r l : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d r l) (omega : ShellSeq d) {x : Vec d}
    (hx : x - cubeCenter R ∈ cubeSet (originCube d (r : ℤ))) :
    shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2 ≤
      shellStepSq r l omega x := by
  have hnn : ∀ S ∈ largeCubeSubcubes d r l,
      0 ≤ Set.indicator (subcubeSlab r S)
        (fun _ => shellPairEnvelope (r + 1) (cubeCenter S) (cubeCenter S) omega ^ 2)
        x := fun _S _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hsingle := Finset.single_le_sum hnn hR
  rwa [Set.indicator_of_mem (show x ∈ subcubeSlab r R from hx)] at hsingle

/-- **The pointwise-in-the-pair bound in the step form.** For every pair of
points of the large cube, the square of the shell increment is dominated by
twice the sum of the two step values times the square of the scale-`r`
truncated Lipschitz profile. -/
theorem sq_matrixOperatorNorm_shell_sub_le_shellStepSq {r l : ℕ}
    (hrl : r ≤ l) (omega : ShellSeq d) {x y : Vec d}
    (hx : x ∈ cubeSet (originCube d (l : ℤ)))
    (hy : y ∈ cubeSet (originCube d (l : ℤ))) :
    matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y) ^ 2 ≤
      2 * (shellStepSq r l omega x + shellStepSq r l omega y) *
        min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) ^ 2 := by
  obtain ⟨R, hR, hxR⟩ := exists_mem_largeCubeSubcubes hrl hx
  obtain ⟨S, hS, hyS⟩ := exists_mem_largeCubeSubcubes hrl hy
  set a := shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega with ha_def
  set b := shellPairEnvelope (r + 1) (cubeCenter S) (cubeCenter S) omega with hb_def
  have ha : 0 ≤ a := shellPairEnvelope_nonneg _ _ _ _
  have hb : 0 ≤ b := shellPairEnvelope_nonneg _ _ _ _
  have hker0 : 0 ≤ min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) :=
    le_min zero_le_one
      (mul_nonneg (by positivity) (euclideanDist_nonneg x y))
  have hpair := matrixOperatorNorm_shell_sub_le_diagEnvelope_pair r omega hxR hyS
  have hsq : matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y) ^ 2 ≤
      ((a + b) * min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y)) ^ 2 := by
    refine pow_le_pow_left₀ ?_ hpair 2
    simpa only [matrixOperatorNorm_eq_l2_opNorm] using
      norm_nonneg ((omega (r + 1)) x - (omega (r + 1)) y)
  have hexpand : ((a + b) * min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y)) ^ 2
      = (a + b) ^ 2 * min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) ^ 2 :=
    mul_pow _ _ 2
  have hstepx := le_shellStepSq hR omega hxR
  have hstepy := le_shellStepSq hS omega hyS
  have hsum : (a + b) ^ 2 ≤ 2 * (shellStepSq r l omega x + shellStepSq r l omega y) := by
    have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith only [sq_nonneg (a - b)]
    linarith only [hab, hstepx, hstepy]
  calc matrixOperatorNorm ((omega (r + 1)) x - (omega (r + 1)) y) ^ 2
      ≤ (a + b) ^ 2 * min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) ^ 2 :=
        hsq.trans_eq hexpand
    _ ≤ 2 * (shellStepSq r l omega x + shellStepSq r l omega y) *
          min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist x y) ^ 2 :=
        mul_le_mul_of_nonneg_right hsum (pow_nonneg hker0 2)

/-! ## The normalized average of the step majorant -/

private theorem ofReal_indicator_const {A : Set (Vec d)} {c : ℝ} (x : Vec d) :
    ENNReal.ofReal (Set.indicator A (fun _ => c) x) =
      Set.indicator A (fun _ => ENNReal.ofReal c) x := by
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      ENNReal.ofReal_zero]

/-- The subcube family and the volume ratio are matched: the `3^{d(l-r)}`
subcubes each carry the fraction `3^{d(r-l)}` of the normalized measure of the
large cube, and the two factors cancel. -/
theorem card_mul_subcubeRatio {r l : ℕ} (hrl : r ≤ l) :
    (((largeCubeSubcubes d r l).card : ℕ) : ℝ) *
        ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d)) = 1 := by
  have hne : ((3 : ℝ) ^ (l * d)) ≠ 0 := by positivity
  have hexp : d * (l - r) + r * d = l * d := by
    have hl : (l - r) + r = l := Nat.sub_add_cancel hrl
    calc d * (l - r) + r * d = ((l - r) + r) * d := by ring
      _ = l * d := by rw [hl]
  rw [largeCubeSubcubes_card]
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  have hrewrite : ((3 : ℝ) ^ (d * (l - r))) *
        (((3 : ℝ) ^ (l * d))⁻¹ * ((3 : ℝ) ^ (r * d)))
      = ((3 : ℝ) ^ (d * (l - r)) * (3 : ℝ) ^ (r * d)) * ((3 : ℝ) ^ (l * d))⁻¹ := by
    ring
  rw [hrewrite, ← pow_add, hexp, mul_inv_cancel₀ hne]

/-- The normalized average of the step majorant over `cu_l` is the volume-ratio
weighted sum of the squared diagonal envelopes of the subcubes. -/
theorem lintegral_shellStepSq_le (r l : ℕ) (omega : ShellSeq d) :
    ∫⁻ x, ENNReal.ofReal (shellStepSq r l omega x)
        ∂(normalizedCubeMeasure (originCube d (l : ℤ))) ≤
      ENNReal.ofReal
        ((((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) *
          ∑ R ∈ largeCubeSubcubes d r l,
            shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) := by
  set Q : TriadicCube d := originCube d (l : ℤ) with hQ_def
  set rho : ℝ := (((3 : ℝ) ^ l) ^ d)⁻¹ * (((3 : ℝ) ^ r) ^ d) with hrho_def
  have hrho0 : 0 ≤ rho := by
    rw [hrho_def]; positivity
  have hslab : ∀ R : TriadicCube d,
      normalizedCubeMeasure Q (subcubeSlab r R) ≤ ENNReal.ofReal rho := by
    intro R
    have hrestr : cubeMeasure Q (subcubeSlab r R) ≤ volume (subcubeSlab r R) := by
      rw [cubeMeasure]
      exact Measure.restrict_le_self _
    have hvol : volume (subcubeSlab r R) = ENNReal.ofReal (((3 : ℝ) ^ r) ^ d) := by
      rw [volume_subcubeSlab, volume_cubeSet_eq_ofReal, cubeVolume_originCube_nat]
    have hQvol : cubeVolume Q = ((3 : ℝ) ^ l) ^ d := by
      rw [hQ_def, cubeVolume_originCube_nat]
    rw [normalizedCubeMeasure, Measure.smul_apply, smul_eq_mul, hQvol]
    calc ENNReal.ofReal ((((3 : ℝ) ^ l) ^ d)⁻¹) * cubeMeasure Q (subcubeSlab r R)
        ≤ ENNReal.ofReal ((((3 : ℝ) ^ l) ^ d)⁻¹) *
            ENNReal.ofReal (((3 : ℝ) ^ r) ^ d) := by
          rw [← hvol]
          exact mul_le_mul_right hrestr _
      _ = ENNReal.ofReal rho := by
          rw [hrho_def, ENNReal.ofReal_mul (by positivity)]
  have hmeas : ∀ R ∈ largeCubeSubcubes d r l,
      Measurable fun x : Vec d =>
        Set.indicator (subcubeSlab r R)
          (fun _ => ENNReal.ofReal
            (shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2)) x :=
    fun R _ => measurable_const.indicator (measurableSet_subcubeSlab r R)
  have hpoint : ∀ x : Vec d, ENNReal.ofReal (shellStepSq r l omega x) =
      ∑ R ∈ largeCubeSubcubes d r l,
        Set.indicator (subcubeSlab r R)
          (fun _ => ENNReal.ofReal
            (shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2)) x := by
    intro x
    rw [shellStepSq,
      ENNReal.ofReal_sum_of_nonneg
        (fun _R _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) x)]
    exact Finset.sum_congr rfl fun _R _ => ofReal_indicator_const x
  calc ∫⁻ x, ENNReal.ofReal (shellStepSq r l omega x) ∂(normalizedCubeMeasure Q)
      = ∑ R ∈ largeCubeSubcubes d r l,
          ∫⁻ x, Set.indicator (subcubeSlab r R)
            (fun _ => ENNReal.ofReal
              (shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2)) x
            ∂(normalizedCubeMeasure Q) := by
        rw [lintegral_congr hpoint]
        exact lintegral_finsetSum _ hmeas
    _ ≤ ∑ R ∈ largeCubeSubcubes d r l,
          ENNReal.ofReal
            (shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) *
            ENNReal.ofReal rho := by
        refine Finset.sum_le_sum fun R _ => ?_
        rw [lintegral_indicator (measurableSet_subcubeSlab r R), setLIntegral_const]
        exact mul_le_mul_right (hslab R) _
    _ = ENNReal.ofReal
          (rho * ∑ R ∈ largeCubeSubcubes d r l,
            shellPairEnvelope (r + 1) (cubeCenter R) (cubeCenter R) omega ^ 2) := by
        rw [← Finset.sum_mul,
          ← ENNReal.ofReal_sum_of_nonneg (fun _R _ => sq_nonneg _),
          ← ENNReal.ofReal_mul (Finset.sum_nonneg fun _R _ => sq_nonneg _),
          mul_comm]

/-! ## The pointwise majorant of the Gagliardo kernel -/

/-- The Gagliardo measure of a cube is carried by the product of the cube with
itself, so a bound valid on the cube holds almost everywhere for it. -/
theorem ae_mem_cubeSet_prod (Q : TriadicCube d) :
    ∀ᵐ z : Vec d × Vec d ∂(Gagliardo.gagliardoCubeMeasure Q),
      z.1 ∈ cubeSet Q ∧ z.2 ∈ cubeSet Q := by
  have : SFinite (cubeMeasure Q) := by rw [cubeMeasure]; infer_instance
  have hmeasS : MeasurableSet (cubeSet Q ×ˢ cubeSet Q) :=
    (measurableSet_cubeSet Q).prod (measurableSet_cubeSet Q)
  have hrestr : Gagliardo.gagliardoCubeMeasure Q
      = ENNReal.ofReal (cubeVolume Q)⁻¹ •
        ((volume.prod volume).restrict (cubeSet Q ×ˢ cubeSet Q)) := by
    rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
      Measure.prod_smul_left, Measure.prod_restrict]
  rw [hrestr]
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_restrict_mem hmeasS] with z hz
  exact ⟨hz.1, hz.2⟩

theorem measurable_radialIntegrand_sub (dim : ℕ) (s a b : ℝ) :
    Measurable fun z : Vec dim × Vec dim => radialIntegrand dim s a b (z.1 - z.2) := by
  show Measurable fun z : Vec dim × Vec dim =>
    ENNReal.ofReal
      (min a (b * ‖z.1 - z.2‖) ^ 2 * ‖z.1 - z.2‖ ^ (-(2 * s + (dim : ℝ))))
  fun_prop

theorem radialIntegrand_comm (dim : ℕ) (s a b : ℝ) (x y : Vec dim) :
    radialIntegrand dim s a b (x - y) = radialIntegrand dim s a b (y - x) := by
  show ENNReal.ofReal
      (min a (b * ‖x - y‖) ^ 2 * ‖x - y‖ ^ (-(2 * s + (dim : ℝ))))
    = ENNReal.ofReal
      (min a (b * ‖y - x‖) ^ 2 * ‖y - x‖ ^ (-(2 * s + (dim : ℝ))))
  rw [norm_sub_rev]

private theorem rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast t 2]
  norm_num

/-- **The pointwise majorant of the Gagliardo kernel of one shell.** At every
pair of points of the large cube the squared kernel is dominated by the step
majorant times the radial integrand of `IncrementHsClause` at the amplitudes
`a = 1` and `b = 2 (d+1) 3^{−r}`. The amplitude `b` carries the factor `d + 1`
because `Vec d` has the ambient sup norm while the kernel is written with
`euclideanDist`. -/
theorem enorm_euclideanGagliardoKernel_shell_sq_le {r l : ℕ} (hrl : r ≤ l)
    {s : ℝ} (hs : 0 < s) (omega : ShellSeq d) {z : Vec d × Vec d}
    (hz1 : z.1 ∈ cubeSet (originCube d (l : ℤ)))
    (hz2 : z.2 ∈ cubeSet (originCube d (l : ℤ))) :
    ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 * (shellStepSq r l omega z.1 + shellStepSq r l omega z.2)) *
        radialIntegrand d s 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹) (z.1 - z.2) := by
  have hbpos : (0 : ℝ) < 2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ := by positivity
  have hgx := shellStepSq_nonneg r l omega z.1
  have hgy := shellStepSq_nonneg r l omega z.2
  have hcoef : (0 : ℝ) ≤ 2 * (shellStepSq r l omega z.1 + shellStepSq r l omega z.2) := by
    linarith only [hgx, hgy]
  have hexp : -(2 * s + (d : ℝ)) ≤ 0 := by
    have : (0 : ℝ) ≤ 2 * s + (d : ℝ) := by positivity
    linarith only [this]
  have hexpne : -(2 * s + (d : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * s + (d : ℝ) := by positivity
    exact ne_of_lt (by linarith only [hpos])
  have hker0 : (0 : ℝ) ≤
      min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist z.1 z.2) :=
    le_min zero_le_one
      (mul_nonneg (by positivity) (euclideanDist_nonneg z.1 z.2))
  -- the real-valued majorant
  have hreal : ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ ^ (2 : ℝ) ≤
      2 * (shellStepSq r l omega z.1 + shellStepSq r l omega z.2) *
        (min 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ * ‖z.1 - z.2‖) ^ 2 *
          ‖z.1 - z.2‖ ^ (-(2 * s + (d : ℝ)))) := by
    have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
    have hnormK : ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ =
        euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2)) *
          matrixOperatorNorm ((omega (r + 1)) z.1 - (omega (r + 1)) z.2) := by
      rw [norm_euclideanGagliardoKernel, h2, matrixOperatorNorm_eq_l2_opNorm]
    have hsplit : ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ ^ (2 : ℝ) =
        euclideanDist z.1 z.2 ^ (-(2 * s + (d : ℝ))) *
          matrixOperatorNorm ((omega (r + 1)) z.1 - (omega (r + 1)) z.2) ^ 2 := by
      rw [hnormK, rpow_two_eq_sq, mul_pow, ← Real.rpow_natCast
        (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2))) 2,
        ← Real.rpow_mul (euclideanDist_nonneg z.1 z.2)]
      congr 2
      push_cast
      ring
    rw [hsplit]
    have hNsq := sq_matrixOperatorNorm_shell_sub_le_shellStepSq hrl omega hz1 hz2
    have hkerle : min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist z.1 z.2) ≤
        min 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ * ‖z.1 - z.2‖) := by
      refine min_le_min le_rfl ?_
      have hed : euclideanDist z.1 z.2 ≤ ((d : ℝ) + 1) * ‖z.1 - z.2‖ := by
        have h1 := euclideanDist_le_dimension_mul_dist z.1 z.2
        rw [dist_eq_norm] at h1
        have h2' : (0 : ℝ) ≤ ‖z.1 - z.2‖ := norm_nonneg _
        nlinarith only [h1, h2']
      have hmul : 2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist z.1 z.2 ≤
          2 * ((3 : ℝ) ^ r)⁻¹ * (((d : ℝ) + 1) * ‖z.1 - z.2‖) :=
        mul_le_mul_of_nonneg_left hed (by positivity)
      calc 2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist z.1 z.2
          ≤ 2 * ((3 : ℝ) ^ r)⁻¹ * (((d : ℝ) + 1) * ‖z.1 - z.2‖) := hmul
        _ = 2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ * ‖z.1 - z.2‖ := by ring
    have hkersq : min 1 (2 * ((3 : ℝ) ^ r)⁻¹ * euclideanDist z.1 z.2) ^ 2 ≤
        min 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ * ‖z.1 - z.2‖) ^ 2 :=
      pow_le_pow_left₀ hker0 hkerle 2
    have hNbound : matrixOperatorNorm
          ((omega (r + 1)) z.1 - (omega (r + 1)) z.2) ^ 2 ≤
        2 * (shellStepSq r l omega z.1 + shellStepSq r l omega z.2) *
          min 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ * ‖z.1 - z.2‖) ^ 2 :=
      hNsq.trans (mul_le_mul_of_nonneg_left hkersq hcoef)
    rcases eq_or_lt_of_le (norm_nonneg (z.1 - z.2)) with hzero | hpos
    · have hxy : z.1 - z.2 = 0 := by
        rw [← norm_eq_zero]
        exact hzero.symm
      have hsub : (omega (r + 1)) z.1 - (omega (r + 1)) z.2 = 0 := by
        have : z.1 = z.2 := by
          have := sub_eq_zero.mp hxy
          exact this
        rw [this, sub_self]
      rw [hsub]
      have hN0 : matrixOperatorNorm (0 : Mat d) = 0 := by
        rw [matrixOperatorNorm_eq_l2_opNorm, norm_zero]
      rw [hN0]
      have hzero' : ‖z.1 - z.2‖ = 0 := hzero.symm
      rw [hzero', Real.zero_rpow hexpne]
      norm_num
    · have hle : ‖z.1 - z.2‖ ≤ euclideanDist z.1 z.2 := by
        simpa only [dist_eq_norm] using dist_le_euclideanDist z.1 z.2
      have hpow : euclideanDist z.1 z.2 ^ (-(2 * s + (d : ℝ))) ≤
          ‖z.1 - z.2‖ ^ (-(2 * s + (d : ℝ))) :=
        Real.rpow_le_rpow_of_nonpos hpos hle hexp
      have hNnn : (0 : ℝ) ≤ matrixOperatorNorm
          ((omega (r + 1)) z.1 - (omega (r + 1)) z.2) ^ 2 := sq_nonneg _
      have hstep : euclideanDist z.1 z.2 ^ (-(2 * s + (d : ℝ))) *
            matrixOperatorNorm ((omega (r + 1)) z.1 - (omega (r + 1)) z.2) ^ 2 ≤
          ‖z.1 - z.2‖ ^ (-(2 * s + (d : ℝ))) *
            (2 * (shellStepSq r l omega z.1 + shellStepSq r l omega z.2) *
              min 1 (2 * ((d : ℝ) + 1) * ((3 : ℝ) ^ r)⁻¹ * ‖z.1 - z.2‖) ^ 2) :=
        mul_le_mul hpow hNbound hNnn (Real.rpow_nonneg (norm_nonneg _) _)
      refine hstep.trans (le_of_eq ?_)
      ring
  have henorm : ‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal
          (‖euclideanGagliardoKernel s 2 (fun x => (omega (r + 1)) x) z‖ ^ (2 : ℝ)) := by
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  rw [henorm]
  show ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul hcoef]
  exact ENNReal.ofReal_le_ofReal hreal

end

end SuperdiffusionCLT.Section2.Estimates.Stream
