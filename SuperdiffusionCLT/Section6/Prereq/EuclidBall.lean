/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Euclidean balls in `Vec d`

`Vec d = Fin d → ℝ` carries the sup norm, so `Metric.ball` is a cube. The Euclidean ball is
therefore defined through `Homogenization.vecNormSq`.

## Main definitions

* `euclidBall r`: the open Euclidean ball of radius `r` about the origin.
* `ballMeasure r`: Lebesgue measure conditioned on `euclidBall r` (normalized).

## Main results

* `measurableSet_euclidBall`, `euclidBall_mono`
* `euclidBall_subset_ball`: `euclidBall r ⊆ Metric.ball 0 r` (the cube of half-side `r`)
* `ball_subset_euclidBall`: `Metric.ball 0 r ⊆ euclidBall (√d * r)`
* `volume_euclidBall_pos`, `volume_euclidBall_lt_top`
* `isProbabilityMeasure_ballMeasure`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory Homogenization

variable {d : ℕ}

/-- The open Euclidean ball of radius `r` about the origin of `Vec d`. -/
def euclidBall (r : ℝ) : Set (Vec d) := {x | vecNormSq x < r ^ 2}

/-- Lebesgue measure on `Vec d` conditioned on the Euclidean ball of radius `r`. -/
noncomputable def ballMeasure (r : ℝ) : Measure (Vec d) :=
  ProbabilityTheory.cond volume (euclidBall r)

theorem mem_euclidBall {r : ℝ} {x : Vec d} : x ∈ euclidBall r ↔ vecNormSq x < r ^ 2 :=
  Iff.rfl

theorem continuous_vecNormSq : Continuous (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  fun_prop

theorem isOpen_euclidBall (r : ℝ) : IsOpen (euclidBall (d := d) r) :=
  isOpen_lt continuous_vecNormSq continuous_const

theorem measurableSet_euclidBall (r : ℝ) : MeasurableSet (euclidBall (d := d) r) :=
  (isOpen_euclidBall r).measurableSet

theorem euclidBall_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    euclidBall (d := d) r ⊆ euclidBall s := by
  intro x hx
  exact lt_of_lt_of_le hx (pow_le_pow_left₀ hr hrs 2)

theorem zero_mem_euclidBall {r : ℝ} (hr : 0 < r) : (0 : Vec d) ∈ euclidBall r := by
  simp [euclidBall, vecNormSq, vecDot, hr]

theorem euclidBall_nonempty {r : ℝ} (hr : 0 < r) : (euclidBall (d := d) r).Nonempty :=
  ⟨0, zero_mem_euclidBall hr⟩

/-- The Euclidean ball lies in the cube of half-side `r`. -/
theorem euclidBall_subset_ball {r : ℝ} (hr : 0 < r) :
    euclidBall (d := d) r ⊆ Metric.ball (0 : Vec d) r := by
  intro x hx
  rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt (sq_apply_le_vecNormSq x i) hx) hr.le

/-- The cube of half-side `r` lies in the Euclidean ball of radius `√d * r`. -/
theorem ball_subset_euclidBall [NeZero d] {r : ℝ} :
    Metric.ball (0 : Vec d) r ⊆ euclidBall (Real.sqrt d * r) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have hxi : ∀ i, x i ^ 2 < r ^ 2 := by
    intro i
    have hi : |x i| < r := by
      simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans_lt hx
    exact sq_lt_sq' (abs_lt.1 hi).1 (abs_lt.1 hi).2
  have hsum : vecNormSq x < (d : ℝ) * r ^ 2 := by
    unfold vecNormSq vecDot
    have h1 : ∑ i, x i * x i < ∑ _i : Fin d, r ^ 2 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ => by simpa [pow_two] using hxi i)
    simpa using h1
  rw [mem_euclidBall, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  exact hsum

theorem volume_euclidBall_lt_top {r : ℝ} (hr : 0 < r) :
    volume (euclidBall (d := d) r) < ⊤ :=
  lt_of_le_of_lt (measure_mono (euclidBall_subset_ball hr))
    Metric.isBounded_ball.measure_lt_top

theorem volume_euclidBall_ne_top {r : ℝ} (hr : 0 < r) :
    volume (euclidBall (d := d) r) ≠ ⊤ :=
  (volume_euclidBall_lt_top hr).ne

theorem volume_euclidBall_pos [NeZero d] {r : ℝ} (hr : 0 < r) :
    0 < volume (euclidBall (d := d) r) := by
  have hpos : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
  have h : Metric.ball (0 : Vec d) (r / Real.sqrt d) ⊆ euclidBall r := by
    refine (ball_subset_euclidBall).trans ?_
    rw [mul_div_cancel₀ _ hpos.ne']
  exact lt_of_lt_of_le (Metric.measure_ball_pos _ _ (div_pos hr hpos)) (measure_mono h)

theorem volume_euclidBall_ne_zero [NeZero d] {r : ℝ} (hr : 0 < r) :
    volume (euclidBall (d := d) r) ≠ 0 :=
  (volume_euclidBall_pos hr).ne'

theorem isProbabilityMeasure_ballMeasure [NeZero d] {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (ballMeasure (d := d) r) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (volume_euclidBall_ne_zero hr)
    (volume_euclidBall_ne_top hr)

theorem ballMeasure_apply {r : ℝ} (s : Set (Vec d)) :
    ballMeasure r s = (volume (euclidBall (d := d) r))⁻¹ * volume (euclidBall r ∩ s) := by
  unfold ballMeasure
  rw [ProbabilityTheory.cond_apply (measurableSet_euclidBall r)]

theorem ballMeasure_absolutelyContinuous (r : ℝ) :
    ballMeasure (d := d) r ≪ volume :=
  ProbabilityTheory.cond_absolutelyContinuous

/-- Witness: the unit ball in dimension two is a nonempty, positive-volume, finite-volume set
carrying a probability measure. -/
example : (0 < volume (euclidBall (d := 2) 1)) ∧ (volume (euclidBall (d := 2) 1) < ⊤) ∧
    IsProbabilityMeasure (ballMeasure (d := 2) 1) :=
  ⟨volume_euclidBall_pos one_pos, volume_euclidBall_lt_top one_pos,
    isProbabilityMeasure_ballMeasure one_pos⟩

end SuperdiffusionCLT.Section6
