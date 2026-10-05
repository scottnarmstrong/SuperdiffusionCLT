/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeC
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsD

/-!
# The displacement tail of the kernel at shifts at most one

The localized tail of the rough split (`CrudeMomentsLargeC`) bounds the normalized `mu`-potential of
the complement of a ball, for every shift `mu ≤ 1`, about every centre `x` with `|x| ≤ θ ρ`.  Through
the identification of the kernel resolvent with the analytic minimal resolvent this is a bound for
the potential of the kernel.  At the origin the displacement tail follows from the displacement-tail
lemma, the far points `y` with `|y| ≥ 10 r` being covered by the same bound at the centre `y` and the
radius `|y| - 2 r`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set Filter
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

/-- The decay constant of the displacement tail, depending on the data of the field only through
the dimension, `nu`, `c0` and the exponent `n`. -/
def crudeMomL_kap (d : ℕ) [NeZero d] (nu c0 : ℝ) (n : ℕ) : ℝ :=
  crudeMomL_kappa n (crudeMomL_Lam1 nu c0 n) (crudeMomL_r1 d nu)

/-- The cutting constant of the displacement tail. -/
def crudeMomL_cut (d : ℕ) [NeZero d] (nu c0 amp : ℝ) (n : ℕ) : ℝ :=
  crudeMomL_W0 d n (crudeMomL_Cc d nu) (crudeMomL_Lam1 nu c0 n) (crudeMomL_r1 d nu)
    ((1 + 2 * (d : ℝ)) / amp)

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

theorem crudeMomL_kap_pos {nu c0 : ℝ} (hnu : 0 < nu) (hc0 : 0 ≤ c0) (n : ℕ) :
    0 < crudeMomL_kap d nu c0 n :=
  crudeMomL_kappa_pos n (crudeMomL_Lam1_pos hnu hc0 n) (crudeMomL_r1_pos hnu)

theorem one_le_crudeMomL_cut (nu c0 amp : ℝ) (n : ℕ) : 1 ≤ crudeMomL_cut d nu c0 amp n :=
  crudeMomL_one_le_W0 _ _ _ _ _ _

omit [NeZero d] in
private theorem crudeMomL_measurable_indicator (x : Vec d) (r : ℝ) :
    Measurable fun z ↦ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet.compl

omit [NeZero d] in
private theorem crudeMomL_indicator_nonneg (x : Vec d) (r : ℝ) (z : Vec d) :
    0 ≤ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem crudeMomL_abs_indicator_le (x : Vec d) (r : ℝ) (z : Vec d) :
    |(Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z| ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem crudeMomL_ofReal_indicator (x : Vec d) (r : ℝ) :
    (fun z ↦ ENNReal.ofReal
      ((Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z)) =
      (Metric.ball x r)ᶜ.indicator (1 : Vec d → ℝ≥0∞) := by
  funext z
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> norm_num

/-- **The resolvent tail of the kernel at every shift `mu ≤ 1`.**  The normalized `mu`-potential of
the complement of the sup-metric ball of radius `ρ` about `x`, where `|x| ≤ θ ρ` and
`sqrt mu * ρ ≥ 1`, is at most the absorbed expression. -/
theorem RoughLogBounds.crudeMomL_liveTail (Rb : RoughLogBounds Sp)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (mu : PositiveShift) (hmu1 : (mu : ℝ) ≤ 1) (x : Vec d) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 ≤ θ)
    (hx : euclideanNorm x ≤ θ * ρ) (hs : 1 ≤ Real.sqrt (mu : ℝ) * ρ) :
    ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x ρ)ᶜ ≤
      ENNReal.ofReal (crudeMomL_phi d Rb.n (crudeMomL_Cc d A.nu)
        (crudeMomL_Lam1 A.nu Rb.c0 Rb.n) (crudeMomL_r1 d A.nu) ((1 + θ) / Rb.amp)
        (crudeMomL_ell Rb.Kc θ (mu : ℝ)⁻¹) (mu : ℝ)⁻¹ (Real.sqrt (mu : ℝ) * ρ)) := by
  let f : Vec d → ℝ := fun z ↦ (Metric.ball x ρ)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z
  have hf : Measurable f := crudeMomL_measurable_indicator x ρ
  have hf0 : ∀ z, 0 ≤ f z := crudeMomL_indicator_nonneg x ρ
  have hf1 : ∀ z, |f z| ≤ 1 := crudeMomL_abs_indicator_le x ρ
  have hzero : ∀ z ∈ euclideanBall x ρ, f z = 0 := by
    intro z hz
    dsimp only [f]
    rw [Set.indicator_of_notMem]
    exact fun hzcompl ↦ hzcompl (Homogenization.euclideanBall_subset_metricBall hρ hz)
  have htail := A.mul_toReal_analyticMinimalResolvent_le_localizedTail Sp mu hf hf0 hf1 hρ hzero
  have hdom := Rb.crudeMomL_tail_le mu hmu1 x hρ hθ hx hs
  have hreal := htail.trans hdom
  have hfinite := A.analyticMinimalResolvent_ne_top mu hf hf0 (by norm_num : (0 : ℝ) ≤ 1) hf1 x
  have hset : R.kernelSemigroup.kernelResolvent (mu : ℝ)
      ((Metric.ball x ρ)ᶜ.indicator 1) x =
      R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x ρ)ᶜ := by
    rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
      (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl) x,
      lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]
  rw [← hset, ← crudeMomL_ofReal_indicator x ρ, hid mu hf hf0 hf1 x]
  rw [← ENNReal.ofReal_toReal hfinite, ← ENNReal.ofReal_mul mu.property.le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **The displacement tail at the origin, at every time `t ≥ 1`.**  Above the cutting radius the
transition law at time `t = 1 / mu` started at the origin leaves the ball of radius `11 r` with
probability at most `2 e` times a stretched exponential of the dimensionless radius. -/
theorem RoughLogBounds.crudeMomL_tail_at_origin (Rb : RoughLogBounds Sp)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (mu : PositiveShift) (hmu1 : (mu : ℝ) ≤ 1) {t : ℝ≥0} (ht : (mu : ℝ) * (t : ℝ) = 1)
    {r : ℝ} (hr : 0 < r)
    (hrs : (crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n *
        crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (mu : ℝ)⁻¹) ^ (2 * Rb.n) ≤ Real.sqrt (mu : ℝ) * r) :
    R.kernelSemigroup t 0 (Metric.ball (0 : Vec d) (11 * r))ᶜ ≤
      ENNReal.ofReal (2 * Real.exp 1 *
        Real.exp (-(crudeMomL_kap d A.nu Rb.c0 Rb.n * Real.sqrt (Real.sqrt (mu : ℝ) * r)))) := by
  have hμ : 0 < (mu : ℝ) := mu.property
  have hsm : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 hμ
  have hμi : 1 ≤ (mu : ℝ)⁻¹ := by rw [one_le_inv₀ hμ]; exact hmu1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hθ : (0 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [hd0]
  obtain ⟨hℓ1, hℓt⟩ := crudeMomL_ell_ge Rb.two_le_Kc hθ hμi
  have habs := crudeMomL_absorb d Rb.n Rb.two_le_n (crudeMomL_Cc_nonneg (d := d) A.hnu)
    (crudeMomL_Lam1_pos A.hnu Rb.c0_nonneg Rb.n) (crudeMomL_r1_pos (d := d) A.hnu)
    (show 0 < (1 + 2 * (d : ℝ)) / Rb.amp from div_pos (by linarith only [hd0]) Rb.amp_pos)
  have hcut1 : 1 ≤ crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n := one_le_crudeMomL_cut _ _ _ _
  have hone : 1 ≤ (crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n *
      crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (mu : ℝ)⁻¹) ^ (2 * Rb.n) :=
    one_le_pow₀ (by nlinarith only [hcut1, hℓ1])
  have hkey : ∀ y : Vec d, ∀ ρ : ℝ, 0 < ρ → euclideanNorm y ≤ 2 * (d : ℝ) * ρ →
      r ≤ ρ → ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball y ρ)ᶜ ≤
        ENNReal.ofReal (Real.exp (-(crudeMomL_kap d A.nu Rb.c0 Rb.n *
          Real.sqrt (Real.sqrt (mu : ℝ) * ρ)))) := by
    intro y ρ hρ hy hrρ
    have hsρ : Real.sqrt (mu : ℝ) * r ≤ Real.sqrt (mu : ℝ) * ρ :=
      mul_le_mul_of_nonneg_left hrρ hsm.le
    have hlow := hrs.trans hsρ
    have hs1 : 1 ≤ Real.sqrt (mu : ℝ) * ρ := hone.trans hlow
    refine (Rb.crudeMomL_liveTail R hid mu hmu1 y hρ hθ hy hs1).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact (habs _ _ _ hℓ1 hμi hℓt hlow).1
  have hcentre := hkey 0 r hr (by simp [euclideanNorm, vecNormSq, vecDot]; positivity) le_rfl
  have hphi0 : 0 ≤ Real.exp (-(crudeMomL_kap d A.nu Rb.c0 Rb.n *
      Real.sqrt (Real.sqrt (mu : ℝ) * r))) := (Real.exp_pos _).le
  refine crudeMom_measure_compl_ball_le R hcons ht 0 hr hphi0 hcentre ?_
  intro y hy
  rw [dist_zero_right] at hy
  set ρ : ℝ := ‖y‖ - 2 * r with hρdef
  have hρr : 8 * r ≤ ρ := by linarith only [hy]
  have hρ0 : 0 < ρ := by linarith only [hρr, hr]
  have hyρ : ‖y‖ ≤ 5 / 4 * ρ := by linarith only [hy, hρdef]
  have heu : euclideanNorm y ≤ 2 * (d : ℝ) * ρ := by
    calc euclideanNorm y ≤ (d : ℝ) * ‖y‖ := euclideanNorm_le_dimension_mul_norm y
      _ ≤ (d : ℝ) * (5 / 4 * ρ) := mul_le_mul_of_nonneg_left hyρ hd0
      _ ≤ 2 * (d : ℝ) * ρ := by nlinarith only [hd0, hρ0, mul_nonneg hd0 hρ0.le]
  have hfar := hkey y ρ hρ0 heu (by linarith only [hρr, hr])
  have hsρ : Real.sqrt (mu : ℝ) * r ≤ Real.sqrt (mu : ℝ) * ρ :=
    mul_le_mul_of_nonneg_left (by linarith only [hρr, hr]) hsm.le
  have hhalf := (habs _ _ _ hℓ1 hμi hℓt (hrs.trans hsρ)).2
  have hsub : Metric.ball (0 : Vec d) (2 * r) ⊆ (Metric.ball y ρ)ᶜ := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right, Set.mem_compl_iff, not_lt] at hz ⊢
    have h1 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
    rw [dist_comm, dist_eq_norm]
    linarith only [h1, hz, hρdef]
  calc ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball (0 : Vec d) (2 * r))
      ≤ ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball y ρ)ᶜ := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (-(crudeMomL_kap d A.nu Rb.c0 Rb.n *
          Real.sqrt (Real.sqrt (mu : ℝ) * ρ)))) := hfar
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hhalf

end

end SuperdiffusionCLT.Section8
