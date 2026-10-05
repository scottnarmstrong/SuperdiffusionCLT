/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedH

/-!
# Poincare inequalities: the affine inequality

`Section7.a10_affine_L2_lower`: an affine function that approximates `u` in `L²(W)` at least as well
as a constant has slope controlled by the `L²` oscillation of `u`, for any `W` containing a cube.
The proof reflects the cube in the coordinate of largest slope (the cross term cancels) and bounds
the second moment of that coordinate from below on a slab of the cube.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The reflection of the `i`-th coordinate about `c i`. -/
def a10_reflect (c : Vec d) (i : Fin d) (y : Vec d) : Vec d :=
  fun j => if j = i then 2 * c i - y j else y j

theorem a10_reflect_invol (c : Vec d) (i : Fin d) : Function.Involutive (a10_reflect c i) := by
  intro y
  ext j
  by_cases hj : j = i
  · subst hj; simp [a10_reflect]
  · simp [a10_reflect, hj]

theorem a10_reflect_measurable (c : Vec d) (i : Fin d) : Measurable (a10_reflect c i) := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : j = i
  · subst hj
    simp only [a10_reflect, ite_true]
    exact measurable_const.sub (measurable_pi_apply _)
  · simp only [a10_reflect, hj, ite_false]
    exact measurable_pi_apply _

theorem a10_reflect_mp (c : Vec d) (i : Fin d) :
    MeasurePreserving (a10_reflect c i) volume volume := by
  have := volume_preserving_pi (α' := fun _ : Fin d => ℝ) (β' := fun _ : Fin d => ℝ)
    (f := fun j t => if j = i then 2 * c i - t else t) (fun j => by
      by_cases hj : j = i
      · simp only [hj, ite_true]
        exact (volume : Measure ℝ).measurePreserving_sub_left (2 * c i)
      · simp only [hj, ite_false]
        exact MeasurePreserving.id _)
  exact this

theorem a10_reflect_norm (c : Vec d) (i : Fin d) (y : Vec d) :
    ‖a10_reflect c i y - c‖ = ‖y - c‖ := by
  have h : ∀ j, |a10_reflect c i y j - c j| = |y j - c j| := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [a10_reflect, ite_true]
      rw [show 2 * c j - y j - c j = -(y j - c j) by ring, abs_neg]
    · simp [a10_reflect, hj]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, h j]
    simpa using norm_le_pi_norm (y - c) j
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, ← h j]
    simpa using norm_le_pi_norm (a10_reflect c i y - c) j

theorem a10_reflect_ball (c : Vec d) (i : Fin d) (s : ℝ) :
    a10_reflect c i ⁻¹' Metric.ball c s = Metric.ball c s := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, a10_reflect_norm]

theorem a10_reflect_lintegral {c : Vec d} (i : Fin d) (s : ℝ) (g : Vec d → ENNReal) :
    ∫⁻ y in Metric.ball c s, g (a10_reflect c i y) = ∫⁻ y in Metric.ball c s, g y := by
  let e : Vec d ≃ᵐ Vec d :=
    ⟨Function.Involutive.toPerm _ (a10_reflect_invol c i), a10_reflect_measurable c i,
      a10_reflect_measurable c i⟩
  have hemb : MeasurableEmbedding (a10_reflect c i) := e.measurableEmbedding
  have := (a10_reflect_mp c i).setLIntegral_comp_preimage_emb hemb g (Metric.ball c s)
  rwa [a10_reflect_ball] at this

theorem a10_reflect_sub (c : Vec d) (i : Fin d) (y : Vec d) :
    a10_reflect c i y - c = (y - c) - (2 * (y i - c i)) • basisVec i := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [a10_reflect, ite_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
    ring
  · simp [a10_reflect, hj]

theorem a10_reflect_vecDot (c : Vec d) (i : Fin d) (b y : Vec d) :
    vecDot b (a10_reflect c i y - c) = vecDot b (y - c) - 2 * (y i - c i) * b i := by
  rw [a10_reflect_sub, g1b_vecDot_sub_smul_right, vecDot_basisVec_right]

theorem a10_slab_volume {c : Vec d} {s : ℝ} (hs : 0 < s) (i : Fin d) :
    volume (Metric.ball c s ∩ {y | c i + s / 2 ≤ y i}) =
      ENNReal.ofReal (1 / 4) * volume (Metric.ball c s) := by
  have hset : Metric.ball c s ∩ {y | c i + s / 2 ≤ y i} =
      Set.pi univ (fun j => if j = i then Set.Ico (c i + s / 2) (c i + s) else
        Set.Ioo (c j - s) (c j + s)) := by
    ext y
    simp only [Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ j
      have hj := (pi_norm_lt_iff (by positivity)).1 h1 j
      rw [Real.norm_eq_abs, Pi.sub_apply, abs_lt] at hj
      by_cases hji : j = i
      · subst hji
        simp only [ite_true, Set.mem_Ico]
        exact ⟨h2, by linarith only [hj.2]⟩
      · simp only [hji, ite_false, Set.mem_Ioo]
        constructor <;> linarith only [hj.1, hj.2]
    · intro h
      have key : ∀ j, c j - s < y j ∧ y j < c j + s ∧ (j = i → c i + s / 2 ≤ y i) := by
        intro j
        by_cases hji : j = i
        · subst hji
          have := h j
          simp only [ite_true, Set.mem_Ico] at this
          exact ⟨by linarith only [this.1, hs], this.2, fun _ => this.1⟩
        · have := h j
          simp only [hji, ite_false, Set.mem_Ioo] at this
          exact ⟨this.1, this.2, fun h' => absurd h' hji⟩
      refine ⟨(pi_norm_lt_iff hs).2 fun j => ?_, (key i).2.2 rfl⟩
      rw [Real.norm_eq_abs, Pi.sub_apply, abs_lt]
      constructor <;> linarith only [(key j).1, (key j).2.1]
  have hb := Real.volume_pi_ball c hs
  rw [hset, hb, volume_pi, Measure.pi_pi]
  have hA : ∀ j : Fin d, volume (if j = i then Set.Ico (c i + s / 2) (c i + s) else
      Set.Ioo (c j - s) (c j + s)) =
      ENNReal.ofReal (2 * s) * (if j = i then ENNReal.ofReal (1 / 4) else 1) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [ite_true, Real.volume_Ico]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · simp only [hji, ite_false, Real.volume_Ioo, mul_one]
      congr 1
      ring
  simp only [hA]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [mul_comm]
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ s * 2)]

theorem a10_cube_affine_lower {c : Vec d} {s : ℝ} (hs : 0 < s) (i : Fin d) (a : ℝ) (b : Vec d) :
    ENNReal.ofReal (b i ^ 2 * s ^ 2 / 16) * volume (Metric.ball c s) ≤
      ∫⁻ y in Metric.ball c s, ENNReal.ofReal ((a + vecDot b (y - c)) ^ 2) := by
  have hBm : MeasurableSet (Metric.ball c s) := Metric.isOpen_ball.measurableSet
  have hdotm : Measurable fun y : Vec d => vecDot b (y - c) := by
    unfold vecDot
    exact Finset.measurable_sum _ fun j _ => (measurable_const.mul
      ((measurable_pi_apply j).sub measurable_const))
  set G : Vec d → ENNReal := fun y => ENNReal.ofReal ((a + vecDot b (y - c)) ^ 2) with hG
  have hGm : Measurable G :=
    ENNReal.measurable_ofReal.comp ((measurable_const.add hdotm).pow_const 2)
  set X : ENNReal := ∫⁻ y in Metric.ball c s, G y with hX
  have hY : ∫⁻ y in Metric.ball c s, G (a10_reflect c i y) = X := a10_reflect_lintegral i s G
  have hpt : ∀ y : Vec d, ENNReal.ofReal (2 * (b i ^ 2 * (y i - c i) ^ 2)) ≤
      G y + G (a10_reflect c i y) := by
    intro y
    simp only [hG, a10_reflect_vecDot]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith only [sq_nonneg (a + vecDot b (y - c) - (y i - c i) * b i)]
  have h2X : ∫⁻ y in Metric.ball c s, ENNReal.ofReal (2 * (b i ^ 2 * (y i - c i) ^ 2)) ≤ X + X := by
    calc ∫⁻ y in Metric.ball c s, ENNReal.ofReal (2 * (b i ^ 2 * (y i - c i) ^ 2))
        ≤ ∫⁻ y in Metric.ball c s, (G y + G (a10_reflect c i y)) := lintegral_mono hpt
      _ = X + X := by
          rw [lintegral_add_left hGm, hY]
  set T : Set (Vec d) := Metric.ball c s ∩ {y | c i + s / 2 ≤ y i} with hT
  have hTm : MeasurableSet T :=
    hBm.inter (measurableSet_le measurable_const (measurable_pi_apply i))
  have hlow : ENNReal.ofReal (b i ^ 2 * s ^ 2 / 2) * volume T ≤
      ∫⁻ y in Metric.ball c s, ENNReal.ofReal (2 * (b i ^ 2 * (y i - c i) ^ 2)) := by
    calc ENNReal.ofReal (b i ^ 2 * s ^ 2 / 2) * volume T
        = ∫⁻ y in T, ENNReal.ofReal (b i ^ 2 * s ^ 2 / 2) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ y in T, ENNReal.ofReal (2 * (b i ^ 2 * (y i - c i) ^ 2)) := by
          refine setLIntegral_mono' hTm fun y hy => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hz : s / 2 ≤ y i - c i := by
            have := hy.2
            simp only [Set.mem_ofPred_eq] at this
            linarith only [this]
          have : (s / 2) ^ 2 ≤ (y i - c i) ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
          nlinarith only [this, sq_nonneg (b i)]
      _ ≤ ∫⁻ y in Metric.ball c s, ENNReal.ofReal (2 * (b i ^ 2 * (y i - c i) ^ 2)) :=
          lintegral_mono_set Set.inter_subset_left
  rw [hT, a10_slab_volume hs i] at hlow
  have hcalc : ENNReal.ofReal (b i ^ 2 * s ^ 2 / 2) * (ENNReal.ofReal (1 / 4) * volume (Metric.ball c s))
      = 2 * (ENNReal.ofReal (b i ^ 2 * s ^ 2 / 16) * volume (Metric.ball c s)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 2
    ring
  have h3 : 2 * (ENNReal.ofReal (b i ^ 2 * s ^ 2 / 16) * volume (Metric.ball c s)) ≤ 2 * X := by
    rw [← hcalc, two_mul X]
    exact hlow.trans h2X
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h3

theorem a10_exists_max_coord (b : Vec d) : ‖b‖ = 0 ∨ ∃ i : Fin d, ‖b‖ = |b i| := by
  by_cases hd : Nonempty (Fin d)
  · obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin d => |b i|)
      (Finset.univ_nonempty_iff.2 hd)
    right
    refine ⟨i, le_antisymm ?_ ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
      rw [Real.norm_eq_abs]
      exact hi j (Finset.mem_univ j)
    · simpa using norm_le_pi_norm b i
  · left
    have : IsEmpty (Fin d) := not_nonempty_iff.1 hd
    rw [norm_eq_zero]
    exact Subsingleton.elim _ _

theorem a10_affine_L2_lower {W : Set (Vec d)} {x0 : Vec d} {s : ℝ} (hs : 0 < s)
    (hBW : Metric.ball x0 s ⊆ W) (a : ℝ) (b : Vec d) :
    ENNReal.ofReal (s * ‖b‖ / 4) * volume (Metric.ball x0 s) ^ (1 / (2 : ℝ)) ≤
      eLpNorm (fun x => a + vecDot b (x - x0)) 2 (volume.restrict W) := by
  rcases a10_exists_max_coord b with h0 | ⟨i, hi⟩
  · rw [h0]
    simp
  have hcont : Continuous fun x : Vec d => a + vecDot b (x - x0) := by
    unfold vecDot
    fun_prop
  have hmono : eLpNorm (fun x => a + vecDot b (x - x0)) 2 (volume.restrict (Metric.ball x0 s)) ≤
      eLpNorm (fun x => a + vecDot b (x - x0)) 2 (volume.restrict W) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hBW le_rfl)
  refine le_trans ?_ hmono
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hcont.aestronglyMeasurable]
  have hE : ∀ x : Vec d, ‖a + vecDot b (x - x0)‖ₑ ^ ((2 : ENNReal).toReal) =
      ENNReal.ofReal ((a + vecDot b (x - x0)) ^ 2) := fun x => by
    rw [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp only [hE]
  have hlow := a10_cube_affine_lower (c := x0) hs i a b
  have h2 : (0 : ℝ) ≤ 1 / (2 : ENNReal).toReal := by norm_num
  calc ENNReal.ofReal (s * ‖b‖ / 4) * volume (Metric.ball x0 s) ^ (1 / (2 : ℝ))
      = (ENNReal.ofReal (b i ^ 2 * s ^ 2 / 16) * volume (Metric.ball x0 s)) ^
          (1 / (2 : ENNReal).toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h2, ENNReal.toReal_ofNat,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        have e : b i ^ 2 * s ^ 2 / 16 = (s * ‖b‖ / 4) ^ 2 := by
          rw [hi, div_pow, mul_pow, sq_abs]
          ring
        rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    _ ≤ _ := ENNReal.rpow_le_rpow hlow h2

end SuperdiffusionCLT.Section7
