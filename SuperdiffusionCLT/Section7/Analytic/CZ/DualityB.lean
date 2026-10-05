/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.Duality

/-!
# The norming lemma

For `1 < p < ∞`, a measurable field `F` on a bounded measurable set `U` of finite positive
measure, tested against bounded measurable `G`: if
`|⨍_U F·G| ≤ M · lpBar U p' G` for all such `G`, then `lpBar U p F ≤ M`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p14_conj {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) :
    p.conjExponent = ENNReal.ofReal (p.toReal / (p.toReal - 1)) := by
  have hP : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hpt).2 hp1
    simpa using this
  have hp : p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hpt).symm
  have h1 : p.toReal / (p.toReal - 1) = 1 + (p.toReal - 1)⁻¹ := by
    have : p.toReal - 1 ≠ 0 := by linarith only [hP]
    field_simp
    ring
  rw [h1, ENNReal.ofReal_add (by norm_num) (inv_nonneg.2 (by linarith only [hP])),
    ENNReal.ofReal_inv_of_pos (by linarith only [hP]), ENNReal.ofReal_sub _ (by norm_num)]
  simp only [ENNReal.ofReal_one, ENNReal.conjExponent]
  rw [← hp]

theorem p14_lpBar_eq {V : Set (Vec d)} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict V)) :
    lpBar V q G = ((volume V)⁻¹ * ∫⁻ x in V, ‖G x‖ₑ ^ q.toReal) ^ (1 / q.toReal) := by
  unfold lpBar
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt (hG.smul_measure _),
    lintegral_smul_measure, smul_eq_mul]

theorem p14_lintegral_T_le {P : ℝ} (hP : 1 < P) {n : ℝ} (hn : 0 ≤ n) (F : Vec d → Vec d)
    (V : Set (Vec d)) :
    ∫⁻ x in V, ENNReal.ofReal (p14_T P n F x) ≤ ENNReal.ofReal (n ^ P) * volume V := by
  have hb : ∀ x, ENNReal.ofReal (p14_T P n F x) ≤ ENNReal.ofReal (n ^ P) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    unfold p14_T
    split_ifs with h
    · exact Real.rpow_le_rpow (norm_nonneg _) h (by linarith only [hP])
    · exact Real.rpow_nonneg hn _
  calc ∫⁻ x in V, ENNReal.ofReal (p14_T P n F x) ≤ ∫⁻ _x in V, ENNReal.ofReal (n ^ P) :=
        lintegral_mono hb
    _ = ENNReal.ofReal (n ^ P) * volume V := by
        rw [setLIntegral_const]

theorem p14_iSup_T {P : ℝ} (hP : 1 < P) (F : Vec d → Vec d) (x : Vec d) :
    ⨆ n : ℕ, ENNReal.ofReal (p14_T P (n : ℝ) F x) = ‖F x‖ₑ ^ P := by
  have hP0 : 0 < P := by linarith only [hP]
  have he : ‖F x‖ₑ ^ P = ENNReal.ofReal (‖F x‖ ^ P) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le]
  rw [he]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    apply ENNReal.ofReal_le_ofReal
    unfold p14_T
    split_ifs
    · exact le_refl _
    · exact Real.rpow_nonneg (norm_nonneg _) _
  · obtain ⟨n, hn⟩ := exists_nat_ge ‖F x‖
    refine le_iSup_of_le n ?_
    unfold p14_T
    simp only [hn, ↓reduceIte, le_refl]

theorem p14_monotone_T {P : ℝ} (F : Vec d → Vec d) (x : Vec d) :
    Monotone fun n : ℕ => ENNReal.ofReal (p14_T P (n : ℝ) F x) := by
  intro m n hmn
  apply ENNReal.ofReal_le_ofReal
  unfold p14_T
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  by_cases h : ‖F x‖ ≤ (m : ℝ)
  · simp only [h, h.trans hmn', ↓reduceIte, le_refl]
  · simp only [h, ↓reduceIte]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_refl _

theorem p14_measurable_vecDot {f g : Vec d → Vec d} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => vecDot (f x) (g x) := by
  unfold vecDot
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

theorem p14_norming_step {U : Set (Vec d)} (h0 : volume U ≠ 0) (hfin : volume U ≠ ∞)
    {P Q : ℝ} (hP : 1 < P) (hQ0 : 0 < Q) (hQ : (P - 1) * Q = P) (hPQ : 1 / P + 1 / Q = 1)
    {F : Vec d → Vec d} (hF : Measurable F) {M : ℝ} (n : ℕ)
    (hdual : ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (p14_G P n F x)| ≤
        ENNReal.ofReal M * lpBar U (ENNReal.ofReal Q) (p14_G P n F)) :
    (volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (p14_T P (n : ℝ) F x) ≤ ENNReal.ofReal M ^ P := by
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hcT : (volume U)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hGm := p14_measurable_G P (n : ℝ) hF
  have hTm := p14_measurable_T P (n : ℝ) hF
  have hdm := p14_measurable_vecDot hF hGm
  have hTint : Integrable (p14_T P (n : ℝ) F) (volume.restrict U) := by
    refine Integrable.of_bound hTm.aestronglyMeasurable ((n : ℝ) ^ P) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (p14_T_nonneg P _ F x)]
    unfold p14_T
    split_ifs with h
    · exact Real.rpow_le_rpow (norm_nonneg _) h (by linarith only [hP])
    · exact Real.rpow_nonneg hn _
  have hdint : Integrable (fun x => vecDot (F x) (p14_G P (n : ℝ) F x)) (volume.restrict U) :=
    Integrable.of_bound hdm.aestronglyMeasurable (d * (n : ℝ) ^ P)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact p14_dot_le hP hn F x)
  have hmono : ∫ x in U, p14_T P (n : ℝ) F x ≤ ∫ x in U, vecDot (F x) (p14_G P (n : ℝ) F x) :=
    integral_mono hTint hdint fun x => p14_T_le_dot hP _ F x
  have hinv : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  have hlow : (volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (p14_T P (n : ℝ) F x) ≤
      ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (p14_G P (n : ℝ) F x)| := by
    have e1 : ENNReal.ofReal ((volume U).toReal⁻¹) = (volume U)⁻¹ := by
      rw [← ENNReal.toReal_inv, ENNReal.ofReal_toReal hcT]
    have e2 : ∫⁻ x in U, ENNReal.ofReal (p14_T P (n : ℝ) F x) =
        ENNReal.ofReal (∫ x in U, p14_T P (n : ℝ) F x) :=
      (ofReal_integral_eq_lintegral_ofReal hTint
        (Filter.Eventually.of_forall fun x => p14_T_nonneg P _ F x)).symm
    rw [e2, ← e1, ← ENNReal.ofReal_mul hinv]
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hmono hinv).trans (le_abs_self _)
  have hQt : ENNReal.ofReal Q ≠ ∞ := ENNReal.ofReal_ne_top
  have hQz : ENNReal.ofReal Q ≠ 0 := by simpa using hQ0
  have hup : lpBar U (ENNReal.ofReal Q) (p14_G P (n : ℝ) F) ≤
      ((volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (p14_T P (n : ℝ) F x)) ^ (1 / Q) := by
    rw [p14_lpBar_eq hQz hQt hGm.aestronglyMeasurable, ENNReal.toReal_ofReal hQ0.le]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    gcongr with x
    exact p14_enorm_G_pow_le hP hQ hQ0 F _ x
  set X := (volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (p14_T P (n : ℝ) F x) with hX
  have hXT : X ≠ ∞ := by
    refine ENNReal.mul_ne_top hcT ?_
    exact ne_of_lt (lt_of_le_of_lt (p14_lintegral_T_le hP hn F U)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top))
  have h1 : X ≤ ENNReal.ofReal M * X ^ (1 / Q) :=
    hlow.trans (hdual.trans (by gcongr))
  by_cases hX0 : X = 0
  · rw [hX0]
    exact zero_le
  · have hP0 : 0 < P := by linarith only [hP]
    have hXQ0 : X ^ (1 / Q) ≠ 0 := by
      intro h
      rw [ENNReal.rpow_eq_zero_iff] at h
      rcases h with h | h
      · exact hX0 h.1
      · exact absurd h.2 (not_lt.2 (by positivity))
    have hXQT : X ^ (1 / Q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hXT
    have h2 : X ^ (1 / P) * X ^ (1 / Q) ≤ ENNReal.ofReal M * X ^ (1 / Q) := by
      rw [← ENNReal.rpow_add _ _ hX0 hXT, hPQ, ENNReal.rpow_one]
      exact h1
    have h3 : X ^ (1 / P) ≤ ENNReal.ofReal M :=
      (ENNReal.mul_le_mul_iff_left hXQ0 hXQT).1 h2
    calc X = (X ^ (1 / P)) ^ P := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hP0.ne', ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal M ^ P := ENNReal.rpow_le_rpow h3 hP0.le

/-- **Norming lemma** (measurable field). If `|⨍_U F·G| ≤ M · lpBar U p' G` for every bounded
measurable `G`, then `lpBar U p F ≤ M`; the constant is `1` for the sup norm on `Vec d`. -/
theorem p14_norming_measurable {U : Set (Vec d)} (h0 : volume U ≠ 0) (hfin : volume U ≠ ∞)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) {F : Vec d → Vec d} (hF : Measurable F) {M : ℝ}
    (hdual : ∀ G : Vec d → Vec d, Measurable G → (∃ B : ℝ, ∀ x, ‖G x‖ ≤ B) →
      ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (G x)| ≤
        ENNReal.ofReal M * lpBar U p.conjExponent G) :
    lpBar U p F ≤ ENNReal.ofReal M := by
  have hP : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hpt).2 hp1
    simpa using this
  have hP0 : 0 < p.toReal := by linarith only [hP]
  have hP1 : p.toReal - 1 ≠ 0 := by linarith only [hP]
  have hQ0 : 0 < p.toReal / (p.toReal - 1) := div_pos hP0 (by linarith only [hP])
  have hQ : (p.toReal - 1) * (p.toReal / (p.toReal - 1)) = p.toReal := by
    field_simp
  have hPQ : 1 / p.toReal + 1 / (p.toReal / (p.toReal - 1)) = 1 := by
    field_simp
    ring
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hp1
    exact absurd hp1 (by simp)
  have hc0 : (volume U)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin
  have key : ∀ n : ℕ, (volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (p14_T p.toReal (n : ℝ) F x) ≤
      ENNReal.ofReal M ^ p.toReal := by
    intro n
    refine p14_norming_step h0 hfin hP hQ0 hQ hPQ hF n ?_
    have := hdual (p14_G p.toReal (n : ℝ) F) (p14_measurable_G _ _ hF)
      ⟨(n : ℝ) ^ (p.toReal - 1), p14_norm_G_le hP (Nat.cast_nonneg n) F⟩
    rwa [p14_conj hp1 hpt] at this
  have hsup : ∫⁻ x in U, ‖F x‖ₑ ^ p.toReal =
      ⨆ n : ℕ, ∫⁻ x in U, ENNReal.ofReal (p14_T p.toReal (n : ℝ) F x) := by
    rw [← lintegral_iSup (fun n => (p14_measurable_T _ _ hF).ennreal_ofReal)
      (fun m n hmn x => p14_monotone_T F x hmn)]
    exact lintegral_congr fun x => (p14_iSup_T hP F x).symm
  rw [p14_lpBar_eq hp0 hpt hF.aestronglyMeasurable, hsup, ENNReal.mul_iSup]
  have : (⨆ n : ℕ, (volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (p14_T p.toReal (n : ℝ) F x)) ≤
      ENNReal.ofReal M ^ p.toReal := iSup_le key
  calc _ ≤ (ENNReal.ofReal M ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow this (by positivity)
    _ = ENNReal.ofReal M := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hP0.ne', ENNReal.rpow_one]

/-- **Norming lemma**: `F` only a.e. strongly measurable on `U`. -/
theorem p14_norming {U : Set (Vec d)} (h0 : volume U ≠ 0) (hfin : volume U ≠ ∞)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (volume.restrict U)) {M : ℝ}
    (hdual : ∀ G : Vec d → Vec d, Measurable G → (∃ B : ℝ, ∀ x, ‖G x‖ ≤ B) →
      ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (G x)| ≤
        ENNReal.ofReal M * lpBar U p.conjExponent G) :
    lpBar U p F ≤ ENNReal.ofReal M := by
  have hA : AEMeasurable F (volume.restrict U) := hF.aemeasurable
  have hae : F =ᵐ[volume.restrict U] hA.mk F := hA.ae_eq_mk
  have hlp : lpBar U p F = lpBar U p (hA.mk F) :=
    eLpNorm_congr_ae (Measure.ae_smul_measure hae _)
  rw [hlp]
  refine p14_norming_measurable h0 hfin hp1 hpt hA.measurable_mk fun G hG hB => ?_
  have hint : ∫ x in U, vecDot (hA.mk F x) (G x) = ∫ x in U, vecDot (F x) (G x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hint]
  exact hdual G hG hB

end SuperdiffusionCLT.Section7
