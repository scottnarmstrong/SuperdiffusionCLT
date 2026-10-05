/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.WhitneyBall
public import Homogenization.Sobolev.H1.BasicLemmas
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareF
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Whitney interior of a ball: the mean-value Poincare inequality and the satisfiability witness

Let `W` be open of finite volume, `C ⊆ W` a star-ball domain, and `Ψ = wpd_shift ℓ` the shift of
the coordinates of absolute value at least `ℓ` towards the origin. If every segment from `x ∈ W` to
`Ψ x` lies in `W` and `Ψ` maps `W` into `C`, then `W` carries the mean-value Poincare inequality
(`wpd_poincare`) with a constant depending only on `d`, `ℓ`, and the star-ball data of `C`. The
shift acts as a translation on each of the `3^d` measurable pieces of the state of the
coordinates, so that it compares `u` with `u ∘ Ψ` through the translation identity of the weak
gradient, and `u ∘ Ψ` with its mean over `C` by the Poincare inequality on `C`.

For a ball, `wpd_ball_poincare` applies this to the digital ball of the Whitney interior, and
`wpd_whitney_poincare_witness` shows that the scaled Poincare hypothesis on the Whitney interior of
`t • euclidBall (1/2)` holds with a constant `D 3^m`, `D` depending only on `d`.
-/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The state of a coordinate: `1` if `x ≥ ℓ`, `2` if `x ≤ -ℓ`, `0` otherwise. -/
noncomputable def wpd_code (ℓ x : ℝ) : Fin 3 := if ℓ ≤ x then 1 else if x ≤ -ℓ then 2 else 0

/-- The translation amount attached to a state. -/
noncomputable def wpd_dec (ℓ : ℝ) : Fin 3 → ℝ := ![0, -ℓ, ℓ]

/-- The state vector of a point. -/
noncomputable def wpd_codeV (ℓ : ℝ) (x : Vec d) : Fin d → Fin 3 := fun i => wpd_code ℓ (x i)

/-- The translation vector attached to a state vector. -/
noncomputable def wpd_hv (ℓ : ℝ) (σ : Fin d → Fin 3) : Vec d := fun i => wpd_dec ℓ (σ i)

theorem wpd_step_eq (ℓ x : ℝ) : wpd_step ℓ x = x + wpd_dec ℓ (wpd_code ℓ x) := by
  unfold wpd_step wpd_code
  by_cases h1 : ℓ ≤ x
  · simp [h1, wpd_dec, sub_eq_add_neg]
  · by_cases h2 : x ≤ -ℓ
    · simp [h1, h2, wpd_dec]
    · simp [h1, h2, wpd_dec]

theorem wpd_shift_eq (ℓ : ℝ) (x : Vec d) : wpd_shift ℓ x = x + wpd_hv ℓ (wpd_codeV ℓ x) := by
  ext i
  simp [wpd_shift, wpd_hv, wpd_codeV, wpd_step_eq]

theorem wpd_dec_abs_le {ℓ : ℝ} (hℓ : 0 < ℓ) (a : Fin 3) : |wpd_dec ℓ a| ≤ ℓ := by
  fin_cases a <;> simp [wpd_dec, abs_of_pos hℓ, hℓ.le]

theorem wpd_hv_normSq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Fin d → Fin 3) :
    vecNormSq (wpd_hv ℓ σ) ≤ d * ℓ ^ 2 := by
  rw [wpd_vecNormSq_eq]
  calc ∑ i, wpd_hv ℓ σ i ^ 2 ≤ ∑ _i : Fin d, ℓ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (wpd_dec_abs_le hℓ _) 2
    _ = d * ℓ ^ 2 := by simp

theorem wpd_measurable_code (ℓ : ℝ) : Measurable (wpd_code ℓ) := by
  unfold wpd_code
  exact Measurable.ite measurableSet_Ici measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)

theorem wpd_measurable_codeV (ℓ : ℝ) : Measurable (wpd_codeV (d := d) ℓ) :=
  Measurable.of_eval fun i => (wpd_measurable_code ℓ).comp (measurable_pi_apply i)

theorem wpd_measurableSet_piece (ℓ : ℝ) (σ : Fin d → Fin 3) :
    MeasurableSet {x : Vec d | wpd_codeV ℓ x = σ} :=
  (wpd_measurable_codeV ℓ) (measurableSet_singleton σ)

theorem wpd_lintegral_pieces (ℓ : ℝ) {W : Set (Vec d)}
    (φ : Vec d → (Fin d → Fin 3) → ENNReal) (hφ : ∀ σ, Measurable fun x => φ x σ) :
    ∫⁻ x in W, φ x (wpd_codeV ℓ x) =
      ∑ σ : Fin d → Fin 3, ∫⁻ x in W ∩ {x | wpd_codeV ℓ x = σ}, φ x σ := by
  have hpt : ∀ x, φ x (wpd_codeV ℓ x) =
      ∑ σ : Fin d → Fin 3, {x : Vec d | wpd_codeV ℓ x = σ}.indicator (fun x => φ x σ) x := by
    intro x
    rw [Finset.sum_eq_single (wpd_codeV ℓ x)]
    · rw [Set.indicator_of_mem (by rfl)]
    · intro σ _ hσ
      rw [Set.indicator_of_notMem]
      exact fun h => hσ h.symm
    · simp
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun σ _ => (hφ σ).indicator (wpd_measurableSet_piece ℓ σ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [lintegral_indicator (wpd_measurableSet_piece ℓ σ), Measure.restrict_restrict (wpd_measurableSet_piece ℓ σ),
    Set.inter_comm]

theorem wpd_lintegral_translate_le {P T : Set (Vec d)} (hPm : MeasurableSet P)
    (hTm : MeasurableSet T) {f : Vec d → ENNReal} (h : Vec d) (hPT : ∀ x ∈ P, x + h ∈ T) :
    ∫⁻ x in P, f (x + h) ≤ ∫⁻ y in T, f y := by
  rw [← lintegral_indicator hPm, ← lintegral_indicator hTm,
    ← lintegral_add_right_eq_self (T.indicator f) h]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ P
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hPT x hx)]
  · rw [Set.indicator_of_notMem hx]; exact zero_le

theorem wpd_sq_diff_piece {W : Set (Vec d)} (hWo : IsOpen W) {U : Vec d → ℝ}
    {G : Fin d → Vec d → ℝ} (hUm : Measurable U) (hGm : ∀ i, Measurable (G i))
    (hUl : LocallyIntegrable U volume) (hGl : ∀ i, LocallyIntegrable (G i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, U x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x)
    (h : Vec d) {P : Set (Vec d)} (hPm : MeasurableSet P)
    (hseg : ∀ x ∈ P, ∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ W) :
    ∫⁻ x in P, ENNReal.ofReal ((U (x + h) - U x) ^ 2) ≤
      ENNReal.ofReal (vecNormSq h) * ∫⁻ z in W, ENNReal.ofReal (∑ i, G i z ^ 2) := by
  set gs : Vec d → ENNReal := fun z => ENNReal.ofReal (∑ i, G i z ^ 2) with hgs
  have hgsm : Measurable gs :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => (hGm i).pow_const 2)
  have hWm : MeasurableSet W := hWo.measurableSet
  have ha : ∫⁻ x in P, ENNReal.ofReal ((U (x + h) - U x) ^ 2) ≤
      ∫⁻ x in P, ENNReal.ofReal (vecNormSq h) * ∫⁻ s in Icc (0 : ℝ) 1, gs (x + s • h) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (a10_sq_diff_le hWo hUm hGm hUl hGl hweak h),
      ae_restrict_mem hPm] with x hx hxP
    exact hx (hseg x hxP)
  refine ha.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_right ?_ _
  have hmeas : Measurable fun p : Vec d × ℝ => gs (p.1 + p.2 • h) :=
    hgsm.comp (by fun_prop)
  rw [lintegral_lintegral_swap (f := fun x s => gs (x + s • h)) hmeas.aemeasurable]
  calc ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ x in P, gs (x + s • h)
      ≤ ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ z in W, gs z := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        exact wpd_lintegral_translate_le hPm hWm (s • h) fun x hx => hseg x hx s hs
    _ = ∫⁻ z in W, gs z := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        simp

theorem wpd_measurable_step (ℓ : ℝ) : Measurable (wpd_step ℓ) := by
  unfold wpd_step
  exact Measurable.ite measurableSet_Ici (measurable_id.sub_const _)
    (Measurable.ite measurableSet_Iic (measurable_id.add_const _) measurable_id)

theorem wpd_measurable_shift (ℓ : ℝ) : Measurable (wpd_shift (d := d) ℓ) :=
  Measurable.of_eval fun i => (wpd_measurable_step ℓ).comp (measurable_pi_apply i)

theorem wpd_ofReal_sq_le (a b c : ℝ) :
    ENNReal.ofReal ((a - c) ^ 2) ≤
      2 * ENNReal.ofReal ((a - b) ^ 2) + 2 * ENNReal.ofReal ((b - c) ^ 2) := by
  have h := a10_two_sq_le a c b
  calc ENNReal.ofReal ((a - c) ^ 2) = ENNReal.ofReal ((c - a) ^ 2) := by congr 1; ring
    _ ≤ ENNReal.ofReal (2 * (a - b) ^ 2 + 2 * (c - b) ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal ((a - b) ^ 2) + 2 * ENNReal.ofReal ((b - c) ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        have e2 : (c - b) ^ 2 = (b - c) ^ 2 := by ring
        rw [e2]
        simp

/-- **Poincare inequality on a set mapped into a star-ball domain by the shift of the large
coordinates**, lower-integral form. -/
theorem wpd_poincare_lintegral {W C : Set (Vec d)} {x0 : Vec d} {s0 Dc ℓ : ℝ}
    (hWo : IsOpen W) (hWt : volume W ≠ ⊤) (hC : IsStarBallDomain C x0 s0 Dc) (hCW : C ⊆ W)
    (hℓ : 0 < ℓ)
    (hseg : ∀ x ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, x + s • (wpd_shift ℓ x - x) ∈ W)
    (hmap : ∀ x ∈ W, wpd_shift ℓ x ∈ C) (u : H1Function W) :
    ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) ^ 2) ≤
      ENNReal.ofReal (8 * 3 ^ d * (d * ℓ ^ 2 + 4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d))) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2) := by
  have hWm : MeasurableSet W := hWo.measurableSet
  have hC' := hC
  obtain ⟨hCo, hs0, hBC, -, hdiam⟩ := hC
  have hCm : MeasurableSet C := hCo.measurableSet
  obtain ⟨hB0, hBt⟩ := a10_volume_ball_ne x0 hs0
  have hW0 : volume W ≠ 0 := by
    intro h0
    exact hB0 (measure_mono_null (hBC.trans hCW) h0)
  obtain ⟨U, G, hUm, hGm, hUl, hGl, hweak, hUae, hGae⟩ := a10_clean_data hWo u
  set Q : ENNReal := ∫⁻ z in W, ENNReal.ofReal (∑ i, G i z ^ 2) with hQ
  have hQ' : Q = ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2) := by
    refine lintegral_congr_ae ?_
    have hall : ∀ᵐ z ∂(volume.restrict W), ∀ i, G i z = u.grad z i := by
      rw [ae_all_iff]; exact hGae
    filter_upwards [hall] with z hz
    simp [hz]
  set c : ℝ := (∫ y in C, u.toFun y) / (volume C).toReal with hc
  -- the Poincare inequality on `C`
  have hPC := a10_poincare_starBall_lintegral hC' (u.restrict hCo hCW)
  have hPC' : ∫⁻ x in C, ENNReal.ofReal ((U x - c) ^ 2) ≤
      ENNReal.ofReal (4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) * Q := by
    have hUC : U =ᵐ[volume.restrict C] u.toFun := ae_restrict_of_ae_restrict_of_subset hCW hUae
    calc ∫⁻ x in C, ENNReal.ofReal ((U x - c) ^ 2)
        = ∫⁻ x in C, ENNReal.ofReal ((u.toFun x - c) ^ 2) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hUC] with x hx
          rw [hx]
      _ ≤ ENNReal.ofReal (4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) *
          ∫⁻ z in C, ENNReal.ofReal (∑ i, u.grad z i ^ 2) := hPC
      _ ≤ ENNReal.ofReal (4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) * Q := by
          rw [hQ']
          gcongr
  -- the two comparison estimates
  have hshiftm := wpd_measurable_shift (d := d) ℓ
  have hT1 : ∫⁻ x in W, ENNReal.ofReal ((U (wpd_shift ℓ x) - U x) ^ 2) ≤
      3 ^ d * (ENNReal.ofReal (d * ℓ ^ 2) * Q) := by
    have h1 : ∀ x, ENNReal.ofReal ((U (wpd_shift ℓ x) - U x) ^ 2) =
        (fun x σ => ENNReal.ofReal ((U (x + wpd_hv ℓ σ) - U x) ^ 2)) x (wpd_codeV ℓ x) := by
      intro x
      simp only [wpd_shift_eq]
    simp_rw [h1]
    rw [wpd_lintegral_pieces ℓ (W := W) (fun x σ => ENNReal.ofReal ((U (x + wpd_hv ℓ σ) - U x) ^ 2))
      (fun σ => ENNReal.measurable_ofReal.comp
        (((hUm.comp (measurable_id.add_const _)).sub hUm).pow_const 2))]
    calc ∑ σ : Fin d → Fin 3, ∫⁻ x in W ∩ {x | wpd_codeV ℓ x = σ},
          ENNReal.ofReal ((U (x + wpd_hv ℓ σ) - U x) ^ 2)
        ≤ ∑ _σ : Fin d → Fin 3, ENNReal.ofReal (d * ℓ ^ 2) * Q := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hP : MeasurableSet (W ∩ {x | wpd_codeV ℓ x = σ}) :=
            hWm.inter (wpd_measurableSet_piece ℓ σ)
          refine (wpd_sq_diff_piece hWo hUm hGm hUl hGl hweak (wpd_hv ℓ σ) hP ?_).trans ?_
          · intro x hx s hs
            have := hseg x hx.1 s hs
            have e : wpd_shift ℓ x - x = wpd_hv ℓ σ := by
              rw [wpd_shift_eq, hx.2]; abel
            rwa [e] at this
          · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (wpd_hv_normSq_le hℓ σ)) le_rfl
      _ = 3 ^ d * (ENNReal.ofReal (d * ℓ ^ 2) * Q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
          simp
  have hT2 : ∫⁻ x in W, ENNReal.ofReal ((U (wpd_shift ℓ x) - c) ^ 2) ≤
      3 ^ d * ∫⁻ x in C, ENNReal.ofReal ((U x - c) ^ 2) := by
    have h1 : ∀ x, ENNReal.ofReal ((U (wpd_shift ℓ x) - c) ^ 2) =
        (fun x σ => ENNReal.ofReal ((U (x + wpd_hv ℓ σ) - c) ^ 2)) x (wpd_codeV ℓ x) := by
      intro x
      simp only [wpd_shift_eq]
    simp_rw [h1]
    rw [wpd_lintegral_pieces ℓ (W := W) (fun x σ => ENNReal.ofReal ((U (x + wpd_hv ℓ σ) - c) ^ 2))
      (fun σ => ENNReal.measurable_ofReal.comp
        (((hUm.comp (measurable_id.add_const _)).sub_const c).pow_const 2))]
    calc ∑ σ : Fin d → Fin 3, ∫⁻ x in W ∩ {x | wpd_codeV ℓ x = σ},
          ENNReal.ofReal ((U (x + wpd_hv ℓ σ) - c) ^ 2)
        ≤ ∑ _σ : Fin d → Fin 3, ∫⁻ x in C, ENNReal.ofReal ((U x - c) ^ 2) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hP : MeasurableSet (W ∩ {x | wpd_codeV ℓ x = σ}) :=
            hWm.inter (wpd_measurableSet_piece ℓ σ)
          refine wpd_lintegral_translate_le (f := fun y => ENNReal.ofReal ((U y - c) ^ 2)) hP hCm
            (wpd_hv ℓ σ) ?_
          intro x hx
          have := hmap x hx.1
          rwa [wpd_shift_eq, hx.2] at this
      _ = 3 ^ d * ∫⁻ x in C, ENNReal.ofReal ((U x - c) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
          simp
  -- the chain
  have hUi : IntegrableOn U W volume := by
    have hmem : MemLp u.toFun 2 (volume.restrict W) := u.memL2
    have : IsFiniteMeasure (volume.restrict W) := ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hWt⟩
    have h1 : Integrable u.toFun (volume.restrict W) := hmem.integrable (by norm_num)
    exact h1.congr hUae.symm
  have hmean : ∫ y in W, U y = ∫ y in W, u.toFun y := integral_congr_ae hUae
  have hL0 := a10_meanW_le hW0 hWt hUm hUi c
  have hmeasA : Measurable fun x => ENNReal.ofReal ((U (wpd_shift ℓ x) - U x) ^ 2) :=
    ENNReal.measurable_ofReal.comp (((hUm.comp hshiftm).sub hUm).pow_const 2)
  have hL1 : ∫⁻ x in W, ENNReal.ofReal ((U x - c) ^ 2) ≤
      2 * (∫⁻ x in W, ENNReal.ofReal ((U (wpd_shift ℓ x) - U x) ^ 2)) +
        2 * (∫⁻ x in W, ENNReal.ofReal ((U (wpd_shift ℓ x) - c) ^ 2)) := by
    calc ∫⁻ x in W, ENNReal.ofReal ((U x - c) ^ 2)
        ≤ ∫⁻ x in W, (2 * ENNReal.ofReal ((U x - U (wpd_shift ℓ x)) ^ 2) +
            2 * ENNReal.ofReal ((U (wpd_shift ℓ x) - c) ^ 2)) :=
          lintegral_mono fun x => wpd_ofReal_sq_le _ _ _
      _ = _ := by
          have e : ∀ x, ENNReal.ofReal ((U x - U (wpd_shift ℓ x)) ^ 2) =
              ENNReal.ofReal ((U (wpd_shift ℓ x) - U x) ^ 2) := fun x => by congr 1; ring
          simp_rw [e]
          rw [lintegral_add_left (hmeasA.const_mul 2), lintegral_const_mul _ hmeasA,
            lintegral_const_mul' _ _ (by norm_num)]
  -- assemble
  have hfinal : ∫⁻ x in W, ENNReal.ofReal ((U x - (∫ y in W, U y) / (volume W).toReal) ^ 2) ≤
      8 * 3 ^ d * (ENNReal.ofReal (d * ℓ ^ 2) +
        ENNReal.ofReal (4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d))) * Q := by
    calc ∫⁻ x in W, ENNReal.ofReal ((U x - (∫ y in W, U y) / (volume W).toReal) ^ 2)
        ≤ 4 * ∫⁻ x in W, ENNReal.ofReal ((U x - c) ^ 2) := hL0
      _ ≤ 4 * (2 * (3 ^ d * (ENNReal.ofReal (d * ℓ ^ 2) * Q)) +
            2 * (3 ^ d * (ENNReal.ofReal (4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) * Q))) := by
          gcongr
          · exact hL1.trans (add_le_add (by gcongr) (by
              calc 2 * ∫⁻ x in W, ENNReal.ofReal ((U (wpd_shift ℓ x) - c) ^ 2)
                  ≤ 2 * (3 ^ d * ∫⁻ x in C, ENNReal.ofReal ((U x - c) ^ 2)) := by gcongr
                _ ≤ _ := by gcongr))
      _ = _ := by ring
  have hlhs : ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) ^ 2) =
      ∫⁻ x in W, ENNReal.ofReal ((U x - (∫ y in W, U y) / (volume W).toReal) ^ 2) := by
    rw [hmean]
    refine lintegral_congr_ae ?_
    filter_upwards [hUae] with x hx
    rw [hx]
  have hconst : ENNReal.ofReal (8 * 3 ^ d * (d * ℓ ^ 2 + 4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d))) =
      (8 : ENNReal) * 3 ^ d * (ENNReal.ofReal (d * ℓ ^ 2) +
        ENNReal.ofReal (4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d))) := by
    have hD0 : 0 ≤ Dc := by
      have := hdiam x0 (hBC (Metric.mem_ball_self hs0)) x0 (hBC (Metric.mem_ball_self hs0))
      simpa using this
    have hq : 0 ≤ (Dc / s0) ^ d := by positivity
    have hA : 0 ≤ (d : ℝ) * ℓ ^ 2 := by positivity
    have hB : 0 ≤ 4 * (d : ℝ) * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d) := by positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add hA hB, ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [hlhs, ← hQ', hconst]
  exact hfinal

/-- **Poincare inequality on a set mapped into a star-ball domain by the shift of the large
coordinates**, mean-value form, gradient measured in the sup norm. -/
theorem wpd_poincare {W C : Set (Vec d)} {x0 : Vec d} {s0 Dc ℓ : ℝ}
    (hWo : IsOpen W) (hWt : volume W ≠ ⊤) (hC : IsStarBallDomain C x0 s0 Dc) (hCW : C ⊆ W)
    (hℓ : 0 < ℓ)
    (hseg : ∀ x ∈ W, ∀ s ∈ Icc (0 : ℝ) 1, x + s • (wpd_shift ℓ x - x) ∈ W)
    (hmap : ∀ x ∈ W, wpd_shift ℓ x ∈ C) (u : H1Function W) :
    eLpNorm (fun x => u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) 2
        (volume.restrict W) ≤
      ENNReal.ofReal (Real.sqrt (8 * 3 ^ d * (d * ℓ ^ 2 +
          4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) * d)) *
        eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W) := by
  have hD0 : 0 ≤ Dc := by
    have := hC.2.2.2.2 x0 (hC.2.2.1 (Metric.mem_ball_self hC.2.1)) x0
      (hC.2.2.1 (Metric.mem_ball_self hC.2.1))
    simpa using this
  have hq : 0 ≤ (Dc / s0) ^ d := by
    have := hC.2.1
    positivity
  have hκ0 : 0 ≤ 8 * 3 ^ d * ((d : ℝ) * ℓ ^ 2 +
      4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) * d := by positivity
  have hmeas_f : AEStronglyMeasurable (fun x => u.toFun x -
      (∫ y in W, u.toFun y) / (volume W).toReal) (volume.restrict W) :=
    u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hmeas_g : AEStronglyMeasurable (fun x => ‖u.grad x‖) (volume.restrict W) := by
    have : AEMeasurable u.grad (volume.restrict W) :=
      aemeasurable_pi_iff.2 fun i => (u.gradMemL2 i).aestronglyMeasurable.aemeasurable
    exact this.norm.aestronglyMeasurable
  refine a10_eLpNorm_le_of_lintegral hκ0 hmeas_f hmeas_g ?_
  refine (wpd_poincare_lintegral hWo hWt hC hCW hℓ hseg hmap u).trans ?_
  have hpt : ∀ z, ENNReal.ofReal (∑ i, u.grad z i ^ 2) ≤
      ENNReal.ofReal d * ENNReal.ofReal (‖u.grad z‖ ^ 2) := fun z => by
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    exact ENNReal.ofReal_le_ofReal (a10_sum_sq_le _)
  calc ENNReal.ofReal (8 * 3 ^ d * ((d : ℝ) * ℓ ^ 2 +
          4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d))) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2)
      ≤ ENNReal.ofReal (8 * 3 ^ d * ((d : ℝ) * ℓ ^ 2 +
          4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d))) *
        ∫⁻ z in W, ENNReal.ofReal d * ENNReal.ofReal (‖u.grad z‖ ^ 2) := by
        gcongr with z
        exact hpt z
    _ = ENNReal.ofReal (8 * 3 ^ d * ((d : ℝ) * ℓ ^ 2 +
          4 * d * Dc ^ 2 * 2 ^ d * (1 + (Dc / s0) ^ d)) * d) *
        ∫⁻ z in W, ENNReal.ofReal (‖u.grad z‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]


/-- The constant of the Poincare inequality on the Whitney interior of a ball (in units of the
radius of the ball). -/
noncomputable def wpd_D1 (d : ℕ) : ℝ :=
  Real.sqrt (8 * 3 ^ d * (12544 * (d : ℝ) ^ 2 + 16 * d * 2 ^ d * (1 + (2 * Real.sqrt d) ^ d)) * d)

theorem wpd_V_eq_euclidBall (ρ : ℝ) : wpd_V (d := d) ρ = Section6.euclidBall ρ := by
  ext x
  rw [Section6.mem_euclidBall, wpd_vecNormSq_eq]
  rfl

theorem wpd_norm_le_eucNorm (v : Vec d) : ‖v‖ ≤ eucNorm v := by
  unfold eucNorm
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq v i)

theorem wpd_isStarBallDomain_ball [NeZero d] {ρc : ℝ} (hρc : 0 < ρc) :
    IsStarBallDomain (wpd_V (d := d) ρc) 0 (ρc / Real.sqrt d) (2 * ρc) := by
  have hs : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
  rw [wpd_V_eq_euclidBall]
  refine a10_isStarBallDomain_of_convex (Section6.isOpen_euclidBall ρc) (convex_euclidBall ρc)
    (div_pos hρc hs) ?_ ?_
  · refine Section6.ball_subset_euclidBall.trans ?_
    rw [mul_div_cancel₀ _ hs.ne']
  · intro x hx y hy
    have hx' := Section6.euclidBall_subset_ball hρc hx
    have hy' := Section6.euclidBall_subset_ball hρc hy
    rw [mem_ball_zero_iff] at hx' hy'
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ 2 * ρc := by linarith only [hx', hy']

theorem wpd_ball_poincare [NeZero d] {h ρ : ℝ} {V : Set (Vec d)} (hh : 0 < h)
    (hρ : 238 * d * h ≤ ρ) (hV : V = wpd_V ρ) (φ : H1Function V) :
    eLpNorm (fun x => φ.toFun x - ⨍ z in wpd_W0 d h (27 * h / 2) ρ, φ.toFun z) 2
        (volume.restrict (wpd_W0 d h (27 * h / 2) ρ)) ≤
      ENNReal.ofReal (wpd_D1 d * ρ) *
        eLpNorm (fun x => eucNorm (φ.grad x)) 2 (volume.restrict (wpd_W0 d h (27 * h / 2) ρ)) := by
  subst hV
  set r : ℝ := 27 * h / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hrh : h / 2 < r := by rw [hr]; linarith only [hh]
  set c : ℝ := h / 2 + r with hc
  have hc14 : c = 14 * h := by rw [hc, hr]; ring
  have hc0 : 0 < c := by rw [hc14]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hρ' : 17 * d * c ≤ ρ := by rw [hc14]; linarith only [hρ]
  have hρ0 : 0 < ρ := by nlinarith only [hρ, hh, hd1]
  set s : ℝ := Real.sqrt d with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith only [hd1])
  have hs2 : s ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hs1 : 1 ≤ s := by nlinarith only [hs2, hs0, hd1]
  have hsd : s ≤ d := by nlinarith only [hs2, hs0, hd1]
  set ℓ : ℝ := 8 * s * c with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  set ρc : ℝ := ρ - c * s with hρc
  have hρc16 : 16 * d * c ≤ ρc := by
    have : c * s ≤ d * c := by nlinarith only [hsd, hc0]
    linarith only [hρ', this, hρc]
  have hρc0 : 0 < ρc := by nlinarith only [hρc16, hc0, hd1]
  have hρcρ : ρc ≤ ρ := by nlinarith only [hρc, hc0, hs0]
  -- the sets
  set W : Set (Vec d) := wpd_W d h r ρ with hW
  have hWo : IsOpen W := wpd_W_isOpen hh hr0
  have hWV : W ⊆ wpd_V ρ := wpd_W_subset_V hh hrh
  have hWt : volume W ≠ ⊤ := by
    refine ne_top_of_le_ne_top (Section6.volume_euclidBall_ne_top hρ0) (measure_mono ?_)
    rw [← wpd_V_eq_euclidBall]
    exact hWV
  have hCW : wpd_V (d := d) ρc ⊆ W := wpd_V_subset_W hh (by linarith only [hrh, hh]) (le_of_eq (by rw [hρc, hc, hs]; ring)) hρc0.le
  have hCstar := wpd_isStarBallDomain_ball (d := d) hρc0
  have hseg : ∀ x ∈ W, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (wpd_shift ℓ x - x) ∈ W :=
    fun x hx t ht => wpd_shift_segment hh hr0 hℓ0 hx ht.1 ht.2
  have hmap : ∀ x ∈ W, wpd_shift ℓ x ∈ wpd_V (d := d) ρc := fun x hx =>
    wpd_shift_core hc0 hρ' (hWV hx)
  have hmain := wpd_poincare hWo hWt hCstar hCW hℓ0 hseg hmap (φ.restrict hWo hWV)
  have hhρ : h ≤ ρ := by nlinarith only [hρ, hh, hd1]
  have hratio : 2 * ρc / (ρc / s) = 2 * s := by field_simp
  have hA : 0 ≤ 8 * 3 ^ d * (12544 * (d : ℝ) ^ 2 + 16 * d * 2 ^ d * (1 + (2 * s) ^ d)) * d := by
    positivity
  have hκ : 8 * 3 ^ d * ((d : ℝ) * ℓ ^ 2 + 4 * d * (2 * ρc) ^ 2 * 2 ^ d *
        (1 + (2 * ρc / (ρc / s)) ^ d)) * d ≤ (wpd_D1 d * ρ) ^ 2 := by
    have hD1sq : wpd_D1 d ^ 2 =
        8 * 3 ^ d * (12544 * (d : ℝ) ^ 2 + 16 * d * 2 ^ d * (1 + (2 * s) ^ d)) * d := by
      unfold wpd_D1
      exact Real.sq_sqrt hA
    rw [hratio, mul_pow (wpd_D1 d) ρ 2, hD1sq]
    have hℓ2 : ℓ ^ 2 = 64 * d * c ^ 2 := by rw [hℓ, mul_pow, mul_pow, hs2]; ring
    have h1 : (d : ℝ) * ℓ ^ 2 ≤ 12544 * (d : ℝ) ^ 2 * ρ ^ 2 := by
      rw [hℓ2, hc14]
      have : (14 * h) ^ 2 ≤ 14 ^ 2 * ρ ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le hhρ 2) (by norm_num)
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith only [this, hd0, sq_nonneg (d : ℝ)]
    have hq : 0 ≤ 1 + (2 * s) ^ d := by positivity
    have h2 : 4 * (d : ℝ) * (2 * ρc) ^ 2 * 2 ^ d * (1 + (2 * s) ^ d) ≤
        16 * d * 2 ^ d * (1 + (2 * s) ^ d) * ρ ^ 2 := by
      have hρ2 : ρc ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρc0.le hρcρ 2
      have : 0 ≤ (d : ℝ) * 2 ^ d * (1 + (2 * s) ^ d) := by positivity
      nlinarith only [hρ2, this]
    have hmul : 0 ≤ 8 * (3 : ℝ) ^ d * d := by positivity
    have hsum : (d : ℝ) * ℓ ^ 2 + 4 * d * (2 * ρc) ^ 2 * 2 ^ d * (1 + (2 * s) ^ d) ≤
        (12544 * (d : ℝ) ^ 2 + 16 * d * 2 ^ d * (1 + (2 * s) ^ d)) * ρ ^ 2 := by
      nlinarith only [h1, h2]
    calc 8 * (3 : ℝ) ^ d * ((d : ℝ) * ℓ ^ 2 + 4 * d * (2 * ρc) ^ 2 * 2 ^ d * (1 + (2 * s) ^ d)) * d
        = 8 * 3 ^ d * d * ((d : ℝ) * ℓ ^ 2 + 4 * d * (2 * ρc) ^ 2 * 2 ^ d * (1 + (2 * s) ^ d)) := by ring
      _ ≤ 8 * 3 ^ d * d * ((12544 * (d : ℝ) ^ 2 + 16 * d * 2 ^ d * (1 + (2 * s) ^ d)) * ρ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum hmul
      _ = _ := by ring
  have hae := wpd_W_ae_eq (d := d) hh hr0 (ρ := ρ)
  have hμ : volume.restrict (wpd_W0 d h r ρ) = volume.restrict W := Measure.restrict_congr_set hae
  have havg : ⨍ z in W, φ.toFun z = (∫ y in W, φ.toFun y) / (volume W).toReal := by
    rw [setAverage_eq, smul_eq_mul, Measure.real, inv_mul_eq_div]
  rw [hμ, havg]
  refine hmain.trans ?_
  have hmeas_g : AEStronglyMeasurable (fun x => ‖φ.grad x‖) (volume.restrict W) := by
    have : AEMeasurable φ.grad (volume.restrict W) :=
      aemeasurable_pi_iff.2 fun i =>
        ((φ.restrict hWo hWV).gradMemL2 i).aestronglyMeasurable.aemeasurable
    exact this.norm.aestronglyMeasurable
  have hnorm : eLpNorm (fun x => ‖φ.grad x‖) 2 (volume.restrict W) ≤
      eLpNorm (fun x => eucNorm (φ.grad x)) 2 (volume.restrict W) := by
    refine eLpNorm_mono_ae hmeas_g (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ eucNorm (φ.grad x) from Real.sqrt_nonneg _)]
    exact wpd_norm_le_eucNorm _
  have hK : ENNReal.ofReal (Real.sqrt (8 * 3 ^ d * ((d : ℝ) * ℓ ^ 2 + 4 * d * (2 * ρc) ^ 2 * 2 ^ d *
      (1 + (2 * ρc / (ρc / Real.sqrt d)) ^ d)) * d)) ≤ ENNReal.ofReal (wpd_D1 d * ρ) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have := Real.sqrt_le_sqrt hκ
    rwa [Real.sqrt_sq (by unfold wpd_D1; positivity)] at this
  exact mul_le_mul' hK hnorm

theorem wpd_ball_subset_cube [NeZero d] :
    Section6.euclidBall (d := d) (1 / 2) ⊆ openCubeSet (originCube d 0) := by
  intro x hx
  have := Section6.euclidBall_subset_ball (d := d) (by norm_num : (0 : ℝ) < 1 / 2) hx
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)] at this
  rw [w0_mem_openCubeSet_originCube_zero_iff]
  intro i
  have := this i
  rw [Real.norm_eq_abs, abs_lt] at this
  exact this

theorem wpd_three_pow_log_ge {M : ℝ} (hM : 1 ≤ M) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ≤ (3 : ℝ) ^ (⌈M * Real.log m⌉ : ℤ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hk : Real.log m ≤ ((⌈M * Real.log m⌉ : ℤ) : ℝ) :=
    (by nlinarith only [hM, hl0] : Real.log m ≤ M * Real.log m).trans (Int.le_ceil _)
  have hlog3 : 1 ≤ Real.log 3 := by
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith only [this]
    exact ((Real.lt_log_iff_exp_lt (by norm_num)).2 this).le
  rw [← Real.rpow_intCast]
  calc (m : ℝ) = Real.exp (Real.log m) := (Real.exp_log hm0).symm
    _ ≤ Real.exp (Real.log 3 * Real.log m) :=
        Real.exp_le_exp.2 (by nlinarith only [hlog3, hl0])
    _ = (3 : ℝ) ^ (Real.log m) := (Real.rpow_def_of_pos (by norm_num) _).symm
    _ ≤ (3 : ℝ) ^ (((⌈M * Real.log m⌉ : ℤ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hk

/-- **The Poincare hypothesis of the Whitney lemma on a ball is satisfiable.** For `U` the
Euclidean ball of radius `1/2` (smooth, contained in the unit origin cube), there are `D₀` and `T`,
depending only on `d`, such that for every `D ≥ D₀`, `M ≥ 1`, every `t ≥ T` and `m` with
`3^{m-1} < t ≤ 3^m`, and every `φ ∈ H¹(t U)`, the scaled Poincare inequality on the Whitney
interior at the scale `m - ⌈M log m⌉` holds with the constant `D 3^m`. -/
theorem wpd_whitney_poincare_witness [NeZero d] :
    IsSmoothBoundedDomain (Section6.euclidBall (d := d) (1 / 2)) ∧
    Section6.euclidBall (d := d) (1 / 2) ⊆ openCubeSet (originCube d 0) ∧
    ∃ D₀ T : ℝ, 1 ≤ D₀ ∧ 1 ≤ T ∧ ∀ D M : ℝ, D₀ ≤ D → 1 ≤ M →
      ∀ (t : ℝ) (m : ℕ), T ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
        ∀ φ : H1Function (t • Section6.euclidBall (d := d) (1 / 2)),
          eLpNorm (fun x => φ.toFun x -
              ⨍ z in wpd_whitneyInterior (t • Section6.euclidBall (d := d) (1 / 2))
                ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉), φ.toFun z) 2
            (volume.restrict (wpd_whitneyInterior (t • Section6.euclidBall (d := d) (1 / 2))
              ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) ≤
          ENNReal.ofReal (D * (3 : ℝ) ^ m) *
            eLpNorm (fun x => eucNorm (φ.grad x)) 2
              (volume.restrict (wpd_whitneyInterior (t • Section6.euclidBall (d := d) (1 / 2))
                ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) := by
  refine ⟨w0_isSmoothBoundedDomain_euclidBall (by norm_num), wpd_ball_subset_cube,
    max 1 (wpd_D1 d), (3 : ℝ) ^ (1428 * d), le_max_left _ _, one_le_pow₀ (by norm_num), ?_⟩
  intro D M hD hM t m hT htm1 htm2 φ
  have hD1 : wpd_D1 d ≤ D := (le_max_right _ _).trans hD
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hT1 : (1 : ℝ) ≤ (3 : ℝ) ^ (1428 * d) := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith only [hT, hT1]
  have hmN : 1428 * d ≤ m := by
    have : (3 : ℝ) ^ (1428 * d) ≤ (3 : ℝ) ^ m := hT.trans htm2
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 this
  have hm1 : 1 ≤ m := by omega
  have hmd : (1428 * d : ℝ) ≤ m := by exact_mod_cast hmN
  set k : ℤ := ⌈M * Real.log m⌉ with hk
  have h3k : (m : ℝ) ≤ (3 : ℝ) ^ k := wpd_three_pow_log_ge hM hm1
  have hV : t • Section6.euclidBall (d := d) (1 / 2) = wpd_V (t / 2) := wpd_smul_euclidBall ht0
  have hj : (3 : ℝ) ^ ((m : ℤ) - k + 3) / 2 = 27 * (3 : ℝ) ^ ((m : ℤ) - k) / 2 := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hint : wpd_whitneyInterior (t • Section6.euclidBall (d := d) (1 / 2))
      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉) =
      wpd_W0 d ((3 : ℝ) ^ ((m : ℤ) - k)) (27 * (3 : ℝ) ^ ((m : ℤ) - k) / 2) (t / 2) := by
    rw [hV, wpd_interior_eq, hj]
  rw [hint]
  set h : ℝ := (3 : ℝ) ^ ((m : ℤ) - k) with hh
  have hh0 : 0 < h := by positivity
  have h3m : (3 : ℝ) ^ m = h * (3 : ℝ) ^ k := by
    rw [hh, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  have hcond : 238 * (d : ℝ) * h ≤ t / 2 := by
    have h1 : 1428 * (d : ℝ) ≤ (3 : ℝ) ^ k := hmd.trans h3k
    have h2 : (3 : ℝ) ^ m / 3 < t := by linarith only [htm1]
    have h3 : 1428 * (d : ℝ) * h ≤ (3 : ℝ) ^ k * h := mul_le_mul_of_nonneg_right h1 hh0.le
    nlinarith only [h1, h2, h3, h3m, hh0]
  have := wpd_ball_poincare (d := d) hh0 hcond hV φ
  refine this.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hρ : t / 2 ≤ (3 : ℝ) ^ m := by
    have : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    linarith only [htm2, this]
  have hD0 : 0 ≤ wpd_D1 d := by unfold wpd_D1; positivity
  calc wpd_D1 d * (t / 2) ≤ wpd_D1 d * (3 : ℝ) ^ m := mul_le_mul_of_nonneg_left hρ hD0
    _ ≤ D * (3 : ℝ) ^ m := mul_le_mul_of_nonneg_right hD1 (by positivity)

end SuperdiffusionCLT.Section7
