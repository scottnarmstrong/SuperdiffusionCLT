/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareB

/-!
# Poincare inequalities on domains: the double integral estimate

For an open set `W` and a measurable set `B` such that `W` is star-shaped with respect to every
point of `B` (all segments from `W` to `B` lie in `W`), and `u` with weak gradient `g` on `W`,
`Section7.a10_double_integral_le` bounds `∫_W ∫_B |u b - u x|² db dx` by
`d D² 2^d (|W| + |B|) ∫_W |g|²`, where `D` bounds the distances between `W` and `B`.
The proof combines the translation identity with the affine change of variables
`z = (1 - s) x + s b` (one of the two variables is scaled by a factor at least `1/2`).
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Affine change of variables for the lower integral. -/
theorem a10_lintegral_affine {r : ℝ} (hr : 0 < r) (a : Vec d) {F : Vec d → ENNReal}
    (hF : Measurable F) :
    ∫⁻ b, F (a + r • b) = ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ z, F z := by
  have hmap := Measure.map_addHaar_smul (volume : Measure (Vec d)) hr.ne'
  have hfin : Module.finrank ℝ (Vec d) = d := by simp
  rw [hfin, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hr.le _))] at hmap
  have hG : Measurable fun y : Vec d => F (a + y) := hF.comp (by fun_prop)
  calc ∫⁻ b, F (a + r • b) = ∫⁻ b, (fun y : Vec d => F (a + y)) ((fun x => r • x) b) := rfl
    _ = ∫⁻ y, F (a + y) ∂(Measure.map (fun x : Vec d => r • x) volume) :=
        (lintegral_map hG (measurable_const_smul r)).symm
    _ = ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ y, F (a + y) := by
        rw [hmap, lintegral_smul_measure]; rfl
    _ = ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ z, F z := by
        rw [lintegral_add_left_eq_self F a]

theorem a10_inv_pow_le {s : ℝ} (hs : 1 / 2 ≤ s) :
    ENNReal.ofReal ((s ^ d)⁻¹) ≤ 2 ^ d := by
  have hs0 : 0 < s := by linarith only [hs]
  have h1 : ((1 : ℝ) / 2) ^ d ≤ s ^ d := pow_le_pow_left₀ (by norm_num) hs d
  have h2 : (s ^ d)⁻¹ ≤ (2 : ℝ) ^ d := by
    have hpos : 0 < ((1 : ℝ) / 2) ^ d := by positivity
    calc (s ^ d)⁻¹ ≤ (((1 : ℝ) / 2) ^ d)⁻¹ := inv_anti₀ hpos h1
      _ = (2 : ℝ) ^ d := by rw [one_div, inv_pow, inv_inv]
  calc ENNReal.ofReal ((s ^ d)⁻¹) ≤ ENNReal.ofReal ((2 : ℝ) ^ d) := ENNReal.ofReal_le_ofReal h2
    _ = 2 ^ d := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      simp

/-- One of the two affine regimes: the averaged integral along the segments from `W` to `B` is
bounded by the integral over `W`. -/
theorem a10_star_average_le {W B : Set (Vec d)} (hWm : MeasurableSet W) (hBm : MeasurableSet B)
    (hstar : ∀ x ∈ W, ∀ b ∈ B, ∀ s ∈ Icc (0 : ℝ) 1, (1 - s) • x + s • b ∈ W)
    {F : Vec d → ENNReal} (hF : Measurable F) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫⁻ x in W, ∫⁻ b in B, F ((1 - s) • x + s • b) ≤
      2 ^ d * (volume W + volume B) * ∫⁻ z in W, F z := by
  have hFW : Measurable (W.indicator F) := hF.indicator hWm
  have hint : ∫⁻ z, W.indicator F z = ∫⁻ z in W, F z := lintegral_indicator hWm F
  by_cases hs2 : 1 / 2 ≤ s
  · have hs0 : 0 < s := by linarith only [hs2]
    have hinner : ∀ x ∈ W, ∫⁻ b in B, F ((1 - s) • x + s • b) ≤ 2 ^ d * ∫⁻ z in W, F z := by
      intro x hx
      calc ∫⁻ b in B, F ((1 - s) • x + s • b)
          ≤ ∫⁻ b, W.indicator F ((1 - s) • x + s • b) := by
            rw [← lintegral_indicator hBm]
            refine lintegral_mono fun b => ?_
            by_cases hb : b ∈ B
            · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (hstar x hx b hb s hs)]
            · rw [Set.indicator_of_notMem hb]; exact zero_le
        _ = ENNReal.ofReal ((s ^ d)⁻¹) * ∫⁻ z, W.indicator F z :=
            a10_lintegral_affine hs0 ((1 - s) • x) hFW
        _ ≤ 2 ^ d * ∫⁻ z in W, F z := by
            rw [hint]
            exact mul_le_mul_left (a10_inv_pow_le hs2) _
    calc ∫⁻ x in W, ∫⁻ b in B, F ((1 - s) • x + s • b)
        ≤ ∫⁻ x in W, 2 ^ d * ∫⁻ z in W, F z := setLIntegral_mono' hWm hinner
      _ = 2 ^ d * ((∫⁻ z in W, F z) * volume W) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          ring
      _ ≤ 2 ^ d * (volume W + volume B) * ∫⁻ z in W, F z := by
          have : volume W ≤ volume W + volume B := le_self_add
          calc 2 ^ d * ((∫⁻ z in W, F z) * volume W)
              = 2 ^ d * volume W * ∫⁻ z in W, F z := by ring
            _ ≤ 2 ^ d * (volume W + volume B) * ∫⁻ z in W, F z := by gcongr
  · have hs1 : s < 1 / 2 := not_le.1 hs2
    have hr : 1 / 2 ≤ 1 - s := by linarith only [hs1]
    have hr0 : 0 < 1 - s := by linarith only [hr]
    have hswap : ∫⁻ x in W, ∫⁻ b in B, F ((1 - s) • x + s • b) =
        ∫⁻ b in B, ∫⁻ x in W, F ((1 - s) • x + s • b) := by
      refine lintegral_lintegral_swap (f := fun x b => F ((1 - s) • x + s • b)) ?_
      exact (hF.comp (by fun_prop)).aemeasurable
    have hinner : ∀ b ∈ B, ∫⁻ x in W, F ((1 - s) • x + s • b) ≤ 2 ^ d * ∫⁻ z in W, F z := by
      intro b hb
      calc ∫⁻ x in W, F ((1 - s) • x + s • b)
          ≤ ∫⁻ x, W.indicator F (s • b + (1 - s) • x) := by
            rw [← lintegral_indicator hWm]
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ W
            · have hmem : s • b + (1 - s) • x ∈ W := by
                rw [add_comm]; exact hstar x hx b hb s hs
              rw [Set.indicator_of_mem hx, Set.indicator_of_mem hmem, add_comm]
            · rw [Set.indicator_of_notMem hx]; exact zero_le
        _ = ENNReal.ofReal (((1 - s) ^ d)⁻¹) * ∫⁻ z, W.indicator F z :=
            a10_lintegral_affine hr0 (s • b) hFW
        _ ≤ 2 ^ d * ∫⁻ z in W, F z := by
            rw [hint]
            exact mul_le_mul_left (a10_inv_pow_le hr) _
    rw [hswap]
    calc ∫⁻ b in B, ∫⁻ x in W, F ((1 - s) • x + s • b)
        ≤ ∫⁻ b in B, 2 ^ d * ∫⁻ z in W, F z := setLIntegral_mono' hBm hinner
      _ = 2 ^ d * ((∫⁻ z in W, F z) * volume B) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          ring
      _ ≤ 2 ^ d * (volume W + volume B) * ∫⁻ z in W, F z := by
          have : volume B ≤ volume W + volume B := le_add_self
          calc 2 ^ d * ((∫⁻ z in W, F z) * volume B)
              = 2 ^ d * volume B * ∫⁻ z in W, F z := by ring
            _ ≤ 2 ^ d * (volume W + volume B) * ∫⁻ z in W, F z := by gcongr

theorem a10_vecNormSq_le (h : Vec d) : vecNormSq h ≤ d * ‖h‖ ^ 2 := by
  unfold vecNormSq vecDot
  calc ∑ i, h i * h i ≤ ∑ _i : Fin d, ‖h‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_le_pi_norm h i
        rw [Real.norm_eq_abs] at this
        calc h i * h i = |h i| ^ 2 := by rw [sq_abs]; ring
          _ ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = d * ‖h‖ ^ 2 := by simp

/-- The mean-value double integral: for `x ∈ W` and `b ∈ B`, with all segments in `W`. -/
theorem a10_double_integral_le {W B : Set (Vec d)} (hW : IsOpen W) (hBm : MeasurableSet B)
    (hstar : ∀ x ∈ W, ∀ b ∈ B, ∀ s ∈ Icc (0 : ℝ) 1, (1 - s) • x + s • b ∈ W) {D : ℝ}
    (hD : ∀ x ∈ W, ∀ b ∈ B, ‖b - x‖ ≤ D) {U : Vec d → ℝ} {G : Fin d → Vec d → ℝ}
    (hUm : Measurable U) (hGm : ∀ i, Measurable (G i))
    (hUl : LocallyIntegrable U volume) (hGl : ∀ i, LocallyIntegrable (G i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, U x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x) :
    ∫⁻ x in W, ∫⁻ b in B, ENNReal.ofReal ((U b - U x) ^ 2) ≤
      ENNReal.ofReal (d * D ^ 2) * (2 ^ d * (volume W + volume B)) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, G i z ^ 2) := by
  have hWm : MeasurableSet W := hW.measurableSet
  set gs : Vec d → ENNReal := fun z => ENNReal.ofReal (∑ i, G i z ^ 2) with hgs
  have hgsm : Measurable gs :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => (hGm i).pow_const 2)
  set S : Set (Vec d × Vec d) := {p | p.1 ∈ W ∧ p.1 + p.2 ∈ B} with hS
  have hSm : MeasurableSet S :=
    (measurable_fst hWm).inter (measurable_add hBm)
  set K : Vec d × Vec d → ENNReal :=
    S.indicator (fun p => ENNReal.ofReal ((U (p.1 + p.2) - U p.1) ^ 2)) with hK
  have hKm : Measurable K := by
    refine Measurable.indicator ?_ hSm
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((hUm.comp measurable_add).sub (hUm.comp measurable_fst)).pow_const 2
  -- Step 1
  have step1 : ∫⁻ x in W, ∫⁻ b in B, ENNReal.ofReal ((U b - U x) ^ 2) =
      ∫⁻ x, ∫⁻ h, K (x, h) := by
    rw [← lintegral_indicator hWm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem hx, ← lintegral_indicator hBm,
        ← lintegral_add_left_eq_self (fun b => B.indicator (fun b => ENNReal.ofReal ((U b - U x) ^ 2)) b) x]
      refine lintegral_congr fun h => ?_
      by_cases hb : x + h ∈ B
      · have : (x, h) ∈ S := ⟨hx, hb⟩
        rw [hK]; simp only [Set.indicator_of_mem this, Set.indicator_of_mem hb]
      · have : (x, h) ∉ S := fun hh => hb hh.2
        rw [hK]; simp only [Set.indicator_of_notMem this, Set.indicator_of_notMem hb]
    · rw [Set.indicator_of_notMem hx]
      symm
      rw [← lintegral_zero (μ := (volume : Measure (Vec d)))]
      refine lintegral_congr fun h => ?_
      have : (x, h) ∉ S := fun hh => hx hh.1
      rw [hK]; simp only [Set.indicator_of_notMem this]
  -- the triple function
  set T : Set (Vec d × Vec d × ℝ) := {q | (q.1, q.2.1) ∈ S} with hT
  have hTm : MeasurableSet T := by
    refine hSm.preimage ?_
    fun_prop
  set L : Vec d × Vec d × ℝ → ENNReal :=
    T.indicator (fun q => gs (q.1 + q.2.2 • q.2.1)) with hL
  have hLm : Measurable L := by
    refine Measurable.indicator (hgsm.comp ?_) hTm
    fun_prop
  have hLx : ∀ x h s, L (x, h, s) = S.indicator (fun p => gs (p.1 + s • p.2)) (x, h) := by
    intro x h s
    by_cases hxh : (x, h) ∈ S
    · have : (x, h, s) ∈ T := hxh
      rw [hL]; simp only [Set.indicator_of_mem this, Set.indicator_of_mem hxh]
    · have : (x, h, s) ∉ T := hxh
      rw [hL]; simp only [Set.indicator_of_notMem this, Set.indicator_of_notMem hxh]
  -- Step 3
  have step3 : ∀ h : Vec d, ∀ᵐ x : Vec d, K (x, h) ≤
      ENNReal.ofReal (d * D ^ 2) * ∫⁻ s in Icc (0 : ℝ) 1, L (x, h, s) := by
    intro h
    filter_upwards [a10_sq_diff_le hW hUm hGm hUl hGl hweak h] with x hx
    by_cases hxS : (x, h) ∈ S
    · have hxW : x ∈ W := hxS.1
      have hxB : x + h ∈ B := hxS.2
      have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ W := by
        intro s hs
        have := hstar x hxW (x + h) hxB s hs
        have e : (1 - s) • x + s • (x + h) = x + s • h := by module
        rwa [e] at this
      have hnorm : ‖h‖ ≤ D := by
        have := hD x hxW (x + h) hxB
        rwa [add_sub_cancel_left] at this
      have hvn : vecNormSq h ≤ d * D ^ 2 := by
        refine (a10_vecNormSq_le h).trans ?_
        have h0 : 0 ≤ ‖h‖ := norm_nonneg h
        have : ‖h‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ h0 hnorm 2
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        exact mul_le_mul_of_nonneg_left this hd
      have hLeq : ∀ s, L (x, h, s) = gs (x + s • h) := by
        intro s
        rw [hLx, Set.indicator_of_mem hxS]
      have hKeq : K (x, h) = ENNReal.ofReal ((U (x + h) - U x) ^ 2) := by
        rw [hK]; exact Set.indicator_of_mem hxS _
      rw [hKeq]
      refine (hx hseg).trans ?_
      simp only [hLeq, hgs]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hvn) _
    · have : K (x, h) = 0 := by rw [hK]; exact Set.indicator_of_notMem hxS _
      rw [this]; exact zero_le
  have step2 : ∫⁻ x, ∫⁻ h, K (x, h) = ∫⁻ h, ∫⁻ x, K (x, h) :=
    lintegral_lintegral_swap (f := fun x h => K (x, h)) hKm.aemeasurable
  have hLslice : ∀ h : Vec d, Measurable fun p : Vec d × ℝ => L (p.1, h, p.2) := fun h =>
    hLm.comp (by fun_prop)
  have step4 : ∫⁻ h, ∫⁻ x, K (x, h) ≤ ENNReal.ofReal (d * D ^ 2) *
      ∫⁻ h, ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ x, L (x, h, s) := by
    calc ∫⁻ h, ∫⁻ x, K (x, h)
        ≤ ∫⁻ h, ∫⁻ x, ENNReal.ofReal (d * D ^ 2) * ∫⁻ s in Icc (0 : ℝ) 1, L (x, h, s) :=
          lintegral_mono fun h => lintegral_mono_ae (step3 h)
      _ = ∫⁻ h, ENNReal.ofReal (d * D ^ 2) * ∫⁻ x, ∫⁻ s in Icc (0 : ℝ) 1, L (x, h, s) := by
          refine lintegral_congr fun h => ?_
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (d * D ^ 2) * ∫⁻ h, ∫⁻ x, ∫⁻ s in Icc (0 : ℝ) 1, L (x, h, s) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (d * D ^ 2) * ∫⁻ h, ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ x, L (x, h, s) := by
          congr 1
          refine lintegral_congr fun h => ?_
          exact lintegral_lintegral_swap (f := fun x s => L (x, h, s)) (hLslice h).aemeasurable
  have step4b : ∫⁻ h, ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ x, L (x, h, s) =
      ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ h, ∫⁻ x, L (x, h, s) := by
    refine lintegral_lintegral_swap (f := fun h s => ∫⁻ x, L (x, h, s)) ?_
    have : Measurable fun p : Vec d × ℝ => ∫⁻ x, L (x, p.1, p.2) := by
      refine Measurable.lintegral_prod_right' (f := fun q : (Vec d × ℝ) × Vec d => L (q.2, q.1.1, q.1.2)) ?_
      exact hLm.comp (by fun_prop)
    exact this.aemeasurable
  have step5 : ∀ s ∈ Icc (0 : ℝ) 1, ∫⁻ h, ∫⁻ x, L (x, h, s) ≤
      2 ^ d * (volume W + volume B) * ∫⁻ z in W, gs z := by
    intro s hs
    have hsw : ∫⁻ h, ∫⁻ x, L (x, h, s) = ∫⁻ x, ∫⁻ h, L (x, h, s) := by
      refine lintegral_lintegral_swap (f := fun h x => L (x, h, s)) ?_
      exact (hLm.comp (by fun_prop : Measurable fun p : Vec d × Vec d => (p.2, p.1, s))).aemeasurable
    have hx : ∀ x, ∫⁻ h, L (x, h, s) =
        W.indicator (fun x => ∫⁻ b in B, gs ((1 - s) • x + s • b)) x := by
      intro x
      by_cases hxW : x ∈ W
      · rw [Set.indicator_of_mem hxW, ← lintegral_indicator hBm,
          ← lintegral_add_left_eq_self
            (fun b => B.indicator (fun b => gs ((1 - s) • x + s • b)) b) x]
        refine lintegral_congr fun h => ?_
        have e : (1 - s) • x + s • (x + h) = x + s • h := by module
        by_cases hb : x + h ∈ B
        · have hxS : (x, h) ∈ S := ⟨hxW, hb⟩
          rw [hLx, Set.indicator_of_mem hxS, Set.indicator_of_mem hb, e]
        · have hxS : (x, h) ∉ S := fun hh => hb hh.2
          rw [hLx, Set.indicator_of_notMem hxS, Set.indicator_of_notMem hb]
      · rw [Set.indicator_of_notMem hxW]
        have : ∀ h, L (x, h, s) = 0 := by
          intro h
          have hxS : (x, h) ∉ S := fun hh => hxW hh.1
          rw [hLx, Set.indicator_of_notMem hxS]
        simp [this]
    rw [hsw]
    calc ∫⁻ x, ∫⁻ h, L (x, h, s) = ∫⁻ x, W.indicator (fun x => ∫⁻ b in B, gs ((1 - s) • x + s • b)) x :=
          lintegral_congr hx
      _ = ∫⁻ x in W, ∫⁻ b in B, gs ((1 - s) • x + s • b) := lintegral_indicator hWm _
      _ ≤ 2 ^ d * (volume W + volume B) * ∫⁻ z in W, gs z :=
          a10_star_average_le hWm hBm hstar hgsm hs
  rw [step1, step2]
  refine step4.trans ?_
  rw [step4b, mul_assoc]
  refine mul_le_mul_right ?_ _
  calc ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ h, ∫⁻ x, L (x, h, s)
      ≤ ∫⁻ s in Icc (0 : ℝ) 1, 2 ^ d * (volume W + volume B) * ∫⁻ z in W, gs z :=
        setLIntegral_mono' measurableSet_Icc step5
    _ = 2 ^ d * (volume W + volume B) * ∫⁻ z in W, gs z := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        simp

end SuperdiffusionCLT.Section7
