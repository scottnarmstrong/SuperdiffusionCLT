/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2BdryD
public import SuperdiffusionCLT.Section8.Prereq.LinftyL2D
public import SuperdiffusionCLT.Section7.Linfty.Field
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateJ

/-!
# Boundary `L^∞`-`L²` estimate: the cut cell and the assembly
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- Two random scales share one triadic scale. -/
theorem linfL2c_scale2 {N L X₁ X₂ C0 r : ℝ} (hN : 0 ≤ N) (hX₁ : 1 ≤ X₁) (hX₂ : 1 ≤ X₂)
    (hC0 : 1 ≤ C0) (h₁ : C0 * (3 : ℝ) ^ ms_star N L X₁ ≤ r)
    (h₂ : C0 * (3 : ℝ) ^ ms_star N L X₂ ≤ r) :
    ∃ n : ℕ, ms_j0 N ≤ n ∧ L ≤ (nK N n : ℝ) ∧ X₁ ≤ (3 : ℝ) ^ nK N n ∧
      X₂ ≤ (3 : ℝ) ^ nK N n ∧ (3 : ℝ) ^ n ≤ r / C0 ∧ r / C0 < (3 : ℝ) ^ (n + 1) := by
  obtain ⟨n, hj, hL, hX, h3n, h3n1⟩ := linfL2_scale hN hX₁ hC0 h₁
  obtain ⟨n2, hj2, hL2, hX2, h3n2, h3n21⟩ := linfL2_scale hN hX₂ hC0 h₂
  have h12 : n < n2 + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1
    (lt_of_le_of_lt h3n h3n21)
  have h21 : n2 < n + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1
    (lt_of_le_of_lt h3n2 h3n1)
  have : n2 = n := by omega
  subst this
  exact ⟨n2, hj, hL, hX, hX2, h3n, h3n1⟩

/-- **Absorption of the ellipticity ratio.** -/
theorem linfL2c_absorb_ell {N Cf CD nu rho : ℝ} (hN : 0 ≤ N) (hCf : 1 ≤ Cf) (hCD : 0 ≤ CD)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hrho1 : rho < 1) {m' m nb c : ℕ}
    (hm'1 : 1 ≤ m') (hmm : m ≤ 2 * m') (hm1 : 1 ≤ m)
    (hc : c = ⌈(4 * N + 1) * Real.log (m' : ℝ)⌉₊) (hnc : nb + c = m')
    (hk : CD * (4 * Cf ^ 2 / nu ^ 2) ^ N * (2 : ℝ) ^ (4 * N) ≤ (m' : ℝ)) :
    CD * ((((nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 / nu) / nu) ^ N) *
      ((3 : ℝ) ^ nb / (3 : ℝ) ^ m') ≤ 1 := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hq : 0 ≤ 4 * Cf ^ 2 / nu ^ 2 := by positivity
  have hpow : (m : ℝ) ^ (1 + rho) ≤ (m : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hmr (show 1 + rho ≤ 2 by linarith only [hrho1])
    simpa using this
  have h1 : nu + Cf * (m : ℝ) ^ (1 + rho) ≤ 2 * Cf * (m : ℝ) ^ 2 := by
    have h2 : 1 ≤ Cf * (m : ℝ) ^ 2 := by nlinarith only [hCf, hmr]
    have h3 : Cf * (m : ℝ) ^ (1 + rho) ≤ Cf * (m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hpow (by linarith only [hCf])
    linarith only [hnu1, h2, h3]
  have hb : (((nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 / nu) / nu) ≤
      (4 * Cf ^ 2 / nu ^ 2) * ((m : ℝ) ^ 4) := by
    have h4 : (nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 ≤ (2 * Cf * (m : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc _ = (nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 / nu ^ 2 := by field_simp
      _ ≤ (2 * Cf * (m : ℝ) ^ 2) ^ 2 / nu ^ 2 := by gcongr
      _ = _ := by ring
  have hbN : ((((nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 / nu) / nu) ^ N) ≤
      (4 * Cf ^ 2 / nu ^ 2) ^ N * (((m : ℝ) ^ 4) ^ N) := by
    calc _ ≤ ((4 * Cf ^ 2 / nu ^ 2) * ((m : ℝ) ^ 4)) ^ N :=
          Real.rpow_le_rpow (by positivity) hb hN
      _ = _ := Real.mul_rpow hq (by positivity)
  have habs := linfL2c_absorb (N := N) (K0 := CD * (4 * Cf ^ 2 / nu ^ 2) ^ N) hN
    (by positivity) hm'1 hmm hc hnc hk
  calc _ ≤ CD * ((4 * Cf ^ 2 / nu ^ 2) ^ N * (((m : ℝ) ^ 4) ^ N)) * ((3 : ℝ) ^ nb / (3 : ℝ) ^ m') := by
        gcongr
    _ = CD * (4 * Cf ^ 2 / nu ^ 2) ^ N * (((m : ℝ) ^ 4) ^ N) * ((3 : ℝ) ^ nb / (3 : ℝ) ^ m') := by
        ring
    _ ≤ 1 := habs

/-- From an almost-everywhere bound by the oscillation to the normalised norm. -/
theorem linfL2c_ae_to_lpBar [NeZero d] {R : ℝ} (hR : 0 < R)
    (u0 : H1Function (euclidBall (d := d) R)) {C CB : ℝ} (hC : 0 ≤ C) (hCB : C ≤ CB)
    (h : ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (R / 3) R),
      |u0.toFun x| ≤ C * h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun) :
    eLpNorm u0.toFun ⊤ (volume.restrict (decayEst_ann (d := d) (R / 3) R)) ≤
      ENNReal.ofReal CB * lpBar (decayEst_ann (d := d) (R / 4) R) 2
        (fun x => u0.toFun x - ⨍ z in decayEst_ann (d := d) (R / 4) R, u0.toFun z) := by
  have hWafin : volume (decayEst_ann (d := d) (R / 4) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono (decayEst_ann_subset _ _))
  have hWapos : 0 < (volume (decayEst_ann (d := d) (R / 4) R)).toReal :=
    lt_of_lt_of_le (by have := decayEst_volT_ball_pos (d := d) hR; linarith only [this])
      (decayEst_vol_ann_ge hR)
  have hu2 : MemLp u0.toFun 2 (volume.restrict (decayEst_ann (d := d) (R / 4) R)) :=
    u0.memL2.mono_measure (Measure.restrict_mono (decayEst_ann_subset _ _) le_rfl)
  simp only [hr_avg_eq]
  rw [hr_lpBar_eq hWafin hWapos hu2, ← ENNReal.ofReal_mul (by linarith only [hC, hCB])]
  have hmeas : AEStronglyMeasurable u0.toFun (volume.restrict (decayEst_ann (d := d) (R / 3) R)) :=
    u0.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (decayEst_ann_subset _ _) le_rfl)
  rw [eLpNorm_exponent_top hmeas]
  refine le_trans (eLpNormEssSup_le_of_ae_bound (C := C * h1_l2 (decayEst_ann (d := d) (R / 4) R)
    u0.toFun) (by filter_upwards [h] with x hx; simpa [Real.norm_eq_abs] using hx)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right hCB (Real.sqrt_nonneg _)

/-- **The sup bound on the annulus from the boundary estimate** (deterministic part). -/
theorem linfL2c_core (hd : 2 ≤ d) [NeZero d] :
    ∃ CD : ℝ, 0 < CD ∧
      ∀ {lam Lam : ℝ} {a : CoeffField d} {R : ℝ} (u0 : H1Function (euclidBall (d := d) R))
        {sL e n' N m' nc : ℕ} {Mg E1 K cd V2 V3 : ℝ},
        n' + 1 + N + 1 = m' → e + 2 ≤ n' + 1 → n' + 1 ≤ nc → nc < m' → 0 < lam → lam ≤ Lam →
        1 ≤ K → 0 ≤ E1 → 0 < cd → 0 ≤ V2 → 0 ≤ V3 → 0 < R → 0 ≤ Mg →
        8 * (d : ℝ) ≤ (3 : ℝ) ^ e →
        (∀ i : ℕ, i + e + 2 ≤ m' → ∀ x ∈ euclidBall (d := d) R,
          ∃ w ∈ gridPts d (((i + e + 2 : ℕ) : ℤ) - (sL : ℤ)) Mg, w ∈ euclidBall (d := d) R ∧
            ‖x - w‖ ≤ (3 : ℝ) ^ i) →
        (∀ j : ℕ, j ≤ m' → ∀ w ∈ euclidBall (d := d) R,
          ENNReal.ofReal (cd * ((3 : ℝ) ^ j) ^ d) ≤
            volume (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R)) →
        (3 : ℝ) ^ d ≤ K * cd →
        Real.sqrt d * ((3 : ℝ) ^ m' + (3 : ℝ) ^ m' / 2) ≤ R / 12 →
        (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
          V3 * (cd * ((3 : ℝ) ^ (n' + 1 + N)) ^ d) →
        (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤ V2 * (cd * ((3 : ℝ) ^ nc) ^ d) →
        E1 * ((3 : ℝ) ^ nc / (3 : ℝ) ^ m') ≤ 1 / 2 →
        IsEllipticFieldOn lam Lam (euclidBall (d := d) R) a →
        (∀ (V : Set (Vec d)) (hV : IsOpen V) (hVS : V ⊆ euclidBall (d := d) R),
          V ⊆ decayEst_ann (d := d) (R / 8) R →
          IsWeakSolutionOn a V (u0.restrict hV hVS) (fun _ => 0) (fun _ => 0)) →
        (∀ (w : Vec d) (j : ℕ), LocalizedZeroTraceFunctionOn
          (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) (shiftCube w (j : ℤ)) u0.toFun) →
        (∀ j : ℕ, n' + 1 ≤ j → j < m' → ∀ w ∈ gridPts d ((j : ℤ) - (sL : ℤ)) Mg,
          w ∈ euclidBall (d := d) R →
          (∃ x ∈ decayEst_ann (d := d) (R / 3) R, ‖x - w‖ ≤ (3 : ℝ) ^ m') →
          h1_l2 (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) u0.toFun ≤
              E1 * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') *
                (h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun +
                  linfL2b_nl2 (decayEst_ann (d := d) (R / 4) R) u0.toFun) ∧
            (¬ shiftCube w (j : ℤ) ⊆ euclidBall (d := d) R →
              linfL2b_nl2 (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) u0.toFun ≤
                E1 * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') *
                  (h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun +
                    linfL2b_nl2 (decayEst_ann (d := d) (R / 4) R) u0.toFun))) →
        CD * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') ≤ 1 →
        ∀ᵐ x ∂volume.restrict (decayEst_ann (d := d) (R / 3) R),
          |u0.toFun x| ≤ ((Real.sqrt K * (E1 * (1 / 2)) + E1) * (1 + (3 + 2 * Real.sqrt V2)) +
            Real.sqrt V3 * (3 + 2 * Real.sqrt V2)) *
              h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun := by
  obtain ⟨CD, hCD, Hpt⟩ := linfL2c_point hd (d := d)
  refine ⟨CD, hCD, ?_⟩
  intro lam Lam a R u0 sL e n' N m' nc Mg E1 K cd V2 V3 hm' he hnb hnc hlam hLL hK1 hE1 hcd hV2 hV3 hR
    hMg h3e hcovS hdens hK3 hgeo hratio3 hratio2 hθ hell hwS hz0 hLC hAbs
  set D : ℝ := h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun with hD
  set Y : ℝ := linfL2b_nl2 (decayEst_ann (d := d) (R / 4) R) u0.toFun with hY
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := linfL2b_nl2_nonneg _ _
  have hSo : IsOpen (euclidBall (d := d) R) := isOpen_euclidBall R
  have hu2 := u0.memL2
  have hWafin : volume (decayEst_ann (d := d) (R / 4) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono (decayEst_ann_subset _ _))
  have hsd1 : 1 ≤ Real.sqrt d := h1_sqrt_d_pos
  have h3m : (3 : ℝ) ^ m' ≤ R := by
    have hp : (0 : ℝ) < (3 : ℝ) ^ m' := by positivity
    nlinarith only [hgeo, hsd1, hp]
  have h3nc : (3 : ℝ) ^ nc ≤ R := le_trans (pow_le_pow_right₀ (by norm_num) hnc.le) h3m
  -- the norm on the annulus is controlled by the oscillation
  obtain ⟨z0, hz0g, hz0S, hz0cut, x0, hx0A, hx0d⟩ := linfL2c_cut_cell (sL := sL) (e := e) (nc := nc)
    (Mg := Mg) hR (fun i hi => hcovS i (by omega)) (by omega) h3e h3nc
  have hx0R : R / 3 < eucNorm x0 :=
    ((linfL2c_ann_iff (a := R / 3) (b := R) (by positivity) hR).1 hx0A).1
  have hq0 := (hLC nc hnb hnc z0 hz0g hz0S ⟨x0, hx0A, hx0d.trans
    (pow_le_pow_right₀ (by norm_num) hnc.le)⟩).2 hz0cut
  have hq0W : shiftCube z0 (nc : ℤ) ∩ euclidBall (d := d) R ⊆ decayEst_ann (d := d) (R / 4) R := by
    intro y hy
    refine linfL2c_cube_in_ann (j := nc) (ρ := (3 : ℝ) ^ m') hR hx0R
      (hx0d.trans (pow_le_pow_right₀ (by norm_num) hnc.le)) ?_ hy.1 hy.2
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)) hgeo
    have : (3 : ℝ) ^ nc ≤ (3 : ℝ) ^ m' := pow_le_pow_right₀ (by norm_num) hnc.le
    linarith only [this]
  have hvq0 : 0 < (volume (shiftCube z0 (nc : ℤ) ∩ euclidBall (d := d) R)).toReal := by
    have h := hdens nc hnc.le z0 hz0S
    have hfin : volume (shiftCube z0 (nc : ℤ) ∩ euclidBall (d := d) R) ≠ ⊤ :=
      ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono Set.inter_subset_right)
    have := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    exact lt_of_lt_of_le (by positivity) this
  have hratio0 : (volume (decayEst_ann (d := d) (R / 4) R)).toReal /
      (volume (shiftCube z0 (nc : ℤ) ∩ euclidBall (d := d) R)).toReal ≤ V2 := by
    rw [div_le_iff₀ hvq0]
    have h := hdens nc hnc.le z0 hz0S
    have hfin : volume (shiftCube z0 (nc : ℤ) ∩ euclidBall (d := d) R) ≠ ⊤ :=
      ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono Set.inter_subset_right)
    have h2 := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    calc _ ≤ V2 * (cd * ((3 : ℝ) ^ nc) ^ d) := hratio2
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hV2
  have hYD : Y ≤ (3 + 2 * Real.sqrt V2) * D :=
    linfL2c_conv hq0W hWafin hvq0 (hu2.mono_measure
      (Measure.restrict_mono (decayEst_ann_subset _ _) le_rfl)) hratio0 hθ (le_trans hq0 (by
        have := mul_le_mul_of_nonneg_right hθ (add_nonneg hD0 hY0)
        linarith only [this]))
  set M : ℝ := Real.sqrt K * (E1 * (D + Y) * (1 / 2)) + Real.sqrt V3 * Y + E1 * (D + Y) with hMdef
  have hMC : M ≤ ((Real.sqrt K * (E1 * (1 / 2)) + E1) * (1 + (3 + 2 * Real.sqrt V2)) +
      Real.sqrt V3 * (3 + 2 * Real.sqrt V2)) * D := by
    have hc1 : 0 ≤ Real.sqrt K * (E1 * (1 / 2)) + E1 := by positivity
    have h1 : D + Y ≤ (1 + (3 + 2 * Real.sqrt V2)) * D := by linarith only [hYD]
    have h2 : (Real.sqrt K * (E1 * (1 / 2)) + E1) * (D + Y) ≤
        (Real.sqrt K * (E1 * (1 / 2)) + E1) * ((1 + (3 + 2 * Real.sqrt V2)) * D) :=
      mul_le_mul_of_nonneg_left h1 hc1
    have h3 : Real.sqrt V3 * Y ≤ Real.sqrt V3 * ((3 + 2 * Real.sqrt V2) * D) :=
      mul_le_mul_of_nonneg_left hYD (Real.sqrt_nonneg _)
    have e1 : M = (Real.sqrt K * (E1 * (1 / 2)) + E1) * (D + Y) + Real.sqrt V3 * Y := by
      rw [hMdef]; ring
    rw [e1]
    nlinarith only [h2, h3]
  have hpt := Hpt (lam := lam) (Lam := Lam) (a := a) (R := R) u0 (sL := sL) (e := e) (n' := n')
    (N := N) (m' := m') (Mg := Mg) (E1 := E1) (K := K) (cd := cd) (V3 := V3) (D := D) (Y := Y)
    hm' he hlam hLL hK1 hE1 hD0 hY0 hcd hV3 hR hMg hcovS hdens hK3 hgeo hratio3 hell hwS hz0 hLC
    hAbs rfl rfl
  have hall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ z ∈ gridPts d (((n' + 1 : ℕ) : ℤ) - (sL : ℤ)) Mg,
      (z ∈ euclidBall (d := d) R ∧ ∃ x' ∈ decayEst_ann (d := d) (R / 3) R,
        ‖x' - z‖ ≤ (3 : ℝ) ^ (n' + 1 - (e + 2))) →
      x ∈ euclidBall (d := d) R ∩ shiftCube z (n' : ℤ) → |u0.toFun x| ≤ M := by
    rw [Filter.eventually_all_finset]
    intro z hzG
    by_cases hgood : z ∈ euclidBall (d := d) R ∧ ∃ x' ∈ decayEst_ann (d := d) (R / 3) R,
        ‖x' - z‖ ≤ (3 : ℝ) ^ (n' + 1 - (e + 2))
    · have h := hpt z hzG hgood.1 hgood.2
      have hm : MeasurableSet (euclidBall (d := d) R ∩ shiftCube z (n' : ℤ)) :=
        (measurableSet_euclidBall R).inter (rc_isOpen_shiftCube z _).measurableSet
      have := (ae_restrict_iff' hm).1 h
      filter_upwards [this] with x hx _ hxc using hx hxc
    · exact Filter.Eventually.of_forall fun x h => absurd h hgood
  rw [ae_restrict_iff' (decayEst_ann_measurable _ _)]
  filter_upwards [hall] with x hx hxA
  have hxS : x ∈ euclidBall (d := d) R := decayEst_ann_subset _ _ hxA
  obtain ⟨w, hw, hwS, hwd⟩ := hcovS (n' + 1 - (e + 2)) (by omega) x hxS
  have e1 : n' + 1 - (e + 2) + e + 2 = n' + 1 := by omega
  rw [e1] at hw
  have hxc : x ∈ shiftCube w (n' : ℤ) := by
    rw [linfL2c_shiftCube_eq, Metric.mem_ball, dist_eq_norm]
    have h3 : (3 : ℝ) ^ (n' + 1 - (e + 2)) * 3 ≤ (3 : ℝ) ^ n' := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (0 : ℝ) < (3 : ℝ) ^ (n' + 1 - (e + 2)) := by positivity
    linarith only [hwd, h3, h4]
  exact (hx w hw ⟨hwS, x, hxA, hwd⟩ ⟨hxS, hxc⟩).trans hMC


/-- **The `L^∞`-`L²` estimate up to the boundary** (`l.inproof.Linfty.L2`, boundary case, used at
`T:15283`): the type of the hypothesis `hBdry` of `decayEst_linfty`. -/
theorem linfL2_boundary (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hLipB :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ openCubeSet (originCube d 0) →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∀ (A s : ℕ) (B E : ℝ), 0 ≤ B → 0 ≤ E →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ m n m' : ℕ, n < m' → m' ≤ m → m ≤ m' + A →
          (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) → Lhat ≤ (n : ℝ) → X omega ≤ (3 : ℝ) ^ n →
          ∀ t : ℝ, (3 : ℝ) ^ m' ≤ t → t ≤ (3 : ℝ) ^ m →
          ∀ z ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2)), z ∈ t • U →
          ∀ (f g : Vec d → ℝ), ContDiff ℝ 2 g →
          ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ t • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
              (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
              (shiftCube z (m' : ℤ)) (fun x => u.toFun x - g x) →
            ∀ R : ℝ≥0∞,
              R = ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
                  (lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) +
                    lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x)) +
                ENNReal.ofReal (C * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m') *
                  eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) +
                ENNReal.ofReal (C * ((m' : ℝ) - (n : ℝ))) *
                  eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
                ENNReal.ofReal (C * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                  eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
                    (volume.restrict (shiftCube z (m' : ℤ))) →
            -- e.Dir.new.C01.boundary, with the oscillation kept on the left
            ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) ≤ R ∧
              -- on a cube that meets the boundary, the solution itself is flat relative to `g`
              (¬ shiftCube z (n : ℤ) ⊆ t • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R)) :
    ∃ CB : ℝ, 1 ≤ CB ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K ρ : ℝ, 0 < ρ → ρ < 1 →
            ∀ (P : MeasureTheory.ProbabilityMeasure
                  (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
              (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
              (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
              (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
              SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
              SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
              SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                  hPrefix hJ2 hJ3 →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧
                (∃ Ct : ℝ, 1 ≤ Ct ∧ ∀ t : ℝ, 2 ≤ t →
                  P.toMeasure.real {ω | t < X ω} ≤
                    Ct * Real.exp (-(Ct⁻¹ * Real.log t ^ ρ))) ∧
                ∀ᵐ ω ∂P.toMeasure, ∀ R : ℝ, X ω ≤ R →
                  ∀ u : H10Function (euclidBall (d := d) R),
                    IsWeakSolutionOn (fullCoefficientRecentered nu ω)
                        (decayEst_ann (R / 8) R)
                        (u.toH1Function.restrict (decayEst_ann_isOpen _ _)
                          (decayEst_ann_subset _ _)) (fun _ => 0) (fun _ => 0) →
                    eLpNorm u.toH1Function.toFun ⊤
                        (volume.restrict (decayEst_ann (d := d) (R / 3) R)) ≤
                      ENNReal.ofReal CB *
                        lpBar (decayEst_ann (d := d) (R / 4) R) 2
                          (fun x => u.toH1Function.toFun x -
                            ⨍ z in decayEst_ann (d := d) (R / 4) R, u.toH1Function.toFun z) := by
  classical
  have hU : IsSmoothBoundedDomain (euclidBall (d := d) (1 / 2)) :=
    w0_isSmoothBoundedDomain_euclidBall (by norm_num)
  have hUc : euclidBall (d := d) (1 / 2) ⊆ openCubeSet (originCube d 0) := by
    intro y hy
    rw [← rc_shiftCube_zero, rc_mem_shiftCube]
    intro i
    have h1 := (linfL2b_mem_euclidBall (by norm_num : (0 : ℝ) < 1 / 2)).1 hy
    have h2 : |y i - (0 : Vec d) i| ≤ ‖y‖ := by
      simpa using norm_le_pi_norm y i
    have h3 := linfL2b_norm_le_euc y
    have h4 : (3 : ℝ) ^ (0 : ℤ) / 2 = 1 / 2 := by norm_num
    rw [h4]
    linarith only [h1, h2, h3]
  obtain ⟨CL, hCL1, HL⟩ := hLipB _ hU hUc
  obtain ⟨sc, cc, hcc, hcov⟩ := linf_fine_cover hU
  obtain ⟨cd, hcd, hdens⟩ := linf_density hU
  obtain ⟨CD, hCD, Hcore⟩ := linfL2c_core hd (d := d)
  obtain ⟨Cf, hCf1, HF⟩ := linf_field d hd
    (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
  have hNn0 : 0 ≤ deGiorgiPower d := inv_nonneg.2 (one_sub_two_div_sobStar_pos hd).le
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (8 * (d : ℝ)) (by norm_num : (1 : ℝ) < 3)
  have hC0def : ∃ C0 : ℝ, C0 = max (30 * (d : ℝ)) (1 / (2 * cc)) := ⟨_, rfl⟩
  obtain ⟨C0, hC0eq⟩ := hC0def
  have hC0d : 30 * (d : ℝ) ≤ C0 := by rw [hC0eq]; exact le_max_left _ _
  have hC0c : 1 / (2 * cc) ≤ C0 := by rw [hC0eq]; exact le_max_right _ _
  have hC0 : 1 ≤ C0 := by linarith only [hC0d, hd1]
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (6 * C0) (by norm_num : (1 : ℝ) < 3)
  obtain ⟨ωv, hωv⟩ : ∃ ωv : ℝ, ωv = (volume (euclidBall (d := d) 1)).toReal := ⟨_, rfl⟩
  have hωpos : 0 < ωv := by rw [hωv]; exact decayEst_volT_ball_pos one_pos
  obtain ⟨V0, hV0⟩ : ∃ V0 : ℝ, V0 = ωv * (3 * C0) ^ d / cd := ⟨_, rfl⟩
  have hV00 : 0 ≤ V0 := by rw [hV0]; positivity
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = CL * Real.sqrt V0 := ⟨_, rfl⟩
  have hE10 : 0 ≤ E1 := by rw [hE1]; positivity
  obtain ⟨j0, hj0⟩ := pow_unbounded_of_one_lt (2 * E1 + 1) (by norm_num : (1 : ℝ) < 3)
  have hj01 : 1 ≤ j0 := by
    rcases Nat.eq_zero_or_pos j0 with h | h
    · subst h; norm_num at hj0; linarith only [hj0, hE10]
    · exact h
  obtain ⟨V2, hV2⟩ : ∃ V2 : ℝ, V2 = V0 * ((3 : ℝ) ^ j0) ^ d := ⟨_, rfl⟩
  obtain ⟨V3, hV3⟩ : ∃ V3 : ℝ, V3 = V0 * (3 : ℝ) ^ d := ⟨_, rfl⟩
  have hV20 : 0 ≤ V2 := by rw [hV2]; positivity
  have hV30 : 0 ≤ V3 := by rw [hV3]; positivity
  obtain ⟨Kk, hKk⟩ : ∃ Kk : ℝ, Kk = max 1 ((3 : ℝ) ^ d / cd) := ⟨_, rfl⟩
  have hKk1 : 1 ≤ Kk := by rw [hKk]; exact le_max_left _ _
  have hKk3 : (3 : ℝ) ^ d ≤ Kk * cd := by
    have : (3 : ℝ) ^ d / cd ≤ Kk := by rw [hKk]; exact le_max_right _ _
    rwa [div_le_iff₀ hcd] at this
  obtain ⟨Cfin, hCfin⟩ : ∃ Cfin : ℝ, Cfin = (Real.sqrt Kk * (E1 * (1 / 2)) + E1) *
      (1 + (3 + 2 * Real.sqrt V2)) + Real.sqrt V3 * (3 + 2 * Real.sqrt V2) := ⟨_, rfl⟩
  have hCfin0 : 0 ≤ Cfin := by rw [hCfin]; positivity
  refine ⟨max 1 Cfin, le_max_left _ _, ?_⟩
  intro nu hnu hnu1 cStar hcs Kc rho hrho hrho1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hN'0 : (0 : ℝ) ≤ 4 * deGiorgiPower d + 1 := by linarith only [hNn0]
  obtain ⟨Lhat₁, hL₁1, hP₁⟩ := HL nu hnu hnu1 cStar hcs Kc 1 rho one_pos le_rfl hrho hrho1 A
    (sc + e + 2) (4 * deGiorgiPower d + 1 + 1) 0 (by linarith only [hNn0]) le_rfl
  obtain ⟨X₁, hX₁m, hX₁1, hX₁O, hae₁⟩ := hP₁ P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Lhat₂, hL₂1, hP₂⟩ := HF nu hnu hnu1 cStar hcs Kc 1 rho Cf one_pos le_rfl hrho hrho1 le_rfl
  obtain ⟨X₂, hX₂m, hX₂1, hX₂O, hae₂⟩ := hP₂ P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Lhat₁ + Lhat₂ +
      CD * (4 * Cf ^ 2 / nu ^ 2) ^ deGiorgiPower d * (2 : ℝ) ^ (4 * deGiorgiPower d) + A + e + 5 +
        (3 : ℝ) ^ (j0 + 1) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  obtain ⟨Ct₁, hCt₁, hT₁⟩ := ms_scale_tail P.toMeasure (X₀ := X₁) (Λ := Lhat₁) (ρ := rho)
    (σ := rho) (N₀ := 4 * deGiorgiPower d + 1) (L := L) (C₀ := C0) hX₁1
    (by linarith only [hL₁1]) hrho le_rfl hN'0 hL0 hC0 hX₁O
  obtain ⟨Ct₂, hCt₂, hT₂⟩ := ms_scale_tail P.toMeasure (X₀ := X₂) (Λ := Lhat₂) (ρ := rho)
    (σ := rho) (N₀ := 4 * deGiorgiPower d + 1) (L := L) (C₀ := C0) hX₂1
    (by linarith only [hL₂1]) hrho le_rfl hN'0 hL0 hC0 hX₂O
  have hT₁' : ∀ t : ℝ, 2 ≤ t → P.toMeasure.real {ω | t < C0 * (3 : ℝ) ^ ms_star
      (4 * deGiorgiPower d + 1) L (X₁ ω)} ≤ Ct₁ * Real.exp (-(Ct₁⁻¹ * Real.log t ^ rho)) :=
    fun t ht => (measureReal_mono (fun ω (hω : t < _) => le_of_lt hω)).trans
      (hT₁ t (by linarith only [ht]))
  have hT₂' : ∀ t : ℝ, 2 ≤ t → P.toMeasure.real {ω | t < C0 * (3 : ℝ) ^ ms_star
      (4 * deGiorgiPower d + 1) L (X₂ ω)} ≤ Ct₂ * Real.exp (-(Ct₂⁻¹ * Real.log t ^ rho)) :=
    fun t ht => (measureReal_mono (fun ω (hω : t < _) => le_of_lt hω)).trans
      (hT₂ t (by linarith only [ht]))
  have tmax := decayEst_tail_max (μ := P.toMeasure) hCt₁ hCt₂ hT₁' hT₂'
  refine ⟨fun ω => max (C0 * (3 : ℝ) ^ ms_star (4 * deGiorgiPower d + 1) L (X₁ ω))
      (C0 * (3 : ℝ) ^ ms_star (4 * deGiorgiPower d + 1) L (X₂ ω)), ?_, ?_,
    ⟨Ct₁ + Ct₂, by linarith only [hCt₁, hCt₂], tmax⟩, ?_⟩
  · exact (measurable_const.mul
      ((measurable_from_nat (f := fun k : ℕ => (3 : ℝ) ^ k)).comp
        (ms_star_measurable hN'0 hX₁1 hX₁m))).max
      (measurable_const.mul
      ((measurable_from_nat (f := fun k : ℕ => (3 : ℝ) ^ k)).comp
        (ms_star_measurable hN'0 hX₂1 hX₂m)))
  · intro ω
    have : (1 : ℝ) ≤ (3 : ℝ) ^ ms_star (4 * deGiorgiPower d + 1) L (X₁ ω) :=
      one_le_pow₀ (by norm_num)
    exact le_max_of_le_left (by nlinarith only [hC0, this])
  filter_upwards [hae₁, hae₂, linfL2c_weak_centred hJ3 hnu] with ω hω1 hω2 hω3
  intro R hRX u hwu
  have hr₁ : C0 * (3 : ℝ) ^ ms_star (4 * deGiorgiPower d + 1) L (X₁ ω) ≤ R :=
    le_trans (le_max_left _ _) hRX
  have hr₂ : C0 * (3 : ℝ) ^ ms_star (4 * deGiorgiPower d + 1) L (X₂ ω) ≤ R :=
    le_trans (le_max_right _ _) hRX
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hr₁
  obtain ⟨m', hj, hLm, hX1m, hX2m, h3n, h3n1⟩ :=
    linfL2c_scale2 hN'0 (hX₁1 ω) (hX₂1 ω) hC0 hr₁ hr₂
  -- the scales
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ, c = ⌈(4 * deGiorgiPower d + 1) * Real.log (m' : ℝ)⌉₊ := ⟨_, rfl⟩
  have hnK : nK (4 * deGiorgiPower d + 1) m' = m' - c := by rw [hcdef]; rfl
  have hj' : (4 * (4 * deGiorgiPower d + 1) + 2) ^ 2 ≤ (m' : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have hcm := ceil_le_half hN'0 hj'
  rw [← hcdef] at hcm
  have hcm' : c ≤ m' := by
    have : (c : ℝ) ≤ m' := by linarith only [hcm, Nat.cast_nonneg (α := ℝ) c]
    exact_mod_cast this
  rw [hnK, Nat.cast_sub hcm'] at hLm
  have hLm' : L ≤ (m' : ℝ) - c := hLm
  have hLparts : (3 : ℝ) ^ (j0 + 1) ≤ (m' : ℝ) - c ∧ (A : ℝ) + e + 5 ≤ (m' : ℝ) - c ∧
      CD * (4 * Cf ^ 2 / nu ^ 2) ^ deGiorgiPower d * (2 : ℝ) ^ (4 * deGiorgiPower d) ≤
        (m' : ℝ) - c ∧ Lhat₁ ≤ (m' : ℝ) - c ∧ Lhat₂ ≤ (m' : ℝ) - c := by
    have h1 : 0 ≤ CD * (4 * Cf ^ 2 / nu ^ 2) ^ deGiorgiPower d * (2 : ℝ) ^ (4 * deGiorgiPower d) :=
      by positivity
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (j0 + 1) := by positivity
    have h3 : (0 : ℝ) ≤ A + e := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hLm', hLdef, h1, h2, h3, hL₁1, hL₂1]
  obtain ⟨hL3, hLA, hLK, hLL1, hLL2⟩ := hLparts
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hm'3 : (3 : ℝ) ^ (j0 + 1) ≤ m' := by linarith only [hL3, hcR]
  have hm'1 : (1 : ℝ) ≤ m' := le_trans (one_le_pow₀ (by norm_num)) hm'3
  have hm'pos : (0 : ℝ) < m' := lt_of_lt_of_le (by positivity) hm'3
  have hlog : (j0 + 1 : ℝ) ≤ Real.log (m' : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hm'3
    rw [Real.log_pow] at h1
    have := linfL2c_log_three
    have h2 : (0 : ℝ) ≤ (j0 : ℝ) + 1 := by positivity
    push_cast at h1
    nlinarith only [h1, this, h2]
  have hcj : (j0 : ℝ) + 1 ≤ c := by
    have h1 : (4 * deGiorgiPower d + 1) * Real.log (m' : ℝ) ≤ c := by
      rw [hcdef]; exact Nat.le_ceil _
    have h2 : Real.log (m' : ℝ) ≤ (4 * deGiorgiPower d + 1) * Real.log (m' : ℝ) := by
      nlinarith only [hNn0, hlog, hj01]
    linarith only [h1, h2, hlog]
  have hcj' : j0 + 1 ≤ c := by exact_mod_cast hcj
  have hc1 : (c : ℝ) < (4 * deGiorgiPower d + 1) * Real.log (m' : ℝ) + 1 := by
    rw [hcdef]
    exact Nat.ceil_lt_add_one (mul_nonneg hN'0 (Real.log_nonneg (hm'1)))
  -- the cell scales
  obtain ⟨nb, hnb⟩ : ∃ nb : ℕ, nb = m' - c := ⟨_, rfl⟩
  have hnbc : nb + c = m' := by omega
  have hnbR : (nb : ℝ) = (m' : ℝ) - c := by rw [hnb, Nat.cast_sub hcm']
  have he2 : e + 2 ≤ nb := by
    have : (e : ℝ) + 2 ≤ nb := by rw [hnbR]; linarith only [hLA, hcR, Nat.cast_nonneg (α := ℝ) A]
    exact_mod_cast this
  have hnbK : nK (4 * deGiorgiPower d + 1) m' = nb := by rw [hnK, hnb]
  rw [hnbK] at hX1m hX2m
  obtain ⟨n', hn'⟩ : ∃ n' : ℕ, nb = n' + 1 := ⟨nb - 1, by omega⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, c = N + 1 := ⟨c - 1, by omega⟩
  have hm'eq : n' + 1 + N + 1 = m' := by omega
  have hncle : n' + 1 ≤ m' - j0 := by omega
  have hncl : m' - j0 < m' := by omega
  -- the real scale
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = m' + A := ⟨_, rfl⟩
  have h3m' : (3 : ℝ) ^ m' ≤ R / C0 := h3n
  have hRC : R / C0 ≤ R := div_le_self hRpos.le hC0
  have ht1 : (3 : ℝ) ^ m' ≤ 2 * R := by linarith only [h3m', hRC, hRpos]
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ m' := by positivity
  have ht2 : 2 * R ≤ (3 : ℝ) ^ m := by
    have h1 : R < C0 * (3 : ℝ) ^ (m' + 1) := by
      have := h3n1
      rw [div_lt_iff₀ (by linarith only [hC0])] at this
      linarith only [this]
    have h2 : (3 : ℝ) ^ (m' + 1) = 3 * (3 : ℝ) ^ m' := by ring
    have h3 : (3 : ℝ) ^ m = (3 : ℝ) ^ m' * (3 : ℝ) ^ A := by rw [hm, pow_add]
    nlinarith only [h1, h2, h3, hA, h3pos, hC0]
  have hgeo : Real.sqrt d * ((3 : ℝ) ^ m' + (3 : ℝ) ^ m' / 2) ≤ R / 12 := by
    have hs0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
    have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le
    have h1 : (3 : ℝ) ^ m' * C0 ≤ R := by
      have := h3m'; rw [le_div_iff₀ (by linarith only [hC0])] at this; exact this
    have h2 : 30 * Real.sqrt d ≤ C0 := by
      have : Real.sqrt d ≤ d := by nlinarith only [hss, hs0, hd1]
      linarith only [hC0d, this]
    have h3 : 30 * Real.sqrt d * (3 : ℝ) ^ m' ≤ R := by
      calc 30 * Real.sqrt d * (3 : ℝ) ^ m' ≤ C0 * (3 : ℝ) ^ m' :=
            mul_le_mul_of_nonneg_right h2 h3pos.le
        _ ≤ R := by linarith only [h1]
    nlinarith only [h3, hs0, h3pos]
  have hS : (2 * R) • euclidBall (d := d) (1 / 2) = euclidBall (d := d) R := by
    rw [decayEst_euclidBall_smul (by positivity) (1 / 2)]
    congr 1; ring
  have hMg : (0 : ℝ) ≤ (3 : ℝ) ^ (m + 2) := by positivity
  have hball_coord : ∀ w ∈ euclidBall (d := d) R, ∀ k : Fin d, |w k| ≤ (3 : ℝ) ^ (m + 2) := by
    intro w hw k
    have h1 := (linfL2b_mem_euclidBall hRpos).1 hw
    have h2 : |w k| ≤ ‖w‖ := by simpa using norm_le_pi_norm w k
    have h3 := linfL2b_norm_le_euc w
    have h4 : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [h1, h2, h3, h4, ht2, hRpos]
  have hcovS : ∀ i : ℕ, i + e + 2 ≤ m' → ∀ x ∈ euclidBall (d := d) R,
      ∃ w ∈ gridPts d (((i + e + 2 : ℕ) : ℤ) - ((sc + e + 2 : ℕ) : ℤ)) ((3 : ℝ) ^ (m + 2)),
        w ∈ euclidBall (d := d) R ∧ ‖x - w‖ ≤ (3 : ℝ) ^ i := by
    intro i hi x hx
    have hc : (3 : ℝ) ^ i ≤ cc * (2 * R) := by
      have h1 : (3 : ℝ) ^ i ≤ (3 : ℝ) ^ m' := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : 1 ≤ C0 * (2 * cc) := by
        have := hC0c
        rw [div_le_iff₀ (by positivity)] at this
        linarith only [this]
      have h4 : R ≤ C0 * (2 * cc) * R := by nlinarith only [h2, hRpos]
      have h5 : R / C0 ≤ cc * (2 * R) := by
        rw [div_le_iff₀ (by linarith only [hC0])]
        linarith only [h4]
      linarith only [h1, h3n, h5]
    obtain ⟨w, hwg, hwU, hwd⟩ := linfL2c_cover_pt (U := euclidBall (d := d) (1 / 2)) hcov e i
      (t := 2 * R) (M := (3 : ℝ) ^ (m + 2)) (by positivity) hMg hc
      (fun w hw k => hball_coord w (by rw [hS] at hw; exact hw) k) (x := x)
      (by rw [hS]; exact hx)
    exact ⟨w, hwg, by rw [hS] at hwU; exact hwU, hwd⟩
  have hdens' : ∀ j : ℕ, j ≤ m' → ∀ w ∈ euclidBall (d := d) R,
      ENNReal.ofReal (cd * ((3 : ℝ) ^ j) ^ d) ≤
        volume (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) := by
    intro j hj w hw
    have h := hdens (2 * R) j (le_trans (pow_le_pow_right₀ (by norm_num) hj) ht1) w
      (by rw [hS]; exact hw)
    rw [hS] at h
    exact h
  -- the volume of the annulus
  have hWa : (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
      ωv * (3 * C0) ^ d * ((3 : ℝ) ^ m') ^ d := by
    have h1 : (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
        (volume (euclidBall (d := d) R)).toReal :=
      ENNReal.toReal_mono (h1_vol_ball_ne_top hRpos) (measure_mono (decayEst_ann_subset _ _))
    rw [decayEst_volT_ball hRpos, ← hωv] at h1
    have h2 : R ≤ 3 * C0 * (3 : ℝ) ^ m' := by
      have := h3n1
      rw [div_lt_iff₀ (by linarith only [hC0])] at this
      have e3 : (3 : ℝ) ^ (m' + 1) = 3 * (3 : ℝ) ^ m' := by ring
      rw [e3] at this
      linarith only [this]
    have h3 : R ^ d ≤ (3 * C0 * (3 : ℝ) ^ m') ^ d := pow_le_pow_left₀ hRpos.le h2 d
    calc _ ≤ R ^ d * ωv := h1
      _ ≤ (3 * C0 * (3 : ℝ) ^ m') ^ d * ωv := mul_le_mul_of_nonneg_right h3 hωpos.le
      _ = _ := by rw [mul_pow]; ring
  have hV1' : (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
      V0 * (cd * ((3 : ℝ) ^ m') ^ d) := by
    have : V0 * (cd * ((3 : ℝ) ^ m') ^ d) = ωv * (3 * C0) ^ d * ((3 : ℝ) ^ m') ^ d := by
      rw [hV0]; field_simp
    rw [this]; exact hWa
  have hratio3 : (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
      V3 * (cd * ((3 : ℝ) ^ (n' + 1 + N)) ^ d) := by
    have : V3 * (cd * ((3 : ℝ) ^ (n' + 1 + N)) ^ d) = ωv * (3 * C0) ^ d * ((3 : ℝ) ^ m') ^ d := by
      rw [hV3, hV0, ← hm'eq, pow_succ (3 : ℝ) (n' + 1 + N), mul_pow]; field_simp; rw [mul_pow, mul_comm]
    rw [this]; exact hWa
  have hratio2 : (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
      V2 * (cd * ((3 : ℝ) ^ (m' - j0)) ^ d) := by
    have : V2 * (cd * ((3 : ℝ) ^ (m' - j0)) ^ d) = ωv * (3 * C0) ^ d * ((3 : ℝ) ^ m') ^ d := by
      have e5 : (3 : ℝ) ^ m' = (3 : ℝ) ^ (m' - j0) * (3 : ℝ) ^ j0 := by
        rw [← pow_add]; congr 1; omega
      rw [hV2, hV0, e5]; field_simp; ring
    rw [this]; exact hWa
  -- the field
  have hXm : X₂ ω ≤ (3 : ℝ) ^ m :=
    le_trans hX2m (pow_le_pow_right₀ (by norm_num) (by omega))
  have hLm2 : Lhat₂ ≤ (m : ℝ) := by
    have : (m' : ℝ) ≤ m := by rw [hm]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) A]
    linarith only [hLL2, hcR, this]
  obtain ⟨-, hellc⟩ := hω2 m hXm hLm2
  have hsub : euclidBall (d := d) R ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro y hy
    rw [← rc_shiftCube_zero, rc_mem_shiftCube]
    intro i
    have h1 := (linfL2b_mem_euclidBall hRpos).1 hy
    have h2 : |y i - (0 : Vec d) i| ≤ ‖y‖ := by simpa using norm_le_pi_norm y i
    have h3 := linfL2b_norm_le_euc y
    have h4 : (3 : ℝ) ^ (m : ℤ) / 2 = (3 : ℝ) ^ m / 2 := by rw [zpow_natCast]
    rw [h4]
    linarith only [h1, h2, h3, ht2]
  have hell := wh2_isEllipticFieldOn_mono (measurableSet_euclidBall R) hsub hellc
  have hwR : ∀ (V : Set (Vec d)) (hV : IsOpen V) (hVS : V ⊆ euclidBall (d := d) R),
      V ⊆ decayEst_ann (d := d) (R / 8) R →
      IsWeakSolutionOn (fullCoefficientRecentered nu ω) V (u.toH1Function.restrict hV hVS)
        (fun _ => 0) (fun _ => 0) :=
    fun V hV hVS hVA => decayEst_weak_restrict hV hVA hwu
  have hwS := hω3 m hRpos u.toH1Function hwR
  have hz0 : ∀ (w : Vec d) (j : ℕ), LocalizedZeroTraceFunctionOn
      (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) (shiftCube w (j : ℤ))
      u.toH1Function.toFun := fun w j => linfL2c_zero_trace u w j
  -- the boundary estimate
  have hBn : (m' : ℝ) - (4 * deGiorgiPower d + 1 + 1) * Real.log (m' : ℝ) ≤ (nb : ℝ) := by
    rw [hnbR]
    nlinarith only [hc1, hlog, hj01]
  have hLC := linfL2c_lip_wa hω1 (by linarith only [hCL1]) hRpos hS u.toH1Function
    (m := m) (m' := m') (nb := nb) (by omega) (by omega) hBn (by rw [hnbR]; linarith only [hLL1])
    hX1m ht1 ht2 hcd hV00 hdens' hV1' hgeo hwR hz0
  rw [← hE1, hn'] at hLC
  -- the absorption
  have hmm : m ≤ 2 * m' := by
    have : A ≤ m' := by
      have : (A : ℝ) ≤ m' := by linarith only [hLA, hcR, Nat.cast_nonneg (α := ℝ) e]
      exact_mod_cast this
    omega
  have hm1 : 1 ≤ m := by omega
  have hm'1' : 1 ≤ m' := by exact_mod_cast hm'1
  have hk : CD * (4 * Cf ^ 2 / nu ^ 2) ^ deGiorgiPower d * (2 : ℝ) ^ (4 * deGiorgiPower d) ≤
      (m' : ℝ) := by linarith only [hLK, hcR]
  have hAbs := linfL2c_absorb_ell (N := deGiorgiPower d) (Cf := Cf) (CD := CD) (nu := nu)
    (rho := rho) hNn0 hCf1 hCD.le hnu hnu1 hrho1 hm'1' hmm hm1 hcdef hnbc hk
  rw [hn'] at hAbs
  have hθ : E1 * ((3 : ℝ) ^ (m' - j0) / (3 : ℝ) ^ m') ≤ 1 / 2 := by
    have e5 : (3 : ℝ) ^ m' = (3 : ℝ) ^ (m' - j0) * (3 : ℝ) ^ j0 := by
      rw [← pow_add]; congr 1; omega
    have h6 : (3 : ℝ) ^ (m' - j0) / (3 : ℝ) ^ m' = 1 / (3 : ℝ) ^ j0 := by
      rw [e5]; field_simp
    rw [h6, mul_one_div, div_le_iff₀ (by positivity)]
    linarith only [hj0, hE10]
  have hLL : nu ≤ (nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 / nu := by
    rw [le_div_iff₀ hnu]
    have : (0 : ℝ) ≤ Cf * (m : ℝ) ^ (1 + rho) := by positivity
    nlinarith only [this, hnu]
  have hcore := Hcore (lam := nu) (Lam := (nu + Cf * (m : ℝ) ^ (1 + rho)) ^ 2 / nu)
    (a := fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
      ω (cubeSet (originCube d (m : ℤ))) x) (R := R) u.toH1Function (sL := sc + e + 2) (e := e)
    (n' := n') (N := N) (m' := m') (nc := m' - j0) (Mg := (3 : ℝ) ^ (m + 2)) (E1 := E1)
    (K := Kk) (cd := cd) (V2 := V2) (V3 := V3) hm'eq (by omega) hncle hncl hnu hLL hKk1 hE10 hcd
    hV20 hV30 hRpos hMg (le_of_lt he) hcovS hdens' hKk3 hgeo hratio3 hratio2 hθ hell hwS hz0 hLC
    hAbs
  rw [← hCfin] at hcore
  exact linfL2c_ae_to_lpBar hRpos u.toH1Function hCfin0 (le_max_right 1 Cfin) hcore

/-- Satisfiability of the hypotheses of the conclusion: the zero function of the ball is an `H¹₀`
weak solution of every recentred field on the annulus, for every radius. -/
example (nu : ℝ) (omega : ShellSeq d) (R : ℝ) :
    ∃ u : H10Function (euclidBall (d := d) R),
      IsWeakSolutionOn (fullCoefficientRecentered nu omega) (decayEst_ann (R / 8) R)
        (u.toH1Function.restrict (decayEst_ann_isOpen _ _) (decayEst_ann_subset _ _))
        (fun _ => 0) (fun _ => 0) := by
  have hz : ∀ (x : Vec d) (j : Fin d),
      (H10Function.toH1Function (0 : H10Function (euclidBall (d := d) R))).grad x j = 0 :=
    fun _ _ => rfl
  refine ⟨0, fun φ => ?_⟩
  simp [H1Function.restrict, vecDot, matVecMul, hz]

end SuperdiffusionCLT.Section8
