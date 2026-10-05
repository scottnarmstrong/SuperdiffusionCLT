/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD6
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyB
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyB2
public import SuperdiffusionCLT.Section4.MinimalScales.NearSkewMaxE
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

/-!
# Arithmetic blocks of the near-scale bound `hNear`

Self-contained real-arithmetic pieces of `srootNS_hNear` (in `NearShiftAssemblyD7.lean`):
the cap condition, and the two amplitude estimates of the final assembly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- The constants of `hNear` are dominated by the threshold constant. -/
theorem srootNSD7_consts {Aw Ask A0 U0 c3 Q2 e1c A1 Cp g3 Abig C1 : ℝ}
    (hAw1 : 1 ≤ Aw) (hAsk1 : 1 ≤ Ask) (hA01 : 1 ≤ A0) (hU0n : 0 ≤ U0) (hc3n : 0 ≤ c3)
    (hQ2n : 0 ≤ Q2) (he1n : 0 ≤ e1c) (hA1n : 0 ≤ A1) (hA2n : 0 ≤ Cp * (2 * Ask + 44))
    (hA3n : 0 ≤ g3 * (1 + 16384 * A0))
    (hAbig : Abig = 20000 + Aw + Ask + A0 + U0 + c3 + Q2 + e1c + Cp * (2 * Ask + 44) + A1 +
      g3 * (1 + 16384 * A0))
    (hC1 : Abig ≤ C1) :
    Aw ≤ C1 ∧ 20000 ≤ C1 ∧ Ask ≤ C1 ∧ U0 ≤ C1 ∧ c3 ≤ C1 ∧ Q2 ≤ C1 ∧ e1c ≤ C1 ∧ A1 ≤ Abig ∧
      Cp * (2 * Ask + 44) ≤ Abig ∧ g3 * (1 + 16384 * A0) ≤ Abig := by
  rw [hAbig] at hC1 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hC1, hAw1, hAsk1, hA01, hU0n, hc3n, hQ2n, he1n, hA1n, hA2n, hA3n]

/-- The cap condition of the near-scale bound: `log` of the cardinality cap, and the
product bound `Au * Bv * ... ≤ m ^ (-4900)`. -/
theorem srootNSD7_cap {d Nl hbar h m : ℕ}
    {C0 Cp Ask cE ctc g1 K s lg σ c3 Q2 U0 C1 : ℝ}
    (hNldef : Nl = hbar + 1) (hhbar2 : (hbar : ℝ) ≤ 2 * C0 * s⁻¹ * lg) (hC0 : 1 ≤ C0)
    (hs0 : 0 < s) (hK1 : 1 ≤ K) (hlg1 : 1 ≤ lg) (hPm : s⁻¹ * K * lg ≤ (m : ℝ))
    (hm1 : (1 : ℝ) ≤ m) (hm64 : (64 : ℝ) ≤ m) (hdn : (0 : ℝ) ≤ d)
    (hc3 : c3 = 3 * (2 + 3 * C0 * (1 + 2 * (d : ℝ))))
    (hcE : 1 ≤ cE) (hg1 : 0 < g1) (hAsk1 : 1 ≤ Ask) (hlgm : lg ≤ (m : ℝ))
    (hKlg : K * lg ≤ (m : ℝ)) (hlog2h : Real.log (2 * (h : ℝ)) ≤ lg)
    (hlg20 : 0 ≤ Real.log (2 * (h : ℝ))) (hu0 : 0 ≤ σ⁻¹) (hu : σ⁻¹ ≤ 2 * cE * m)
    (hU0 : U0 = g1 * (1 + 6 * cE * Ask)) (hCp1 : 1 ≤ Cp) (hcE0 : 0 < cE) (hctc0 : 0 ≤ ctc)
    (hQ2 : Q2 = Cp * (2 : ℝ) ^ (5000 : ℝ) + 16 * cE ^ 2 * ctc)
    (hmC1 : C1 ≤ (m : ℝ)) (hU0C : U0 ≤ C1) (hc3C : c3 ≤ C1) (hQ2C : Q2 ≤ C1)
    (hU0n : 0 ≤ U0) (hc3n : 0 ≤ c3) (hQ2n : 0 ≤ Q2) (hCpp : 0 < Cp) (hmpos : (0 : ℝ) < m) :
    3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl))) ≤ c3 * m ∧
    0 ≤ 3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl))) ∧
    (g1 * ((1 + (σ⁻¹ + 1) * (Ask * (K * lg * Real.log (2 * (h : ℝ))))) +
      (σ⁻¹ + 1) * (Ask * (s⁻¹ * K * lg)))) *
      ((3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl)))) ^
        ((1 / 3 : ℝ)⁻¹) * (Cp * ((m : ℝ) / 2) ^ (-(5000 : ℝ)) +
          (16 * cE ^ 2 * ctc) * (m : ℝ) ^ (-(5000 : ℝ)))) ≤ (m : ℝ) ^ (-(4900 : ℝ)) := by
  have hNl : 0 < Nl := by rw [hNldef]; exact Nat.succ_pos _
  have hslg : s⁻¹ * lg ≤ m := by
    have h1 : lg ≤ K * lg := by
      have := mul_le_mul_of_nonneg_right hK1 (by linarith only [hlg1] : (0 : ℝ) ≤ lg)
      linarith only [this]
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs0.le)
    have e : s⁻¹ * (K * lg) = s⁻¹ * K * lg := by ring
    linarith only [h2, e, hPm]
  have hNlR : (Nl : ℝ) ≤ 3 * C0 * m := by
    rw [hNldef]; push_cast
    have h1 : (hbar : ℝ) ≤ 2 * C0 * (s⁻¹ * lg) := by
      have e : 2 * C0 * s⁻¹ * lg = 2 * C0 * (s⁻¹ * lg) := by ring
      linarith only [hhbar2, e]
    have h2 : 2 * C0 * (s⁻¹ * lg) ≤ 2 * C0 * m :=
      mul_le_mul_of_nonneg_left hslg (by linarith only [hC0])
    have h3 : 1 ≤ C0 * m := one_le_mul_of_one_le_of_one_le hC0 hm1
    linarith only [h1, h2, h3]
  have hlog3 := srootNSD_log_Ncap (m := (m : ℝ)) (C0 := C0) (d := (d : ℝ)) (Nl := Nl)
    (by linarith only [hm64]) hdn hNl hNlR d rfl
  rw [← hc3] at hlog3
  have hLg0 : 0 ≤ 3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl))) := by
    have := Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left 2
      ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl))))
    linarith only [this]
  have hAuLe := srootNSD_Au_le (cE := cE) (g1 := g1) (Ask := Ask) (K := K) (lg := lg)
    (lg2 := Real.log (2 * (h : ℝ))) (t := s⁻¹) (u := σ⁻¹) (m := (m : ℝ)) hm1 hcE hg1.le
    (by linarith only [hAsk1]) hK1 hlg1 hlgm hKlg hPm hlog2h hlg20 (inv_nonneg.2 hs0.le) hu0 hu
  rw [← hU0] at hAuLe
  have hBvLe := srootNSD_Bv_le (Cp := Cp) (cE := cE) (ctc := ctc) (c3 := c3) (m := (m : ℝ))
    (Lg := 3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl))))
    (βB := (16 * cE ^ 2 * ctc) * (m : ℝ) ^ (-(5000 : ℝ))) hm1 (by linarith only [hCp1]) hLg0
    hlog3 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hcE0.le 2)) hctc0)
      (Real.rpow_nonneg hmpos.le _)) le_rfl
  rw [← hQ2] at hBvLe
  refine ⟨hlog3, hLg0, ?_⟩
  refine srootNSD_cap_cond hm1 ?_ hAuLe hBvLe (hU0C.trans hmC1) (hc3C.trans hmC1)
    (hQ2C.trans hmC1) hU0n hc3n hQ2n
  have h1 : 0 ≤ Cp * ((m : ℝ) / 2) ^ (-(5000 : ℝ)) :=
    mul_nonneg hCpp.le (Real.rpow_nonneg (half_pos hmpos).le _)
  have h2 : 0 ≤ (16 * cE ^ 2 * ctc) * (m : ℝ) ^ (-(5000 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hcE0.le 2)) hctc0)
      (Real.rpow_nonneg hmpos.le _)
  have h3 : 0 ≤ (3 * Real.log (max 2 ((2 * (m : ℝ)) * ((Nl : ℝ) * ((3 : ℝ) ^ d) ^ Nl)))) ^
      ((1 / 3 : ℝ)⁻¹) := Real.rpow_nonneg hLg0 _
  exact mul_nonneg h3 (add_nonneg h1 h2)

/-- Positivity of the amplitudes and the amplitude of the `Γ₁` part. -/
theorem srootNSD7_tailY1 {d Nl : ℕ} {hr Cp C1 s K σ lg g1 Ask Abig : ℝ}
    (hCpp : 0 < Cp) (hAskp : 0 < Ask) (hKpos : 0 < K) (hK1 : 1 ≤ K) (hlgpos : 0 < lg)
    (hlg1 : 1 ≤ lg) (hs0 : 0 < s) (hs1 : s ≤ 1) (hC1one : 1 ≤ C1)
    (hSgpos : 0 < σ ^ (-(2 : ℝ))) (hSg : σ ^ (-(2 : ℝ)) = (σ⁻¹) ^ 2)
    (hh0 : 0 ≤ hr) (hh2 : hr ≤ 2 * K * lg) (hg1 : 0 < g1)
    (hA1C : g1 * Cp * (6 + 62 * (d : ℝ)) + g1 ^ 2 * Cp * Ask + 14 * g1 ^ 3 * Cp ≤ Abig) :
    0 < Cp * (6 + 62 * (d : ℝ)) * C1 * (s⁻¹) ^ 2 * K * σ ^ (-(2 : ℝ)) * lg ∧
    0 < g1 * (Cp * σ ^ (-(2 : ℝ)) * (Ask * (s⁻¹ * K * lg)) + g1 *
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * σ ^ (-(2 : ℝ)) * (2 * hr + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg))) ∧
    g1 * (Cp * (6 + 62 * (d : ℝ)) * C1 * (s⁻¹) ^ 2 * K * σ ^ (-(2 : ℝ)) * lg + 1 *
      (g1 * (Cp * σ ^ (-(2 : ℝ)) * (Ask * (s⁻¹ * K * lg)) + g1 *
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * σ ^ (-(2 : ℝ)) * (2 * hr + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg))))) ≤
      Abig * C1 * (s⁻¹ * K ^ ((1 : ℝ) / 2) * σ⁻¹ * lg ^ ((1 : ℝ) / 2)) ^ 2 := by
  have hC1pos : 0 < C1 := by linarith only [hC1one]
  have hsi : 0 < s⁻¹ := inv_pos.2 hs0
  have hCp0 : 0 ≤ Cp := hCpp.le
  have hAsk0 : 0 ≤ Ask := hAskp.le
  have hKp0 : 0 ≤ 4 * C1 * s⁻¹ * K :=
    (mul_pos (mul_pos (mul_pos (by norm_num) hC1pos) hsi) hKpos).le
  have hc0pos : 0 < Cp * (6 + 62 * (d : ℝ)) * C1 * (s⁻¹) ^ 2 * K * σ ^ (-(2 : ℝ)) * lg :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hCpp (by positivity))
      hC1pos) (pow_pos hsi 2)) hKpos) hSgpos) hlgpos
  have hsumpos : 0 ≤ ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
      (Cp * σ ^ (-(2 : ℝ)) * (2 * hr + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg)) :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (Homogenization.geometricWeight_nonneg l
        (by linarith only [hs0])) (mul_nonneg (mul_nonneg hCpp.le hSgpos.le) (by
          have hl0 := Nat.cast_nonneg (α := ℝ) l
          have hz : 0 ≤ (4 * C1 * s⁻¹ * K) * lg := mul_nonneg hKp0 hlgpos.le
          linarith only [hh0, hz, hl0])))
  have hAY1pos : 0 < g1 * (Cp * σ ^ (-(2 : ℝ)) * (Ask * (s⁻¹ * K * lg)) + g1 *
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * σ ^ (-(2 : ℝ)) * (2 * hr + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg))) := by
    have h1 : 0 < Cp * σ ^ (-(2 : ℝ)) * (Ask * (s⁻¹ * K * lg)) :=
      mul_pos (mul_pos hCpp hSgpos) (mul_pos hAskp (mul_pos (mul_pos hsi hKpos) hlgpos))
    have h2 : 0 ≤ g1 * ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * σ ^ (-(2 : ℝ)) * (2 * hr + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg)) :=
      mul_nonneg hg1.le hsumpos
    exact mul_pos hg1 (add_pos_of_pos_of_nonneg h1 h2)
  have hY1amp := srootNSD_Y1_amp (Cp := Cp) (Sg := σ ^ (-(2 : ℝ))) (s := s) (K := K) (C1 := C1)
    (lg := lg) (h := hr) (Kp := 4 * C1 * s⁻¹ * K) (g1 := g1) (Ask := Ask) (d := (d : ℝ)) Nl
    hCp0 hSgpos.le hs0 hs1 hK1 hC1one hlg1 hh0 hh2 hKp0 le_rfl hg1 hAsk0
  obtain ⟨_, hsq2⟩ := srootNSD_sq_forms (u := σ⁻¹) hs0 (by linarith only [hK1]) (by
    linarith only [hlg1])
  have hZ0 : 0 ≤ C1 * (s⁻¹) ^ 2 * K * σ ^ (-(2 : ℝ)) * lg :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le (pow_nonneg hsi.le 2)) hKpos.le)
      hSgpos.le) hlgpos.le
  refine ⟨hc0pos, hAY1pos, ?_⟩
  refine hY1amp.trans ?_
  rw [hsq2, hSg]
  have e : Abig * C1 * ((s⁻¹) ^ 2 * K * σ⁻¹ ^ 2 * lg) =
      Abig * (C1 * (s⁻¹) ^ 2 * K * (σ⁻¹) ^ 2 * lg) := by ring
  rw [e]
  have hZ0' : 0 ≤ C1 * (s⁻¹) ^ 2 * K * (σ⁻¹) ^ 2 * lg := by rw [← hSg]; exact hZ0
  exact mul_le_mul_of_nonneg_right hA1C hZ0'

/-- The deterministic sum bound of the final assembly. -/
theorem srootNSD7_tailSum {d Nl : ℕ} {hr Cp Ask C1 s K σ lg Abig : ℝ}
    (hCp0 : 0 ≤ Cp) (hAsk0 : 0 ≤ Ask) (hKpos : 0 < K) (hlgpos : 0 < lg)
    (hSgpos : 0 < σ ^ (-(2 : ℝ))) (hSg : σ ^ (-(2 : ℝ)) = (σ⁻¹) ^ 2)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hK1 : 1 ≤ K) (hC1one : 1 ≤ C1) (hlg1 : 1 ≤ lg)
    (hdn : (0 : ℝ) ≤ d) (hlog2h2 : Real.log (2 * hr) ≤ 2 * lg)
    (hH0n : 0 ≤ Ask * (K * lg * Real.log (2 * hr))) (hh0 : 0 ≤ hr) (hh2 : hr ≤ 2 * K * lg)
    (hKp0 : 0 ≤ 4 * C1 * s⁻¹ * K) (hu0 : 0 ≤ σ⁻¹) (hA2C : Cp * (2 * Ask + 44) ≤ Abig) :
    ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * σ ^ (-(2 : ℝ)) * (Ask * (K * lg * Real.log (2 * hr)) + 2 * hr + (l : ℝ) +
            (4 * C1 * s⁻¹ * K) * (4 * lg ^ 2)) +
          Cp * σ ^ (-(2 : ℝ)) * (2 * hr + (l : ℝ) + 2 * (4 * C1 * s⁻¹ * K) * lg) *
            (2 * lg + 2 * (d : ℝ) * (l : ℝ))) ≤
      Abig * C1 * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * σ⁻¹ * lg) ^ 2 +
        Cp * (6 + 62 * (d : ℝ)) * C1 * (s⁻¹) ^ 2 * K * σ ^ (-(2 : ℝ)) * lg := by
  have hC1pos : 0 < C1 := by linarith only [hC1one]
  have hsi : 0 < s⁻¹ := inv_pos.2 hs0
  have hdet := srootNSD_det_bound (Cp := Cp) (cH := Ask) (S := σ ^ (-(2 : ℝ))) (s := s) (K := K)
    (C1 := C1) (lg := lg) (lg2 := Real.log (2 * hr))
    (H0 := Ask * (K * lg * Real.log (2 * hr))) (h := hr) (L2 := 4 * lg ^ 2)
    (Kp := 4 * C1 * s⁻¹ * K) (D := (d : ℝ)) Nl hCp0 hAsk0 hSgpos.le hs0 hs1 hK1 hC1one hlg1 hdn
    hlog2h2 hH0n le_rfl hh0 hh2 (mul_nonneg (by norm_num) (sq_nonneg lg)) le_rfl hKp0 le_rfl
  obtain ⟨hsq1, _⟩ := srootNSD_sq_forms (u := σ⁻¹) hs0 (by linarith only [hK1]) (by
    linarith only [hlg1])
  have hmain : Cp * (2 * Ask + 44) * C1 * s⁻¹ * K * σ ^ (-(2 : ℝ)) * lg ^ 2 ≤
      Abig * C1 * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * σ⁻¹ * lg) ^ 2 := by
    rw [hsq1, hSg]
    have e1 : Cp * (2 * Ask + 44) * C1 * s⁻¹ * K * (σ⁻¹) ^ 2 * lg ^ 2 =
        (Cp * (2 * Ask + 44)) * (C1 * s⁻¹ * K * (σ⁻¹) ^ 2 * lg ^ 2) := by ring
    have e2 : Abig * C1 * (s⁻¹ * K * σ⁻¹ ^ 2 * lg ^ 2) =
        Abig * (C1 * s⁻¹ * K * (σ⁻¹) ^ 2 * lg ^ 2) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_right hA2C ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le hsi.le) hKpos.le)
      (pow_nonneg hu0 2)) (pow_nonneg hlgpos.le 2)
  linarith only [hdet, hmain]

end

end SuperdiffusionCLT.Section4.MinimalScales
