/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD4

/-!
# Near-scale assembly: numerical bookkeeping in the threshold `m`

Everything here is real arithmetic. The standing facts are `C1 ≤ K`, `4 ≤ log m` and the
threshold `C1 (C1 s⁻¹ K log m) ≤ 1600 m`, which give `C1, K, s⁻¹ K log m ≤ m`; all constants
independent of `m` are then at most `C1 ≤ m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

theorem srootNSD_basic {m lg s K C1 : ℝ} (hC1 : 40 ≤ C1) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hK : C1 ≤ K) (hlg : 4 ≤ lg) (hcore : C1 * (C1 * s⁻¹ * K * lg) ≤ 1600 * m) :
    C1 ≤ m ∧ s⁻¹ * K * lg ≤ m ∧ K ≤ m := by
  have ht : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).2 hs1
  have hK1 : 1 ≤ K := by linarith only [hK, hC1]
  have hP1 : K ≤ s⁻¹ * K * lg := by
    have h1 : K * 1 ≤ K * s⁻¹ := mul_le_mul_of_nonneg_left ht (by linarith only [hK1])
    have h2 : K * s⁻¹ * 1 ≤ K * s⁻¹ * lg :=
      mul_le_mul_of_nonneg_left (by linarith only [hlg]) (by positivity)
    nlinarith only [h1, h2]
  have hP : s⁻¹ * K * lg ≤ m := by
    have hsq : 1600 ≤ C1 * C1 := by nlinarith only [hC1]
    have hP0 : 0 ≤ s⁻¹ * K * lg := by
      have : 0 ≤ K := by linarith only [hK1]
      positivity
    have h1 : 1600 * (s⁻¹ * K * lg) ≤ C1 * C1 * (s⁻¹ * K * lg) :=
      mul_le_mul_of_nonneg_right hsq hP0
    have e : C1 * (C1 * s⁻¹ * K * lg) = C1 * C1 * (s⁻¹ * K * lg) := by ring
    linarith only [h1, e, hcore]
  have hKm : K ≤ m := hP1.trans hP
  exact ⟨by linarith only [hK, hKm], hP, hKm⟩

/-- `m^k · m^{-r} ≤ m^{-r'}` for `m ≥ 1` and `k - r ≤ -r'`. -/
theorem srootNSD_pow_mul_rpow_le {m : ℝ} (hm : 1 ≤ m) (k : ℕ) {r r' : ℝ} (h : (k : ℝ) - r ≤ -r') :
    m ^ k * m ^ (-r) ≤ m ^ (-r') := by
  have hm0 : 0 < m := by linarith only [hm]
  rw [← Real.rpow_natCast, ← Real.rpow_add hm0]
  exact Real.rpow_le_rpow_of_exponent_le hm (by linarith only [h])

/-- The tail ratio is tiny: `3^m / 3^{m+h} ≤ m^{-12000}` when `h ≥ K log m` and `K ≥ 12000`. -/
theorem srootNSD_theta_le {K : ℝ} {mn h : ℕ} (hm1 : 1 < (mn : ℝ))
    (hK : 12000 ≤ K) (hh : K * Real.log (mn : ℝ) ≤ (h : ℝ)) :
    (3 : ℝ) ^ mn * ((3 : ℝ) ^ (mn + h))⁻¹ ≤ (mn : ℝ) ^ (-(12000 : ℝ)) := by
  set m : ℝ := (mn : ℝ) with hmdef
  have hm0 : 0 < m := by linarith only [hm1]
  have hlog : 0 < Real.log m := Real.log_pos hm1
  have e : (3 : ℝ) ^ mn * ((3 : ℝ) ^ (mn + h))⁻¹ = ((3 : ℝ) ^ h)⁻¹ := by
    rw [pow_add]; field_simp
  rw [e]
  have h1 : m ^ (12000 : ℝ) ≤ (3 : ℝ) ^ h := by
    have hl3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith only [this]
    have hexp : Real.exp (12000 * Real.log m) ≤ Real.exp ((h : ℝ) * Real.log 3) := by
      apply Real.exp_le_exp.2
      have h2 : (h : ℝ) ≤ (h : ℝ) * Real.log 3 := by
        have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
        nlinarith only [hl3, this]
      nlinarith only [hK, hh, h2, hlog]
    have e1 : Real.exp (12000 * Real.log m) = m ^ (12000 : ℝ) := by
      rw [mul_comm, Real.rpow_def_of_pos hm0]
    have e2 : Real.exp ((h : ℝ) * Real.log 3) = (3 : ℝ) ^ h := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast]
    rw [← e1, ← e2]; exact hexp
  rw [Real.rpow_neg hm0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hm0 _) h1

/-- The ratio factor of the tail amplitudes: `ni θ + ni² θ² ≤ 2 m² θ`. -/
theorem srootNSD_ratio_le {ni m θ : ℝ} (hni1 : 1 ≤ ni) (hnim : ni ≤ m) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : ni * θ + ni ^ 2 * θ ^ 2 ≤ 2 * m ^ 2 * θ := by
  have hm1 : 1 ≤ m := hni1.trans hnim
  have h1 : ni * θ ≤ m ^ 2 * θ := by
    have : ni ≤ m ^ 2 := by nlinarith only [hnim, hm1]
    exact mul_le_mul_of_nonneg_right this hθ0
  have h2 : ni ^ 2 * θ ^ 2 ≤ m ^ 2 * θ := by
    have h3 : ni ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by linarith only [hni1]) hnim 2
    have h4 : θ ^ 2 ≤ θ := by nlinarith only [hθ0, hθ1]
    exact mul_le_mul h3 h4 (by positivity) (by positivity)
  linarith only [h1, h2]

/-- The `Γ_{1/3}` amplitude of the second tail witness is at most `16 cE² ctc m^{-5000}`. -/
theorem srootNSD_tail_amp2 {cE ctc tc ni u m θ : ℝ} (hcE : 1 ≤ cE) (hctc : 0 ≤ ctc)
    (htc : tc ≤ ctc) (hni1 : 1 ≤ ni) (hnim : ni ≤ m) (hu0 : 0 ≤ u) (hu : u ≤ 2 * cE * m)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : θ ≤ m ^ (-(12000 : ℝ))) :
    (2 * (2 * cE * ni) * u) * (tc * (ni * θ + ni ^ 2 * θ ^ 2)) ≤
      (16 * cE ^ 2 * ctc) * m ^ (-(5000 : ℝ)) := by
  have hm1 : 1 ≤ m := hni1.trans hnim
  have hrat := srootNSD_ratio_le hni1 hnim hθ0 hθ1
  have hX0 : 0 ≤ ni * θ + ni ^ 2 * θ ^ 2 := by positivity
  have h1 : tc * (ni * θ + ni ^ 2 * θ ^ 2) ≤ ctc * (2 * m ^ 2 * θ) :=
    (mul_le_mul_of_nonneg_right htc hX0).trans (mul_le_mul_of_nonneg_left hrat hctc)
  have hA0 : 0 ≤ 2 * (2 * cE * ni) * u := by
    have : 0 ≤ cE := by linarith only [hcE]
    have : 0 ≤ ni := by linarith only [hni1]
    positivity
  have hA : 2 * (2 * cE * ni) * u ≤ 8 * cE ^ 2 * m ^ 2 := by
    have : 2 * (2 * cE * ni) * u ≤ 2 * (2 * cE * m) * (2 * cE * m) :=
      mul_le_mul (by nlinarith only [hnim, hcE]) hu hu0 (by nlinarith only [hm1, hcE])
    nlinarith only [this]
  have hθm : m ^ 2 * θ ≤ m ^ 2 * m ^ (-(12000 : ℝ)) := mul_le_mul_of_nonneg_left hθ (by positivity)
  have hmm : m ^ 2 * m ^ 2 * m ^ (-(12000 : ℝ)) ≤ m ^ (-(5000 : ℝ)) := by
    have := srootNSD_pow_mul_rpow_le hm1 4 (r := 12000) (r' := 5000) (by norm_num)
    have e : m ^ 2 * m ^ 2 = m ^ 4 := by ring
    rw [e]; exact this
  calc (2 * (2 * cE * ni) * u) * (tc * (ni * θ + ni ^ 2 * θ ^ 2))
      ≤ (2 * (2 * cE * ni) * u) * (ctc * (2 * m ^ 2 * θ)) := mul_le_mul_of_nonneg_left h1 hA0
    _ ≤ (8 * cE ^ 2 * m ^ 2) * (ctc * (2 * m ^ 2 * θ)) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = (16 * cE ^ 2 * ctc) * (m ^ 2 * (m ^ 2 * θ)) := by ring
    _ ≤ (16 * cE ^ 2 * ctc) * (m ^ 2 * (m ^ 2 * m ^ (-(12000 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hθm (by positivity)
    _ = (16 * cE ^ 2 * ctc) * (m ^ 2 * m ^ 2 * m ^ (-(12000 : ℝ))) := by ring
    _ ≤ (16 * cE ^ 2 * ctc) * m ^ (-(5000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmm (by positivity)

/-- The `Γ_{1/3}` amplitude of the first tail witness is at most `52 cE² ctc m^{-11000}`. -/
theorem srootNSD_tail_amp1 {cE ctc tc ni u σ nu m mmR θ : ℝ} (hcE : 1 ≤ cE) (hctc : 0 ≤ ctc)
    (htc : tc ≤ ctc) (hni1 : 1 ≤ ni) (hnim : ni ≤ m) (hnu0 : 0 < nu) (hnu1 : nu ≤ 1)
    (hu0 : 0 ≤ u) (hu : u ≤ 2 * cE * m) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ nu + 2 * cE * ni * max 1 m) (hmm1 : 1 ≤ mmR) (hmm : mmR ≤ 3 * m)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : θ ≤ m ^ (-(12000 : ℝ))) :
    ((nu + 2 * cE * ni * max 1 mmR) * u + 2 * (2 * cE * ni) * σ) *
        (tc * (ni * θ + ni ^ 2 * θ ^ 2)) ≤
      (52 * cE ^ 2 * ctc) * m ^ (-(11000 : ℝ)) := by
  have hm1 : 1 ≤ m := hni1.trans hnim
  have hcE0 : 0 ≤ cE := by linarith only [hcE]
  have hni0 : 0 ≤ ni := by linarith only [hni1]
  have hmaxm : max 1 m = m := max_eq_right hm1
  have hmaxmm : max 1 mmR = mmR := max_eq_right hmm1
  rw [hmaxm] at hσ
  rw [hmaxmm]
  have hrat := srootNSD_ratio_le hni1 hnim hθ0 hθ1
  have hX0 : 0 ≤ ni * θ + ni ^ 2 * θ ^ 2 := by positivity
  have h1 : tc * (ni * θ + ni ^ 2 * θ ^ 2) ≤ ctc * (2 * m ^ 2 * θ) :=
    (mul_le_mul_of_nonneg_right htc hX0).trans (mul_le_mul_of_nonneg_left hrat hctc)
  have hm2 : m ≤ m ^ 2 := by nlinarith only [hm1]
  have hσ3 : σ ≤ 3 * cE * m ^ 2 := by
    have h1' : ni * m ≤ m * m := mul_le_mul_of_nonneg_right hnim (by linarith only [hm1])
    have h2' : 2 * cE * (ni * m) ≤ 2 * cE * (m * m) := mul_le_mul_of_nonneg_left h1' (by positivity)
    have h3' : (1 : ℝ) ≤ cE * m ^ 2 := by nlinarith only [hcE, hm1]
    nlinarith only [hσ, h2', hnu1, h3']
  have hU : nu + 2 * cE * ni * mmR ≤ 7 * cE * m ^ 2 := by
    have h1' : ni * mmR ≤ m * (3 * m) :=
      mul_le_mul hnim hmm (by linarith only [hmm1]) (by linarith only [hm1])
    have h2' : 2 * cE * (ni * mmR) ≤ 2 * cE * (m * (3 * m)) :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have h3' : (1 : ℝ) ≤ cE * m ^ 2 := by nlinarith only [hcE, hm1]
    nlinarith only [hnu1, h2', h3']
  have hU0 : 0 ≤ nu + 2 * cE * ni * mmR := by
    have : 0 ≤ mmR := by linarith only [hmm1]
    positivity
  have hB : (nu + 2 * cE * ni * mmR) * u + 2 * (2 * cE * ni) * σ ≤ 26 * cE ^ 2 * m ^ 3 := by
    have a1 : (nu + 2 * cE * ni * mmR) * u ≤ (7 * cE * m ^ 2) * (2 * cE * m) :=
      mul_le_mul hU hu hu0 (by positivity)
    have a2 : 2 * (2 * cE * ni) * σ ≤ 2 * (2 * cE * m) * (3 * cE * m ^ 2) :=
      mul_le_mul (by nlinarith only [hnim, hcE]) hσ3 hσ0 (by positivity)
    nlinarith only [a1, a2]
  have hB0 : 0 ≤ (nu + 2 * cE * ni * mmR) * u + 2 * (2 * cE * ni) * σ := by positivity
  have hθm : m ^ 2 * θ ≤ m ^ 2 * m ^ (-(12000 : ℝ)) := mul_le_mul_of_nonneg_left hθ (by positivity)
  have hmm5 : m ^ 3 * m ^ 2 * m ^ (-(12000 : ℝ)) ≤ m ^ (-(11000 : ℝ)) := by
    have := srootNSD_pow_mul_rpow_le hm1 5 (r := 12000) (r' := 11000) (by norm_num)
    have e : m ^ 3 * m ^ 2 = m ^ 5 := by ring
    rw [e]; exact this
  calc ((nu + 2 * cE * ni * mmR) * u + 2 * (2 * cE * ni) * σ) *
        (tc * (ni * θ + ni ^ 2 * θ ^ 2))
      ≤ ((nu + 2 * cE * ni * mmR) * u + 2 * (2 * cE * ni) * σ) * (ctc * (2 * m ^ 2 * θ)) :=
        mul_le_mul_of_nonneg_left h1 hB0
    _ ≤ (26 * cE ^ 2 * m ^ 3) * (ctc * (2 * m ^ 2 * θ)) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
    _ = (52 * cE ^ 2 * ctc) * (m ^ 3 * (m ^ 2 * θ)) := by ring
    _ ≤ (52 * cE ^ 2 * ctc) * (m ^ 3 * (m ^ 2 * m ^ (-(12000 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hθm (by positivity)
    _ = (52 * cE ^ 2 * ctc) * (m ^ 3 * m ^ 2 * m ^ (-(12000 : ℝ))) := by ring
    _ ≤ (52 * cE ^ 2 * ctc) * m ^ (-(11000 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmm5 (by positivity)

/-- The `Γ₁`-coefficient sum: `Σ w_l (Cp Sg (2h + l + 2 Kp lg)) ≤ 14 Cp Sg C1 s⁻² K lg`. -/
theorem srootNSD_alpha_sum_le {Cp Sg s K C1 lg h Kp : ℝ} (N : ℕ) (hCp : 0 ≤ Cp) (hSg : 0 ≤ Sg)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hK : 1 ≤ K) (hC1 : 1 ≤ C1) (hlg : 1 ≤ lg) (hh0 : 0 ≤ h)
    (hh : h ≤ 2 * K * lg) (hKp0 : 0 ≤ Kp) (hKp : Kp ≤ 4 * C1 * s⁻¹ * K) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) ≤
      14 * Cp * Sg * (C1 * (s⁻¹) ^ 2 * K * lg) := by
  set t : ℝ := s⁻¹ with ht
  have ht1 : 1 ≤ t := by rw [ht]; exact one_le_inv₀ hs0 |>.2 hs1
  have hCS : 0 ≤ Cp * Sg := mul_nonneg hCp hSg
  have hpt : ∀ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) =
      Homogenization.geometricWeight s 2 l * ((Cp * Sg * (2 * h + 2 * Kp * lg)) +
        (Cp * Sg) * (l : ℝ) + 0 * (l : ℝ) ^ 2) := fun l _ => by ring
  rw [Finset.sum_congr rfl hpt]
  have hc0 : 0 ≤ Cp * Sg * (2 * h + 2 * Kp * lg) := by positivity
  refine le_trans (srootNSD_weighted_poly_le hs0 hc0 hCS le_rfl N) ?_
  have hu : 1 ≤ K * lg := by nlinarith only [hK, hlg]
  have hKplg : Kp * lg ≤ 4 * C1 * t * K * lg := by
    have := mul_le_mul_of_nonneg_right hKp (by linarith only [hlg] : (0 : ℝ) ≤ lg)
    linarith only [this]
  have e2 : (2 : ℝ) / s = 2 * t := by rw [ht]; ring
  rw [e2]
  have hA : 2 * h + 2 * Kp * lg ≤ 12 * (C1 * t * K * lg) := by
    have h1 : 1 ≤ C1 * t := by nlinarith only [hC1, ht1]
    have h2 : K * lg ≤ C1 * t * (K * lg) := by nlinarith only [h1, hu]
    nlinarith only [hh, hKplg, h2]
  have hB : 2 * t ≤ 2 * (C1 * t * K * lg) := by
    have h1 : t ≤ t * (K * lg) := by nlinarith only [ht1, hu]
    have h2 : t * (K * lg) ≤ C1 * t * K * lg := by
      have h0 : 0 ≤ t * (K * lg) := by
        have : 0 ≤ K * lg := by linarith only [hu]
        positivity
      have := mul_le_mul_of_nonneg_right hC1 h0
      have e : C1 * (t * (K * lg)) = C1 * t * K * lg := by ring
      linarith only [this, e]
    nlinarith only [h1, h2]
  have h3 := mul_le_mul_of_nonneg_left hA hCS
  have h4 := mul_le_mul_of_nonneg_left hB hCS
  have hD : C1 * t * K * lg ≤ C1 * t ^ 2 * K * lg := by
    have : 0 ≤ C1 * t * K * lg := by
      have : 0 ≤ K := by linarith only [hK]
      have : 0 ≤ lg := by linarith only [hlg]
      positivity
    nlinarith only [ht1, this]
  have hD' := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 14 * Cp * Sg)
  nlinarith only [h3, h4, hD']

/-- The amplitude of the final `Γ₁` variable. -/
theorem srootNSD_Y1_amp {Cp Sg s K C1 lg h Kp g1 Ask d : ℝ} (N : ℕ) (hCp : 0 ≤ Cp)
    (hSg : 0 ≤ Sg) (hs0 : 0 < s) (hs1 : s ≤ 1) (hK : 1 ≤ K) (hC1 : 1 ≤ C1) (hlg : 1 ≤ lg)
    (hh0 : 0 ≤ h) (hh : h ≤ 2 * K * lg) (hKp0 : 0 ≤ Kp) (hKp : Kp ≤ 4 * C1 * s⁻¹ * K)
    (hg1 : 0 < g1) (hAsk : 0 ≤ Ask) :
    g1 * (Cp * (6 + 62 * d) * C1 * (s⁻¹) ^ 2 * K * Sg * lg +
        1 * (g1 * (Cp * Sg * (Ask * (s⁻¹ * K * lg)) + g1 *
          ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
            (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg))))) ≤
      (g1 * Cp * (6 + 62 * d) + g1 ^ 2 * Cp * Ask + 14 * g1 ^ 3 * Cp) *
        (C1 * (s⁻¹) ^ 2 * K * Sg * lg) := by
  set t : ℝ := s⁻¹ with ht
  have ht1 : 1 ≤ t := by rw [ht]; exact one_le_inv₀ hs0 |>.2 hs1
  have hSum := srootNSD_alpha_sum_le N hCp hSg hs0 hs1 hK hC1 hlg hh0 hh hKp0 hKp
  have hZ : 0 ≤ C1 * t ^ 2 * K * Sg * lg := by
    have : 0 ≤ K := by linarith only [hK]
    have : 0 ≤ lg := by linarith only [hlg]
    have : 0 ≤ C1 := by linarith only [hC1]
    positivity
  have hAW : Cp * Sg * (Ask * (t * K * lg)) ≤ Cp * Ask * (C1 * t ^ 2 * K * Sg * lg) := by
    have h1 : t * K * lg ≤ C1 * t ^ 2 * K * lg := by
      have h0 : 0 ≤ t * K * lg := by
        have : 0 ≤ K := by linarith only [hK]
        have : 0 ≤ lg := by linarith only [hlg]
        positivity
      have h2 : C1 * t ^ 2 * K * lg = (C1 * t) * (t * K * lg) := by ring
      rw [h2]
      have : 1 ≤ C1 * t := by nlinarith only [hC1, ht1]
      nlinarith only [this, h0]
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Cp * Sg * Ask)
    have e1 : Cp * Sg * Ask * (t * K * lg) = Cp * Sg * (Ask * (t * K * lg)) := by ring
    have e2 : Cp * Sg * Ask * (C1 * t ^ 2 * K * lg) = Cp * Ask * (C1 * t ^ 2 * K * Sg * lg) := by
      ring
    linarith only [h3, e1, e2]
  have hSum' : ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
      (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) ≤ 14 * Cp * (C1 * t ^ 2 * K * Sg * lg) := by
    have e : 14 * Cp * Sg * (C1 * t ^ 2 * K * lg) = 14 * Cp * (C1 * t ^ 2 * K * Sg * lg) := by ring
    linarith only [hSum, e]
  have hin : Cp * Sg * (Ask * (t * K * lg)) + g1 * ∑ l ∈ Finset.range N,
      Homogenization.geometricWeight s 2 l * (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) ≤
      Cp * Ask * (C1 * t ^ 2 * K * Sg * lg) + g1 * (14 * Cp * (C1 * t ^ 2 * K * Sg * lg)) :=
    add_le_add hAW (mul_le_mul_of_nonneg_left hSum' hg1.le)
  have hin2 := mul_le_mul_of_nonneg_left hin hg1.le
  have e3 : Cp * (6 + 62 * d) * C1 * t ^ 2 * K * Sg * lg =
      Cp * (6 + 62 * d) * (C1 * t ^ 2 * K * Sg * lg) := by ring
  rw [e3]
  have hfin := mul_le_mul_of_nonneg_left (add_le_add
      (le_refl (Cp * (6 + 62 * d) * (C1 * t ^ 2 * K * Sg * lg))) (by linarith only [hin2] :
      1 * (g1 * (Cp * Sg * (Ask * (t * K * lg)) + g1 * ∑ l ∈ Finset.range N,
        Homogenization.geometricWeight s 2 l * (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)))) ≤
      g1 * (Cp * Ask * (C1 * t ^ 2 * K * Sg * lg) + g1 * (14 * Cp * (C1 * t ^ 2 * K * Sg * lg)))))
      hg1.le
  refine hfin.trans (le_of_eq ?_)
  ring

/-- `x ^ ((1/3)⁻¹) = x ^ 3`. -/
theorem srootNSD_rpow_three (x : ℝ) : x ^ ((1 / 3 : ℝ)⁻¹) = x ^ 3 := by
  rw [show ((1 / 3 : ℝ)⁻¹) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The amplitude of the `Γ₁` cap factor `U`. -/
theorem srootNSD_Au_le {cE g1 Ask K lg lg2 t u m : ℝ} (hm : 1 ≤ m) (hcE : 1 ≤ cE) (hg1 : 0 ≤ g1)
    (hAsk : 0 ≤ Ask) (hK : 1 ≤ K) (hlg : 1 ≤ lg) (hlgm : lg ≤ m) (hKlg : K * lg ≤ m)
    (hP : t * K * lg ≤ m) (hlg2 : lg2 ≤ lg) (hlg20 : 0 ≤ lg2) (ht : 0 ≤ t) (hu0 : 0 ≤ u)
    (hu : u ≤ 2 * cE * m) :
    g1 * ((1 + (u + 1) * (Ask * (K * lg * lg2))) + (u + 1) * (Ask * (t * K * lg))) ≤
      (g1 * (1 + 6 * cE * Ask)) * m ^ 3 := by
  have hu1 : u + 1 ≤ 3 * cE * m := by nlinarith only [hu, hcE, hm]
  have hH : K * lg * lg2 ≤ m * m := by
    have h1 : K * lg * lg2 ≤ K * lg * lg :=
      mul_le_mul_of_nonneg_left hlg2 (by nlinarith only [hK, hlg])
    have h2 : K * lg * lg ≤ m * m :=
      mul_le_mul hKlg hlgm (by linarith only [hlg]) (by linarith only [hm])
    linarith only [h1, h2]
  have hu10 : 0 ≤ u + 1 := by linarith only [hu0]
  have a1 : (u + 1) * (Ask * (K * lg * lg2)) ≤ (3 * cE * m) * (Ask * (m * m)) :=
    mul_le_mul hu1 (mul_le_mul_of_nonneg_left hH hAsk) (by
      have : 0 ≤ K * lg * lg2 := by
        have : 0 ≤ K := by linarith only [hK]
        have : 0 ≤ lg := by linarith only [hlg]
        positivity
      positivity) (by positivity)
  have a2 : (u + 1) * (Ask * (t * K * lg)) ≤ (3 * cE * m) * (Ask * m) :=
    mul_le_mul hu1 (mul_le_mul_of_nonneg_left hP hAsk) (by
      have : 0 ≤ K := by linarith only [hK]
      have : 0 ≤ lg := by linarith only [hlg]
      positivity) (by positivity)
  have hm3 : m ≤ m ^ 3 := by nlinarith only [hm, one_le_pow₀ (n := 2) hm]
  have hm2 : m * m ≤ m ^ 3 := by nlinarith only [hm]
  have b1 : (3 * cE * m) * (Ask * (m * m)) ≤ 3 * cE * Ask * m ^ 3 := by
    have := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ 3 * cE * Ask * m)
    nlinarith only [this]
  have b2 : (3 * cE * m) * (Ask * m) ≤ 3 * cE * Ask * m ^ 3 := by
    have h1 : m * m ≤ m ^ 3 := hm2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 3 * cE * Ask)
    nlinarith only [this]
  have hone : (1 : ℝ) ≤ m ^ 3 := by nlinarith only [hm, hm3]
  have hsum : (1 + (u + 1) * (Ask * (K * lg * lg2))) + (u + 1) * (Ask * (t * K * lg)) ≤
      (1 + 6 * cE * Ask) * m ^ 3 := by nlinarith only [a1, a2, b1, b2, hone]
  have := mul_le_mul_of_nonneg_left hsum hg1
  linarith only [this]

/-- `(m/2)^{-p} = 2^p m^{-p}`. -/
theorem srootNSD_half_rpow {m : ℝ} (hm : 0 < m) (p : ℝ) :
    (m / 2) ^ (-p) = (2 : ℝ) ^ p * m ^ (-p) := by
  rw [Real.div_rpow hm.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg hm.le]
  field_simp

/-- The amplitude of the `Γ_{1/3}` factor `V`. -/
theorem srootNSD_Bv_le {Cp cE ctc c3 m Lg βB : ℝ} (hm : 1 ≤ m) (hCp : 0 ≤ Cp)
    (hLg0 : 0 ≤ Lg) (hLg : Lg ≤ c3 * m) (hβB0 : 0 ≤ βB)
    (hβB : βB ≤ (16 * cE ^ 2 * ctc) * m ^ (-(5000 : ℝ))) :
    Lg ^ ((1 / 3 : ℝ)⁻¹) * (Cp * (m / 2) ^ (-(5000 : ℝ)) + βB) ≤
      (c3 * m) ^ 3 * ((Cp * (2 : ℝ) ^ (5000 : ℝ) + 16 * cE ^ 2 * ctc) * m ^ (-(5000 : ℝ))) := by
  have hm0 : 0 < m := by linarith only [hm]
  rw [srootNSD_rpow_three]
  have e := srootNSD_half_rpow hm0 5000
  have h1 : Lg ^ 3 ≤ (c3 * m) ^ 3 := pow_le_pow_left₀ hLg0 hLg 3
  have h2 : Cp * (m / 2) ^ (-(5000 : ℝ)) + βB ≤
      (Cp * (2 : ℝ) ^ (5000 : ℝ) + 16 * cE ^ 2 * ctc) * m ^ (-(5000 : ℝ)) := by
    rw [e]
    nlinarith only [hβB]
  exact mul_le_mul h1 h2 (by
    have : 0 ≤ Cp * (m / 2) ^ (-(5000 : ℝ)) := by positivity
    linarith only [this, hβB0]) (pow_nonneg (le_trans hLg0 hLg) 3)

/-- The cap condition: `Au · Bv ≤ m^{-4900}`. -/
theorem srootNSD_cap_cond {Au Bv U0 c3 Q2 m : ℝ} (hm : 1 ≤ m) (hBv0 : 0 ≤ Bv)
    (hAu : Au ≤ U0 * m ^ 3) (hBv : Bv ≤ (c3 * m) ^ 3 * (Q2 * m ^ (-(5000 : ℝ))))
    (hU0 : U0 ≤ m) (hc3 : c3 ≤ m) (hQ2 : Q2 ≤ m) (hU00 : 0 ≤ U0) (hc30 : 0 ≤ c3)
    (hQ20 : 0 ≤ Q2) : Au * Bv ≤ m ^ (-(4900 : ℝ)) := by
  have hm0 : 0 < m := by linarith only [hm]
  have hmr : 0 ≤ m ^ (-(5000 : ℝ)) := Real.rpow_nonneg hm0.le _
  have h1 : Au * Bv ≤ (U0 * m ^ 3) * ((c3 * m) ^ 3 * (Q2 * m ^ (-(5000 : ℝ)))) :=
    mul_le_mul hAu hBv hBv0 (by positivity)
  have h2 : (U0 * m ^ 3) * ((c3 * m) ^ 3 * (Q2 * m ^ (-(5000 : ℝ)))) ≤
      (m * m ^ 3) * (((m * m) ^ 3) * (m * m ^ (-(5000 : ℝ)))) := by
    refine mul_le_mul (mul_le_mul hU0 le_rfl (by positivity) hm0.le)
      (mul_le_mul (pow_le_pow_left₀ (by positivity) (mul_le_mul hc3 le_rfl hm0.le hm0.le) 3)
        (mul_le_mul hQ2 le_rfl hmr hm0.le) (by positivity) (by positivity)) (by positivity)
      (by positivity)
  have h3 : (m * m ^ 3) * (((m * m) ^ 3) * (m * m ^ (-(5000 : ℝ)))) =
      m ^ 11 * m ^ (-(5000 : ℝ)) := by ring
  have h4 := srootNSD_pow_mul_rpow_le hm 11 (r := 5000) (r' := 4900) (by norm_num)
  linarith only [h1, h2, h3, h4]

/-- The amplitude of the final `Γ_{1/3}` variable. -/
theorem srootNSD_Y2_amp {g3 κ E1 e1c c3 A m Lg : ℝ} (hm : 1 ≤ m) (hg3 : 0 ≤ g3)
    (hLg0 : 0 ≤ Lg) (hLg : Lg ≤ c3 * m) (hE1 : E1 = e1c * m ^ (-(11000 : ℝ)))
    (hc3 : c3 ≤ m) (he1 : e1c ≤ m) (he10 : 0 ≤ e1c) (hA : g3 * (1 + κ) ≤ A) :
    g3 * (Lg ^ ((1 / 3 : ℝ)⁻¹) * E1 + κ * m ^ (-(2000 : ℝ))) ≤ A * m ^ (-(2000 : ℝ)) := by
  have hm0 : 0 < m := by linarith only [hm]
  have hmr : 0 ≤ m ^ (-(11000 : ℝ)) := Real.rpow_nonneg hm0.le _
  rw [srootNSD_rpow_three, hE1]
  have h1 : Lg ^ 3 ≤ (m * m) ^ 3 :=
    pow_le_pow_left₀ hLg0 (hLg.trans (mul_le_mul_of_nonneg_right hc3 hm0.le)) 3
  have h2 : Lg ^ 3 * (e1c * m ^ (-(11000 : ℝ))) ≤ (m * m) ^ 3 * (m * m ^ (-(11000 : ℝ))) :=
    mul_le_mul h1 (mul_le_mul he1 le_rfl hmr hm0.le) (by positivity) (by positivity)
  have h3 : (m * m) ^ 3 * (m * m ^ (-(11000 : ℝ))) = m ^ 7 * m ^ (-(11000 : ℝ)) := by ring
  have h4 := srootNSD_pow_mul_rpow_le hm 7 (r := 11000) (r' := 2000) (by norm_num)
  have hmr2 : 0 ≤ m ^ (-(2000 : ℝ)) := Real.rpow_nonneg hm0.le _
  have h5 : Lg ^ 3 * (e1c * m ^ (-(11000 : ℝ))) ≤ m ^ (-(2000 : ℝ)) := by
    linarith only [h2, h3, h4]
  have h6 : Lg ^ 3 * (e1c * m ^ (-(11000 : ℝ))) + κ * m ^ (-(2000 : ℝ)) ≤
      (1 + κ) * m ^ (-(2000 : ℝ)) := by nlinarith only [h5]
  have h7 := mul_le_mul_of_nonneg_left h6 hg3
  have h8 : g3 * ((1 + κ) * m ^ (-(2000 : ℝ))) ≤ A * m ^ (-(2000 : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hA hmr2
    nlinarith only [this]
  linarith only [h7, h8]

/-- The square forms of the target amplitudes of `hNear`. -/
theorem srootNSD_sq_forms {s K u lg : ℝ} (hs : 0 < s) (hK : 0 ≤ K) (hlg : 0 ≤ lg) :
    (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * u * lg) ^ 2 = s⁻¹ * K * u ^ 2 * lg ^ 2 ∧
    (s⁻¹ * K ^ ((1 : ℝ) / 2) * u * lg ^ ((1 : ℝ) / 2)) ^ 2 = (s⁻¹) ^ 2 * K * u ^ 2 * lg := by
  have hsq : ∀ x : ℝ, 0 ≤ x → (x ^ ((1 : ℝ) / 2)) ^ 2 = x := fun x hx => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have hs2 : (s ^ (-((1 : ℝ) / 2))) ^ 2 = s⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    rw [show -((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  constructor
  · rw [mul_pow, mul_pow, mul_pow, hs2, hsq K hK]
  · rw [mul_pow, mul_pow, mul_pow, hsq K hK, hsq lg hlg]

end

end SuperdiffusionCLT.Section4.MinimalScales
