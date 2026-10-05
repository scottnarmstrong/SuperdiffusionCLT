/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.UpperRatioC

/-!
# `cor.upper.ratio`: auxiliary facts

The zero Dirichlet response for the flux `hshellFlux .. 0`, the rewriting of the principal-term bound
into the shape of the Neumann-input bound, the `limsup` step in the cube size, and the real arithmetic
which closes the expansion of the product.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

theorem upperRatio_grad_zero (U : Set (Vec d)) :
    (0 : H10Function U).toH1Function.grad = 0 := by
  rfl

theorem upperRatio_hshellFlux_zero [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (m h : ℕ)
    (omega : ShellSeq d) : hshellFlux nu P m h omega (0 : Vec d) = 0 := by
  funext x
  simp [hshellFlux, matVecMul_zero]

theorem upperRatio_dirichlet_zero [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (omega : ShellSeq d) :
    IsCubeDirichletResponse (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega (0 : Vec d))
      (0 : H10Function (openCubeSet (originCube d (Kc : ℤ)))) := by
  intro φ
  rw [upperRatio_hshellFlux_zero, upperRatio_grad_zero]
  simp [vecDot]

theorem upperRatio_volumeAverageVec_zero (U : Set (Vec d)) :
    volumeAverageVec U (0 : Vec d → Vec d) = 0 := by
  funext i
  simp [volumeAverageVec, volumeAverage]

theorem upperRatio_blockLenSq (X : BlockVec d) : blockLenSq X = blockVecDot X X := by
  simp [blockLenSq, blockVecDot, vecNormSq]

theorem upperRatio_phat_eq [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (m h : ℕ)
    (Q : TriadicCube d) (omega : ShellSeq d) (e' : Vec d) (g : Vec d → Vec d)
    (U : Set (Vec d)) :
    blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h Q omega
      (blockSlope nu (m - h) P Q (0 : Vec d) e' (0 : H10Function U).toH1Function.grad g))) =
    blockVecDot
      (ahomSqrtApply nu (m - h) P (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
        (ahomInvSqrtApply nu (m - h) P (e', volumeAverageVec (cubeSet Q) g))))
      (ahomSqrtApply nu (m - h) P (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
        (ahomInvSqrtApply nu (m - h) P (e', volumeAverageVec (cubeSet Q) g)))) := by
  rw [upperRatio_blockLenSq]
  simp only [principalPhat, blockSlope, upperRatio_grad_zero, upperRatio_volumeAverageVec_zero,
    add_zero, zero_add]

theorem upperRatio_vecNormSq_smul (c : ℝ) (v : Vec d) : vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
  unfold vecNormSq
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

theorem upperRatio_lNaught_mono {C C' cStar nu K : ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C') (hK : 0 ≤ K)
    (hc : 0 < cStar) (hnu : 0 < nu) :
    SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C' C' (3 / 4) cStar nu K :=
  SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both hC hCC' hC hCC' hK hc hnu (by norm_num)

theorem upperRatio_algebra {Cp R0 u Λ ℓ h cs L3 K r : ℝ} (hCp : 1 ≤ Cp) (hR0 : 0 ≤ R0)
    (hu : 0 < u) (hΛℓ : Λ ^ 2 ≤ 4 * ℓ ^ 2) (hh : 0 ≤ h) (hcs : 0 ≤ cs) (hcs2 : cs ≤ 2)
    (hL : 0 ≤ L3) (hL2 : L3 ≤ 2) (hK : 0 ≤ K) (hu1 : 4 * (u ^ 2 * ℓ ^ 2) ≤ 1)
    (hr : r ≤ R0 * (u ^ 2 * ℓ ^ 2)) :
    (1 + Cp * u ^ 2 * Λ ^ 2) * (1 + cs * L3 * h * u ^ 2 + K * u ^ 2) + r ≤
      1 + (cs * L3 * h + (13 * Cp + R0 + 1) * (ℓ ^ 2 + K)) * u ^ 2 +
        (13 * Cp + R0 + 1) * u ^ 4 * h ^ 2 := by
  set a : ℝ := u ^ 2 * Λ ^ 2 with ha
  set bq : ℝ := u ^ 2 * ℓ ^ 2 with hbq
  have hu2 : 0 ≤ u ^ 2 := by positivity
  have hbq0 : 0 ≤ bq := by positivity
  have ha0 : 0 ≤ a := by positivity
  have ha4 : a ≤ 4 * bq := by
    rw [ha, hbq]
    nlinarith only [hΛℓ, hu2]
  have ha1 : a ≤ 1 := by linarith only [ha4, hu1]
  have hcl : cs * L3 ≤ 4 := by nlinarith only [hcs, hcs2, hL, hL2]
  have hcl0 : 0 ≤ cs * L3 := mul_nonneg hcs hL
  have hu4 : u ^ 4 = (u ^ 2) ^ 2 := by ring
  -- the cross term
  have hAB : Cp * u ^ 2 * Λ ^ 2 * (cs * L3 * h * u ^ 2) ≤ 2 * Cp * u ^ 4 * h ^ 2 + 8 * Cp * bq := by
    have e1 : Cp * u ^ 2 * Λ ^ 2 * (cs * L3 * h * u ^ 2) = Cp * (cs * L3) * (u ^ 4 * Λ ^ 2 * h) := by
      ring
    have y : 2 * h * Λ ^ 2 ≤ h ^ 2 + (Λ ^ 2) ^ 2 := by nlinarith only [sq_nonneg (h - Λ ^ 2)]
    have h5 : u ^ 4 * Λ ^ 2 * h ≤ (u ^ 4 * h ^ 2 + u ^ 4 * (Λ ^ 2) ^ 2) / 2 := by
      have := mul_le_mul_of_nonneg_left y (by positivity : 0 ≤ u ^ 4)
      nlinarith only [this]
    have h6 : u ^ 4 * (Λ ^ 2) ^ 2 = a ^ 2 := by rw [ha, hu4]; ring
    have h7 : a ^ 2 ≤ a := by nlinarith only [ha0, ha1]
    have h8 : Cp * (cs * L3) * (u ^ 4 * Λ ^ 2 * h) ≤ Cp * 4 * ((u ^ 4 * h ^ 2 + a) / 2) := by
      have hpos : 0 ≤ u ^ 4 * Λ ^ 2 * h := by positivity
      have hc : Cp * (cs * L3) ≤ Cp * 4 := mul_le_mul_of_nonneg_left hcl (by linarith only [hCp])
      calc Cp * (cs * L3) * (u ^ 4 * Λ ^ 2 * h) ≤ Cp * 4 * (u ^ 4 * Λ ^ 2 * h) :=
            mul_le_mul_of_nonneg_right hc hpos
        _ ≤ Cp * 4 * ((u ^ 4 * h ^ 2 + a) / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hCp])
            linarith only [h5, h6, h7]
    rw [e1]
    nlinarith only [h8, ha4, hCp]
  have hAN : Cp * u ^ 2 * Λ ^ 2 * (K * u ^ 2) ≤ Cp * (K * u ^ 2) := by
    have : Cp * u ^ 2 * Λ ^ 2 = Cp * a := by rw [ha]; ring
    rw [this]
    have hN : 0 ≤ K * u ^ 2 := by positivity
    nlinarith only [mul_nonneg (mul_nonneg (by linarith only [hCp] : (0 : ℝ) ≤ Cp) (sub_nonneg.2 ha1)) hN]
  have hA : Cp * u ^ 2 * Λ ^ 2 ≤ 4 * Cp * bq := by
    have : Cp * u ^ 2 * Λ ^ 2 = Cp * a := by rw [ha]; ring
    rw [this]; nlinarith only [ha4, hCp]
  have hN0 : 0 ≤ K * u ^ 2 := by positivity
  have hh2 : 0 ≤ u ^ 4 * h ^ 2 := by positivity
  have hRHS : (cs * L3 * h + (13 * Cp + R0 + 1) * (ℓ ^ 2 + K)) * u ^ 2 =
      cs * L3 * h * u ^ 2 + (13 * Cp + R0 + 1) * bq + (13 * Cp + R0 + 1) * (K * u ^ 2) := by
    rw [hbq]; ring
  have hLHS : (1 + Cp * u ^ 2 * Λ ^ 2) * (1 + cs * L3 * h * u ^ 2 + K * u ^ 2) =
      1 + cs * L3 * h * u ^ 2 + K * u ^ 2 + Cp * u ^ 2 * Λ ^ 2 +
        Cp * u ^ 2 * Λ ^ 2 * (cs * L3 * h * u ^ 2) + Cp * u ^ 2 * Λ ^ 2 * (K * u ^ 2) := by ring
  rw [hLHS, hRHS]
  have hkk : (13 * Cp + R0 + 1) * (K * u ^ 2) ≥ (1 + Cp) * (K * u ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith only [hCp, hR0]) hN0
  have hbb : (13 * Cp + R0 + 1) * bq ≥ (12 * Cp + R0) * bq :=
    mul_le_mul_of_nonneg_right (by linarith only [hCp, hR0]) hbq0
  have hhh : (13 * Cp + R0 + 1) * u ^ 4 * h ^ 2 ≥ 2 * Cp * u ^ 4 * h ^ 2 := by
    have := mul_le_mul_of_nonneg_right (by linarith only [hCp, hR0] : 2 * Cp ≤ 13 * Cp + R0 + 1) hh2
    linarith only [this, mul_assoc (13 * Cp + R0 + 1) (u ^ 4) (h ^ 2), mul_assoc (2 * Cp) (u ^ 4) (h ^ 2)]
  nlinarith only [hAB, hAN, hA, hr, hkk, hbb, hhh, hCp]

theorem upperRatio_limsup {T a b Y0 : ℝ≥0∞} {Zs : ℕ → ℝ≥0∞} {N0 : ℕ} (ha : a ≠ ⊤)
    (hev : ∀ Kc, N0 ≤ Kc → T ≤ a * Zs Kc + b) (hZ : limsup Zs atTop ≤ Y0) :
    T ≤ a * Y0 + b := by
  have h1 : T ≤ limsup (fun Kc => a * Zs Kc + b) atTop := by
    calc T = limsup (fun _ : ℕ => T) atTop := (limsup_const T).symm
      _ ≤ _ := limsup_le_limsup (eventually_atTop.2 ⟨N0, hev⟩)
  have hmono : Monotone (fun x : ℝ≥0∞ => a * x + b) := fun x y hxy =>
    add_le_add (mul_le_mul' le_rfl hxy) le_rfl
  have hcont : Continuous (fun x : ℝ≥0∞ => a * x + b) :=
    ((ENNReal.continuous_const_mul ha).add continuous_const)
  have h2 := hmono.map_limsup_of_continuousAt Zs hcont.continuousAt (F := atTop)
  exact h1.trans (h2.symm.le.trans (hmono hZ))

theorem upperRatio_scale_bounds {m σ ℓ Cc : ℝ} (hmR : (1000000 : ℝ) ≤ m) (hσ : 0 < σ)
    (hℓ : 1 ≤ ℓ)
    (hag : m ^ (3 / 8 : ℝ) * ℓ ^ (3 / 2 : ℝ) ≤ σ) (hσc : σ ≤ Cc * m * m) (hCc : 1 ≤ Cc) :
    4 * ((σ⁻¹) ^ 2 * ℓ ^ 2) ≤ 1 ∧ ((m ^ 10)⁻¹ : ℝ) ≤ Cc ^ 2 * ((σ⁻¹) ^ 2 * ℓ ^ 2) := by
  have hm0 : 0 < m := by linarith only [hmR]
  have h2 : 2 ≤ m ^ (3 / 8 : ℝ) := by
    by_contra hlt
    push Not at hlt
    have h8 : (m ^ (3 / 8 : ℝ)) ^ 8 = m ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, ← Real.rpow_natCast]
      norm_num
    have h9 := pow_le_pow_left₀ (by positivity : 0 ≤ m ^ (3 / 8 : ℝ)) hlt.le 8
    rw [h8] at h9
    have : (1000000 : ℝ) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by norm_num) hmR 3
    norm_num at h9 this
    linarith only [h9, this]
  have h3 : ℓ ≤ ℓ ^ (3 / 2 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hℓ (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [Real.rpow_one] at this
  have h4 : 2 * ℓ ≤ σ := by
    refine le_trans ?_ hag
    exact mul_le_mul h2 h3 (by linarith only [hℓ]) (by positivity)
  have hσ2 : 0 < σ ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have e : 4 * ((σ⁻¹) ^ 2 * ℓ ^ 2) = (2 * ℓ) ^ 2 / σ ^ 2 := by
      field_simp
      norm_num
    rw [e, div_le_one hσ2]
    exact pow_le_pow_left₀ (by linarith only [hℓ]) h4 2
  · have h5 : 1 ≤ Cc ^ 2 * ((σ⁻¹) ^ 2) * m ^ 4 := by
      have hs : σ ^ 2 ≤ (Cc * m * m) ^ 2 := pow_le_pow_left₀ hσ.le hσc 2
      calc (1 : ℝ) = σ ^ 2 * (σ⁻¹) ^ 2 := by field_simp
        _ ≤ (Cc * m * m) ^ 2 * (σ⁻¹) ^ 2 := mul_le_mul_of_nonneg_right hs (by positivity)
        _ = Cc ^ 2 * ((σ⁻¹) ^ 2) * m ^ 4 := by ring
    have h6 : ((m ^ 4)⁻¹ : ℝ) ≤ Cc ^ 2 * ((σ⁻¹) ^ 2) :=
      (inv_le_iff_one_le_mul₀ (by positivity)).2 (by linarith only [h5])
    have h7 : ((m ^ 10)⁻¹ : ℝ) ≤ (m ^ 4)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hmR]) (by norm_num))
    have h8 : (Cc ^ 2 * ((σ⁻¹) ^ 2)) * 1 ≤ (Cc ^ 2 * ((σ⁻¹) ^ 2)) * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hℓ]) (by positivity)
    calc ((m ^ 10)⁻¹ : ℝ) ≤ Cc ^ 2 * ((σ⁻¹) ^ 2) := h7.trans h6
      _ = (Cc ^ 2 * ((σ⁻¹) ^ 2)) * 1 := (mul_one _).symm
      _ ≤ (Cc ^ 2 * ((σ⁻¹) ^ 2)) * ℓ ^ 2 := h8
      _ = Cc ^ 2 * ((σ⁻¹) ^ 2 * ℓ ^ 2) := by ring

end SuperdiffusionCLT.Section5
