/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryV
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryS
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryT
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliE

/-!
# The boundary Caccioppoli block at one scale from the scale-separation data
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2w_main [NeZero d] (hd : 2 ≤ d) {C1 ν S ρ δ : ℝ} (m n h : ℕ) (hnh : n + h = m)
    (hh : 3 ≤ h) (kf : Vec d → Mat d) (y : Vec d) (hC1 : 1 ≤ C1) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hνS : ν ≤ S) (hSm : S ≤ m) (hρ1 : ρ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hm : 1 + 4 * (d : ℝ) ≤ m) (hm5 : 5 * C1 ^ 2 ≤ m)
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m : ℤ)))
      (fun x => ν • (1 : Mat d) + kf (y + x)))
    (hsym : ∀ x, symmPart (ν • (1 : Mat d) + kf x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d (m : ℤ)), ∀ v : Vec d,
      eucNorm (matVecMul (ν • (1 : Mat d) + kf (y + x)) v) ≤ (ν + (m : ℝ) ^ (1 + ρ)) * eucNorm v)
    (hBB0 : ∀ k : Fin d → ℤ,
      (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) '' cubeSet (originCube d (n : ℤ)) ⊆
        cubeSet (originCube d (m : ℤ)) →
      ∀ (u : H1Function (openCubeSet (originCube d (n : ℤ)))) (f : Vec d → ℝ),
      IsWeakSolutionOn (fun x => ν • (1 : Mat d) +
          kf (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (openCubeSet (originCube d (n : ℤ))) u f (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
          (1 / 4 : ℝ) (fun x => matVecMul (ν • (1 : Mat d) +
            kf (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) - S • (1 : Mat d)) (u.grad x))) ≤
        ENNReal.ofReal (C1 * Real.sqrt S * δ * Real.sqrt ν) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal ((C1 * Real.sqrt S * δ * Real.sqrt ν + C1 * (|ν - S| + (m : ℝ) ^ (1 + ρ))) *
              (C1 * (3 : ℝ) ^ (n : ℤ) / ν)) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (n : ℤ)) (ENNReal.ofReal (sobStar d)).conjExponent f ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
          (1 / 4 : ℝ) u.grad) ≤
        ENNReal.ofReal (C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal ((C1 * (Real.sqrt S)⁻¹ * Real.sqrt ν + C1) * (C1 * (3 : ℝ) ^ (n : ℤ) / ν)) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (n : ℤ)) (ENNReal.ofReal (sobStar d)).conjExponent f)
    {E C Cth cden Kτ : ℝ} {N : ℕ} {a : CoeffField d} {W : Set (Vec d)} (hWo : IsOpen W)
    (hC0 : 0 < C)
    (hflux : ∀ u : H1Function (openCubeSet (originCube d (m : ℤ)) ∩ W),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)) ∩ W) (fun x => matVecMul (a x) (u.grad x)))
    (hbridge : ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)) ∩ W)) (f : Vec d → ℝ),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)) ∩ W) (fun x => matVecMul (a x) (u.grad x)) →
      IsWeakSolutionOn a (openCubeSet (originCube d (m : ℤ)) ∩ W) u f (fun _ => 0) →
      IsWeakSolutionOn (fun x => ν • (1 : Mat d) + kf (y + x)) (openCubeSet (originCube d (m : ℤ)) ∩ W)
        u f (fun _ => 0))
    (hCth0 : 0 ≤ Cth) (hcden : 0 < cden)
    (hdenW : cden * cubeVolume (originCube d (m : ℤ)) ≤
      (volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W)).toReal)
    (hBW : (volume (ca2_Bset (m : ℤ) h ((3 : ℝ) ^ (m : ℤ) / 4) W)).toReal ≤
      Cth * ((3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ)) * cubeVolume (originCube d (m : ℤ)))
    (hsep : (m : ℝ) ^ (8 : ℝ) * ν ^ (-(8 : ℝ)) * (1 : ℝ) ^ (8 : ℝ) *
      (3 : ℝ) ^ ((1 / (d : ℝ)) * (((n : ℤ) : ℝ) - (m : ℝ))) ≤ ((m : ℝ) ^ N)⁻¹)
    (hN1 : 1 ≤ N) (hEN : E + 1 ≤ N) (hKτ1 : 1 ≤ Kτ) (hCthm : Cth ≤ m)
    (hKm : Kτ * (1 + 4 * d) ≤ m) (hKτdef : 4 * ca2_CB d * Cth ^ (1 / (d : ℝ)) ≤ Kτ)
    (hC : ca2_Cdet d (4 * C1 ^ 2) / cden ≤ C) :
    LipCaccBdryS a ν S C E W 0 m := by
  classical
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith only [hm, this]
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hS0 : 0 ≤ S := (hν.trans_le hνS).le
  have hd1 : 1 ≤ d := by omega
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hnm : (m : ℤ) - (h : ℤ) = (n : ℤ) := by
    have : (m : ℤ) = n + h := by exact_mod_cast hnh.symm
    omega
  -- the scale-separation quantities
  obtain ⟨yy, hyydef⟩ : ∃ yy : ℝ, yy = (3 : ℝ) ^ ((1 / (d : ℝ)) * (((n : ℤ) : ℝ) - (m : ℝ))) := ⟨_, rfl⟩
  have hyy0 : 0 < yy := by rw [hyydef]; positivity
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hxyy : x = yy ^ d := by
    rw [hyydef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (1 / (d : ℝ) * (((n : ℤ) : ℝ) - (m : ℝ))) * (d : ℝ) = (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) := by
      push_cast; field_simp
    rw [this, Real.rpow_intCast, zpow_sub₀ (by norm_num), hxdef, zpow_natCast]
  have hsep' : (m : ℝ) ^ 8 * (ν ^ 8)⁻¹ * yy ≤ ((m : ℝ) ^ N)⁻¹ := by
    have e1 : (m : ℝ) ^ (8 : ℝ) = (m : ℝ) ^ 8 := by exact_mod_cast Real.rpow_natCast (m : ℝ) 8
    have e2 : ν ^ (-(8 : ℝ)) = (ν ^ 8)⁻¹ := by
      rw [Real.rpow_neg hν.le]; congr 1; exact_mod_cast Real.rpow_natCast ν 8
    rw [e1, e2, Real.one_rpow, mul_one, ← hyydef] at hsep
    exact hsep
  have hmN : (m : ℝ) ≤ (m : ℝ) ^ N := by
    calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m : ℝ) ^ N := pow_le_pow_right₀ hm1 hN1
  have hq1 : 1 ≤ (m : ℝ) ^ 8 * (ν ^ 8)⁻¹ := by
    have h1 : 1 ≤ (m : ℝ) ^ 8 := one_le_pow₀ hm1
    have h2 : 1 ≤ (ν ^ 8)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]; exact pow_le_one₀ hν.le hν1
    nlinarith only [h1, h2]
  have hyyN : yy ≤ ((m : ℝ) ^ N)⁻¹ := by
    refine le_trans ?_ hsep'
    calc yy = 1 * yy := (one_mul _).symm
      _ ≤ ((m : ℝ) ^ 8 * (ν ^ 8)⁻¹) * yy := mul_le_mul_of_nonneg_right hq1 hyy0.le
      _ = _ := by ring
  have hyy1 : yy ≤ 1 := by
    refine hyyN.trans ?_
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ hm1
  have hxy : x ≤ yy := by
    rw [hxyy]
    exact pow_le_of_le_one hyy0.le hyy1 (by omega)
  have hΛ0 : 0 ≤ ν + (m : ℝ) ^ (1 + ρ) := by positivity
  have hΛ : ν + (m : ℝ) ^ (1 + ρ) ≤ 2 * (m : ℝ) ^ 2 := by
    have h1 := ca1w_rpow_le_sq (m := (m : ℝ)) hm1 hρ1
    have h2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm1
    linarith only [h1, h2, hν1]
  have hCB : 0 ≤ ca2_CB d := by
    unfold ca2_CB ca2_C1
    positivity
  obtain ⟨⟨hϑ0, hϑ1⟩, hτx, hτs, hτΞ, hεB⟩ := ca2w_params (d := d) (N := N) hd1 hν hν1 hm1 hSm hS0 hΛ hΛ0
    hyy0 hxyy hN1 hsep' hKτ1 hCB hCth0 hCthm hKm hKτdef hxy
  -- the scale-separation inequality used by the coefficient bounds
  have hmaster : x * ((m : ℝ) / ν) ^ 4 ≤ (m : ℝ)⁻¹ := by
    have h1 : x * ((m : ℝ) / ν) ^ 4 ≤ (m : ℝ) ^ 8 * (ν ^ 8)⁻¹ * yy := by
      rw [div_pow, div_eq_mul_inv]
      have h2 : (ν ^ 4)⁻¹ ≤ (ν ^ 8)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_of_le_one hν.le hν1 (by norm_num)
      have h3 : (m : ℝ) ^ 4 ≤ (m : ℝ) ^ 8 := pow_le_pow_right₀ hm1 (by norm_num)
      calc x * ((m : ℝ) ^ 4 * (ν ^ 4)⁻¹) ≤ yy * ((m : ℝ) ^ 8 * (ν ^ 8)⁻¹) := by gcongr
        _ = _ := by ring
    exact h1.trans (hsep'.trans (by rw [inv_le_inv₀ (by positivity) hm0]; exact hmN))
  have hx1 : x ≤ ((m : ℝ) ^ N)⁻¹ := hxy.trans hyyN
  -- the bound for the `G₂` term
  have hSx : S * x ^ 2 ≤ ((m : ℝ) ^ (-E)) ^ 2 := by
    have hmN0 : 0 < (m : ℝ) ^ N := by positivity
    have hE' : (m : ℝ) ^ E ≤ (m : ℝ) ^ (N - 1) := by
      have h1 : E ≤ ((N - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hN1]; push_cast; linarith only [hEN]
      have := Real.rpow_le_rpow_of_exponent_le hm1 h1
      rwa [Real.rpow_natCast] at this
    have hE0 : 0 < (m : ℝ) ^ E := Real.rpow_pos_of_pos hm0 E
    have h2 : S * x ^ 2 ≤ (m : ℝ) * (((m : ℝ) ^ N)⁻¹) ^ 2 :=
      mul_le_mul hSm (pow_le_pow_left₀ hx0 hx1 2) (sq_nonneg _) hm0.le
    refine h2.trans ?_
    rw [Real.rpow_neg hm0.le, inv_pow, inv_pow, ← div_eq_mul_inv, ← one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : ((m : ℝ) ^ E) ^ 2 ≤ ((m : ℝ) ^ (N - 1)) ^ 2 := pow_le_pow_left₀ hE0.le hE' 2
    have h4 : ((m : ℝ) ^ N) ^ 2 = (m : ℝ) ^ 2 * ((m : ℝ) ^ (N - 1)) ^ 2 := by
      rw [← mul_pow, ← pow_succ']
      rw [Nat.sub_add_cancel hN1]
    rw [h4, one_mul]
    have h5 : (0 : ℝ) ≤ ((m : ℝ) ^ (N - 1)) ^ 2 := sq_nonneg _
    nlinarith only [h3, h5, hm1, mul_nonneg hm0.le h5]
  have hL : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hC1' : ca2_Cdet d (4 * C1 ^ 2) / cden ≤ C := hC
  have hCd0 : 0 ≤ ca2_Cdet d (4 * C1 ^ 2) := by
    unfold ca2_Cdet ca2_Cal ca2_c8
    have hKb := cubeBesovW12EmbeddingConstant_nonneg d
    positivity
  have hxe : x = (3 : ℝ) ^ n / (3 : ℝ) ^ m := by rw [hxdef, zpow_natCast, zpow_natCast]
  have hcore : ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)) ∩ W)) (f : Vec d → ℝ)
      (γ : Vec d → ℝ), ContDiff ℝ 2 γ → ∀ (G1 G2 : ℝ), 0 ≤ G1 → 0 ≤ G2 →
      (∀ x ∈ openCubeSet (originCube d (m : ℤ)) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1) →
      (∀ x ∈ openCubeSet (originCube d (m : ℤ)) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) →
      MemLp f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W)) →
      IsWeakSolutionOn (fun x => ν • (1 : Mat d) + kf (y + x))
        (openCubeSet (originCube d (m : ℤ)) ∩ W) u f (fun _ => 0) →
      LocalizedZeroTraceFunctionOn (openCubeSet (originCube d (m : ℤ)) ∩ W)
        (openCubeSet (originCube d (m : ℤ))) (fun x => u.toFun x - γ x) →
      ν * ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, vecNormSq (u.grad x) ≤
        ca2_Cdet d (4 * C1 ^ 2) * cubeVolume (originCube d (m : ℤ)) *
          (S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * ((cubeVolume (originCube d (m : ℤ)))⁻¹ *
              ∫ x in openCubeSet (originCube d (m : ℤ)) ∩ W, (u.toFun x - γ x) ^ 2) +
            S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * ((cubeVolume (originCube d (m : ℤ)))⁻¹ *
              ∫ x in openCubeSet (originCube d (m : ℤ)) ∩ W, f x ^ 2) +
            S * G1 ^ 2 + S * ((3 : ℝ) ^ n) ^ 2 * G2 ^ 2) := by
    intro u f γ hγ G1 G2 hG1 hG2 hb1 hb2 hf hu hZ
    have := ca2w_scale hd m n h hnh hh kf y hC1 hν hν1 hνS hSm hρ1 hδ0 hδ1 hm hm5 (by rw [← hxdef]; exact hmaster) hell hsym hop hBB0
      hWo u hf hu hγ hG1 hG2 hb1 hb2 hZ (ϑ := Cth * x) (τ := Kτ * (m : ℝ) ^ 4 * (ν ^ 2)⁻¹ * yy) hϑ0 hϑ1
      (by rw [hxdef] at *; exact hBW) (by rw [← hxdef]; exact hτx) hτs hτΞ hεB
    simpa only [zpow_natCast] using this
  obtain ⟨lam, Lam, hEll⟩ := hell
  have hDm : MeasurableSet (openCubeSet (originCube d (m : ℤ)) ∩ W) :=
    ((isOpen_openCubeSet _).inter hWo).measurableSet
  have hEllA : IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m : ℤ)) ∩ W)
      (fun x => ν • (1 : Mat d) + kf (y + x)) := hEll.mono hDm Set.inter_subset_left
  refine ca2w_lip_of_core (A := fun x => ν • (1 : Mat d) + kf (y + x)) (Cd := ca2_Cdet d (4 * C1 ^ 2))
    (cden := cden) (ℓ2 := ((3 : ℝ) ^ n) ^ 2) m hWo hν (hν.trans_le hνS) hC0 hCd0 hcden hEllA hflux hbridge
    hcore hdenW hC1' ?_
  have hCn : 0 ≤ ca2_Cdet d (4 * C1 ^ 2) / cden := by positivity
  have hsq : S * ((3 : ℝ) ^ n) ^ 2 ≤ ((m : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ m) ^ 2 := by
    have e : ((3 : ℝ) ^ n) ^ 2 = x ^ 2 * ((3 : ℝ) ^ m) ^ 2 := by
      rw [hxe, div_pow]; field_simp
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hSx (sq_nonneg _)
  calc ca2_Cdet d (4 * C1 ^ 2) / cden * (S * ((3 : ℝ) ^ n) ^ 2)
      ≤ C * (((m : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ m) ^ 2) :=
        mul_le_mul hC1' hsq (by positivity) hC0.le
    _ = _ := by ring

end SuperdiffusionCLT.Section7
