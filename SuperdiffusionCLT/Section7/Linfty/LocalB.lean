/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Local

@[expose] public section

open MeasureTheory Homogenization Metric
open scoped Pointwise ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem linf_local_arith {Cl C1 κs σ F G G2 X0 X1 Kc Kp T mj Kn : ℝ} (hCl : 0 ≤ Cl)
    (hC1a : 6 * κs ≤ C1) (hC1b : 1 ≤ C1) (hκs : 0 ≤ κs) (hσ : 0 < σ) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hG2 : 0 ≤ G2) (hX0 : 0 ≤ X0) (hX1 : 0 ≤ X1) (hKc : 0 ≤ Kc) (hKp : 0 ≤ Kp) (hT : 0 ≤ T)
    (hmj0 : 0 ≤ mj) (hmj : mj ≤ Kn) :
    Cl * (3 * Kc) * (κs * (2 * X0 + X1)) + Cl * σ⁻¹ * T * F + Cl * mj * G + Cl * Kp * T * G2 ≤
      C1 * Cl * (Kc * (X0 + X1) + σ⁻¹ * (3 * T) * F + Kn * G + Kp * (3 * T) * G2) := by
  have hσi : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
  have h1 : Cl * (3 * Kc) * (κs * (2 * X0 + X1)) ≤ C1 * Cl * (Kc * (X0 + X1)) := by
    have e : Cl * (3 * Kc) * (κs * (2 * X0 + X1)) = Cl * Kc * (3 * κs * (2 * X0 + X1)) := by ring
    rw [e]
    have : 3 * κs * (2 * X0 + X1) ≤ C1 * (X0 + X1) := by
      nlinarith only [hC1a, hκs, hX0, hX1]
    calc Cl * Kc * (3 * κs * (2 * X0 + X1)) ≤ Cl * Kc * (C1 * (X0 + X1)) := by gcongr
      _ = C1 * Cl * (Kc * (X0 + X1)) := by ring
  have h2 : Cl * σ⁻¹ * T * F ≤ C1 * Cl * (σ⁻¹ * (3 * T) * F) := by
    have : 0 ≤ Cl * σ⁻¹ * T * F := by positivity
    nlinarith only [this, hC1b, hCl, hσi, hT, hF, mul_nonneg (mul_nonneg hCl hσi) (mul_nonneg hT hF)]
  have h3 : Cl * mj * G ≤ C1 * Cl * (Kn * G) := by
    have hK0 : 0 ≤ Kn := hmj0.trans hmj
    have : Cl * mj * G ≤ Cl * Kn * G := by gcongr
    have h4 : 0 ≤ Cl * Kn * G := by positivity
    nlinarith only [this, h4, hC1b]
  have h4 : Cl * Kp * T * G2 ≤ C1 * Cl * (Kp * (3 * T) * G2) := by
    have : 0 ≤ Cl * Kp * T * G2 := by positivity
    nlinarith only [this, hC1b, mul_nonneg (mul_nonneg hCl hKp) (mul_nonneg hT hG2)]
  linarith only [h1, h2, h3, h4]

private theorem linf_local_Bk_nonneg {K n : ℕ} {σ F G G2 X0 X1 Kp : ℝ} (hσ : 0 < σ)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hG2 : 0 ≤ G2) (hX0 : 0 ≤ X0) (hX1 : 0 ≤ X1)
    (hKn : 0 ≤ (K : ℝ) - (n : ℝ)) (hKp : 0 ≤ Kp) :
    0 ≤ ((3 : ℝ)⁻¹) ^ K * (X0 + X1) + σ⁻¹ * (3 : ℝ) ^ K * F + ((K : ℝ) - (n : ℝ)) * G +
      Kp * (3 : ℝ) ^ K * G2 := by
  positivity

/-- **The local inputs** (`e.Dir.new.Linfty.local.grad`, and the `L²`
input of the boundary De Giorgi step): from the boundary Lipschitz estimate at the centres of a
fine grid, with the top scale `m' = K - 1`, the oscillations on `(z + □_{m'}) ∩ R U` being bounded
by norms over `R U` through the lower volume bound. -/
theorem linf_local [NeZero d] {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U)
    (hU0 : U ⊆ openCubeSet (originCube d 0)) :
    ∃ (s0 : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ (a : CoeffField d) (nu σ Cl E : ℝ) (K n m' : ℕ) (R : ℝ),
      0 < nu → 0 < σ → 1 ≤ Cl → 0 ≤ E → m' + 1 = K → n + 4 ≤ K → (3 : ℝ) ^ K < 3 * R →
      R ≤ (3 : ℝ) ^ K → C * (3 : ℝ) ^ (n + 4) ≤ (3 : ℝ) ^ K →
      ∀ (f gt : Vec d → ℝ) (F G G2 c0 : ℝ), ContDiff ℝ 2 gt → 0 ≤ F → 0 ≤ G → 0 ≤ G2 →
        (∀ᵐ x ∂volume.restrict (R • U), |f x| ≤ F) →
        AEStronglyMeasurable f (volume.restrict (R • U)) → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
        (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ G2) →
      ∀ v : H1Function (R • U), IsWeakSolutionOn a (R • U) v f (fun _ => 0) →
        MemH10 (R • U) (fun x => v.toFun x - gt x) →
      (∀ j : ℕ, n ≤ j → j ≤ n + 3 →
        ∀ z ∈ gridPts d ((j : ℤ) - s0) ((3 : ℝ) ^ (K + 2)), z ∈ R • U →
        ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ R • U),
          IsWeakSolutionOn a (shiftCube z (m' : ℤ) ∩ R • U) u f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ R • U)
            (shiftCube z (m' : ℤ)) (fun x => u.toFun x - gt x) →
          ∀ Rr : ℝ≥0∞,
            Rr = ENNReal.ofReal (Cl * (3 : ℝ) ^ (-(m' : ℝ))) *
                (lpBar (shiftCube z (m' : ℤ) ∩ R • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ R • U, u.toFun w) +
                  lpBar (shiftCube z (m' : ℤ) ∩ R • U) 2 (fun x => u.toFun x - gt x)) +
              ENNReal.ofReal (Cl * σ⁻¹ * (3 : ℝ) ^ m') *
                eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ R • U)) +
              ENNReal.ofReal (Cl * ((m' : ℝ) - (j : ℝ))) *
                eLpNorm (fun x => ‖fderiv ℝ gt x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
              ENNReal.ofReal (Cl * (K : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ gt) x‖) ⊤
                  (volume.restrict (shiftCube z (m' : ℤ))) →
            ENNReal.ofReal ((Real.sqrt σ)⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (j : ℤ) ∩ R • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℝ))) *
                  lpBar (shiftCube z (j : ℤ) ∩ R • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (j : ℤ) ∩ R • U, u.toFun w) ≤ Rr ∧
              (¬ shiftCube z (j : ℤ) ⊆ R • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℝ))) *
                  lpBar (shiftCube z (j : ℤ) ∩ R • U) 2 (fun x => u.toFun x - gt x) ≤ Rr)) →
      ∀ Rb : ℝ,
        Rb = C * Cl * (((3 : ℝ)⁻¹) ^ K *
              ((lpBar (R • U) 2 (fun x => v.toFun x - c0)).toReal +
                (lpBar (R • U) 2 (fun x => v.toFun x - gt x)).toReal) +
            σ⁻¹ * (3 : ℝ) ^ K * F + ((K : ℝ) - (n : ℝ)) * G + (K : ℝ) ^ (-E) * (3 : ℝ) ^ K * G2) →
        (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ R • U →
          lpBar (shiftCube (l2b_pt n k) ((n : ℤ) + 1)) 2 (fun x => eucNorm (v.grad x)) ≤
            ENNReal.ofReal (Real.sqrt σ * (Real.sqrt nu)⁻¹ * Rb)) ∧
        (∀ k : Fin d → ℤ,
          (∃ x ∈ l2b_cell (l2b_pt n k) n ∩ R • U,
            Metric.infDist x (R • U)ᶜ < 10 * (3 : ℝ) ^ n) →
          eLpNorm (fun x => v.toFun x - gt x) 2
              (volume.restrict (R • U ∩ shiftCube (l2b_pt n k) ((n : ℤ) + 2))) ≤
            ENNReal.ofReal (((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ n * Rb))) := by
  obtain ⟨s_fc, c_fc, hc_fc, hcover⟩ := linf_fine_cover hU
  obtain ⟨c_d, hc_d, hdens⟩ := linf_density hU
  have hUo : IsOpen U := hU.1
  set κ : ℝ := (3 : ℝ) ^ d / c_d with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set C1 : ℝ := max (6 * Real.sqrt κ) 1 with hC1
  have hC1a : 6 * Real.sqrt κ ≤ C1 := le_max_left _ _
  have hC1b : 1 ≤ C1 := le_max_right _ _
  refine ⟨s_fc + 3, (3 : ℝ) ^ (d + 3) * C1 + 1 / c_fc, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ 3 ^ (d + 3) := one_le_pow₀ (by norm_num)
    have : 0 < 1 / c_fc := by positivity
    nlinarith only [h1, hC1b, this]
  intro a nu σ Cl E K n m' R hnu hσ hCl hE hm hnK hRlo hRhi hCn f gt F G G2 c0 hgt hF hG hG2 hf hfm
    hG1 hG2' v hv hv0 hblock Rb hRb
  set C : ℝ := (3 : ℝ) ^ (d + 3) * C1 + 1 / c_fc with hCdef
  have hK3 : (3 : ℝ) ^ K = 3 * 3 ^ m' := by rw [← hm, pow_succ]; ring
  have hR : 0 < R := by
    have : (0 : ℝ) < 3 ^ K := by positivity
    linarith only [hRlo, this]
  have hRm : (3 : ℝ) ^ m' ≤ R := by
    have : (0 : ℝ) < 3 ^ m' := by positivity
    linarith only [hRlo, hK3]
  have hWo : IsOpen (R • U) := hUo.smul₀ hR.ne'
  have hWball := linf_local_dil_subset hU0 hR
  have hWb : ∀ x ∈ (R • U), ‖x‖ ≤ R / 2 := fun x hx => by
    have := hWball hx
    rw [mem_ball_zero_iff] at this
    exact this.le
  have hWvol := linf_local_vol_le hU0 hR
  have hWfin : volume (R • U) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWvol
  have hφ : MemLp v.toFun 2 (volume.restrict (R • U)) := v.memL2
  have hψ : MemLp (fun x => v.toFun x - gt x) 2 (volume.restrict (R • U)) :=
    linf_local_memLp_sub hWo.measurableSet hWfin hWb (hgt.of_le (by norm_num)) hG1 hφ
  have hvolS : ∀ z ∈ (R • U), ENNReal.ofReal (c_d * ((3 : ℝ) ^ m') ^ d) ≤
      volume (shiftCube z (m' : ℤ) ∩ (R • U)) := fun z hz => hdens R m' hRm z hz
  have hvolκ : ∀ z ∈ (R • U), volume (R • U) ≤ ENNReal.ofReal κ * volume (shiftCube z (m' : ℤ) ∩ (R • U)) := by
    intro z hz
    calc volume (R • U) ≤ ENNReal.ofReal (R ^ d) := hWvol
      _ ≤ ENNReal.ofReal (((3 : ℝ) ^ K) ^ d) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hR.le hRhi d)
      _ = ENNReal.ofReal κ * ENNReal.ofReal (c_d * ((3 : ℝ) ^ m') ^ d) := by
          rw [← ENNReal.ofReal_mul hκ0]
          congr 1
          rw [hK3, mul_pow, hκ]
          field_simp
      _ ≤ ENNReal.ofReal κ * volume (shiftCube z (m' : ℤ) ∩ (R • U)) := by
          gcongr
          exact hvolS z hz
  have hgd1 : Continuous (fderiv ℝ gt) := hgt.continuous_fderiv (by norm_num)
  have hgd2 : Continuous (fderiv ℝ (fderiv ℝ gt)) :=
    (hgt.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hCl0 : 0 ≤ Cl := by linarith only [hCl]
  have hn2 : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ gt) x‖) :=
    Continuous.norm (E := Vec d →L[ℝ] Vec d →L[ℝ] ℝ) hgd2
  have hX0 : 0 ≤ lipL2 (R • U) (fun x => v.toFun x - c0) := ENNReal.toReal_nonneg
  have hX1 : 0 ≤ lipL2 (R • U) (fun x => v.toFun x - gt x) := ENNReal.toReal_nonneg
  have hKn : (0 : ℝ) ≤ (K : ℝ) - (n : ℝ) := by
    have : ((n + 4 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnK
    push_cast at this
    linarith only [this]
  set Bk : ℝ := ((3 : ℝ)⁻¹) ^ K * (lipL2 (R • U) (fun x => v.toFun x - c0) +
      lipL2 (R • U) (fun x => v.toFun x - gt x)) + σ⁻¹ * (3 : ℝ) ^ K * F + ((K : ℝ) - (n : ℝ)) * G +
      (K : ℝ) ^ (-E) * (3 : ℝ) ^ K * G2 with hBk
  have hRb' : Rb = C * Cl * Bk := hRb
  have hKp : 0 ≤ (K : ℝ) ^ (-E) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBk0 : 0 ≤ Bk := linf_local_Bk_nonneg hσ hF hG hG2 hX0 hX1 hKn hKp
  have hC1C : C1 ≤ C := by
    have h1 : (1 : ℝ) ≤ 3 ^ (d + 3) := one_le_pow₀ (by norm_num)
    have : 0 < 1 / c_fc := by positivity
    nlinarith only [h1, hC1b, this]
  have hKc : (3 : ℝ) ^ (-(m' : ℝ)) = 3 * ((3 : ℝ)⁻¹) ^ K := by
    rw [← hm, pow_succ, Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
    field_simp
  have key : ∀ j : ℕ, n ≤ j → j ≤ n + 3 →
      ∀ z ∈ gridPts d ((j : ℤ) - ((s_fc + 3 : ℕ) : ℤ)) ((3 : ℝ) ^ (K + 2)), z ∈ (R • U) →
      (ENNReal.ofReal ((Real.sqrt σ)⁻¹ * Real.sqrt nu) *
            lpBar (shiftCube z (j : ℤ) ∩ (R • U)) 2 (fun x => eucNorm (v.grad x)) +
          ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℝ))) *
            lpBar (shiftCube z (j : ℤ) ∩ (R • U)) 2
              (fun x => v.toFun x - ⨍ w in shiftCube z (j : ℤ) ∩ (R • U), v.toFun w) ≤
          ENNReal.ofReal (C1 * Cl * Bk)) ∧
      (¬ shiftCube z (j : ℤ) ⊆ (R • U) →
        ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℝ))) *
          lpBar (shiftCube z (j : ℤ) ∩ (R • U)) 2 (fun x => v.toFun x - gt x) ≤
          ENNReal.ofReal (C1 * Cl * Bk)) := by
    intro j hj1 hj2 z hz hzW
    have hSo : IsOpen (shiftCube z (m' : ℤ) ∩ (R • U)) :=
      (lip_bdry_approx_isOpen_cube z m').inter hWo
    obtain ⟨hweak, hloc⟩ := linf_local_restrict hWo z m' hv hv0
    have hS0 : volume (shiftCube z (m' : ℤ) ∩ (R • U)) ≠ 0 := by
      have := hvolS z hzW
      have hp : 0 < c_d * ((3 : ℝ) ^ m') ^ d := by positivity
      exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hp) this).ne'
    have hOsc := linf_local_osc_le (Set.inter_subset_right (s := shiftCube z (m' : ℤ)) (t := (R • U)))
      hκ0 hS0 hWfin (hvolκ z hzW) hφ hψ c0
    have hEb : eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ (R • U))) ≤ ENNReal.ofReal F :=
      linf_local_essSup_le _ (hfm.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
        (ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hf)
    have hEc : eLpNorm (fun x => ‖fderiv ℝ gt x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) ≤
        ENNReal.ofReal G :=
      linf_local_essSup_le _ (hgd1.norm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          rw [abs_of_nonneg (by positivity)]
          exact hG1 x)
    have hEe : eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ gt) x‖) ⊤
        (volume.restrict (shiftCube z (m' : ℤ))) ≤ ENNReal.ofReal G2 :=
      linf_local_essSup_le _ hn2.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [abs_of_nonneg (by positivity)]
          exact hG2' x)
    have hmj0 : 0 ≤ (m' : ℝ) - (j : ℝ) := by
      have : j ≤ m' := by
        have := hj2.trans (Nat.le_of_succ_le_succ (hm ▸ hnK : n + 3 + 1 ≤ m' + 1))
        exact this
      have : (j : ℝ) ≤ (m' : ℝ) := by exact_mod_cast this
      linarith only [this]
    have hmj : (m' : ℝ) - (j : ℝ) ≤ (K : ℝ) - (n : ℝ) := by
      have h1 : (n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have h2 : (m' : ℝ) ≤ (K : ℝ) := by exact_mod_cast (hm ▸ Nat.le_succ m' : m' ≤ K)
      linarith only [h1, h2]
    have hO0 : 0 ≤ Real.sqrt κ * (2 * lipL2 (R • U) (fun x => v.toFun x - c0) +
        lipL2 (R • U) (fun x => v.toFun x - gt x)) := by positivity
    have hRr : ENNReal.ofReal (Cl * (3 : ℝ) ^ (-(m' : ℝ))) *
          (lpBar (shiftCube z (m' : ℤ) ∩ (R • U)) 2
              (fun x => v.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ (R • U), v.toFun w) +
            lpBar (shiftCube z (m' : ℤ) ∩ (R • U)) 2 (fun x => v.toFun x - gt x)) +
        ENNReal.ofReal (Cl * σ⁻¹ * (3 : ℝ) ^ m') *
          eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ (R • U))) +
        ENNReal.ofReal (Cl * ((m' : ℝ) - (j : ℝ))) *
          eLpNorm (fun x => ‖fderiv ℝ gt x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
        ENNReal.ofReal (Cl * (K : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
          eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ gt) x‖) ⊤
            (volume.restrict (shiftCube z (m' : ℤ))) ≤ ENNReal.ofReal (C1 * Cl * Bk) := by
      refine (linf_local_Rr_le (by positivity) (by positivity)
        (mul_nonneg hCl0 hmj0) (by positivity) hF hG hG2 hO0 hOsc hEb hEc hEe).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hari := linf_local_arith (Cl := Cl) (C1 := C1) (κs := Real.sqrt κ) (σ := σ) (F := F)
        (G := G) (G2 := G2) (X0 := lipL2 (R • U) (fun x => v.toFun x - c0))
        (X1 := lipL2 (R • U) (fun x => v.toFun x - gt x)) (Kc := ((3 : ℝ)⁻¹) ^ K)
        (Kp := (K : ℝ) ^ (-E)) (T := (3 : ℝ) ^ m') (mj := (m' : ℝ) - (j : ℝ))
        (Kn := (K : ℝ) - (n : ℝ)) hCl0 hC1a hC1b (Real.sqrt_nonneg _) hσ hF hG
        hG2 hX0 hX1 (by positivity) hKp (by positivity) hmj0 hmj
      rw [hKc]
      rw [hBk, hK3]
      linarith only [hari]
    have hbl := hblock j hj1 hj2 z hz hzW (v.restrict hSo Set.inter_subset_right) hweak hloc _ rfl
    exact ⟨hbl.1.trans hRr, fun h => (hbl.2 h).trans hRr⟩
  clear hblock hv hv0 hfm hf hG1 hG2' hgd1 hgd2 hn2 hφ hψ hvolκ hvolS hgt hWvol hWball hWfin
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · set z : Vec d := l2b_pt n k with hz
    have e1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1]
    have hQsub : shiftCube z ((n + 1 : ℕ) : ℤ) ⊆ l2b_cell z (n + 1) := by
      intro x hx
      rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball] at hx
      rw [l2b_mem_cell]
      intro i
      have h1 := dist_le_pi_dist x z i
      rw [Real.dist_eq] at h1
      have h := lt_of_le_of_lt h1 hx
      rw [abs_lt] at h
      constructor <;> linarith only [h.1, h.2]
    have hQW := hQsub.trans hk
    have hQvol := lip_bdry_approx_vol_cube z (n + 1)
    have hQ0 : volume (shiftCube z ((n + 1 : ℕ) : ℤ)) ≠ 0 := by
      rw [hQvol]
      exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hQT := lip_bdry_approx_vol_cube_ne_top z (n + 1)
    have hh : AEStronglyMeasurable (fun x => eucNorm (v.grad x))
        (volume.restrict (shiftCube z ((n + 1 : ℕ) : ℤ))) :=
      (wh2_aemeasurable_eucNorm v).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono hQW le_rfl)
    refine linf_local_union_le (T := fun j : Fin d → Fin 3 => shiftCube (linfTilePt z n j) (n : ℤ))
      hQ0 hQT (fun j => linf_local_tile_sub z n j) (linf_local_tile_cover z n)
      (le_of_eq (linf_local_tile_vol_sum z n)) hh ?_
    intro j
    set p := linfTilePt z n j with hp
    have hpT : shiftCube p (n : ℤ) ⊆ (R • U) := (linf_local_tile_sub z n j).trans hQW
    have hpW : p ∈ R • U := hpT (rc_mem_shiftCube_self p n)
    have hgrid : p ∈ gridPts d ((n : ℤ) - ((s_fc + 3 : ℕ) : ℤ)) ((3 : ℝ) ^ (K + 2)) := by
      refine linf_local_mem_grid (by positivity) (fun i => ?_) (fun i => ?_)
      · refine ⟨k i + ((j i : ℕ) : ℤ) - 1, ?_⟩
        simp only [hp, linfTilePt, hz, l2b_pt]
        push_cast
        ring
      · have h1 := hWb p hpW
        have h2 := norm_le_pi_norm p i
        rw [Real.norm_eq_abs] at h2
        have h3 : (3 : ℝ) ^ K ≤ 3 ^ (K + 2) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_right K 2)
        linarith only [h1, h2, h3, hRhi, hR]
    have hk1 := (key n le_rfl (Nat.le_add_right n 3) p hgrid hpW).1
    rw [Set.inter_eq_left.2 hpT] at hk1
    have hc : 0 < (Real.sqrt σ)⁻¹ * Real.sqrt nu := by positivity
    refine (linf_local_le_of_mul_le hc hk1).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hRb']
    have e : ((Real.sqrt σ)⁻¹ * Real.sqrt nu)⁻¹ = Real.sqrt σ * (Real.sqrt nu)⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm]
    rw [e]
    have h4 : C1 * Cl * Bk ≤ C * Cl * Bk :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1C hCl0) hBk0
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  · obtain ⟨x, ⟨hxc, hxW⟩, hxd⟩ := hk
    set z : Vec d := l2b_pt n k with hz
    have hCc : 1 / c_fc ≤ C := by
      have : 0 ≤ (3 : ℝ) ^ (d + 3) * C1 := by positivity
      simp only [hCdef]
      linarith only [this]
    have h3n : (3 : ℝ) ^ n ≤ c_fc * R := by
      have h1 : 1 / c_fc * (3 : ℝ) ^ (n + 4) ≤ C * 3 ^ (n + 4) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have h2 : 1 / c_fc * (3 : ℝ) ^ (n + 4) < 3 * R := by linarith only [h1, hCn, hRlo]
      have h4 : (3 : ℝ) ^ (n + 4) = 81 * 3 ^ n := by ring
      rw [h4] at h2
      have h5 : 81 * (3 : ℝ) ^ n < c_fc * (3 * R) := by
        calc 81 * (3 : ℝ) ^ n = c_fc * (1 / c_fc * (81 * 3 ^ n)) := by field_simp
          _ < c_fc * (3 * R) := by gcongr
      have h6 : (0 : ℝ) < 3 ^ n := by positivity
      have h7 : 0 < c_fc * R := by positivity
      linarith only [h5, h6, h7]
    obtain ⟨kk, hz'W, hxz'⟩ := hcover R n hR h3n x hxW
    set z' : Vec d := fun i => (3 : ℝ) ^ ((n : ℤ) - s_fc) * (kk i : ℝ) with hz'
    have hgrid : z' ∈ gridPts d (((n + 3 : ℕ) : ℤ) - ((s_fc + 3 : ℕ) : ℤ)) ((3 : ℝ) ^ (K + 2)) := by
      rw [mem_gridPts (by positivity)]
      refine ⟨kk, fun i => ?_, fun i => ?_⟩
      · have e : ((n + 3 : ℕ) : ℤ) - ((s_fc + 3 : ℕ) : ℤ) = (n : ℤ) - s_fc := by push_cast; ring
        rw [e]
      · have h1 := hWb z' hz'W
        have h2 := norm_le_pi_norm z' i
        rw [Real.norm_eq_abs] at h2
        have h3 : (3 : ℝ) ^ K ≤ 3 ^ (K + 2) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_right K 2)
        linarith only [h1, h2, h3, hRhi, hR]
    have hnotsub : ¬ shiftCube z' ((n + 3 : ℕ) : ℤ) ⊆ R • U := by
      intro hsub
      have hne : (R • U)ᶜ.Nonempty := by
        refine ⟨fun _ => R, fun hy => ?_⟩
        have h1 := hWb _ hy
        have i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
        have h2 := norm_le_pi_norm (fun _ : Fin d => R) i0
        rw [Real.norm_eq_abs, abs_of_pos hR] at h2
        linarith only [h1, h2, hR]
      obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hne).1 hxd
      refine hy (hsub ?_)
      rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball]
      have h1 : dist y z' ≤ dist y x + dist x z' := dist_triangle _ _ _
      have h2 : dist x z' ≤ (3 : ℝ) ^ n := by rw [dist_eq_norm]; exact hxz'
      have h3 : (3 : ℝ) ^ (n + 3) = 27 * 3 ^ n := by ring
      have h4 : (0 : ℝ) < 3 ^ n := by positivity
      rw [h3]
      rw [dist_comm y x] at h1
      linarith only [h1, h2, hdy, h4]
    have hB := (key (n + 3) (Nat.le_add_right n 3) le_rfl z' hgrid hz'W).2 hnotsub
    have e2 : (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e2]
    have hz'S : z' ∈ shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U := ⟨rc_mem_shiftCube_self z' _, hz'W⟩
    have hS'o : IsOpen (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U) :=
      (lip_bdry_approx_isOpen_cube z' _).inter hWo
    have hS'0 : volume (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U) ≠ 0 :=
      (hS'o.measure_pos volume ⟨z', hz'S⟩).ne'
    have hS'le : volume (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U) ≤
        ENNReal.ofReal (((3 : ℝ) ^ (n + 3)) ^ d) := by
      rw [← lip_bdry_approx_vol_cube]
      exact measure_mono Set.inter_subset_left
    have hS'T : volume (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS'le
    have hxz : dist x z ≤ (3 : ℝ) ^ n / 2 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      have := (l2b_mem_cell.1 hxc) i
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith only [this.1, this.2]
    have hsub2 : R • U ∩ shiftCube z ((n + 2 : ℕ) : ℤ) ⊆
        shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U := by
      rintro y ⟨hyW, hyQ⟩
      refine ⟨?_, hyW⟩
      rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball] at hyQ ⊢
      have h1 : dist y z' ≤ dist y z + dist z x + dist x z' := by
        calc dist y z' ≤ dist y z + dist z z' := dist_triangle _ _ _
          _ ≤ dist y z + (dist z x + dist x z') := by gcongr; exact dist_triangle _ _ _
          _ = _ := by ring
      have h2 : dist x z' ≤ (3 : ℝ) ^ n := by rw [dist_eq_norm]; exact hxz'
      have h3 : (3 : ℝ) ^ (n + 3) = 27 * 3 ^ n := by ring
      have h5 : (3 : ℝ) ^ (n + 2) = 9 * 3 ^ n := by ring
      have h4 : (0 : ℝ) < 3 ^ n := by positivity
      rw [dist_comm z x] at h1
      rw [h5] at hyQ
      rw [h3]
      linarith only [h1, h2, hxz, hyQ, h4]
    have hLb : lpBar (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U) 2 (fun x => v.toFun x - gt x) ≤
        ENNReal.ofReal (((3 : ℝ) ^ (-((n + 3 : ℕ) : ℝ)))⁻¹) * ENNReal.ofReal (C1 * Cl * Bk) :=
      linf_local_le_of_mul_le (by positivity) (A := 0) (by simpa using hB)
    have hP1 : (((3 : ℝ) ^ (n + 3)) ^ d) ^ (1 / (2 : ℝ)) =
        (3 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) := by
      have e : ((3 : ℝ) ^ (n + 3)) ^ d = ((3 : ℝ) ^ (n + 3)) ^ (d : ℝ) :=
        (Real.rpow_natCast _ _).symm
      rw [e, ← Real.rpow_mul (by positivity),
        show (3 : ℝ) ^ (n + 3) = 3 * 3 ^ (n + 2) by ring, Real.mul_rpow (by norm_num) (by positivity)]
      congr 2 <;> ring
    have hP2 : ((3 : ℝ) ^ (-((n + 3 : ℕ) : ℝ)))⁻¹ = 27 * 3 ^ n := by
      rw [Real.rpow_neg (by norm_num), inv_inv, Real.rpow_natCast]
      ring
    have hq : (3 : ℝ) ^ ((d : ℝ) / 2) ≤ 3 ^ d := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith only [this]
    have hC27 : 27 * (3 : ℝ) ^ ((d : ℝ) / 2) * C1 ≤ C := by
      have h1 : 27 * (3 : ℝ) ^ ((d : ℝ) / 2) * C1 ≤ 27 * 3 ^ d * C1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (zero_le_one.trans hC1b)
      have h2 : (27 : ℝ) * 3 ^ d * C1 = 3 ^ (d + 3) * C1 := by ring
      have h3 : 0 < 1 / c_fc := by positivity
      simp only [hCdef]
      linarith only [h1, h2, h3]
    calc eLpNorm (fun x => v.toFun x - gt x) 2
          (volume.restrict (R • U ∩ shiftCube z ((n + 2 : ℕ) : ℤ)))
        ≤ eLpNorm (fun x => v.toFun x - gt x) 2
            (volume.restrict (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U)) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hsub2 le_rfl)
      _ = (volume (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U)) ^ (1 / (2 : ℝ)) *
            lpBar (shiftCube z' ((n + 3 : ℕ) : ℤ) ∩ R • U) 2 (fun x => v.toFun x - gt x) :=
          linf_local_eLp_eq hS'0 hS'T _
      _ ≤ ENNReal.ofReal ((((3 : ℝ) ^ (n + 3)) ^ d) ^ (1 / (2 : ℝ))) *
            (ENNReal.ofReal (((3 : ℝ) ^ (-((n + 3 : ℕ) : ℝ)))⁻¹) *
              ENNReal.ofReal (C1 * Cl * Bk)) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          gcongr
      _ = ENNReal.ofReal ((((3 : ℝ) ^ (n + 3)) ^ d) ^ (1 / (2 : ℝ)) *
            (((3 : ℝ) ^ (-((n + 3 : ℕ) : ℝ)))⁻¹ * (C1 * Cl * Bk))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hP1, hP2, hRb']
          have hP : 0 ≤ ((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) :=
            Real.rpow_nonneg (pow_nonneg (by norm_num) _) _
          have hT : 0 ≤ (3 : ℝ) ^ n := pow_nonneg (by norm_num) _
          have hClBk : 0 ≤ Cl * Bk := mul_nonneg hCl0 hBk0
          calc (3 : ℝ) ^ ((d : ℝ) / 2) * ((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) *
                (27 * 3 ^ n * (C1 * Cl * Bk))
              = ((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) * (3 ^ n *
                  ((27 * (3 : ℝ) ^ ((d : ℝ) / 2) * C1) * (Cl * Bk))) := by ring
            _ ≤ ((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) * (3 ^ n * (C * (Cl * Bk))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hC27 hClBk) hT) hP
            _ = _ := by ring

end SuperdiffusionCLT.Section7
