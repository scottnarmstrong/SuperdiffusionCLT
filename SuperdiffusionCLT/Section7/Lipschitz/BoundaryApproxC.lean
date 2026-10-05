/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryApproxB

/-!
# The harmonic approximation near the boundary

`lip_bdry_approx` (the display of the boundary approximation in the proof of the large-scale
Lipschitz estimate): the mollified datum `gt` and the solution `ub` of `-s Δ ub = f` in `V` with
the boundary values of `u - w`, where `w` is the auxiliary `a`-harmonic function with the boundary
values of the cut-off difference `ψ`.  The estimate of `u - ub` in `L̲²(V)` uses the `L²` block on
`V`, the boundary Caccioppoli block at the scale `k + 2` for `w` and at the scale `k + 1` for `u`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **The harmonic approximation near the boundary**: the mollified
datum `gt`, and the solution `ub` of `-s Δ ub = f` in `V` with the boundary values of
`u_k = u - w`, where `w` is the auxiliary `a`-harmonic function of `lip_aux`.  The pinned flatness
of `u` at the scale `k + 1` and the slope `p` bound the gradient of `u` through the boundary
Caccioppoli block. -/
theorem lip_bdry_approx (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cin M₁ rU : ℝ) (hCin : 1 ≤ Cin)
    (hrU : 0 < rU) (ag A : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : CoeffField d) (W V : Set (Vec d)) (rW M₂W DW nu s δ E lam Lam : ℝ)
        (z x₀ : Vec d) (k : ℕ),
        0 < nu → 1 ≤ s → 0 ≤ δ → δ ≤ 1 → 0 ≤ E → 1 ≤ k →
        ((k : ℝ) ^ A)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu → ((k : ℝ) ^ A)⁻¹ * s ≤ 1 →
        IsUniformC11Domain W rW M₁ M₂W DW → rU * (3 : ℝ) ^ k ≤ rW →
        z ∈ W → ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 2 →
        IsOpen V → Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V →
        V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ W →
        IsEllipticFieldOn lam Lam (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) a → 0 < lam →
        LipL2Block a nu s δ Cin A k V →
        LipCaccBdryS a nu s Cin E W z (k + 1) → LipCaccBdryS a nu s Cin E W z (k + 2) →
        ∀ (f g : Vec d → ℝ) (F G1 G2 : ℝ) (u : H1Function (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W)),
          ContDiff ℝ 2 g → 0 ≤ F → 0 ≤ G1 → 0 ≤ G2 →
          (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
          (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
          (∀ᵐ x ∂volume.restrict (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W), |f x| ≤ F) →
          IsWeakSolutionOn a (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) u f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W)
            (shiftCube z ((k + 2 : ℕ) : ℤ)) (fun x => u.toFun x - g x) →
          ∃ (gt : Vec d → ℝ) (ub : H1Function V), ContDiff ℝ (⊤ : ℕ∞) gt ∧
            (∀ x, ‖fderiv ℝ gt x‖ ≤ C * G1) ∧
            (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ C * ((3 : ℝ) ^ k)⁻¹ * G1) ∧
            (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), |gt x - g x| ≤ C * (3 : ℝ) ^ k * G1) ∧
            IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0) ∧
            LocalizedZeroTraceFunctionOn V (Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2))
              (fun x => ub.toFun x - gt x) ∧
            ∀ p : Vec d,
              ((3 : ℝ)⁻¹) ^ k * lipL2 V (fun x => u.toFun x - ub.toFun x) ≤
                C * (δ * (lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀)
                      u.toFun p + ‖p‖) +
                  G1 + s⁻¹ * (3 : ℝ) ^ k * F + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) := by
  have _hd2 : 2 ≤ d := hd
  obtain ⟨Cd, hCd, hdat⟩ := lip_datum d
  obtain ⟨κ, hκ, hratio⟩ := lip_bdry_approx_volume_ratio d M₁ rU hrU ag
  have hCin0 : 0 < Cin := by linarith only [hCin]
  have hsκ : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  have hM0 : 0 ≤ 2 * Cin ^ 2 * Real.sqrt κ * ((d : ℝ) + 14 + 11 * Cd) := by positivity
  refine ⟨Cd + Cin + 2 * Cin ^ 2 * Real.sqrt κ * ((d : ℝ) + 14 + 11 * Cd),
    by linarith only [hCd, hCin, hM0], ?_⟩
  intro a W V rW M₂W DW nu s δ E lam Lam z x₀ k hnu hs hδ0 hδ1 hE hk hP1 hP2 hW hrW hzW hx₀ hVo
    hBV hVk hell hlam hblk hc1 hc2 f g F G1 G2 u hg hF0 hG1 hG2 hDg hD2g hFae hsol hz
  have hs0 : 0 < s := by linarith only [hs]
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hVQ0 : V ⊆ shiftCube z (k : ℤ) := by
    intro x hx
    rw [lip_bdry_approx_shiftCube_eq_ball]
    exact (hVk hx).1
  have hVW : V ⊆ W := fun x hx => (hVk hx).2
  obtain ⟨hV0, hvolκ⟩ := hratio W V rW M₂W DW z k hW hrW hzW hBV hVQ0
  have hQ01 : shiftCube z (k : ℤ) ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (by omega)
  have hQ12 : shiftCube z ((k + 1 : ℕ) : ℤ) ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (by omega)
  have hVD0 : V ⊆ shiftCube z (k : ℤ) ∩ W := fun x hx => ⟨hVQ0 hx, hVW hx⟩
  have hD01 : shiftCube z (k : ℤ) ∩ W ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ01
  have hD12 : shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ12
  have hVD1 : V ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W := hVD0.trans hD01
  have hVD2 : V ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W := hVD1.trans hD12
  have hD2o : IsOpen (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW.1
  have hVt : volume V ≠ ⊤ :=
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z k) (measure_mono hVQ0)
  have hVb : IsBoundedDomain V := lip_bdry_approx_isBoundedDomain hVQ0
  obtain ⟨hD0v, hD0t⟩ := lip_bdry_approx_vol_ne_zero_ne_top hV0 hVD0 (Set.inter_subset_left)
  obtain ⟨hD1v, hD1t⟩ := lip_bdry_approx_vol_ne_zero_ne_top hV0 hVD1 (Set.inter_subset_left)
  obtain ⟨hD2v, hD2t⟩ := lip_bdry_approx_vol_ne_zero_ne_top hV0 hVD2 (Set.inter_subset_left)
  -- the datum and the auxiliary function
  obtain ⟨gt, ψ, hgt, hψ2, hψc, hψsup, hψeq, hψ0, hψ1, hψ2', hgt1, hgt2, hgtg⟩ :=
    hdat z k g G1 G2 hg hG1 hG2 hDg hD2g
  obtain ⟨w, hwsol, hwh10, hwb⟩ := lip_aux d a (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) hD2o
    (lip_bdry_approx_isBoundedDomain Set.inter_subset_left) hell ψ (Cd * (3 : ℝ) ^ k * G1)
    hψ2 hψ0
  have hMψ0 : 0 ≤ Cd * (3 : ℝ) ^ k * G1 := by positivity
  -- the solution of the Laplace problem on `V`
  obtain ⟨fV, ub, hfVm, hfVb, hukVsol, hubsolV, hubsolf, hubm⟩ :=
    lip_bdry_approx_ub_data hD2o hVo hVD2 hVt hVb hs0 hF0 hell hFae hsol hwsol
  -- the localized zero trace
  have hr3 : (3 : ℝ) ^ k / 3 ^ ag / 2 ≤ (3 : ℝ) ^ (k + 1) / 2 := by
    have h1 : (3 : ℝ) ^ k / 3 ^ ag ≤ (3 : ℝ) ^ k :=
      div_le_self ht.le (one_le_pow₀ (by norm_num))
    have h2 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [h1, h2]
  have hB'Q1 : Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) := by
    rw [lip_bdry_approx_shiftCube_eq_ball]
    exact Metric.ball_subset_ball hr3
  have hB'Q2 : Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) :=
    hB'Q1.trans hQ12
  have hagree : (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) ∩ Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) =
      V ∩ Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) := by
    ext x
    constructor
    · rintro ⟨⟨_, hw'⟩, hb⟩
      exact ⟨hBV ⟨hb, hw'⟩, hb⟩
    · rintro ⟨hx, hb⟩
      exact ⟨hVD2 hx, hb⟩
  have htrace := lip_bdry_approx_trace hVo Metric.isOpen_ball hVD2 hB'Q2 hagree hz hwh10 hubm
    (fun x hx => hψeq x (hB'Q1 hx))
  -- the auxiliary function in the boundary Caccioppoli block at the scale `k + 2`
  have e2 : (((k + 2 : ℕ) : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hqk2 : (((k + 2 : ℕ) : ℝ)) ^ (-E) ≤ (k : ℝ) ^ (-E) :=
    Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith only) (by linarith only [hE])
  have hq02 : 0 ≤ (((k + 2 : ℕ) : ℝ)) ^ (-E) := by positivity
  have hkE1 : (k : ℝ) ^ (-E) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith only [hE])
  have hwQ : lpBar (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) 2 (fun x => w.toFun x - ψ x) ≤
      ENNReal.ofReal (2 * (Cd * (3 : ℝ) ^ k * G1)) :=
    lip_int_harm_of_l2_lpBar_le_of_ae_bound hD2v hD2t 2
      (w.memL2.aestronglyMeasurable.sub hψ2.continuous.aestronglyMeasurable)
      (by
        filter_upwards [hwb] with x hx
        have := hψ0 x
        calc |w.toFun x - ψ x| ≤ |w.toFun x| + |ψ x| := abs_sub _ _
          _ ≤ 2 * (Cd * (3 : ℝ) ^ k * G1) := by linarith only [hx, this])
  have hwF : lpBar (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) 2 (fun _ : Vec d => (0 : ℝ)) ≤
      ENNReal.ofReal 0 :=
    lip_int_harm_of_l2_lpBar_le_of_ae_bound hD2v hD2t 2 aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun x => by simp)
  have hw1 : ∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W, ‖fderiv ℝ ψ x‖ ≤ Cd * G1 :=
    fun x _ => hψ1 x
  have hw2 : ∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W,
      ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ Cd * (((3 : ℝ) ^ k)⁻¹ * G1 + G2) :=
    fun x _ => hψ2' x
  have hwcacc := lip_bdry_approx_cacc hc2 hnu hs0 hCin0.le (by rw [e2]; exact hD1v)
    (by rw [e2]; exact hD1t) (by rw [e2]; exact hD12) (fun _ => (0 : ℝ)) ψ w hψ2 hwsol
    (lip_bdry_approx_loc_of_h10 hwh10) hwQ hwF hw1 hw2 (by positivity) le_rfl (by positivity)
    (by positivity)
  rw [e2] at hwcacc
  have hSw : (Real.sqrt s)⁻¹ * Real.sqrt nu *
      lipGradL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) w.grad ≤
      11 * Cin * Cd * (G1 + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) :=
    lip_bdry_approx_sgrad_le hnu hs0 ENNReal.toReal_nonneg (by positivity)
      (hwcacc.trans (lip_bdry_approx_w_arith k hCin hCd hs hG1 hG2 hq02 hqk2 hkE1))
  -- the bound of `w` in `L̲²(V)`
  have hT1 : ((3 : ℝ)⁻¹) ^ k * lipL2 V w.toFun ≤ Cd * G1 := by
    have h1 := lipL2_le_of_ae_abs_le hMψ0 hV0 hVt (f := w.toFun)
      (ae_restrict_of_ae_restrict_of_subset hVD2 hwb)
    have h2 : ((3 : ℝ)⁻¹) ^ k * (Cd * (3 : ℝ) ^ k * G1) = Cd * G1 := by
      have : ((3 : ℝ)⁻¹) ^ k * (3 : ℝ) ^ k = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
      calc ((3 : ℝ)⁻¹) ^ k * (Cd * (3 : ℝ) ^ k * G1)
          = (((3 : ℝ)⁻¹) ^ k * (3 : ℝ) ^ k) * (Cd * G1) := by ring
        _ = Cd * G1 := by rw [this, one_mul]
    calc ((3 : ℝ)⁻¹) ^ k * lipL2 V w.toFun ≤ ((3 : ℝ)⁻¹) ^ k * (Cd * (3 : ℝ) ^ k * G1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cd * G1 := h2
  have hCdC : Cd ≤ Cd + Cin + 2 * Cin ^ 2 * Real.sqrt κ * ((d : ℝ) + 14 + 11 * Cd) := by
    linarith only [hCin0, hM0]
  refine ⟨gt, ub, hgt, fun x => (hgt1 x).trans (mul_le_mul_of_nonneg_right hCdC hG1),
    fun x => (hgt2 x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCdC (by positivity)) hG1),
    fun x hx => (hgtg x hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCdC ht.le) hG1),
    hubsolf, htrace, ?_⟩
  intro p
  have hSu := lip_bdry_approx_su hnu hs hCin hE hk hW.1 hx₀ hell hc1 hD0v f g F G1 G2 u hg hF0
    hG1 hG2 hDg hD2g hFae hsol hz p
  -- the `L²` block on `V`
  set ukV : H1Function V := u.restrict hVo hVD2 - w.restrict hVo hVD2 with hukV
  have hukVf : ∀ x, ukV.toFun x = u.toFun x - w.toFun x := fun x => by
    simp [hukV, H1Function.sub_toFun, H1Function.restrict]
  have hukVg : ∀ x, ukV.grad x = u.grad x - w.grad x := fun x => by
    simp [hukV, H1Function.sub_grad, H1Function.restrict]
  have hzero : MemH10 V (fun x => ukV.toFun x - ukV.toFun x) := by
    have e : (fun x => ukV.toFun x - ukV.toFun x) = 0 := funext fun x => sub_self _
    rw [e]
    exact memH10_zero
  have hBlock := hblk fV ukV ukV ub hukVsol hubsolV hzero hubm
  have hmemUk : MemLp (fun x => eucNorm (ukV.grad x)) 2 (volume.restrict V) :=
    p13_memLp_euc ukV.grad_memVectorL2
  have hGlt : lpBar V 2 (fun x => eucNorm (ukV.grad x)) ≠ ⊤ :=
    lip_int_harm_of_l2_lpBar_lt_top hV0 hVt hmemUk
  have hFv := lip_int_harm_of_l2_lpBar_le_of_ae_bound hV0 hVt
    (ENNReal.ofReal (sobStar d)).conjExponent hfVm hfVb
  have hBlock' : ENNReal.ofReal (((3 : ℝ)⁻¹) ^ k) *
      lpBar V 2 (fun x => ukV.toFun x - ub.toFun x) ≤
      ENNReal.ofReal (Cin * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu) *
        lpBar V 2 (fun x => eucNorm (ukV.grad x)) +
      ENNReal.ofReal (Cin * ((k : ℝ) ^ A)⁻¹) * (lpBar V 2 (fun x => eucNorm (ukV.grad x)) +
        ENNReal.ofReal ((3 : ℝ) ^ k) * ENNReal.ofReal F) :=
    hBlock.trans (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl
      (mul_le_mul' le_rfl hFv))))
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hq : 0 < Real.sqrt nu := Real.sqrt_pos.2 hnu
  have hPA : 0 ≤ ((k : ℝ) ^ A)⁻¹ := by positivity
  have hreal := lip_int_harm_of_l2_enn_real (by positivity) (by positivity) (by positivity)
    (by positivity) hF0 hGlt hBlock'
  set Gv : ℝ := lipGradL2 V ukV.grad with hGvdef
  set Tk : ℝ := lipL2 V (fun x => ukV.toFun x - ub.toFun x) with hTkdef
  have hreal' : ((3 : ℝ)⁻¹) ^ k * Tk ≤ Cin * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu * Gv +
      Cin * ((k : ℝ) ^ A)⁻¹ * (Gv + (3 : ℝ) ^ k * F) := hreal
  -- the two bounds of the exponent factor
  have hPA1 : ((k : ℝ) ^ A)⁻¹ ≤ δ * Real.sqrt nu * (Real.sqrt s)⁻¹ := by
    calc ((k : ℝ) ^ A)⁻¹ = ((k : ℝ) ^ A)⁻¹ * Real.sqrt s * (Real.sqrt s)⁻¹ := by
          field_simp
      _ ≤ δ * Real.sqrt nu * (Real.sqrt s)⁻¹ :=
          mul_le_mul_of_nonneg_right hP1 (inv_nonneg.2 hr.le)
  have hPA2 : ((k : ℝ) ^ A)⁻¹ ≤ s⁻¹ := by
    calc ((k : ℝ) ^ A)⁻¹ = ((k : ℝ) ^ A)⁻¹ * s * s⁻¹ := by field_simp
      _ ≤ 1 * s⁻¹ := mul_le_mul_of_nonneg_right hP2 (inv_nonneg.2 hs0.le)
      _ = s⁻¹ := one_mul _
  have hGv0 : 0 ≤ Gv := ENNReal.toReal_nonneg
  have hTk : ((3 : ℝ)⁻¹) ^ k * Tk ≤
      2 * Cin * δ * ((Real.sqrt s)⁻¹ * Real.sqrt nu * Gv) + Cin * (s⁻¹ * (3 : ℝ) ^ k * F) := by
    have a1 : ((k : ℝ) ^ A)⁻¹ * (Cin * Gv) ≤ (δ * Real.sqrt nu * (Real.sqrt s)⁻¹) * (Cin * Gv) :=
      mul_le_mul_of_nonneg_right hPA1 (by positivity)
    have a2 : ((k : ℝ) ^ A)⁻¹ * (Cin * ((3 : ℝ) ^ k * F)) ≤ s⁻¹ * (Cin * ((3 : ℝ) ^ k * F)) :=
      mul_le_mul_of_nonneg_right hPA2 (by positivity)
    linarith only [hreal', a1, a2]
  -- the gradient of `u_k` on `V` against the gradients of `u` and `w`
  have hmu : MemLp (fun x => eucNorm (u.grad x)) 2 (volume.restrict V) :=
    p13_memLp_euc (u.grad_memVectorL2.mono_measure (Measure.restrict_mono hVD2 le_rfl))
  have hmw : MemLp (fun x => eucNorm (w.grad x)) 2 (volume.restrict V) :=
    p13_memLp_euc (w.grad_memVectorL2.mono_measure (Measure.restrict_mono hVD2 le_rfl))
  have hG1' : Gv ≤ lipL2 V (fun x => eucNorm (u.grad x)) + lipL2 V (fun x => eucNorm (w.grad x)) := by
    refine (lip_bdry_approx_lipL2_mono hV0 hVt hmemUk.aestronglyMeasurable (hmu.add hmw)
      (Filter.Eventually.of_forall fun x => ?_)).trans
      (lip_int_harm_of_l2_lipL2_add_le hV0 hVt hmu hmw)
    rw [abs_of_nonneg (by unfold eucNorm; positivity), hukVg x, sub_eq_add_neg]
    refine (r1_eucNorm_add_le _ _).trans (le_of_eq ?_)
    rw [r1_eucNorm_neg]
    rfl
  have hvolκ' : ∀ S : Set (Vec d), S ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) →
      (volume S).toReal ≤ κ * (volume V).toReal := fun S hS =>
    (ENNReal.toReal_mono (lip_bdry_approx_vol_cube_ne_top z (k + 2)) (measure_mono hS)).trans
      hvolκ
  have hmuD0 : MemLp (fun x => eucNorm (u.grad x)) 2
      (volume.restrict (shiftCube z (k : ℤ) ∩ W)) :=
    p13_memLp_euc (u.grad_memVectorL2.mono_measure
      (Measure.restrict_mono (hD01.trans hD12) le_rfl))
  have hmwD1 : MemLp (fun x => eucNorm (w.grad x)) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    p13_memLp_euc (w.grad_memVectorL2.mono_measure (Measure.restrict_mono hD12 le_rfl))
  have hG2' : lipL2 V (fun x => eucNorm (u.grad x)) ≤
      Real.sqrt κ * lipGradL2 (shiftCube z (k : ℤ) ∩ W) u.grad :=
    lip_int_harm_of_l2_lipL2_mono_set hVD0 hV0 hD0t
      (hvolκ' _ (Set.inter_subset_left.trans (hQ01.trans hQ12))) hmuD0
  have hG3' : lipL2 V (fun x => eucNorm (w.grad x)) ≤
      Real.sqrt κ * lipGradL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) w.grad :=
    lip_int_harm_of_l2_lipL2_mono_set hVD1 hV0 hD1t
      (hvolκ' _ (Set.inter_subset_left.trans hQ12)) hmwD1
  have hSg : (Real.sqrt s)⁻¹ * Real.sqrt nu * Gv ≤ Real.sqrt κ *
      ((Real.sqrt s)⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (k : ℤ) ∩ W) u.grad +
        (Real.sqrt s)⁻¹ * Real.sqrt nu *
          lipGradL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) w.grad) := by
    have h := mul_le_mul_of_nonneg_left (hG1'.trans (add_le_add hG2' hG3'))
      (by positivity : 0 ≤ (Real.sqrt s)⁻¹ * Real.sqrt nu)
    calc (Real.sqrt s)⁻¹ * Real.sqrt nu * Gv ≤ _ := h
      _ = _ := by ring
  -- `u - ub = w + (u_k - ub)`
  have hwmem : MemLp w.toFun 2 (volume.restrict V) :=
    w.memL2.mono_measure (Measure.restrict_mono hVD2 le_rfl)
  have hTot : lipL2 V (fun x => u.toFun x - ub.toFun x) ≤ lipL2 V w.toFun + Tk := by
    have e : (fun x => u.toFun x - ub.toFun x) =
        fun x => w.toFun x + (ukV.toFun x - ub.toFun x) := funext fun x => by
      rw [hukVf]; ring
    rw [e]
    exact lipL2_add_le hV0 hVt hwmem (ukV.memL2.sub ub.memL2)
  have hTot' : ((3 : ℝ)⁻¹) ^ k * lipL2 V (fun x => u.toFun x - ub.toFun x) ≤
      ((3 : ℝ)⁻¹) ^ k * lipL2 V w.toFun + ((3 : ℝ)⁻¹) ^ k * Tk := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hTot (by positivity)
  have hΦ0 : 0 ≤ lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p := by
    unfold lipPin lipL2
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hfin := lip_bdry_approx_final_arith (Cin := Cin) (Cd := Cd) (κs := Real.sqrt κ)
    (d' := (d : ℝ)) (δ := δ)
    (Φ := lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p) (P := ‖p‖)
    (G1 := G1) (Gk := (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) (Fs := s⁻¹ * (3 : ℝ) ^ k * F)
    (T1 := ((3 : ℝ)⁻¹) ^ k * lipL2 V w.toFun) (Tk := ((3 : ℝ)⁻¹) ^ k * Tk)
    (Sg := (Real.sqrt s)⁻¹ * Real.sqrt nu * Gv)
    (Su := (Real.sqrt s)⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (k : ℤ) ∩ W) u.grad)
    (Sw := (Real.sqrt s)⁻¹ * Real.sqrt nu *
      lipGradL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) w.grad)
    hCin hCd hsκ (by positivity) hδ0 hδ1 hΦ0 (norm_nonneg _) hG1 (by positivity) (by positivity)
    hT1 hTk hSg hSu hSw
  exact hTot'.trans hfin

/-- Witness: the numerical and geometric hypotheses of `lip_bdry_approx` hold together on the unit
ball, with the exponent `A = 1`, the scale `k = 1`, and `V` the trace of a small ball. -/
example [NeZero d] : ∃ (M₁ rU : ℝ) (W V : Set (Vec d)) (rW M₂W DW nu s δ E : ℝ) (z x₀ : Vec d)
    (k A ag : ℕ), 0 < rU ∧ 0 < nu ∧ 1 ≤ s ∧ 0 ≤ δ ∧ δ ≤ 1 ∧ 0 ≤ E ∧ 1 ≤ k ∧
      ((k : ℝ) ^ A)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu ∧ ((k : ℝ) ^ A)⁻¹ * s ≤ 1 ∧
      IsUniformC11Domain W rW M₁ M₂W DW ∧ rU * (3 : ℝ) ^ k ≤ rW ∧ z ∈ W ∧
      ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 2 ∧ IsOpen V ∧
      Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V ∧
      V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ W := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_euclidBall (d := d)
  have hr : 0 < r := h.2.1
  refine ⟨M₁, r / 3, Section6.euclidBall (d := d) 1,
    Metric.ball (0 : Vec d) ((3 : ℝ) ^ 1 / 3 ^ 1 / 2) ∩ Section6.euclidBall (d := d) 1, r, M₂, D,
    1, 1, 1, 0, 0, 0, 1, 1, 1, by positivity, one_pos, le_rfl, zero_le_one, le_rfl, le_rfl, le_rfl,
    ?_, ?_, h, ?_, Section6.zero_mem_euclidBall one_pos, ?_, ?_, Set.Subset.rfl, ?_⟩
  · simp
  · simp
  · linarith only [hr]
  · norm_num
  · exact Metric.isOpen_ball.inter h.1
  · refine Set.inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    norm_num

end SuperdiffusionCLT.Section7
