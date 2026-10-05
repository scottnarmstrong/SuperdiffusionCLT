/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarm
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliC
public import SuperdiffusionCLT.Section7.Prereq.FieldBridge
public import SuperdiffusionCLT.Section6.Engine.Solutions

/-!
# The interior harmonic approximation from the `L²` block: the deterministic core

For an `H¹` solution `u` of `-∇·a∇u = f` on `□_k` with `|f| ≤ F` and `f` measurable: the
Poisson solution `ub` of `-sΔ ub = f` on `V` with the trace of `u`, the Laplace solution `h` with the
same trace, the `L²` block for `u - ub` on `V` and the interior Caccioppoli block give
`‖u - h‖_{L̲²(□_{k-3})} ≤ C (δ 3^k 3^{-k}‖u - (u)‖_{L̲²(□_k)} + s⁻¹ 9^k F)`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_int_harm_of_l2_enn_real {e a b c F : ℝ} {X G : ℝ≥0∞} (he : 0 ≤ e) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hF : 0 ≤ F) (hG : G ≠ ⊤)
    (h : ENNReal.ofReal e * X ≤ ENNReal.ofReal a * G +
      ENNReal.ofReal b * (G + ENNReal.ofReal c * ENNReal.ofReal F)) :
    e * X.toReal ≤ a * G.toReal + b * (G.toReal + c * F) := by
  have hfin : ENNReal.ofReal a * G + ENNReal.ofReal b * (G + ENNReal.ofReal c * ENNReal.ofReal F)
      ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hG,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)⟩
  have := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hG,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal he,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
    ENNReal.toReal_add hG (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hF] at this
  exact this

theorem lip_int_harm_of_l2_scale_loss {k : ℕ} (hk : 3 ≤ k) (A : ℕ) :
    ((((k - 1 : ℕ) : ℝ)) ^ A)⁻¹ ≤ 2 ^ A * (((k : ℝ)) ^ A)⁻¹ := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : (k : ℝ) / 2 ≤ ((k - 1 : ℕ) : ℝ) := by
    rw [hc]; linarith only [hk']
  have h2 : ((k : ℝ) / 2) ^ A ≤ (((k - 1 : ℕ) : ℝ)) ^ A :=
    pow_le_pow_left₀ (by positivity) h1 A
  have h3 : (0 : ℝ) < ((k : ℝ) / 2) ^ A := by positivity
  calc ((((k - 1 : ℕ) : ℝ)) ^ A)⁻¹ ≤ (((k : ℝ) / 2) ^ A)⁻¹ := inv_anti₀ h3 h2
    _ = 2 ^ A * (((k : ℝ)) ^ A)⁻¹ := by
        rw [div_pow, inv_div, div_eq_mul_inv]

/-- **The deterministic core**, for a measurable right-hand side. -/
theorem lip_int_harm_of_l2_core (d : ℕ) [NeZero d] (Cin : ℝ) (hCin : 1 ≤ Cin) (A : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : CoeffField d) (nu s δ : ℝ) (k : ℕ) (V : Set (Vec d)),
        0 < nu → 0 < s → 0 ≤ δ → 3 ≤ k →
        ((k : ℝ) ^ A)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu → ((k : ℝ) ^ A)⁻¹ * s ≤ 1 →
        IsOpen V → Section6.engCube d (k - 2) ⊆ V → V ⊆ Section6.engCube d (k - 1) →
        LipL2Block a nu s δ Cin A (k - 1) V → LipCaccInt a nu s Cin 1 k →
        ∀ (f : Vec d → ℝ) (F : ℝ) (u : H1Function (Section6.engCube d k)),
          IsWeakSolutionOn a (Section6.engCube d k) u f (fun _ => 0) → 0 ≤ F →
          (∀ᵐ x ∂volume.restrict (Section6.engCube d k), |f x| ≤ F) →
          AEStronglyMeasurable f (volume.restrict (Section6.engCube d k)) →
          ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
            Section6.IsSolOn (fun _ => (1 : Mat d)) (Section6.engCube d (k - 3)) w gw ∧
              Section6.cubeL2 (k - 3) (fun x => u.toFun x - w x) ≤
                C * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun +
                  s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) := by
  obtain ⟨c, hc, hEn⟩ := lip_int_harm_of_l2_energy (d := d)
  set N1 : ℝ := Real.sqrt ((3 : ℝ) ^ d) with hN1
  set N3 : ℝ := Real.sqrt (((3 : ℝ) ^ d) ^ 2) with hN3
  set N27 : ℝ := Real.sqrt (((3 : ℝ) ^ d) ^ 3) with hN27
  set K : ℝ := N1 * (Cin ^ 2 * (1 + 2 ^ A)) + Cin * 2 ^ A + c ^ 2 with hK
  have hCin0 : 0 < Cin := by linarith only [hCin]
  have hN1' : 0 ≤ N1 := Real.sqrt_nonneg _
  have hN3' : 0 ≤ N3 := Real.sqrt_nonneg _
  have hN27' : 0 ≤ N27 := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨1 + N3 * K + N27, by
    have : 0 ≤ N3 * K := mul_nonneg hN3' hK0
    linarith only [this, hN27'], ?_⟩
  intro a nu s δ k V hnu hs hδ hk H1 H2 hVo hV2 hV1 hblk hcacc f F u hu hF hfb hfm
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hδ1 : 1 ≤ δ
  · obtain ⟨w, gw, hw, hb⟩ := lip_int_harm_of_l2_const hk u
    refine ⟨w, gw, hw, hb.trans ?_⟩
    have h0 : 0 ≤ (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun :=
      mul_nonneg ht.le (Section6.cubeFlat_nonneg _ _)
    have h1 : 0 ≤ s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F := by positivity
    have h2 : (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun ≤
        δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun := by
      have := mul_le_mul_of_nonneg_right hδ1 h0
      linarith only [this]
    have h3 : 0 ≤ N3 * K := mul_nonneg hN3' hK0
    calc N27 * ((3 : ℝ) ^ k * Section6.cubeFlat k u.toFun)
        ≤ (1 + N3 * K + N27) * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) := by
          have := mul_le_mul_of_nonneg_left h2 hN27'
          have h4 : 0 ≤ (1 + N3 * K) * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) :=
            mul_nonneg (by linarith only [h3]) (h0.trans h2)
          calc _ ≤ N27 * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) := this
            _ ≤ _ := by linarith only [h4]
      _ ≤ _ := by
          have : 0 ≤ (1 + N3 * K + N27) * (s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) :=
            mul_nonneg (by linarith only [h3, hN27']) h1
          linarith only [this]
  · have hδ' : δ ≤ 1 := (not_le.1 hδ1).le

    have hk1 : k - 3 ≤ k - 1 := by omega
    have hQ1Q : Section6.engCube d (k - 1) ⊆ Section6.engCube d k :=
      Section6.eh_engCube_mono (Nat.sub_le k 1)
    have hVQ : V ⊆ Section6.engCube d k := hV1.trans hQ1Q
    have hQ3Q2 : Section6.engCube d (k - 3) ⊆ Section6.engCube d (k - 2) :=
      Section6.eh_engCube_mono (by omega)
    have hQ3V : Section6.engCube d (k - 3) ⊆ V := hQ3Q2.trans hV2
    have hQ2Q1 : Section6.engCube d (k - 2) ⊆ Section6.engCube d (k - 1) :=
      Section6.eh_engCube_mono (by omega)
    have hVt : volume V ≠ ⊤ := ne_top_of_le_ne_top (Section6.eh_volume_engCube_ne_top (k - 1))
      (measure_mono hV1)
    have hV0 : volume V ≠ 0 := fun h0 => lip_int_harm_of_l2_vol_ne_zero (k - 2)
      (le_antisymm (h0 ▸ measure_mono hV2) bot_le)
    have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVt.lt_top⟩
    have hbd : IsBoundedDomain V := lip_int_harm_of_l2_isBoundedDomain hV1
    set uV : H1Function V := u.restrict hVo hVQ with huVdef
    have huV : IsWeakSolutionOn a V uV f (fun _ => 0) := ca1_weak_restrict hVo hVQ hu
    have hfmV : AEStronglyMeasurable f (volume.restrict V) :=
      hfm.mono_measure (Measure.restrict_mono hVQ le_rfl)
    have hfbV : ∀ᵐ x ∂volume.restrict V, |f x| ≤ F := ae_restrict_of_ae_restrict_of_subset hVQ hfb
    have hf2 : MemLp f 2 (volume.restrict V) :=
      MemLp.of_bound hfmV F (hfbV.mono fun x hx => by rwa [Real.norm_eq_abs])
    obtain ⟨ub, hub, hubm⟩ := w0_dirichlet_exists hVo hbd
      (rc_isEllipticFieldOn_smul_one hs hVo.measurableSet) hf2 uV
    obtain ⟨h, hh, hhm⟩ := w0_dirichlet_exists hVo hbd
      (lip_int_harm_of_l2_ell_one hVo.measurableSet) (f := fun _ => (0 : ℝ)) (memLp_const 0) uV
    have hubh : MemH10 V (fun x => ub.toFun x - h.toFun x) := by
      have e : (fun x => ub.toFun x - h.toFun x) =
          fun x => (ub.toFun x - uV.toFun x) - (h.toFun x - uV.toFun x) := by
        funext x; ring
      rw [e]
      exact memH10_sub hubm hhm
    have hzero : MemH10 V (fun x => uV.toFun x - uV.toFun x) := by
      have e : (fun x => uV.toFun x - uV.toFun x) = 0 := funext fun x => sub_self _
      rw [e]
      exact memH10_zero
    have hBlock := hblk f uV uV ub huV hub hzero hubm
    have hEnergy := hEn hVo hV1 hV0 hs f hF hfmV hfbV ub h hub hh hubh

    -- real quantities
    have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have hq : 0 < Real.sqrt nu := Real.sqrt_pos.2 hnu
    have hrs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    set P : ℝ := ((k : ℝ) ^ A)⁻¹ with hPdef
    set P' : ℝ := (((k - 1 : ℕ) : ℝ) ^ A)⁻¹ with hP'def
    have hP0 : 0 < P := by positivity
    have hP'0 : 0 ≤ P' := by positivity
    have hP'le : P' ≤ 2 ^ A * P := lip_int_harm_of_l2_scale_loss hk A
    have hH2 : P * Real.sqrt s ^ 2 ≤ 1 := by rw [hrs]; exact H2
    have hmemG : MemLp (fun x => eucNorm (uV.grad x)) 2 (volume.restrict V) :=
      p13_memLp_euc uV.grad_memVectorL2
    have hGlt : lpBar V 2 (fun x => eucNorm (uV.grad x)) ≠ ⊤ :=
      lip_int_harm_of_l2_lpBar_lt_top hV0 hVt hmemG
    have hFv := lip_int_harm_of_l2_lpBar_le_of_ae_bound hV0 hVt
      (ENNReal.ofReal (sobStar d)).conjExponent hfmV hfbV
    have hBlock' : ENNReal.ofReal (((3 : ℝ)⁻¹) ^ (k - 1)) *
        lpBar V 2 (fun x => uV.toFun x - ub.toFun x) ≤
        ENNReal.ofReal (Cin * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu) *
          lpBar V 2 (fun x => eucNorm (uV.grad x)) +
        ENNReal.ofReal (Cin * P') * (lpBar V 2 (fun x => eucNorm (uV.grad x)) +
          ENNReal.ofReal ((3 : ℝ) ^ (k - 1)) * ENNReal.ofReal F) :=
      hBlock.trans (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl
        (mul_le_mul' le_rfl hFv))))
    have hreal := lip_int_harm_of_l2_enn_real (by positivity) (by positivity) (by positivity)
      (by positivity) hF hGlt hBlock'
    have hL : (3 : ℝ) ^ k / 3 = (3 : ℝ) ^ (k - 1) := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have hLinv : (3 : ℝ) ^ (k - 1) * ((3 : ℝ)⁻¹) ^ (k - 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
    have hLpos : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := by positivity
    set T : ℝ := lipL2 V (fun x => uV.toFun x - ub.toFun x) with hT
    set Gv : ℝ := lipGradL2 V uV.grad with hGvdef
    have hblockA : T ≤ ((3 : ℝ) ^ k / 3) * (Cin * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu * Gv +
        Cin * P' * (Gv + (3 : ℝ) ^ k / 3 * F)) := by
      rw [hL]
      have h1 : T = (3 : ℝ) ^ (k - 1) * (((3 : ℝ)⁻¹) ^ (k - 1) * T) := by
        rw [← mul_assoc, hLinv, one_mul]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hreal hLpos.le
    -- the gradient on `V` against the Caccioppoli bound on `□_{k-1}`
    have hmemG1 : MemLp (fun x => eucNorm (u.grad x)) 2
        (volume.restrict (Section6.engCube d (k - 1))) :=
      p13_memLp_euc ((u.grad_memVectorL2).mono_measure (Measure.restrict_mono hQ1Q le_rfl))
    have hvolG : (volume (Section6.engCube d (k - 1))).toReal ≤
        (3 : ℝ) ^ d * (volume V).toReal := by
      have h1 : (volume (Section6.engCube d (k - 2))).toReal ≤ (volume V).toReal :=
        ENNReal.toReal_mono hVt (measure_mono hV2)
      rw [lip_int_harm_of_l2_vol_toReal] at h1
      rw [lip_int_harm_of_l2_vol_toReal]
      have e : ((3 : ℝ) ^ d) ^ (k - 1) = (3 : ℝ) ^ d * ((3 : ℝ) ^ d) ^ (k - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [e]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hGv : Gv ≤ N1 * Section6.cubeGradL2 (k - 1) u.grad := by
      have h := lip_int_harm_of_l2_lipL2_mono_set (f := fun x => eucNorm (u.grad x)) hV1 hV0
        (Section6.eh_volume_engCube_ne_top (k - 1)) hvolG hmemG1
      rw [← lip_int_harm_of_l2_lipGradL2_engCube]
      exact h
    have hCacc := hcacc f F u hu hF hfb
    have hCacc' : Real.sqrt nu * Section6.cubeGradL2 (k - 1) u.grad ≤
        Cin * (Real.sqrt s * Section6.cubeFlat k u.toFun +
          (Real.sqrt s)⁻¹ * ((3 : ℝ) ^ k * F)) := by
      rw [← mul_assoc]
      exact hCacc
    have hEn' : lipL2 V (fun x => ub.toFun x - h.toFun x) ≤
        c ^ 2 * ((3 : ℝ) ^ k / 3) ^ 2 * ((Real.sqrt s ^ 2)⁻¹ * F) := by
      rw [hL, hrs]
      exact hEnergy
    have hArith := lip_int_harm_of_l2_arith (A := A) hCin hδ hδ' hr hq hP'0 hP'le H1 hH2 hN1'
      (sq_nonneg c) hGv (Section6.cubeFlat_nonneg _ _) hF ht hCacc' hblockA hEn'
    have hmemUh : MemLp (fun x => u.toFun x - h.toFun x) 2 (volume.restrict V) :=
      uV.memL2.sub h.memL2
    have hTri : lipL2 V (fun x => u.toFun x - h.toFun x) ≤
        T + lipL2 V (fun x => ub.toFun x - h.toFun x) := by
      have e : (fun x => u.toFun x - h.toFun x) =
          fun x => (uV.toFun x - ub.toFun x) + (ub.toFun x - h.toFun x) := by
        funext x
        show uV.toFun x - h.toFun x = _
        ring
      rw [e]
      exact lip_int_harm_of_l2_lipL2_add_le hV0 hVt (uV.memL2.sub ub.memL2) (ub.memL2.sub h.memL2)
    have hvol3 : (volume V).toReal ≤ ((3 : ℝ) ^ d) ^ 2 *
        (volume (Section6.engCube d (k - 3))).toReal := by
      have h1 : (volume V).toReal ≤ (volume (Section6.engCube d (k - 1))).toReal :=
        ENNReal.toReal_mono (Section6.eh_volume_engCube_ne_top (k - 1)) (measure_mono hV1)
      rw [lip_int_harm_of_l2_vol_toReal] at h1
      rw [lip_int_harm_of_l2_vol_toReal]
      have e : ((3 : ℝ) ^ d) ^ (k - 1) = ((3 : ℝ) ^ d) ^ 2 * ((3 : ℝ) ^ d) ^ (k - 3) := by
        rw [← pow_add]
        congr 1
        omega
      rw [← e]
      exact h1
    have hTr := lip_int_harm_of_l2_lipL2_mono_set hQ3V (lip_int_harm_of_l2_vol_ne_zero (k - 3))
      hVt hvol3 hmemUh
    have hS : Section6.IsSolOn (fun _ => (1 : Mat d)) V h.toFun h.grad :=
      (w0_isSolOn_iff _ V _ _).2 ⟨h, hh, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
    have hS3 := Section6.IsSolOn.mono hVo (Section6.eh_isOpen_engCube (k - 3)) hQ3V
      (Section6.eh_volume_engCube_ne_top (k - 3))
      ⟨1, 1, lip_int_harm_of_l2_ell_one (Section6.eh_measurableSet_engCube (k - 3))⟩ hS
    refine ⟨h.toFun, h.grad, hS3, ?_⟩
    rw [← lip_int_harm_of_l2_lipL2_engCube]
    have hcN : 0 ≤ N3 * K := mul_nonneg hN3' hK0
    have hX1 : 0 ≤ δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun :=
      mul_nonneg (mul_nonneg hδ ht.le) (Section6.cubeFlat_nonneg _ _)
    have hX2 : 0 ≤ s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F := by positivity
    have e1 : δ * ((3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) =
        δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun := by ring
    have e2 : (Real.sqrt s ^ 2)⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F = s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F := by
      rw [hrs]
    rw [e1, e2] at hArith
    calc lipL2 (Section6.engCube d (k - 3)) (fun x => u.toFun x - h.toFun x)
        ≤ N3 * lipL2 V (fun x => u.toFun x - h.toFun x) := hTr
      _ ≤ N3 * (K * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) +
            K * (s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F)) :=
          mul_le_mul_of_nonneg_left (hTri.trans hArith) hN3'
      _ = (N3 * K) * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun +
            s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) := by ring
      _ ≤ (1 + N3 * K + N27) * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun +
            s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) :=
          mul_le_mul_of_nonneg_right (by linarith only [hN27']) (add_nonneg hX1 hX2)

end SuperdiffusionCLT.Section7
