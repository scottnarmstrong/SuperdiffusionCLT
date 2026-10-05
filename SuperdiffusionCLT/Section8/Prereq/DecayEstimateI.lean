/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateH
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# Dilation from the `ε`-problem to the unit-scale problem

The `ε`-equation `-∇·(S⁻¹ a(·/ε) ∇u) = F` on `B_R` becomes `-∇·(a ∇u_ε) = S ε² F(ε ·)` on `B_{R/ε}`
for `u_ε = u(ε ·)`, with `a = ν Id + (k - k(0))`.  Also: the integrals of the rescaled source, and
transfer of almost everywhere bounds along the dilation.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

theorem decayEst_mem_euclid_smul {ε R : ℝ} (hε : 0 < ε) {y : Vec d} :
    ε • y ∈ euclidBall (d := d) R ↔ y ∈ euclidBall (ε⁻¹ * R) := by
  rw [mem_euclidBall, mem_euclidBall, vecNormSq_smul, mul_pow, inv_pow]
  have h2 : 0 < ε ^ 2 := by positivity
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h (inv_pos.2 h2)
    rw [← mul_assoc, inv_mul_cancel₀ h2.ne', one_mul] at this
    exact this
  · intro h
    have := mul_lt_mul_of_pos_left h h2
    rw [← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul] at this
    exact this

/-- Almost everywhere statements pull back along a nonzero dilation. -/
theorem decayEst_ae_of_ae_dilate {ε : ℝ} (hε : ε ≠ 0) {P : Vec d → Prop}
    (h : ∀ᵐ y ∂(volume : Measure (Vec d)), P (ε • y)) : ∀ᵐ x ∂(volume : Measure (Vec d)), P x := by
  rw [ae_iff] at h ⊢
  have h2 : volume ((fun y : Vec d => ε • y) ⁻¹' {x | ¬ P x}) = 0 := h
  rw [Measure.addHaar_preimage_smul volume hε] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have : 0 < |(ε ^ Module.finrank ℝ (Vec d))⁻¹| := by
      rw [abs_pos]; exact inv_ne_zero (pow_ne_zero _ hε)
    exact absurd h3 (ENNReal.ofReal_pos.2 this).ne'
  · exact h3

/-- **Dilation of the solution.** -/
theorem decayEst_dilate_solution {R ε S : ℝ} (hε : 0 < ε) (hS : S ≠ 0) (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (u : H10Function (euclidBall (d := d) R)) (F : Vec d → ℝ)
    (hu : IsWeakSolutionOn (fun x => S⁻¹ • epField nu omega ε x) (euclidBall R)
      u.toH1Function F (fun _ => 0)) :
    ∃ um : H10Function (euclidBall (d := d) (ε⁻¹ * R)),
      (∀ y, um.toH1Function.toFun y = u.toH1Function.toFun (ε • y)) ∧
      IsWeakSolutionOn (fullCoefficientRecentered nu omega) (euclidBall (ε⁻¹ * R))
        um.toH1Function (fun y => S * ε ^ 2 * F (ε • y)) (fun _ => 0) := by
  have hset : ε⁻¹ • euclidBall (d := d) R = euclidBall (ε⁻¹ * R) :=
    decayEst_euclidBall_smul (inv_pos.2 hε) R
  have hε0 : ε ≠ 0 := hε.ne'
  refine ⟨(u.dilateArg hε0).castSet hset, ?_, ?_⟩
  · intro y
    rw [H10Function.castSet_toH1Function, H1Function.castSet_toFun,
      H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun]
  · have h1 := (IsWeakSolutionOn.dilate_h10 hε0 hu).smul S
    rw [H10Function.castSet_toH1Function]
    refine a18_transfer hset ?_ ?_ ?_ h1
    · intro y
      simp only [epField, smul_smul, inv_smul_smul₀ hε0]
      rw [mul_inv_cancel₀ hS, one_smul]
    · intro y
      ring
    · intro y
      simp


theorem decayEst_euclid_inv_smul {ε : ℝ} (hε : 0 < ε) :
    ε • euclidBall (d := d) (ε⁻¹ * 1) = euclidBall 1 := by
  rw [decayEst_euclidBall_smul hε]
  congr 1
  field_simp

theorem decayEst_setIntegral_scale {ε : ℝ} (hε : 0 < ε) (G : Vec d → ℝ) :
    ∫ y in euclidBall (d := d) (ε⁻¹ * 1), G (ε • y) =
      (ε ^ d)⁻¹ * ∫ x in euclidBall (d := d) 1, G x := by
  rw [Measure.setIntegral_comp_smul_of_pos volume G _ hε, decayEst_euclid_inv_smul hε]
  simp [Module.finrank_fintype_fun_eq_card]

theorem decayEst_memLp_comp_smul {ε : ℝ} (hε : 0 < ε) {F : Vec d → ℝ}
    (hF : MemLp F 2 (volume.restrict (euclidBall (d := d) 1))) :
    MemLp (fun y => F (ε • y)) 2 (volume.restrict (euclidBall (d := d) (ε⁻¹ * 1))) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (abs (ε ^ Module.finrank ℝ (Vec d))⁻¹) with hc
  have hmeas : Measurable (fun y : Vec d => ε • y) := measurable_const_smul ε
  have hpre : (fun y : Vec d => ε • y) ⁻¹' euclidBall (d := d) 1 =
      euclidBall (ε⁻¹ * 1) := by
    ext y
    exact decayEst_mem_euclid_smul hε
  have hmap : Measure.map (fun y : Vec d => ε • y)
      (volume.restrict (euclidBall (d := d) (ε⁻¹ * 1))) = c • volume.restrict (euclidBall 1) := by
    rw [← hpre, ← Measure.restrict_map hmeas (measurableSet_euclidBall _),
      Measure.map_addHaar_smul volume hε.ne']
    rw [Measure.restrict_smul]
  have hmp : MeasurePreserving (fun y : Vec d => ε • y)
      (volume.restrict (euclidBall (d := d) (ε⁻¹ * 1))) (c • volume.restrict (euclidBall 1)) :=
    ⟨hmeas, hmap⟩
  have hF' : MemLp F 2 (c • volume.restrict (euclidBall (d := d) 1)) :=
    hF.smul_measure ENNReal.ofReal_ne_top
  exact hF'.comp_measurePreserving hmp


/-- Properties of the rescaled source. -/
theorem decayEst_dilate_source {ε S : ℝ} (hε : 0 < ε) {F : Vec d → ℝ}
    (hF : MemLp F 2 (volume.restrict (euclidBall (d := d) 1)))
    (hsuppF : ∀ x, x ∉ euclidBall (d := d) 1 → F x = 0)
    (hmeanF : ∫ x in euclidBall (d := d) 1, F x = 0) :
    (∀ y, y ∉ euclidBall (d := d) (ε⁻¹ * 1) → S * ε ^ 2 * F (ε • y) = 0) ∧
      (∫ y in euclidBall (d := d) (ε⁻¹ * 1), S * ε ^ 2 * F (ε • y) = 0) ∧
      MemLp (fun y => S * ε ^ 2 * F (ε • y)) 2
        (volume.restrict (euclidBall (d := d) (ε⁻¹ * 1))) ∧
      (∫ y in euclidBall (d := d) (ε⁻¹ * 1), (S * ε ^ 2 * F (ε • y)) ^ 2 =
        (S * ε ^ 2) ^ 2 * (ε ^ d)⁻¹ * ∫ x in euclidBall (d := d) 1, F x ^ 2) := by
  refine ⟨fun y hy => ?_, ?_, ?_, ?_⟩
  · rw [hsuppF _ (fun h => hy ((decayEst_mem_euclid_smul hε).1 h)), mul_zero]
  · rw [integral_const_mul, decayEst_setIntegral_scale hε F, hmeanF]
    ring
  · exact (decayEst_memLp_comp_smul hε hF).const_mul _
  · have h1 : ∀ y : Vec d, (S * ε ^ 2 * F (ε • y)) ^ 2 = (S * ε ^ 2) ^ 2 * (F (ε • y)) ^ 2 :=
      fun y => by ring
    simp only [h1]
    rw [integral_const_mul, decayEst_setIntegral_scale hε (fun x => F x ^ 2)]
    ring


/-- The powers of `ε` and of the logarithm cancel under the dilation. -/
theorem decayEst_dilate_arith {ε r ℓ cs γ Cm I : ℝ} (hε : 0 < ε) (hr : 0 < r) (hℓ : 0 < ℓ)
    (hcs : 0 < cs) :
    Cm * (ε⁻¹ * r) ^ (-((d : ℝ) - 2 + γ)) *
        ((ε⁻¹ * 1) ^ (γ + (d : ℝ) / 2) * ℓ ^ (-(1 / 2 : ℝ)) *
          Real.sqrt ((2 * Real.sqrt (2 * cs * ℓ) * ε ^ 2) ^ 2 * (ε ^ d)⁻¹ * I)) =
      (Cm * (2 * Real.sqrt (2 * cs))) * r ^ (-((d : ℝ) - 2 + γ)) * Real.sqrt I := by
  set S : ℝ := 2 * Real.sqrt (2 * cs * ℓ) with hS
  have hS0 : 0 ≤ S := by positivity
  have hsd : Real.sqrt (ε ^ d) = ε ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    ring
  have h1 : Real.sqrt ((S * ε ^ 2) ^ 2 * (ε ^ d)⁻¹ * I) =
      S * ε ^ 2 * (ε ^ ((d : ℝ) / 2))⁻¹ * Real.sqrt I := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
      Real.sqrt_inv, hsd]
  have h2 : (ε⁻¹ * r) ^ (-((d : ℝ) - 2 + γ)) =
      ε ^ ((d : ℝ) - 2 + γ) * r ^ (-((d : ℝ) - 2 + γ)) := by
    rw [Real.mul_rpow (by positivity) hr.le, Real.inv_rpow hε.le, ← Real.rpow_neg hε.le, neg_neg]
  have h3 : (ε⁻¹ * 1) ^ (γ + (d : ℝ) / 2) = ε ^ (-(γ + (d : ℝ) / 2)) := by
    rw [mul_one, Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
  have h4 : (ε ^ ((d : ℝ) / 2))⁻¹ = ε ^ (-((d : ℝ) / 2)) := by
    rw [Real.rpow_neg hε.le]
  have h5 : ε ^ 2 = ε ^ (2 : ℝ) := by rw [Real.rpow_two]
  have key : ε ^ ((d : ℝ) - 2 + γ) * ε ^ (-(γ + (d : ℝ) / 2)) * ε ^ (2 : ℝ) *
      ε ^ (-((d : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hε, ← Real.rpow_add hε, ← Real.rpow_add hε]
    rw [show (d : ℝ) - 2 + γ + -(γ + (d : ℝ) / 2) + 2 + -((d : ℝ) / 2) = 0 by ring,
      Real.rpow_zero]
  have hsℓ : ℓ ^ (-(1 / 2 : ℝ)) * S = 2 * Real.sqrt (2 * cs) := by
    have : Real.sqrt ℓ = ℓ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow ℓ
    have h6 : ℓ ^ (-(1 / 2 : ℝ)) * Real.sqrt ℓ = 1 := by
      rw [this, ← Real.rpow_add hℓ]
      norm_num
    rw [hS, Real.sqrt_mul (by positivity)]
    calc ℓ ^ (-(1 / 2 : ℝ)) * (2 * (Real.sqrt (2 * cs) * Real.sqrt ℓ)) =
        2 * Real.sqrt (2 * cs) * (ℓ ^ (-(1 / 2 : ℝ)) * Real.sqrt ℓ) := by ring
      _ = _ := by rw [h6, mul_one]
  rw [h1, h2, h3, h4, h5]
  calc Cm * (ε ^ ((d : ℝ) - 2 + γ) * r ^ (-((d : ℝ) - 2 + γ))) *
        (ε ^ (-(γ + (d : ℝ) / 2)) * ℓ ^ (-(1 / 2 : ℝ)) *
          (S * ε ^ (2 : ℝ) * ε ^ (-((d : ℝ) / 2)) * Real.sqrt I)) =
      Cm * (ℓ ^ (-(1 / 2 : ℝ)) * S) * r ^ (-((d : ℝ) - 2 + γ)) * Real.sqrt I *
        (ε ^ ((d : ℝ) - 2 + γ) * ε ^ (-(γ + (d : ℝ) / 2)) * ε ^ (2 : ℝ) *
          ε ^ (-((d : ℝ) / 2))) := by ring
    _ = _ := by rw [key, hsℓ]; ring

end

/-!
# The decay estimate for the `ε`-problem at a good sample

Dilation of the unit-scale estimate `decayEst_micro` to the problem
`-L^ε u = F` on `B_R` with `F` of mean zero supported in `B_1`.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- The constant of the decay estimate for the `ε`-problem. -/
def decayEst_Cmacro (d : ℕ) (γ ν cs CH CP CL CB : ℝ) : ℝ :=
  decayEst_Cmicro d γ ν cs CH CP CL CB * (2 * Real.sqrt (2 * cs))

theorem decayEst_eLpNorm_two_real {S : Set (Vec d)} {F : Vec d → ℝ}
    (hF : MemLp F 2 (volume.restrict S)) :
    eLpNorm F 2 (volume.restrict S) = ENNReal.ofReal (Real.sqrt (∫ x in S, F x ^ 2)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  have hint : ∫ x in S, ‖F x‖ ^ (2 : ℝ≥0∞).toReal = ∫ x in S, F x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, sq_abs]
  rw [hint]
  simp only [ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow]
  norm_num

theorem decayEst_opScale_eq {cs ε : ℝ} (hε : ε < 1) (hε0 : 0 < ε) :
    (opScale cs ε)⁻¹ = 2 * Real.sqrt (2 * cs * Real.log ε⁻¹) := by
  have hlog : Real.log ε < 0 := Real.log_neg hε0 hε
  have h1 : |Real.log ε| = Real.log ε⁻¹ := by
    rw [abs_of_neg hlog, Real.log_inv]
  unfold opScale
  rw [h1, ← Real.sqrt_eq_rpow, mul_inv, inv_inv]
  norm_num


/-- Convert an almost everywhere bound into an `eLpNorm` bound at exponent `∞`. -/
theorem decayEst_eLpNorm_top_le {μ : Measure (Vec d)} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f μ) {M : ℝ} (h : ∀ᵐ x ∂μ, |f x| ≤ M) :
    eLpNorm f ⊤ μ ≤ ENNReal.ofReal M := by
  rw [eLpNorm_exponent_top hf]
  exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using h)

/-- **The decay estimate for the `ε`-problem at a good sample.** -/
theorem decayEst_macro [NeZero d] (hd : 2 ≤ d) {ν cs γ CH CP CL CB Y : ℝ} (hν : 0 < ν)
    (hcs : 0 < cs) (hγ : 0 < γ) (hCH : 0 ≤ CH) (hCP : 0 ≤ CP) (hCL : 0 ≤ CL) (hCB : 0 ≤ CB)
    (hY : 3 ≤ Y) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (hexist : ∀ (R' : ℝ) (g : Vec d → ℝ), 0 < R' → MemLp g 2 (volume.restrict (euclidBall (d := d) R')) →
      ∃ v : H10Function (euclidBall (d := d) R'),
        IsWeakSolutionOn (fun x => matTranspose (fullCoefficientRecentered ν omega x))
          (euclidBall R') v.toH1Function g (fun _ => 0))
    (hHolR : ∀ R' : ℝ, Y ≤ R' → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R')),
      IsWeakSolutionOn (fun x => matTranspose (fullCoefficientRecentered ν omega x))
        (euclidBall R') w f (fun _ => 0) →
      ∀ r' : ℝ, Y ≤ r' → r' ≤ R' / 2 →
        eLpNorm (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) r') ⊤
            (volume.restrict (euclidBall r')) ≤
          ENNReal.ofReal (CH * (r' / R') ^ γ) *
            (ballL2 R' (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) R') +
              ENNReal.ofReal (Real.log R' ^ (-(1 / 2 : ℝ)) * R' ^ 2) *
                eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R'))))
    (hPoR : ∀ R' : ℝ, Y ≤ R' → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R')),
      IsWeakSolutionOn (fun x => matTranspose (fullCoefficientRecentered ν omega x))
        (euclidBall R') w f (fun _ => 0) →
      lpBar (euclidBall (d := d) R') 2 (fun x => w.toFun x - ⨍ z in euclidBall R', w.toFun z) ≤
        ENNReal.ofReal (CP * R' * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt ν *
            Real.log R' ^ (-(1 / 4 : ℝ))) *
          lpBar (euclidBall R') 2 (fun x => eucNorm (w.grad x)) +
        ENNReal.ofReal (CP * R' ^ 2 * ν⁻¹ * Real.log R' ^ (-(100 : ℝ))) *
          lpBar (euclidBall R') 2 f)
    (hLin : ∀ s : ℝ, Y ≤ s → ∀ W V : Set (Vec d), V ⊆ W →
      (∀ x ∈ V, Metric.ball x (1 / (12 * (d : ℝ)) * s) ⊆ W) → W ⊆ Metric.ball 0 (2 * s) →
      ∀ w : H1Function W, IsWeakSolutionOn (fullCoefficientRecentered ν omega) W w
        (fun _ => 0) (fun _ => 0) →
        eLpNorm (fun x => w.toFun x - ⨍ z in V, w.toFun z) ⊤ (volume.restrict V) ≤
          ENNReal.ofReal CL * lpBar W 2 (fun x => w.toFun x - ⨍ z in W, w.toFun z))
    (hBd : ∀ R' : ℝ, Y ≤ R' → ∀ u' : H10Function (euclidBall (d := d) R'),
      IsWeakSolutionOn (fullCoefficientRecentered ν omega) (decayEst_ann (R' / 8) R')
        (u'.toH1Function.restrict (decayEst_ann_isOpen _ _) (decayEst_ann_subset _ _))
        (fun _ => 0) (fun _ => 0) →
      eLpNorm u'.toH1Function.toFun ⊤ (volume.restrict (decayEst_ann (d := d) (R' / 3) R')) ≤
        ENNReal.ofReal CB * lpBar (decayEst_ann (d := d) (R' / 4) R') 2
          (fun x => u'.toH1Function.toFun x -
            ⨍ z in decayEst_ann (d := d) (R' / 4) R', u'.toH1Function.toFun z))
    {ε r R : ℝ} (hε : 0 < ε) (hεY : Y ≤ ε⁻¹) (hr8 : 8 ≤ r) (hrR : r ≤ R)
    (u : H10Function (euclidBall (d := d) R)) (F : Vec d → ℝ)
    (hF : MemLp F 2 (volume.restrict (euclidBall (d := d) 1)))
    (hsuppF : ∀ x, x ∉ euclidBall (d := d) 1 → F x = 0)
    (hmeanF : ∫ x in euclidBall (d := d) 1, F x = 0)
    (hu : IsWeakSolutionOn (fun x => opScale cs ε • epCoeff ν omega ε x) (euclidBall R)
      u.toH1Function F (fun _ => 0)) :
    eLpNorm u.toH1Function.toFun ⊤ (volume.restrict (euclidBall (d := d) R \ euclidBall r)) ≤
      ENNReal.ofReal (decayEst_Cmacro d γ ν cs CH CP CL CB * r ^ (-((d : ℝ) - 2 + γ))) *
        eLpNorm F 2 (volume.restrict (euclidBall (d := d) 1)) := by
  have hε1 : (3 : ℝ) ≤ ε⁻¹ := hY.trans hεY
  have hεlt : ε < 1 := by
    have := mul_le_mul_of_nonneg_left hε1 hε.le
    rw [mul_inv_cancel₀ hε.ne'] at this
    linarith only [this, hε]
  have hεinv : 0 < ε⁻¹ := inv_pos.2 hε
  set ℓ : ℝ := Real.log ε⁻¹ with hℓ
  have hℓ1 : 1 ≤ ℓ := sdPoinc_one_le_log_three.trans (Real.log_le_log (by norm_num) hε1)
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  have hSpos : 0 < 2 * Real.sqrt (2 * cs * ℓ) := by
    have : 0 < Real.sqrt (2 * cs * ℓ) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hopS : (opScale cs ε)⁻¹ = 2 * Real.sqrt (2 * cs * ℓ) := decayEst_opScale_eq hεlt hε
  have hu' : IsWeakSolutionOn (fun x => (2 * Real.sqrt (2 * cs * ℓ))⁻¹ • epField ν omega ε x)
      (euclidBall R) u.toH1Function F (fun _ => 0) := by
    rw [← hopS, inv_inv]
    exact hu
  obtain ⟨um, hum, hweak⟩ := decayEst_dilate_solution hε hSpos.ne' ν omega u F hu'
  obtain ⟨hsupH, hmeanH, hLH, hsqH⟩ := decayEst_dilate_source (S := 2 * Real.sqrt (2 * cs * ℓ))
    hε hF hsuppF hmeanF
  have hRpos : 0 < R := by linarith only [hr8, hrR]
  have hrpos : 0 < r := by linarith only [hr8]
  have hmicro := decayEst_micro hd (fullCoefficientRecentered ν omega) hν hcs hγ hCH hCP hCL hCB
    (Y := Y) (by linarith only [hY]) hℓ1
    (fun x => symmPart_fullCoefficientRecentered ν omega x)
    (Rm := ε⁻¹ * R) (rm := ε⁻¹ * r) (ρ := ε⁻¹ * 1) (by rw [mul_one]; exact hεY)
    (by rw [mul_one]; nlinarith only [hr8, hεinv])
    (by nlinarith only [hrR, hεinv])
    (Real.log_le_log hεinv (by nlinarith only [hr8, hεinv]))
    (fun g hg => hexist (ε⁻¹ * R) g (by positivity) hg) hHolR hPoR hLin hBd um
    (fun y => 2 * Real.sqrt (2 * cs * ℓ) * ε ^ 2 * F (ε • y)) hweak hsupH hmeanH hLH
  rw [hsqH] at hmicro
  set I : ℝ := ∫ x in euclidBall (d := d) 1, F x ^ 2 with hI
  have hM := decayEst_dilate_arith (d := d) (γ := γ) (Cm := decayEst_Cmicro d γ ν cs CH CP CL CB)
    (I := I) hε hrpos hℓ0 hcs
  rw [hM] at hmicro
  set M : ℝ := decayEst_Cmacro d γ ν cs CH CP CL CB * r ^ (-((d : ℝ) - 2 + γ)) * Real.sqrt I
    with hMdef
  have hMeq : decayEst_Cmicro d γ ν cs CH CP CL CB * (2 * Real.sqrt (2 * cs)) *
      r ^ (-((d : ℝ) - 2 + γ)) * Real.sqrt I = M := by
    rw [hMdef, decayEst_Cmacro]
  rw [hMeq] at hmicro
  have hDm : MeasurableSet (euclidBall (d := d) (ε⁻¹ * R) \ euclidBall (ε⁻¹ * r)) :=
    (measurableSet_euclidBall _).diff (measurableSet_euclidBall _)
  have hD : MeasurableSet (euclidBall (d := d) R \ euclidBall r) :=
    (measurableSet_euclidBall _).diff (measurableSet_euclidBall _)
  have hmacro : ∀ᵐ x ∂volume.restrict (euclidBall (d := d) R \ euclidBall r),
      |u.toH1Function.toFun x| ≤ M := by
    rw [ae_restrict_iff' hD]
    refine decayEst_ae_of_ae_dilate hε.ne'
      (P := fun x => x ∈ euclidBall (d := d) R \ euclidBall r → |u.toH1Function.toFun x| ≤ M) ?_
    have := (ae_restrict_iff' hDm).1 hmicro
    filter_upwards [this] with y hy hyD
    have hyD' : y ∈ euclidBall (d := d) (ε⁻¹ * R) \ euclidBall (ε⁻¹ * r) :=
      ⟨(decayEst_mem_euclid_smul hε).1 hyD.1, fun h => hyD.2 ((decayEst_mem_euclid_smul hε).2 h)⟩
    have := hy hyD'
    rwa [hum y] at this
  have hmeas : AEStronglyMeasurable u.toH1Function.toFun
      (volume.restrict (euclidBall (d := d) R \ euclidBall r)) :=
    u.toH1Function.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono Set.sdiff_subset le_rfl)
  refine (decayEst_eLpNorm_top_le hmeas hmacro).trans (le_of_eq ?_)
  rw [decayEst_eLpNorm_two_real hF, hMdef, ENNReal.ofReal_mul' (Real.sqrt_nonneg _)]

end

end

end SuperdiffusionCLT.Section8
