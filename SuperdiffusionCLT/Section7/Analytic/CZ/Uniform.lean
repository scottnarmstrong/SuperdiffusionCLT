/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.CaccioppoliB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Sobolev

/-!
# Global `W^{1,p}` estimate: energy bound and uniform Poincare inequality

For the divergence-form Dirichlet problem `-Δφ = ∇·F` with `φ ∈ H¹₀(U)`:

* `p13_energy`: `‖∇φ‖_{L²(U)} ≤ (d + 1) ‖F‖_{L²(U)}` (sup norm on vectors), with no dependence on `U`.
* `p13_poincare`: `‖φ‖_{L²(U)} ≤ c L ‖∇φ‖_{L²(U)}` when `U` lies in an axis cube of side `L`,
  with `c` depending only on `d`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p13_vecNormSq_eq (v : Vec d) : vecNormSq v = eucNorm v ^ 2 := by
  unfold eucNorm
  rw [Real.sq_sqrt]
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem p13_sup_le_euc (v : Vec d) : ‖v‖ ≤ eucNorm v := by
  have h0 : 0 ≤ eucNorm v := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_eucNorm v i

theorem p13_euc_le_sup (v : Vec d) : eucNorm v ≤ ((d : ℝ) + 1) * ‖v‖ := by
  have hn : 0 ≤ ‖v‖ := norm_nonneg v
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : ∀ i, v i * v i ≤ ‖v‖ ^ 2 := fun i => by
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hsq : vecNormSq v ≤ (((d : ℝ) + 1) * ‖v‖) ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = d * ‖v‖ ^ 2 := by simp
      _ ≤ (((d : ℝ) + 1) * ‖v‖) ^ 2 := by
        have h3 : (((d : ℝ) + 1) * ‖v‖) ^ 2 = d * ‖v‖ ^ 2 + ((d : ℝ) ^ 2 + d + 1) * ‖v‖ ^ 2 := by ring
        have h4 : 0 ≤ ((d : ℝ) ^ 2 + d + 1) * ‖v‖ ^ 2 := by positivity
        linarith only [h3, h4]
  unfold eucNorm
  exact Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩

theorem p13_continuous_eucNorm : Continuous (fun v : Vec d => eucNorm v) := by
  unfold eucNorm vecNormSq vecDot
  fun_prop

theorem p13_memLp_euc {μ : Measure (Vec d)} {f : Vec d → Vec d} (hf : MemLp f 2 μ) :
    MemLp (fun x => eucNorm (f x)) 2 μ := by
  refine (hf.norm.const_mul ((d : ℝ) + 1)).mono
    (p13_continuous_eucNorm.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h0 : 0 ≤ eucNorm (f x) := Real.sqrt_nonneg _
  have h1 := p13_euc_le_sup (f x)
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
  exact h1

theorem p13_integrable_vecNormSq {μ : Measure (Vec d)} {f : Vec d → Vec d} (hf : MemLp f 2 μ) :
    Integrable (fun x => vecNormSq (f x)) μ := by
  have := (p13_memLp_euc hf).integrable_sq
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  exact (p13_vecNormSq_eq (f x)).symm

theorem p13_eLpNorm_euc {μ : Measure (Vec d)} {f : Vec d → Vec d} (hf : MemLp f 2 μ) :
    eLpNorm (fun x => eucNorm (f x)) 2 μ =
      ENNReal.ofReal ((∫ x, vecNormSq (f x) ∂μ) ^ (1 / 2 : ℝ)) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 ENNReal.ofNat_ne_top
    (p13_memLp_euc hf).aestronglyMeasurable]
  have hint := p13_integrable_vecNormSq hf
  have hnn : 0 ≤ᵐ[μ] fun x => vecNormSq (f x) := Filter.Eventually.of_forall fun x => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hl : ∫⁻ x, ‖eucNorm (f x)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ = ENNReal.ofReal (∫ x, vecNormSq (f x) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine lintegral_congr fun x => ?_
    have h0 : 0 ≤ eucNorm (f x) := Real.sqrt_nonneg _
    rw [Real.enorm_eq_ofReal h0, p13_vecNormSq_eq, ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact (ENNReal.ofReal_pow h0 2).symm
  have hI : 0 ≤ ∫ x, vecNormSq (f x) ∂μ := integral_nonneg_of_ae hnn
  rw [hl, ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg hI (by norm_num)]

theorem p13_matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

theorem p13_abs_vecDot_le (x y : Vec d) : |vecDot x y| ≤ (vecNormSq x + vecNormSq y) / 2 := by
  have h1 := abs_vecDot_le_eucNorm_mul x y
  have h2 := two_mul_le_add_sq (eucNorm x) (eucNorm y)
  rw [p13_vecNormSq_eq, p13_vecNormSq_eq]
  linarith only [h1, h2]

theorem p13_aesm_vecDot {μ : Measure (Vec d)} {F G : Vec d → Vec d}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    AEStronglyMeasurable (fun x => vecDot (F x) (G x)) μ := by
  unfold vecDot
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  have h1 : AEStronglyMeasurable (fun x => F x i) μ := (continuous_apply i).comp_aestronglyMeasurable hF
  have h2 : AEStronglyMeasurable (fun x => G x i) μ := (continuous_apply i).comp_aestronglyMeasurable hG
  exact h1.mul h2

theorem p13_energy_sq {U : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 U F)
    (φ : H10Function U)
    (hw : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function 0 F) :
    ∫ x in U, vecNormSq (φ.toH1Function.grad x) ≤ ∫ x in U, vecNormSq (F x) := by
  have hG : MemLp φ.toH1Function.grad 2 (volume.restrict U) := φ.toH1Function.grad_memVectorL2
  have hF' : MemLp F 2 (volume.restrict U) := hF
  have hiF := p13_integrable_vecNormSq hF'
  have hiG := p13_integrable_vecNormSq hG
  have h := hw φ
  simp only [p13_matVecMul_one, Pi.zero_apply, zero_mul, integral_zero, zero_add] at h
  have h' : ∫ x in U, vecNormSq (φ.toH1Function.grad x) =
      ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) := h
  have hiD : Integrable (fun x => vecDot (F x) (φ.toH1Function.grad x)) (volume.restrict U) := by
    refine ((hiF.add hiG).div_const 2).mono' (p13_aesm_vecDot hF'.aestronglyMeasurable
      hG.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact p13_abs_vecDot_le _ _
  have hpt : ∀ x, vecDot (F x) (φ.toH1Function.grad x) ≤
      (vecNormSq (F x) + vecNormSq (φ.toH1Function.grad x)) / 2 := fun x =>
    (le_abs_self _).trans (p13_abs_vecDot_le _ _)
  have hmono : ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ≤
      ∫ x in U, (vecNormSq (F x) + vecNormSq (φ.toH1Function.grad x)) / 2 :=
    integral_mono hiD ((hiF.add hiG).div_const 2) hpt
  rw [integral_div, integral_add hiF hiG] at hmono
  linarith only [h', hmono]

/-- The energy bound for the divergence-form Dirichlet problem, in the sup norm. -/
theorem p13_energy {U : Set (Vec d)} {F : Vec d → Vec d} (hF : MemVectorL2 U F)
    (φ : H10Function U)
    (hw : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function 0 F) :
    eLpNorm φ.toH1Function.grad 2 (volume.restrict U) ≤
      ENNReal.ofReal ((d : ℝ) + 1) * eLpNorm F 2 (volume.restrict U) := by
  have hG : MemLp φ.toH1Function.grad 2 (volume.restrict U) := φ.toH1Function.grad_memVectorL2
  have hF' : MemLp F 2 (volume.restrict U) := hF
  have h1 : eLpNorm φ.toH1Function.grad 2 (volume.restrict U) ≤
      eLpNorm (fun x => eucNorm (φ.toH1Function.grad x)) 2 (volume.restrict U) := by
    refine eLpNorm_mono hG.aestronglyMeasurable fun x => ?_
    have h0 : 0 ≤ eucNorm (φ.toH1Function.grad x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact p13_sup_le_euc _
  have h2 : eLpNorm (fun x => eucNorm (F x)) 2 (volume.restrict U) ≤
      ENNReal.ofReal ((d : ℝ) + 1) * eLpNorm F 2 (volume.restrict U) := by
    have hc : eLpNorm (((d : ℝ) + 1) • F) 2 (volume.restrict U) =
        ENNReal.ofReal ((d : ℝ) + 1) * eLpNorm F 2 (volume.restrict U) := by
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    rw [← hc]
    refine eLpNorm_mono (p13_memLp_euc hF').aestronglyMeasurable fun x => ?_
    have h0 : 0 ≤ eucNorm (F x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact p13_euc_le_sup _
  refine h1.trans (le_trans ?_ h2)
  rw [p13_eLpNorm_euc hG, p13_eLpNorm_euc hF']
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.rpow_le_rpow (integral_nonneg fun x => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _) (p13_energy_sq hF φ hw) (by norm_num)

/-- Uniform Poincare inequality for `H¹₀(U)`, `U` inside an axis cube of side `L`. -/
theorem p13_poincare [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      U ⊆ axisCube z L → ∀ φ : H10Function U,
        eLpNorm φ.toH1Function.toFun 2 (volume.restrict U) ≤
          ENNReal.ofReal (c * L) *
            eLpNorm φ.toH1Function.grad 2 (volume.restrict U) := by
  have hP0 := Homogenization.unitDirichletPoincareConst_nonneg d
  set P := Homogenization.unitDirichletPoincareConst d with hPdef
  refine ⟨(P + 1) * d + 1, by positivity, ?_⟩
  intro U hU z L hL hUV φ
  set Φ := φ.extendByZeroToOpenSuperset hU.measurableSet (isOpen_axisCube z L) hUV with hΦ
  set M := volume.restrict (axisCube z L) with hM
  have hpo := Homogenization.scaled_dirichlet_poincare z hL Φ
  have hvalEq : eLpNorm Φ.toH1Function.toFun 2 M = eLpNorm φ.toH1Function.toFun 2 (volume.restrict U) := by
    rw [hΦ, H10Function.extendByZeroToOpenSuperset_toFun, H10Function.zeroExtension,
      MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet,
      Measure.restrict_restrict_of_subset hUV]
  have hcoord : ∀ i : Fin d, eLpNorm (fun x => Φ.toH1Function.grad x i) 2 M =
      eLpNorm (fun x => φ.toH1Function.grad x i) 2 (volume.restrict U) := by
    intro i
    have : (fun x => Φ.toH1Function.grad x i) = U.indicator (fun x => φ.toH1Function.grad x i) := by
      funext x
      rw [hΦ, H10Function.extendByZeroToOpenSuperset_grad, H10Function.zeroExtensionGrad]
      by_cases hx : x ∈ U <;> simp [hx]
    rw [this, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet,
      Measure.restrict_restrict_of_subset hUV]
  set A := eLpNorm φ.toH1Function.grad 2 (volume.restrict U) with hA
  set S := ∑ i : Fin d, eLpNorm (fun x => φ.toH1Function.grad x i) 2 (volume.restrict U) with hS
  have hcle : ∀ i : Fin d, eLpNorm (fun x => φ.toH1Function.grad x i) 2 (volume.restrict U) ≤ A := by
    intro i
    refine eLpNorm_mono (φ.toH1Function.gradMemL2 i).aestronglyMeasurable ?_
    intro x
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (φ.toH1Function.grad x) i
  have hSA : S ≤ (d : ℝ≥0∞) * A := by
    calc S ≤ ∑ _i : Fin d, A := Finset.sum_le_sum fun i _ => hcle i
      _ = d * A := by simp
  have hSfin : ∀ i : Fin d, eLpNorm (fun x => φ.toH1Function.grad x i) 2 (volume.restrict U) ≠ ⊤ :=
    fun i => (φ.toH1Function.gradMemL2 i).eLpNorm_ne_top
  have hSne : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => hSfin i
  have hv2 : eLpNorm φ.toH1Function.toFun 2 (volume.restrict U) ≠ ⊤ :=
    φ.toH1Function.memL2.eLpNorm_ne_top
  have hsum : (∑ i, (eLpNorm (fun x => Φ.toH1Function.grad x i) 2 M).toReal) = S.toReal := by
    rw [hS, ENNReal.toReal_sum (fun i _ => hSfin i)]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoord i]
  have hpo' : (eLpNorm φ.toH1Function.toFun 2 (volume.restrict U)).toReal ≤ P * L * S.toReal := by
    rw [← hsum, ← hvalEq]; exact hpo
  have hmain : eLpNorm φ.toH1Function.toFun 2 (volume.restrict U) ≤ ENNReal.ofReal (P * L) * S := by
    calc eLpNorm φ.toH1Function.toFun 2 (volume.restrict U)
        = ENNReal.ofReal ((eLpNorm φ.toH1Function.toFun 2 (volume.restrict U)).toReal) :=
          (ENNReal.ofReal_toReal hv2).symm
      _ ≤ ENNReal.ofReal (P * L * S.toReal) := ENNReal.ofReal_le_ofReal hpo'
      _ = ENNReal.ofReal (P * L) * S := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hSne]
  calc eLpNorm φ.toH1Function.toFun 2 (volume.restrict U) ≤ ENNReal.ofReal (P * L) * S := hmain
    _ ≤ ENNReal.ofReal (P * L) * ((d : ℝ≥0∞) * A) := mul_le_mul_right hSA _
    _ = ENNReal.ofReal (P * L * d) * A := by
        rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (((P + 1) * d + 1) * L) * A := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have h1 : ((P + 1) * d + 1) * L = P * L * d + (d + 1) * L := by ring
        have h2 : 0 ≤ ((d : ℝ) + 1) * L := by positivity
        linarith only [h1, h2]

end SuperdiffusionCLT.Section7
