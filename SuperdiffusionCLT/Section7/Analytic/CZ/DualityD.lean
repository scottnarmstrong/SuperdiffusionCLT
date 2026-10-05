/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.DualityC

/-!
# The duality step

If the divergence-form estimate holds at the conjugate exponent `p'` on a fixed bounded domain
`U`, with constant `Cq`, then it holds at `p` for `W^{-1,p}` data plus `L^p` divergence data
with the constant `Cq`, up to the dimensional factor `d` from Hölder's inequality for the sup
norm on `ℝᵈ`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p14_abs_vecDot_le (a b : Vec d) : |vecDot a b| ≤ d * ‖a‖ * ‖b‖ := by
  unfold vecDot
  calc |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖a‖ * ‖b‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using norm_le_pi_norm a i) (by simpa using norm_le_pi_norm b i)
          (abs_nonneg _) (norm_nonneg _)
    _ = d * ‖a‖ * ‖b‖ := by simp [mul_assoc]

theorem p14_grad_aesm {U : Set (Vec d)} (u : H1Function U) :
    AEStronglyMeasurable u.grad (volume.restrict U) :=
  (aemeasurable_pi_iff.2 fun i => (u.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable

/-- Hölder's inequality for the normalized norms and the sup norm. -/
theorem p14_holder_pairing {U : Set (Vec d)} (h0 : volume U ≠ 0)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) {F g : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (volume.restrict U))
    (hg : AEStronglyMeasurable g (volume.restrict U)) :
    ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (g x)| ≤
      ENNReal.ofReal d * lpBar U p F * lpBar U p.conjExponent g := by
  have hcT : (volume U)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have hP : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hpt).2 hp1
    simpa using this
  have hp : p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hpt).symm
  have hconj : (p.toReal).HolderConjugate (p.toReal / (p.toReal - 1)) := by
    refine Real.HolderConjugate.conjExponent hP
  have hH : ENNReal.HolderConjugate p p.conjExponent := by
    rw [p14_conj hp1 hpt]
    have := hconj.ennrealOfReal
    rwa [← hp] at this
  have hfm : AEStronglyMeasurable (fun x => vecDot (F x) (g x)) (volume.restrict U) := by
    unfold vecDot
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((continuous_apply i).comp_aestronglyMeasurable hF).mul
        ((continuous_apply i).comp_aestronglyMeasurable hg)
  have hb : Continuous (fun z : Vec d × Vec d => vecDot z.1 z.2) := by
    unfold vecDot
    fun_prop
  have hmain := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm
    (μ := ((volume U)⁻¹) • volume.restrict U) (p := p) (q := p.conjExponent) (r := 1)
    (fun a b : Vec d => vecDot a b) (ENNReal.ofReal d) hb
    (hF.smul_measure _) (hg.smul_measure _)
    (Filter.Eventually.of_forall fun x => by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (Nat.cast_nonneg d),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs]
      exact p14_abs_vecDot_le _ _)
  have e1 : eLpNorm (fun x => vecDot (F x) (g x)) 1 (((volume U)⁻¹) • volume.restrict U) =
      (volume U)⁻¹ * ∫⁻ x in U, ‖vecDot (F x) (g x)‖ₑ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hfm.smul_measure _), lintegral_smul_measure, smul_eq_mul]
  have e2 : ENNReal.ofReal |(volume U).toReal⁻¹ * ∫ x in U, vecDot (F x) (g x)| =
      (volume U)⁻¹ * ENNReal.ofReal |∫ x in U, vecDot (F x) (g x)| := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ← ENNReal.toReal_inv,
      ENNReal.ofReal_toReal hcT]
  rw [e2]
  refine le_trans ?_ hmain
  rw [e1]
  gcongr
  rw [← Real.norm_eq_abs, ofReal_norm]
  exact enorm_integral_le_lintegral_enorm _

theorem p14_isElliptic_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn (d := d) 1 1 U (fun _ => (1 : Mat d)) := by
  classical
  refine ⟨?_, fun x _ => isEllipticMatrix_one⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite hU measurable_const measurable_const

theorem p14_volume_lt_top {U : Set (Vec d)} (hb : IsBoundedDomain U) : volume U ≠ ∞ := by
  obtain ⟨R, hR0, hR⟩ := hb
  refine ne_of_lt (lt_of_le_of_lt (measure_mono (t := Metric.closedBall (0 : Vec d) R) ?_)
    (Metric.isBounded_closedBall.measure_lt_top))
  intro x hx
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg hR0.le).2 fun i => by simpa using hR x hx i

/-- **Duality step.** If the divergence-form estimate holds on `U` at the conjugate exponent
`p'` with constant `Cq`, then a solution `φ` of `-Δφ = h - ∇·F` satisfies
`lpBar U p ∇φ ≤ Cq (wMinusOneBar U p h + d · lpBar U p F)`. -/
theorem p14_duality_step [NeZero d] {U : Set (Vec d)} (hUo : IsOpen U) (hUb : IsBoundedDomain U)
    (hne : U.Nonempty) {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hq : ∀ (G : Vec d → Vec d) (ψ : H10Function U), MemVectorL2 U G →
      IsWeakSolutionOn (fun _ => (1 : Mat d)) U ψ.toH1Function 0 G →
      lpBar U p.conjExponent ψ.toH1Function.grad ≤
        ENNReal.ofReal Cq * lpBar U p.conjExponent G)
    {h : Vec d → ℝ} {F : Vec d → Vec d} (φ : H10Function U)
    (hφ : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function h F)
    (hw : wMinusOneBar U p h ≠ ∞) (hF : AEStronglyMeasurable F (volume.restrict U))
    (hFp : lpBar U p F ≠ ∞) :
    lpBar U p φ.toH1Function.grad ≤
      ENNReal.ofReal Cq * (wMinusOneBar U p h + ENNReal.ofReal d * lpBar U p F) := by
  have h0 : volume U ≠ 0 := (hUo.measure_pos volume hne).ne'
  have hfin : volume U ≠ ∞ := p14_volume_lt_top hUb
  have hfm : IsFiniteMeasure (volume.restrict U) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hcT : (volume U)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have hS : IsFiniteMeasure (((volume U)⁻¹) • volume.restrict U) :=
    ⟨by simpa [Measure.smul_apply, Measure.restrict_apply_univ] using
      ENNReal.mul_lt_top hcT.lt_top hfin.lt_top⟩
  obtain ⟨C0, -, hC⟩ := h10_dirichlet_wellPosed hUo hUb hne
  set X : ℝ≥0∞ := wMinusOneBar U p h + ENNReal.ofReal d * lpBar U p F with hXdef
  have hXT : X ≠ ∞ := ENNReal.add_ne_top.2 ⟨hw, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFp⟩
  have hM : ENNReal.ofReal (Cq * X.toReal) = ENNReal.ofReal Cq * X := by
    rw [ENNReal.ofReal_mul hCq, ENNReal.ofReal_toReal hXT]
  rw [← hM]
  refine p14_norming h0 hfin hp1 hpt (p14_grad_aesm φ.toH1Function) fun G hGm hB => ?_
  obtain ⟨B, hB⟩ := hB
  have hGL2 : MemVectorL2 U G :=
    MemLp.of_bound hGm.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  obtain ⟨ψ, hψ⟩ := (hC (p14_isElliptic_one hUo.measurableSet) (f := (0 : Vec d → ℝ)) (g := G)
    MemLp.zero hGL2).1
  have hGfin : lpBar U p.conjExponent G ≠ ∞ := by
    have : MemLp G p.conjExponent (((volume U)⁻¹) • volume.restrict U) :=
      MemLp.of_bound (hGm.aestronglyMeasurable.smul_measure _) B
        (Measure.ae_smul_measure (Filter.Eventually.of_forall hB) _)
    exact this.eLpNorm_ne_top
  have hLψ := hq G ψ hGL2 hψ
  have hLfin : lpBar U p.conjExponent ψ.toH1Function.grad ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin) hLψ
  have hid := p14_adjoint_identity φ ψ hφ hψ
  have e : ∫ x in U, vecDot (φ.toH1Function.grad x) (G x) =
      (∫ x in U, h x * ψ.toH1Function.toFun x) +
        ∫ x in U, vecDot (F x) (ψ.toH1Function.grad x) := by
    rw [← hid]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => p14_vecDot_comm _ _)
  rw [e]
  set A := ∫ x in U, h x * ψ.toH1Function.toFun x
  set B' := ∫ x in U, vecDot (F x) (ψ.toH1Function.grad x)
  have hA := p14_wMinusOne_bound U p h ψ hw hLfin
  have hB' := p14_holder_pairing h0 hp1 hpt hF (p14_grad_aesm ψ.toH1Function)
  have htri : ENNReal.ofReal |(volume U).toReal⁻¹ * (A + B')| ≤
      ENNReal.ofReal |(volume U).toReal⁻¹ * A| + ENNReal.ofReal |(volume U).toReal⁻¹ * B'| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_add]
    exact abs_add_le _ _
  calc _ ≤ _ := htri
    _ ≤ wMinusOneBar U p h * lpBar U p.conjExponent ψ.toH1Function.grad +
        ENNReal.ofReal d * lpBar U p F * lpBar U p.conjExponent ψ.toH1Function.grad :=
        add_le_add hA hB'
    _ = X * lpBar U p.conjExponent ψ.toH1Function.grad := by
        rw [hXdef, add_mul, mul_assoc]
    _ ≤ X * (ENNReal.ofReal Cq * lpBar U p.conjExponent G) := by gcongr
    _ = ENNReal.ofReal (Cq * X.toReal) * lpBar U p.conjExponent G := by rw [hM]; ring

end SuperdiffusionCLT.Section7
