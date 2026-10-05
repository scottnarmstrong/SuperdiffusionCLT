/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorApproxE
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Interior
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalB

/-!
# Interior approximation: De Giorgi for solutions minus a constant, and the mollification error

`ip_dg_abs` is the `L^∞`-`L²` estimate of the printed argument: for a weak solution `u` in an axis
cube and any constant `c`, the sup norm of `u - c` on the concentric half cube is bounded by
`C (Λ/λ)^N` times the normalized `L²` norm of `u - c` plus the right-hand side.
The mollification step turns a sup bound of `u - c` into a sup bound of `u - η_h ∗ u` (the last
display of the printed argument).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constant function as an `H¹` function on a set of finite measure. -/
noncomputable def ip_const (U : Set (Vec d)) (hU : volume U ≠ ⊤) (c : ℝ) : H1Function U where
  toFun := fun _ => c
  grad := fun _ => 0
  memL2 := by
    have : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hU.lt_top⟩
    exact memLp_const c
  gradMemL2 := fun i => by
    have : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hU.lt_top⟩
    exact memLp_const (0 : ℝ)
  hasWeakGradient := by
    have := HasWeakGradientOn.of_contDiff (U := U) (f := fun _ : Vec d => c) contDiff_const
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply] at this
    exact this

@[simp] theorem ip_const_toFun (U : Set (Vec d)) (hU : volume U ≠ ⊤) (c : ℝ) (x : Vec d) :
    (ip_const U hU c).toFun x = c := rfl

@[simp] theorem ip_const_grad (U : Set (Vec d)) (hU : volume U ≠ ⊤) (c : ℝ) (x : Vec d) :
    (ip_const U hU c).grad x = 0 := rfl

/-- Subtracting a constant keeps a weak solution (zero vector datum). -/
theorem ip_isWeakSolutionOn_sub_const {a : CoeffField d} {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    {u : H1Function U} {f : Vec d → ℝ} (h : IsWeakSolutionOn a U u f (fun _ => 0)) (c : ℝ) :
    IsWeakSolutionOn a U (u - ip_const U hU c) f (fun _ => 0) := by
  intro φ
  have h1 := h φ
  have hg : (u - ip_const U hU c).grad = u.grad := by
    funext x
    simp
  rw [hg]
  exact h1

/-- Negating a weak solution keeps a weak solution, with the negated right-hand side. -/
theorem ip_isWeakSolutionOn_neg {a : CoeffField d} {U : Set (Vec d)}
    {u : H1Function U} {f : Vec d → ℝ} (h : IsWeakSolutionOn a U u f (fun _ => 0)) :
    IsWeakSolutionOn a U (-u) (fun x => -f x) (fun _ => 0) := by
  intro φ
  have h1 := h φ
  have hg : (-u).grad = fun x => -u.grad x := by
    funext x
    simp
  rw [hg]
  simp only [matVecMul_neg, vecDot_neg_left, MeasureTheory.integral_neg, neg_mul, vecDot_zero_left,
    integral_zero, add_zero] at h1 ⊢
  rw [h1]

/-- **De Giorgi `L^∞`–`L²` bound for `u - c`, two-sided.** -/
theorem ip_dg_abs (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (axisCube z L) a →
      ∀ (f : Vec d → ℝ) (u : H1Function (axisCube z L)) (c : ℝ),
        IsWeakSolutionOn a (axisCube z L) u f (fun _ => 0) →
        eLpNorm (fun x => u.toFun x - c) ⊤ (volume.restrict (halfCube z L)) ≤
          ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
            (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
                eLpNorm (fun x => u.toFun x - c) 2 (volume.restrict (axisCube z L)) +
              ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (axisCube z L))) := by
  obtain ⟨C, hC, H⟩ := deGiorgi_interior_bound hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a z L hL hEll f u c hu
  have hU : volume (axisCube z L) ≠ ⊤ := (volume_axisCube_lt_top z L).ne
  have hvs : IsWeakSolutionOn a (axisCube z L) (u - ip_const (axisCube z L) hU c) f (fun _ => 0) :=
    ip_isWeakSolutionOn_sub_const hU hu c
  have hvn : IsWeakSolutionOn a (axisCube z L) (-(u - ip_const (axisCube z L) hU c)) (fun x => -f x) (fun _ => 0) :=
    ip_isWeakSolutionOn_neg hvs
  have hg : AEStronglyMeasurable (fun _ : Vec d => (0 : Vec d)) (volume.restrict (axisCube z L)) :=
    aestronglyMeasurable_const
  have h1 := H z hL hEll f (fun _ => 0) hg _ hvs
  have h2 := H z hL hEll (fun x => -f x) (fun _ => 0) hg _ hvn
  have e0 : eLpNorm (fun x => eucNorm ((fun _ : Vec d => (0 : Vec d)) x)) ⊤ (volume.restrict (axisCube z L)) = 0 := by
    have : (fun x => eucNorm ((fun _ : Vec d => (0 : Vec d)) x)) = fun _ => (0 : ℝ) := by
      funext x
      simp [eucNorm, vecNormSq, vecDot]
    rw [this]
    exact eLpNorm_zero
  rw [e0, mul_zero, add_zero] at h1 h2
  have ef : eLpNorm (fun x => -f x) ⊤ (volume.restrict (axisCube z L)) = eLpNorm f ⊤ (volume.restrict (axisCube z L)) :=
    eLpNorm_neg f ⊤ _
  rw [ef] at h2
  simp only [H1Function.neg_toFun, H1Function.sub_toFun, ip_const_toFun] at h1 h2
  have hum : AEStronglyMeasurable (fun x => u.toFun x - c) (volume.restrict (axisCube z L)) :=
    (u.memL2.aestronglyMeasurable).sub aestronglyMeasurable_const
  have hmono2 : eLpNorm (fun x => max (u.toFun x - c) 0) 2 (volume.restrict (axisCube z L)) ≤
      eLpNorm (fun x => u.toFun x - c) 2 (volume.restrict (axisCube z L)) :=
    eLpNorm_mono (hum.aemeasurable.max aemeasurable_const).aestronglyMeasurable (fun x => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hmono2' : eLpNorm (fun x => max (-(u.toFun x - c)) 0) 2 (volume.restrict (axisCube z L)) ≤
      eLpNorm (fun x => u.toFun x - c) 2 (volume.restrict (axisCube z L)) :=
    eLpNorm_mono (hum.aemeasurable.neg.max aemeasurable_const).aestronglyMeasurable (fun x => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (neg_le_abs _) (abs_nonneg _))
  set B : ℝ≥0∞ := ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
    (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
        eLpNorm (fun x => u.toFun x - c) 2 (volume.restrict (axisCube z L)) +
      ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (axisCube z L))) with hB
  have hB1 : eLpNorm (fun x => max (u.toFun x - c) 0) ⊤ (volume.restrict (halfCube z L)) ≤ B :=
    h1.trans (by
      rw [hB]
      gcongr)
  have hB2 : eLpNorm (fun x => max (-(u.toFun x - c)) 0) ⊤ (volume.restrict (halfCube z L)) ≤ B :=
    h2.trans (by
      rw [hB]
      gcongr)
  have hsub : halfCube z L ⊆ axisCube z L := halfCube_subset z L
  have hmh : AEStronglyMeasurable (fun x => u.toFun x - c) (volume.restrict (halfCube z L)) :=
    hum.mono_measure (Measure.restrict_mono hsub le_rfl)
  rw [eLpNorm_exponent_top hmh]
  refine eLpNormEssSup_le_of_ae_enorm_bound ?_
  have m1 : AEStronglyMeasurable (fun x => max (u.toFun x - c) 0) (volume.restrict (halfCube z L)) :=
    (hmh.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun x => max (-(u.toFun x - c)) 0)
      (volume.restrict (halfCube z L)) := (hmh.aemeasurable.neg.max aemeasurable_const).aestronglyMeasurable
  rw [eLpNorm_exponent_top m1] at hB1
  rw [eLpNorm_exponent_top m2] at hB2
  filter_upwards [enorm_ae_le_eLpNormEssSup (fun x => max (u.toFun x - c) 0)
    (volume.restrict (halfCube z L)), enorm_ae_le_eLpNormEssSup
    (fun x => max (-(u.toFun x - c)) 0) (volume.restrict (halfCube z L))] with x hx1 hx2
  rcases le_total 0 (u.toFun x - c) with hs | hs
  · calc ‖u.toFun x - c‖ₑ = ‖max (u.toFun x - c) 0‖ₑ := by rw [max_eq_left hs]
      _ ≤ _ := hx1.trans hB1
  · calc ‖u.toFun x - c‖ₑ = ‖max (-(u.toFun x - c)) 0‖ₑ := by
          rw [max_eq_left (by linarith only [hs]), enorm_neg]
      _ ≤ _ := hx2.trans hB2

theorem ip_kernel_integral {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} :
    ∫ w, a16_kernel d h η w = ∫ w, η w := by
  unfold a16_kernel
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_smul_of_nonneg (volume : Measure (Vec d)) η
    h⁻¹ (hR := inv_nonneg.2 hh.le)]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  
/-- The mollification of `u` at `x` differs from the constant `c` by at most `S`, when
`|u - c| ≤ S` almost everywhere on a measurable set containing the sup-ball of radius `h`. -/
theorem ip_moll_sub_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    {u : Vec d → ℝ} {x : Vec d} {H : Set (Vec d)} (hHm : MeasurableSet H)
    (hH : Metric.closedBall x h ⊆ H) (hum : AEStronglyMeasurable u (volume.restrict H))
    {c S : ℝ} (hS : ∀ᵐ w ∂(volume.restrict H), |u w - c| ≤ S) :
    |l2a_moll d h η u x - c| ≤ S := by
  set k : Vec d → ℝ := fun w => a16_kernel d h η (x - w) with hk
  have hk0 : ∀ w, 0 ≤ k w := fun w =>
    mul_nonneg (pow_nonneg (inv_nonneg.2 hh.le) _) (hη0 _)
  have hkz : ∀ w, w ∉ Metric.closedBall x h → k w = 0 := by
    intro w hw
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw
    have : h < ‖x - w‖ := by rwa [← norm_neg, neg_sub]
    exact l2a_kernel_eq_zero_of_norm hh hηs this
  have hkc : Continuous k := (a16_kernel_continuous hηc).comp (continuous_const.sub continuous_id)
  have hkcs : HasCompactSupport k :=
    (l2a_kernel_compact hh hηs).comp_homeomorph (Homeomorph.subLeft x)
  have hkI : Integrable k := hkc.integrable_of_hasCompactSupport hkcs
  have hkint : ∫ w, k w = 1 := by
    have := integral_sub_left_eq_self (fun t => a16_kernel d h η t) (volume : Measure (Vec d)) x
    rw [hk]
    simp only
    rw [this, ip_kernel_integral hh, hη1]
  set g : Vec d → ℝ := fun w => k w * (u w - c) with hg
  have hgb : ∀ᵐ w ∂(volume.restrict H), ‖g w‖ ≤ S * k w := by
    filter_upwards [hS] with w hw
    simp only [hg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 w)]
    nlinarith only [hw, hk0 w]
  have hgI : IntegrableOn g H := by
    refine Integrable.mono' ((hkI.const_mul S).integrableOn) ?_ hgb
    exact (hkc.aestronglyMeasurable.mono_measure le_rfl).mul (hum.sub aestronglyMeasurable_const)
  have hgsupp : Function.support g ⊆ H := by
    intro w hw
    by_contra hwH
    exact hw (by simp only [hg, hkz w (fun hc => hwH (hH hc)), zero_mul])
  have hgI' : Integrable g := (integrableOn_iff_integrable_of_support_subset hgsupp).1 hgI
  have hmoll : l2a_moll d h η u x = (∫ w, g w) + c := by
    unfold l2a_moll
    have : (fun y => a16_kernel d h η (x - y) * u y) = fun w => g w + c * k w := by
      funext w
      simp only [hg, hk]
      ring
    rw [this, integral_add hgI' (hkI.const_mul c), integral_const_mul, hkint, mul_one]
  rw [hmoll, add_sub_cancel_right]
  have hae : ∀ᵐ w ∂(volume : Measure (Vec d)), ‖g w‖ ≤ S * k w := by
    filter_upwards [(ae_restrict_iff' hHm).1 hgb] with w hw
    by_cases hwH : w ∈ H
    · exact hw hwH
    · have : k w = 0 := hkz w (fun hc => hwH (hH hc))
      simp only [hg, this, zero_mul, norm_zero, mul_zero, le_refl]
  have := norm_integral_le_of_norm_le (hkI.const_mul S) hae
  rw [integral_const_mul, hkint, mul_one] at this
  simpa only [Real.norm_eq_abs] using this

end SuperdiffusionCLT.Section7
