/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorApproxD
public import SuperdiffusionCLT.Section7.Analytic.CZ.GlobalC

/-!
# Interior approximation: the deterministic core

`ia_core`: the sup norm of `uhom - η_h ∗ u` on the rounded cube `V` is bounded by
`C L (B / s + s⁻¹ ‖f‖_∞ d √d h)`, where `B` bounds `η_h ∗ ((a - s)∇u)` on `V`
(Calderon-Zygmund at `p = 2d` and Morrey's inequality applied to the equation of `ia_weak_eq`).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A bounded vector field with continuous components on `V` is in `L²(V)`. -/
theorem ia_memVectorL2_of_bound {V : Set (Vec d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {G : Vec d → Vec d} (hGm : ∀ i, ∃ c : Vec d → ℝ, Continuous c ∧ ∀ x ∈ V, G x i = c x)
    {B : ℝ} (hB : ∀ x ∈ V, ‖G x‖ ≤ B) : MemVectorL2 V G := by
  have : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVb.measure_lt_top⟩
  refine MemLp.of_bound ?_ B ?_
  · refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.mpr fun i => ?_)
    obtain ⟨c, hc, hce⟩ := hGm i
    refine hc.measurable.aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact (hce x hx).symm
  · filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact hB x hx

/-- A bounded function has small normalized norm. -/
theorem ia_lpBar_le_of_bound {V : Set (Vec d)} (ht : volume V ≠ ⊤) {E : Type*}
    [NormedAddCommGroup E] {G : Vec d → E} (hG : AEStronglyMeasurable G (volume.restrict V))
    {C : ℝ} (hC : ∀ x ∈ V, ‖G x‖ ≤ C) (hV : MeasurableSet V) (q : ℝ≥0∞) :
    lpBar V q G ≤ ENNReal.ofReal C := by
  unfold lpBar
  by_cases h0 : volume V = 0
  · rw [Measure.restrict_eq_zero.2 h0, smul_zero, eLpNorm_measure_zero]; exact zero_le
  have hp : IsProbabilityMeasure (((volume V)⁻¹) • volume.restrict V) := by
    refine ⟨?_⟩
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 ht
  have := eLpNorm_le_of_ae_bound (p := q) (hG.smul_measure ((volume V)⁻¹))
    (C := C) (MeasureTheory.Measure.ae_smul_measure (by
      filter_upwards [ae_restrict_mem hV] with x hx
      exact hC x hx) _)
  rwa [measure_univ, ENNReal.one_rpow, one_mul] at this

/-- **The deterministic core of the interior approximation**: the sup norm of
`uhom - η_h ∗ u` on the rounded cube `V` (CZ at `p = 2d` and Morrey applied to the equation of
`ia_weak_eq`), in terms of a sup bound `B` of the mollified flux `η_h ∗ ((a - s)∇u)` on `V`. -/
theorem ia_core [NeZero d] (hd : 2 ≤ d) (M₁ κ ρ : ℝ) :
    ∃ Cc : ℝ, 0 < Cc ∧
      ∀ {Q V : Set (Vec d)} {r M₂ D : ℝ} {z : Vec d} {L : ℝ}, IsOpen Q → Bornology.IsBounded Q →
        IsUniformC11Domain V r M₁ M₂ D → r * M₂ ≤ κ → D ≤ ρ * r → 0 < L → V ⊆ axisCube z L →
        V ⊆ Q →
        ∀ {h : ℝ}, 0 < h → ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → (∀ w, 0 ≤ η w) →
          ∫ w, η w = 1 → (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
        ∀ {rc : ℝ}, 0 < rc →
          (∀ x ∈ Metric.cthickening h V, x ∈ Q ∧ 2 * rc < Metric.infDist x Qᶜ) →
        ∀ {a : CoeffField d} {u : H1Function Q} {f : Vec d → ℝ} {s : ℝ}, 0 < s →
          (∀ i, LocallyIntegrableOn (fun x => matVecMul (a x) (u.grad x) i) Q volume) →
          LocallyIntegrableOn f Q volume → Measurable f →
          ∀ {Fs : ℝ}, 0 ≤ Fs → (∀ x ∈ Metric.cthickening h V, |f x| ≤ Fs) →
          IsWeakSolutionOn a Q u f (fun _ => 0) →
          ∀ uhom : H1Function V,
            IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V uhom f (fun _ => 0) →
            MemH10 V (fun x => uhom.toFun x - l2a_moll d h η u.toFun x) →
          ∀ {B : ℝ}, (∀ x ∈ V, ‖a16_mollify d h η
              (fun y => matVecMul (a y - s • (1 : Mat d)) (u.grad y)) x‖ ≤ B) →
            eLpNorm (fun x => uhom.toFun x - l2a_moll d h η u.toFun x) ⊤ (volume.restrict V) ≤
              ENNReal.ofReal (Cc * L) *
                (ENNReal.ofReal (B / s) +
                  ENNReal.ofReal (s⁻¹ * (Fs * (Real.sqrt d * h) * d))) := by
  obtain ⟨Cz, hCz, Hcore⟩ := ia_linfty_cz_morrey hd M₁ κ ρ
  refine ⟨Cz, hCz, ?_⟩
  intro Q V r M₂ D z L hQ hQb hU hκ hρ hL hUL hVQ h hh η hη hη0 hη1 hηs rc hrc hmarg a u f s hs
    hF hf hfm Fs hFs hfb hu uhom hhom hw B hB
  obtain ⟨w, hwfun⟩ := hw
  have hV : IsOpen V := hU.1
  have hVb : Bornology.IsBounded V := hQb.subset hVQ
  have hKW : Metric.cthickening h (closure V) ⊆ Q := by
    rw [Metric.cthickening_closure]; exact fun x hx => (hmarg x hx).1
  have hweq := fun φ => ia_weak_eq hQ hQb hV hVQ hh hη hηs hrc hmarg hF hf hfm
    (fun x hx => hfb x (Metric.self_subset_cthickening V hx)) hu uhom hhom w
    (fun x _ => by rw [hwfun]) φ
  have hgl : ∀ i, LocallyIntegrableOn (fun y => u.grad y i) Q volume := fun i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((u.gradMemL2 i).locallyIntegrable (by norm_num))
  have hGl : ∀ i, LocallyIntegrableOn
      (fun y => matVecMul (a y - s • (1 : Mat d)) (u.grad y) i) Q volume := by
    intro i
    have h2 := (hF i).sub ((hgl i).smul s)
    convert h2 using 1
    funext y
    rw [ia_matVecMul_sub]
    simp
  set G : Vec d → Vec d := fun x => a16_mollify d h η
    (fun y => matVecMul (a y - s • (1 : Mat d)) (u.grad y)) x with hG
  have hGc : ∀ i, ∃ c : Vec d → ℝ, Continuous c ∧ ∀ x ∈ V, G x i = c x := by
    intro i
    obtain ⟨c, hc, hce⟩ := ia_moll_cont (Q := Q) hVb hh hη hηs hKW (hGl i)
    exact ⟨c, hc, fun x hx => by rw [hG]; simp only [l2a_mollify_apply]; exact (hce x (subset_closure hx)).symm⟩
  have hF' : MemVectorL2 V (fun x => s⁻¹ • G x) := by
    refine ia_memVectorL2_of_bound hV hVb (B := s⁻¹ * B) (fun i => ?_) (fun x hx => ?_)
    · obtain ⟨c, hc, hce⟩ := hGc i
      exact ⟨fun x => s⁻¹ * c x, continuous_const.mul hc, fun x hx => by
        simp only [Pi.smul_apply, smul_eq_mul, hce x hx]⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      exact mul_le_mul_of_nonneg_left (hB x hx) (inv_nonneg.2 hs.le)
  obtain ⟨cf, hcf, hcfe⟩ := ia_moll_cont (Q := Q) hVb hh hη hηs hKW hf
  obtain ⟨Cb, hCb⟩ := hVb.isCompact_closure.exists_bound_of_continuousOn hcf.continuousOn
  have habs : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    rw [sub_eq_add_neg]; simpa [abs_neg] using abs_add_le x (-y)
  have hh' : MemScalarL2 V (fun x => s⁻¹ * (f x - l2a_moll d h η f x)) := by
    have : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVb.measure_lt_top⟩
    refine MemLp.of_bound (f := fun x => s⁻¹ * (f x - l2a_moll d h η f x)) ?_ (s⁻¹ * (Fs + Cb)) ?_
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine ((Measurable.const_mul (hfm.sub hcf.measurable) s⁻¹).aemeasurable).congr ?_
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      show s⁻¹ * (f x - cf x) = s⁻¹ * (f x - l2a_moll d h η f x)
      rw [hcfe x (subset_closure hx)]
    · filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      have h1 := hfb x (Metric.self_subset_cthickening V hx)
      have h2 := hCb x (subset_closure hx)
      rw [hcfe x (subset_closure hx)] at h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hs)]
      refine mul_le_mul_of_nonneg_left ((habs _ _).trans ?_) (inv_nonneg.2 hs.le)
      rw [Real.norm_eq_abs] at h2
      linarith only [h1, h2]
  have hweak' : IsWeakSolutionOn (fun _ => (1 : Mat d)) V w.toH1Function
      (fun x => s⁻¹ * (f x - l2a_moll d h η f x)) (fun x => s⁻¹ • G x) := by
    intro φ
    have h1 := hweq φ
    have e1 : ∫ x in V, vecDot (matVecMul ((fun _ => (1 : Mat d)) x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x) = ∫ x in V, vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [p14_matVecMul_one]
    have e2 : ∫ x in V, s⁻¹ * (f x - l2a_moll d h η f x) * φ.toH1Function.toFun x =
        s⁻¹ * ∫ x in V, (f x - l2a_moll d h η f x) * φ.toH1Function.toFun x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    have e3 : ∫ x in V, vecDot ((fun x => s⁻¹ • G x) x) (φ.toH1Function.grad x) =
        s⁻¹ * ∫ x in V, vecDot (G x) (φ.toH1Function.grad x) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ia_vecDot_smul_left]
    rw [e1, e2, e3, ← mul_add]
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    linarith only [h1]
  have hpq : (1 : ℝ≥0∞) < ENNReal.ofReal (2 * d) := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hdR])).2 (by linarith only [hdR])
  obtain ⟨hq1, -, -, -, -⟩ := p14g_conj_facts hpq ENNReal.ofReal_ne_top
  have hmain := Hcore hU hκ hρ hL hUL (fun x => s⁻¹ • G x) (fun x => s⁻¹ * (f x - l2a_moll d h η f x))
    w hF' hh' hweak'
  rw [hwfun] at hmain
  have hvt : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have hlp : lpBar V (ENNReal.ofReal (2 * d)) (fun x => s⁻¹ • G x) ≤ ENNReal.ofReal (B / s) := by
    refine ia_lpBar_le_of_bound hvt hF'.aestronglyMeasurable (C := B / s) (fun x hx => ?_)
      hV.measurableSet _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hB x hx) (inv_nonneg.2 hs.le)
  have hwm := ia_wMinusOne_moll hh hη hη0 hη1 hηs hV hVb (f := fun y => s⁻¹ * f y)
    (hfm.const_mul _) (Fs := s⁻¹ * Fs) (mul_nonneg (inv_nonneg.2 hs.le) hFs)
    (fun x hx => by
      rw [abs_mul, abs_of_pos (inv_pos.2 hs)]
      exact mul_le_mul_of_nonneg_left (hfb x hx) (inv_nonneg.2 hs.le)) (p := ENNReal.ofReal (2 * d))
    hq1.le
  have hfun : (fun x => s⁻¹ * f x - l2a_moll d h η (fun y => s⁻¹ * f y) x) =
      fun x => s⁻¹ * (f x - l2a_moll d h η f x) := by
    funext x
    rw [l2a_moll_const_mul]
    ring
  rw [hfun] at hwm
  refine hmain.trans ?_
  refine mul_le_mul' le_rfl (add_le_add hlp ?_)
  refine hwm.trans (le_of_eq ?_)
  congr 1
  ring

end SuperdiffusionCLT.Section7
