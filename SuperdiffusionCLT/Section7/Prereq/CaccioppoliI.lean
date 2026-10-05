/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliH

/-!
# A weak solution with a non-measurable right-hand side is harmonic

If `f` is bounded almost everywhere but not almost-everywhere strongly measurable, then
`∫ f φ = 0` for every test function `φ` for which `fφ` is not integrable, and a positive test
function with `fφ` not integrable exists; adding it to any other test function shows that the
left-hand side of the weak formulation vanishes identically.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca1w_exists_bad_test {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : IsFiniteMeasure (volume.restrict U)) {f : Vec d → ℝ} {F : ℝ}
    (hfF : ∀ᵐ x ∂volume.restrict U, |f x| ≤ F)
    (hf : ¬ AEStronglyMeasurable f (volume.restrict U)) :
    ∃ φ : H10Function U, ¬ AEStronglyMeasurable (fun x => f x * φ.toH1Function.toFun x)
      (volume.restrict U) := by
  by_contra hcon
  push Not at hcon
  refine hf (LocallyIntegrableOn.aestronglyMeasurable fun x hx => ?_)
  obtain ⟨g, hgsub, hgcomp, hgsm, -, hgx⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx)
  have hgsm' : ContDiff ℝ (⊤ : ℕ∞) g := by exact_mod_cast hgsm
  obtain ⟨φ, hφ⟩ := memH10_of_contDiff hU hgsm' hgcomp hgsub
  have hmeas : AEStronglyMeasurable (fun z => f z * g z) (volume.restrict U) := by
    have := hcon φ
    rwa [hφ] at this
  have hgc : Continuous g := hgsm.continuous
  have hV : IsOpen {z | 1 / 2 < g z} := isOpen_lt continuous_const hgc
  have hxV : x ∈ {z | 1 / 2 < g z} := by
    show 1 / 2 < g x
    rw [hgx]; norm_num
  have hVU : {z | 1 / 2 < g z} ⊆ U := by
    intro z hz
    have : g z ≠ 0 := by
      have : (1 : ℝ) / 2 < g z := hz
      linarith only [this]
    exact hgsub (subset_tsupport _ this)
  refine ⟨{z | 1 / 2 < g z}, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), ?_⟩
  have hmeasV : AEStronglyMeasurable f (volume.restrict {z | 1 / 2 < g z}) := by
    have h1 : AEStronglyMeasurable (fun z => f z * g z) (volume.restrict {z | 1 / 2 < g z}) :=
      hmeas.mono_measure (Measure.restrict_mono hVU le_rfl)
    have h2 : AEStronglyMeasurable (fun z => (g z)⁻¹) (volume.restrict {z | 1 / 2 < g z}) :=
      (hgc.measurable.inv).aestronglyMeasurable
    refine (h1.mul h2).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hV.measurableSet]
    refine Filter.Eventually.of_forall fun z hz => ?_
    have : g z ≠ 0 := by
      have : (1 : ℝ) / 2 < g z := hz
      linarith only [this]
    simp only [Pi.mul_apply]
    field_simp
  have hfinV : IsFiniteMeasure (volume.restrict {z | 1 / 2 < g z}) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    have h1 := hfin.measure_univ_lt_top
    rw [Measure.restrict_apply_univ] at h1
    exact lt_of_le_of_lt (measure_mono hVU) h1
  refine Integrable.mono' (integrable_const F) hmeasV ?_
  have hb : ∀ᵐ z ∂volume.restrict {z | 1 / 2 < g z}, |f z| ≤ F :=
    (ae_restrict_of_ae_restrict_of_subset hVU hfF)
  filter_upwards [hb] with z hz
  rwa [Real.norm_eq_abs]

/-- **A weak solution with a non-measurable right-hand side is harmonic.** -/
theorem ca1w_nonmeas_weak {a : CoeffField d} {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : IsFiniteMeasure (volumeMeasureOn U)) (u : H1Function U) {f : Vec d → ℝ} {F : ℝ}
    (hfF : ∀ᵐ x ∂volume.restrict U, |f x| ≤ F)
    (hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.grad x)))
    (hf : ¬ AEStronglyMeasurable f (volume.restrict U))
    (hu : IsWeakSolutionOn a U u f (fun _ => 0)) :
    IsWeakSolutionOn a U u (fun _ => 0) (fun _ => 0) := by
  have hfin' : IsFiniteMeasure (volume.restrict U) := by
    simpa [volumeMeasureOn] using hfin
  obtain ⟨φ0, hφ0⟩ := ca1w_exists_bad_test hU hfin' hfF hf
  have hL0 : ∀ ψ : H10Function U,
      ¬ AEStronglyMeasurable (fun x => f x * ψ.toH1Function.toFun x) (volume.restrict U) →
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (ψ.toH1Function.grad x) = 0 := by
    intro ψ h
    have h1 := hu ψ
    have h2 : ∫ x in U, f x * ψ.toH1Function.toFun x = 0 :=
      integral_undef fun hi => h hi.aestronglyMeasurable
    rw [h2] at h1
    simp only [zero_add, vecDot_zero_left, integral_zero] at h1
    exact h1
  intro ψ
  simp only [zero_mul, integral_zero, vecDot_zero_left, zero_add]
  by_cases hψ : AEStronglyMeasurable (fun x => f x * ψ.toH1Function.toFun x) (volume.restrict U)
  · have hbad : ¬ AEStronglyMeasurable
        (fun x => f x * (φ0 + ψ).toH1Function.toFun x) (volume.restrict U) := by
      intro h
      apply hφ0
      have := h.sub hψ
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      show f x * (φ0.toH1Function.toFun x + ψ.toH1Function.toFun x) - f x * ψ.toH1Function.toFun x =
        f x * φ0.toH1Function.toFun x
      ring
    have h1 := hL0 (φ0 + ψ) hbad
    have h0 := hL0 φ0 hφ0
    have hi0 : IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (φ0.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hflux (MemLp.of_eval fun i => φ0.toH1Function.gradMemL2 i)
    have hi1 : IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x)) (ψ.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hflux (MemLp.of_eval fun i => ψ.toH1Function.gradMemL2 i)
    have hsum : ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) ((φ0 + ψ).toH1Function.grad x) =
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ0.toH1Function.grad x)) +
          ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (ψ.toH1Function.grad x) := by
      rw [← integral_add hi0 hi1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show vecDot (matVecMul (a x) (u.grad x)) (φ0.toH1Function.grad x + ψ.toH1Function.grad x) = _
      rw [vecDot_add_right]
    rw [hsum, h0] at h1
    linarith only [h1]
  · exact hL0 ψ hψ

end SuperdiffusionCLT.Section7
