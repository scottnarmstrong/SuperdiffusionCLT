/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryStepB

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_bdry_step_vecDot_sub_left (a b v : Vec d) :
    vecDot (a - b) v = vecDot a v - vecDot b v := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

theorem lip_bdry_step_vecDot_add_left (a b v : Vec d) :
    vecDot (a + b) v = vecDot a v + vecDot b v := by
  simp [vecDot, add_mul, Finset.sum_add_distrib]

theorem lip_bdry_step_memLp_aff {S : Set (Vec d)} (hSm : MeasurableSet S) (hSt : volume S ≠ ⊤)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict S)) {x₀ : Vec d} {R : ℝ}
    (hR : ∀ y ∈ S, ‖y - x₀‖ ≤ R) (c : ℝ) (p : Vec d) :
    MemLp (fun x => u x - c - vecDot p (x - x₀)) 2 (volume.restrict S) := by
  have hfin : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSt.lt_top⟩
  have hc : Continuous (fun x : Vec d => c + vecDot p (x - x₀)) :=
    continuous_const.add (lip_bdry_approx_continuous_aff p x₀)
  have hA : MemLp (fun x : Vec d => c + vecDot p (x - x₀)) 2 (volume.restrict S) :=
    MemLp.of_bound hc.aestronglyMeasurable (|c| + (d : ℝ) * ‖p‖ * R)
      ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]
        have h1 := lip_bdry_approx_abs_vecDot_le p (x - x₀)
        have h4 : (d : ℝ) * ‖p‖ * ‖x - x₀‖ ≤ (d : ℝ) * ‖p‖ * R :=
          mul_le_mul_of_nonneg_left (hR x hx) (by positivity)
        calc |c + vecDot p (x - x₀)| ≤ |c| + |vecDot p (x - x₀)| := abs_add_le _ _
          _ ≤ _ := by linarith only [h1, h4]))
  have e : (fun x : Vec d => u x - c - vecDot p (x - x₀)) =
      fun x => u x - (c + vecDot p (x - x₀)) := funext fun x => by ring
  rw [e]
  exact hu.sub hA

theorem lip_bdry_step_rpow_half (j : ℕ) :
    ((((3 : ℝ)⁻¹) ^ j) ^ (1 / 2 : ℝ)) = ((Real.sqrt 3)⁻¹) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast, Real.inv_rpow (by norm_num),
    ← Real.sqrt_eq_rpow]

theorem lip_bdry_step_lipL2_comm (S : Set (Vec d)) (a b : Vec d → ℝ) :
    lipL2 S (fun x => a x - b x) = lipL2 S (fun x => b x - a x) := by
  unfold lipL2 lpBar
  rw [show (fun x => a x - b x) = a - b from rfl, show (fun x => b x - a x) = b - a from rfl,
    eLpNorm_sub_comm]

theorem lip_bdry_step_taylor_R {gt : Vec d → ℝ} (hgt : ContDiff ℝ 2 gt) {M R : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ M) (x₀ y : Vec d) (hy : ‖y - x₀‖ ≤ R) :
    |gt y - gt x₀ - vecDot (fun i => fderiv ℝ gt x₀ (basisVec i)) (y - x₀)| ≤ M * R * R := by
  have h := lip_bdry_step_taylor hgt hM x₀ y
  have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ gt) x₀)).trans (hM x₀)
  have hn := norm_nonneg (y - x₀)
  refine h.trans ?_
  have h1 : ‖y - x₀‖ * ‖y - x₀‖ ≤ R * R := mul_le_mul hy hy hn (hn.trans hy)
  calc M * ‖y - x₀‖ * ‖y - x₀‖ = M * (‖y - x₀‖ * ‖y - x₀‖) := by ring
    _ ≤ M * (R * R) := mul_le_mul_of_nonneg_left h1 hM0
    _ = M * R * R := by ring

theorem lip_bdry_step_L2_add_bdd {D : Set (Vec d)} (hD0 : volume D ≠ 0)
    (hDt : volume D ≠ ⊤) {f h : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict D))
    (hhm : AEStronglyMeasurable h (volume.restrict D)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict D, |h x| ≤ B) :
    lipL2 D (fun x => f x + h x) ≤ lipL2 D f + B := by
  have hfin : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hDt.lt_top⟩
  have hhL : MemLp h 2 (volume.restrict D) :=
    MemLp.of_bound hhm B (hb.mono fun x hx => by rwa [Real.norm_eq_abs])
  exact (lipL2_add_le hD0 hDt hf hhL).trans
    (add_le_add le_rfl (lipL2_le_of_ae_abs_le hB hD0 hDt hb))

/-- The flatness on the small patch against the flatness of `u - ub` on `V` and the pointwise
bound of the remaining affine and Taylor terms. -/
theorem lip_bdry_step_Dpart {D V : Set (Vec d)} {u ub gt : Vec d → ℝ} {x₀ : Vec d} {c₀ : ℝ}
    {b G : Vec d} {j : ℕ} {κ' B1 T Cc : ℝ} (hDV : D ⊆ V) (hDm : MeasurableSet D)
    (hD0 : volume D ≠ 0) (hVt : volume V ≠ ⊤) (hvol : (volume V).toReal ≤ κ' * (volume D).toReal)
    (humb : MemLp (fun x => u x - ub x) 2 (volume.restrict V))
    (hmeas : AEStronglyMeasurable (fun x => ub x - gt x - vecDot b (x - x₀)) (volume.restrict D))
    (hgtc : Continuous gt) (hB1 : 0 ≤ B1) (hT : 0 ≤ T) (hCc : 0 ≤ Cc)
    (hb1 : ∀ᵐ x ∂volume.restrict D, |ub x - gt x - vecDot b (x - x₀)| ≤ B1)
    (hTa : ∀ x ∈ D, |gt x - gt x₀ - vecDot G (x - x₀)| ≤ T) (hc : |gt x₀ - c₀| ≤ Cc) :
    lipPin D j x₀ c₀ u (b + G) ≤
      ((3 : ℝ)⁻¹) ^ j * (Real.sqrt κ' * lipL2 V (fun x => u x - ub x) + (B1 + T + Cc)) := by
  have hDt : volume D ≠ ⊤ := ne_top_of_le_ne_top hVt (measure_mono hDV)
  set h : Vec d → ℝ := fun x => (ub x - gt x - vecDot b (x - x₀)) +
    ((gt x - gt x₀ - vecDot G (x - x₀)) + (gt x₀ - c₀)) with hh
  have hcT : Continuous (fun x : Vec d => gt x - gt x₀ - vecDot G (x - x₀)) :=
    (hgtc.sub continuous_const).sub (lip_bdry_approx_continuous_aff G x₀)
  have hid : (fun x => u x - c₀ - vecDot (b + G) (x - x₀)) =
      fun x => (u x - ub x) + h x := by
    funext x
    simp only [hh, lip_bdry_step_vecDot_add_left]
    ring
  have hr2 : ∀ᵐ x ∂volume.restrict D, |(gt x - gt x₀ - vecDot G (x - x₀)) + (gt x₀ - c₀)| ≤ T + Cc := by
    filter_upwards [ae_restrict_mem hDm] with x hx
    exact (abs_add_le _ _).trans (add_le_add (hTa x hx) hc)
  have hm2 : AEStronglyMeasurable (fun x => (gt x - gt x₀ - vecDot G (x - x₀)) + (gt x₀ - c₀))
      (volume.restrict D) := (hcT.add continuous_const).aestronglyMeasurable
  have humbD : MemLp (fun x => u x - ub x) 2 (volume.restrict D) :=
    humb.mono_measure (Measure.restrict_mono hDV le_rfl)
  have e1 : lipL2 D (fun x => u x - c₀ - vecDot (b + G) (x - x₀)) ≤
      lipL2 D (fun x => u x - ub x) + (B1 + T + Cc) := by
    rw [hid]
    have step1 := lip_bdry_step_L2_add_bdd hD0 hDt humbD
      (h := h) (hmeas.add hm2) (B := B1 + (T + Cc)) (by positivity) (by
        filter_upwards [hb1, hr2] with x h1 h2
        exact (abs_add_le _ _).trans (add_le_add h1 h2))
    linarith only [step1]
  have e2 : lipL2 D (fun x => u x - ub x) ≤ Real.sqrt κ' * lipL2 V (fun x => u x - ub x) :=
    lip_int_harm_of_l2_lipL2_mono_set hDV hD0 hVt hvol humb
  unfold lipPin
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith only [e1, e2]

end SuperdiffusionCLT.Section7
