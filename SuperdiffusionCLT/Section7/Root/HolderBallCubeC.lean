/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Oscillation transfer between sets

Averages, normalized `L²` oscillations and `L^∞` oscillations on measurable subsets of `Vec d`
(Lebesgue measure), and the comparison estimates used when passing from translated cubes to the
Euclidean ball in the large-scale Hölder theorem (the
paragraph "We pass from cubes to balls" of the paper).

For `A ⊆ S` with `vol A > 0`, `u` square integrable on `S`:

* `|(u)_A - (u)_S| ≤ (|S|/|A|)^{1/2} ‖u - (u)_S‖_{L̲²(S)}`,
* `‖u - (u)_A‖_{L̲²(A)} ≤ (|S|/|A|)^{1/2} ‖u - (u)_S‖_{L̲²(S)}`.

## Main results

* `SuperdiffusionCLT.Section7.h1_avg_sub_le`
* `SuperdiffusionCLT.Section7.h1_l2_le`
* `SuperdiffusionCLT.Section7.h1_ae_le_linf`
* `SuperdiffusionCLT.Section7.h1_linf_le_of_ae`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The average of `u` over `S`. -/
noncomputable def h1_avg (S : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (∫ x in S, u x) / (volume S).toReal

/-- The normalized `L²` oscillation of `u` over `S`. -/
noncomputable def h1_l2 (S : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt ((∫ x in S, (u x - h1_avg S u) ^ 2) / (volume S).toReal)

/-- The `L^∞(S)` norm of `u - c`, as a real number. -/
noncomputable def h1_linf (S : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ) : ℝ :=
  (eLpNorm (fun x => u x - c) ⊤ (volume.restrict S)).toReal

theorem h1_linf_le_of_ae {S : Set (Vec d)} {u : Vec d → ℝ} {c M : ℝ}
    (hm : AEStronglyMeasurable u (volume.restrict S)) (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂volume.restrict S, |u x - c| ≤ M) : h1_linf S u c ≤ M := by
  unfold h1_linf
  rw [eLpNorm_exponent_top (show AEStronglyMeasurable (fun x => u x - c) _ from
    hm.sub aestronglyMeasurable_const)]
  refine ENNReal.toReal_le_of_le_ofReal hM ?_
  exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using h)

theorem h1_ae_le_linf {S : Set (Vec d)} {u : Vec d → ℝ} {c : ℝ}
    (hf : MemLp (fun x => u x - c) ⊤ (volume.restrict S)) :
    ∀ᵐ x ∂volume.restrict S, |u x - c| ≤ h1_linf S u c := by
  have h := ae_le_eLpNormEssSup (f := fun x => u x - c) (μ := volume.restrict S)
  have hfin : eLpNormEssSup (fun x => u x - c) (volume.restrict S) ≠ ⊤ := by
    have := hf.eLpNorm_ne_top
    rwa [eLpNorm_exponent_top hf.aestronglyMeasurable] at this
  unfold h1_linf
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
  filter_upwards [h] with x hx
  have := ENNReal.toReal_mono hfin hx
  rwa [toReal_enorm, Real.norm_eq_abs] at this

theorem h1_memLp_two_of_top {S : Set (Vec d)} (hS : volume S ≠ ⊤) {u : Vec d → ℝ}
    (hu : MemLp u ⊤ (volume.restrict S)) : MemLp u 2 (volume.restrict S) := by
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa [Measure.restrict_apply_univ] using hS.lt_top⟩
  exact hu.mono_exponent le_top

/-- Expansion of the quadratic functional. -/
theorem h1_var_expand {A : Set (Vec d)} {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict A))
    (hA : volume A ≠ ⊤) (c : ℝ) :
    ∫ x in A, (u x - c) ^ 2 =
      (∫ x in A, u x ^ 2) - 2 * c * (∫ x in A, u x) + c ^ 2 * (volume A).toReal := by
  have : IsFiniteMeasure (volume.restrict A) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hA.lt_top⟩
  have h1 : Integrable (fun x => u x ^ 2) (volume.restrict A) := hu.integrable_sq
  have h2 : Integrable u (volume.restrict A) := hu.integrable (by norm_num)
  have e : (fun x => (u x - c) ^ 2) = fun x => (u x ^ 2 - (2 * c) * u x) + c ^ 2 := by
    funext x; ring
  have i1 : Integrable (fun x => u x ^ 2 - (2 * c) * u x) (volume.restrict A) :=
    h1.sub (h2.const_mul _)
  rw [e, integral_add i1 (integrable_const _), integral_sub h1 (h2.const_mul _),
    integral_const_mul, setIntegral_const]
  simp only [smul_eq_mul]
  rw [Measure.real]; ring

theorem h1_var_eq {A : Set (Vec d)} {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict A))
    (hA : volume A ≠ ⊤) (hv : 0 < (volume A).toReal) (c : ℝ) :
    ∫ x in A, (u x - c) ^ 2 =
      (∫ x in A, (u x - h1_avg A u) ^ 2) + (volume A).toReal * (h1_avg A u - c) ^ 2 := by
  rw [h1_var_expand hu hA c, h1_var_expand hu hA (h1_avg A u)]
  unfold h1_avg
  field_simp
  ring

theorem h1_integral_sq_mono {A S : Set (Vec d)} (hAS : A ⊆ S) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (hS : volume S ≠ ⊤) (c : ℝ) :
    ∫ x in A, (u x - c) ^ 2 ≤ ∫ x in S, (u x - c) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hS.lt_top⟩
  have hi : Integrable (fun x => (u x - c) ^ 2) (volume.restrict S) := by
    have : MemLp (fun x => u x - c) 2 (volume.restrict S) :=
      hu.sub (memLp_const c)
    exact this.integrable_sq
  exact setIntegral_mono_set hi (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (Filter.Eventually.of_forall hAS)

theorem h1_integral_sq_nonneg (A : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ) :
    0 ≤ ∫ x in A, (u x - c) ^ 2 := integral_nonneg fun _ => sq_nonneg _

/-- `|A| (u_A - c)² ≤ ∫_S (u - c)²`. -/
theorem h1_avg_sq_le {A S : Set (Vec d)} (hAS : A ⊆ S) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (hS : volume S ≠ ⊤) (hv : 0 < (volume A).toReal) (c : ℝ) :
    (volume A).toReal * (h1_avg A u - c) ^ 2 ≤ ∫ x in S, (u x - c) ^ 2 := by
  have hA : volume A ≠ ⊤ := ne_top_of_le_ne_top hS (measure_mono hAS)
  have huA : MemLp u 2 (volume.restrict A) := hu.mono_measure (Measure.restrict_mono hAS le_rfl)
  have := h1_var_eq huA hA hv c
  have h0 := h1_integral_sq_nonneg A u (h1_avg A u)
  have := h1_integral_sq_mono hAS hu hS c
  linarith only [‹∫ x in A, (u x - c) ^ 2 = _›, h0, this]

/-- `∫_A (u - u_A)² ≤ ∫_S (u - c)²`. -/
theorem h1_var_le {A S : Set (Vec d)} (hAS : A ⊆ S) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (hS : volume S ≠ ⊤) (hv : 0 < (volume A).toReal) (c : ℝ) :
    ∫ x in A, (u x - h1_avg A u) ^ 2 ≤ ∫ x in S, (u x - c) ^ 2 := by
  have hA : volume A ≠ ⊤ := ne_top_of_le_ne_top hS (measure_mono hAS)
  have huA : MemLp u 2 (volume.restrict A) := hu.mono_measure (Measure.restrict_mono hAS le_rfl)
  have h1 := h1_var_eq huA hA hv c
  have h2 := h1_integral_sq_mono hAS hu hS c
  have h3 : 0 ≤ (volume A).toReal * (h1_avg A u - c) ^ 2 := by positivity
  linarith only [h1, h2, h3]

theorem h1_l2_sq {S : Set (Vec d)} {u : Vec d → ℝ} (hv : 0 < (volume S).toReal) :
    (volume S).toReal * h1_l2 S u ^ 2 = ∫ x in S, (u x - h1_avg S u) ^ 2 := by
  unfold h1_l2
  rw [Real.sq_sqrt (div_nonneg (h1_integral_sq_nonneg _ _ _) hv.le)]
  field_simp

/-- `|(u)_A - (u)_S| ≤ (|S|/|A|)^{1/2} ‖u - (u)_S‖_{L̲²(S)}`. -/
theorem h1_avg_sub_le {A S : Set (Vec d)} (hAS : A ⊆ S) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (hS : volume S ≠ ⊤) (hv : 0 < (volume A).toReal) :
    |h1_avg A u - h1_avg S u| ≤ Real.sqrt ((volume S).toReal / (volume A).toReal) * h1_l2 S u := by
  have hvS : 0 < (volume S).toReal := lt_of_lt_of_le hv (ENNReal.toReal_mono hS (measure_mono hAS))
  have h := h1_avg_sq_le hAS hu hS hv (h1_avg S u)
  rw [← h1_l2_sq hvS] at h
  have hL : 0 ≤ h1_l2 S u := Real.sqrt_nonneg _
  set a := h1_avg A u - h1_avg S u
  have hsq : a ^ 2 ≤ (Real.sqrt ((volume S).toReal / (volume A).toReal) * h1_l2 S u) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hv]
    linarith only [h, mul_comm (volume A).toReal (a ^ 2)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (by positivity))

/-- `‖u - (u)_A‖_{L̲²(A)} ≤ (|S|/|A|)^{1/2} ‖u - (u)_S‖_{L̲²(S)}`. -/
theorem h1_l2_le {A S : Set (Vec d)} (hAS : A ⊆ S) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict S)) (hS : volume S ≠ ⊤) (hv : 0 < (volume A).toReal) :
    h1_l2 A u ≤ Real.sqrt ((volume S).toReal / (volume A).toReal) * h1_l2 S u := by
  have hvS : 0 < (volume S).toReal := lt_of_lt_of_le hv (ENNReal.toReal_mono hS (measure_mono hAS))
  have h := h1_var_le hAS hu hS hv (h1_avg S u)
  rw [← h1_l2_sq hvS] at h
  have hL : 0 ≤ h1_l2 S u := Real.sqrt_nonneg _
  have e : h1_l2 A u = Real.sqrt ((∫ x in A, (u x - h1_avg A u) ^ 2) / (volume A).toReal) := rfl
  rw [e]
  calc Real.sqrt ((∫ x in A, (u x - h1_avg A u) ^ 2) / (volume A).toReal)
      ≤ Real.sqrt ((volume S).toReal / (volume A).toReal * h1_l2 S u ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hv]
        exact h
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hL]

end SuperdiffusionCLT.Section7
