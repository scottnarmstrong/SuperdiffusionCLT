/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The orthogonal decomposition along a filtration

For a finite measure `μ`, a filtration `m j` of sub-sigma-algebras and square-integrable `f`, `h`,
with `E j f = μ[f | m j]`:

`∫ f h = ∫ E 0 f · E 0 h + ∑_{j<J} ∫ (E (j+1) f − E j f)(E (j+1) h − E j h) + ∫ (f − E J f)(h − E J h)`.

The Cauchy-Schwarz inequality then bounds the sum by the product of the increment norms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The `L²` norm `(∫ f²)^{1/2}`. -/
noncomputable def kc2_l2 (μ : Measure Ω) (f : Ω → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2 ∂μ)

variable [IsFiniteMeasure μ]

theorem kc2_int_condExp_mul {m : MeasurableSpace Ω} (hm : m ≤ m0) {f h : Ω → ℝ}
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    ∫ x, (μ[f | m]) x * h x ∂μ = ∫ x, (μ[f | m]) x * (μ[h | m]) x ∂μ := by
  have hEf : MemLp (μ[f | m]) 2 μ := hf.condExp (by norm_num)
  have hint : Integrable (μ[f | m] * h) μ := hEf.integrable_mul hh
  have := condExp_mul_of_stronglyMeasurable_left (m := m) (μ := μ) stronglyMeasurable_condExp
    hint (hh.integrable (by norm_num))
  calc ∫ x, (μ[f | m]) x * h x ∂μ = ∫ x, (μ[(μ[f | m]) * h | m]) x ∂μ :=
        (integral_condExp hm).symm
    _ = _ := integral_congr_ae this

/-- One generation of the decomposition. -/
theorem kc2_split {m : MeasurableSpace Ω} (hm : m ≤ m0) {f h : Ω → ℝ}
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    ∫ x, f x * h x ∂μ = ∫ x, (μ[f | m]) x * (μ[h | m]) x ∂μ +
      ∫ x, (f x - (μ[f | m]) x) * (h x - (μ[h | m]) x) ∂μ := by
  have hEf : MemLp (μ[f | m]) 2 μ := hf.condExp (by norm_num)
  have hEh : MemLp (μ[h | m]) 2 μ := hh.condExp (by norm_num)
  have e1 := kc2_int_condExp_mul hm hf hh
  have e2 := kc2_int_condExp_mul hm hh hf
  have i1 : Integrable (fun x => f x * h x) μ := hf.integrable_mul hh
  have i2 : Integrable (fun x => f x * (μ[h | m]) x) μ := hf.integrable_mul hEh
  have i3 : Integrable (fun x => (μ[f | m]) x * h x) μ := hEf.integrable_mul hh
  have i4 : Integrable (fun x => (μ[f | m]) x * (μ[h | m]) x) μ := hEf.integrable_mul hEh
  have e : ∀ x, (f x - (μ[f | m]) x) * (h x - (μ[h | m]) x) =
      f x * h x - f x * (μ[h | m]) x - (μ[f | m]) x * h x + (μ[f | m]) x * (μ[h | m]) x :=
    fun x => by ring
  simp_rw [e]
  have j1 : Integrable (fun x => f x * h x - f x * (μ[h | m]) x) μ := i1.sub i2
  have j2 : Integrable
      (fun x => f x * h x - f x * (μ[h | m]) x - (μ[f | m]) x * h x) μ := j1.sub i3
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2]
  have e3 : ∫ x, f x * (μ[h | m]) x ∂μ = ∫ x, (μ[h | m]) x * f x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have e4 : ∫ x, (μ[h | m]) x * (μ[f | m]) x ∂μ = ∫ x, (μ[f | m]) x * (μ[h | m]) x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [e3, e2, e4, e1]
  ring

variable {m : ℕ → MeasurableSpace Ω}

/-- The increment of the conditional expectations between generations `j` and `j+1`. -/
noncomputable def kc2_incr (μ : Measure Ω) (m : ℕ → MeasurableSpace Ω) (f : Ω → ℝ) (j : ℕ) :
    Ω → ℝ := fun x => (μ[f | m (j + 1)]) x - (μ[f | m j]) x

theorem kc2_telescope (hm0 : ∀ j, m j ≤ m0) (hmono : ∀ j, m j ≤ m (j + 1)) {f h : Ω → ℝ}
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) (J : ℕ) :
    ∫ x, f x * h x ∂μ = ∫ x, (μ[f | m 0]) x * (μ[h | m 0]) x ∂μ +
      ∑ j ∈ Finset.range J, ∫ x, kc2_incr μ m f j x * kc2_incr μ m h j x ∂μ +
      ∫ x, (f x - (μ[f | m J]) x) * (h x - (μ[h | m J]) x) ∂μ := by
  induction J with
  | zero => simpa using kc2_split (hm0 0) hf hh
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hEf : MemLp (μ[f | m (J + 1)]) 2 μ := hf.condExp (by norm_num)
    have hEh : MemLp (μ[h | m (J + 1)]) 2 μ := hh.condExp (by norm_num)
    have t1 : μ[μ[f | m (J + 1)] | m J] =ᵐ[μ] μ[f | m J] :=
      condExp_condExp_of_le (hmono J) (hm0 (J + 1))
    have t2 : μ[μ[h | m (J + 1)] | m J] =ᵐ[μ] μ[h | m J] :=
      condExp_condExp_of_le (hmono J) (hm0 (J + 1))
    have a1 : ∫ x, (μ[f | m (J + 1)]) x * (μ[h | m (J + 1)]) x ∂μ =
        ∫ x, (μ[f | m J]) x * (μ[h | m J]) x ∂μ +
          ∫ x, kc2_incr μ m f J x * kc2_incr μ m h J x ∂μ := by
      rw [kc2_split (hm0 J) hEf hEh]
      congr 1
      · refine integral_congr_ae ?_
        filter_upwards [t1, t2] with x e1 e2 using by rw [e1, e2]
      · refine integral_congr_ae ?_
        filter_upwards [t1, t2] with x e1 e2
        simp only [kc2_incr, e1, e2]
    have a2 := kc2_split (hm0 (J + 1)) hf hh
    have b := kc2_split (hm0 J) hf hh
    linarith only [ih, a2, a1, b]
