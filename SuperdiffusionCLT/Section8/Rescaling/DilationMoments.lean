/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.BrownianMotion

/-!
# The time factor and the reparametrization scale of the marginal rescaling

The manuscript's rescaled process is

```
X^ep_t = ep * X_{t / (ep ^ 2 * (8 * cstar * |log ep|) ^ (1/2))} ,
```

so its space dilation is by `ep` and its time factor is `superdiffusiveTimeFactor cstar ep`.
This module records that time factor together with the reparametrization scale used in the
proof of the invariance principle (Section 8).

Main results:

* `norm_apply_le_norm_c0`: a `C₀` function is bounded by its norm.
* `superdiffusiveTimeFactor`: the manuscript's time factor.
* `reparamScale`: the map `delta` to `delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2)`.
* `strictMonoOn_reparamScale`: this map is strictly increasing on `(0, exp (-1/2))`, so the
  reparametrization `delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2` has at most one
  solution there.

Nothing here asserts a scaling limit: `ep` is a fixed parameter throughout.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Rescaling

open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

section Construction

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]

end Construction

section Moments

variable {alpha beta : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [PseudoEMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]
  {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c a : ℝ≥0}

end Moments

section MetricDilation

variable {alpha beta : Type*} [PseudoMetricSpace alpha] [PseudoMetricSpace beta]

end MetricDilation

section C0

variable {alpha beta : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]

/-- A `C₀` function is bounded by its norm. -/
theorem norm_apply_le_norm_c0 (f : C₀(alpha, ℝ)) (x : alpha) : ‖f x‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm x

end C0

section Feller

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]
  {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta}
  {e : alpha ≃ₜ beta} {c : ℝ≥0}

end Feller

section TimeFactor

/-- **The time factor of the marginal rescaling.**  The manuscript rescales the process by
`X^ep_t = ep * X_{t / (ep ^ 2 * (8 * cstar * |log ep|) ^ (1/2))}`, so the clock of `X^ep` runs
faster than that of `X` by this factor. -/
def superdiffusiveTimeFactor (cStar ep : ℝ) : ℝ :=
  (ep ^ 2)⁻¹ * (8 * cStar * |Real.log ep|) ^ (-(1 / 2 : ℝ))

end TimeFactor

section MarginalRescaling

variable {d : ℕ}

end MarginalRescaling

section Reparametrization

/-- Pulling a fourth power out of a square root. -/
private theorem sqrt_pow_four_mul (z A : ℝ) :
    Real.sqrt (z ^ 4 * A) = z ^ 2 * Real.sqrt A := by
  rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

/-- **The reparametrization scale of the invariance principle.**  The proof of
the invariance principle (Section 8) chooses `delta = delta(ep)` by
`delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2`; the left-hand side is this function
of `delta`. -/
def reparamScale (cStar delta : ℝ) : ℝ :=
  delta ^ 2 * (8 * cStar * |Real.log delta|) ^ (1 / 2 : ℝ)

/-- The reparametrization scale as a square root, on the range where `log` is negative. -/
private theorem reparamScale_eq_sqrt {cStar z : ℝ} (hlog : Real.log z < 0) :
    reparamScale cStar z = Real.sqrt (z ^ 4 * (8 * cStar * (-Real.log z))) := by
  rw [reparamScale, abs_of_neg hlog, ← Real.sqrt_eq_rpow, sqrt_pow_four_mul]

/-- The elementary comparison behind the monotonicity of the reparametrization scale: on
`(0, exp (-1/2))` the growth of `z ^ 4` beats the decay of `-log z`.  The proof compares the two
sides at the ratio `r = y / x > 1`, where the claim is `-log y + (r - 1) < (-log y) * r ^ 4`, and
uses only `log r ≤ r - 1` together with `2 * (r - 1) ≤ r ^ 4 - 1`. -/
private theorem pow_mul_neg_log_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : Real.log y < -(1 / 2)) :
    x ^ 4 * (-Real.log x) < y ^ 4 * (-Real.log y) := by
  have hy0 : 0 < y := hx.trans hxy
  have ha : (1 : ℝ) / 2 < -Real.log y := by linarith only [hy]
  set r : ℝ := y / x with hrdef
  have hr : 1 < r := (one_lt_div hx).mpr hxy
  have hr0 : 0 < r := by linarith only [hr]
  have hlogr : Real.log r = Real.log y - Real.log x := Real.log_div hy0.ne' hx.ne'
  have hlogle : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
  have hr2 : 1 < r ^ 2 := one_lt_pow₀ hr (by norm_num)
  have hr3 : 1 < r ^ 3 := one_lt_pow₀ hr (by norm_num)
  have hr4 : 1 < r ^ 4 := one_lt_pow₀ hr (by norm_num)
  have hfac : r ^ 4 - 1 - 2 * (r - 1) = (r - 1) * (r ^ 3 + r ^ 2 + r - 1) := by ring
  have hposfac : 0 < (r - 1) * (r ^ 3 + r ^ 2 + r - 1) :=
    mul_pos (by linarith only [hr]) (by linarith only [hr, hr2, hr3])
  have hcube : 2 * (r - 1) ≤ r ^ 4 - 1 := by linarith only [hfac, hposfac]
  have hhalf : (1 : ℝ) / 2 * (r ^ 4 - 1) < (-Real.log y) * (r ^ 4 - 1) :=
    mul_lt_mul_of_pos_right ha (by linarith only [hr4])
  have hkey : (-Real.log y) + (r - 1) < (-Real.log y) * r ^ 4 := by
    linarith only [hhalf, hcube]
  have hlogx : -Real.log x ≤ (-Real.log y) + (r - 1) := by linarith only [hlogr, hlogle]
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  have hstep : x ^ 4 * (-Real.log x) < x ^ 4 * ((-Real.log y) * r ^ 4) := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlogx hx4.le) ?_
    exact mul_lt_mul_of_pos_left hkey hx4
  have hxr : x ^ 4 * ((-Real.log y) * r ^ 4) = y ^ 4 * (-Real.log y) := by
    rw [hrdef, div_pow]
    field_simp
  linarith only [hstep, hxr]

/-- **The reparametrization scale is strictly increasing on `(0, exp (-1/2))`.**  Consequently
the manuscript's equation `delta ^ 2 * (8 * cstar * |log delta|) ^ (1/2) = ep ^ 2` has at most
one solution `delta` in that interval. -/
theorem strictMonoOn_reparamScale {cStar : ℝ} (hc : 0 < cStar) :
    StrictMonoOn (reparamScale cStar) (Set.Ioo 0 (Real.exp (-(1 / 2 : ℝ)))) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx.1
  have hy0 : 0 < y := hy.1
  have hlogx : Real.log x < -(1 / 2 : ℝ) := by
    have h := Real.log_lt_log hx0 hx.2
    rwa [Real.log_exp] at h
  have hlogy : Real.log y < -(1 / 2 : ℝ) := by
    have h := Real.log_lt_log hy0 hy.2
    rwa [Real.log_exp] at h
  rw [reparamScale_eq_sqrt (by linarith only [hlogx]),
    reparamScale_eq_sqrt (by linarith only [hlogy])]
  refine Real.sqrt_lt_sqrt (mul_nonneg (by positivity)
    (mul_nonneg (by linarith only [hc]) (by linarith only [hlogx]))) ?_
  have hkey := pow_mul_neg_log_lt hx0 hxy hlogy
  have h8 : (0 : ℝ) < 8 * cStar := by linarith only [hc]
  calc x ^ 4 * (8 * cStar * (-Real.log x)) = 8 * cStar * (x ^ 4 * (-Real.log x)) := by ring
    _ < 8 * cStar * (y ^ 4 * (-Real.log y)) := mul_lt_mul_of_pos_left hkey h8
    _ = y ^ 4 * (8 * cStar * (-Real.log y)) := by ring

end Reparametrization

end

end SuperdiffusionCLT.Section8.Rescaling
