/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.Support.Dirichlet
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.WeakGradientLocality
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-!
# Weak harmonicity against smooth tests

`Support.IsWeaklyHarmonicOn W v` is stated against *every* `H¹₀(W)` competitor,
while every construction that produces harmonicity — in particular the odd
reflection of §4.3 — produces it against *smooth compactly supported* tests.
This file supplies the analytic input of both bridges between the two formulations, which run
through the `H10Function` package's own `L²` approximation data: that smooth tests suffice, and
that a *smooth* function lying in `H¹₀(W)` may be used as a competitor with its **classical**
gradient.  The only analytic input is the `L²` continuity of the tested integral, passing to the
limit through Hölder's inequality at the pair `(2, 2)`.

## Main results

* `tendsto_setIntegral_mul_of_tendsto_eLpNormTwo` — the `L²` continuity of the tested integral.
* `memLp_two_fderiv_apply_restrict` — a coordinate derivative of a smooth compactly supported
  function is in `L²` of the restricted measure.

## References

* CoarseGraining, `Homogenization/Sobolev/WeakDerivatives.lean`
  (`HasWeakPartialDerivOn.ae_eq`, `HasWeakPartialDerivOn.of_contDiff`),
  `Homogenization/Sobolev/H1/Definitions.lean` (the `H10Function` package).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization SuperdiffusionCLT.Section8.Common.Support MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `L²` continuity of the tested integral -/

/-- **`L²` continuity of the tested integral.**  If `f n → g` in `L²(W)` and
`h ∈ L²(W)`, the paired integrals converge.  (This is the `p = 2`
specialization of the graph-closure engine of `OddReflectionGlue`, restated
publicly here because the tested integral of a *gradient* pairing needs it once
per coordinate.) -/
theorem tendsto_setIntegral_mul_of_tendsto_eLpNormTwo {W : Set (Vec d)}
    {h : Vec d → ℝ} {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict W))
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W))
    (htend : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 (volume.restrict W))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in W, f n x * h x ∂volume) atTop
      (nhds (∫ x in W, g x * h x ∂volume)) := by
  set μ : Measure (Vec d) := volume.restrict W with hμ
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := fun n => (hf n).integrable_mul hh
  have hgh_int : Integrable (fun x => g x * h x) μ := hg.integrable_mul hh
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ) = ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) 2 μ * eLpNorm h 2 μ with hB
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (nhds 0) := by
    have hprod : Tendsto B atTop (nhds (0 * eLpNorm h 2 μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [μ] using htend) (Or.inr hh.eLpNorm_ne_top)
        tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    exact hreal
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ, ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have hh' := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := 1)
      (f := fun x => f n x - g x) (g := h)
      (fun x y => x * y) 1 continuous_mul
      ((hf n).sub hg).aestronglyMeasurable hh.aestronglyMeasurable hbound
    simpa [B] using hh'
  calc ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
        have hm : AEStronglyMeasurable (fun x => (f n x - g x) * h x) μ :=
          ((hf n).sub hg).aestronglyMeasurable.mul hh.aestronglyMeasurable
        rw [eLpNorm_one_eq_lintegral_enorm hm]
        simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
        refine ENNReal.toReal_mono ?_ hHolder
        exact ENNReal.mul_ne_top ((hf n).sub hg).eLpNorm_ne_top hh.eLpNorm_ne_top

/-! ## 2. Coordinate splitting of the tested integral -/

/-- A smooth compactly supported function's coordinate derivative is in
`L²(W)` for every `W`. -/
theorem memLp_two_fderiv_apply_restrict {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin d) :
    MemLp (fun y => (fderiv ℝ f y) (basisVec j)) 2 (volume.restrict W) := by
  have hcont : Continuous fun y => (fderiv ℝ f y) (basisVec j) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun y => (fderiv ℝ f y) (basisVec j) := by
    simpa only using hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact (hcont.memLp_of_hasCompactSupport hsupp).restrict W

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
