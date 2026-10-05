/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecay
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationC
public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Lipschitz.InnerBall
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareL
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiB

/-!
# Caccioppoli for the Laplacian on a cube cut by a domain: the energy estimate

Test the equation of `u` on `V` with `η² (u - γ)`, where the localized zero trace of `u - γ` makes
the test function admissible, and bound `∫ η² |∇(u - γ)|²`.  The remaining lemmas
convert between the normalized `L²` norms and integrals, and carry out the real arithmetic of
the block.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_witness_bdry_memLp_cont {V : Set (Vec d)} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) {g : Vec d → ℝ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict V) := by
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hVb.measure_lt_top⟩
  obtain ⟨B, hB⟩ := (hVb.isCompact_closure.exists_bound_of_continuousOn hg.continuousOn)
  refine MemLp.of_bound hg.aestronglyMeasurable B ?_
  rw [ae_restrict_iff' hV.measurableSet]
  exact Filter.Eventually.of_forall fun x hx => hB x (subset_closure hx)

theorem lip_witness_bdry_lpBar_sq {S : Set (Vec d)} (h0 : volume S ≠ 0) (ht : volume S ≠ ⊤)
    {F : Vec d → ℝ} (hF : MemLp F 2 (volume.restrict S)) :
    lpBar S 2 F ^ 2 = ENNReal.ofReal ((volume S).toReal⁻¹ * ∫ x in S, F x ^ 2) := by
  rw [rc_lpBar_two_eq S F hF.aestronglyMeasurable, mul_pow]
  have h1 : ((volume S)⁻¹ ^ (1 / 2 : ℝ)) ^ 2 = ENNReal.ofReal (volume S).toReal⁻¹ := by
    rw [sq]; exact rc_sqrt_inv_mul_self _ h0 ht
  have h2 : eLpNorm F 2 (volume.restrict S) ^ 2 = ENNReal.ofReal (∫ x in S, F x ^ 2) := by
    rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hnn : 0 ≤ ∫ x in S, ‖F x‖ ^ ((2 : ℝ≥0∞).toReal) :=
      integral_nonneg fun x => by positivity
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [ENNReal.toReal_ofNat] at hnn ⊢
    have : ∀ x, ‖F x‖ ^ (2 : ℝ) = F x ^ 2 := fun x => by
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    simp only [this] at hnn ⊢
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]

end SuperdiffusionCLT.Section7
