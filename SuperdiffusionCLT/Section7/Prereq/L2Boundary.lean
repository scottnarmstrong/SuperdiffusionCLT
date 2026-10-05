/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonC
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryLayer

/-!
# Boundary-layer terms of the `L²` comparison: Hölder with the layer measure

Display `e.Dir.new.boundary.g.term`.
A vector field supported in a set `L ⊆ W` has normalized `L^p(W)` norm, for `1 ≤ p ≤ 2`, at most
`(|L| / |W|)^{1/p - 1/2}` times its normalized `L²(W)` norm.  Applied to `(1 - ζ) ∇g` this is the
smallness of the boundary term involving the boundary datum.

## Main results

* `Section7.l2c_lpBar_eq`: the normalized norm as a scalar multiple of the plain norm.
* `Section7.l2c_holder_layer`: Hölder with the layer measure.
* `Section7.l2c_boundary_g_term`: the bound for `(1 - ζ) ∇g`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The normalized `L^p` norm is the plain norm times `|V|^{-1/p}`. -/
theorem l2c_lpBar_eq {E : Type*} [NormedAddCommGroup E] {V : Set (Vec d)} {p : ℝ} (hp : 1 ≤ p)
    {F : Vec d → E}
    (hF : AEStronglyMeasurable F (volume.restrict V)) :
    lpBar V (ENNReal.ofReal p) F =
      ((volume V)⁻¹) ^ (1 / p) * eLpNorm F (ENNReal.ofReal p) (volume.restrict V) := by
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top F _ hF, one_div, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith only [hp])]
  simp only [smul_eq_mul, one_div]

/-- **Hölder with the layer measure.**  A field supported in `L` has `L^p` norm at most
`(|L| / |W|)^{1/p - 1/2}` times its `L²` norm, normalized on `W`, for `1 ≤ p ≤ 2`. -/
theorem l2c_holder_layer {W L : Set (Vec d)} (hWm : MeasurableSet W) (hW0 : volume W ≠ 0)
    (hWt : volume W ≠ ⊤) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {E : Type*} [NormedAddCommGroup E] {F : Vec d → E}
    (hF : AEStronglyMeasurable F (volume.restrict W))
    (hsupp : ∀ x ∈ W, x ∉ L → F x = 0) :
    lpBar W (ENNReal.ofReal p) F ≤
      (volume L / volume W) ^ (1 / p - 1 / 2) * lpBar W 2 F := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, l2c_lpBar_eq hp1 hF, l2c_lpBar_eq (by norm_num) hF]
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hp2
  have hsupport : Function.support F ⊆ L ∪ Wᶜ := fun x hx => by
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hx (hsupp x h.2 h.1)
  have hrestr : ∀ q : ℝ≥0∞, eLpNorm F q ((volume.restrict W).restrict (L ∪ Wᶜ)) =
      eLpNorm F q (volume.restrict W) := fun q => eLpNorm_restrict_eq_of_support_subset hF hsupport
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := ENNReal.ofReal p)
    (q := ENNReal.ofReal 2) (μ := (volume.restrict W).restrict (L ∪ Wᶜ)) hpq (hF.restrict)
  rw [hrestr, hrestr] at h1
  have hmeas : ((volume.restrict W).restrict (L ∪ Wᶜ)) Set.univ ≤ volume L := by
    rw [Measure.restrict_apply_univ, Measure.restrict_apply' hWm]
    refine measure_mono fun x hx => ?_
    rcases hx.1 with h | h
    · exact h
    · exact absurd hx.2 h
  have he : 0 ≤ 1 / p - 1 / 2 := by
    have : 1 / 2 ≤ 1 / p := one_div_le_one_div_of_le (by linarith only [hp1]) hp2
    linarith only [this]
  have hr1 : (ENNReal.ofReal p).toReal = p := by
    rw [ENNReal.toReal_ofReal]
    linarith only [hp1]
  have hr2 : (ENNReal.ofReal 2).toReal = 2 := by
    rw [ENNReal.toReal_ofReal]
    norm_num
  rw [hr1, hr2] at h1
  have h3 : eLpNorm F (ENNReal.ofReal p) (volume.restrict W) ≤
      eLpNorm F (ENNReal.ofReal 2) (volume.restrict W) * volume L ^ (1 / p - 1 / 2) :=
    h1.trans (by gcongr)
  set c : ℝ≥0∞ := (volume W)⁻¹ with hc
  have hc0 : c ≠ 0 := by simp [hc, hWt]
  have hct : c ≠ ⊤ := by simp [hc, hW0]
  have hsplit : c ^ (1 / p) = c ^ (1 / p - 1 / 2) * c ^ (1 / (2 : ℝ)) := by
    rw [← ENNReal.rpow_add _ _ hc0 hct]; congr 1; ring
  have hdiv : volume L / volume W = volume L * c := by rw [hc, div_eq_mul_inv]
  rw [hdiv, ENNReal.mul_rpow_of_nonneg _ _ he, hsplit]
  calc c ^ (1 / p - 1 / 2) * c ^ (1 / (2 : ℝ)) * eLpNorm F (ENNReal.ofReal p) (volume.restrict W)
      ≤ c ^ (1 / p - 1 / 2) * c ^ (1 / (2 : ℝ)) *
        (eLpNorm F (ENNReal.ofReal 2) (volume.restrict W) * volume L ^ (1 / p - 1 / 2)) := by
        gcongr
    _ = _ := by ring

/-- The gradient of an `H¹(V)` function is a.e. strongly measurable. -/
theorem l2c_aesm_grad {V : Set (Vec d)} (g : H1Function V) :
    AEStronglyMeasurable g.grad (volume.restrict V) :=
  (aemeasurable_pi_iff.2 fun i => (g.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable

/-- **The boundary term of the datum** (`e.Dir.new.boundary.g.term`): for a cutoff
`ζ` with values in `[0, 1]`, `‖(1 - ζ) G‖_{L̲^p(W)} ≤ (|{ζ ≠ 1} ∩ W| / |W|)^{1/p - 1/2} ‖G‖_{L̲²(W)}`
for `1 ≤ p ≤ 2`. -/
theorem l2c_boundary_g_term {W : Set (Vec d)} (hWm : MeasurableSet W) (hW0 : volume W ≠ 0)
    (hWt : volume W ≠ ⊤) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {ζ : Vec d → ℝ}
    (hζc : Continuous ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict W)) :
    lpBar W (ENNReal.ofReal p) (fun x => (1 - ζ x) • G x) ≤
      (volume {x | x ∈ W ∧ ζ x ≠ 1} / volume W) ^ (1 / p - 1 / 2) * lpBar W 2 G := by
  have hF : AEStronglyMeasurable (fun x => (1 - ζ x) • G x) (volume.restrict W) :=
    ((continuous_const.sub hζc).aestronglyMeasurable).smul hG
  refine (l2c_holder_layer hWm hW0 hWt hp1 hp2 hF (L := {x | x ∈ W ∧ ζ x ≠ 1})
    (fun x hx hxL => ?_)).trans ?_
  · have : ζ x = 1 := by
      by_contra h
      exact hxL ⟨hx, h⟩
    simp [this]
  · gcongr
    unfold lpBar
    refine eLpNorm_mono (hF.smul_measure _) fun x => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hζ1 x])]
    have := hζ0 x
    have h2 : 1 - ζ x ≤ 1 := by linarith only [this]
    calc (1 - ζ x) * ‖G x‖ ≤ 1 * ‖G x‖ := by gcongr
      _ = ‖G x‖ := one_mul _

end SuperdiffusionCLT.Section7
