/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.Morrey
public import Homogenization.Sobolev.Foundations.AxisCube

@[expose] public section

open MeasureTheory Homogenization

/-!
# Morrey's inequality for `C¹` functions on sub-boxes of an axis cube

For `v ∈ C¹` and `x, y` in an axis cube `U`, the oscillation `|v x - v y|` is at most
`4 (1 - d/p)⁻¹ ‖x - y‖^{1-d/p}` times any bound on the `L^p(U)` norm of `∇v`.  The proof applies
the `C¹` Morrey inequality on an open box of half-width `‖x - y‖` around the midpoint, clipped to `U`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The open box of half-width `‖x - y‖` around the midpoint of `x, y`, clipped to the axis cube. -/
def morreyBox (z : Vec d) (L : ℝ) (x y : Vec d) : Set (Vec d) :=
  Set.pi Set.univ fun j =>
    Set.Ioo (max ((x j + y j) / 2 - ‖x - y‖) (z j)) (min ((x j + y j) / 2 + ‖x - y‖) (z j + L))

theorem norm_sub_lt_of_mem_axisCube {z : Vec d} {L : ℝ} (hL : 0 < L) {x y : Vec d}
    (hx : x ∈ axisCube z L) (hy : y ∈ axisCube z L) : ‖x - y‖ < L := by
  rw [pi_norm_lt_iff hL]
  intro j
  have h1 := hx j (Set.mem_univ j)
  have h2 := hy j (Set.mem_univ j)
  rw [Real.norm_eq_abs, abs_lt]
  simp only [Pi.sub_apply]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

theorem morreyBox_subset {z : Vec d} {L : ℝ} (x y : Vec d) :
    morreyBox z L x y ⊆ axisCube z L := by
  intro a ha j hj
  have h := ha j hj
  exact ⟨lt_of_le_of_lt (le_max_right _ _) h.1, lt_of_lt_of_le h.2 (min_le_right _ _)⟩

theorem mem_morreyBox_left {z : Vec d} {L : ℝ} {x y : Vec d} (hx : x ∈ axisCube z L)
    (hxy : x ≠ y) : x ∈ morreyBox z L x y := by
  have hD : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  intro j _
  have h1 := hx j (Set.mem_univ j)
  have hj : |x j - y j| ≤ ‖x - y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) j
  rw [abs_le] at hj
  constructor
  · refine max_lt ?_ h1.1
    linarith only [hj.1, hj.2, hD]
  · refine lt_min ?_ h1.2
    linarith only [hj.1, hj.2, hD]

theorem mem_morreyBox_right {z : Vec d} {L : ℝ} {x y : Vec d} (hy : y ∈ axisCube z L)
    (hxy : x ≠ y) : y ∈ morreyBox z L x y := by
  have hD : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  intro j _
  have h1 := hy j (Set.mem_univ j)
  have hj : |x j - y j| ≤ ‖x - y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) j
  rw [abs_le] at hj
  constructor
  · refine max_lt ?_ h1.1
    linarith only [hj.1, hj.2, hD]
  · refine lt_min ?_ h1.2
    linarith only [hj.1, hj.2, hD]

theorem norm_sub_le_of_mem_morreyBox {z : Vec d} {L : ℝ} {x y a b : Vec d}
    (ha : a ∈ morreyBox z L x y) (hb : b ∈ morreyBox z L x y) : ‖a - b‖ ≤ 2 * ‖x - y‖ := by
  have hD : 0 ≤ ‖x - y‖ := norm_nonneg _
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  have h1 := ha j (Set.mem_univ j)
  have h2 := hb j (Set.mem_univ j)
  have a1 := lt_of_le_of_lt (le_max_left _ _) h1.1
  have a2 := lt_of_lt_of_le h1.2 (min_le_left _ _)
  have b1 := lt_of_le_of_lt (le_max_left _ _) h2.1
  have b2 := lt_of_lt_of_le h2.2 (min_le_left _ _)
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.sub_apply]
  constructor <;> linarith only [a1, a2, b1, b2]

theorem pow_le_volume_morreyBox {z : Vec d} {L : ℝ} (hL : 0 < L) {x y : Vec d}
    (hx : x ∈ axisCube z L) (hy : y ∈ axisCube z L) (hxy : x ≠ y) :
    ‖x - y‖ ^ d ≤ (volume (morreyBox z L x y)).toReal := by
  have hD : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hDL := norm_sub_lt_of_mem_axisCube hL hx hy
  have hlen : ∀ j, ‖x - y‖ ≤ min ((x j + y j) / 2 + ‖x - y‖) (z j + L) -
      max ((x j + y j) / 2 - ‖x - y‖) (z j) := by
    intro j
    have h1 := hx j (Set.mem_univ j)
    have h2 := hy j (Set.mem_univ j)
    rcases max_cases ((x j + y j) / 2 - ‖x - y‖) (z j) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      rcases min_cases ((x j + y j) / 2 + ‖x - y‖) (z j + L) with ⟨hn, _⟩ | ⟨hn, _⟩ <;>
      rw [hm, hn] <;> linarith only [h1.1, h1.2, h2.1, h2.2, hD, hDL]
  have hab : (fun j => max ((x j + y j) / 2 - ‖x - y‖) (z j)) ≤
      fun j => min ((x j + y j) / 2 + ‖x - y‖) (z j + L) := fun j => by
    have := hlen j
    linarith only [this, hD]
  unfold morreyBox
  rw [Real.volume_pi_Ioo_toReal hab]
  calc ‖x - y‖ ^ d = ∏ _j : Fin d, ‖x - y‖ := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hD.le) (fun j _ => hlen j)

theorem measurableSet_morreyBox (z : Vec d) (L : ℝ) (x y : Vec d) :
    MeasurableSet (morreyBox z L x y) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem convex_morreyBox (z : Vec d) (L : ℝ) (x y : Vec d) : Convex ℝ (morreyBox z L x y) :=
  convex_pi fun _ _ => convex_Ioo _ _

theorem isBounded_morreyBox (z : Vec d) (L : ℝ) (x y : Vec d) :
    Bornology.IsBounded (morreyBox z L x y) :=
  Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

theorem eLpNorm_restrict_eq_integral {g : Vec d → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {K : Set (Vec d)} (hK : MeasurableSet K) (hKb : Bornology.IsBounded K) {p : ℝ} (hp : 0 < p) :
    eLpNorm g (ENNReal.ofReal p) (volume.restrict K) =
      ENNReal.ofReal ((∫ z in K, g z ^ p ∂volume) ^ (1 / p)) := by
  have hcl : IsCompact (closure K) := hKb.isCompact_closure
  have hGint : IntegrableOn (fun y => g y ^ p) K volume :=
    ((hg.rpow_const (fun _ => Or.inr hp.le)).continuousOn.integrableOn_compact hcl).mono_set
      subset_closure
  have hGr0 : 0 ≤ ∫ y in K, g y ^ p ∂volume :=
    setIntegral_nonneg hK fun y _ => Real.rpow_nonneg (hg0 y) _
  have hGeq : ∫⁻ y in K, ‖g y‖ₑ ^ p ∂volume = ENNReal.ofReal (∫ y in K, g y ^ p ∂volume) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (hg0 y) _)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (hg0 y) hp.le, Real.enorm_eq_ofReal (hg0 y)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le, hGeq,
    ENNReal.ofReal_rpow_of_nonneg hGr0 (by positivity)]

/-- **Morrey's inequality for `C¹` functions on an axis cube**, in terms of the `L^p(U)` bound. -/
theorem abs_sub_le_morrey_axisCube {z : Vec d} {L : ℝ} (hL : 0 < L) {v : Vec d → ℝ}
    (hv : ContDiff ℝ 1 v) {p : ℝ} (hp1 : 1 < p) (hd : (d : ℝ) < p) {Er : ℝ} (hEr : 0 ≤ Er)
    (hE : eLpNorm (fun w => ‖fderiv ℝ v w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal Er)
    {x y : Vec d} (hx : x ∈ axisCube z L) (hy : y ∈ axisCube z L) :
    |v x - v y| ≤ 4 * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) * Er := by
  have hp0 : 0 < p := by linarith only [hp1]
  have hdp : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hd
  have hc : 0 < 1 / (1 - (d : ℝ) / p) := one_div_pos.2 (by linarith only [hdp])
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero, norm_zero]
    positivity
  have hD : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set D := ‖x - y‖ with hDdef
  have hvol := pow_le_volume_morreyBox hL hx hy hxy
  have hm : 0 < (volume (morreyBox z L x y)).toReal := lt_of_lt_of_le (by positivity) hvol
  have hK0 : volume (morreyBox z L x y) ≠ 0 := fun h => by simp [h] at hm
  have hmorrey := abs_sub_le_morrey (volume : Measure (Vec d)) hv (measurableSet_morreyBox z L x y)
    (convex_morreyBox z L x y) (isBounded_morreyBox z L x y) hK0 (δ := 2 * D)
    (fun a ha b hb => norm_sub_le_of_mem_morreyBox ha hb) hp1
    (by simpa [Module.finrank_fin_fun] using hd) (mem_morreyBox_left hx hxy)
    (mem_morreyBox_right hy hxy)
  rw [Module.finrank_fin_fun] at hmorrey
  set m := (volume (morreyBox z L x y)).toReal with hmdef
  have hg : Continuous fun w => ‖fderiv ℝ v w‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hI0 : 0 ≤ ∫ w in morreyBox z L x y, ‖fderiv ℝ v w‖ ^ p ∂volume :=
    setIntegral_nonneg (measurableSet_morreyBox z L x y) fun w _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hIle : (∫ w in morreyBox z L x y, ‖fderiv ℝ v w‖ ^ p ∂volume) ^ (1 / p) ≤ Er := by
    have h1 := eLpNorm_restrict_eq_integral (g := fun w => ‖fderiv ℝ v w‖) hg
      (fun _ => norm_nonneg _) (measurableSet_morreyBox z L x y) (isBounded_morreyBox z L x y) hp0
    have h2 : eLpNorm (fun w => ‖fderiv ℝ v w‖) (ENNReal.ofReal p)
        (volume.restrict (morreyBox z L x y)) ≤
        eLpNorm (fun w => ‖fderiv ℝ v w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono (morreyBox_subset x y) le_rfl)
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hEr).1 (h2.trans hE)
  have hpow : (m⁻¹) ^ (1 / p) ≤ (D ^ (-(d : ℝ) / p)) := by
    have h3 : m⁻¹ ≤ (D ^ d)⁻¹ := inv_anti₀ (by positivity) hvol
    calc (m⁻¹) ^ (1 / p) ≤ ((D ^ d)⁻¹) ^ (1 / p) :=
          Real.rpow_le_rpow (by positivity) h3 (by positivity)
      _ = D ^ (-(d : ℝ) / p) := by
          rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hD.le, ← Real.rpow_neg (by positivity)]
          congr 1
          ring
  have hmain : (m⁻¹ * ∫ w in morreyBox z L x y, ‖fderiv ℝ v w‖ ^ p ∂volume) ^ (1 / p) ≤
      D ^ (-(d : ℝ) / p) * Er := by
    rw [Real.mul_rpow (by positivity) hI0]
    exact mul_le_mul hpow hIle (by positivity) (by positivity)
  have hexp : D * D ^ (-(d : ℝ) / p) = D ^ (1 - (d : ℝ) / p) := by
    rw [← Real.rpow_one_add' hD.le (by rw [neg_div]; linarith only [hdp] : (1 : ℝ) + -(d : ℝ) / p ≠ 0)]
    congr 1
    ring
  calc |v x - v y| ≤ _ := hmorrey
    _ ≤ 2 * (1 / (1 - (d : ℝ) / p)) * (2 * D) * (D ^ (-(d : ℝ) / p) * Er) := by gcongr
    _ = 4 * (1 / (1 - (d : ℝ) / p)) * (D * D ^ (-(d : ℝ) / p)) * Er := by ring
    _ = _ := by rw [hexp]

end SuperdiffusionCLT.Section7
