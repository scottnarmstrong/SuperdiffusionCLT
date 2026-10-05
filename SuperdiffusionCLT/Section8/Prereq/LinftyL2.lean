/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderRootB
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalB

/-!
# `L^∞`-`L²` estimate: the deterministic covering step

This is lemma `l.inproof.Linfty.L2` (interior part of the proof).  A set `V` is covered by
translated cubes `y + □_n`, `y` in a lattice of spacing `s < 3^n`, whose enlargements
`y + □_{n+1}` lie in `W`.  If on every such cube the estimate
`‖u - (u)_Q‖_{L^∞(Q)} ≤ B ‖u - (u)_{Q⁺}‖_{L̲²(Q⁺)}` holds, then
`‖u - (u)_V‖_{L^∞(V)} ≤ 2 (B + 1) √Kr ‖u - (u)_W‖_{L̲²(W)}`, where `|W| ≤ Kr 3^{nd}`.

## Main results

* `SuperdiffusionCLT.Section8.linfL2_core`
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section7

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem linfL2_lattice_countable (s : ℝ) : (h1_lattice d s).Countable := by
  refine (Set.countable_range (fun k : Fin d → ℤ => fun i => s * (k i : ℝ))).mono ?_
  intro y hy
  choose k hk using hy
  exact ⟨k, funext fun i => (hk i).symm⟩

theorem linfL2_cube_mono (y : Vec d) (n : ℕ) : h1_cube y n ⊆ h1_cube y (n + 1) := by
  intro z hz
  rw [h1_mem_cube_iff] at hz ⊢
  intro i
  have h := hz i
  have : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  linarith only [h, this]

/-- The pointwise bound on one cube. -/
theorem linfL2_cube_ae {W : Set (Vec d)} (hW : volume W ≠ ⊤) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict W)) {y : Vec d} {n : ℕ} {B Kr : ℝ} (hB : 0 ≤ B)
    (hKr : (volume W).toReal ≤ Kr * ((3 : ℝ) ^ n) ^ d)
    (hQW : h1_cube y (n + 1) ⊆ W)
    (hmem : MemLp u ⊤ (volume.restrict (h1_cube y n)))
    (hbd : h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤ B * h1_l2 (h1_cube y (n + 1)) u) :
    ∀ᵐ x ∂volume.restrict (h1_cube y n),
      |u x - h1_avg W u| ≤ (B + 1) * Real.sqrt Kr * h1_l2 W u := by
  have hQ1 : h1_cube y n ⊆ W := (linfL2_cube_mono y n).trans hQW
  have hv := h1_vol_cube_pos y n
  have hv1 := h1_vol_cube_pos y (n + 1)
  have h1 := h1_ae_le_linf (h1_memLp_sub (subset_refl _) (h1_vol_cube_ne_top y n) hmem
    (h1_avg (h1_cube y n) u))
  have h2 := h1_avg_sub_le hQ1 hu hW hv
  have hl : 0 ≤ h1_l2 W u := Real.sqrt_nonneg _
  have hl1 := h1_l2_le hQW hu hW hv1
  have hr0 : 0 ≤ Real.sqrt Kr := Real.sqrt_nonneg _
  have hKr0 : 0 ≤ Kr := by
    by_contra hneg
    push Not at hneg
    have : Kr * ((3 : ℝ) ^ n) ^ d < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    have := ENNReal.toReal_nonneg (a := volume W)
    linarith only [‹Kr * ((3 : ℝ) ^ n) ^ d < 0›, hKr, this]
  have hr1 : (volume W).toReal / (volume (h1_cube y n)).toReal ≤ Kr := by
    rw [div_le_iff₀ hv, h1_volT_cube]; exact hKr
  have hmono : (volume (h1_cube y n)).toReal ≤ (volume (h1_cube y (n + 1))).toReal :=
    ENNReal.toReal_mono (h1_vol_cube_ne_top y (n + 1)) (measure_mono (linfL2_cube_mono y n))
  have hr2 : (volume W).toReal / (volume (h1_cube y (n + 1))).toReal ≤ Kr :=
    le_trans (div_le_div_of_nonneg_left ENNReal.toReal_nonneg hv hmono) hr1
  have hs1 : Real.sqrt ((volume W).toReal / (volume (h1_cube y n)).toReal) ≤ Real.sqrt Kr :=
    Real.sqrt_le_sqrt hr1
  have hs2 : Real.sqrt ((volume W).toReal / (volume (h1_cube y (n + 1))).toReal) ≤
      Real.sqrt Kr := Real.sqrt_le_sqrt hr2
  have hb1 : h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤ B * (Real.sqrt Kr * h1_l2 W u) :=
    hbd.trans (mul_le_mul_of_nonneg_left (hl1.trans (mul_le_mul_of_nonneg_right hs2 hl)) hB)
  have hb2 : Real.sqrt ((volume W).toReal / (volume (h1_cube y n)).toReal) * h1_l2 W u ≤
      Real.sqrt Kr * h1_l2 W u := mul_le_mul_of_nonneg_right hs1 hl
  filter_upwards [h1] with x hx
  have : |u x - h1_avg W u| ≤ |u x - h1_avg (h1_cube y n) u| +
      |h1_avg (h1_cube y n) u - h1_avg W u| := by
    have := abs_add_le (u x - h1_avg (h1_cube y n) u) (h1_avg (h1_cube y n) u - h1_avg W u)
    simpa using this
  have hprod : 0 ≤ Real.sqrt Kr * h1_l2 W u := mul_nonneg hr0 hl
  nlinarith only [this, hx, h2, hb1, hb2, hprod]

/-- **The covering step.** -/
theorem linfL2_core {W V : Set (Vec d)} (hVW : V ⊆ W)
    (hW : volume W ≠ ⊤) {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict W))
    {n : ℕ} {s B Kr : ℝ} (hs : 0 < s) (hsn : s < (3 : ℝ) ^ n) (hB : 0 ≤ B)
    (hKr : (volume W).toReal ≤ Kr * ((3 : ℝ) ^ n) ^ d)
    (hball : ∀ x ∈ V, ∀ z : Vec d,
      (∀ i, |z i - x i| < (3 : ℝ) ^ (n + 1) / 2 + s / 2) → z ∈ W)
    (H : ∀ y ∈ h1_lattice d s, (∃ x ∈ V, ∀ i, |x i - y i| ≤ s / 2) →
      MemLp u ⊤ (volume.restrict (h1_cube y n)) ∧
        h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
          B * h1_l2 (h1_cube y (n + 1)) u) :
    MemLp u ⊤ (volume.restrict V) ∧
      h1_linf V u (h1_avg V u) ≤ 2 * ((B + 1) * Real.sqrt Kr * h1_l2 W u) := by
  set M : ℝ := (B + 1) * Real.sqrt Kr * h1_l2 W u with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ h1_l2 W u := Real.sqrt_nonneg _
    positivity
  have hVfin : volume V ≠ ⊤ := ne_top_of_le_ne_top hW (measure_mono hVW)
  have hVrfin : IsFiniteMeasure (volume.restrict V) := h1_finite_restrict hVfin
  by_cases hv : 0 < (volume V).toReal
  · set T : Set (Vec d) := {y | y ∈ h1_lattice d s ∧ ∃ x ∈ V, ∀ i, |x i - y i| ≤ s / 2} with hT
    have hTc : T.Countable := (linfL2_lattice_countable s).mono fun y hy => hy.1
    have hcov : V ⊆ ⋃ y ∈ T, h1_cube y n := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := h1_exists_lattice hs x
      refine Set.mem_biUnion (x := y) ⟨hy, x, hx, hxy⟩ ?_
      rw [h1_mem_cube_iff]
      intro i
      have := hxy i
      linarith only [this, hsn]
    have hae : ∀ᵐ x ∂volume.restrict V, |u x - h1_avg W u| ≤ M := by
      have h1 : ∀ᵐ x ∂volume.restrict (⋃ y ∈ T, h1_cube y n), |u x - h1_avg W u| ≤ M := by
        rw [ae_restrict_biUnion_iff _ hTc]
        intro y hy
        obtain ⟨hmem, hbd⟩ := H y hy.1 hy.2
        have hQW : h1_cube y (n + 1) ⊆ W := by
          intro z hz
          obtain ⟨x, hx, hxy⟩ := hy.2
          refine hball x hx z fun i => ?_
          have h2 := (h1_mem_cube_iff.1 hz) i
          have h3 := hxy i
          have : |z i - x i| ≤ |z i - y i| + |y i - x i| := by
            have := abs_add_le (z i - y i) (y i - x i)
            simpa using this
          rw [abs_sub_comm (y i) (x i)] at this
          linarith only [this, h2, h3]
        exact linfL2_cube_ae hW hu hB hKr hQW hmem hbd
      exact ae_restrict_of_ae_restrict_of_subset hcov h1
    have hmem : MemLp u ⊤ (volume.restrict V) := by
      refine memLp_top_of_bound (hu.aestronglyMeasurable.mono_measure (Measure.restrict_mono hVW le_rfl))
        (M + |h1_avg W u|) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs]
      have := abs_add_le (u x - h1_avg W u) (h1_avg W u)
      simp only [sub_add_cancel] at this
      linarith only [this, hx]
    exact ⟨hmem, h1_osc_two hVfin hv hmem hM0 hae⟩
  · have h0 : volume V = 0 := by
      have := ENNReal.toReal_nonneg (a := volume V)
      have h00 : (volume V).toReal = 0 := le_antisymm (not_lt.1 hv) this
      exact (ENNReal.toReal_eq_zero_iff _).1 h00 |>.resolve_right hVfin
    have hr : (volume.restrict V : Measure (Vec d)) = 0 := Measure.restrict_eq_zero.2 h0
    refine ⟨?_, ?_⟩
    · rw [hr]; simp
    · unfold h1_linf
      rw [hr]
      simp [hM0]

end SuperdiffusionCLT.Section8
