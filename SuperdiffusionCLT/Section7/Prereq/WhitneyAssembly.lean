/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyInterpolantC

/-!
# The Whitney interpolant with boundary-adjacent values replaced by neighbours

For the coarse-grained Poincare inequality in a dilated domain `W`, let `Zg` be the finite set of
grid indices `k` whose averaging cube `B_k` lies in `W`.  The interpolant `A` of the cube averages
`c k` is built on `Zg.biUnion wh1_nbhd`, and for an index `k` outside `Zg` the value `c k` is
replaced by `c (wh3_sig Zg k)`, a neighbour in `Zg`.  Then on every cell of `Zg` the interpolant is
a partition-of-unity combination of values that are controlled by the local oscillations on the
cubes of `Zg`, and the oscillations enter with bounded overlap.

## Main results

* `Section7.wh3_sig`: the replacement map.
* `Section7.wh3_interp_sub_A`: `∫_{⋃ cells} (u - A)² ≤ 9^d ∑_{k ∈ Zg} osc_k`.
* `Section7.wh3_interp_grad`: `∫_{⋃ cells} |∇A|² ≤ C d³ 27^d h⁻² ∑_{k ∈ Zg} osc_k`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The open cell of the grid index `k`. -/
def wh3_cell (h : ℝ) (k : Fin d → ℤ) : Set (Vec d) := wh1_box (wh1_pt h k) (h / 2)

open Classical in
/-- The replacement map: the identity on `Zg`, otherwise a chosen neighbour in `Zg`. -/
noncomputable def wh3_sig (Zg : Finset (Fin d → ℤ)) (k : Fin d → ℤ) : Fin d → ℤ :=
  if k ∈ Zg then k else if hk : ∃ a ∈ Zg, a ∈ wh1_nbhd k then Classical.choose hk else k

theorem wh3_sig_of_mem {Zg : Finset (Fin d → ℤ)} {k : Fin d → ℤ} (hk : k ∈ Zg) :
    wh3_sig Zg k = k := by
  unfold wh3_sig
  simp only [hk, ↓reduceIte]

theorem wh3_sig_mem {Zg : Finset (Fin d → ℤ)} {k : Fin d → ℤ}
    (hk : k ∈ Zg.biUnion wh1_nbhd) : wh3_sig Zg k ∈ Zg ∧ wh3_sig Zg k ∈ wh1_nbhd k := by
  by_cases hkZ : k ∈ Zg
  · rw [wh3_sig_of_mem hkZ]
    exact ⟨hkZ, wh1_self_mem_nbhd k⟩
  · obtain ⟨a, ha, hka⟩ := Finset.mem_biUnion.1 hk
    have hex : ∃ a ∈ Zg, a ∈ wh1_nbhd k := ⟨a, ha, wh1_mem_nbhd_symm.1 hka⟩
    have : wh3_sig Zg k = Classical.choose hex := by
      unfold wh3_sig
      simp only [hkZ, ↓reduceIte, hex, ↓reduceDIte]
    rw [this]
    exact Classical.choose_spec hex

/-- Two indices at sup-distance at most one of a common index are at distance at most two. -/
theorem wh3_near_two {k₀ k a : Fin d → ℤ} (hk : k ∈ wh1_nbhd k₀) (ha : a ∈ wh1_nbhd k)
    (i : Fin d) : |(a i : ℝ) - (k₀ i : ℝ)| ≤ 2 := by
  have h1 := wh1_mem_nbhd_iff.1 hk i
  have h2 := wh1_mem_nbhd_iff.1 ha i
  have hz : |a i - k₀ i| ≤ 2 := by rw [abs_le] at h1 h2 ⊢; omega
  have : |((a i - k₀ i : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast hz
  push_cast at this
  exact this

/-- The cell of `k₀` lies in the averaging box of any index at distance at most two. -/
theorem wh3_cell_subset_box {h r : ℝ} (hh : 0 < h) (hr : 5 * h / 2 ≤ r) {k₀ a : Fin d → ℤ}
    (ha : ∀ i, |(a i : ℝ) - (k₀ i : ℝ)| ≤ 2) : wh3_cell h k₀ ⊆ wh1_box (wh1_pt h a) r := by
  intro x hx i
  have h1 := abs_lt.1 (hx i)
  have h1' : -(h / 2) < x i - h * (k₀ i : ℝ) ∧ x i - h * (k₀ i : ℝ) < h / 2 := h1
  have h2 := abs_le.1 (ha i)
  have a1 := mul_le_mul_of_nonneg_left h2.1 hh.le
  have a2 := mul_le_mul_of_nonneg_left h2.2 hh.le
  have e : h * ((a i : ℝ) - (k₀ i : ℝ)) = h * (a i : ℝ) - h * (k₀ i : ℝ) := by ring
  show |x i - h * (a i : ℝ)| < r
  rw [abs_lt]
  constructor <;> linarith only [h1'.1, h1'.2, a1, a2, e, hr]

theorem wh3_volume_cell {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) :
    volume (wh3_cell h k) = ENNReal.ofReal (h ^ d) := by
  unfold wh3_cell
  rw [wh1_volume_box _ (by linarith only [hh])]
  congr 2
  ring

/-- A squared difference of two values at indices at distance at most two, against the local
oscillations. -/
theorem wh3_sq_diff_le {h r : ℝ} (hh : 0 < h) (hr : 5 * h / 2 ≤ r) {k₀ a : Fin d → ℤ}
    (ha : ∀ i, |(a i : ℝ) - (k₀ i : ℝ)| ≤ 2) (c : (Fin d → ℤ) → ℝ) (u : Vec d → ℝ)
    (hu : AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) r))) :
    ENNReal.ofReal ((c a - c k₀) ^ 2) * ENNReal.ofReal (h ^ d) ≤
      2 * (wh1_osc h r u c a + wh1_osc h r u c k₀) := by
  have hS0 : wh3_cell h k₀ ⊆ wh1_box (wh1_pt h k₀) r :=
    wh1_box_mono _ (by linarith only [hh, hr])
  have hSk : wh3_cell h k₀ ⊆ wh1_box (wh1_pt h a) r := wh3_cell_subset_box hh hr ha
  have hmS : MeasurableSet (wh3_cell h k₀) := wh1_box_measurable _ _
  have hu' : AEMeasurable u (volume.restrict (wh3_cell h k₀)) :=
    hu.mono_measure (Measure.restrict_mono hS0 le_rfl)
  have hm1 : AEMeasurable (fun x => ENNReal.ofReal ((u x - c a) ^ 2))
      (volume.restrict (wh3_cell h k₀)) :=
    ((hu'.sub aemeasurable_const).pow_const 2).ennreal_ofReal
  calc ENNReal.ofReal ((c a - c k₀) ^ 2) * ENNReal.ofReal (h ^ d)
      = ∫⁻ _x in wh3_cell h k₀, ENNReal.ofReal ((c a - c k₀) ^ 2) := by
        rw [setLIntegral_const, wh3_volume_cell hh]
    _ ≤ ∫⁻ x in wh3_cell h k₀,
          (2 * ENNReal.ofReal ((u x - c a) ^ 2) + 2 * ENNReal.ofReal ((u x - c k₀) ^ 2)) := by
        refine setLIntegral_mono' hmS fun x _ => ?_
        rw [← wh1_ofReal_two_mul _, ← wh1_ofReal_two_mul _,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have key : 2 * (u x - c a) ^ 2 + 2 * (u x - c k₀) ^ 2 - (c a - c k₀) ^ 2 =
            (2 * u x - c a - c k₀) ^ 2 := by ring
        linarith only [key, sq_nonneg (2 * u x - c a - c k₀)]
    _ = 2 * (∫⁻ x in wh3_cell h k₀, ENNReal.ofReal ((u x - c a) ^ 2)) +
          2 * (∫⁻ x in wh3_cell h k₀, ENNReal.ofReal ((u x - c k₀) ^ 2)) := by
        rw [lintegral_add_left' (hm1.const_mul 2), lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := by
        rw [mul_add]
        unfold wh1_osc
        gcongr

/-- Counting: every index of `Zg` is the image of at most `9^d` pairs `(k₀, k)`. -/
theorem wh3_sum_sig_le (Zg : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → ℝ≥0∞) :
    ∑ k₀ ∈ Zg, ∑ k ∈ wh1_nbhd k₀, g (wh3_sig Zg k) ≤ 9 ^ d * ∑ a ∈ Zg, g a := by
  classical
  refine (wh1_sum_nbhd_le (P := Zg) (fun k => g (wh3_sig Zg k))).trans ?_
  have hmaps : ∀ k ∈ Zg.biUnion wh1_nbhd, wh3_sig Zg k ∈ Zg :=
    fun k hk => (wh3_sig_mem hk).1
  have hfib := Finset.sum_fiberwise_of_maps_to (s := Zg.biUnion wh1_nbhd) (t := Zg)
    (g := wh3_sig Zg) hmaps (fun k => g (wh3_sig Zg k))
  have h2 : ∑ k ∈ Zg.biUnion wh1_nbhd, g (wh3_sig Zg k) ≤ 3 ^ d * ∑ a ∈ Zg, g a := by
    rw [← hfib, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have e : ∑ k ∈ (Zg.biUnion wh1_nbhd).filter (fun k => wh3_sig Zg k = a),
        g (wh3_sig Zg k) =
        ∑ k ∈ (Zg.biUnion wh1_nbhd).filter (fun k => wh3_sig Zg k = a), g a :=
      Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2]
    rw [e, Finset.sum_const, nsmul_eq_mul]
    gcongr
    have : ((Zg.biUnion wh1_nbhd).filter (fun k => wh3_sig Zg k = a)).card ≤
        (wh1_nbhd a).card := by
      refine Finset.card_le_card fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
      have := (wh3_sig_mem hk1).2
      rw [hk2] at this
      exact wh1_mem_nbhd_symm.2 this
    rw [wh1_card_nbhd] at this
    exact_mod_cast this
  calc (3 : ℝ≥0∞) ^ d * ∑ k ∈ Zg.biUnion wh1_nbhd, g (wh3_sig Zg k)
      ≤ 3 ^ d * (3 ^ d * ∑ a ∈ Zg, g a) := by gcongr
    _ = 9 ^ d * ∑ a ∈ Zg, g a := by
        rw [← mul_assoc, ← mul_pow]
        norm_num

/-- The `L²` interpolation estimate over the cells of `Zg`, with the replaced values. -/
theorem wh3_interp_sub_A {h r : ℝ} (hh : 0 < h) (hr : 5 * h / 2 ≤ r)
    (Zg : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (u : Vec d → ℝ)
    (hu : ∀ k₀ ∈ Zg, AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) r))) :
    ∫⁻ x in ⋃ k₀ ∈ Zg, wh3_cell h k₀,
        ENNReal.ofReal ((u x - wh1_A h (Zg.biUnion wh1_nbhd) (fun k => c (wh3_sig Zg k)) x) ^ 2) ≤
      9 ^ d * ∑ a ∈ Zg, wh1_osc h r u c a := by
  refine (wh1_lintegral_biUnion_le Zg _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k₀ hk₀ => ?_) (wh3_sum_sig_le Zg fun a => wh1_osc h r u c a)
  have hZ' : wh1_nbhd k₀ ⊆ Zg.biUnion wh1_nbhd :=
    fun k hk => Finset.mem_biUnion.2 ⟨k₀, hk₀, hk⟩
  have hm : MeasurableSet (wh3_cell h k₀) := wh1_box_measurable _ _
  have hu' : AEMeasurable u (volume.restrict (wh3_cell h k₀)) :=
    (hu k₀ hk₀).mono_measure (Measure.restrict_mono (wh1_box_mono _ (by linarith only [hh, hr]))
      le_rfl)
  calc ∫⁻ x in wh3_cell h k₀,
        ENNReal.ofReal ((u x - wh1_A h (Zg.biUnion wh1_nbhd) (fun k => c (wh3_sig Zg k)) x) ^ 2)
      ≤ ∫⁻ x in wh3_cell h k₀,
          ∑ k ∈ wh1_nbhd k₀, ENNReal.ofReal ((u x - c (wh3_sig Zg k)) ^ 2) := by
        refine setLIntegral_mono' hm fun x hx => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
        exact ENNReal.ofReal_le_ofReal
          (wh1_sq_sub_A_le hh hZ' (fun k => c (wh3_sig Zg k)) u (wh1_cell_le hx))
    _ = ∑ k ∈ wh1_nbhd k₀, ∫⁻ x in wh3_cell h k₀, ENNReal.ofReal ((u x - c (wh3_sig Zg k)) ^ 2) :=
        lintegral_finsetSum' _ fun k _ => ((hu'.sub aemeasurable_const).pow_const 2).ennreal_ofReal
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkZ : k ∈ Zg.biUnion wh1_nbhd := hZ' hk
        have hs := (wh3_sig_mem hkZ).2
        refine lintegral_mono_set (wh3_cell_subset_box hh hr fun i => ?_)
        exact wh3_near_two hk hs i

end SuperdiffusionCLT.Section7
