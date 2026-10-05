/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2Interior

/-!
# The mesoscale grid of cubes

The cells `z + □_n`, `z ∈ 3^n ℤ^d`,
tile space; the cells `z + □_{n+1}` have overlap `3^d`; every point with `‖y - x‖ ≤ 2·3^n` in `W`
lies in a cell `z + □_n` with `z + □_{n+1} ⊆ W`.

* `Section7.l2b_cell`, `Section7.l2b_pt`: the cell `z + □_m` and the grid point `3^n k`.
* `Section7.l2b_cell_disjoint`, `Section7.l2b_exists_cell`, `Section7.l2b_overlap`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The cell `z + □_m` (half open, side `3^m`, centred at `z`). -/
def l2b_cell (z : Vec d) (m : ℕ) : Set (Vec d) :=
  translateSet z (cubeSet (originCube d (m : ℤ)))

/-- The grid point `3^n k`. -/
noncomputable def l2b_pt (n : ℕ) (k : Fin d → ℤ) : Vec d := fun i => (3 : ℝ) ^ n * (k i : ℝ)

theorem l2b_mem_cell {z x : Vec d} {m : ℕ} :
    x ∈ l2b_cell z m ↔ ∀ i, -(1 / 2 * (3 : ℝ) ^ m) ≤ x i - z i ∧ x i - z i < 1 / 2 * (3 : ℝ) ^ m := by
  unfold l2b_cell
  rw [mem_translateSet_iff_sub_mem, mem_cubeSet_originCube_iff]
  simp only [zpow_natCast, Pi.sub_apply]
  refine forall_congr' fun i => ?_
  rw [neg_mul]

theorem l2b_cell_measurable (z : Vec d) (m : ℕ) : MeasurableSet (l2b_cell z m) := by
  have : l2b_cell z m = (fun x => x - z) ⁻¹' cubeSet (originCube d (m : ℤ)) := by
    ext x; unfold l2b_cell; rw [mem_translateSet_iff_sub_mem]; rfl
  rw [this]
  exact (measurableSet_cubeSet _).preimage (measurable_id.sub_const z)

theorem l2b_volume_cell (z : Vec d) (m : ℕ) :
    volume (l2b_cell z m) = ENNReal.ofReal (((3 : ℝ) ^ (m : ℤ)) ^ d) := by
  unfold l2b_cell
  rw [volume_translateSet_eq, ← ENNReal.ofReal_toReal (volume_cubeSet_lt_top _).ne,
    volume_cubeSet_toReal]
  rfl

theorem l2b_cell_disjoint (n : ℕ) {k k' : Fin d → ℤ} (hk : k ≠ k') :
    Disjoint (l2b_cell (l2b_pt n k) n) (l2b_cell (l2b_pt n k') n) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [l2b_mem_cell] at hx hx'
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ k' i := by
    by_contra h; push Not at h; exact hk (funext h)
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have a1 := hx i
  have a2 := hx' i
  simp only [l2b_pt] at a1 a2
  rcases lt_or_gt_of_ne hi with h | h
  · have h1 : (k i : ℝ) + 1 ≤ k' i := by exact_mod_cast Int.add_one_le_iff.2 h
    have : (3 : ℝ) ^ n * ((k i : ℝ) + 1) ≤ 3 ^ n * k' i := mul_le_mul_of_nonneg_left h1 h3.le
    linarith only [a1.2, a2.1, this]
  · have h1 : (k' i : ℝ) + 1 ≤ k i := by exact_mod_cast Int.add_one_le_iff.2 h
    have : (3 : ℝ) ^ n * ((k' i : ℝ) + 1) ≤ 3 ^ n * k i := mul_le_mul_of_nonneg_left h1 h3.le
    linarith only [a1.1, a2.2, this]

/-- The index of the cell containing `x`. -/
noncomputable def l2b_idx (n : ℕ) (x : Vec d) : Fin d → ℤ := fun i => ⌊x i / (3 : ℝ) ^ n + 1 / 2⌋

theorem l2b_mem_cell_idx (n : ℕ) (x : Vec d) : x ∈ l2b_cell (l2b_pt n (l2b_idx n x)) n := by
  rw [l2b_mem_cell]
  intro i
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have f1 := Int.floor_le (x i / (3 : ℝ) ^ n + 1 / 2)
  have f2 := Int.lt_floor_add_one (x i / (3 : ℝ) ^ n + 1 / 2)
  simp only [l2b_pt, l2b_idx]
  have e1 : (3 : ℝ) ^ n * (x i / 3 ^ n) = x i := by field_simp
  have g1 := mul_le_mul_of_nonneg_left f1 h3.le
  have g2 := mul_lt_mul_of_pos_left f2 h3
  constructor <;> nlinarith only [g1, g2, e1]

/-- The offsets of the `3^d` cells of scale `n` inside a cell of scale `n + 1`. -/
def l2b_offsets (d : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)

theorem l2b_card_offsets (d : ℕ) : (l2b_offsets d).card = 3 ^ d := by
  unfold l2b_offsets
  rw [Fintype.card_piFinset]
  simp

theorem l2b_cell_sub_cell (n : ℕ) (k : Fin d → ℤ) {j : Fin d → ℤ} (hj : j ∈ l2b_offsets d) :
    l2b_cell (l2b_pt n (k + j)) n ⊆ l2b_cell (l2b_pt n k) (n + 1) := by
  intro x hx
  rw [l2b_mem_cell] at hx ⊢
  intro i
  have hji : j i ∈ ({-1, 0, 1} : Finset ℤ) := by
    unfold l2b_offsets at hj; exact Fintype.mem_piFinset.1 hj i
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have h1 : (-1 : ℝ) ≤ j i ∧ (j i : ℝ) ≤ 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hji
    rcases hji with h | h | h <;> rw [h] <;> norm_num
  have a := hx i
  simp only [l2b_pt, Pi.add_apply, Int.cast_add] at a
  simp only [l2b_pt]
  have e : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
  have g1 := mul_le_mul_of_nonneg_left h1.1 h3.le
  have g2 := mul_le_mul_of_nonneg_left h1.2 h3.le
  rw [e]
  constructor <;> nlinarith only [a.1, a.2, g1, g2]

theorem l2b_cell_succ_subset (n : ℕ) (k : Fin d → ℤ) :
    l2b_cell (l2b_pt n k) (n + 1) ⊆ ⋃ j ∈ l2b_offsets d, l2b_cell (l2b_pt n (k + j)) n := by
  intro x hx
  have hx' := (l2b_mem_cell.1 hx)
  simp only [Set.mem_iUnion]
  refine ⟨l2b_idx n x - k, ?_, ?_⟩
  · unfold l2b_offsets
    refine Fintype.mem_piFinset.2 fun i => ?_
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    have a := hx' i
    simp only [l2b_pt] at a
    have e : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
    rw [e] at a
    have t1 : ((k i : ℝ) - 1) ≤ x i / 3 ^ n + 1 / 2 := by
      rw [← sub_nonneg]
      have : x i / 3 ^ n + 1 / 2 - ((k i : ℝ) - 1) = (x i - 3 ^ n * k i + 3 / 2 * 3 ^ n) / 3 ^ n := by
        field_simp; ring
      rw [this]
      exact div_nonneg (by linarith only [a.1]) h3.le
    have t2 : x i / 3 ^ n + 1 / 2 < (k i : ℝ) + 2 := by
      rw [← sub_pos]
      have : (k i : ℝ) + 2 - (x i / 3 ^ n + 1 / 2) =
          (3 / 2 * 3 ^ n - (x i - 3 ^ n * k i)) / 3 ^ n := by
        field_simp; ring
      rw [this]
      exact div_pos (by linarith only [a.2]) h3
    have f1 : k i - 1 ≤ ⌊x i / (3 : ℝ) ^ n + 1 / 2⌋ := Int.le_floor.2 (by exact_mod_cast t1)
    have f2 : ⌊x i / (3 : ℝ) ^ n + 1 / 2⌋ < k i + 2 := Int.floor_lt.2 (by exact_mod_cast t2)
    simp only [l2b_idx, Pi.sub_apply, Finset.mem_insert, Finset.mem_singleton]
    omega
  · have := l2b_mem_cell_idx n x
    have e : k + (l2b_idx n x - k) = l2b_idx n x := by abel
    rw [e]; exact this

/-- **Overlap of the enlarged cells** ("finite overlap"): the cells `z + □_{n+1}` with
`z ∈ 3^n ℤ^d` lying in `W` have total overlap at most `3^d`. -/
theorem l2b_overlap (n : ℕ) (W : Set (Vec d)) (h : Vec d → ℝ≥0∞) :
    ∑' k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W},
        ∫⁻ x in l2b_cell (l2b_pt n k.1) (n + 1), h x ≤
      (3 : ℝ≥0∞) ^ d * ∫⁻ x in W, h x := by
  have hdisj : ∀ j : Fin d → ℤ, Pairwise (Function.onFun Disjoint
      fun k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W} =>
        l2b_cell (l2b_pt n (k.1 + j)) n) := by
    intro j k k' hkk'
    refine l2b_cell_disjoint n fun h => hkk' (Subtype.ext (add_right_cancel h))
  have hstep : ∀ k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W},
      ∫⁻ x in l2b_cell (l2b_pt n k.1) (n + 1), h x ≤
        ∑ j ∈ l2b_offsets d, ∫⁻ x in l2b_cell (l2b_pt n (k.1 + j)) n, h x := by
    intro k
    calc ∫⁻ x in l2b_cell (l2b_pt n k.1) (n + 1), h x
        ≤ ∫⁻ x in ⋃ j ∈ l2b_offsets d, l2b_cell (l2b_pt n (k.1 + j)) n, h x :=
          lintegral_mono_set (l2b_cell_succ_subset n k.1)
      _ = _ := by
          refine lintegral_biUnion_finset ?_ (fun j _ => l2b_cell_measurable _ _) _
          intro j _ j' _ hjj'
          exact l2b_cell_disjoint n fun h => hjj' (add_left_cancel h)
  calc ∑' k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W},
        ∫⁻ x in l2b_cell (l2b_pt n k.1) (n + 1), h x
      ≤ ∑' k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W},
        ∑ j ∈ l2b_offsets d, ∫⁻ x in l2b_cell (l2b_pt n (k.1 + j)) n, h x :=
        ENNReal.tsum_le_tsum hstep
    _ = ∑ j ∈ l2b_offsets d, ∑' k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W},
        ∫⁻ x in l2b_cell (l2b_pt n (k.1 + j)) n, h x :=
        Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ j ∈ l2b_offsets d, ∫⁻ x in W, h x := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← lintegral_iUnion (fun k => l2b_cell_measurable _ _) (hdisj j)]
        refine lintegral_mono_set (Set.iUnion_subset fun k => ?_)
        exact (l2b_cell_sub_cell n k.1 hj).trans k.2
    _ = (3 : ℝ≥0∞) ^ d * ∫⁻ x in W, h x := by
        rw [Finset.sum_const, l2b_card_offsets, nsmul_eq_mul]
        norm_num

/-- **Covering by good cells**: if every point within sup-distance `2·3^n` of `x` lies in `W`,
then `x` lies in a cell `z + □_n` with `z + □_{n+1} ⊆ W`. -/
theorem l2b_exists_cell (n : ℕ) {W : Set (Vec d)} {x : Vec d}
    (hx : ∀ y, (∀ i, |y i - x i| ≤ 2 * 3 ^ n) → y ∈ W) :
    ∃ k : {k : Fin d → ℤ // l2b_cell (l2b_pt n k) (n + 1) ⊆ W},
      x ∈ l2b_cell (l2b_pt n k.1) n := by
  refine ⟨⟨l2b_idx n x, fun y hy => hx y fun i => ?_⟩, l2b_mem_cell_idx n x⟩
  have a := (l2b_mem_cell.1 hy) i
  have b := (l2b_mem_cell.1 (l2b_mem_cell_idx n x)) i
  have e : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
  rw [e] at a
  rw [abs_le]
  constructor <;> linarith only [a.1, a.2, b.1, b.2]

end SuperdiffusionCLT.Section7
