/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyAssemblyB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerH1C
public import Mathlib.Data.Pi.Interval
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# The geometry of the grid cells and of the boundary layer

For `h = 3^j` the carrier `whitneyInterior W j` is the union of the half-open cells of the grid
indices `k` whose averaging box `B_k = box (h k) (27 h / 2)` lies in `W`.  Up to the null set of
cell faces it is the union of the open cells of the finite set `Zg` of such indices, and the part
of an open set `W` outside this union lies in the boundary layer of width `14 h`.

## Main results

* `Section7.wh3_whitneyInterior_ae`: `whitneyInterior W j` and the union of open cells agree a.e.
* `Section7.wh3_layer_cover`: a.e. point of `W` outside the union of the cells lies in the layer.
* `Section7.wh3_finite_of_bounded`: the index set is finite for a bounded `W`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The half-open cell of the grid index `k`. -/
def wh3_halfcell (h : ℝ) (k : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, h * (k i : ℝ) - h / 2 ≤ x i ∧ x i < h * (k i : ℝ) + h / 2}

theorem wh3_cell_subset_halfcell (h : ℝ) (k : Fin d → ℤ) : wh3_cell h k ⊆ wh3_halfcell h k := by
  intro x hx i
  have h1 := abs_lt.1 (hx i)
  have h1' : -(h / 2) < x i - h * (k i : ℝ) ∧ x i - h * (k i : ℝ) < h / 2 := h1
  exact ⟨by linarith only [h1'.1], by linarith only [h1'.2]⟩

theorem wh3_shiftCube_eq_box (y : Vec d) (j : ℤ) :
    shiftCube y (j + 3) = wh1_box y (27 * (3 : ℝ) ^ j / 2) := by
  ext x
  rw [rc_mem_shiftCube]
  have h27 : (3 : ℝ) ^ (j + 3) = 27 * (3 : ℝ) ^ j := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  rw [h27]
  rfl

/-- The Whitney interior as a union of half-open cells. -/
theorem wh3_mem_whitneyInterior {W : Set (Vec d)} {j : ℤ} {x : Vec d} :
    x ∈ whitneyInterior W j ↔ ∃ k : Fin d → ℤ,
      wh1_box (wh1_pt ((3 : ℝ) ^ j) k) (27 * (3 : ℝ) ^ j / 2) ⊆ W ∧
        x ∈ wh3_halfcell ((3 : ℝ) ^ j) k := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  simp only [whitneyInterior, Set.mem_iUnion, exists_prop]
  refine exists_congr fun k => ?_
  rw [wh3_shiftCube_eq_box, wpd_mem_cellImage k]
  refine and_congr_left fun _ => ?_
  constructor
  · exact fun h => h.2
  · intro hsub
    refine ⟨hsub ?_, hsub⟩
    intro i
    show |wh1_pt ((3 : ℝ) ^ j) k i - ((3 : ℝ) ^ j * (k i : ℝ))| < _
    simp only [wh1_pt, sub_self, abs_zero]
    positivity

/-- The index set of the cells whose averaging box lies in `W`. -/
def wh3_good (h : ℝ) (W : Set (Vec d)) : Set (Fin d → ℤ) :=
  {k | wh1_box (wh1_pt h k) (27 * h / 2) ⊆ W}

theorem wh3_finite_of_bounded {W : Set (Vec d)} {R : ℝ} (hW : ∀ x ∈ W, ∀ i, |x i| ≤ R) {h : ℝ}
    (hh : 0 < h) : (wh3_good h W).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_ge (R / h)
  refine (Set.finite_Icc (fun _ : Fin d => -(N : ℤ)) (fun _ => (N : ℤ))).subset fun k hk => ?_
  have hmem : wh1_pt h k ∈ wh1_box (wh1_pt h k) (27 * h / 2) := by
    intro i
    simp only [sub_self, abs_zero]
    positivity
  have hb := hW _ (hk hmem)
  have hk' : ∀ i, |(k i : ℝ)| ≤ N := by
    intro i
    have h1 := hb i
    simp only [wh1_pt] at h1
    rw [abs_mul, abs_of_pos hh] at h1
    have h2 : |(k i : ℝ)| ≤ R / h := by rw [le_div_iff₀ hh]; linarith only [h1]
    linarith only [h2, hN]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.1 (hk' i)).1
    have : (-(N : ℤ) : ℝ) ≤ (k i : ℝ) := by push_cast; linarith only [this]
    exact_mod_cast this
  · have := (abs_le.1 (hk' i)).2
    exact_mod_cast this

/-- The null set of the faces. -/
theorem wh3_ae_notMem_faces {h : ℝ} (hh : 0 < h) : ∀ᵐ x : Vec d, x ∉ wpd_faces d h :=
  measure_eq_zero_iff_ae_notMem.1 (wpd_volume_faces hh)

theorem wh3_halfcell_ae {h : ℝ} (hh : 0 < h) (k : Fin d → ℤ) :
    ∀ᵐ x : Vec d, x ∈ wh3_halfcell h k → x ∈ wh3_cell h k := by
  filter_upwards [wh3_ae_notMem_faces (d := d) hh] with x hx hxc i
  have h1 := hxc i
  have hne : x i ≠ h * (k i : ℝ) - h / 2 := by
    intro he
    refine hx ⟨i, k i, ?_⟩
    rw [he]
    field_simp
    ring
  have h2 : -(h / 2) < x i - h * (k i : ℝ) := by
    have := lt_of_le_of_ne h1.1 (Ne.symm hne)
    linarith only [this]
  show |x i - h * (k i : ℝ)| < h / 2
  rw [abs_lt]
  exact ⟨h2, by linarith only [h1.2]⟩

/-- The Whitney interior and the union of the open cells agree almost everywhere. -/
theorem wh3_whitneyInterior_ae {W : Set (Vec d)} {j : ℤ} {Zg : Finset (Fin d → ℤ)}
    (hZg : ∀ k, k ∈ Zg ↔ k ∈ wh3_good ((3 : ℝ) ^ j) W) :
    whitneyInterior W j =ᵐ[volume] ⋃ k ∈ Zg, wh3_cell ((3 : ℝ) ^ j) k := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hsub : (⋃ k ∈ Zg, wh3_cell ((3 : ℝ) ^ j) k) ⊆ whitneyInterior W j := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    rw [wh3_mem_whitneyInterior]
    exact ⟨k, ((hZg k).1 hk), wh3_cell_subset_halfcell _ _ hxk⟩
  refine Filter.EventuallyLE.antisymm ?_ hsub.eventuallyLE
  have hall : ∀ᵐ x : Vec d, ∀ k : Fin d → ℤ, x ∈ wh3_halfcell ((3 : ℝ) ^ j) k →
      x ∈ wh3_cell ((3 : ℝ) ^ j) k := by
    rw [ae_all_iff]
    exact fun k => wh3_halfcell_ae h3 k
  filter_upwards [hall] with x hx hxQ
  rw [wh3_mem_whitneyInterior] at hxQ
  obtain ⟨k, hk, hxk⟩ := hxQ
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨k, (hZg k).2 hk, hx k hxk⟩

/-- Along a segment from a point of an open set to a point outside, the segment meets the
frontier. -/
theorem wh3_infDist_le {W : Set (Vec d)} (hW : IsOpen W) {x y : Vec d} (hx : x ∈ W) (hy : y ∉ W) :
    Metric.infDist x (frontier W) ≤ dist x y := by
  by_cases hz : ∃ z ∈ segment ℝ x y, z ∈ frontier W
  · obtain ⟨z, hzs, hzf⟩ := hz
    refine (Metric.infDist_le_dist_of_mem hzf).trans ?_
    have := dist_add_dist_of_mem_segment hzs
    linarith only [this, dist_nonneg (x := z) (y := y)]
  · exfalso
    push Not at hz
    have hcl : closure W = W ∪ frontier W := by
      rw [frontier, hW.interior_eq]; exact (Set.union_sdiff_cancel subset_closure).symm
    have hseg : segment ℝ x y ⊆ W ∪ (closure W)ᶜ := by
      intro z hzs
      by_cases hzW : z ∈ W
      · exact Or.inl hzW
      · refine Or.inr fun hc => ?_
        rw [hcl] at hc
        rcases hc with h1 | h1
        · exact hzW h1
        · exact hz z hzs h1
    have hdisj : Disjoint W (closure W)ᶜ := by
      rw [Set.disjoint_compl_right_iff_subset]
      exact subset_closure
    have hpre : IsPreconnected (segment ℝ x y) := (convex_segment x y).isPreconnected
    rcases hpre.subset_or_subset hW isClosed_closure.isOpen_compl hdisj hseg with h1 | h1
    · exact hy (h1 (right_mem_segment ℝ x y))
    · exact (h1 (left_mem_segment ℝ x y)) (subset_closure hx)

/-- Almost every point of `W` outside the union of the cells lies in the boundary layer of width
`14 h`. -/
theorem wh3_layer_cover {W : Set (Vec d)} (hW : IsOpen W) {h : ℝ} (hh : 0 < h)
    {Zg : Finset (Fin d → ℤ)} (hZg : ∀ k, k ∈ Zg ↔ k ∈ wh3_good h W) :
    ∀ᵐ x : Vec d, x ∈ W → x ∉ (⋃ k ∈ Zg, wh3_cell h k) → x ∈ boundaryLayer W (14 * h) := by
  filter_upwards [wh3_ae_notMem_faces (d := d) hh] with x hxf hxW hxU
  refine ⟨hxW, ?_⟩
  set k₀ : Fin d → ℤ := fun i => ⌊x i / h + 1 / 2⌋ with hk₀
  have hcell : x ∈ wh3_cell h k₀ := by
    intro i
    have hf1 := Int.floor_le (x i / h + 1 / 2)
    have hf2 := Int.lt_floor_add_one (x i / h + 1 / 2)
    have hne : (k₀ i : ℝ) ≠ x i / h + 1 / 2 := by
      intro he
      exact hxf ⟨i, k₀ i, he.symm⟩
    have hlt : (k₀ i : ℝ) < x i / h + 1 / 2 := lt_of_le_of_ne hf1 hne
    have e1 : x i - h * (k₀ i : ℝ) = h * (x i / h - (k₀ i : ℝ)) := by field_simp
    show |x i - h * (k₀ i : ℝ)| < h / 2
    rw [e1, abs_mul, abs_of_pos hh]
    have : |x i / h - (k₀ i : ℝ)| < 1 / 2 := by
      rw [abs_lt]; constructor <;> linarith only [hlt, hf2]
    nlinarith only [this, hh]
  have hk0 : k₀ ∉ Zg := fun hk => hxU (by
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨k₀, hk, hcell⟩)
  have hnot : ¬ (wh1_box (wh1_pt h k₀) (27 * h / 2) ⊆ W) := fun hs => hk0 ((hZg k₀).2 hs)
  rw [Set.not_subset] at hnot
  obtain ⟨y, hyb, hyW⟩ := hnot
  refine lt_of_le_of_lt (wh3_infDist_le hW hxW hyW) ?_
  rw [dist_eq_norm, pi_norm_lt_iff (by positivity)]
  intro i
  have h1 := abs_lt.1 (hcell i)
  have h2 := abs_lt.1 (hyb i)
  have h1' : -(h / 2) < x i - h * (k₀ i : ℝ) ∧ x i - h * (k₀ i : ℝ) < h / 2 := h1
  have h2' : -(27 * h / 2) < y i - h * (k₀ i : ℝ) ∧ y i - h * (k₀ i : ℝ) < 27 * h / 2 := h2
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> simp only [Pi.sub_apply] <;> linarith only [h1'.1, h1'.2, h2'.1, h2'.2]

end SuperdiffusionCLT.Section7
