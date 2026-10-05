/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryJ
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryF

/-!
# Normalized `L²` norms on the grid cubes of a subdomain

For a function in `L²(D)` with `D` a subdomain of the cube `Q`, the zero extension is in
`L²(Q)` with `‖ĝ‖²_{L̲²(Q)} = |Q|⁻¹ ∫_D g²`, and on a grid cube inside `D` the normalized norms of
`g` and of `ĝ` agree.  Hence the average over the grid of the squared norms over the good cubes is
at most `|Q|⁻¹ ∫_D g²`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_ext_memLp [NeZero d] (Q : TriadicCube d) {D : Set (Vec d)} (hD : MeasurableSet D)
    (hDQ : D ⊆ openCubeSet Q) {g : Vec d → ℝ} (hg : MemLp g 2 (volume.restrict D)) :
    MemLp (D.indicator g) 2 (normalizedCubeMeasure Q) := by
  refine ca1_memLp_of_restrict Q ?_
  rw [memLp_indicator_iff_restrict hD, Measure.restrict_restrict hD, Set.inter_eq_left.2 hDQ]
  exact hg

theorem ca2_ext_sq [NeZero d] (Q : TriadicCube d) {D : Set (Vec d)} (hD : MeasurableSet D)
    (hDQ : D ⊆ openCubeSet Q) {g : Vec d → ℝ} (hg : MemLp g 2 (volume.restrict D)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (D.indicator g) ^ 2 = (cubeVolume Q)⁻¹ * ∫ x in D, g x ^ 2 := by
  rw [ca1_cubeLpNorm_sq Q (ca2_ext_memLp Q hD hDQ hg), ca1_cubeAverage_eq]
  congr 1
  have e : (fun x => D.indicator g x ^ 2) = D.indicator (fun x => g x ^ 2) := by
    funext x
    by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  rw [e, setIntegral_indicator hD, Set.inter_eq_right.2 hDQ]

theorem ca2_cubeLpNorm_ext (R : TriadicCube d) {D : Set (Vec d)} (hRD : openCubeSet R ⊆ D)
    (g : Vec d → ℝ) :
    cubeLpNorm R (2 : ℝ≥0∞) (D.indicator g) = cubeLpNorm R (2 : ℝ≥0∞) g := by
  unfold cubeLpNorm
  refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
  filter_upwards [ca1_ae_openR R (P := fun x => D.indicator g x = g x)
    (fun x hx => by simp [Set.indicator, hRD hx])] with x hx
  exact hx

theorem ca2_Zi_subset (m : ℤ) (h : ℕ) (a : ℝ) (W : Set (Vec d)) :
    ca2_Zi m h a W ⊆ descendantsAtDepth (originCube d m) h := by
  classical
  unfold ca2_Zi
  exact Finset.filter_subset _ _

theorem ca2_good_openCube_subset (m : ℤ) (h : ℕ) {a : ℝ} {W : Set (Vec d)} {R : TriadicCube d}
    (hR : R ∈ ca2_Zi m h a W) : openCubeSet R ⊆ openCubeSet (originCube d m) ∩ W := by
  classical
  have hR' := Finset.mem_filter.1 hR
  exact fun x hx => ⟨openCubeSet_subset_of_mem_descendantsAtDepth hR'.1 hx, hR'.2.2 hx⟩

theorem ca2_sum_sq_le [NeZero d] (m : ℤ) (h : ℕ) (a : ℝ) {W : Set (Vec d)} (hWo : IsOpen W)
    {g : Vec d → ℝ} (hg : MemLp g 2 (volume.restrict (openCubeSet (originCube d m) ∩ W))) :
    ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
        ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞) g ^ 2 ≤
      (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W, g x ^ 2 := by
  classical
  set D := openCubeSet (originCube d m) ∩ W with hDdef
  have hDm : MeasurableSet D := ((isOpen_openCubeSet _).inter hWo).measurableSet
  have hDQ : D ⊆ openCubeSet (originCube d m) := Set.inter_subset_left
  have hext := ca2_ext_memLp (originCube d m) hDm hDQ hg
  rw [← ca2_ext_sq (originCube d m) hDm hDQ hg, ← ca1_desc_sq (originCube d m) hext h]
  show _ ≤ ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d m) h, cubeLpNorm R (2 : ℝ≥0∞) (D.indicator g) ^ 2
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  calc ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞) g ^ 2
      = ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞) (D.indicator g) ^ 2 := by
        refine Finset.sum_congr rfl fun R hR => ?_
        rw [ca2_cubeLpNorm_ext R (ca2_good_openCube_subset m h hR |>.trans (by rw [hDdef]))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (ca2_Zi_subset m h a W)
        (fun R _ _ => sq_nonneg _)

end SuperdiffusionCLT.Section7
