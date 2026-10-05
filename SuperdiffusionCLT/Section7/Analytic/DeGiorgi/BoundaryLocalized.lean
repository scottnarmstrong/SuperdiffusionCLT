/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Boundary
public import Homogenization.Sobolev.H1.LocalizedZeroTrace

/-!
# Level-set test functions under a localized zero trace

Let `Ω ⊆ Q` be open and let `u ∈ H¹(Ω)` have localized zero trace in the window `Q`: every smooth
compactly supported cutoff with support in `Q` turns `u` into an `H¹₀(Ω)` function.  Then the level
test functions `η² (u - k)₊`, `k ≥ 0`, with `η` supported in `Q`, are `H¹₀(Ω)` functions with the
gradient `levelTest u k η`.  No regularity of `∂Ω` is used.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A smooth cutoff equal to `1` on a neighbourhood of every point of a compact set `K` inside an
open set `Q`, with compact support in `Q`. -/
theorem dgloc_exists_cutoff {K Q : Set (Vec d)} (hK : IsCompact K) (hQ : IsOpen Q)
    (hKQ : K ⊆ Q) :
    ∃ ζ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Q ∧
      ∀ x ∈ K, ∀ᶠ y in nhds x, ζ y = 1 := by
  obtain ⟨ε, hε, hεB⟩ := hK.exists_cthickening_subset_open hQ hKQ
  have hK' : IsCompact (Metric.cthickening (ε / 2) K) := hK.cthickening
  have hcl : IsClosed ((Metric.thickening ε K)ᶜ) := Metric.isOpen_thickening.isClosed_compl
  have hdis : Disjoint ((Metric.thickening ε K)ᶜ) (Metric.cthickening (ε / 2) K) := by
    rw [Set.disjoint_compl_left_iff_subset]
    exact Metric.cthickening_subset_thickening' hε (by linarith only [hε]) K
  obtain ⟨ζ, hζ, -, hζ0, hζ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) hcl hK'.isClosed hdis
  have hsupp : tsupport ζ ⊆ Metric.cthickening ε K := by
    refine closure_minimal ?_ Metric.isClosed_cthickening
    intro x hx
    by_contra hxn
    exact hx ((hζ0 x).1 (fun h => hxn (Metric.thickening_subset_cthickening _ _ h)))
  refine ⟨ζ, hζ, ?_, hsupp.trans hεB, fun x hx => ?_⟩
  · exact (hK.cthickening (r := ε)).of_isClosed_subset (isClosed_tsupport ζ) hsupp
  · have hb : Metric.ball x (ε / 2) ∈ nhds x := Metric.ball_mem_nhds x (by linarith only [hε])
    filter_upwards [hb] with y hy
    refine (hζ1 y).1 ?_
    exact Metric.mem_cthickening_of_dist_le y x (ε / 2) K hx (le_of_lt (by simpa [dist_comm] using hy))

/-- The cutoff product of a localized zero trace function, with its gradient. -/
theorem dgloc_cut {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (u : H1Function Ω)
    (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hζQ : tsupport ζ ⊆ Q) :
    ∃ w : H10Function Ω, (∀ x, w.toH1Function.toFun x = ζ x * u.toFun x) ∧
      ∀ᵐ x ∂(volume.restrict Ω), ∀ i, w.toH1Function.grad x i =
        ζ x * u.grad x i + u.toFun x * (fderiv ℝ ζ x) (basisVec i) := by
  obtain ⟨w, hw⟩ := hz ζ hζ hζc hζQ
  refine ⟨w, fun x => congrFun hw x, ?_⟩
  have hp : w.toH1Function.toFun = (u.mulContDiffHasCompactSupport hζ hζc).toFun := by
    rw [hw, H1Function.mulContDiffHasCompactSupport_toFun]
  have hall : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, w.toH1Function.grad x i =
      (u.mulContDiffHasCompactSupport hζ hζc).grad x i :=
    ae_all_iff.2 fun i => gradCoord_ae_eq_of_toFun_eq hΩ w.toH1Function _ hp i
  filter_upwards [hall] with x hx i
  rw [hx i, H1Function.mulContDiffHasCompactSupport_grad]

/-- Where the cutoff is `1` near `x`, the cutoff product has the gradient of `u`. -/
theorem dgloc_cut_grad_eq {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (u : H1Function Ω)
    (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (hζQ : tsupport ζ ⊆ Q) :
    ∃ w : H10Function Ω, (∀ x, w.toH1Function.toFun x = ζ x * u.toFun x) ∧
      ∀ᵐ x ∂(volume.restrict Ω), (∀ᶠ y in nhds x, ζ y = 1) →
        w.toH1Function.grad x = u.grad x := by
  obtain ⟨w, hwf, hwg⟩ := dgloc_cut hΩ u hz hζ hζc hζQ
  refine ⟨w, hwf, ?_⟩
  filter_upwards [hwg] with x hx h1
  have h1' : ζ =ᶠ[nhds x] fun _ => (1 : ℝ) := h1
  funext i
  rw [hx i, h1'.fderiv_eq, h1'.self_of_nhds]
  simp

/-- **The `H¹₀(Ω)` test function `η² (u - k)₊` under a localized zero trace.** -/
theorem dgloc_levelTest_h10 {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (hQ : IsOpen Q)
    (hfin : volume Ω ≠ ⊤) (u : H1Function Ω)
    (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) {k : ℝ} (hk : 0 ≤ k) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Q) :
    ∃ φ : H10Function Ω,
      (∀ x, φ.toH1Function.toFun x = η x ^ 2 * max (u.toFun x - k) 0) ∧
      ∀ᵐ x ∂(volume.restrict Ω), φ.toH1Function.grad x = levelTest u k η x := by
  obtain ⟨ζ, hζ, hζc, hζQ, hζ1⟩ := dgloc_exists_cutoff hηc hQ hηs
  obtain ⟨w, hwf, hwg⟩ := dgloc_cut_grad_eq hΩ u hz hζ hζc hζQ
  obtain ⟨φ, hφf, hφg⟩ := exists_levelTest_h10 hΩ hfin w hk hη hηc
  have hone : ∀ x ∈ tsupport η, ζ x = 1 := fun x hx => (hζ1 x hx).self_of_nhds
  refine ⟨φ, fun x => ?_, ?_⟩
  · rw [hφf x, hwf x]
    by_cases hx : x ∈ tsupport η
    · rw [hone x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  · filter_upwards [hφg, hwg] with x hx hx2
    rw [hx]
    by_cases hxs : x ∈ tsupport η
    · refine levelTest_congr ?_ (hx2 (hζ1 x hxs))
      rw [hwf x, hone x hxs, one_mul]
    · rw [levelTest_eq_zero_of_notMem _ k hxs, levelTest_eq_zero_of_notMem _ k hxs]

end SuperdiffusionCLT.Section7
