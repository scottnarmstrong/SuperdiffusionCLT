/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2H

/-!
# `C²` regularity at the origin

A bounded continuous `H¹` solution of `-∇·(a∇u) + μu = g` on the origin cube of scale `3^m`, with
`a = νId + skew` and `g` of class `C¹`, is `C²` on the box `|xᵢ| < 3^(m-2)/4`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_contDiffAt_two {u : Vec d → ℝ} {G : Fin d → Vec d → ℝ} {B : Set (Vec d)}
    (hB : IsOpen B) (hderiv : ∀ y ∈ B, HasFDerivAt u (intC2_cand G y) y)
    (hG2 : ∀ i, ∃ G' : Fin d → Vec d → ℝ, (∀ j, ContinuousOn (G' j) B) ∧
      ∀ y ∈ B, HasFDerivAt (G i) (intC2_cand G' y) y) {x : Vec d} (hx : x ∈ B) :
    ContDiffAt ℝ 2 u x := by
  have h1 : ∀ i, ContDiffAt ℝ 1 (G i) x := fun i ↦ by
    obtain ⟨G', hc, hd'⟩ := hG2 i
    rw [contDiffAt_one_iff]
    refine ⟨intC2_cand G', B, hB.mem_nhds hx, ?_, hd'⟩
    unfold intC2_cand
    exact continuousOn_finsetSum _ fun j _ ↦ (hc j).smul continuousOn_const
  have h2 : ContDiffAt ℝ 1 (intC2_cand G) x := by
    unfold intC2_cand
    refine ContDiffAt.sum fun i _ ↦ ?_
    exact (h1 i).smul contDiffAt_const
  have : ContDiffAt ℝ ((1 : ℕ) + 1) u x := by
    rw [contDiffAt_succ_iff_hasFDerivAt]
    exact ⟨intC2_cand G, ⟨B, hB.mem_nhds hx, hderiv⟩, by simpa using h2⟩
  have e : ((1 : ℕ) : WithTop ℕ∞) + 1 = 2 := by norm_num
  rwa [e] at this

/-- **Interior `C²` regularity at the origin.** -/
theorem intC2_origin [NeZero d] (hd : 2 ≤ d) (m : ℤ) {a : CoeffField d} {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    {M : ℝ} {u : H1Function (openCubeSet (originCube d m))}
    (hu : intC2_Weak a mu g (openCubeSet (originCube d m)) u)
    (hcont : ContinuousOn u.toFun (openCubeSet (originCube d m)))
    (hbd : ∀ x ∈ openCubeSet (originCube d m), |u.toFun x| ≤ M) :
    ∀ x ∈ intC2_box d ((3 : ℝ) ^ (m - 1 - 1) / 4), ContDiffAt ℝ 2 u.toFun x := by
  have hP : (d : ℝ) < d + 1 := lt_add_one _
  have hP2 : (2 : ℝ) ≤ d + 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  obtain ⟨G, Hs, hGc, hderiv, hGae, hHs, hHsL⟩ :=
    intC2_stage1 hd m hP hnu hsk ha hg.continuous hu hcont hbd
  have hB : IsOpen (intC2_box d ((3 : ℝ) ^ (m - 1) / 4)) := intC2_isOpen_box _
  have hBU : intC2_box d ((3 : ℝ) ^ (m - 1) / 4) ⊆ openCubeSet (originCube d m) :=
    (intC2_box_subset_cube (m - 1)).trans (intC2_cube_sub m)
  have : IsFiniteMeasure (volume.restrict (intC2_box d ((3 : ℝ) ^ (m - 1) / 4))) :=
    intC2_isFinite_box (m - 1)
  have hP2' : (2 : ENNReal) ≤ ENNReal.ofReal (d + 1) := by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hP2
  have hHs2 : ∀ i j, MemLp (Hs i j) 2 (volume.restrict (intC2_box d ((3 : ℝ) ^ (m - 1) / 4))) :=
    fun i j ↦ (hHsL i j).mono_exponent hP2'
  have hsub2 : openCubeSet (originCube d (m - 1 - 1)) ⊆
      intC2_box d ((3 : ℝ) ^ (m - 1) / 4) := intC2_box_quarter_sub (m - 1)
  have hstage : ∀ k : Fin d, ∃ G' : Fin d → Vec d → ℝ,
      (∀ j, ContinuousOn (G' j) (intC2_box d ((3 : ℝ) ^ (m - 1 - 1) / 4))) ∧
      ∀ y ∈ intC2_box d ((3 : ℝ) ^ (m - 1 - 1) / 4), HasFDerivAt (G k) (intC2_cand G' y) y := by
    intro k
    obtain ⟨v, hvf, hvg⟩ := intC2_vH1 (m - 1) hGc hHs hHs2 k
    have hz := intC2_vWeak (m - 1) hP2 hnu hsk ha hg (uB := u.restrict hB hBU) (hu.restrict hB hBU)
      hGae hGc hHs hHsL k v hvg
    have hhv := intC2_rhs_memLp (m - 1) (nu := nu) (mu := mu) ha hg hGc hHsL k
    have hgz : ∀ j, MemLp (fun x ↦ v.grad x j) (ENNReal.ofReal (d + 1))
        (normalizedCubeMeasure (originCube d (m - 1 - 1))) := fun j ↦ by
      simp only [hvg]
      exact intC2_memLp_cube_of_restrict hsub2 (hHsL k j)
    have hcontv : ContinuousOn v.toFun (openCubeSet (originCube d (m - 1 - 1))) := by
      rw [hvf]; exact (hGc k).mono hsub2
    have hK : IsCompact (closure (openCubeSet (originCube d (m - 1 - 1)))) :=
      (isBounded_openCubeSet _).isCompact_closure
    obtain ⟨Mv, hMv⟩ := hK.exists_bound_of_continuousOn
      ((hGc k).mono (intC2_closure_cube_sub (m - 1)))
    have hzz : MemLp v.toFun (ENNReal.ofReal (d + 1))
        (normalizedCubeMeasure (originCube d (m - 1 - 1))) := by
      rw [hvf]
      exact intC2_memLp_cubeBdd (((hGc k).mono hsub2).aestronglyMeasurable
        (isOpen_openCubeSet _).measurableSet) (M := Mv) (fun x hx ↦ by
          simpa only [Real.norm_eq_abs] using hMv x (subset_closure hx)) _
    obtain ⟨G', -, hG'c, hG'd, -⟩ := intC2_core_c1 hd (m - 1 - 1) hP hz hhv hgz hzz hcontv
    exact ⟨G', hG'c, fun y hy ↦ by simpa only [hvf] using hG'd y hy⟩
  intro x hx
  exact intC2_contDiffAt_two (intC2_isOpen_box _)
    (fun y hy ↦ hderiv y (intC2_box_subset (by
      have hp : (0 : ℝ) < 3 ^ (m - 1) := zpow_pos (by norm_num) _
      have e : (3 : ℝ) ^ (m - 1 - 1) = 3 ^ (m - 1) / 3 := by
        rw [zpow_sub_one₀ (by norm_num)]
        ring
      rw [e]
      linarith only [hp]) hy)) hstage hx

end SuperdiffusionCLT.Section8
