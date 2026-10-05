/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2I
public import SuperdiffusionCLT.Section7.Analytic.CZ.Local

/-!
# Translation, and `C²` regularity at every point
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_translateSet_eq (z : Vec d) (U : Set (Vec d)) :
    translateSet z U = (fun x : Vec d ↦ x - z) ⁻¹' U := by
  ext x
  simp only [translateSet, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x - z, h, by simp⟩

theorem intC2_isOpen_translateSet (z : Vec d) {U : Set (Vec d)} (hU : IsOpen U) :
    IsOpen (translateSet z U) := by
  rw [intC2_translateSet_eq]
  exact hU.preimage (continuous_id.sub continuous_const)

theorem intC2_Weak.translate {a : CoeffField d} {mu : ℝ} {g : Vec d → ℝ} {U : Set (Vec d)}
    {u : H1Function U} (hw : intC2_Weak a mu g U u) (z : Vec d) :
    intC2_Weak (fun x ↦ a (x - z)) mu (fun x ↦ g (x - z)) (translateSet z U) (u.translate z) := by
  intro φ hφ hc hs
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) fun y ↦ φ (y + z) := hφ.comp (contDiff_id.add contDiff_const)
  have hc' : HasCompactSupport fun y ↦ φ (y + z) :=
    hc.comp_homeomorph (Homeomorph.addRight z)
  have hs' : tsupport (fun y ↦ φ (y + z)) ⊆ U := by
    intro y hy
    have : y + z ∈ tsupport φ := by
      have h2 := tsupport_comp_eq_preimage φ (Homeomorph.addRight z)
      have hy' : y ∈ tsupport (φ ∘ (Homeomorph.addRight z)) := hy
      rw [h2] at hy'
      exact hy'
    have h3 := hs this
    rw [intC2_translateSet_eq] at h3
    simpa using h3
  have h := hw _ hφ' hc' hs'
  have hmp := measurePreserving_subRight_restrict_translateSet z U
  have hme : MeasurableEmbedding (fun x : Vec d ↦ x - z) :=
    (Homeomorph.subRight z).measurableEmbedding
  have e1 := hmp.integral_comp hme (fun y ↦ vecDot (matVecMul (a y) (u.grad y))
    (fun i ↦ fderiv ℝ φ (y + z) (basisVec i)))
  have e2 := hmp.integral_comp hme (fun y ↦ u.toFun y * φ (y + z))
  have e3 := hmp.integral_comp hme (fun y ↦ g y * φ (y + z))
  simp only [sub_add_cancel] at e1 e2 e3
  simp only [fderiv_comp_add_right] at h
  simp only [H1Function.translate_grad, H1Function.translate_toFun]
  rw [e1, e2, e3]
  exact h

theorem intC2_exists_cube {U : Set (Vec d)} (hU : IsOpen U) (hz : (0 : Vec d) ∈ U) :
    ∃ m : ℤ, openCubeSet (originCube d m) ⊆ U := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU 0 hz
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨-(n : ℤ), fun x hx ↦ hball ?_⟩
  rw [mem_openCubeSet_originCube_iff] at hx
  have e : (3 : ℝ) ^ (-(n : ℤ)) = (1 / 3) ^ n := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hr]
  intro i
  have h := hx i
  rw [e] at h
  rw [Real.norm_eq_abs, abs_lt]
  have hp : (0 : ℝ) < (1 / 3) ^ n := by positivity
  constructor <;> linarith only [h.1, h.2, hn, hp]

/-- **Interior `C²` regularity.**  A bounded continuous `H¹` solution of
`-∇·(a∇u) + μu = g` in an open set, with `a = νId + skew` of class `C²` and `g` of class `C¹`,
is `C²` at every point of the set. -/
theorem intC2_contDiffAt [NeZero d] (hd : 2 ≤ d) {U : Set (Vec d)} (hU : IsOpen U)
    {a : CoeffField d} {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    {M : ℝ} {u : H1Function U} (hu : intC2_Weak a mu g U u) (hcont : ContinuousOn u.toFun U)
    (hbd : ∀ x ∈ U, |u.toFun x| ≤ M) {x₀ : Vec d} (hx₀ : x₀ ∈ U) :
    ContDiffAt ℝ 2 u.toFun x₀ := by
  set z : Vec d := -x₀ with hzdef
  have hU0 : IsOpen (translateSet z U) := intC2_isOpen_translateSet z hU
  have h0 : (0 : Vec d) ∈ translateSet z U := by
    rw [intC2_translateSet_eq]
    simpa [hzdef] using hx₀
  obtain ⟨m, hm⟩ := intC2_exists_cube hU0 h0
  have hcube : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  have hw0 := hu.translate z
  have hwc := hw0.restrict hcube hm
  have hmaps : Set.MapsTo (fun x : Vec d ↦ x - z) (openCubeSet (originCube d m)) U := fun x hx ↦ by
    have := hm hx
    rw [intC2_translateSet_eq] at this
    exact this
  have hcont0 : ContinuousOn (u.translate z).toFun (openCubeSet (originCube d m)) := by
    have : ContinuousOn (fun x : Vec d ↦ u.toFun (x - z)) (openCubeSet (originCube d m)) :=
      hcont.comp (continuous_id.sub continuous_const).continuousOn hmaps
    exact this
  have key := intC2_origin hd m hnu (a := fun x ↦ a (x - z)) (fun y i j ↦ hsk (y - z) i j)
    (fun i j ↦ (ha i j).comp (contDiff_id.sub contDiff_const)) (g := fun x ↦ g (x - z))
    (hg.comp (contDiff_id.sub contDiff_const)) (M := M) hwc
    (u := (u.translate z).restrict hcube hm) hcont0 (fun x hx ↦ by
      simpa only [H1Function.restrict, H1Function.translate_toFun] using hbd _ (hmaps hx)) 0
    (fun i ↦ by
      simp only [Pi.zero_apply, abs_zero]
      have hp : (0 : ℝ) < 3 ^ (m - 1 - 1) := zpow_pos (by norm_num) _
      linarith only [hp])
  have key' : ContDiffAt ℝ 2 (fun x ↦ u.toFun (x - z)) ((fun x : Vec d ↦ x - x₀) x₀) := by
    have : (fun x : Vec d ↦ x - x₀) x₀ = 0 := sub_self _
    rw [this]
    exact key
  have hsubx : ContDiffAt ℝ 2 (fun x : Vec d ↦ x - x₀) x₀ := contDiffAt_id.sub contDiffAt_const
  have hcomp := ContDiffAt.comp (g := fun x ↦ u.toFun (x - z)) (f := fun x : Vec d ↦ x - x₀)
    x₀ key' hsubx
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [hzdef]

end SuperdiffusionCLT.Section8
