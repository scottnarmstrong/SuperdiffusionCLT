/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.Domains
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Homogenization.Sobolev.Foundations.AxisCube

/-!
# Invariance of smooth bounded domains under dilations and translations

`IsSmoothBoundedDomain` is preserved by every positive-ratio affine map `x ↦ y + t • x`, hence by
dilations `t • U` and translations `y + U`, and every Euclidean ball `euclidBall r`, `r > 0`, is a
smooth bounded domain. Dilations of subsets of the unit origin cube lie in the cube of side `t`.

## Main results

* `Section7.w0_isSmoothBoundedDomain_affineImage`
* `Section7.w0_isSmoothBoundedDomain_smul`, `Section7.w0_isSmoothBoundedDomain_translate`
* `Section7.w0_isSmoothBoundedDomain_euclidBall`
* `Section7.w0_smul_subset_axisCube`, `Section7.w0_smul_subset_openCubeSet_originCube`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization
open scoped Pointwise

variable {d : ℕ}

/-- The affine homeomorphism `x ↦ y + t • x`. -/
noncomputable def w0_affineHomeo (y : Vec d) {t : ℝ} (ht : t ≠ 0) : Vec d ≃ₜ Vec d :=
  (Homeomorph.smulOfNeZero t ht).trans (Homeomorph.addLeft y)

theorem w0_vecDot_add_smul (e y z : Vec d) (t : ℝ) :
    vecDot e (y + t • z) = vecDot e y + t * vecDot e z := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem w0_proj_add_smul (e y z : Vec d) (t : ℝ) :
    (y + t • z) - vecDot e (y + t • z) • e =
      (y - vecDot e y • e) + t • (z - vecDot e z • e) := by
  rw [w0_vecDot_add_smul]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem w0_vecNormSq_smul (c : ℝ) (v : Vec d) : vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Affine invariance.** The image of a smooth bounded domain under `x ↦ y + t • x`, `t > 0`,
is a smooth bounded domain. -/
theorem w0_isSmoothBoundedDomain_affineImage {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U)
    {t : ℝ} (ht : 0 < t) (y : Vec d) :
    IsSmoothBoundedDomain ((fun x => y + t • x) '' U) := by
  obtain ⟨hUo, hUc, ⟨R, hR, hRb⟩, hch⟩ := hU
  have hne : t ≠ 0 := ht.ne'
  set T : Vec d ≃ₜ Vec d := w0_affineHomeo y hne with hT
  have hTapp : ∀ x, T x = y + t • x := fun x => rfl
  have himg : (fun x => y + t • x) '' U = T '' U := by
    ext z
    simp only [Set.mem_image, hTapp]
  rw [himg]
  have hmem : ∀ z, z ∈ T '' U ↔ T.symm z ∈ U := fun z =>
    ⟨fun ⟨x, hx, hxz⟩ => by rw [← hxz, T.symm_apply_apply]; exact hx,
      fun h => ⟨_, h, T.apply_symm_apply z⟩⟩
  refine ⟨T.isOpenMap U hUo, hUc.image _ T.continuous.continuousOn, ?_, ?_⟩
  · refine ⟨(∑ j, |y j|) + t * R + 1, by positivity, ?_⟩
    rintro z ⟨x, hx, rfl⟩ i
    rw [hTapp]
    have h1 : |y i| ≤ ∑ j, |y j| :=
      Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : |t * x i| ≤ t * R := by
      rw [abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (hRb x hx i) ht.le
    have h3 := abs_add_le (y i) (t * x i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith only [h1, h2, h3]
  · intro z hz
    rw [← T.image_frontier] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨e, ψ, W, r, he, hr, hWo, hψ, hloc⟩ := hch x hx
    set p : Vec d := y - vecDot e y • e with hp
    set c : ℝ := vecDot e y with hc
    have hcont : Continuous (fun w : Vec d => t⁻¹ • (w - p)) := by fun_prop
    refine ⟨e, fun w => c + t * ψ (t⁻¹ • (w - p)), {w | t⁻¹ • (w - p) ∈ W}, t * r, he,
      by positivity, hWo.preimage hcont, ?_, fun z hz => ?_⟩
    · have hψ' : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec d => ψ (t⁻¹ • (w - p)))
          {w | t⁻¹ • (w - p) ∈ W} := by
        refine hψ.comp ?_ (fun w hw => hw)
        have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => t⁻¹ • (w - p)) :=
          (contDiff_id.sub contDiff_const).const_smul t⁻¹
        exact hcd.contDiffOn
      exact (contDiff_const.contDiffOn).add (contDiff_const.contDiffOn.mul hψ')
    · obtain ⟨z', rfl⟩ : ∃ z', z = y + t • z' := ⟨t⁻¹ • (z - y), by
        rw [smul_inv_smul₀ hne]; abel⟩
      have hdist : z' ∈ Metric.ball x r := by
        rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
        have : T x = y + t • x := rfl
        rw [this] at hz
        have h1 : y + t • z' - (y + t • x) = t • (z' - x) := by
          rw [smul_sub]; abel
        rw [h1, norm_smul, Real.norm_of_nonneg ht.le] at hz
        exact lt_of_mul_lt_mul_left hz ht.le
      obtain ⟨hW, hiff⟩ := hloc z' hdist
      have hpr := w0_proj_add_smul e y z' t
      have hpr' : (y + t • z') - vecDot e (y + t • z') • e = p + t • (z' - vecDot e z' • e) := hpr
      have hback : t⁻¹ • (((y + t • z') - vecDot e (y + t • z') • e) - p) =
          z' - vecDot e z' • e := by
        rw [hpr']
        simp only [add_sub_cancel_left]
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      refine ⟨by simpa only [Set.mem_ofPred_eq, hback] using hW, ?_⟩
      have hsymm : T.symm (y + t • z') = z' := by
        have := T.symm_apply_apply z'
        rwa [hTapp] at this
      rw [hmem]
      beta_reduce
      rw [hback, hsymm, hiff, w0_vecDot_add_smul]
      constructor
      · intro h
        have := mul_lt_mul_of_pos_left h ht
        linarith only [this]
      · intro h
        have := (mul_lt_mul_iff_right₀ ht).1 (by linarith only [h] : t * vecDot e z' < t * ψ (z' - vecDot e z' • e))
        exact this

/-- Dilations preserve smooth bounded domains. -/
theorem w0_isSmoothBoundedDomain_smul {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) {t : ℝ}
    (ht : 0 < t) : IsSmoothBoundedDomain (t • U) := by
  have := w0_isSmoothBoundedDomain_affineImage hU ht 0
  rwa [show ((fun x => (0 : Vec d) + t • x) '' U) = t • U by
    ext z
    simp [Set.mem_smul_set]] at this

/-- Translations preserve smooth bounded domains. -/
theorem w0_isSmoothBoundedDomain_translate {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U)
    (y : Vec d) : IsSmoothBoundedDomain ((fun x => y + x) '' U) := by
  have := w0_isSmoothBoundedDomain_affineImage hU one_pos y
  simpa only [one_smul] using this

theorem w0_euclidBall_eq_smul {r : ℝ} (hr : 0 < r) :
    Section6.euclidBall (d := d) r = r • Section6.euclidBall 1 := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [Section6.mem_euclidBall, w0_vecNormSq_smul]
  have hr2 : 0 < r ^ 2 := by positivity
  rw [one_pow, inv_pow, inv_mul_lt_iff₀ hr2, mul_one]

/-- Every Euclidean ball is a smooth bounded domain. -/
theorem w0_isSmoothBoundedDomain_euclidBall [NeZero d] {r : ℝ} (hr : 0 < r) :
    IsSmoothBoundedDomain (Section6.euclidBall (d := d) r) := by
  rw [w0_euclidBall_eq_smul hr]
  exact w0_isSmoothBoundedDomain_smul isSmoothBoundedDomain_euclidBall hr

/-- A point of the open unit origin cube has all coordinates in `(-1/2, 1/2)`. -/
theorem w0_mem_openCubeSet_originCube_zero_iff {x : Vec d} :
    x ∈ openCubeSet (originCube d 0) ↔ ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
  simp only [openCubeSet, originCube, cubeScaleFactor, Set.mem_ofPred_eq, zpow_zero]
  refine forall_congr' fun i => ?_
  simp only [Pi.zero_apply, Int.cast_zero, zero_sub, zero_add, mul_one]

/-- A dilation of a subset of the unit origin cube lies in the cube `(-t/2, t/2)^d` of side `t`. -/
theorem w0_smul_subset_axisCube {U : Set (Vec d)} (hU : U ⊆ openCubeSet (originCube d 0))
    {t : ℝ} (ht : 0 < t) : t • U ⊆ axisCube (fun _ => -(t / 2)) t := by
  rintro _ ⟨x, hx, rfl⟩ i _
  have h := w0_mem_openCubeSet_originCube_zero_iff.1 (hU hx) i
  change t * x i ∈ Set.Ioo (-(t / 2)) (-(t / 2) + t)
  rw [Set.mem_Ioo]
  constructor
  · nlinarith only [h.1, ht]
  · nlinarith only [h.2, ht]

/-- A dilation by `t ≤ 3^m` of a subset of the unit origin cube lies in the origin cube `□_m`. -/
theorem w0_smul_subset_openCubeSet_originCube {U : Set (Vec d)}
    (hU : U ⊆ openCubeSet (originCube d 0)) {t : ℝ} (ht : 0 < t) (m : ℤ)
    (htm : t ≤ (3 : ℝ) ^ m) : t • U ⊆ openCubeSet (originCube d m) := by
  rintro _ ⟨x, hx, rfl⟩ i
  have h := w0_mem_openCubeSet_originCube_zero_iff.1 (hU hx) i
  simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
  change -(1 / 2) * 3 ^ m < t * x i ∧ t * x i < 1 / 2 * 3 ^ m
  constructor
  · nlinarith only [h.1, ht, htm]
  · nlinarith only [h.2, ht, htm]

/-! ### Witnesses -/

/-- The unit ball is a smooth bounded domain, hence so are its dilates and translates. -/
example [NeZero d] (r : ℝ) (hr : 0 < r) (y : Vec d) :
    IsSmoothBoundedDomain ((fun x => y + x) '' Section6.euclidBall r) :=
  w0_isSmoothBoundedDomain_translate (w0_isSmoothBoundedDomain_euclidBall hr) y

/-- The ball of radius `1/2` lies in the unit cube, so its `t`-dilate lies in the cube of side `t`. -/
example [NeZero d] {t : ℝ} (ht : 0 < t) :
    t • Section6.euclidBall (d := d) (1 / 2) ⊆ axisCube (fun _ => -(t / 2)) t := by
  refine w0_smul_subset_axisCube (fun x hx => ?_) ht
  rw [w0_mem_openCubeSet_originCube_zero_iff]
  intro i
  have h1 := Section6.euclidBall_subset_ball (d := d) (r := 1 / 2) (by norm_num) hx
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)] at h1
  have := h1 i
  rw [Real.norm_eq_abs, abs_lt] at this
  exact this

end SuperdiffusionCLT.Section7
