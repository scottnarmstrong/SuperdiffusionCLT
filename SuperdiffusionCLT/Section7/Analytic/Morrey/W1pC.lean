/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Morrey.W1p
public import SuperdiffusionCLT.Section7.Analytic.Morrey.W1pB

@[expose] public section

open MeasureTheory Homogenization Filter Topology

/-!
# Uniform Hölder bound for the convex smoothing of a `W^{1,p}` function

Combines the box Morrey inequality with the uniform gradient bound, and records two elementary
lemmas used for the passage to the limit: a sequence that is uniformly equicontinuous and converges
on a dense set converges everywhere, and the weak gradient of a `W^{1,p}` function has finite `L^p`
norm.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A uniformly equicontinuous sequence converging on a dense set converges everywhere. -/
theorem exists_tendsto_of_dense {X : Type*} (P : X → Prop) (S : Set X) (f : ℕ → X → ℝ)
    (H : X → X → ℝ) (hH : ∀ k x y, P x → P y → |f k x - f k y| ≤ H x y)
    (hSP : ∀ x ∈ S, P x) (hdense : ∀ x, P x → ∀ η > 0, ∃ x' ∈ S, H x x' < η)
    (hS : ∀ x ∈ S, ∃ l, Tendsto (fun k => f k x) atTop (𝓝 l)) {x : X} (hx : P x) :
    ∃ l, Tendsto (fun k => f k x) atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  obtain ⟨x', hx'S, hx'⟩ := hdense x hx (ε / 3) (by positivity)
  obtain ⟨l, hl⟩ := hS x' hx'S
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hH m x x' hx (hSP x' hx'S)
  have h2 := hH n x x' hx (hSP x' hx'S)
  have h3 := hN m hm n hn
  rw [Real.dist_eq] at h3 ⊢
  rw [abs_lt] at h3
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [abs_lt]
  constructor <;> linarith only [h1'.1, h1'.2, h2'.1, h2'.2, h3.1, h3.2, hx']

theorem norm_le_sum_abs_apply (w : Vec d) : ‖w‖ ≤ ∑ i, |w i| := by
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |w j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- The `L^p` norm of the weak gradient of a `W^{1,p}` function is finite. -/
theorem eLpNorm_grad_lt_top {U : Set (Vec d)} {p : ℝ} (hp1 : 1 < p)
    (u : W1pFunction U (ENNReal.ofReal p)) :
    eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p) (volume.restrict U) < ⊤ := by
  have hp1' : 1 ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp1.le)
  have hmeas : AEStronglyMeasurable (fun w => ‖u.grad w‖) (volume.restrict U) := by
    refine AEMeasurable.aestronglyMeasurable ?_
    exact (aemeasurable_pi_iff.2 fun i => (u.gradMemLp i).aestronglyMeasurable.aemeasurable).norm
  have hsum : eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p) (volume.restrict U) ≤
      eLpNorm (∑ i, fun x => ‖u.grad x i‖) (ENNReal.ofReal p) (volume.restrict U) := by
    refine eLpNorm_mono_ae hmeas (ae_of_all _ fun x => ?_)
    have hnn : 0 ≤ (∑ i, fun x => ‖u.grad x i‖) x := by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hnn, Finset.sum_apply]
    simpa [Real.norm_eq_abs] using norm_le_sum_abs_apply (u.grad x)
  refine lt_of_le_of_lt hsum (lt_of_le_of_lt (eLpNorm_sum_le hp1') ?_)
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [eLpNorm_norm _ (u.gradMemLp i).aestronglyMeasurable]
  exact (u.gradMemLp i).eLpNorm_lt_top

theorem closedBall_subset_axisCube {z : Vec d} {L : ℝ} (hL : 0 < L) :
    Metric.closedBall (fun j => z j + L / 2) (L / 4) ⊆ axisCube z L := by
  intro a ha j _
  have h := (Metric.mem_closedBall.1 ha)
  rw [dist_eq_norm] at h
  have hj : |a j - (z j + L / 2)| ≤ L / 4 := by
    have h2 : |a j - (z j + L / 2)| ≤ ‖a - fun j => z j + L / 2‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (a - fun j => z j + L / 2) j
    exact h2.trans h
  rw [abs_le] at hj
  constructor <;> linarith only [hj.1, hj.2, hL]

/-- Uniform Hölder bound for the smooth representatives of the convex smoothing. -/
theorem abs_sub_convexApproxSmoothRepresentative_le {z : Vec d} {L : ℝ} (hL : 0 < L) {p : ℝ}
    (hp1 : 1 < p) (hd : (d : ℝ) < p) (u : W1pFunction (axisCube z L) (ENNReal.ofReal p))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {x y : Vec d} (hx : x ∈ axisCube z L)
    (hy : y ∈ axisCube z L) :
    |convexApproxSmoothRepresentative (axisCube z L) unitConvexApproxKernel u.toFun
        (fun j => z j + L / 2) (L / 4) ε x -
      convexApproxSmoothRepresentative (axisCube z L) unitConvexApproxKernel u.toFun
        (fun j => z j + L / 2) (L / 4) ε y| ≤
      4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L))).toReal := by
  have hG := (eLpNorm_grad_lt_top hp1 u).ne
  have hv : ContDiff ℝ 1 (convexApproxSmoothRepresentative (axisCube z L) unitConvexApproxKernel
      u.toFun (fun j => z j + L / 2) (L / 4) ε) := by
    have hp1' : 1 ≤ ENNReal.ofReal p := by simpa using (ENNReal.ofReal_le_ofReal hp1.le)
    exact (contDiff_convexApproxSmoothRepresentative
      (isOpenBoundedConvexDomain_axisCube z L).isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp1' u.memLp (show (0:ℝ) < L / 4 by positivity)
      hε0).of_le (by exact_mod_cast le_top)
  have hM2 := eLpNorm_fderiv_convexApproxSmoothRepresentative_le hp1 hd u
    (closedBall_subset_axisCube hL) (show (0:ℝ) < L / 4 by positivity) hε0 hε1
  have hGr : 0 ≤ (eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L))).toReal := ENNReal.toReal_nonneg
  have hE : eLpNorm (fun w => ‖fderiv ℝ (convexApproxSmoothRepresentative (axisCube z L)
      unitConvexApproxKernel u.toFun (fun j => z j + L / 2) (L / 4) ε) w‖) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L)) ≤ ENNReal.ofReal ((d : ℝ) *
        (eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p)
          (volume.restrict (axisCube z L))).toReal) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_toReal hG]
    exact hM2
  have := abs_sub_le_morrey_axisCube hL hv hp1 hd (by positivity) hE hx hy
  calc _ ≤ _ := this
    _ = _ := by ring

end SuperdiffusionCLT.Section7
