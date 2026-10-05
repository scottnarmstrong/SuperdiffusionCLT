/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.MollifierC
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaC

/-!
# The mollified flux and gradient: deterministic estimates

For `x` in the cube `□_n` the
mollification `η_n ∗ F` at `x` of a vector field with square integrable components on `□_{n+1}` is
bounded by a constant times the scale-normalized `H̲^{-1/4}` norm of `F` on `□_{n+1}`
(`m1_mollify_dual_le`), and the mollification is linear (`m1_mollify_add`), which gives the full
flux bound `a ∇u = (a - S Id) ∇u + S ∇u` (`m1_mollify_fullflux_le`).
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The sup-ball of radius `3^n` around a point of `□_n` lies in `□_{n+1}`. -/
theorem m1_ball_subset (n : ℕ) {x : Vec d} (hx : x ∈ cubeSet (originCube d (n : ℤ))) :
    ∀ y, dist y x ≤ (3 : ℝ) ^ (n : ℤ) → y ∈ cubeSet (originCube d ((n + 1 : ℕ) : ℤ)) := by
  intro y hy
  have hh : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  intro i
  have hyi : |y i - x i| ≤ (3 : ℝ) ^ (n : ℤ) := by
    have := (dist_pi_le_iff hh.le).1 hy i
    rwa [Real.dist_eq] at this
  rw [abs_le] at hyi
  obtain ⟨hx1, hx2⟩ := hx i
  have h3 : (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ)) = 3 * (3 : ℝ) ^ (n : ℤ) := by
    rw [Nat.cast_succ, zpow_add_one₀ (by norm_num), mul_comm]
  rw [h3]
  constructor <;> nlinarith only [hyi.1, hyi.2, hx1, hx2]

/-- The kernel centered at `x` is integrable against an `L²` function of the cube. -/
theorem m1_integrable_kernel_mul (Q : TriadicCube d) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    {A : ℝ} {L : NNReal} (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : ∀ y, dist y x ≤ h → y ∈ cubeSet Q) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Integrable (fun y => a16_kernel d h η (x - y) * f y) volume := by
  set g : Vec d → ℝ := fun y => a16_kernel d h η (x - y) with hg
  have hgc : Continuous g :=
    (a16_kernel_continuous hL.continuous).comp (continuous_const.sub continuous_id)
  have hM : ∀ y, |g y| ≤ A * (h⁻¹) ^ d := fun y => a16_kernel_abs_le hh hA _
  have hsupp : ∀ y, y ∉ cubeSet Q → g y = 0 := by
    intro y hy
    by_contra hne
    refine hy (hx y ?_)
    rw [dist_pi_le_iff hh.le]
    intro i
    by_contra hlt
    push Not at hlt
    apply hne
    refine a16_kernel_eq_zero hh hη (w := x - y) (i := i) ?_
    rw [Real.dist_eq] at hlt
    simpa only [Pi.sub_apply, abs_sub_comm] using hlt
  have hfin : IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
  have hfμ : MemLp f 2 (volume.restrict (cubeSet Q)) := by
    have e : normalizedCubeMeasure Q =
        ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (cubeSet Q) := rfl
    rw [e] at hf
    refine MemLp.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q)) ENNReal.ofReal_ne_top
      (le_of_eq ?_) hf
    rw [smul_smul, ← ENNReal.ofReal_mul (cubeVolume_pos Q).le, mul_inv_cancel₀ (cubeVolume_pos Q).ne',
      ENNReal.ofReal_one, one_smul]
  have hgμ : MemLp g 2 (volume.restrict (cubeSet Q)) :=
    MemLp.of_bound hgc.aestronglyMeasurable (A * (h⁻¹) ^ d)
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y)
  have hint : Integrable (fun y => g y * f y) (volume.restrict (cubeSet Q)) := hgμ.integrable_mul hfμ
  refine (integrableOn_iff_integrable_of_support_subset (s := cubeSet Q) ?_).1 hint
  intro y hy
  by_contra hyQ
  have h0 : a16_kernel d h η (x - y) = 0 := hsupp y hyQ
  exact hy (by show a16_kernel d h η (x - y) * f y = 0; rw [h0, zero_mul])

/-- Linearity of the mollification. -/
theorem m1_mollify_add (Q : TriadicCube d) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    {A : ℝ} {L : NNReal} (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : ∀ y, dist y x ≤ h → y ∈ cubeSet Q) {F G : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun y => G y i) 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    a16_mollify d h η (fun y => F y + c • G y) x =
      a16_mollify d h η F x + c • a16_mollify d h η G x := by
  funext i
  have h1 := m1_integrable_kernel_mul Q hh hA hL hη hx (hF i)
  have h2 := (m1_integrable_kernel_mul Q hh hA hL hη hx (hG i)).const_mul c
  simp only [a16_mollify, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- **The elementary mollifier estimate on the cube `□_{n+1}`**, for a point `x` of
`□_n`: `‖η_n ∗ F (x)‖ ≤ 3^d (6L + A) ‖F‖_{H̲^{-1/4}(□_{n+1})}`. -/
theorem m1_mollify_dual_le (n : ℕ) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure (originCube d ((n + 1 : ℕ) : ℤ)))) :
    ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η F x‖ ≤ 3 ^ d * (6 * (L : ℝ) + A) *
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4) F := by
  have hh : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  have hc : cubeScaleFactor (originCube d ((n + 1 : ℕ) : ℤ)) = 3 * (3 : ℝ) ^ (n : ℤ) := by
    unfold cubeScaleFactor originCube
    simp only
    rw [Nat.cast_succ, zpow_add_one₀ (by norm_num), mul_comm]
  exact mollifier_norm_le_dualNegativeBesov _ hh hc hA hL hη (m1_ball_subset n hx) hF

/-- The mollified flux defect `η_n ∗ ((a - S Id) ∇u)` at a point of `□_n`. -/
theorem m1_mollify_flux_le (n : ℕ) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) a) (S : ℝ)
    (u : H1Function (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ)))) :
    ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun y => matVecMul (a y - S • (1 : Mat d)) (u.grad y)) x‖ ≤
      3 ^ d * (6 * (L : ℝ) + A) *
        Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4)
          (fun y => matVecMul (a y - S • (1 : Mat d)) (u.grad y)) :=
  m1_mollify_dual_le n hA hL hη hx fun i =>
    memLp_component_of_memLp (Q := originCube d ((n + 1 : ℕ) : ℤ)) _ i (r1_memLp_flux _ hEll S u)

/-- The mollified gradient `η_n ∗ ∇u` at a point of `□_n`. -/
theorem m1_mollify_grad_le (n : ℕ) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ)))
    (u : H1Function (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ)))) :
    ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η u.grad x‖ ≤ 3 ^ d * (6 * (L : ℝ) + A) *
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4) u.grad :=
  m1_mollify_dual_le n hA hL hη hx fun i => r1_memLp_grad_comp _ u i

/-- The mollified full flux `η_n ∗ (a ∇u)` at a point of `□_n`: the flux defect plus `S` times the
gradient. -/
theorem m1_mollify_fullflux_le (n : ℕ) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (n : ℤ))) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) a) {S : ℝ}
    (hS : 0 ≤ S) (u : H1Function (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ)))) :
    ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun y => matVecMul (a y) (u.grad y)) x‖ ≤
      3 ^ d * (6 * (L : ℝ) + A) *
        Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4)
          (fun y => matVecMul (a y - S • (1 : Mat d)) (u.grad y)) +
      S * (3 ^ d * (6 * (L : ℝ) + A) *
        Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d ((n + 1 : ℕ) : ℤ)) (1 / 4) u.grad) := by
  have hF : ∀ i, MemLp (fun y => matVecMul (a y - S • (1 : Mat d)) (u.grad y) i) 2
      (normalizedCubeMeasure (originCube d ((n + 1 : ℕ) : ℤ))) := fun i =>
    memLp_component_of_memLp (Q := originCube d ((n + 1 : ℕ) : ℤ)) _ i (r1_memLp_flux _ hEll S u)
  have hG : ∀ i, MemLp (fun y => u.grad y i) 2
      (normalizedCubeMeasure (originCube d ((n + 1 : ℕ) : ℤ))) := fun i =>
    r1_memLp_grad_comp _ u i
  have e : (fun y => matVecMul (a y) (u.grad y)) =
      fun y => matVecMul (a y - S • (1 : Mat d)) (u.grad y) + S • u.grad y := by
    funext y
    rw [r1_matVecMul_sub_smul_one, sub_add_cancel]
  have hh : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  rw [e, m1_mollify_add _ hh hA hL hη (m1_ball_subset n hx) hF hG]
  refine (norm_add_le _ _).trans (add_le_add (m1_mollify_flux_le n hA hL hη hx hEll S u) ?_)
  rw [norm_smul, Real.norm_of_nonneg hS]
  exact mul_le_mul_of_nonneg_left (m1_mollify_grad_le n hA hL hη hx u) hS

end SuperdiffusionCLT.Section7
