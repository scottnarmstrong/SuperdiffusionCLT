/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import SuperdiffusionCLT.Section7.Prereq.Domains

/-!
# The uniform `C^{1,1}` atlas of a smooth bounded domain

* `Section7.HasC11ChartAt`, `Section7.IsUniformC11Domain`: the quantitative `C^{1,1}` charts.
* `Section7.exists_isUniformC11Domain_of_isSmoothBoundedDomain`: a smooth bounded domain is
  uniformly `C^{1,1}`. The charts of `IsSmoothBoundedDomain` are globalized by a bump function
  (so the slope and gradient-Lipschitz bounds hold on the whole space), and finitely many charts
  cover the compact frontier.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}



/-- Quantitative `C^{1,1}` chart at a boundary point: a smooth graph function (globalized by a
cutoff) with slope bound `M₁` and gradient-Lipschitz bound `M₂`, describing `U` on `B(x,r)`. -/
def HasC11ChartAt (U : Set (Vec d)) (x : Vec d) (r M₁ M₂ : ℝ) : Prop :=
  ∃ (e : Vec d) (ψ : Vec d → ℝ), vecNormSq e = 1 ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
    (∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) ∧
    (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) ∧
    ∀ y ∈ Metric.ball x r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))

/-- A uniformly `C^{1,1}` bounded open set: the quantitative class in which every analytic
constant is computed (it contains every `IsSmoothBoundedDomain`, every dilate of one, and the
rounded half-cube family of `l.Dirichlet.uniform.boundary.domains`). -/
def IsUniformC11Domain (U : Set (Vec d)) (r M₁ M₂ D : ℝ) : Prop :=
  IsOpen U ∧ 0 < r ∧ (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) ∧ ∀ x ∈ frontier U, HasC11ChartAt U x r M₁ M₂

theorem HasC11ChartAt.mono {U : Set (Vec d)} {x : Vec d} {r r' M₁ M₂ M₁' M₂' : ℝ}
    (h : HasC11ChartAt U x r M₁ M₂) (hr : r' ≤ r) (h1 : M₁ ≤ M₁') (h2 : M₂ ≤ M₂') :
    HasC11ChartAt U x r' M₁' M₂' := by
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hU⟩ := h
  refine ⟨e, ψ, he, hψ, fun y => (hb1 y).trans h1, fun y z => ?_,
    fun y hy => hU y (Metric.ball_subset_ball hr hy)⟩
  exact (hb2 y z).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- A chart at `x'` of radius `r` gives a chart at any `x` within `r / 2` of `x'`, of radius
`r / 2`. -/
theorem HasC11ChartAt.of_mem_ball {U : Set (Vec d)} {x x' : Vec d} {r M₁ M₂ : ℝ}
    (h : HasC11ChartAt U x' r M₁ M₂) (hx : dist x x' < r / 2) :
    HasC11ChartAt U x (r / 2) M₁ M₂ := by
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hU⟩ := h
  refine ⟨e, ψ, he, hψ, hb1, hb2, fun y hy => hU y ?_⟩
  rw [Metric.mem_ball] at hy ⊢
  have := dist_triangle y x x'
  linarith only [this, hy, hx]

/-- A compactly supported smooth function has bounded gradient and Lipschitz gradient. -/
theorem exists_gradient_bounds {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∃ M₁ M₂ : ℝ, (∀ y, ‖fderiv ℝ φ y‖ ≤ M₁) ∧
      ∀ y z, ‖fderiv ℝ φ y - fderiv ℝ φ z‖ ≤ M₂ * ‖y - z‖ := by
  obtain ⟨M₁, hM₁⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.continuous_fderiv (by simp))
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
    WithTop.coe_le_coe.2 le_top)
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := h2.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ)) h1
    (by simp)
  refine ⟨M₁, K, hM₁, fun y z => ?_⟩
  have := hK.dist_le_mul y z
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- Globalization by a cutoff: a smooth function on an open set agrees near `p` with a smooth
compactly supported function on the whole space. -/
theorem exists_cutoff {W : Set (Vec d)} (hW : IsOpen W) {ψ : Vec d → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ W) {p : Vec d} (hp : p ∈ W) :
    ∃ (ρ : ℝ) (φ : Vec d → ℝ), 0 < ρ ∧ ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      ∀ z ∈ Metric.ball p ρ, φ z = ψ z := by
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW p hp
  let b : ContDiffBump p :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith only [hε] }
  have hsupp : ∀ z, z ∉ Metric.ball p (ε / 2) → b z = 0 := fun z hz => by
    by_contra h
    have h' : z ∈ Function.support b := h
    rw [b.support_eq] at h'
    exact hz h'
  refine ⟨ε / 4, fun z => b z * ψ z, by positivity, ?_, b.hasCompactSupport.mul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ W
    · exact (b.contDiff.contDiffAt).mul (hψ.contDiffAt (hW.mem_nhds hz))
    · have hz' : z ∉ Metric.closedBall p (ε / 2) := fun h =>
        hz (hεW (Metric.closedBall_subset_ball (by linarith only [hε]) h))
      have hev : (fun z => b z * ψ z) =ᶠ[nhds z] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hz'] with w hw
        rw [hsupp w (fun h => hw (Metric.ball_subset_closedBall h)), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro z hz
    have : b z = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    simp [this]

/-- The projection onto the hyperplane orthogonal to `e` is continuous. -/
theorem continuous_proj (e : Vec d) : Continuous fun y : Vec d => y - vecDot e y • e := by
  unfold vecDot
  fun_prop

/-- A chart at a single boundary point of a smooth bounded domain. -/
theorem exists_chart_of_isSmoothBoundedDomain {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U)
    {x : Vec d} (hx : x ∈ frontier U) :
    ∃ r M₁ M₂ : ℝ, 0 < r ∧ HasC11ChartAt U x r M₁ M₂ := by
  obtain ⟨e, ψ, W, r, he, hr, hW, hψ, hchart⟩ := hU.2.2.2 x hx
  have hxb : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hpW : x - vecDot e x • e ∈ W := (hchart x hxb).1
  obtain ⟨ρ, φ, hρ, hφ, hc, hφψ⟩ := exists_cutoff hW hψ hpW
  obtain ⟨M₁, M₂, hM₁, hM₂⟩ := exists_gradient_bounds hφ hc
  obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.1
    ((continuous_proj e).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
  refine ⟨min r' r, M₁, M₂, lt_min hr' hr, e, φ, he, hφ, hM₁, hM₂, fun y hy => ?_⟩
  have hy1 : y ∈ Metric.ball x r' := Metric.ball_subset_ball (min_le_left _ _) hy
  have hy2 : y ∈ Metric.ball x r := Metric.ball_subset_ball (min_le_right _ _) hy
  rw [hφψ _ (hsub hy1)]
  exact (hchart y hy2).2

/-- The frontier of a bounded set is compact. -/
theorem isCompact_frontier_of_isBoundedDomain {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    IsCompact (frontier U) := by
  obtain ⟨R, _, hR⟩ := hU
  have hb : Bornology.IsBounded U := by
    refine (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := R)).subset fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (by linarith only [‹0 < R›])).2 fun i => by
      simpa using hR y hy i
  exact hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

/-- ATLAS: a smooth bounded domain is uniformly `C^{1,1}`. -/
theorem exists_isUniformC11Domain_of_isSmoothBoundedDomain {U : Set (Vec d)}
    (hU : IsSmoothBoundedDomain U) :
    ∃ r M₁ M₂ D : ℝ, IsUniformC11Domain U r M₁ M₂ D := by
  classical
  have hcomp := isCompact_frontier_of_isBoundedDomain hU.2.2.1
  choose! R M₁ M₂ hR hch using fun x (hx : x ∈ frontier U) =>
    exists_chart_of_isSmoothBoundedDomain hU hx
  obtain ⟨t, htF, hcov⟩ := hcomp.elim_nhds_subcover (fun x => Metric.ball x (R x / 2))
    (fun x hx => Metric.ball_mem_nhds x (by linarith only [hR x hx]))
  obtain ⟨R0, hR0⟩ := hU.2.2.1
  obtain ⟨A₁, hA₁⟩ := Finset.exists_le (t.image M₁)
  obtain ⟨A₂, hA₂⟩ := Finset.exists_le (t.image M₂)
  obtain ⟨B, hB⟩ := Finset.exists_le (t.image fun x => (R x)⁻¹)
  have hB1 : 0 < max B 1 := lt_max_of_lt_right one_pos
  refine ⟨(max B 1)⁻¹ / 2, A₁, A₂, 2 * R0, hU.1, by positivity, ?_, fun x hx => ?_⟩
  · intro x hx y hy
    have hR0pos : 0 ≤ 2 * R0 := by
      have := hR0.1
      linarith only [this]
    refine (pi_norm_le_iff_of_nonneg hR0pos).2 fun i => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    have h1 := abs_le.1 (hR0.2 x hx i)
    have h2 := abs_le.1 (hR0.2 y hy i)
    rw [abs_le]
    constructor <;> linarith only [h1, h2]
  · obtain ⟨x', hx't, hxx'⟩ := Set.mem_iUnion₂.1 (hcov hx)
    have hx'F : x' ∈ frontier U := htF x' hx't
    have hRx' := hR x' hx'F
    have hc := (hch x' hx'F).of_mem_ball (Metric.mem_ball.1 hxx')
    have hBx : (R x')⁻¹ ≤ max B 1 :=
      (hB _ (Finset.mem_image_of_mem _ hx't)).trans (le_max_left _ _)
    have hr : (max B 1)⁻¹ / 2 ≤ R x' / 2 := by
      have := inv_anti₀ (inv_pos.2 hRx') hBx
      rw [inv_inv] at this
      linarith only [this]
    exact hc.mono hr (hA₁ _ (Finset.mem_image_of_mem _ hx't))
      (hA₂ _ (Finset.mem_image_of_mem _ hx't))

/-- Witness: the unit Euclidean ball is uniformly `C^{1,1}`. -/
theorem isUniformC11Domain_euclidBall [NeZero d] :
    ∃ r M₁ M₂ D : ℝ, IsUniformC11Domain (Section6.euclidBall (d := d) 1) r M₁ M₂ D :=
  exists_isUniformC11Domain_of_isSmoothBoundedDomain isSmoothBoundedDomain_euclidBall

end SuperdiffusionCLT.Section7
