/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedF
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRounded

/-!
# Charts of the model domain in the axis direction

At a frontier point with `(⟨e,p⟩ + h)² / h² > 1/8` the model domain is, near `p`, the region below
the graph of `w ↦ h √(1 - φ(|w|²/a²)) - σ h` in the direction `σ e`, `σ = ±1`
(`σ` the sign of `⟨e,p⟩ + h`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The graph function of the axis-direction chart. -/
noncomputable def g1b_Sgraph (a h σ : ℝ) (w : Vec d) : ℝ :=
  h * Real.sqrt (1 - g1b_phi (vecNormSq w / a ^ 2)) - σ * h

theorem g1b_Sgraph_contDiffOn (a h σ : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (g1b_Sgraph (d := d) a h σ)
      {w | g1b_phi (vecNormSq w / a ^ 2) < 1} := by
  unfold g1b_Sgraph
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun w : Vec d => 1 - g1b_phi (vecNormSq w / a ^ 2) :=
    contDiff_const.sub (g1b_phi_contDiff.comp (g1b_vecNormSq_contDiff.div_const _))
  refine ContDiffOn.sub (contDiffOn_const.mul (h1.contDiffOn.sqrt fun w hw => ?_)) contDiffOn_const
  exact (sub_pos.2 hw).ne'

theorem g1b_S_chart {e : Vec d} {a h : ℝ} (hh : 0 < h)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : Vec d} (hp : p ∈ frontier (g1b_H e a h))
    (hv : 1 / 8 < g1b_v e h p) (hσp : 0 < σ * (vecDot e p + h)) :
    ∃ (ψ : Vec d → ℝ) (W : Set (Vec d)) (r : ℝ), 0 < r ∧ IsOpen W ∧
      ContDiffOn ℝ (⊤ : ℕ∞) ψ W ∧
      ∀ y ∈ Metric.ball p r, (y - vecDot (σ • e) y • (σ • e)) ∈ W ∧
        (y ∈ g1b_H e a h ↔ vecDot (σ • e) y < ψ (y - vecDot (σ • e) y • (σ • e))) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hQ := g1b_frontier_Q hp
  have hphiv : g1b_phi (g1b_v e h p) = g1b_v e h p := g1b_phi_eq (by linarith only [hv])
  have hphiu : g1b_phi (g1b_u e a p) < 1 := by
    have : g1b_Q e a h p = g1b_phi (g1b_u e a p) + g1b_phi (g1b_v e h p) := rfl
    linarith only [this, hQ, hphiv, hv]
  let N : Set (Vec d) := {y | 1 / 8 < g1b_v e h y ∧ 0 < σ * (vecDot e y + h) ∧
    g1b_phi (g1b_u e a y) < 1}
  have hNopen : IsOpen N := by
    show IsOpen ({y | 1 / 8 < g1b_v e h y} ∩ ({y | 0 < σ * (vecDot e y + h)} ∩
      {y | g1b_phi (g1b_u e a y) < 1}))
    refine IsOpen.inter (isOpen_lt continuous_const (g1b_v_contDiff e h).continuous)
      (IsOpen.inter (isOpen_lt continuous_const ?_)
        (isOpen_lt (g1b_phi_contDiff.comp (g1b_u_contDiff e a)).continuous continuous_const))
    exact (continuous_const.mul (((g1b_vecDot_contDiff e).continuous).add continuous_const))
  have hpN : p ∈ N := ⟨hv, hσp, hphiu⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hNopen p hpN
  refine ⟨g1b_Sgraph a h σ, {w | g1b_phi (vecNormSq w / a ^ 2) < 1}, r, hr,
    isOpen_lt (g1b_phi_contDiff.comp (g1b_vecNormSq_contDiff.div_const _)).continuous
      continuous_const, g1b_Sgraph_contDiffOn a h σ, fun y hy => ?_⟩
  obtain ⟨hy1, hy2, hy3⟩ := hball hy
  rw [g1b_proj_smul hσ]
  refine ⟨hy3, ?_⟩
  have hphivy : g1b_phi (g1b_v e h y) = g1b_v e h y := g1b_phi_eq (by linarith only [hy1])
  have hGpos : 0 < 1 - g1b_phi (g1b_u e a y) := sub_pos.2 hy3
  have hs0 : 0 ≤ σ * (vecDot e y + h) / h := div_nonneg hy2.le hh.le
  have hsq : (σ * (vecDot e y + h) / h) ^ 2 = g1b_v e h y := by
    unfold g1b_v
    rw [div_pow, mul_pow, sq σ, hσ2, one_mul]
  show g1b_Q e a h y < 1 ↔ _
  rw [g1b_vecDot_smul]
  unfold g1b_Sgraph
  have hU : vecNormSq (y - vecDot e y • e) / a ^ 2 = g1b_u e a y := rfl
  rw [hU]
  have key : g1b_Q e a h y < 1 ↔ σ * (vecDot e y + h) / h < Real.sqrt (1 - g1b_phi (g1b_u e a y)) := by
    rw [Real.lt_sqrt hs0, hsq]
    unfold g1b_Q
    rw [hphivy]
    constructor <;> intro h' <;> linarith only [h']
  rw [key]
  have hrw : σ * (vecDot e y + h) / h < Real.sqrt (1 - g1b_phi (g1b_u e a y)) ↔
      σ * (vecDot e y + h) < h * Real.sqrt (1 - g1b_phi (g1b_u e a y)) := by
    rw [div_lt_iff₀ hh, mul_comm (Real.sqrt _) h]
  rw [hrw]
  constructor <;> intro h' <;> linarith only [h']

end SuperdiffusionCLT.Section7
