/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# The model domain with a flat top and a flat bottom

For a unit vector `e` and parameters `a, h > 0`, put `P y = y - ⟨e,y⟩ e` and
`H = {y | φ(|P y|² / a²) + φ((⟨e,y⟩ + h)² / h²) < 1}`, where `φ` is the smooth nondecreasing
function `φ(u) = u · smoothTransition(16 (u - 1/16))`: `φ = 0` on `u ≤ 1/16` and `φ(u) = u`
for `u ≥ 1/8`. Then `H` is a bounded, connected, open body of revolution about the axis `e`
whose boundary contains the flat discs `{⟨e,y⟩ = 0, |P y|² ≤ a²/16}` and
`{⟨e,y⟩ = -2h, |P y|² ≤ a²/16}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The profile `φ(u) = u · smoothTransition(16 (u - 1/16))`. -/
noncomputable def g1b_phi (u : ℝ) : ℝ := u * Real.smoothTransition ((u - 1 / 16) * 16)

theorem g1b_phi_contDiff : ContDiff ℝ (⊤ : ℕ∞) g1b_phi := by
  unfold g1b_phi
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).mul contDiff_const))

theorem g1b_phi_zero {u : ℝ} (hu : u ≤ 1 / 16) : g1b_phi u = 0 := by
  unfold g1b_phi
  rw [Real.smoothTransition.zero_of_nonpos (by linarith only [hu]), mul_zero]

theorem g1b_phi_eq {u : ℝ} (hu : 1 / 8 ≤ u) : g1b_phi u = u := by
  unfold g1b_phi
  rw [Real.smoothTransition.one_of_one_le (by linarith only [hu]), mul_one]

theorem g1b_phi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ g1b_phi u :=
  mul_nonneg hu (Real.smoothTransition.nonneg _)

theorem g1b_phi_le {u : ℝ} (hu : 0 ≤ u) : g1b_phi u ≤ u := by
  unfold g1b_phi
  calc u * Real.smoothTransition ((u - 1 / 16) * 16) ≤ u * 1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) hu
    _ = u := mul_one u

theorem g1b_phi_mono {u u' : ℝ} (hu : 0 ≤ u) (huu : u ≤ u') : g1b_phi u ≤ g1b_phi u' := by
  unfold g1b_phi
  exact mul_le_mul huu (Real.smoothTransition.monotone (by linarith only [huu]))
    (Real.smoothTransition.nonneg _) (hu.trans huu)

theorem g1b_phi_lt_one_iff {u : ℝ} (hu : 0 ≤ u) : g1b_phi u < 1 ↔ u < 1 := by
  constructor
  · intro h
    by_contra hc
    have h1 : 1 ≤ u := not_lt.1 hc
    rw [g1b_phi_eq (by linarith only [h1])] at h
    linarith only [h, h1]
  · intro h
    exact lt_of_le_of_lt (g1b_phi_le hu) h

theorem g1b_phi_eq_one {u : ℝ} (hu : 0 ≤ u) (h : g1b_phi u = 1) : u = 1 := by
  have h1 : ¬ u < 1 := fun hlt => by
    have := (g1b_phi_lt_one_iff hu).2 hlt
    linarith only [this, h]
  have h2 : 1 ≤ u := not_lt.1 h1
  rw [g1b_phi_eq (by linarith only [h2])] at h
  exact h

/-- `|P y|² / a²`. -/
noncomputable def g1b_u (e : Vec d) (a : ℝ) (y : Vec d) : ℝ :=
  vecNormSq (y - vecDot e y • e) / a ^ 2

/-- `(⟨e,y⟩ + h)² / h²`. -/
noncomputable def g1b_v (e : Vec d) (h : ℝ) (y : Vec d) : ℝ := (vecDot e y + h) ^ 2 / h ^ 2

/-- The defining function of the model domain. -/
noncomputable def g1b_Q (e : Vec d) (a h : ℝ) (y : Vec d) : ℝ :=
  g1b_phi (g1b_u e a y) + g1b_phi (g1b_v e h y)

/-- The model domain. -/
def g1b_H (e : Vec d) (a h : ℝ) : Set (Vec d) := {y | g1b_Q e a h y < 1}

theorem g1b_vecNormSq_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => vecNormSq w) := by
  unfold vecNormSq vecDot
  fun_prop

theorem g1b_vecDot_contDiff (e : Vec d) : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => vecDot e w) := by
  unfold vecDot
  fun_prop

theorem g1b_proj_contDiff (e : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y - vecDot e y • e) :=
  contDiff_id.sub ((g1b_vecDot_contDiff e).smul contDiff_const)

theorem g1b_u_contDiff (e : Vec d) (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (g1b_u e a) := by
  unfold g1b_u
  exact (g1b_vecNormSq_contDiff.comp (g1b_proj_contDiff e)).div_const _

theorem g1b_v_contDiff (e : Vec d) (h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (g1b_v e h) := by
  unfold g1b_v
  exact (((g1b_vecDot_contDiff e).add contDiff_const).pow 2).div_const _

theorem g1b_Q_contDiff (e : Vec d) (a h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (g1b_Q e a h) :=
  (g1b_phi_contDiff.comp (g1b_u_contDiff e a)).add (g1b_phi_contDiff.comp (g1b_v_contDiff e h))

theorem g1b_isOpen_H (e : Vec d) (a h : ℝ) : IsOpen (g1b_H e a h) :=
  isOpen_lt (g1b_Q_contDiff e a h).continuous continuous_const

theorem g1b_u_nonneg (e : Vec d) {a : ℝ} (y : Vec d) : 0 ≤ g1b_u e a y :=
  div_nonneg (vecNormSq_nonneg _) (sq_nonneg _)

theorem g1b_v_nonneg (e : Vec d) (h : ℝ) (y : Vec d) : 0 ≤ g1b_v e h y :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem g1b_Q_ge_left (e : Vec d) {a : ℝ} (h : ℝ) (y : Vec d) :
    g1b_phi (g1b_u e a y) ≤ g1b_Q e a h y := by
  have := g1b_phi_nonneg (g1b_v_nonneg e h y)
  unfold g1b_Q
  linarith only [this]

theorem g1b_Q_ge_right (e : Vec d) (a : ℝ) {h : ℝ} (y : Vec d) :
    g1b_phi (g1b_v e h y) ≤ g1b_Q e a h y := by
  have := g1b_phi_nonneg (g1b_u_nonneg (a := a) e y)
  unfold g1b_Q
  linarith only [this]

/-- Points of the model domain have `|P y|² < a²` and `|⟨e,y⟩ + h| < h`. -/
theorem g1b_mem_H_iff_lt {e : Vec d} {a h : ℝ} {y : Vec d} (hy : y ∈ g1b_H e a h) :
    g1b_u e a y < 1 ∧ g1b_v e h y < 1 := by
  have h1 : g1b_Q e a h y < 1 := hy
  exact ⟨(g1b_phi_lt_one_iff (g1b_u_nonneg e y)).1 (lt_of_le_of_lt (g1b_Q_ge_left e h y) h1),
    (g1b_phi_lt_one_iff (g1b_v_nonneg e h y)).1 (lt_of_le_of_lt (g1b_Q_ge_right e a y) h1)⟩

/-- The frontier of the model domain lies in `{Q = 1}`. -/
theorem g1b_frontier_Q {e : Vec d} {a h : ℝ} {x : Vec d} (hx : x ∈ frontier (g1b_H e a h)) :
    g1b_Q e a h x = 1 := by
  have hcl : closure (g1b_H e a h) ⊆ {y | g1b_Q e a h y ≤ 1} :=
    closure_minimal (fun y hy => le_of_lt (show g1b_Q e a h y < 1 from hy))
      (isClosed_le (g1b_Q_contDiff e a h).continuous continuous_const)
  rw [(g1b_isOpen_H e a h).frontier_eq] at hx
  have h1 : g1b_Q e a h x ≤ 1 := hcl hx.1
  have h2 : ¬ g1b_Q e a h x < 1 := hx.2
  exact le_antisymm h1 (not_lt.1 h2)

/-- In the flat zone `|P y|² ≤ a²/16`, the model domain is the slab `-2h < ⟨e,y⟩ < 0`. -/
theorem g1b_mem_H_flat {e : Vec d} {a h : ℝ} (hh : 0 < h) {y : Vec d}
    (hy : g1b_u e a y ≤ 1 / 16) :
    y ∈ g1b_H e a h ↔ -(2 * h) < vecDot e y ∧ vecDot e y < 0 := by
  show g1b_Q e a h y < 1 ↔ _
  unfold g1b_Q
  rw [g1b_phi_zero hy, zero_add, g1b_phi_lt_one_iff (g1b_v_nonneg e h y)]
  unfold g1b_v
  rw [div_lt_one (by positivity), sq_lt_sq, abs_of_pos hh, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

end SuperdiffusionCLT.Section7
