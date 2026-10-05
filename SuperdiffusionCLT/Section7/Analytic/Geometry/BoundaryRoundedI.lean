/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedH

/-!
# The radial chart of the model domain
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The graph function of the radial chart. -/
noncomputable def g1b_Rgraph (e : Vec d) (a h : ℝ) (z : Vec d) : ℝ :=
  Real.sqrt (a ^ 2 * (1 - g1b_phi (g1b_v e h z)) - vecNormSq (z - vecDot e z • e))

/-- The set where the radial chart is defined. -/
def g1b_Rset (e : Vec d) (a h : ℝ) : Set (Vec d) :=
  {z | vecNormSq (z - vecDot e z • e) < a ^ 2 * (1 - g1b_phi (g1b_v e h z))}

theorem g1b_Rfun_contDiff (e : Vec d) (a h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun z : Vec d =>
      a ^ 2 * (1 - g1b_phi (g1b_v e h z)) - vecNormSq (z - vecDot e z • e) :=
  (contDiff_const.mul (contDiff_const.sub (g1b_phi_contDiff.comp (g1b_v_contDiff e h)))).sub
    (g1b_vecNormSq_contDiff.comp (g1b_proj_contDiff e))

theorem g1b_isOpen_Rset (e : Vec d) (a h : ℝ) : IsOpen (g1b_Rset e a h) := by
  have := (g1b_Rfun_contDiff e a h).continuous
  have h2 : IsOpen {z : Vec d | 0 < a ^ 2 * (1 - g1b_phi (g1b_v e h z)) -
      vecNormSq (z - vecDot e z • e)} := isOpen_lt continuous_const this
  convert h2 using 1
  ext z
  simp only [g1b_Rset, Set.mem_ofPred_eq, sub_pos]

theorem g1b_Rgraph_contDiffOn (e : Vec d) (a h : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (g1b_Rgraph e a h) (g1b_Rset e a h) := by
  unfold g1b_Rgraph
  refine ((g1b_Rfun_contDiff e a h).contDiffOn).sqrt fun z hz => ?_
  have : vecNormSq (z - vecDot e z • e) < a ^ 2 * (1 - g1b_phi (g1b_v e h z)) := hz
  exact (sub_pos.2 this).ne'

theorem g1b_R_chart {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a)
    {p : Vec d} (hp : p ∈ frontier (g1b_H e a h)) (hv : g1b_v e h p ≤ 1 / 8) :
    ∃ (e' : Vec d) (ψ : Vec d → ℝ) (W : Set (Vec d)) (r : ℝ), vecNormSq e' = 1 ∧ 0 < r ∧
      IsOpen W ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ W ∧
      ∀ y ∈ Metric.ball p r, (y - vecDot e' y • e') ∈ W ∧
        (y ∈ g1b_H e a h ↔ vecDot e' y < ψ (y - vecDot e' y • e')) := by
  have hQ := g1b_frontier_Q hp
  have hQ' : g1b_phi (g1b_u e a p) + g1b_phi (g1b_v e h p) = 1 := hQ
  have hφv : g1b_phi (g1b_v e h p) ≤ 1 / 8 :=
    (g1b_phi_le (g1b_v_nonneg e h p)).trans hv
  have hu1 : 1 / 8 < g1b_u e a p := by
    have := g1b_phi_le (g1b_u_nonneg (a := a) e p)
    linarith only [this, hQ', hφv]
  have ha2 : 0 < a ^ 2 := by positivity
  set m := vecNormSq (p - vecDot e p • e) with hmdef
  have hm : 0 < m := by
    have h1 : 0 < m / a ^ 2 := by
      have : g1b_u e a p = m / a ^ 2 := rfl
      linarith only [hu1, this]
    exact (div_pos_iff_of_pos_right ha2).1 h1
  set c := (Real.sqrt m)⁻¹ with hcdef
  have hc : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hm)
  have hc2 : c ^ 2 * m = 1 := by
    rw [hcdef, inv_pow, Real.sq_sqrt hm.le]
    field_simp
  set e' : Vec d := c • (p - vecDot e p • e) with he'def
  have he' : vecNormSq e' = 1 := by
    rw [he'def, g1b_vecNormSq_smul']
    exact hc2
  have hee : vecDot e e' = 0 := by
    rw [he'def, g1b_vecDot_comm, g1b_vecDot_smul, g1b_vecDot_comm,
      g1b_vecDot_sub_smul_right]
    have : vecDot e e = 1 := he
    rw [this]
    simp
  have hz1 : ∀ y : Vec d, vecDot e (y - vecDot e' y • e') = vecDot e y := fun y => by
    rw [g1b_vecDot_sub_smul_right, hee, mul_zero, sub_zero]
  have hzv : ∀ y : Vec d, g1b_v e h (y - vecDot e' y • e') = g1b_v e h y := fun y => by
    unfold g1b_v
    rw [hz1]
  have hxp : vecDot e' p = c * m := by
    rw [he'def, g1b_vecDot_smul, g1b_vecDot_sub_smul_left, hmdef, g1b_normSq_proj he]
    have : vecDot p p = vecNormSq p := rfl
    rw [this]
    have h2 : vecDot e p * vecDot e p = vecDot e p ^ 2 := (sq _).symm
    rw [h2]
  have hxpos : 0 < vecDot e' p := by rw [hxp]; exact mul_pos hc hm
  have hsplit_p := g1b_normSq_proj_split he he' hee p
  have hPz : vecNormSq ((p - vecDot e' p • e') - vecDot e (p - vecDot e' p • e') • e) = 0 := by
    have h3 : vecDot e' p ^ 2 = m := by
      rw [hxp]
      calc (c * m) ^ 2 = (c ^ 2 * m) * m := by ring
        _ = m := by rw [hc2, one_mul]
    rw [hmdef] at hm
    linarith only [hsplit_p, h3]
  let N : Set (Vec d) := {y | 1 / 8 < g1b_u e a y ∧ 0 < vecDot e' y ∧
    (y - vecDot e' y • e') ∈ g1b_Rset e a h}
  have hNopen : IsOpen N := by
    show IsOpen ({y | 1 / 8 < g1b_u e a y} ∩ ({y | 0 < vecDot e' y} ∩
      {y | (y - vecDot e' y • e') ∈ g1b_Rset e a h}))
    have hz : Continuous fun y : Vec d => y - vecDot e' y • e' :=
      (g1b_proj_contDiff e').continuous
    exact IsOpen.inter (isOpen_lt continuous_const (g1b_u_contDiff e a).continuous)
      (IsOpen.inter (isOpen_lt continuous_const (g1b_vecDot_contDiff e').continuous)
        ((g1b_isOpen_Rset e a h).preimage hz))
  have hpN : p ∈ N := by
    refine ⟨hu1, hxpos, ?_⟩
    show vecNormSq _ < _
    rw [hPz, hzv]
    have := mul_pos ha2 (show 0 < 1 - g1b_phi (g1b_v e h p) by linarith only [hφv])
    exact this
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hNopen p hpN
  refine ⟨e', g1b_Rgraph e a h, g1b_Rset e a h, r, he', hr, g1b_isOpen_Rset e a h,
    g1b_Rgraph_contDiffOn e a h, fun y hy => ?_⟩
  obtain ⟨hy1, hy2, hy3⟩ := hball hy
  refine ⟨hy3, ?_⟩
  have hy3' : vecNormSq ((y - vecDot e' y • e') - vecDot e (y - vecDot e' y • e') • e)
      < a ^ 2 * (1 - g1b_phi (g1b_v e h (y - vecDot e' y • e'))) := hy3
  rw [hz1] at hy3'
  rw [hzv] at hy3'
  have hRpos : 0 < a ^ 2 * (1 - g1b_phi (g1b_v e h y)) - vecNormSq
      ((y - vecDot e' y • e') - vecDot e y • e) := sub_pos.2 hy3'
  have hsp := g1b_normSq_proj_split he he' hee y
  rw [hz1] at hsp
  show g1b_Q e a h y < 1 ↔ _
  unfold g1b_Rgraph
  rw [hz1, hzv, Real.lt_sqrt hy2.le]
  have hu : g1b_u e a y = (vecDot e' y ^ 2 + vecNormSq ((y - vecDot e' y • e') -
      vecDot e y • e)) / a ^ 2 := by
    unfold g1b_u
    rw [hsp]
  have hphi : g1b_phi (g1b_u e a y) = g1b_u e a y := g1b_phi_eq hy1.le
  unfold g1b_Q
  rw [hphi, hu, ← lt_sub_iff_add_lt, div_lt_iff₀ ha2]
  constructor <;> intro h' <;> linarith only [h']

end SuperdiffusionCLT.Section7
