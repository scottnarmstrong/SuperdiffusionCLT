/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueH

/-!
# Poincare inequalities: the glued domain with its shear presentation

`Section7.a10_glue_normalized`: let `V` be described near the origin, on `B(0, R)`, as the
subgraph `⟨e,y⟩ < ψ(Py)` of a smooth `ψ` with `ψ 0 = 0`, gradient bound `M` and gradient
Lipschitz constant `1`. Then there is a uniformly `C^{1,1}` domain `W` (data depending only on
`d` and `M`) with `V ∩ B(0, c₁) = W ∩ B(0, c₁)`, `W ⊆ V ∩ B(0, c₂)` and
`∂W ∩ B(0, c₁) ⊆ ∂V`, provided `c₂ ≤ R`. It also presents the glued domain as the shear preimage
`{y | shear e Ψ y ∈ g1b_H e 1 1}` of the model domain, with a slope bound `K` of `Ψ` depending only
on `d` and `M`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The glued domain of a normalized chart. -/
theorem a10_glue_normalized [NeZero d] {M : ℝ} (hM : 0 ≤ M) :
    ∃ r' M₁' M₂' D' c₁ c₂ K : ℝ, 0 < r' ∧ 0 < c₁ ∧ c₁ < c₂ ∧ 0 ≤ K ∧
      ∀ (V : Set (Vec d)) (e : Vec d) (ψ : Vec d → ℝ) (R : ℝ), vecNormSq e = 1 →
        ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y, ‖fderiv ℝ ψ y‖ ≤ M) →
        (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ 1 * ‖y - z‖) → ψ 0 = 0 → c₂ ≤ R →
        (∀ y ∈ Metric.ball (0 : Vec d) R, (y ∈ V ↔ vecDot e y < ψ (y - vecDot e y • e))) →
        ∃ W : Set (Vec d), IsUniformC11Domain W r' M₁' M₂' D' ∧
          V ∩ Metric.ball 0 c₁ = W ∩ Metric.ball 0 c₁ ∧ W ⊆ V ∩ Metric.ball 0 c₂ ∧
          frontier W ∩ Metric.ball 0 c₁ ⊆ frontier V ∧
          ∃ Ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ (∀ y, ‖fderiv ℝ Ψ y‖ ≤ K) ∧
            W = shear e Ψ ⁻¹' g1b_H e 1 1 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hd1 : (0 : ℝ) < 1 + d := by positivity
  obtain ⟨hn1, hn2, hn3, hn4⟩ := g1c_numerics (d := d) hM
  set ζ : ℝ := 1 / (4 * ((d : ℝ) + 1)) with hζdef
  set c₁ : ℝ := 1 / (16 * (1 + (d : ℝ)) ^ 2 * (1 + M)) with hc₁def
  have hζpos : 0 < ζ := by positivity
  have hc₁pos : 0 < c₁ := by positivity
  set ρ₃ : ℝ := ζ / 2 with hρ₃def
  set ρ₁ : ℝ := ζ / 4 with hρ₁def
  have hρ₃pos : 0 < ρ₃ := by positivity
  have hρ₁pos : 0 < ρ₁ := by positivity
  have hlt : ρ₃ + ρ₁ < ζ := by rw [hρ₃def, hρ₁def]; linarith only [hζpos]
  obtain ⟨χ, A₁, A₂, hχ, hA₁0, hA₂0, hA₁, hA₂, hχ01, hχ1, hχ0, hdχ0⟩ :=
    g1c_exists_cutoff (d := d) (ρ₁ := ρ₁) (ρ₃ := ρ₃) hρ₁pos (by rw [hρ₃def, hρ₁def]; linarith only [hζpos])
  obtain ⟨rH, M₁H, M₂H, DH, -, -, hrH, hHe⟩ := g1c_exists_uniform_H_dir (d := d) one_pos one_pos
  set K₁ : ℝ := (M * ρ₃ * A₁ + M) + M * A₁ with hK₁def
  set K₂ : ℝ := (M * ρ₃ * A₂ + 2 * A₁ * M + 1) + M * A₂ with hK₂def
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hΛ := g1b_Lam_pos (d := d) hK₁0
  have hr₁ := g1c_r₁_pos (d := d) (h := 1) (ρ := ρ₃) (δ := ρ₁) (ζ := ζ) one_pos hlt
  have hc₂ : c₁ < 4 + 3 * M := by linarith only [hn4, hM]
  refine ⟨min (g1c_r₁ d 1 ρ₃ ρ₁ ζ / g1b_Lam d K₁) (min rH (ρ₁ / (1 + d))), max (0 + K₁) M₁H,
    max (0 + K₂) M₂H, g1b_Lam d K₁ * DH, c₁, 4 + 3 * M, K₁, lt_min (div_pos hr₁ hΛ)
    (lt_min hrH (div_pos hρ₁pos hd1)), hc₁pos, hc₂, hK₁0, ?_⟩
  intro V e ψ R he hψ hM₁ hM₂ hψ0 hR hch
  set Ψ : Vec d → ℝ := g1c_Psi χ ψ M with hΨdef
  obtain ⟨hΨ, hK₁, hK₂, hΨc⟩ := g1c_Psi_bounds hχ hψ (A₁ := A₁) (A₂ := A₂) (M₁ := M)
    (M₂ := 1) (ρ₃ := ρ₃) (L := M) hρ₃pos.le hA₂0 zero_le_one hM hA₁ hA₂ hχ01 hχ0 hdχ0 hM₁ hM₂
    hψ0
  have hW := g1c_uniform_shear he one_pos one_pos hΨ hK₁ hK₂ hΨc hρ₁pos hlt hn1 (hHe e he)
  -- the inner description
  have hin : ∀ y ∈ Metric.ball (0 : Vec d) c₁, (y ∈ V ↔ shear e Ψ y ∈ g1b_H e 1 1) := by
    intro y hy
    have hyn : ‖y‖ < c₁ := by rwa [mem_ball_zero_iff] at hy
    have hyR : y ∈ Metric.ball (0 : Vec d) R := by
      rw [mem_ball_zero_iff]; linarith only [hyn, hc₂, hR]
    have hP : ‖y - vecDot e y • e‖ ≤ ρ₁ := by
      have h1 := g1c_norm_proj_le he y
      have h2 := mul_le_mul_of_nonneg_left hyn.le hd1.le
      linarith only [h1, h2, hn2]
    have hΨy : Ψ (y - vecDot e y • e) = ψ (y - vecDot e y • e) :=
      g1c_Psi_eq_of_one (hχ1 _ hP)
    have hflat := g1c_mem_flat he (Ψ := Ψ) hn1
      (hP.trans (by rw [hρ₁def]; linarith only [hζpos]))
    rw [hflat, hΨy, hch y hyR]
    have hb1 := abs_vecDot_le he y
    have hb2 := g1c_abs_le_of_zero hψ hM₁ hψ0 (y - vecDot e y • e)
    have hb3 := g1c_norm_proj_le he y
    have hb4 : M * ‖y - vecDot e y • e‖ ≤ M * ((1 + d) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hb3 hM
    have hb5 : (1 + (d : ℝ)) * (1 + M) * ‖y‖ ≤ (1 + d) * (1 + M) * c₁ :=
      mul_le_mul_of_nonneg_left hyn.le (by positivity)
    have hb6 := (abs_le.1 hb1).1
    have hb7 := (abs_le.1 hb2).2
    have hlow : -2 < vecDot e y - ψ (y - vecDot e y • e) := by
      nlinarith only [hb6, hb7, hb4, hb5, hn3, hd0, hM, norm_nonneg y]
    constructor
    · intro h
      exact ⟨hlow, by linarith only [h]⟩
    · rintro ⟨-, h⟩
      linarith only [h]
  have hout : ∀ y, shear e Ψ y ∈ g1b_H e 1 1 → y ∈ V ∧ ‖y‖ < 4 + 3 * M := by
    intro y hy
    obtain ⟨hP1, h1, h2⟩ := g1c_mem_bound he (Ψ := Ψ) hy
    have hψb : |ψ (y - vecDot e y • e)| ≤ M := by
      have := g1c_abs_le_of_zero hψ hM₁ hψ0 (y - vecDot e y • e)
      have h3 := mul_le_mul_of_nonneg_left hP1 hM
      linarith only [this, h3]
    have hΨb := g1c_abs_Psi_le (χ := χ) (ψ := ψ) (L := M) (w := y - vecDot e y • e)
      (hχ01 _).1 (hχ01 _).2 hM hψb
    have hnorm := g1c_norm_le_proj_add he y
    have habs1 := (abs_le.1 hΨb).2
    have habs2 := (abs_le.1 hΨb).1
    have hdot : |vecDot e y| ≤ 2 + (M + 2 * M) := by
      rw [abs_le]
      constructor <;> linarith only [h1, h2, habs1, habs2]
    have hlt' : ‖y‖ < 4 + 3 * M := by linarith only [hnorm, hdot, hP1]
    refine ⟨?_, hlt'⟩
    have hyR : y ∈ Metric.ball (0 : Vec d) R := by
      rw [mem_ball_zero_iff]; linarith only [hlt', hR]
    rw [hch y hyR]
    have hle := g1c_Psi_le (χ := χ) (ψ := ψ) (L := M) (w := y - vecDot e y • e)
      (hχ01 _).2 (by linarith only [(abs_le.1 hψb).1])
    linarith only [h2, hle]
  have hset : V ∩ Metric.ball 0 c₁ = {y | shear e Ψ y ∈ g1b_H e 1 1} ∩ Metric.ball 0 c₁ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hy, hb⟩
      exact ⟨(hin y hb).1 hy, hb⟩
    · rintro ⟨hy, hb⟩
      exact ⟨(hin y hb).2 hy, hb⟩
  refine ⟨{y | shear e Ψ y ∈ g1b_H e 1 1}, hW, hset, fun y hy => ?_, ?_, Ψ, hΨ, hK₁, rfl⟩
  · have := hout y hy
    exact ⟨this.1, by rw [mem_ball_zero_iff]; exact this.2⟩
  · intro x ⟨hx, hxb⟩
    have h1 := frontier_inter_open_inter (s := {y : Vec d | shear e Ψ y ∈ g1b_H e 1 1})
      (Metric.isOpen_ball (x := (0 : Vec d)) (ε := c₁))
    have h2 := frontier_inter_open_inter (s := V)
      (Metric.isOpen_ball (x := (0 : Vec d)) (ε := c₁))
    rw [← hset] at h1
    have h3 : x ∈ frontier {y : Vec d | shear e Ψ y ∈ g1b_H e 1 1} ∩ Metric.ball 0 c₁ :=
      ⟨hx, hxb⟩
    rw [← h1, h2] at h3
    exact h3.1

end SuperdiffusionCLT.Section7
