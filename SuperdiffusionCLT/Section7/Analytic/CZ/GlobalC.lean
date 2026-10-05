/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.GlobalB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Analytic.Geometry.Atlas

/-!
# The global estimate `cz_unif`

* `cz_unif`: for `1 < p < ∞`, uniformly `C^{1,1}` domains, `W^{-1,p}` plus divergence data.
  For `p ≤ 2` it is the duality step on top of `cz_unif_div` at `p'`; for `p > 2` the duality step
  is applied with the `p' < 2` estimate (the previous case with zero scalar data).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The case `1 < p ≤ 2`. -/
theorem p14g_low (hd : 2 ≤ d) {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p ≤ 2) (M₁ κ ρ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {U : Set (Vec d)} {r M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D → r * M₂ ≤ κ → D ≤ ρ * r →
        ∀ (F : Vec d → Vec d) (h : Vec d → ℝ) (φ : H10Function U), MemVectorL2 U F →
          IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function h F →
          lpBar U p φ.toH1Function.grad ≤
            ENNReal.ofReal C * (lpBar U p F + wMinusOneBar U p h) := by
  have : NeZero d := ⟨by omega⟩
  have hpt : p ≠ ∞ := ne_top_of_le_ne_top (by simp) hp2
  obtain ⟨hq1, hqt, -, hq2, -⟩ := p14g_conj_facts hp1 hpt
  obtain ⟨Cq, hCq, H⟩ := cz_unif_div hd (hq2 hp2) hqt.lt_top M₁ κ ρ
  refine ⟨Cq * max 1 (d : ℝ), mul_pos hCq (lt_of_lt_of_le one_pos (le_max_left _ _)), ?_⟩
  intro U r M₂ D hU hκ hρ F h φ hF hφ
  exact p14g_step hU.1 (p14g_isBoundedDomain hU) hp1 hpt hCq
    (fun G ψ hG hψ => H hU hκ hρ G ψ hG hψ) φ hF hφ

/-- **CZ-UNIF.** Uniform global Calderón–Zygmund estimate for the Laplacian, `W^{-1,p}` plus
divergence data, on uniformly `C^{1,1}` domains, every `1 < p < ∞`. -/
theorem cz_unif (hd : 2 ≤ d) :
    ∀ (p : ℝ≥0∞), 1 < p → p < ⊤ → ∀ (M₁ κ ρ : ℝ), ∃ C : ℝ, 0 < C ∧
      ∀ {U : Set (Vec d)} {r M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D → r * M₂ ≤ κ →
        D ≤ ρ * r →
        ∀ (F : Vec d → Vec d) (h : Vec d → ℝ) (φ : H10Function U),
          MemVectorL2 U F → MemScalarL2 U h →
          IsWeakSolutionOn (fun _ => 1) U φ.toH1Function h F →
          lpBar U p φ.toH1Function.grad ≤ ENNReal.ofReal C * (lpBar U p F + wMinusOneBar U p h) := by
  intro p hp1 hpt M₁ κ ρ
  have : NeZero d := ⟨by omega⟩
  rcases le_or_gt p 2 with hp2 | hp2
  · obtain ⟨C, hC, H⟩ := p14g_low hd hp1 hp2 M₁ κ ρ
    exact ⟨C, hC, fun hU hκ hρ F h φ hF _ hφ => H hU hκ hρ F h φ hF hφ⟩
  · obtain ⟨hq1, hqt, hqq, -, hq2⟩ := p14g_conj_facts hp1 hpt.ne
    have hq2' := hq2 hp2.le
    obtain ⟨Cl, hCl, Hl⟩ := p14g_low hd hq1 hq2' M₁ κ ρ
    refine ⟨Cl * max 1 (d : ℝ), mul_pos hCl (lt_of_lt_of_le one_pos (le_max_left _ _)), ?_⟩
    intro U r M₂ D hU hκ hρ F h φ hF _ hφ
    have := p14g_step (Cq := Cl) hU.1 (p14g_isBoundedDomain hU) hp1 hpt.ne hCl
      (fun G ψ hG hψ => by
        have h0 := Hl hU hκ hρ G (fun _ => 0) ψ hG hψ
        rw [p14g_wMinusOneBar_zero, add_zero] at h0
        exact h0) φ hF hφ
    exact this

end SuperdiffusionCLT.Section7
