/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.Global

/-!
# Global estimate on a fixed domain, from the divergence-form estimate at the conjugate exponent

`p14g_step` turns the divergence-form estimate at `p'` (on a fixed bounded open set) into the
estimate at `p` for `W^{-1,p}` plus divergence data in the shape `C * (lpBar F + wMinusOneBar h)`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p14g_step [NeZero d] {U : Set (Vec d)} (hUo : IsOpen U) (hUb : IsBoundedDomain U)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) {Cq : ℝ} (hCq : 0 < Cq)
    (hq : ∀ (G : Vec d → Vec d) (ψ : H10Function U), MemVectorL2 U G →
      IsWeakSolutionOn (fun _ => (1 : Mat d)) U ψ.toH1Function 0 G →
      lpBar U p.conjExponent ψ.toH1Function.grad ≤
        ENNReal.ofReal Cq * lpBar U p.conjExponent G)
    {h : Vec d → ℝ} {F : Vec d → Vec d} (φ : H10Function U) (hF : MemVectorL2 U F)
    (hφ : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function h F) :
    lpBar U p φ.toH1Function.grad ≤
      ENNReal.ofReal (Cq * max 1 (d : ℝ)) * (lpBar U p F + wMinusOneBar U p h) := by
  rcases U.eq_empty_or_nonempty with hU | hne
  · subst hU
    simp [p14g_lpBar_empty]
  have hCpos : 0 < Cq * max 1 (d : ℝ) :=
    mul_pos hCq (lt_of_lt_of_le one_pos (le_max_left _ _))
  by_cases hw : wMinusOneBar U p h = ∞
  · rw [hw, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  by_cases hFp : lpBar U p F = ∞
  · rw [hFp, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  have hFm : AEStronglyMeasurable F (volume.restrict U) := hF.aestronglyMeasurable
  have hstep := p14_duality_step hUo hUb hne hp1 hpt hCq.le hq φ hφ hw hFm hFp
  have hd : ENNReal.ofReal (d : ℝ) ≤ ENNReal.ofReal (max 1 (d : ℝ)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 (d : ℝ)) := by
    simp
  have key : wMinusOneBar U p h + ENNReal.ofReal (d : ℝ) * lpBar U p F ≤
      ENNReal.ofReal (max 1 (d : ℝ)) * (lpBar U p F + wMinusOneBar U p h) := by
    calc wMinusOneBar U p h + ENNReal.ofReal (d : ℝ) * lpBar U p F
        ≤ ENNReal.ofReal (max 1 (d : ℝ)) * wMinusOneBar U p h +
          ENNReal.ofReal (max 1 (d : ℝ)) * lpBar U p F := by
          gcongr
          calc wMinusOneBar U p h = 1 * wMinusOneBar U p h := (one_mul _).symm
            _ ≤ ENNReal.ofReal (max 1 (d : ℝ)) * wMinusOneBar U p h := by gcongr
      _ = ENNReal.ofReal (max 1 (d : ℝ)) * (lpBar U p F + wMinusOneBar U p h) := by ring
  calc lpBar U p φ.toH1Function.grad
      ≤ ENNReal.ofReal Cq * (wMinusOneBar U p h + ENNReal.ofReal (d : ℝ) * lpBar U p F) := hstep
    _ ≤ ENNReal.ofReal Cq *
        (ENNReal.ofReal (max 1 (d : ℝ)) * (lpBar U p F + wMinusOneBar U p h)) := by gcongr
    _ = ENNReal.ofReal (Cq * max 1 (d : ℝ)) * (lpBar U p F + wMinusOneBar U p h) := by
        rw [ENNReal.ofReal_mul hCq.le, mul_assoc]

end SuperdiffusionCLT.Section7
