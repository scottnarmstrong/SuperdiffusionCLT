/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.DualityD
public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformI

/-!
# Global estimate: exponent bookkeeping and the duality step on a fixed domain

Conjugate-exponent facts for `1 < p < ∞`, boundedness of a uniformly `C^{1,1}` domain, the
vanishing of `wMinusOneBar` for zero data, and the duality step in the form used by the global
estimate (finiteness and measurability side conditions are discharged here).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p14g_conj_facts {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p ≠ ∞) :
    1 < p.conjExponent ∧ p.conjExponent ≠ ∞ ∧ p.conjExponent.conjExponent = p ∧
      (p ≤ 2 → 2 ≤ p.conjExponent) ∧ (2 ≤ p → p.conjExponent ≤ 2) := by
  set P : ℝ := p.toReal with hPdef
  have hpP : p = ENNReal.ofReal P := (ENNReal.ofReal_toReal hpt).symm
  have hP1 : 1 < P := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).2 hp1
  have hR : Real.HolderConjugate P (Real.conjExponent P) := Real.HolderConjugate.conjExponent hP1
  set Q : ℝ := Real.conjExponent P with hQdef
  have hQ1 : 1 < Q := hR.symm.lt
  have hPQ : P * Q = P + Q := hR.mul_eq_add
  have hE : ENNReal.HolderConjugate p (ENNReal.ofReal Q) := by
    rw [hpP]; exact hR.ennrealOfReal
  have hE' : ENNReal.HolderConjugate (ENNReal.ofReal Q) p := hE.symm
  have hc : p.conjExponent = ENNReal.ofReal Q := hE.conjExponent_eq
  have hcc : (ENNReal.ofReal Q).conjExponent = p := hE'.conjExponent_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hQ1])).2 hQ1
  · rw [hc]; exact ENNReal.ofReal_ne_top
  · rw [hc, hcc]
  · intro h2
    rw [hc]
    have hP2 : P ≤ 2 := by
      have := ENNReal.toReal_mono (by simp) h2
      simpa using this
    have hQ2 : 2 ≤ Q := by
      by_contra hlt
      have hlt := not_le.1 hlt
      nlinarith only [hPQ, hP1, hQ1, hP2, hlt]
    simpa using ENNReal.ofReal_le_ofReal hQ2
  · intro h2
    rw [hc]
    have hP2 : 2 ≤ P := by
      have := ENNReal.toReal_mono hpt h2
      simpa using this
    have hQ2 : Q ≤ 2 := by
      by_contra hlt
      have hlt := not_le.1 hlt
      nlinarith only [hPQ, hP1, hQ1, hP2, hlt]
    simpa using ENNReal.ofReal_le_ofReal hQ2

/-- A uniformly `C^{1,1}` domain is bounded. -/
theorem p14g_isBoundedDomain {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (hU : IsUniformC11Domain U r M₁ M₂ D) : IsBoundedDomain U := by
  rcases U.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨‖x₀‖ + |D| + 1, by positivity, fun x hx i => ?_⟩
    have h1 : ‖x - x₀‖ ≤ D := hU.2.2.1 x hx x₀ hx₀
    have h2 : |x i - x₀ i| ≤ ‖x - x₀‖ := by
      simpa using norm_le_pi_norm (x - x₀) i
    have h3 : |x₀ i| ≤ ‖x₀‖ := by simpa using norm_le_pi_norm x₀ i
    have h4 : |x i| ≤ |x i - x₀ i| + |x₀ i| := by
      simpa using abs_add_le (x i - x₀ i) (x₀ i)
    have h5 : D ≤ |D| := le_abs_self D
    linarith only [h1, h2, h3, h4, h5]

/-- On an empty set every normalized norm vanishes. -/
theorem p14g_lpBar_empty {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (F : Vec d → E) :
    lpBar (∅ : Set (Vec d)) p F = 0 := by
  simp [lpBar]

/-- Zero data has zero `W^{-1,p}` norm. -/
theorem p14g_wMinusOneBar_zero (U : Set (Vec d)) (p : ℝ≥0∞) :
    wMinusOneBar U p (fun _ => 0) = 0 := by
  simp [wMinusOneBar]

end SuperdiffusionCLT.Section7
