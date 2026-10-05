/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3G
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3

/-!
# Condition J3 for the seed shell laws

The seed shell law of amplitude `nv_epsJ3 d` satisfies, at every shell `n`, the strict Gaussian
tail of the marginal J3 observable: `scaledShellLaw (nv_j3_seedShellLaw d ε) n` gives mass at most
`exp (-t²)` to `{j | t < j3Observable d n j}` for every `t ≥ 1`.  Any law on shell sequences whose
`n`-th coordinate marginal is this shell law satisfies `ShellLawJ3`.

## Main results

* `nv_epsJ3_cond`: the amplitude `nv_epsJ3 d` meets the smallness condition
* `nv_scaledSeedShell_tail`
* `nv_shellLawJ3_of_marginals`
* `nv_shellLawJ3_epsJ3`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}

/-- The amplitude `nv_epsJ3 d` meets the smallness condition. -/
theorem nv_epsJ3_cond (hd : 0 < d) :
    2 * (1 + 2 * nv_G d) * nv_epsJ3 d ^ 2 * nv_K0 d ^ 2 * nv_R d ^ 2 ≤ 1 := by
  have hK := nv_K0_pos hd
  have hR := nv_R_pos d
  have hG := nv_G_nonneg d
  have hD : 2 ≤ 2 * (1 + 2 * nv_G d) := by linarith only [hG]
  have hD0 : 0 < 2 * (1 + 2 * nv_G d) := by linarith only [hD]
  have e : nv_epsJ3 d * nv_K0 d * nv_R d = 1 / (2 * (1 + 2 * nv_G d)) := by
    unfold nv_epsJ3; field_simp
  have e2 : 2 * (1 + 2 * nv_G d) * nv_epsJ3 d ^ 2 * nv_K0 d ^ 2 * nv_R d ^ 2
      = 2 * (1 + 2 * nv_G d) * (nv_epsJ3 d * nv_K0 d * nv_R d) ^ 2 := by ring
  rw [e2, e, div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
  nlinarith only [hD]

/-- **J3 for the dilated seed shell laws.** -/
theorem nv_scaledSeedShell_tail (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (hc : 2 * (1 + 2 * nv_G d) * ε ^ 2 * nv_K0 d ^ 2 * nv_R d ^ 2 ≤ 1) (n : ℕ) {t : ℝ}
    (ht : 1 ≤ t) :
    (scaledShellLaw (nv_j3_seedShellLaw d ε) n).toMeasure {j | t < j3Observable d n j}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  have hS : MeasurableSet {j : ShellField d | t < j3Observable d n j} :=
    measurableSet_lt measurable_const (j3Observable_measurable d n)
  rw [scaledShellLaw_toMeasure, Measure.map_apply (measurable_dilate _) hS]
  exact nv_seedShell_tail hd hε hc n ht

/-- **J3 on shell sequences** from the marginals. -/
theorem nv_shellLawJ3_of_marginals (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (hc : 2 * (1 + 2 * nv_G d) * ε ^ 2 * nv_K0 d ^ 2 * nv_R d ^ 2 ≤ 1)
    (P : ProbabilityMeasure (ℕ → ShellField d))
    (hP : ∀ n, P.toMeasure.map (fun F : ℕ → ShellField d ↦ F n)
      = (scaledShellLaw (nv_j3_seedShellLaw d ε) n).toMeasure) :
    ShellLawJ3 d P := by
  refine ⟨fun n t ht ↦ ?_⟩
  have hS : MeasurableSet {j : ShellField d | t < j3Observable d n j} :=
    measurableSet_lt measurable_const (j3Observable_measurable d n)
  have h := Measure.map_apply (μ := P.toMeasure) (measurable_pi_apply n) hS
  rw [hP n] at h
  have e : {F : ℕ → ShellField d | t < j3Observable d n (F n)}
      = (fun F : ℕ → ShellField d ↦ F n) ⁻¹' {j | t < j3Observable d n j} := rfl
  rw [e, ← h]
  exact nv_scaledSeedShell_tail hd hε hc n ht

/-- The explicit amplitude gives J3 for every law with the dilated seed shell marginals. -/
theorem nv_shellLawJ3_epsJ3 (hd : 0 < d) (P : ProbabilityMeasure (ℕ → ShellField d))
    (hP : ∀ n, P.toMeasure.map (fun F : ℕ → ShellField d ↦ F n)
      = (scaledShellLaw (nv_j3_seedShellLaw d (nv_epsJ3 d)) n).toMeasure) :
    ShellLawJ3 d P :=
  nv_shellLawJ3_of_marginals hd (nv_epsJ3_pos hd) (nv_epsJ3_cond hd) P hP

end

/-! ## Satisfiability witnesses (dimension two) -/

example : 0 < nv_epsJ3 2 ∧
    2 * (1 + 2 * nv_G 2) * nv_epsJ3 2 ^ 2 * nv_K0 2 ^ 2 * nv_R 2 ^ 2 ≤ 1 ∧
    (scaledShellLaw (nv_j3_seedShellLaw 2 (nv_epsJ3 2)) 0).toMeasure
        {j | (1 : ℝ) < j3Observable 2 0 j} ≤ ENNReal.ofReal (Real.exp (-((1 : ℝ) ^ 2))) :=
  ⟨nv_epsJ3_pos (by norm_num), nv_epsJ3_cond (by norm_num),
    nv_scaledSeedShell_tail (by norm_num) (nv_epsJ3_pos (by norm_num))
      (nv_epsJ3_cond (by norm_num)) 0 le_rfl⟩

/-- The hypothesis of `nv_shellLawJ3_epsJ3` is met by the product of the dilated seed shell laws. -/
example : ∃ P : ProbabilityMeasure (ℕ → ShellField 2),
    (∀ n, P.toMeasure.map (fun F : ℕ → ShellField 2 ↦ F n)
      = (scaledShellLaw (nv_j3_seedShellLaw 2 (nv_epsJ3 2)) n).toMeasure) ∧ ShellLawJ3 2 P := by
  have : ∀ n, IsProbabilityMeasure (scaledShellLaw (nv_j3_seedShellLaw 2 (nv_epsJ3 2)) n).toMeasure :=
    fun n ↦ inferInstance
  refine ⟨⟨Measure.infinitePi fun n ↦ (scaledShellLaw (nv_j3_seedShellLaw 2 (nv_epsJ3 2)) n).toMeasure,
    inferInstance⟩, fun n ↦ ?_, ?_⟩
  · exact (measurePreserving_eval_infinitePi
      (fun n ↦ (scaledShellLaw (nv_j3_seedShellLaw 2 (nv_epsJ3 2)) n).toMeasure) n).map_eq
  · exact nv_shellLawJ3_epsJ3 (by norm_num) _ fun n ↦
      (measurePreserving_eval_infinitePi
        (fun n ↦ (scaledShellLaw (nv_j3_seedShellLaw 2 (nv_epsJ3 2)) n).toMeasure) n).map_eq

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
