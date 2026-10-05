/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3F

/-!
# J3 for the seed shell law and all its dilations

For `ε > 0` with `2 (1 + 2 G) ε² K₀² R² ≤ 1` (for instance `ε = nv_epsJ3 d`), every shell `n`, and
every `t ≥ 1`, the law `scaledShellLaw (nv_j3_seedShellLaw d ε) n` satisfies
`P[t < j3Observable d n j] ≤ exp (-t²)`.

## Main results

* `nv_seedShell_tail`: the tail of the dilated seed shell at shell `n`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}

theorem nv_card_skewIdx_le (d : ℕ) : (Fintype.card (SkewIdx d) : ℝ) ≤ (d : ℝ) ^ 2 := by
  have h : Fintype.card (SkewIdx d) ≤ d * d := by
    refine (Fintype.card_subtype_le _).trans ?_
    simp
  have : (Fintype.card (SkewIdx d) : ℝ) ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast h
  rw [pow_two]
  simpa using this

theorem nv_measure_eval_preimage (p : SkewIdx d) {s : Set (NvNoise d)} (hs : MeasurableSet s) :
    (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d) {ξ | ξ p ∈ s} = nvNoiseLaw d s :=
  (measurePreserving_eval (fun _ : SkewIdx d ↦ nvNoiseLaw d) p).measure_preimage
    hs.nullMeasurableSet

/-- **J3 for the seed shell law at shell `n`**, in the dilated form. -/
theorem nv_seedShell_tail (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (hc : 2 * (1 + 2 * nv_G d) * ε ^ 2 * nv_K0 d ^ 2 * nv_R d ^ 2 ≤ 1) (n : ℕ) {t : ℝ}
    (ht : 1 ≤ t) :
    (nv_j3_seedShellLaw d ε).toMeasure {F | t < j3Observable d n (dilate (nv_scaleUnit n) F)}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hK := nv_K0_pos hd
  have hR := nv_R_pos d
  have hS : MeasurableSet {F : ShellField d | t < j3Observable d n (dilate (nv_scaleUnit n) F)} :=
    measurableSet_lt measurable_const ((j3Observable_measurable d n).comp (measurable_dilate _))
  rw [nv_j3_seedShellLaw_eq_map, Measure.map_apply (measurable_nv_j3_seedShellMap ε) hS]
  set τ : ℝ := t / (ε * nv_K0 d) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg ht0 (mul_pos hε hK).le
  set B : ENNReal := ENNReal.ofReal (2 * Real.exp (-(τ ^ 2 / (2 * nv_R d ^ 2)))) with hB
  have hrow : ∀ (p : SkewIdx d) (k : Fin d → ℤ),
      (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d) {ξ | ξ p ∈ nv_badRow d τ k} ≤ B := fun p k ↦ by
    rw [nv_measure_eval_preimage p (measurableSet_nv_badRow d τ k)]
    exact nv_noiseLaw_tail_tsum d (nv_R_pos d) (nv_summable_le_R d) k hτ0
  have hgood : ∀ p : SkewIdx d,
      (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d) {ξ | ξ p ∈ (nvGood d)ᶜ} = 0 := fun p ↦ by
    rw [nv_measure_eval_preimage p (measurableSet_nvGood d).compl]
    exact (prob_compl_eq_zero_iff (measurableSet_nvGood d)).2 (nvNoiseLaw_nvGood d)
  refine le_trans (measure_mono (nv_inclusion hd hε n ht0)) ?_
  refine (measure_union_le _ _).trans ?_
  have h1 : (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d)
      (⋃ p : SkewIdx d, {ξ | ξ p ∈ (nvGood d)ᶜ}) = 0 :=
    measure_iUnion_null hgood
  have h2 : (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d)
      (⋃ p : SkewIdx d, ⋃ k ∈ nv_cubeCells d, {ξ | ξ p ∈ nv_badRow d τ k})
      ≤ (Fintype.card (SkewIdx d) * (5 ^ d : ℕ) : ℕ) * B := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    have : ∀ p : SkewIdx d, (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d)
        (⋃ k ∈ nv_cubeCells d, {ξ | ξ p ∈ nv_badRow d τ k}) ≤ (5 ^ d : ℕ) * B := fun p ↦ by
      refine (measure_biUnion_finset_le _ _).trans ?_
      calc ∑ k ∈ nv_cubeCells d, (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d)
            {ξ | ξ p ∈ nv_badRow d τ k} ≤ ∑ _k ∈ nv_cubeCells d, B :=
          Finset.sum_le_sum fun k _ ↦ hrow p k
        _ = (5 ^ d : ℕ) * B := by
          rw [Finset.sum_const, card_nv_cubeCells, nsmul_eq_mul]
    calc ∑ p : SkewIdx d, (Measure.pi fun _ : SkewIdx d ↦ nvNoiseLaw d)
          (⋃ k ∈ nv_cubeCells d, {ξ | ξ p ∈ nv_badRow d τ k})
        ≤ ∑ _p : SkewIdx d, ((5 ^ d : ℕ) : ENNReal) * B := Finset.sum_le_sum fun p _ ↦ this p
      _ = (Fintype.card (SkewIdx d) * (5 ^ d : ℕ) : ℕ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
  rw [h1, zero_add]
  refine h2.trans ?_
  have hN : ((Fintype.card (SkewIdx d) * (5 ^ d : ℕ) : ℕ) : ℝ) ≤ nv_G d := by
    unfold nv_G
    push_cast
    exact mul_le_mul_of_nonneg_right (nv_card_skewIdx_le d) (by positivity)
  have hx : (1 + 2 * nv_G d) * t ^ 2 ≤ τ ^ 2 / (2 * nv_R d ^ 2) := by
    have hP : 0 < ε * nv_K0 d * nv_R d := by positivity
    have e : τ ^ 2 / (2 * nv_R d ^ 2) = t ^ 2 / (2 * (ε * nv_K0 d * nv_R d) ^ 2) := by
      rw [hτ]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have h0 : (1 + 2 * nv_G d) * t ^ 2 * (2 * (ε * nv_K0 d * nv_R d) ^ 2)
        = (2 * (1 + 2 * nv_G d) * ε ^ 2 * nv_K0 d ^ 2 * nv_R d ^ 2) * t ^ 2 := by ring
    rw [h0]
    exact mul_le_of_le_one_left (sq_nonneg t) hc
  have hfin := nv_final_real (nv_G_nonneg d) hN ht hx
  rw [hB, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hfin

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
