/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.AnnealedDtC
public import SuperdiffusionCLT.Section8.Prereq.FieldRegularityB

/-!
# The annealed variance bound: moments of the random scales with constants independent of the law

* the scale `K` of the pointwise growth of the field, together with its tail amplitude, which is a
  constant independent of the law (exposed from the stream estimates);
* the `q`-th moments of `log K` and of the gradient scale `G`, bounded by constants depending
  only on `d` and `q`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- **The growth scale of the field, with law-independent constants.**  There are constants `C`, `B`
such that for every admissible law there is a measurable scale `K ≥ 27` with
`log K = O_{Γ₂}(B)` and `|k(x) - k(0)|² ≤ C (log (K² + |x|²))⁴` almost surely. -/
theorem annDt_scale_uniform :
    ∃ C B : ℝ, ∀ {P : ProbabilityMeasure (ShellSeq d)}, ShellLawPrefix d P → ShellLawJ1Restriction d P →
      ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧ (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 * 1))
          (fun omega => Real.log (Kfun omega)) B ∧
        ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
          matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
            C * Real.log (Kfun omega ^ 2 + vecNormSq x) ^ (2 * (1 + (1 : ℝ))) := by
  obtain ⟨C₂, h⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, h'⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨C, h''⟩ := h' 2 (by norm_num)
  refine ⟨C, C₀ * (C₁ * (1 / 2 : ℝ)⁻¹ * Real.sqrt ((1 : ℝ)⁻¹ *
    Real.log (Real.exp 1 + C₂ * (1 / 2 : ℝ)⁻¹ * (1 : ℝ)⁻¹))) ^ (1 : ℝ)⁻¹, fun {P} hPrefix hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨-, -, h3⟩ := h'' P hPrefix hJ1 hJ2 hJ3 hJ4
  obtain ⟨Kfun, hKm, hK27, hKb, hae⟩ := h3 (1 / 2) (by norm_num) (by norm_num) 1 one_pos
  refine ⟨Kfun, hKm, hK27, hKb, ?_⟩
  filter_upwards [hae, ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega h1 hg x
  have h2 := (h1 hg).2 x
  rw [fieldReg_centered_sub_origin_eq omega hg x] at h2
  exact h2

/-- **Moments of `log K`.**  The tail `O_{Γ₂}(B)` gives a bound on every positive moment depending
only on `B` and the exponent. -/
theorem annDt_logK_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Kfun : Ω → ℝ} (hKm : Measurable Kfun) (hK27 : ∀ omega, (27 : ℝ) ≤ Kfun omega) {B : ℝ}
    (hB : IndependentSums.IsBigO μ (IndependentSums.gammaSigma (2 * 1))
      (fun omega => Real.log (Kfun omega)) B) {q : ℝ} (hq : 0 < q) :
    ∫⁻ omega, ENNReal.ofReal (Real.log (Kfun omega) ^ q) ∂μ ≤
      ENNReal.ofReal (annDt_M (max B 1) 1 q) := by
  have hA : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB' := hB.mono_scale (le_max_left B 1)
  have hX0 : ∀ omega, 0 ≤ Real.log (Kfun omega) := fun omega =>
    Real.log_nonneg (by linarith only [hK27 omega])
  refine annDt_lintegral_rpow_le (a := max B 1) (B := 1) (Real.measurable_log.comp hKm) hX0 hA
    zero_le_one (fun s hs => ?_) hq
  have ht : 1 ≤ s / max B 1 := by rw [le_div_iff₀ hA]; linarith only [hs]
  have h1 := hB' ht
  rw [mul_div_cancel₀ _ hA.ne'] at h1
  have h2 : {omega | s < (Real.log ∘ Kfun) omega} =
      IndependentSums.upperTailEvent (fun omega => |Real.log (Kfun omega)|) s := by
    ext omega
    simp only [Set.mem_ofPred_eq, IndependentSums.upperTailEvent, Function.comp_apply,
      abs_of_nonneg (hX0 omega)]
  rw [h2, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
  rw [IndependentSums.gammaSigma_inv, one_mul]
  congr 2
  rw [show (2 : ℝ) * 1 = 2 by norm_num]
  exact Real.rpow_two _

/-- The gradient scale is nonnegative. -/
theorem annDt_G_nonneg [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (omega : ShellSeq d) : 0 ≤ gradScale_G omega := by
  have ha1 : 0 ≤ gradScale_a1 d := by
    have : 0 < gradScale_c0 d := gradScale_c0_pos hPrefix
    unfold gradScale_a1; positivity
  have ha2 : 0 ≤ gradScale_a2 d := by
    have : 0 ≤ (1 - shellDerivTailScale)⁻¹ :=
      inv_nonneg.2 (by linarith only [shellDerivTailScale_lt_one])
    unfold gradScale_a2; positivity
  exact add_nonneg (mul_nonneg ha1 ENNReal.toReal_nonneg) (mul_nonneg ha2 ENNReal.toReal_nonneg)

theorem annDt_rate_pos [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) : 0 < gradScale_rate d := by
  have hc0 := gradScale_c0_pos hPrefix
  have hinv : 0 < (1 - shellDerivTailScale)⁻¹ :=
    inv_pos.2 (by linarith only [shellDerivTailScale_lt_one])
  have hd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2
    (lt_of_lt_of_le (by norm_num) hPrefix.dimension))
  have h2 : 0 < gradScale_a2 d := by unfold gradScale_a2; positivity
  unfold gradScale_rate
  exact mul_pos (by norm_num) (lt_max_of_lt_right h2)

/-- **Moments of the gradient scale**, with a constant depending only on `d` and the exponent. -/
theorem annDt_G_moment [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {q : ℝ} (hq : 0 < q) :
    ∫⁻ omega, ENNReal.ofReal (gradScale_G omega ^ q) ∂P.toMeasure ≤
      ENNReal.ofReal (annDt_M (gradScale_rate d) 8 q) :=
  annDt_lintegral_rpow_le (a := gradScale_rate d) (B := 8) gradScale_measurable_G
    (annDt_G_nonneg hPrefix) (annDt_rate_pos hPrefix) (by norm_num)
    (fun s hs => gradScale_measure_G_tail hPrefix hJ3 hs) hq

end

end SuperdiffusionCLT.Section8
