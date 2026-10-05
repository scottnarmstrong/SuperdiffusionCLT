/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeF
public import SuperdiffusionCLT.Section8.Prereq.FieldRegularityB

/-!
# The fourth moment of the marginal-field process for times at least one

The pointwise growth clause bounds `|k x - k 0|` by `C (log (K ^ 2 + |x|^2)) ^ (1 + σ)`.
Rounding the exponent up to `n = ⌈1 + σ⌉` gives the rough bound of `CrudeMomentsLarge`, and the
fourth moment of the process is bounded by `M t ^ 2 (log (K ^ 2 + t)) ^ (8 n)` for `t ≥ 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open SuperdiffusionCLT.Section8.Common.Regularity.Freezing
open scoped ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The pointwise growth clause with exponent `2 (1 + σ)` on the square of the operator norm gives
the bound with the integer exponent `⌈1 + σ⌉`. -/
theorem crudeMomL_opNorm_le {C K σ : ℝ} {k : Vec d → Mat d} (hK : 2 ≤ K)
    (h : ∀ x, matrixOperatorNorm (k x) ^ 2 ≤
      C * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ))) :
    ∀ x, matrixOperatorNorm (k x) ≤
      Real.sqrt (max C 0) * Real.log (K ^ 2 + vecNormSq x) ^ ⌈1 + σ⌉₊ := by
  intro x
  set W : ℝ := Real.log (K ^ 2 + vecNormSq x) with hW
  have hW1 : 1 ≤ W := crudeMomL_one_le_log hK (vecNormSq_nonneg x)
  set N : ℕ := ⌈1 + σ⌉₊ with hN
  have hNle : 1 + σ ≤ (N : ℝ) := Nat.le_ceil _
  have hexp : W ^ (2 * (1 + σ)) ≤ W ^ (2 * N) := by
    have : W ^ (2 * (1 + σ)) ≤ W ^ ((2 * N : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith only [hNle])
    rwa [Real.rpow_natCast] at this
  have hop : 0 ≤ matrixOperatorNorm (k x) := by simp [matrixOperatorNorm]
  have hsq : matrixOperatorNorm (k x) ^ 2 ≤ (Real.sqrt (max C 0) * W ^ N) ^ 2 := by
    calc matrixOperatorNorm (k x) ^ 2 ≤ C * W ^ (2 * (1 + σ)) := h x
      _ ≤ max C 0 * W ^ (2 * (1 + σ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith only [hW1]) _)
      _ ≤ max C 0 * W ^ (2 * N) := mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
      _ = (Real.sqrt (max C 0) * W ^ N) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm N 2]
  exact (pow_le_pow_iff_left₀ hop (by positivity) two_ne_zero).1 hsq

theorem two_le_ceil_one_add {σ : ℝ} (hσ : 0 < σ) : 2 ≤ ⌈1 + σ⌉₊ := by
  have : 1 < ⌈1 + σ⌉₊ := by
    rw [Nat.lt_ceil]; push_cast; linarith only [hσ]
  omega

variable [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **The fourth moment at the origin of the marginal-field process, for times at least one.**
For a field `k` with the rough bound `|k x| ≤ c0 (log (K ^ 2 + |x| ^ 2)) ^ n` the fourth moment at
the origin is at most `M t ^ 2 (log (K ^ 2 + t)) ^ (8 n)`, with `M` independent of `K`. -/
theorem fieldMoment_fourth_large (D : FieldInputData d nu k) {c0 Kc : ℝ} {n : ℕ} (hc0 : 0 ≤ c0)
    (hKc : 2 ≤ Kc) (hn : 2 ≤ n)
    (hk : ∀ y, matrixOperatorNorm (k y) ≤ c0 * Real.log (Kc ^ 2 + vecNormSq y) ^ n)
    {t : ℝ≥0} (ht : 1 ≤ t) :
    ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
      ENNReal.ofReal (crudeMomL_const d nu c0
        (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) n *
        Real.log (Kc ^ 2 + (t : ℝ)) ^ (8 * n) * (t : ℝ) ^ 2) :=
  (D.roughLogBounds c0 Kc n hc0 hKc hn hk).crudeMomL_fourth_moment_polylog
    D.logGrowthBounds.resolvent D.logGrowthBounds.isConservative_kernelSemigroup
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal ht

/-- **Almost surely the marginal-field process has the fourth moment bound at the origin for
times at least one.**  The measurable scale `Kfun` is that of the pointwise growth clause
(with `log Kfun = O_{Γ_{2σ}}(B)`); the constant depends on the field only through the freezing
amplitude. -/
theorem fieldMoment_ae_fourth_large {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (hnu : 0 < nu) :
    ∃ C : ℝ, ∀ σ : ℝ, 0 < σ → ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧
      (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
      (∃ B : ℝ, IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 * σ))
        (fun omega => Real.log (Kfun omega)) B) ∧
      ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
        ∃ D : FieldInputData d nu (fullStreamRecentered omega),
          ∀ t : ℝ≥0, 1 ≤ t →
            ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
              ENNReal.ofReal (crudeMomL_const d nu (Real.sqrt (max C 0))
                (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) ⌈1 + σ⌉₊ *
                Real.log (Kfun omega ^ 2 + (t : ℝ)) ^ (8 * ⌈1 + σ⌉₊) * (t : ℝ) ^ 2) := by
  obtain ⟨C, hC⟩ := fieldReg_ae_pointwise_growth hPrefix hJ1 hJ2 hJ3 hJ4
  refine ⟨C, fun σ hσ => ?_⟩
  obtain ⟨Kfun, hKm, hK27, hKb, hae⟩ := hC σ hσ
  refine ⟨Kfun, hKm, hK27, hKb, ?_⟩
  filter_upwards [hae, fieldInput_ae_data hPrefix hJ3 hnu] with omega h1 hD
  obtain ⟨D⟩ := hD
  refine ⟨D, fun t ht => ?_⟩
  have hK2 : (2 : ℝ) ≤ Kfun omega := by linarith only [hK27 omega]
  exact fieldMoment_fourth_large D (Real.sqrt_nonneg _) hK2 (two_le_ceil_one_add hσ)
    (crudeMomL_opNorm_le hK2 h1) ht

end

end SuperdiffusionCLT.Section8
