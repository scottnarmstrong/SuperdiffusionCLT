/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzC

/-!
# The second moment of the ellipticity ratio

`l.bfAm.ellip` (`e.Enaught.vs.A.and.Ahom`): the ellipticity ratio of `bfA_m(Q)` against `bfE_m` is
`O_{Γ₁}(1)`, hence has a second moment bounded by a universal constant.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open scoped ENNReal

variable {d : ℕ}

theorem measurable_envelopeRatio [NeZero d] (m : ℕ) (Q : TriadicCube d) :
    Measurable (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      envelopeRatio m Q omega) := by
  unfold envelopeRatio
  exact measurable_const.max
    ((SuperdiffusionCLT.Section2.Annealed.measurable_volumeAverage_sq_streamCutoff m
      (openCubeSet Q)).div_const _)

/-- The second moment of the ellipticity ratio is bounded by a universal constant. -/
theorem lintegral_envelopeRatio_sq_le [NeZero d]
    {P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    ∫⁻ omega, ENNReal.ofReal (envelopeRatio m Q omega) ^ (2 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal ((2 * IndependentSums.gammaMomentConst 1) ^ 2) := by
  have hbig := isBigOWith_gammaSigma_envelopeRatio hPrefix hJ2 hJ3 hJ4 m Q
  have hmom := IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    (μ := P.toMeasure) one_pos one_pos
    (fun omega => (zero_le_one.trans (one_le_envelopeRatio m Q omega)))
    (measurable_envelopeRatio m Q).aemeasurable hbig
  obtain ⟨hint, hle⟩ := hmom (p := 2) (by norm_num)
  have e1 : (fun omega => |envelopeRatio m Q omega| ^ (2 : ℝ)) =
      fun omega => envelopeRatio m Q omega ^ 2 := by
    funext omega
    rw [abs_of_nonneg (zero_le_one.trans (one_le_envelopeRatio m Q omega))]
    norm_cast
  rw [e1] at hint hle
  have hnn : 0 ≤ᵐ[P.toMeasure] fun omega => envelopeRatio m Q omega ^ 2 :=
    Filter.Eventually.of_forall fun omega => by positivity
  have h2 := ofReal_integral_eq_lintegral_ofReal hint hnn
  have e2 : ∀ omega, ENNReal.ofReal (envelopeRatio m Q omega ^ 2) =
      ENNReal.ofReal (envelopeRatio m Q omega) ^ (2 : ℕ) := fun omega =>
    ENNReal.ofReal_pow (zero_le_one.trans (one_le_envelopeRatio m Q omega)) 2
  simp_rw [e2] at h2
  rw [← h2]
  refine ENNReal.ofReal_le_ofReal (hle.trans (le_of_eq ?_))
  norm_num
  ring

end SuperdiffusionCLT.Section5
