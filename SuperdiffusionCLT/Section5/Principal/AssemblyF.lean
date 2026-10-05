/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AssemblyE
public import SuperdiffusionCLT.Section5.Principal.AverageMomentF
public import SuperdiffusionCLT.Section5.Principal.AverageMomentE

/-!
# `lem.principal.term`

The reduction of the principal term, for the subcubes `z + cu_n`,
`z ∈ 3^n ℤ^d ∩ cu_Kc`, as `principal_term`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)
open scoped ENNReal

variable {d : ℕ}

theorem pa_lenSq_measurable [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hσ : 0 < sigmaBarInfinite nu L P) {Phat : ShellSeq d → BlockVec d}
    (hPm : ∀ α : BlockCoord d, Measurable fun ω => toFullBlockVec (Phat ω) α) :
    Measurable fun ω => blockLenSq (ahomSqrtApply nu L P (Phat ω)) := by
  have hsq : ∀ (f : ShellSeq d → Vec d), (∀ i, Measurable fun ω => f ω i) →
      Measurable fun ω => vecNormSq (f ω) := by
    intro f hf
    unfold vecNormSq vecDot
    exact Finset.measurable_sum _ fun i _ => (hf i).mul (hf i)
  have h1 := hsq (fun ω => (Phat ω).1) fun i => hPm (Sum.inl i)
  have h2 := hsq (fun ω => (Phat ω).2) fun i => hPm (Sum.inr i)
  have : (fun ω => blockLenSq (ahomSqrtApply nu L P (Phat ω))) = fun ω =>
      sigmaBarInfinite nu L P * vecNormSq (Phat ω).1 +
        (sigmaBarInfinite nu L P)⁻¹ * vecNormSq (Phat ω).2 :=
    funext fun ω => pa_blockLenSq_ahomSqrt nu L P hσ (Phat ω)
  rw [this]
  exact (h1.const_mul _).add (h2.const_mul _)

theorem pa_blockLenSq_nonneg (X : BlockVec d) : 0 ≤ blockLenSq X := by
  unfold blockLenSq
  exact add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)

end SuperdiffusionCLT.Section5
