/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import Homogenization.Book.Ch01.Theorems.NormScaling
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.AKHC61.Tails.CFSTranslate
public import SuperdiffusionCLT.Assumptions.ShellLaw.BlockStationarity

/-!
# Translates of the minimal scale

Translation acts on the cutoff objects by `translateSequence`, and the conventions compose:
`ShellField.translate z j x = j (x + z)`, `translateSet z U = {y + z | y ∈ U}`, and
`volumeAverage (translateSet z U) f = volumeAverage U (f (· + z))`.  Hence the centered cutoff of
the translated sample on `U` is the translate by `z` of the centered cutoff of the original sample
on `translateSet z U`; for `U = cu_m` this is the cube `z + cu_m`.

## Main results

* `translateSequence_measurePreserving`: the shell law is invariant under `translateSequence`.
* `isBigO_comp_translateSequence`: `X ∘ τ_z` has the same `IsBigO` bound as `X`.
* `centeredStreamField_translateSequence`: the translation identity for the centered stream field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- The shell law is invariant under the whole-sequence translation. -/
theorem translateSequence_measurePreserving
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (z : Vec d) :
    MeasurePreserving (ShellField.translateSequence z) P.toMeasure P.toMeasure :=
  ⟨ShellField.measurable_translateSequence z,
    ShellField.map_translateSequence_eq hPrefix hJ2 z⟩

/-- `X ∘ τ_z` carries the same `IsBigO` bound as `X`. -/
theorem isBigO_comp_translateSequence
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (z : Vec d) {X : ShellSeq d → ℝ} (hX : Measurable X)
    {Psi : ℝ → ℝ} {A : ℝ}
    (hO : Homogenization.IndependentSums.IsBigO P.toMeasure Psi X A) :
    Homogenization.IndependentSums.IsBigO P.toMeasure Psi
      (fun omega => X (ShellField.translateSequence z omega)) A :=
  SuperdiffusionCLT.AKHC61.Tails.akhcCfsT_isBigO_comp_of_measurePreserving
    (ShellField.measurable_translateSequence z)
    (ShellField.map_translateSequence_eq hPrefix hJ2 z) hX hO

/-- The volume average of a translated field over `U` is the average of the field over the
translated set. -/
theorem volumeAverageMat_comp_add (z : Vec d) (U : Set (Vec d)) (f : Vec d → Mat d) :
    volumeAverageMat U (fun x => f (x + z)) = volumeAverageMat (translateSet z U) f := by
  funext i j
  exact (Book.Ch01.volumeAverage_translateSet_eq_comp_addRight z U (fun x => f x i j)).symm

/-- The centered stream carrier of the translated sample on `U` is the translate by `z` of the
carrier of the sample on `translateSet z U`. -/
theorem centeredStreamField_translateSequence (z : Vec d) (omega : ShellSeq d)
    (U : Set (Vec d)) (x : Vec d) :
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        (ShellField.translateSequence z omega) U x =
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (translateSet z U)
        (x + z) := by
  unfold SuperdiffusionCLT.Section2.Carriers.centeredStreamField
  refine tsum_congr fun k => ?_
  have h : volumeAverageMat U (fun y => shellReg (ShellField.translateSequence z omega) k y) =
      volumeAverageMat (translateSet z U) (fun y => shellReg omega k y) :=
    volumeAverageMat_comp_add z U (fun y => shellReg omega k y)
  rw [h]
  rfl

end

end SuperdiffusionCLT.Section7
