/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.FieldAE
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# Almost-sure ellipticity of the recentered field on bounded sets

Almost surely (under the single hypothesis `ShellLawJ3`), the recentered field
`ν Id + (k - k(0))` is elliptic with lower constant `ν` on every bounded measurable set, with an
upper constant depending on the sample and the set; the same holds for the rescaled field
`x ↦ a(x / ε)` for every `ε ≠ 0`.

## Main results

* `Section7.w0_ae_isElliptic_bounded`: one almost-sure event for all bounded measurable sets.
* `Section7.w0_ae_isElliptic_rescaled`: the same for `Section8.epCoeff ν ω ε`, all `ε ≠ 0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Pointwise

variable {d : ℕ}

/-- A coefficient bound on a measurable set gives ellipticity with lower constant `ν`. -/
theorem w0_isElliptic_of_entryBound [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    {S : Set (Vec d)} (hS : MeasurableSet S) {C : ℝ}
    (hC : ∀ x ∈ S, ∀ i j : Fin d, |Section6.fullCoefficientRecentered nu omega x i j| ≤ C) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam S (Section6.fullCoefficientRecentered nu omega) := by
  classical
  refine ⟨((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ?_, fun x hx => ?_⟩
  · refine measurable_matrix_of_entries fun i j => Measurable.ite hS ?_ measurable_const
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (Section6.measurable_fullCoefficientRecentered nu omega))
  · exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (Section6.symmPart_fullCoefficientRecentered nu omega x) (fun i j => hC x hx i j)

/-- **Almost-sure ellipticity on bounded sets.** One almost-sure event on which the recentered
field is elliptic, with lower constant `ν`, on every bounded measurable set. -/
theorem w0_ae_isElliptic_bounded [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ W : Set (Vec d), Bornology.IsBounded W →
      MeasurableSet W →
      ∃ Lam : ℝ, IsEllipticFieldOn nu Lam W (Section6.fullCoefficientRecentered nu omega) := by
  filter_upwards [Section6.ae_exists_entryBound_fullCoefficientRecentered hJ3 nu] with omega h W hb hm
  obtain ⟨C, hC⟩ := h W hb
  exact w0_isElliptic_of_entryBound hnu omega hm hC

/-- **Almost-sure ellipticity of the rescaled field.** On the same type of event, the field
`x ↦ a(x / ε)` is elliptic on every bounded measurable set, for every `ε ≠ 0`. -/
theorem w0_ae_isElliptic_rescaled [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ ε : ℝ, ε ≠ 0 → ∀ W : Set (Vec d),
      Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam : ℝ, IsEllipticFieldOn nu Lam W (Section8.epCoeff nu omega ε) := by
  filter_upwards [w0_ae_isElliptic_bounded hJ3 hnu] with omega h ε hε W hb hm
  have hb' : Bornology.IsBounded (ε⁻¹ • W) := hb.smul₀ ε⁻¹
  have hm' : MeasurableSet (ε⁻¹ • W) := hm.const_smul₀ ε⁻¹
  obtain ⟨Lam, hmeas, hell⟩ := h _ hb' hm'
  classical
  refine ⟨Lam, ?_, fun x hx => ?_⟩
  · have hc : Measurable (fun x : Vec d => ε⁻¹ • x) := measurable_const_smul ε⁻¹
    have hcomp := hmeas.comp hc
    have hfun : (fun (x : Vec d) (i j : Fin d) =>
        if x ∈ W then Section8.epCoeff nu omega ε x i j else 0) =
        (fun (x : Vec d) (i j : Fin d) =>
          if x ∈ ε⁻¹ • W then Section6.fullCoefficientRecentered nu omega x i j else 0) ∘
          (fun x : Vec d => ε⁻¹ • x) := by
      funext x i j
      have hiff : ε⁻¹ • x ∈ ε⁻¹ • W ↔ x ∈ W :=
        Set.smul_mem_smul_set_iff₀ (inv_ne_zero hε) W x
      simp only [Function.comp_apply, hiff, Section8.epCoeff]
    exact hfun ▸ hcomp
  · exact hell _ (Set.smul_mem_smul_set hx)

/-- Witness: the Dirac zero law meets `J3`, so the almost-sure ellipticity is not vacuous. -/
example [NeZero d] {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ W : Set (Vec d), Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam : ℝ, IsEllipticFieldOn nu Lam W (Section6.fullCoefficientRecentered nu omega) :=
  w0_ae_isElliptic_bounded SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

/-- Witness for the rescaled field under the Dirac zero law. -/
example [NeZero d] {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ ε : ℝ, ε ≠ 0 → ∀ W : Set (Vec d), Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam : ℝ, IsEllipticFieldOn nu Lam W (Section8.epCoeff nu omega ε) :=
  w0_ae_isElliptic_rescaled SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end SuperdiffusionCLT.Section7
