/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ProcessUniquenessC
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsE

/-!
# Theorem A: existence, uniqueness and the link to the constructed process

For almost every sample the pair `(S, Q)` of the specification exists and is unique.  Every
`FieldInputData` of the sample has kernel semigroup `S`, so the crude moment bounds, which are
stated for these kernel semigroups, are statements about the unique semigroup of the
specification.  The one-point marginal of `Q x` at time `t` is `S t x`.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section2.Cutoff
  SuperdiffusionCLT.Frozen.Assumptions

variable {d : ℕ}

/-- **Existence clause of Theorem A**, in the shape of the printed statement. -/
theorem thmA_existence [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ S : SubMarkovKernelSemigroup (Vec d),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S ∧
          ∃ Q : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw S Q := by
  filter_upwards [domId_ae_exists_process hPrefix hJ3 hnu] with omega h
  obtain ⟨S, Q, hS, hQ⟩ := h
  exact ⟨S, hS, Q, hQ⟩

/-- **Link to the moment lemmas.**  For almost every sample and every `FieldInputData` of the
sample, the kernel semigroup of its resolvent satisfies the specification, carries a
continuous-path law, and is the only semigroup satisfying the specification. -/
theorem thmA_link_data [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ D : FieldInputData d nu (fullStreamRecentered omega),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega)
            D.logGrowthBounds.resolvent.kernelSemigroup ∧
          (∃ Q : Vec d → Measure (ContinuousPath (Vec d)),
            IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q) ∧
          ∀ S : SubMarkovKernelSemigroup (Vec d),
            IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S →
              S = D.logGrowthBounds.resolvent.kernelSemigroup := by
  filter_upwards [fieldReg_ae_contDiff_two_fullStreamRecentered hJ3,
    ae_contDiff_fullStreamRecentered hJ3] with omega h2 h1 D
  have hA : D.analyticData.a = fullCoefficientRecentered nu omega := rfl
  have h1' : ∀ i j, ContDiff ℝ 1 fun y ↦ D.analyticData.a y i j := fun i j => by
    rw [hA]; exact domId_entries_contDiff h1 i j
  have hdf := domId_isDivergenceFormFeller D.analyticData h1'
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal
    D.logGrowthBounds.isConservative_kernelSemigroup
  rw [hA] at hdf
  refine ⟨hdf, ?_, fun S hS => ?_⟩
  · exact procConstr_exists_isContinuousPathLaw D.logGrowthBounds.processInput
      D.logGrowthBounds.isConservative_kernelSemigroup
  · have h2' : ContDiff ℝ 2 (fullCoefficientRecentered nu omega) := contDiff_const.add h2
    have ha : ∀ i j, ContDiff ℝ 2 fun y ↦ D.analyticData.a y i j := fun i j ↦ by
      rw [hA]; exact contDiff_pi.1 (contDiff_pi.1 h2' i) j
    exact procUniq_kernelSemigroup_eq (fullCoefficientRecentered nu omega)
      D.logGrowthBounds.resolvent
      (fun mu g hg hc ↦ by
        have := procUniq_hreg D.analyticData ha
          D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal mu g hg hc
        rwa [hA] at this) hS

/-- **Transfer, semigroups.**  Almost surely any two semigroups satisfying the specification
coincide, and one exists. -/
theorem thmA_transfer_semigroup [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ S₀ : SubMarkovKernelSemigroup (Vec d),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S₀ ∧
          ∀ S : SubMarkovKernelSemigroup (Vec d),
            IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S → S = S₀ := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu, thmA_link_data (nu := nu) hJ3]
    with omega hD hL
  obtain ⟨D⟩ := hD
  obtain ⟨h1, -, h3⟩ := hL D
  exact ⟨_, h1, h3⟩

/-- Two semigroup-valued functions satisfying the specification almost surely agree almost
surely. -/
theorem thmA_ae_eq [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu)
    {S S' : ShellSeq d → SubMarkovKernelSemigroup (Vec d)}
    (hS : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      IsDivergenceFormFeller (fullCoefficientRecentered nu omega) (S omega))
    (hS' : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      IsDivergenceFormFeller (fullCoefficientRecentered nu omega) (S' omega)) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, S omega = S' omega := by
  filter_upwards [thmA_transfer_semigroup hPrefix hJ3 hnu, hS, hS'] with omega h0 h1 h2
  obtain ⟨S₀, -, hu⟩ := h0
  rw [hu _ h1, hu _ h2]

theorem thmA_kernel_eval (S : SubMarkovKernelSemigroup (Vec d)) (n : ℕ) (hn : n = 1)
    (times : FiniteOrderedTimes n) (i : Fin n) :
    (S.finiteTimeKernel times).map (fun p => p i) = S (times i) := by
  subst hn
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval S times

/-- **The one-point marginal.**  Under `Q x` the position at time `t` has law `S t x`. -/
theorem thmA_marginal {S : SubMarkovKernelSemigroup (Vec d)}
    {Q : Vec d → Measure (ContinuousPath (Vec d))} (hQ : IsContinuousPathLaw S Q)
    (t : ℝ≥0) (x : Vec d) :
    (Q x).map (fun w : ContinuousPath (Vec d) => w t) = S t x := by
  have h := (hQ x).2 {t}
  let ev : ContinuousPath (Vec d) → ({t} : Finset ℝ≥0) → Vec d :=
    ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0)
  let pr : (({t} : Finset ℝ≥0) → Vec d) → Vec d :=
    fun f => f ⟨t, Finset.mem_singleton_self t⟩
  have hev : (fun w : ContinuousPath (Vec d) => w t) = pr ∘ ev := rfl
  have hm1 : Measurable ev :=
    measurable_pi_iff.mpr fun s => ContinuousPath.measurable_coordinateProcess (s : ℝ≥0)
  have hm2 : Measurable pr := measurable_pi_apply _
  have h2 : (Q x).map (fun w : ContinuousPath (Vec d) => w t) =
      ((Q x).map ev).map pr := by
    rw [hev]; exact (Measure.map_map hm2 hm1).symm
  rw [h2, h, SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
  have hm3 := SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet (α := Vec d) {t}
  rw [ProbabilityTheory.Kernel.map_apply _ hm3, Measure.map_map hm2 hm3]
  set i0 : Fin ({t} : Finset ℝ≥0).card :=
    (({t} : Finset ℝ≥0).orderIsoOfFin rfl).symm ⟨t, Finset.mem_singleton_self t⟩ with hi0
  have key : pr ∘ SubMarkovKernelSemigroup.orderedPathToFiniteSet (α := Vec d) {t} =
      fun path : Fin ({t} : Finset ℝ≥0).card → Vec d => path i0 := rfl
  rw [key]
  have hk := thmA_kernel_eval S (({t} : Finset ℝ≥0).card) (Finset.card_singleton t)
    (SubMarkovKernelSemigroup.finiteSetTimes ({t} : Finset ℝ≥0)) i0
  have ht : SubMarkovKernelSemigroup.finiteSetTimes ({t} : Finset ℝ≥0) i0 = t :=
    Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ rfl i0)
  rw [ht] at hk
  rw [← ProbabilityTheory.Kernel.map_apply _ (measurable_pi_apply i0), hk]

/-- The expectation of an observable of the position at time `t` is its integral against
`S t x`. -/
theorem thmA_integral_marginal {S : SubMarkovKernelSemigroup (Vec d)}
    {Q : Vec d → Measure (ContinuousPath (Vec d))} (hQ : IsContinuousPathLaw S Q)
    (t : ℝ≥0) (x : Vec d) {f : Vec d → ℝ} (hf : Measurable f) :
    ∫ w, f (w t) ∂(Q x) = ∫ y, f y ∂(S t x) := by
  have hm : Measurable (fun w : ContinuousPath (Vec d) => w t) :=
    ContinuousPath.measurable_coordinateProcess t
  rw [← thmA_marginal hQ t x, integral_map hm.aemeasurable hf.aestronglyMeasurable]

end SuperdiffusionCLT.Section8
