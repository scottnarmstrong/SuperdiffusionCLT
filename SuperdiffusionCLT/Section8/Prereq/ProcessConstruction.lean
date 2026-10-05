/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.FiniteTime.KernelEquivariance
public import MarkovProcess.Main
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestrictionMarginals

/-!
# Finite-dimensional laws of a semigroup read inside a larger state space

Let `S` be a conservative kernel semigroup on `α`, let `P'` be a conservative kernel semigroup on
`β`, and let `e : α → β` be measurable with `P' t (e x) = (S t x).map e`.  Then every
finite-time kernel of `P'` started at `e x` is the image under the coordinatewise map `e` of the
finite-time kernel of `S` started at `x`.  The same holds for finite sets of times.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section FiniteTime

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The finite-time kernels of `P'` at the image of a point are the coordinatewise image of the
finite-time kernels of `S`. -/
theorem procConstr_finiteTimeKernel_apply_map
    {S : SubMarkovKernelSemigroup α} {P' : SubMarkovKernelSemigroup β}
    (hS : S.IsConservative) (hP' : P'.IsConservative) {e : α → β} (he : Measurable e)
    (hkern : ∀ t x, P' t (e x) = (S t x).map e) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n) (x : α),
      finiteTimeKernel P' times (e x) =
        (finiteTimeKernel S times x).map (FiniteOrderedTimes.mapPath e) := by
  intro n
  induction n with
  | zero =>
      intro times x
      simp only [finiteTimeKernel_zero, Kernel.const_apply]
      rw [Measure.map_dirac' (FiniteOrderedTimes.measurable_mapPath (ι := Fin 0) he)]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      intro times x
      have hmapn : Measurable
          (FiniteOrderedTimes.mapPath e : (Fin n → α) → Fin n → β) :=
        FiniteOrderedTimes.measurable_mapPath he
      have hmapn1 : Measurable
          (FiniteOrderedTimes.mapPath e : (Fin (n + 1) → α) → Fin (n + 1) → β) :=
        FiniteOrderedTimes.measurable_mapPath he
      let : IsMarkovKernel (finiteTimeKernel S times.relativeTail) :=
        hS.isMarkovKernel_finiteTimeKernel S times.relativeTail
      let : IsMarkovKernel (finiteTimeKernel P' times.relativeTail) :=
        hP'.isMarkovKernel_finiteTimeKernel P' times.relativeTail
      let : IsMarkovKernel (S (times 0)) := hS.isMarkovKernel (times 0)
      let : IsMarkovKernel (P' (times 0)) := hP'.isMarkovKernel (times 0)
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _ measurable_finCons,
        Kernel.map_apply _ measurable_finCons, Measure.map_map hmapn1 measurable_finCons]
      ext s hs
      rw [Measure.map_apply measurable_finCons hs,
        Measure.map_apply (hmapn1.comp measurable_finCons) hs,
        Kernel.compProd_apply (measurable_finCons hs),
        Kernel.compProd_apply ((hmapn1.comp measurable_finCons) hs), hkern, lintegral_map]
      · refine lintegral_congr fun z ↦ ?_
        simp only [Kernel.prodMkLeft_apply]
        rw [ih times.relativeTail z, Measure.map_apply hmapn
          (measurable_prodMk_left (measurable_finCons hs))]
        congr 1
        ext w
        simp only [Set.mem_preimage, Function.comp_apply]
        exact Iff.of_eq (congrArg (· ∈ s)
          (FiniteOrderedTimes.mapPath_finCons (n := n) e (z, w)).symm)
      · exact Kernel.measurable_kernel_prodMk_left (measurable_finCons hs)
      · exact he

/-- The finite-set kernels of `P'` at the image of a point are the coordinatewise image of the
finite-set kernels of `S`. -/
theorem procConstr_finiteSetKernel_apply_map
    {S : SubMarkovKernelSemigroup α} {P' : SubMarkovKernelSemigroup β}
    (hS : S.IsConservative) (hP' : P'.IsConservative) {e : α → β} (he : Measurable e)
    (hkern : ∀ t x, P' t (e x) = (S t x).map e) (I : Finset ℝ≥0) (x : α) :
    finiteSetKernel P' I (e x) =
      (finiteSetKernel S I x).map (fun f : I → α ↦ fun i ↦ e (f i)) := by
  have hmap : Measurable (fun f : I → α ↦ fun i ↦ e (f i)) :=
    measurable_pi_iff.mpr fun i ↦ he.comp (measurable_pi_apply i)
  have hmapF : Measurable
      (FiniteOrderedTimes.mapPath e : (Fin I.card → α) → Fin I.card → β) :=
    FiniteOrderedTimes.measurable_mapPath he
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, Kernel.map_apply _
    (measurable_orderedPathToFiniteSet I), Kernel.map_apply _
    (measurable_orderedPathToFiniteSet I),
    procConstr_finiteTimeKernel_apply_map hS hP' he hkern, Measure.map_map
    (measurable_orderedPathToFiniteSet I) hmapF, Measure.map_map hmap
    (measurable_orderedPathToFiniteSet I)]
  rfl

end FiniteTime

end

end SuperdiffusionCLT.Section8
