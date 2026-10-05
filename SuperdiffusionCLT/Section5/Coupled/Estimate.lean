/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.PointwiseB
public import SuperdiffusionCLT.Section5.Principal.FreshMeasurableB

/-!
# `lem.coupled.input`: measurability of the box quantities

For a selection `wD` of the cube Dirichlet response of `hshellFlux`, the box averages
`e_{D,z}`, `B_z`, `R_z` are measurable in the shell sequence.  This is what allows the
`lintegral` of a sum to be split in the assembly of `e.coupled.estimate` (the response family
itself is an arbitrary selection).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)
open scoped ENNReal

variable {d : ℕ}

theorem coupled4_measurable_entry (l L : ℕ) (hlL : l ≤ L) (y : Vec d) (i j : Fin d) :
    Measurable (fun omega : ShellSeq d => finiteShellIncrement omega l L y i j) := by
  have hfun : (fun omega : ShellSeq d => finiteShellIncrement omega l L y i j) =
      fun omega : ShellSeq d => streamCutoff omega L y i j - streamCutoff omega l y i j := by
    funext omega
    rw [finiteShellIncrement_apply_eq_streamCutoff_sub omega hlL y]
    rfl
  rw [hfun]
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_streamCutoff_apply L y))).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_streamCutoff_apply l y))))

theorem coupled4_measurable_vecNormSq {α : Type*} [MeasurableSpace α] {f : α → Vec d}
    (hf : Measurable f) : Measurable (fun a => vecNormSq (f a)) := by
  unfold vecNormSq vecDot
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hf)

section Response

variable [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d)
  (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
  (hwD : ∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
    (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega))

include hwD in
theorem coupled4_measurable_gradClass :
    Measurable fun omega : ShellSeq d => (wD omega).toH1Function.gradToHilbertVectorL2 := by
  have hFmeas := pmeas_measurable_fluxClass_fresh (d := d) (Set.Ioc (m - h) m) (Kc := Kc)
    (F := fun omega => hshellFlux nu P m h omega e)
    (fun omega => pmeas_continuous_hshellFlux nu P m h omega e)
    (fun x => pmeas_measurable_hshellFlux_fresh nu P m h e x)
  exact pmeas_measurable_gradClass_dirichlet
    (fun omega => SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ)
      (pmeas_continuous_hshellFlux nu P m h omega e))
    (hFmeas.mono (shellSigma_le_ambient (d := d) _) le_rfl) hwD

include hwD in
theorem coupled4_measurable_E (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) :
    Measurable fun omega : ShellSeq d => coupledE Q (wD omega).toH1Function.grad :=
  (pmeas_measurable_dirichlet_average_fresh nu P m h Kc e wD hwD Q hQ).mono
    (shellSigma_le_ambient (d := d) _) le_rfl

include hwD in
theorem coupled4_measurable_B (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) :
    Measurable fun omega : ShellSeq d => coupledB m h Q omega (wD omega).toH1Function.grad := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hfun0 : (fun omega : ShellSeq d => coupledB m h Q omega (wD omega).toH1Function.grad) =
      fun omega => volumeAverageVec (openCubeSet Q)
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
          ((wD omega).toH1Function.grad x)) :=
    funext fun omega => coupledB_eq_open m h Q omega _
  rw [hfun0]
  refine Measurable.of_eval fun i => ?_
  have hmL : m - h ≤ m := Nat.sub_le m h
  have hrowcont : ∀ omega : ShellSeq d,
      Continuous fun y : Vec d => (fun j => finiteShellIncrement omega (m - h) m y i j : Vec d) :=
    fun omega => continuous_pi fun j => coupled3_continuous_entry omega (m - h) m i j
  have hrowjoint : Measurable fun q : ShellSeq d × Vec d =>
      (fun j => finiteShellIncrement q.1 (m - h) m q.2 i j : Vec d) :=
    SuperdiffusionCLT.Section3.Setup.measurable_prod_of_continuous_of_measurable
      (G := fun omega y => (fun j => finiteShellIncrement omega (m - h) m y i j : Vec d))
      hrowcont (fun x => Measurable.of_eval fun j => coupled4_measurable_entry _ _ hmL x i j)
  have hV : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet Q).measurableSet
  have hKmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (Set.indicator (openCubeSet Q)
        (fun y => (fun j => finiteShellIncrement omega (m - h) m y i j : Vec d))) :=
    fun omega => (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ)
      (hrowcont omega)).indicator hV
  have hKjoint : Measurable fun q : ShellSeq d × Vec d =>
      Set.indicator (openCubeSet Q)
        (fun y => (fun j => finiteShellIncrement q.1 (m - h) m y i j : Vec d)) q.2 := by
    have hrw : (fun q : ShellSeq d × Vec d =>
        Set.indicator (openCubeSet Q)
          (fun y => (fun j => finiteShellIncrement q.1 (m - h) m y i j : Vec d)) q.2) =
        Set.indicator (Prod.snd ⁻¹' openCubeSet Q)
          (fun q : ShellSeq d × Vec d =>
            (fun j => finiteShellIncrement q.1 (m - h) m q.2 i j : Vec d)) := by
      funext q
      by_cases hq : q.2 ∈ openCubeSet Q
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' openCubeSet Q from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' openCubeSet Q from hq)]
    rw [hrw]
    exact hrowjoint.indicator (measurable_snd hV)
  have hKclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hKmem omega) :=
    SuperdiffusionCLT.Section3.Setup.measurable_toHilbertVectorL2OfVecField_of_measurable
      hKjoint hKmem
  have hGclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (wD omega).toH1Function.grad_memVectorL2 :=
    coupled4_measurable_gradClass nu P m h Kc e wD hwD
  have hfun : (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q)
      (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
        ((wD omega).toH1Function.grad x)) i) =
      fun omega : ShellSeq d => (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hKmem omega))
          (toHilbertVectorL2OfVecField (wD omega).toH1Function.grad_memVectorL2) := by
    funext omega
    exact SuperdiffusionCLT.Section3.Setup.volumeAverageVec_matVecMul_eq_inner hQ hV
      (fun y => finiteShellIncrement omega (m - h) m y) (wD omega).toH1Function.grad_memVectorL2 i
      (hKmem omega)
  rw [hfun]
  exact (continuous_inner.measurable.comp (hKclass.prodMk hGclass)).const_mul _

include hwD in
theorem coupled4_measurable_R (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ))) :
    Measurable fun omega : ShellSeq d => coupledR m h Q omega (wD omega).toH1Function.grad := by
  have hB := coupled4_measurable_B nu P m h Kc e wD hwD Q hQ
  have hE := coupled4_measurable_E nu P m h Kc e wD hwD Q hQ
  refine Measurable.of_eval fun i => ?_
  have hG : ∀ a b : Fin d, Measurable fun omega : ShellSeq d => principalGauge m h Q omega a b :=
    fun a b => (pmeas_measurable_principalGauge_entry_fresh m h Q a b).mono
      (shellSigma_le_ambient (d := d) _) le_rfl
  have h1 : Measurable fun omega : ShellSeq d =>
      matVecMul (principalGauge m h Q omega) (coupledE Q (wD omega).toH1Function.grad) i :=
    Finset.measurable_sum _ fun j _ => (hG i j).mul ((measurable_pi_apply j).comp hE)
  exact ((measurable_pi_apply i).comp hB).sub h1

end Response

end SuperdiffusionCLT.Section5
