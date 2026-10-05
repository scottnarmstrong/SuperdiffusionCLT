/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.CellErrorMeasurable
public import SuperdiffusionCLT.Section5.Localization.BasicSplitB
public import SuperdiffusionCLT.Section5.Principal.AssemblyG
public import SuperdiffusionCLT.Section5.Neumann.NeumannInputE

/-!
# `cor.upper.ratio`: the global competitor

The global state `G` of `e.setup.basic-split` with potential `s^{-1/2}(e' + ∇w_D)` and flux
`s^{1/2}(e + ∇w_N + F)` is admissible for the slope `s^{-1/2} e'`, `s^{1/2} e` on a cube whenever `∇w_D`
is a zero-trace potential and `∇w_N + F` is solenoidal with zero normal trace.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The global state of `e.setup.basic-split`. -/
noncomputable def upperRatio_state (s : ℝ) (e e' : Vec d) (gD gN : Vec d → Vec d) :
    BlockState d where
  potential x := s ^ (-(1 : ℝ) / 2) • (e' + gD x)
  flux x := s ^ ((1 : ℝ) / 2) • (e + gN x)

theorem upperRatio_state_admissible {U : Set (Vec d)} (s : ℝ) (e e' : Vec d)
    {gD gN : Vec d → Vec d} (hD : MemVectorL2 U gD) (hDz : IsPotentialZeroTraceOn U gD)
    (hN : MemVectorL2 U gN) (hNs : IsSolenoidalZeroNormalTraceOn U gN) :
    IsBlockMuAdmissible U (s ^ (-(1 : ℝ) / 2) • e', s ^ ((1 : ℝ) / 2) • e)
      (upperRatio_state s e e' gD gN) := by
  have e1 : (fun x => (upperRatio_state s e e' gD gN).potential x -
      (s ^ (-(1 : ℝ) / 2) • e', s ^ ((1 : ℝ) / 2) • e).1) =
      fun x => s ^ (-(1 : ℝ) / 2) • gD x := by
    funext x
    simp only [upperRatio_state, smul_add, add_sub_cancel_left]
  have e2 : (fun x => (upperRatio_state s e e' gD gN).flux x -
      (s ^ (-(1 : ℝ) / 2) • e', s ^ ((1 : ℝ) / 2) • e).2) =
      fun x => s ^ ((1 : ℝ) / 2) • gN x := by
    funext x
    simp only [upperRatio_state, smul_add, add_sub_cancel_left]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact hD.const_smul (s ^ (-(1 : ℝ) / 2))
  · rw [e1]; exact isPotentialZeroTraceOn_smul hDz _
  · rw [e2]; exact hN.const_smul (s ^ ((1 : ℝ) / 2))
  · rw [e2]; exact isSolenoidalZeroNormalTraceOn_smul hNs _

/-- The Neumann response plus the flux is solenoidal with zero normal trace. -/
theorem upperRatio_solenoidal (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse Q F w) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x => w.toH1Function.grad x + F x) := by
  intro φ
  have h := hw φ.toMeanZero
  have hg : φ.toMeanZero.toH1Function.grad = φ.grad := funext fun x => H1Function.toMeanZero_grad φ x
  rw [hg] at h
  have i1 := integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2 φ.grad_memVectorL2
  have i2 := integrableOn_vecDot_of_memVectorL2 hF φ.grad_memVectorL2
  have e : (fun x => vecDot (w.toH1Function.grad x + F x) (φ.grad x)) =
      fun x => vecDot (w.toH1Function.grad x) (φ.grad x) + vecDot (F x) (φ.grad x) := by
    funext x
    simp [vecDot, Finset.sum_add_distrib, add_mul]
  rw [e, integral_add i1 i2, h]
  ring

end SuperdiffusionCLT.Section5
