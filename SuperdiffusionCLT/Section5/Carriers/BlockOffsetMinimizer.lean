/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffset
public import Homogenization.CoarseGraining.MuRecovery

/-!
# Offset block minimizers: existence and uniqueness from recovery data

For a bounded domain `U` carrying `Homogenization.MuCorrectionSpaceRecoveryData` and a bounded
elliptic coefficient operator (`Homogenization.MuOperatorRealization`), and an offset
`F : BlockState d` with `L²` components, the class `IsBlockOffsetAdmissible U F` has an energy
minimizer (`exists_isBlockOffsetMinimizer_of_recovery`).

Uniqueness holds only almost everywhere: modifying a minimizer on a null set gives another
minimizer, so the literal `∃!` is false and the correct statement is that the minimizer is unique
as an element of `L²`. The `L²` hypothesis on the offset is necessary, since for a non-integrable
energy the Bochner integral is `0`.

The proof is the Hilbert-space affine minimization of `Homogenization.HilbertMinimization`, with
the offset embedded in `L²` in place of a constant.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

theorem memBlockL2_eval_of_components {X : BlockState d} (hp : MemVectorL2 U X.potential)
    (hf : MemVectorL2 U X.flux) : MemBlockL2 U X.eval :=
  memBlockL2_blockField hp hf

theorem IsBlockOffsetAdmissible.memVectorL2_potential {F X : BlockState d}
    (hF : MemVectorL2 U F.potential) (hX : IsBlockOffsetAdmissible U F X) :
    MemVectorL2 U X.potential := by
  have h := hX.1.add hF
  have he : ((fun x => X.potential x - F.potential x) + F.potential) = X.potential := by
    funext x; simp
  rwa [he] at h

theorem IsBlockOffsetAdmissible.memVectorL2_flux {F X : BlockState d}
    (hF : MemVectorL2 U F.flux) (hX : IsBlockOffsetAdmissible U F X) :
    MemVectorL2 U X.flux := by
  have h := hX.2.2.1.add hF
  have he : ((fun x => X.flux x - F.flux x) + F.flux) = X.flux := by
    funext x; simp
  rwa [he] at h

theorem toHilbert_sub_eq_components {W F : BlockState d}
    (hW : MemBlockL2 U W.eval) (hF : MemBlockL2 U F.eval)
    (h1 : MemVectorL2 U (fun x => W.potential x - F.potential x))
    (h2 : MemVectorL2 U (fun x => W.flux x - F.flux x)) :
    toHilbertBlockL2OfBlockField hW - toHilbertBlockL2OfBlockField hF =
      toHilbertBlockL2OfComponents h1 h2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [MeasureTheory.Lp.coeFn_sub (toHilbertBlockL2OfBlockField hW) (toHilbertBlockL2OfBlockField hF),
       coeFn_toHilbertBlockL2OfBlockField (U := U) hW,
       coeFn_toHilbertBlockL2OfBlockField (U := U) hF,
       coeFn_toHilbertBlockL2OfComponents h1 h2] with x hs hw hf hc
  rw [hs, hc]
  simp only [Pi.sub_apply, hw, hf]
  apply HilbertBlockVec.ext
  · ext i
    simp [BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]
  · ext i
    simp [BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]

theorem toHilbertBlockL2OfComponents_congr {f f' g g' : Vec d → Vec d} (hf : f = f') (hg : g = g')
    (h1 : MemVectorL2 U f) (h2 : MemVectorL2 U g) (h1' : MemVectorL2 U f')
    (h2' : MemVectorL2 U g') :
    toHilbertBlockL2OfComponents h1 h2 = toHilbertBlockL2OfComponents h1' h2' := by
  subst hf hg
  rfl

/-- The Hilbert image of an admissible state differs from that of the offset by an element of the
correction space. -/
theorem toHilbert_sub_mem_correctionSpace (R : MuCorrectionSpaceRecoveryData U)
    {F X : BlockState d} (hFp : MemVectorL2 U F.potential) (hFf : MemVectorL2 U F.flux)
    (hX : IsBlockOffsetAdmissible U F X) :
    toHilbertBlockL2OfBlockField
        (memBlockL2_eval_of_components (hX.memVectorL2_potential hFp) (hX.memVectorL2_flux hFf)) -
      toHilbertBlockL2OfBlockField (memBlockL2_eval_of_components hFp hFf) ∈
        R.correctionSpace := by
  rw [toHilbert_sub_eq_components _ _ hX.1 hX.2.2.1]
  exact R.mem_correctionSpace hX.1 hX.2.2.1 hX.2.1 hX.2.2.2

/-- Existence, with the Hilbert image of the minimizer identified as the canonical affine
minimizer. -/
theorem exists_admissible_toHilbert_eq (R : MuCorrectionSpaceRecoveryData U)
    (Op : MuOperatorRealization U a) {F : BlockState d}
    (hFp : MemVectorL2 U F.potential) (hFf : MemVectorL2 U F.flux) :
    ∃ (X : BlockState d) (hX : IsBlockOffsetAdmissible U F X),
      toHilbertBlockL2OfBlockField
          (memBlockL2_eval_of_components (hX.memVectorL2_potential hFp)
            (hX.memVectorL2_flux hFf)) =
        affineMinimizerMap R.correctionSpace (energyBilinOfOperator Op.operator)
          Op.operatorCoercive
          (toHilbertBlockL2OfBlockField (memBlockL2_eval_of_components hFp hFf)) := by
  set x := toHilbertBlockL2OfBlockField (memBlockL2_eval_of_components hFp hFf) with hx
  set m := affineMinimizerMap R.correctionSpace (energyBilinOfOperator Op.operator)
    Op.operatorCoercive x with hm
  have hmem : m - x ∈ R.correctionSpace :=
    sub_affineMinimizerMap_apply_mem R.correctionSpace _ Op.operatorCoercive x
  let Y : R.correctionSpace.toSubmodule := ⟨m - x, hmem⟩
  let Z := R.repr Y
  let X : BlockState d := ⟨fun y => F.potential y + Z.potential y, fun y => F.flux y + Z.flux y⟩
  have e1 : (fun y => X.potential y - F.potential y) = Z.potential := by
    funext y; simp [X]
  have e2 : (fun y => X.flux y - F.flux y) = Z.flux := by
    funext y; simp [X]
  have hadm : IsBlockOffsetAdmissible U F X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; exact Z.potential_memL2
    · rw [e1]; exact Z.isPotentialZeroTrace
    · rw [e2]; exact Z.flux_memL2
    · rw [e2]; exact Z.isSolenoidalZeroNormalTrace
  refine ⟨X, hadm, ?_⟩
  have hsub := toHilbert_sub_eq_components
    (memBlockL2_eval_of_components (hadm.memVectorL2_potential hFp) (hadm.memVectorL2_flux hFf))
    (memBlockL2_eval_of_components hFp hFf) hadm.1 hadm.2.2.1
  have hZ : toHilbertBlockL2OfComponents hadm.1 hadm.2.2.1 = m - x := by
    rw [toHilbertBlockL2OfComponents_congr e1 e2 hadm.1 hadm.2.2.1 Z.potential_memL2
      Z.flux_memL2]
    exact R.repr_eq Y
  rw [hZ] at hsub
  rw [← hx] at hsub
  exact sub_left_inj.mp hsub

theorem volumeAverage_blockEnergyDensity_eq_quadraticEnergy (Op : MuOperatorRealization U a)
    {X : BlockState d} (hX : MemBlockL2 U X.eval) :
    volumeAverage U (blockEnergyDensity a X) =
      quadraticEnergy (energyBilinOfOperator Op.operator) (toHilbertBlockL2OfBlockField hX) :=
  (Op.quadraticEnergy_eq_blockEnergyAverage_of_blockState hX).symm

theorem ae_eq_of_toHilbert_eq {W X : BlockState d} (hW : MemBlockL2 U W.eval)
    (hX : MemBlockL2 U X.eval)
    (h : toHilbertBlockL2OfBlockField hW = toHilbertBlockL2OfBlockField hX) :
    W.potential =ᵐ[volumeMeasureOn U] X.potential ∧ W.flux =ᵐ[volumeMeasureOn U] X.flux := by
  have hae : ∀ᵐ x ∂volumeMeasureOn U,
      HilbertBlockVec.ofBlockVec (W.eval x) = HilbertBlockVec.ofBlockVec (X.eval x) := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := U) hW,
      coeFn_toHilbertBlockL2OfBlockField (U := U) hX] with x h1 h2
    have := congrArg (fun Z : HilbertBlockL2 U => (Z : Vec d → HilbertBlockVec d) x) h
    simp only [h1, h2] at this
    exact this
  have hae' : ∀ᵐ x ∂volumeMeasureOn U, W.eval x = X.eval x := by
    filter_upwards [hae] with x hx
    simpa using congrArg HilbertBlockVec.toBlockVec hx
  exact ⟨by filter_upwards [hae'] with x hx; exact congrArg Prod.fst hx,
    by filter_upwards [hae'] with x hx; exact congrArg Prod.snd hx⟩

/-- Existence and almost-everywhere uniqueness of the offset minimizer, from recovery data. -/
theorem exists_isBlockOffsetMinimizer_of_recovery (R : MuCorrectionSpaceRecoveryData U)
    (Op : MuOperatorRealization U a) {F : BlockState d}
    (hFp : MemVectorL2 U F.potential) (hFf : MemVectorL2 U F.flux) :
    ∃ X : BlockState d, IsBlockOffsetMinimizer a U F X ∧
      ∀ W : BlockState d, IsBlockOffsetMinimizer a U F W →
        W.potential =ᵐ[volumeMeasureOn U] X.potential ∧ W.flux =ᵐ[volumeMeasureOn U] X.flux := by
  obtain ⟨X, hadm, hXm⟩ := exists_admissible_toHilbert_eq R Op hFp hFf
  have hsymm := energyBilinOfOperator_symm Op.operator Op.operatorSymm
  have hXmem := memBlockL2_eval_of_components (hadm.memVectorL2_potential hFp)
    (hadm.memVectorL2_flux hFf)
  refine ⟨X, ⟨hadm, fun Y hY => ?_⟩, fun W hW => ?_⟩
  · have hYmem := memBlockL2_eval_of_components (hY.memVectorL2_potential hFp)
      (hY.memVectorL2_flux hFf)
    rw [volumeAverage_blockEnergyDensity_eq_quadraticEnergy Op hXmem,
      volumeAverage_blockEnergyDensity_eq_quadraticEnergy Op hYmem, hXm]
    exact affineMinimizerMap_minimizes_quadraticEnergy R.correctionSpace Op.operatorCoercive hsymm _ _
      (toHilbert_sub_mem_correctionSpace R hFp hFf hY)
  · have hWmem := memBlockL2_eval_of_components (hW.1.memVectorL2_potential hFp)
      (hW.1.memVectorL2_flux hFf)
    have hle := hW.2 X hadm
    rw [volumeAverage_blockEnergyDensity_eq_quadraticEnergy Op hXmem,
      volumeAverage_blockEnergyDensity_eq_quadraticEnergy Op hWmem, hXm] at hle
    have hEq := eq_affineMinimizerMap_of_quadraticEnergy_le R.correctionSpace Op.operatorCoercive
      hsymm _ _ (toHilbert_sub_mem_correctionSpace R hFp hFf hW.1) hle
    exact ae_eq_of_toHilbert_eq hWmem hXmem (hEq.trans hXm.symm)


end SuperdiffusionCLT.Section5
