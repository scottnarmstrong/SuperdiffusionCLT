/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.LowerRatioC
public import SuperdiffusionCLT.Section5.Localization.LocalizationC
public import SuperdiffusionCLT.Section5.Localization.BasicSplitB
public import SuperdiffusionCLT.Section5.Carriers.BlockOffsetMinimizerB

/-!
# `cor.lower.ratio`: the basic split at `e' = 0`

The global offset `G = P₀ + bfAhom^{-1/2}(∇w_D, 0)` of the setup is admissible for the slope
`P₀ = (0, shom^{1/2} e)`, and the basic split `e.setup.basic-split` applies.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

variable {d : ℕ}

/-- **The basic split at `e' = 0`, `w_N = 0`** (pointwise in the sample). -/
theorem lowerRatio_split [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h Kc n : ℕ) (hn : n ≤ Kc)
    (Pl : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (e : Vec d) (omega : ShellSeq d)
    (wD : H10Function (openCubeSet (originCube d (Kc : ℤ)))) (gN : Vec d → Vec d)
    (hgN : ∀ y, gN y = 0) (S St : TriadicCube d → BlockState d)
    (hS : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
        (constBlockState (blockSlope nu (m - h) Pl Q e 0 wD.toH1Function.grad gN)) (S Q))
    (hSt : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
        (blockFluct nu (m - h) Pl Q wD.toH1Function.grad gN) (St Q)) :
    blockVecDot ((0 : Vec d), (sigmaBarInfinite nu (m - h) Pl) ^ ((1 : ℝ) / 2) • e)
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu omega m).toCoeffField)
          ((0 : Vec d), (sigmaBarInfinite nu (m - h) Pl) ^ ((1 : ℝ) / 2) • e)) ≤
      subcubeMean (originCube d (Kc : ℤ)) (n : ℤ) (fun Q =>
        blockVecDot (blockSlope nu (m - h) Pl Q e 0 wD.toH1Function.grad gN)
            (blockMatVecMul (coarseBlockMatrix (cubeSet Q)
              (coefficientCutoff nu omega m).toCoeffField)
              (blockSlope nu (m - h) Pl Q e 0 wD.toH1Function.grad gN)) +
          volumeAverage (cubeSet Q) (fun x =>
            blockVecDot ((2 : ℝ) • blockSlope nu (m - h) Pl Q e 0 wD.toH1Function.grad gN +
                (St Q).eval x)
              (blockMatVecMul (blockCoeffField (coefficientCutoff nu omega m).toCoeffField x)
                ((St Q).eval x)))) := by
  obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m
    (originCube d (Kc : ℤ))
  set s : ℝ := sigmaBarInfinite nu (m - h) Pl with hs
  set G : BlockState d := ⟨fun x => s ^ (-(1 : ℝ) / 2) • wD.toH1Function.grad x,
    fun x => s ^ ((1 : ℝ) / 2) • (e + gN x)⟩ with hG
  have hflux0 : (fun x => G.flux x - (s ^ ((1 : ℝ) / 2) • e)) = fun _ => (0 : Vec d) := by
    funext x
    simp [hG, hgN]
  have hGadm : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ)))
      ((0 : Vec d), s ^ ((1 : ℝ) / 2) • e) G := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (fun x => G.potential x - (0 : Vec d)) =
          fun x => s ^ (-(1 : ℝ) / 2) • wD.toH1Function.grad x := by
        funext x; simp [hG]
      show MemVectorL2 _ (fun x => G.potential x - (0 : Vec d))
      rw [this, memVectorL2_cubeSet_iff_openCubeSet]
      exact wD.toH1Function.grad_memVectorL2.const_smul (s ^ (-(1 : ℝ) / 2))
    · have : (fun x => G.potential x - (0 : Vec d)) =
          ((s ^ (-(1 : ℝ) / 2) : ℝ) • wD : H10Function (openCubeSet (originCube d (Kc : ℤ)))).toH1Function.grad := by
        funext x; simp [hG]; rfl
      show IsPotentialZeroTraceOn _ (fun x => G.potential x - (0 : Vec d))
      rw [this]
      exact isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet
        (H10Function.isPotentialZeroTraceOn _)
    · show MemVectorL2 _ (fun x => G.flux x - (s ^ ((1 : ℝ) / 2) • e))
      rw [hflux0]
      exact memVectorL2_const _
    · show IsSolenoidalZeroNormalTraceOn _ (fun x => G.flux x - (s ^ ((1 : ℝ) / 2) • e))
      rw [hflux0]
      intro φ
      simp [vecDot]
  have hagree : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ x ∈ cubeSet Q,
      G.potential x = (blockSlope nu (m - h) Pl Q e 0 wD.toH1Function.grad gN).1 +
          (blockFluct nu (m - h) Pl Q wD.toH1Function.grad gN).potential x ∧
        G.flux x = (blockSlope nu (m - h) Pl Q e 0 wD.toH1Function.grad gN).2 +
          (blockFluct nu (m - h) Pl Q wD.toH1Function.grad gN).flux x := by
    intro Q _ x _
    constructor
    · simp only [hG, blockSlope, blockFluct, ahomInvSqrtApply, zero_add, ← smul_add]
      congr 1
      abel
    · simp only [hG, blockSlope, blockFluct, ahomInvSqrtApply, ← smul_add]
      congr 1
      abel
  have hb := basic_split hn hEll hGadm hagree hS hSt
  exact hb.1.trans (le_of_eq hb.2)

end SuperdiffusionCLT.Section5
