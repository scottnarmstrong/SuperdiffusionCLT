/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupTransport
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3IntegrabilityC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscProduct
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PrintedFinal
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB

/-!
# Term 3: monotonicity of the coarse-grained display in its constant

The coarse-grained display `e.RHS.term3.A` of `l.RHS.term3` (the binder `_hCgBound` of
the final Term 3 statement) is read at the statement's own constant `Cerr`, whereas the reduction
`cg_bound_bridge` outputs it at the constant `Cerr = cgBoundConst Cp Cw Cb`.  Since the display
is monotone in its constant -- all the prefactors are nonnegative -- the output at a smaller
constant yields the display at any larger one.

## Main results

* `cgBound_mono`: the `_hCgBound` display is monotone in `Cerr`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The constant-shape bridge

The reduction `cg_bound_bridge` (`_hCgBound`) concludes the coarse-grained display at the
constant `Cerr = cgBoundConst Cp Cw Cb`, whereas the binder `_hCgBound` of the final Term 3
statement is read at the statement's own constant.  Since the display is monotone in its constant
-- all the prefactors are nonnegative -- the output at a smaller constant
yields the binder at any larger one.  The lemma below is exactly that bridge; it carries the
display as a hypothesis because the missing step is the assembly inputs, not the constant. -/

/-- **The `_hCgBound` display is monotone in its constant `Cerr`.**  The
error factor `3^{-(ℓ'-ℓ)/4} (L')^2 ν^{-5/2}` is nonnegative, so raising `Cerr`
raises the bound.  This turns the output of `cg_bound_bridge` at
`Cerr = cgBoundConst Cp Cw Cb` into the fixed-`Cerr` binder of the final Term 3 statement
as soon as `Cerr` dominates that constant. -/
theorem cgBound_mono {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {delta etaL Cerr Cerr' : ℝ} (hle : Cerr ≤ Cerr')
    (h : ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2)) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr' * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  have hnu5 : (0 : ℝ) ≤ nu ^ (-(5 : ℝ) / 2) := (Real.rpow_pos_of_pos hnu _).le
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) :=
    Real.rpow_nonneg (by norm_num) _
  have hL2 : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) :=
    pow_nonneg (Nat.cast_nonneg _) 2
  have hstep : Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
        ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) ≤
      Cerr' * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
        ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h3) hL2) hnu5
  exact le_trans h (by linarith only [hstep])

end

end SuperdiffusionCLT.Section3.Terms
