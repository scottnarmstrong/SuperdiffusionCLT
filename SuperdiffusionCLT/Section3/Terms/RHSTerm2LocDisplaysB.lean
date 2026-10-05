/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1LocalizationB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsE
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1MeasurableInputsC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2MeasurabilityB

/-!
# The two localization displays of `l.RHS.term2`

The display `e.RHS.term2.proxy.error` of the paper reads

`E[‖∇u_n − ∇ũ_n‖²_{L̲²(cu_m)}]^{1/2} + |p̃ − p|
   ≤ C ν^{-3/2} L' 3^{-(ℓ-n)/2} shom_{L',*}^{1/2}(cu_n)`,

and its printed derivation is "The localization estimate for minimizers, used
exactly as in `e.localization.minimizers.applied`, gives ...".  The two
displays are the residues `hLocM` and `hLocN` of the assembly of `l.RHS.term2`:
the first at the cube `cu_m` with the glued gradient fields `∇u_{L'} − ∇u_ℓ`,
the second at the cube `cu_n` with the two fields exchanged.  Both are the same
quantity with the roles of the two inner scales swapped, so a single theorem
covers them.

## The single input

`hLocMin` below is the third clause of the conclusion of the anchor
`cutoff_localization` (`e.localization.minimizers`), carried in
its original shape at the scale triple `(m, n, L) = (S.ell, S.n, S.LPrime)`,
exactly as the sibling module `RHSTerm1LocalizationB` carries it for Step 1 of
`l.RHS.term1`; the anchor file is never imported.  Everything below is the
printed chain "sub-cube decomposition + stationarity + Cauchy-Schwarz + the
annealed derivative moment" applied to that one clause: no further hypothesis
beyond the standing shell-law data, the scale ordering and the unit vector is
used.

## What is discharged

* the measurability in the sample of the annealed derivative carrier, which
  `RHSTerm1LocalizationB.localization_bridge` carries as `hMeasDeriv`, is
  discharged here by `measurable_shellDerivCubeLinftyENorm`;
* the annealed second-moment bound on the derivative window, a factor
  for which the window `S.LPrime` lies above the cube scale, is discharged by
  `sqrt_second_moment_shellDerivCubeLinftyENorm_high_le` at `a = S.ell`,
  `b = S.LPrime`, `r = S.n`, which needs only `S.n ≤ S.ell`;
* the two displays are not restated: `hLocM` and `hLocN` are both instances of
  the single estimate `hLoc_display_of_locMin`, uniform in the intermediate
  scale `r`.

## The constant

The earlier assembly recorded the two displays at the literal constant `1`, because
it specialized the bookkeeping constant `Cloc` of
`RHSTerm2Assembly.term2_of_residue` at `1`.  That literal is not reproducible
from the clause above: the chain produces the constant
`sqrt(Cloc * shellDerivLargeCubeMomentConst d)`, where `Cloc` is the clause's
own constant and `shellDerivLargeCubeMomentConst d` is the annealed-derivative
moment constant of `RHSTerm1InputsE`.  The displays below therefore carry the
existential constant `∃ C, 1 ≤ C ∧ ...`, which is the shape the printed
display's own `C` has and the shape the proxy-error input of `RHSTerm2Assembly` consumes;
pinning it to `1` would require `shellDerivLargeCubeMomentConst d ≤ 1`, which
is not available.

## References

* The paper: `e.RHS.term2.proxy.error` and the proof of `l.RHS.term2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The quenched energy display on one sub-cube -/

variable {nu : ℝ}

/-- **The quenched localization display on one scale-`n` sub-cube**, the energy
factor alone.  This is `RHSTerm1LocalizationB.subcube_flux_sq_le` with the
coefficient factor removed: the localization estimate
`RHSTerm1Localization.localization_minimizers_gluedSubcube` in the `ℝ≥0∞` cube
carrier, with the two constants combined and the `L^∞` window of the shell
derivative read at the translated shell sequence `z + cu_m` of the sub-cube
`z`, which is where the stationarity of the shell law enters. -/
theorem subcube_energy_sq_le (hnu : 0 < nu) (S : ScaleSelection) (F : Vec d)
    {Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
    (hCentre : ∀ omega' : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.n : ℤ)))
          (fun x => vecNormSq
            (cubeMaximizerGradient hnu omega' S.LPrime F (originCube d (S.n : ℤ)) x -
              cubeMaximizerGradient hnu omega' S.ell F (originCube d (S.n : ℤ)) x)) ≤
        Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
            anchorDerivSup S.ell S.LPrime S.n omega' * (nu⁻¹ * vecNormSq F))
    (hnm : S.n ≤ S.m) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    (vecCubeLpENorm R 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) ≤
      ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F) *
        shellDerivCubeLinftyENorm S.ell S.LPrime S.n
          (ShellField.translateSequence (triadicCubeShift R) omega) := by
  classical
  set om : ShellSeq d := ShellField.translateSequence (triadicCubeShift R) omega with hom
  have hmemV : MemVectorL2 (openCubeSet R)
      (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
        gluedGradientField hnu S.ell S.n S.m F omega x) :=
    (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega R).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega R)
  have hV2 : (vecCubeLpENorm R 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) ≤
      ENNReal.ofReal (Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
        anchorDerivSup S.ell S.LPrime S.n om * (nu⁻¹ * vecNormSq F)) :=
    vecCubeLpENorm_two_sq_le_of_volumeAverage_le hmemV
      (localization_minimizers_gluedSubcube hnu hnm F hCentre omega hR)
  have hpow3 : (3 : ℝ) ^ S.n = (3 : ℝ) ^ ((S.n : ℝ)) := (Real.rpow_natCast 3 S.n).symm
  have hpownu : nu ^ (-(2 : ℝ)) * nu⁻¹ = nu ^ (-(3 : ℝ)) := by
    rw [show nu⁻¹ = nu ^ (-(1 : ℝ)) from by rw [Real.rpow_neg (le_of_lt hnu), Real.rpow_one],
      ← Real.rpow_add hnu]
    norm_num
  have hKsplit : Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
        anchorDerivSup S.ell S.LPrime S.n om * (nu⁻¹ * vecNormSq F) =
      (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F) *
        anchorDerivSup S.ell S.LPrime S.n om := by
    rw [← hpow3, ← hpownu]
    ring
  have hK0 : (0 : ℝ) ≤ Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F := by
    have h1 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((S.n : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have h3 : (0 : ℝ) ≤ vecNormSq F := vecNormSq_nonneg F
    exact mul_nonneg (mul_nonneg (mul_nonneg hCloc0 h1) h2) h3
  refine hV2.trans ?_
  rw [hKsplit, ENNReal.ofReal_mul hK0]
  exact mul_le_mul' le_rfl
    (ofReal_anchorDerivSup_le_shellDerivCubeLinftyENorm S.ell S.LPrime S.n om)

/-! ## The uniform estimate behind both displays -/

/-! ## The two displays -/

/-! ## The printed display `e.RHS.term2.proxy.error` -/

end

end SuperdiffusionCLT.Section3.Terms
