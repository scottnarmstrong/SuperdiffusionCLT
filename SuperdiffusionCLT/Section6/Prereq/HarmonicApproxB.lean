/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Section4.LNaught

/-!
# Harmonic approximation on the minimal-scale good event

Lemma `l.sharp.scale.inputs`, bullet on harmonic
approximation. The deterministic theorem `harmonic_approximation_deterministic` of
`HarmonicApprox` needs, at each cube, a bound on the homogenization error
`𝓔_{1/9,2}(cu_n; a, σ̄_m Id)` and an ellipticity bound with symmetric part `ν Id`. On the good event
of `p.minimal.scales` (the body `hMS` of `Frozen.Section4.minimal_scales`, at the exponent `1/9`) the
error bound holds for the centered cutoff field at every level `L ≥ m` and for the full centered
stream field. The symmetric part is `ν Id` by skew-symmetry, and the cutoff field is elliptic on the
cube by the entry bounds of the finite sums of shells.

The rate delivered here is the minimal-scale bookkeeping rate `δ σ̄_m^{-1} m^{expon} log m` times
`σ̄_m^{-1/2} ν^{1/2}`. The printed rate of `e.Dir.new.harmonic.approx` is obtained from this one once
the bookkeeping term is absorbed into `δ_m = ε m^{-(1-ρ)/2} log m`, which uses the lower bound
`σ̄_m ≳ m^{1/2}` of `t.sstar.sharp.bounds` and is not part of this file.

## Main results

* `symmPart_centeredStreamField_add`: the symmetric part of `ν Id` plus the centered stream field
  is `ν Id`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.HarmonicApprox

open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-- The symmetric part of the centered coefficient `ν Id + k^U` is `ν Id`. -/
theorem symmPart_centeredStreamField_add (nu : ℝ) (omega : ShellSeq d) (S : Set (Vec d))
    (y : Vec d) :
    symmPart (nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega S y) =
      nu • (1 : Mat d) := by
  ext i k
  have hskew := SuperdiffusionCLT.Section2.Carriers.centeredStreamField_skew_entry omega S y
    i k
  simp only [symmPart, Matrix.add_apply, Matrix.smul_apply]
  rw [SuperdiffusionCLT.Section2.Carriers.centeredStreamField_skew_entry omega S y k i]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply, smul_eq_mul]
    ring
  · have hki : k ≠ i := Ne.symm hik
    simp [hik, hki]

/-- Witness (satisfiability): the full-field ellipticity hypothesis of the harmonic approximation
on the good event is satisfiable (zero shell sequence, where the centered stream field vanishes). -/
example (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu) (n m : ℕ) (z : Vec d) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
      (fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) (cubeSet (originCube d (m : ℤ)))
          (z + x)) := by
  classical
  have h0 : ∀ y, SuperdiffusionCLT.Section2.Carriers.centeredStreamField
      (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) (cubeSet (originCube d (m : ℤ))) y =
        0 := by
    intro y
    exact SuperdiffusionCLT.Section2.Carriers.centeredStreamField_zero _ y
  refine ⟨nu, nu, ?_, fun x _ => ?_⟩
  · simp only [h0, add_zero]
    exact measurable_matrix_of_entries fun i j =>
      Measurable.ite (measurableSet_cubeSet _) measurable_const measurable_const
  · simp only [h0, add_zero]
    simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := nu) hnu

end

end SuperdiffusionCLT.Section6.HarmonicApprox
