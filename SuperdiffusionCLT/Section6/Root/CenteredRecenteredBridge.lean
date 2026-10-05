/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.FullFieldB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockH

/-!
# The centered field is the recentered field plus a constant skew matrix

`ν Id + (k - (k)_{□_m})` (the carrier `centeredStreamField`, centred on the closed cube
`□_m`) and `fullCoefficientRecentered ν ω = ν Id + (k - k(0))` differ by the constant
matrix `centeredStreamField ω □_m 0`, which is anti-symmetric. This holds at every point of
`ℝ^d` (a fortiori on every bounded set) as soon as the derivative series is summable on
every natural open cube, which holds almost surely under `ShellLawJ3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers

variable {d : ℕ}

/-- Pointwise bridge for a sequence satisfying the derivative-summability guard. -/
theorem centered_eq_recentered_add_skew (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (nu : ℝ) (m : ℕ) :
    ∃ K : Mat d, matTranspose K = -K ∧ ∀ x : Vec d,
      nu • (1 : Mat d) +
          centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x =
        fullCoefficientRecentered nu omega x + K := by
  refine ⟨centeredStreamField omega (cubeSet (originCube d (m : ℤ))) 0,
    centeredStreamField_skew omega _ 0, fun x => ?_⟩
  have h := Section2.Estimates.Stream.centeredStreamField_sub_eq_tsum omega hguard m x 0
  have h2 : fullStreamRecentered omega x =
      centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) 0 := by
    rw [h]
    rfl
  simp only [fullCoefficientRecentered, h2]
  abel

/-- Almost-sure bridge: for every `m`, simultaneously and at every point. -/
theorem ae_centered_eq_recentered_add_skew {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ m : ℕ, ∃ K : Mat d,
      matTranspose K = -K ∧ ∀ x : Vec d,
        nu • (1 : Mat d) +
            centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x =
          fullCoefficientRecentered nu omega x + K := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω m
  exact centered_eq_recentered_add_skew omega hω nu m

/-- Witness: the Dirac zero law meets `J3`, so the almost-sure bridge is non-vacuous. -/
example (nu : ℝ) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ m : ℕ, ∃ K : Mat d, matTranspose K = -K ∧ ∀ x : Vec d,
        nu • (1 : Mat d) +
            centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x =
          fullCoefficientRecentered nu omega x + K :=
  ae_centered_eq_recentered_add_skew
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw nu

end SuperdiffusionCLT.Section6
