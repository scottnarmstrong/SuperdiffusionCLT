/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3Assembly
public import SuperdiffusionCLT.Section2.Localization.AdjointCorrespondence
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedData

/-!
# The pure-skew remainder representation of the cutoff pair

The small branch of the third localization conjunct consumes a remainder field
whose skew part is pure: the pointwise `η²` estimate is stated for a matrix field `H`
with `matTranspose H = -H`, related to the base field by `At = A + H`, and bounded
through the relative skew inequality.

This module shows that the purity is a **consequence of the construction**, not
an extra hypothesis.  The remainder field of the cutoff pair is the difference

`â - a_m = centeredPairField nu omega m L U - (coefficientCutoff nu omega m).toCoeffField`

of two coefficient fields whose symmetric parts are both exactly `ν Id`
(`symmPart_centeredPairField_eq_smul_one`, `symmPart_coefficientCutoff`).  Two
matrices with the same symmetric part have an anti-symmetric difference, so the
remainder is a pure skew shift.  The two symmetric-part inputs are proved
one at a time from the API.

The pointwise packaging of the `η²` bridge at the cutoff pair is deliberately not
restated here.  Its universal-in-`r` energy hypothesis is unsatisfiable: at the
cutoff pair `symmPart` is positive definite, so the shift energy is unbounded in
`r`, while the loading form does not mention `r`; a statement carrying that
hypothesis is therefore vacuous.  The faithful coupled packaging, whose single
witness `r` serves both the remainder identity and the energy domination, is not
needed downstream and is not stated in this development.

## Main results

* `matTranspose_sub_of_symmPart_eq_one`: the base algebra.
* `remainder_centeredPairField_skew`: the cutoff pair, both inputs discharged.
* `cutoffPairThetaWindow_le_etaWindow`: the amplitude comparison.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The pure-skew remainder representation -/

/-- **A difference of two matrices with the same symmetric part `ν Id` is
anti-symmetric.**  This is the algebra behind the purity of the remainder. -/
theorem matTranspose_sub_of_symmPart_eq_one {nu : ℝ} {X Y : Mat d}
    (hx : symmPart X = nu • (1 : Mat d)) (hy : symmPart Y = nu • (1 : Mat d)) :
    matTranspose (X - Y) = -(X - Y) := by
  ext i k
  have hxi := congrFun (congrFun hx i) k
  have hxk := congrFun (congrFun hx k) i
  have hyi := congrFun (congrFun hy i) k
  have hyk := congrFun (congrFun hy k) i
  simp only [symmPart, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] at hxi hxk hyi hyk
  show X k i - Y k i = -(X i k - Y i k)
  linarith only [hxi, hxk, hyi, hyk]

/-! ## The cutoff pair

The two coefficient fields of the strict-scale conjunct are the level-`m` cutoff
field and the two-cutoff-centered field.  Both have symmetric part `ν Id`, so
the construction-level hypotheses of the general representation are proved
from the API. -/

/-- **The cutoff remainder field is pure skew.**  The difference
`centeredPairField - coefficientCutoff` is pointwise anti-symmetric.  Both
symmetric-part inputs are discharged: `symmPart_centeredPairField_eq_smul_one`
and `symmPart_coefficientCutoff`. -/
theorem remainder_centeredPairField_skew (nu : ℝ) (omega : ShellSeq d) (m L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    matTranspose (centeredPairField nu omega m L U x -
        (coefficientCutoff nu omega m).toCoeffField x) =
      -(centeredPairField nu omega m L U x -
        (coefficientCutoff nu omega m).toCoeffField x) :=
  matTranspose_sub_of_symmPart_eq_one
    (symmPart_centeredPairField_eq_smul_one nu omega m L U x)
    (symmPart_coefficientCutoff nu omega m x)

/-! ## The amplitude comparison

The small-branch amplitude is the sandwich amplitude `η = θ (1 + θ)`, so it
dominates the relative skew rate `θ`. -/

/-- The window amplitude dominates the relative skew rate: `θ ≤ θ (1 + θ)`
because `θ ≥ 0`. -/
theorem cutoffPairThetaWindow_le_etaWindow (nu : ℝ) (hnu : 0 < nu) (n m L : ℕ)
    (omega : ShellSeq d) :
    cutoffPairThetaWindow d nu n m L omega ≤
      cutoffPairEtaWindow d nu n m L omega := by
  have hθ0 := cutoffPairThetaWindow_nonneg nu hnu n m L omega
  rw [cutoffPairEtaWindow]
  have hsq : 0 ≤ cutoffPairThetaWindow d nu n m L omega ^ 2 := sq_nonneg _
  nlinarith only [hθ0, hsq]

end

end SuperdiffusionCLT.Section2.Localization
