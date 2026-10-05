/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLpLargeCube

/-!
# mixTail: samplewise integrability of `matrixOperatorNorm ∘ finiteShellIncrement`
on an arbitrary triadic cube

The stream estimate
`integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement` (from `Section2`) proves this
integrability only on the *open origin* cube `openCubeSet (originCube d l)`.
This module transports it to `cubeSet R` for an **arbitrary** `TriadicCube d`
`R` at a natural-number scale, samplewise (no probability measure is used):
`R = triadicCubeShift R + cu_{R.scale}` (`cubeSet_eq_translateSet_originCube_of_triadicCube`),
the shell increment is translation-covariant
(`translateReg_finiteShellIncrement`, in
`Section3/Terms/TranslatedBlocks.lean`), Lebesgue measure is translation
invariant (`measurePreserving_addRight_restrict_translateSet`, in
`Geometry/Translation.lean`), and `cubeSet`/`openCubeSet` agree a.e.
(`cubeSet_ae_eq_openCubeSet`).

## Main result

* `mixTail_integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement_cubeSet`:
  `IntegrableOn (fun x => matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
    (cubeSet R) volume`, for every `omega`, `n m : ℕ`, `p ≥ 0`, and every
  triadic cube `R` at a natural-number scale `l` (`R.scale = (l : ℤ)`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-- **Samplewise translation covariance of `matrixOperatorNorm ∘ finiteShellIncrement`.**
This is the stationarity of the finite stream
increment (as in the paper), at the level of the deterministic size function. -/
theorem mixTail_matrixOperatorNorm_finiteShellIncrement_add (z : Vec d) (omega : ShellSeq d)
    (n m : ℕ) (y : Vec d) :
    matrixOperatorNorm (finiteShellIncrement omega n m (y + z)) =
      matrixOperatorNorm
        (finiteShellIncrement (ShellField.translateSequence z omega) n m y) := by
  have h := congrArg (fun a : RegCoeffField d => a y)
    (SuperdiffusionCLT.Section3.Terms.translateReg_finiteShellIncrement z omega n m)
  simp only [translateReg_apply] at h
  rw [h]

/-- **The transport of integrability to an arbitrary triadic cube, at a
natural-number scale.** -/
theorem mixTail_integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement_cubeSet
    (omega : ShellSeq d) (n m : ℕ) {p : ℝ} (hp : (0 : ℝ) ≤ p) (R : Homogenization.TriadicCube d)
    (l : ℕ) (hl : R.scale = (l : ℤ)) :
    IntegrableOn
      (fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
      (cubeSet R) volume := by
  set z : Vec d := triadicCubeShift R with hzdef
  set omega' : ShellSeq d := ShellField.translateSequence z omega with homega'
  have hOpenOrigin :
      IntegrableOn
        (fun y : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega' n m y) ^ p)
        (openCubeSet (originCube d (l : ℤ))) volume :=
    integrableOn_matrixOperatorNorm_rpow_finiteShellIncrement omega' n m l hp
  have hCubeOrigin :
      IntegrableOn
        (fun y : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega' n m y) ^ p)
        (cubeSet (originCube d (l : ℤ))) volume :=
    hOpenOrigin.congr_set_ae (cubeSet_ae_eq_openCubeSet (originCube d (l : ℤ)))
  have hCubeScale :
      IntegrableOn
        (fun y : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega' n m y) ^ p)
        (cubeSet (originCube d R.scale)) volume := by
    rw [hl]; exact hCubeOrigin
  have hcomp :
      IntegrableOn
        ((fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) ∘
          (fun y : Vec d ↦ y + z))
        (cubeSet (originCube d R.scale)) volume := by
    have hfun :
        ((fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) ∘
            (fun y : Vec d ↦ y + z)) =
          fun y : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega' n m y) ^ p := by
      funext y
      show matrixOperatorNorm (finiteShellIncrement omega n m (y + z)) ^ p = _
      rw [mixTail_matrixOperatorNorm_finiteShellIncrement_add z omega n m y]
    rw [hfun]
    exact hCubeScale
  have hMP := measurePreserving_addRight_restrict_translateSet (d := d) z
    (cubeSet (originCube d R.scale))
  have hTransport :
      IntegrableOn
        ((fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) ∘
          (fun y : Vec d ↦ y + z))
        (cubeSet (originCube d R.scale)) volume ↔
        IntegrableOn
          (fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
          (translateSet z (cubeSet (originCube d R.scale))) volume :=
    hMP.integrable_comp_emb (Homeomorph.addRight z).measurableEmbedding
  rw [← cubeSet_eq_translateSet_originCube_of_triadicCube R] at hTransport
  exact hTransport.mp hcomp

end

end SuperdiffusionCLT.Section4.Mixing
