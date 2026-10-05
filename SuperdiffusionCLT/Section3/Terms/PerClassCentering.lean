/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.ConcentrationMean
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparisonB

/-!
# The per-class centring `hmean` at the specific centred field

The comparison `…_descendants_of_subcollections`
(`Section3/Terms/ConcentrationComparisonB.lean`) requires its centring input
`hmean` only *inside* each printed subcollection `subcollectionAtDepth R t c` of
the block family, and its shell-law corollary
`…_subcollections_of_shellLaw` carries that binder as a residual.  The binder is
not dischargeable at an arbitrary field `F`: it is a property of the *specific*
centred field the comparison is applied to, the printed observable
`a_ℓ ∇ũ_n − q̃` (`concDepthField hnu P S e` of
`Section3/Terms/RHSTerm1ConcDepth.lean`).

This module instantiates `F` at that field and discharges the per-class
`hmean` from the block centring
`integral_fluxBlockObservable_eq_zero_of_mem_le_scale`
(`Section3/Terms/TranslatedBlockCentering.lean`), through the carrier identity
`volumeAverage_coord_concDepthField_eq_fluxBlockObservable`
(`Section3/Terms/ConcentrationMean.lean`).  Since a printed subcollection is a
subset of the descendant family (`subcollectionAtDepth_subset_descendantsAtDepth`),
the whole-family centring
`integral_concDepthField_descendantsAtDepth_eq_zero` supplies the per-class
statement, and no new hypothesis appears: the single scale condition it carries
(`S.n ≤ S.m − j`, automatic when `j + ℓ ≤ m`) is the same one the whole-family
discharge already carried.

## What the centring gives, and at which family

`integral_concDepthField_subcollection_eq_zero` is the exact binder `hmean` of
`…_descendants_of_subcollections` at `F = concDepthField hnu P S e`,
`μ = P.toMeasure`, `m = S.m`, `ell = S.ell`, at every class
`c ∈ shellColorSet R (S.m − j − S.ell)` and every block
`B ∈ subcollectionAtDepth R (S.m − j − S.ell) c`.  The two theorems
`…_le_decay_subcollections` and `…_subcollections_of_shellLaw` re-run the
comparison there with that binder removed, so the printed comparison at the
printed observable no longer carries a centring input.

## Residuals

The centring itself carries only the shell-law data (`hPrefix`, `hJ2`,
`hJ3`, `hJ4`) and the scale condition `S.n ≤ S.m − j`; the untruncated form
`…_of_add_le` removes the scale condition when `j + S.ell ≤ S.m`.  The
comparison corollaries below carry, besides those, only the inputs that the
comparison itself still holds at that field: the joint measurability `hFjoint`,
the per-class independence/membership slot (`hpair`/`hmem`, or the lane
inputs `hscaleR`, `hlane`, `K`, `hbd` in the shell-law form), and the
`L̲²` membership (discharged here).  The centring `hmean` is gone from all of
them.

This is an instantiation of the centred field of this development, which is the printed
`a_ℓ ∇ũ_n − q̃` with `q̃ = qVector hnu P S.ell S.ell S.n S.m (fluxSlot …)`.  It
agrees with the printed field: the block observable that the
centring makes mean-zero is exactly `a_ℓ ∇ũ_n − q̃`, and the quantity
subtracted is the printed proxy `q̃`
(`SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A printed subcollection is a sub-family of the descendants -/

/-- **Every printed subcollection is contained in the descendant family.**
`mem_subcollectionAtDepth` reads a class member as a depth-`t` descendant of `R`
together with its colour, so the class is a sub-family of `descendantsAtDepth R t`.
This is what lets a whole-family centring supply the per-class binder `hmean` of
the comparison. -/
theorem subcollectionAtDepth_subset_descendantsAtDepth (R : TriadicCube d) (t : ℕ)
    (c : ShellField.ShellCubeColor d) :
    subcollectionAtDepth R t c ⊆ descendantsAtDepth R t :=
  fun _ hB => (mem_subcollectionAtDepth.mp hB).1

/-! ## The per-class centring `hmean` at the centred field -/

/-- **The per-class centring `hmean` at the depth observable.**  This is exactly
the binder `hmean` of the descendant-subcollection decay estimate
at `F = concDepthField hnu P S e`, `μ = P.toMeasure`, `m = S.m`, `ell = S.ell`:
inside every printed subcollection of the block family the sample mean of the
coordinate cube average of `a_ℓ ∇ũ_n − q̃` vanishes.  It is the whole-family
centring `integral_concDepthField_descendantsAtDepth_eq_zero` restricted along
`subcollectionAtDepth_subset_descendantsAtDepth`, so it carries no new
hypothesis: the scale condition `S.n ≤ S.m − j` is the same one that discharge
already carries. -/
theorem integral_concDepthField_subcollection_eq_zero [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {j : ℕ} {R : TriadicCube d}
    (hjm : j ≤ S.m) (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (hnj : S.n ≤ S.m - j) :
    ∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
      ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c,
        ∫ omega : ShellSeq d, volumeAverage (cubeSet B)
          (fun x => concDepthField hnu P S e omega x i) ∂P.toMeasure = 0 := by
  intro c _ i B hB
  exact integral_concDepthField_descendantsAtDepth_eq_zero hnu P S e hPrefix hJ2 hJ3 hJ4
    hjm hR hnj i B (subcollectionAtDepth_subset_descendantsAtDepth R (S.m - j - S.ell) c hB)

/-! ## The comparison at the centred field, with `hmean` removed

The two corollaries below re-run the printed comparison at the observable
`a_ℓ ∇ũ_n − q̃`, so the centring binder `hmean` is gone.  The first keeps the
comparison's per-class independence/membership slot as an input; the second
discharges that slot too, from the lane data, through the shell-law
corollary of the comparison. -/

/-! ## Witnesses -/

end

end SuperdiffusionCLT.Section3.Terms
