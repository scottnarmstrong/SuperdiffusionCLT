/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgAssemblyB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgInputsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm4Anchors
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB

/-!
# The canonical weak Hessian for the oscillation step of `e.RHS.term3`

The oscillation step `e.RHS.term3.B` of `l.RHS.term3` is stated for a response field `w` together
with a weak-Hessian field of `w`.  The second clause of `e.nablaw.Lt` holds at every weak-Hessian
witness, so the Hessian field may be fixed once and for all.  This module makes that choice.

## Main definitions

* `oscHessianWitness`: a weak Hessian of the Dirichlet response `w omega`, chosen at every sample.
* `oscHessianField`: the same weak Hessian as the `HilbertMat`-valued field read by the clause
  `hZbound` of the oscillation assembly.

## Remarks on the printed proof

The oscillation constant `oscBoundConst Cpo C C3 S.h` depends on the window only through the factor
`(1 + h)^{1/2}`, which comes from the union-bound loss in the second clause of `e.nablaw.Lt`; no
window-free constant replaces the product.

The printed `b_{L'}^{-1/2}` insertion in the proof of `l.RHS.term3` needs `b_{L'}(z + cu_n)` to be
invertible on the cutoff cube; the paper does not remark on this.  The carrier
`translatedBlockHalfWeight` uses only the forward square root `CFC.sqrt`.  The material available
supplies positive semidefiniteness (`posSemidef_translatedCoarseBlock`) but no positive lower bound
on the cutoff cube, so no inverse-square-root carrier is available.  The forward half of the
insertion does not need it, and is what `holderPair_translatedBlockHalfWeightDiff` uses.
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
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## The weak Hessian of the response -/

/-- **The canonical weak-Hessian witness of the response.**  One exists at every
sample (`exists_hasWeakHessianOn_of_isDirichletResponse`), and the second clause of `e.nablaw.Lt`
holds at *every* witness, so the clause may be discharged at this fixed choice. -/
noncomputable def oscHessianWitness {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {S : ScaleSelection} (hSorder : ScalesOrdering S) {p : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
    (omega : ShellSeq d) :
    HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function :=
  Classical.choice (exists_hasWeakHessianOn_of_isDirichletResponse hd omega
    (le_of_lt (lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime))
    p (w omega) (hw omega))

/-- **The canonical weak Hessian of the response**, as the `HilbertMat`-valued
field the clause `hZbound` of the oscillation assembly reads. -/
noncomputable def oscHessianField {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {S : ScaleSelection} (hSorder : ScalesOrdering S) {p : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
    (omega : ShellSeq d) : Vec d → HilbertMat d :=
  fun x => HilbertMat.ofMat (fun i j =>
    (oscHessianWitness hd hSorder w hw omega).hess i j x)

end

end SuperdiffusionCLT.Section3.Terms
