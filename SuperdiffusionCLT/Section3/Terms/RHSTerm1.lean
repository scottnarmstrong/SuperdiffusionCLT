/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Steps
public import SuperdiffusionCLT.Section3.Terms.GluedField

/-!
# `l.RHS.term1`

The estimate `e.RHS.term1` of the paper:

`|E[ ⨍_{cu_m} ∇w · (a_ℓ ∇u_n − q) ]| ≤ C ν^{-3} ℓ² h (3^{-(ℓ-n)/2} + 3^{-(ℓ'-ℓ)})`.

Step 3 of the printed proof combines the two step displays of
`RHSTerm1Steps.lean` with the per-sample decomposition `e.decompose.flux.u.n`
of the same file, and then coarsens the two rates with the pigeonhole scale
comparabilities `m ≤ Cℓ` and `m − ℓ ≤ 2h` of the proof.  Those two rest on
`2h ≤ m`, which `ScalesOrdering` does not imply and which is therefore the explicit
hypothesis `hPigeon`.

This file proves the `L²` membership of the glued gradient field and of its image under the
cutoff coefficient, used by the estimates of `l.RHS.term1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L²` transport across a Chapter 2 coefficient object -/

/-- The flux of an `L²` field against a Chapter 2 coefficient object is `L²`.
The public coefficient object is only a.e. elliptic, so the proof passes to the
pointwise-good representative and transports back across the a.e. equality of
representatives, as `Book.Ch02.Solution.flux_memVectorL2` does for a solution
gradient. -/
theorem memVectorL2_matVecMul_coeffOn {U : Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn U) {f : Vec d → Vec d}
    (hf : MemVectorL2 (U : Set (Vec d)) f) :
    MemVectorL2 (U : Set (Vec d)) (fun x => matVecMul (a.toCoeffField x) (f x)) := by
  let b : Book.Ch02.CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hb : Book.Ch02.CoeffOn.AEEq b a := by
    simpa [b] using Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hbase : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (b.toCoeffField x) (f x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf
  refine MeasureTheory.MemLp.ae_eq ?_ hbase
  exact hb.mono fun x hx => by simp [hx]

/-- The cutoff flux `a_L f` of an `L²` field on a triadic cube is `L²`. -/
theorem memVectorL2_matVecMul_coefficientCutoff {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MemVectorL2 (openCubeSet Q) f) :
    MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x) (f x)) :=
  memVectorL2_matVecMul_coeffOn
    (cutoffDomainCoeffOn (Book.Ch02.cubeDomain Q) hnu omega L) hf

/-- The glued gradient field of `e.u.k.def` is `L²` on every triadic cube. -/
theorem memVectorL2_gluedGradientField {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ)
    (F : Vec d) (omega : ShellSeq d) (Q : TriadicCube d) :
    MemVectorL2 (openCubeSet Q) (gluedGradientField hnu L k m F omega) :=
  (memLp_two_gluedGradientField hnu L k m F omega).restrict (openCubeSet Q)

/-! ## From a Bochner integral to the truncated `∫⁻` functional -/

/-! ## The closing coarsening of Step 3 -/

/-! ## `l.RHS.term1` -/

end

end SuperdiffusionCLT.Section3.Terms
