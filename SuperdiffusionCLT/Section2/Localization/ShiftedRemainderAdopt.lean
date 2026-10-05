/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.ShiftedRemainder
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedRoute

/-!
# Adopting the shifted remainder through the conjunct-3 route

`ShiftedRemainder` treats the paper's object `Z − Z̃ = X − X̃`,
and the test that distinguishes it from the route's carrier: the difference of
two fields admissible at the same loading `(−p, q)` has potential slot of mean
`0`, whereas the route's `(p, q) − (Z − Zt)` has mean `p`.  This module *adopts*
that object and proves the first variation at the shifted field.

## Main results

* `conj3ShiftedPairRemainder_gap_cutoff` — the first variation at the shifted
  object, at the route's two forward maximizers:
  `⨍_U A (Z − Zt)·(Z − Zt) = ⨍_U A Zt·Zt − ⨍_U A Z·Z` and its mirror at `Ã`.
  Unconditional: the only inputs are the two maximizers and the domain.

Everything stays averaged: every left side is a `volumeAverage` over `U`, and no
statement is pointwise.  All dimension statements are `2 ≤ d`; dimension one is
out of scope, as in the statement.  Names from other namespaces are fully qualified.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Assumptions.ShellLaw
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Local algebra -/

/-- A block matrix commutes with negation of its argument. -/
private theorem blockMatVecMul_neg_adopt {d : ℕ} (A : BlockMat d) (X : BlockVec d) :
    blockMatVecMul A (-X) = -blockMatVecMul A X := by
  rcases X with ⟨x, y⟩
  ext <;> simp [blockMatVecMul, matVecMul_neg] <;> ring

/-- The block quadratic form is even in its block argument. -/
private theorem averagedBlockQuadratic_neg_adopt {d : ℕ} (A : Mat d) (X : BlockVec d) :
    averagedBlockQuadratic A (-X) = averagedBlockQuadratic A X := by
  unfold averagedBlockQuadratic
  rw [blockMatVecMul_neg_adopt]
  simp [blockVecDot, vecDot_neg_left, vecDot_neg_right]

/-- The averaged block quadratic is even in the difference: swapping the two
sides of a difference leaves the volume average unchanged.  This is what carries
the first variation at `Ã` from the minimizer order `Zt − Z` to the shifted
object `Z − Zt`. -/
private theorem averagedBlockQuadraticOn_sub_neg_adopt {d : ℕ} {U : Set (Vec d)}
    {A : Vec d → Mat d} {X Y : Vec d → BlockVec d} :
    averagedBlockQuadraticOn U A (fun x => Y x - X x) =
      averagedBlockQuadraticOn U A (fun x => X x - Y x) := by
  unfold averagedBlockQuadraticOn
  apply congrArg (volumeAverage U)
  funext x
  have hxy : Y x - X x = -(X x - Y x) := by abel
  change averagedBlockQuadratic (A x) (Y x - X x) =
    averagedBlockQuadratic (A x) (X x - Y x)
  rw [hxy, averagedBlockQuadratic_neg_adopt]

/-! ## The first variation at the shifted object -/

/-- **The level-`m` route doubled field is a doubled minimizer at `(−p, q)`.**
The forward maximizer `v` and the transpose maximizer supplied by
`transposeResponseMaximizer` put the doubled field of
`Book.Ch02.doubledFieldOfScalarMaximizers` at the infimum of the doubled `mu`
problem for the level-`m` coefficient object. -/
private theorem routeDoubledFieldM_isDoubledMuMinimizer {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v) :
    Book.Ch02.IsDoubledMuMinimizer U (levelMCoeffOn U nu hnu omega m) (-p, q)
      (routeDoubledFieldM U nu hnu omega m p q v) :=
  doubledFieldOfScalarMaximizers_isDoubledMuMinimizer (levelMCoeffOn U nu hnu omega m) p q v
    (transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)) hv
    (transposeResponseMaximizer_isMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q))

/-- **The centered-pair route doubled field is a doubled minimizer at `(−p, q)`.**
The same at the route's upper coefficient object `centeredPairCoeffOn`. -/
private theorem routeDoubledFieldL_isDoubledMuMinimizer {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    Book.Ch02.IsDoubledMuMinimizer U (centeredPairCoeffOn U nu hnu omega m L hmL) (-p, q)
      (routeDoubledFieldL U nu hnu omega m L hmL p q u) :=
  doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
    (centeredPairCoeffOn U nu hnu omega m L hmL) p q u
    (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)) hu
    (transposeResponseMaximizer_isMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
      p (-q))

/-- **The first variation at the shifted remainder.**  At the
route's two forward maximizers, the two averaged gap identities hold at
the *shifted* difference `Z − Zt`, at the two coefficient fields of the cutoff
pair:

* `⨍_U A (Z − Zt)·(Z − Zt) = ⨍_U A Zt·Zt − ⨍_U A Z·Z`;
* `⨍_U Ã (Z − Zt)·(Z − Zt) = ⨍_U Ã Z·Z − ⨍_U Ã Zt·Zt`.

These are `averagedGap_of_doubledMuMinimizer` applied at the two minimizers, with
the `Ã` identity transported across the evenness of the difference.  No residual
slot is carried: the two maximizers, the domain and `m ≤ L` are the only
inputs.  They are exactly the `hgapA`/`hgapAt` slots of
`Conj3AveragedRouteData` at the fields the route actually uses. -/
theorem conj3ShiftedPairRemainder_gap_cutoff {d : ℕ} (U : Book.Ch02.Domain d)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (hv : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega m).toCoeffField v)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (hu : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (centeredPairField nu omega m L (U : Set (Vec d))) u) :
    (averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u) =
      averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => (coefficientCutoff nu omega m).toCoeffField x)
          (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x) -
        averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => (coefficientCutoff nu omega m).toCoeffField x)
          (fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x)) ∧
    (averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
        (conj3ShiftedPairRemainder U nu hnu omega m L hmL p q v u) =
      averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
          (fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x) -
        averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => centeredPairField nu omega m L (U : Set (Vec d)) x)
          (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x)) := by
  have hZ := routeDoubledFieldM_isDoubledMuMinimizer U nu hnu omega m p q v hv
  have hZt := routeDoubledFieldL_isDoubledMuMinimizer U nu hnu omega m L hmL p q u hu
  refine ⟨?_, ?_⟩
  · have h1 := averagedGap_of_doubledMuMinimizer (levelMCoeffOn U nu hnu omega m) hZ hZt.1
    exact h1
  · have hraw := averagedGap_of_doubledMuMinimizer
      (centeredPairCoeffOn U nu hnu omega m L hmL) hZt hZ.1
    have heven := averagedBlockQuadraticOn_sub_neg_adopt (U := (U : Set (Vec d)))
      (A := fun x => (centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField x)
      (X := fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x)
      (Y := fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x)
    exact heven.symm.trans hraw

end

end SuperdiffusionCLT.Section2.Localization
