/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedClose
public import Homogenization.Book.Ch02.Theorems.DeterministicIdentities

/-!
# The printed slope bound, rebuilt at the minimizers

The route's slope bound on the mean squared
slope is `5 η ν⁻¹ (Q_A + Q_{A'})`, where
`Q_A = averagedBlockQuadraticOn U A (fun _ => (-p,q))` is the *volume average of
the pointwise constant-loading quadratic*.  Turning that bound into the response
functional `R` there consumes the `hscale` equality

`Q_A + Q_{A'} = 2 (R_{A'} + R_A + 2 p·q)`,

obtained from two response bridges `⨍_U pointwiseResponse = ResponseJ`.  That
equality is the equality half of `e.CG.bounds.2`, which the manuscript never
takes — it only ever takes the inequality, and in the direction
`ResponseJ ≤ ⨍_U pointwiseResponse`.

The printed comparison is proved differently.  It never forms
`⨍_U pointwiseResponse` at the constant loading.  It uses the *minimizer's own
averaged block energy* (`e.minimizers.energy.vs.bfA`): the energy
of a doubled-`μ` minimizer `Z` at `P = (-p,q)` is `‖A^{1/2}Z‖²`, which is the
coarse energy `P·A(U)P`; and that is converted to `2J + 2p·q` by
`e.Jaas.matform`.  Neither step uses any direction of
`e.CG.bounds.2`, and in particular the printed argument never needs
`⍍_U pointwiseResponse ≤ ResponseJ`.

This module lands that substitute.  The headline is
`doubledMinimizerEnergy_eq_responseJ`: at any doubled-`μ` minimizer `X` of the
field `a` at the loading `(-p,q)`,

`doubledFieldQuadraticOn a X = 2 * ResponseJ (U : Set (Vec d)) p q a.toCoeffField + 2 * vecDot p q`.

Its only hypothesis is the minimality of `X`, and minimizers exist
unconditionally (`Book.Ch02.doubledMuTheory`), so the identity carries no
hypotheses beyond the carriers.
Everything stays averaged: every quantity below is a normalized volume average
over `U`.

The *printed half* `2 R + 2 p·q ≤ ⨍_U (·)` is a consequence of the minimizer
identity, not an alternative to it.  The bridge is the reverse of that inequality
promoted to an equality at the constant loading, i.e. the assertion that the
constant loading is itself a minimizer.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## `e.Jaas.matform` in the `Mu` and coarse-matrix forms -/

/-- `e.Jaas.matform` with the loading `(-p,q)`: the coarse
energy at `(-p,q)` is the response functional plus the cross term.  This is
`ResponseJ_eq_Mu_neg_left_sub_vecDot` rearranged; it carries no hypotheses
beyond the carriers. -/
theorem mu_negLoading_eq_responseJ_add_vecDot {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Mu (U : Set (Vec d)) (-p, q) a.toCoeffField =
      ResponseJ (U : Set (Vec d)) p q a.toCoeffField + vecDot p q := by
  have h := Book.Ch02.ResponseJ_eq_Mu_neg_left_sub_vecDot U a p q
  linarith only [h]

/-- `e.Jaas.matform` read through the coarse block matrix
`A(U)`: `P·A(U)P = 2 J + 2 p·q` at `P = (-p,q)`.  No hypotheses beyond the
carriers. -/
theorem coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    blockVecDot (-p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q)) =
      2 * ResponseJ (U : Set (Vec d)) p q a.toCoeffField + 2 * vecDot p q := by
  have hmu := mu_negLoading_eq_responseJ_add_vecDot U a p q
  have hmq := (Book.Ch02.doubledMuTheory U a).mu_quadratic (-p, q)
  have hdm : Book.Ch02.doubledMu U a (-p, q) = Mu (U : Set (Vec d)) (-p, q) a.toCoeffField :=
    Book.Ch02.doubledMu_eq_Mu U a (-p, q)
  rw [hdm, hmu] at hmq
  linarith only [hmq]

/-! ## The printed substitute: the minimizer's averaged energy -/

/-- **The printed substitute for the response bridges.**  At any doubled-`μ`
minimizer `X` of `a` at the loading `(-p,q)`, the averaged block energy equals
`2 * ResponseJ + 2 * p·q`.  This is what the printed chain consumes in place of
`⨍_U pointwiseResponse = ResponseJ`; it needs no direction of `e.CG.bounds.2`.
The only hypothesis is the minimality of `X`, which `Book.Ch02.doubledMuTheory`
discharges. -/
theorem doubledMinimizerEnergy_eq_responseJ {d : ℕ} {U : Book.Ch02.Domain d}
    {a : Book.Ch02.CoeffOn U} {p q : Vec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U a (-p, q) X) :
    doubledFieldQuadraticOn a X =
      2 * ResponseJ (U : Set (Vec d)) p q a.toCoeffField + 2 * vecDot p q := by
  have h1 : Book.Ch02.doubledMuValue U a X =
      (1 / 2 : ℝ) * doubledFieldQuadraticOn a X :=
    doubledMuValue_eq_half_doubledFieldQuadraticOn a X
  have h2 : Book.Ch02.doubledMuValue U a X = Book.Ch02.doubledMu U a (-p, q) :=
    Book.Ch02.IsDoubledMuMinimizer.doubledMuValue_eq_doubledMu hX
  have h3 : Book.Ch02.doubledMu U a (-p, q) =
      Mu (U : Set (Vec d)) (-p, q) a.toCoeffField :=
    Book.Ch02.doubledMu_eq_Mu U a (-p, q)
  have h4 : Mu (U : Set (Vec d)) (-p, q) a.toCoeffField =
      ResponseJ (U : Set (Vec d)) p q a.toCoeffField + vecDot p q :=
    mu_negLoading_eq_responseJ_add_vecDot U a p q
  calc doubledFieldQuadraticOn a X = 2 * Book.Ch02.doubledMuValue U a X := by rw [h1]; ring
    _ = 2 * Book.Ch02.doubledMu U a (-p, q) := by rw [h2]
    _ = 2 * Mu (U : Set (Vec d)) (-p, q) a.toCoeffField := by rw [h3]
    _ = 2 * (ResponseJ (U : Set (Vec d)) p q a.toCoeffField + vecDot p q) := by rw [h4]
    _ = 2 * ResponseJ (U : Set (Vec d)) p q a.toCoeffField + 2 * vecDot p q := by ring

/-- The same identity in the vocabulary `averagedBlockQuadraticOn` that the
route's `hscale` step is written in.  It is `doubledFieldQuadraticOn` unfolded,
so it is definitional. -/
theorem averagedBlockQuadraticOn_minimizer_eq_responseJ {d : ℕ} {U : Book.Ch02.Domain d}
    {a : Book.Ch02.CoeffOn U} {p q : Vec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U a (-p, q) X) :
    averagedBlockQuadraticOn (U : Set (Vec d)) (fun x => a.toCoeffField x)
        (fun x => X.eval x) =
      2 * ResponseJ (U : Set (Vec d)) p q a.toCoeffField + 2 * vecDot p q :=
  doubledMinimizerEnergy_eq_responseJ hX

/-! ## The route's `hscale` step, at the two carriers -/

/-- The `hscale` equality the route's slope bound consumes,
but fed by the minimizer energies instead
of by the two response bridges. -/
theorem hscale_of_minimizerEnergy {d : ℕ} {U : Set (Vec d)} {A At : Vec d → Mat d}
    {p q : Vec d} {ZA ZAt : Vec d → BlockVec d}
    (hminA : averagedBlockQuadraticOn U A ZA =
      2 * ResponseJ U p q A + 2 * vecDot p q)
    (hminAt : averagedBlockQuadraticOn U At ZAt =
      2 * ResponseJ U p q At + 2 * vecDot p q) :
    averagedBlockQuadraticOn U A ZA + averagedBlockQuadraticOn U At ZAt =
      2 * (ResponseJ U p q At + ResponseJ U p q A + 2 * vecDot p q) := by
  rw [hminA, hminAt]
  ring

end

end SuperdiffusionCLT.Section2.Localization
