/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyOrderOneB
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne

/-!
# `l.LHS.term1` with the a priori statement supplied

The statement and proof of `l.LHS.term1`.

`l_LHS_term1_of_anchors` of `WholeSpaceEnergyOrderOneB.lean` carries the conclusion
of `l.abstract.response.fields.apriori` as an explicit hypothesis `hApriori`.
This is not a mathematical residue but a module-graph one: two modules
of `Section3/ResponseFields/` once declared the same name, so no file could import
the LHS-term chain and the a priori statement at the same time.  The duplicate is
gone, and the version-3 statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne` is now
importable alongside `WholeSpaceEnergyOrderOneB.lean`.

`l_LHS_term1_of_apriori` is therefore `l_LHS_term1_of_anchors` with `hApriori`
discharged by that one term: the hypothesis is the conclusion of the a priori
statement verbatim, at the order-one hatted carrier `Section2.Norms.vecHatNegENormOrderOne`
(the hatted vector norms are of order one), so the application is by
name and nothing is re-proved here.

The conclusion is the one of `l_LHS_term1_of_anchors`, unchanged, and it is
already in the paper's own quantifier order: the constant `Clhs` comes
first, then the scale `nu`, the shell law `P`, the scale selection `S`, the
direction `e` and every remaining datum.  No restatement is needed.

## What still stands as a hypothesis

* `ZhmGe` (four clauses): `e.jk.Hminus.endpoint` in its `r > m` form,
  `‖j_r p − (j_r p)_{cu_m}‖_{Ĥ̲^{-1}(cu_m)} ≤
  O_{Γ₂}(C|p|3^{−(r−m)})`, which the paper obtains from Poincaré's inequality
  and `a.j.reg`.  `ShellHminusEndpointOrderOneB.lean`
  proves the endpoint only for `r ≤ m`, so the `r > m` half is taken as a hypothesis.
* `Zl4` (four clauses): the `L̲⁴` bound of the paper, likewise taken as a hypothesis.
* the shell-law binders `hPrefix`, `_hJ1`, `hJ2`, `hJ3`, `_hJ4` and the
  translation invariance `_hInv`, which are the standing assumptions themselves.
* the response fields of the scale selection — `F`, `gradHatW`, `wD`, `wN`,
  `wDr`, `wNr` with their defining relations, and `hproj`, `hlow`, `hup`,
  `hJ5app` — which are the data `l.abstract.response.fields` and
  `e.ellsep.testing` provide, not estimates.

## Main results

* `l_LHS_term1_of_apriori`: `l.LHS.term1` from the a priori statement.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- **Lemma `l.LHS.term1` with the a priori anchor discharged**.

This is `l_LHS_term1_of_anchors` of `WholeSpaceEnergyOrderOneB.lean` with its
hypothesis `hApriori` supplied by the version-3 statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne`; the
hypothesis is that theorem's conclusion verbatim, so the proof is one
application.  Every other binder, and the conclusion, are unchanged.

The constant comes first: one `Clhs` depending on `d`, on the a priori statement
and on the two remaining input constants `Cl4` and `ChmGe` alone, and then
every admissible scale, shell law, scale selection, direction and response
field.

Discharged below this surface, with no residue: `e.abstract.response.ND.weak`
(the a priori statement), `e.jk.Hminus.endpoint` on the shells `r ≤ m`, and
`e.jk.spatialavg` in both applied shapes.  What remains is listed in the module
docstring: the `r > m` endpoint `ZhmGe`, the `L̲⁴` bound `Zl4`, the
shell laws, and the response-field data of the scale selection. -/
theorem l_LHS_term1_of_apriori
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Cl4 ChmGe : ℝ) (hCl4 : 0 < Cl4) (hChmGe : 0 < ChmGe) :
    ∃ Clhs : ℝ, 1 ≤ Clhs ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (_hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
        (_hJ4 : ShellLawJ4 d P)
        (_hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure)
        (cStar K : ℝ) (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d) (_he : vecNormSq e = 1) (hunit : Book.Ch02.vecNorm e = 1)
        (p : Vec d), p = testVector nu S.LPrime P S.n e →
      ∀ F : ShellSeq d → Vec d → Vec d,
        (∀ omega : ShellSeq d, F omega = fun x =>
          matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p) →
      ∀ (gradHatW : ShellSeq d → Vec d)
        (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (wN : ShellSeq d →
          H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d, IsCubeDirichletResponse (originCube d (S.m : ℤ))
          (F omega) (wD omega)) →
        (∀ omega : ShellSeq d, IsCubeNeumannResponse (originCube d (S.m : ℤ))
          (F omega) (wN omega)) →
        AEStronglyMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (wD omega).toH1Function.grad) P.toMeasure →
      ∀ (hFmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
        (hGmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
        (hGmemLp.toLp fun omega : ShellSeq d =>
              HilbertVec.ofVec (gradHatW omega)) =
            -stationaryPotentialProjection (μ := P.toMeasure)
              (hFmemLp.toLp fun omega : ShellSeq d =>
                HilbertVec.ofVec (F omega 0)) →
        (∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
            ∫⁻ omega : ShellSeq d,
              ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) →
        (∫⁻ omega : ShellSeq d,
              ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
            ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure) →
        |‖blockPotentialResponse P S.ellPrime S.LPrime
              (blockRegLaw_stationary hPrefix hJ2 S.ellPrime S.LPrime) e
              (memLp_originForcing_blockRegLaw hJ3 S.ellPrime S.LPrime e
                hunit)‖ ^ 2 -
            cStar * Real.log 3 * ((S.LPrime - S.ellPrime : ℕ) : ℝ)| ≤ K →
      ∀ (wDr : ℕ → ShellSeq d →
            H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (wNr : ℕ → ShellSeq d →
            H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
          IsCubeDirichletResponse (originCube d (S.m : ℤ))
            (shellFlux omega r p) (wDr r omega)) →
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
          IsCubeNeumannResponse (originCube d (S.m : ℤ))
            (shellFlux omega r p) (wNr r omega)) →
      ∀ Zl4 : ℕ → ShellSeq d → ℝ, (∀ r omega, 0 ≤ Zl4 r omega) →
        (∀ r, Measurable (Zl4 r)) →
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
          IsBigO P.toMeasure (gammaSigma 2) (Zl4 r)
            (Cl4 * Book.Ch02.vecNorm p)) →
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 4
            (fun x => shellFlux omega r p x -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (shellFlux omega r p)) ≤ ENNReal.ofReal (Zl4 r omega)) →
      ∀ ZhmGe : ℕ → ShellSeq d → ℝ, (∀ r omega, 0 ≤ ZhmGe r omega) →
        (∀ r, Measurable (ZhmGe r)) →
        (∀ r ∈ Finset.Ioc S.m S.LPrime,
          IsBigO P.toMeasure (gammaSigma 2) (ZhmGe r)
            (ChmGe * Book.Ch02.vecNorm p *
              (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ)))) →
        (∀ r ∈ Finset.Ioc S.m S.LPrime, ∀ omega : ShellSeq d,
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => shellFlux omega r p x -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (shellFlux omega r p)) ≤ ENNReal.ofReal (ZhmGe r omega)) →
        |(∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                ℝ≥0∞).toReal -
            cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
          (Clhs * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p
    :=
  l_LHS_term1_of_anchors d hd
    (_root_.SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd)
    Cl4 ChmGe hCl4 hChmGe

end

end SuperdiffusionCLT.Section3.Setup
