/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.LHSTerm1Final
public import SuperdiffusionCLT.Section3.Terms.LHSSandwichInputs

/-!
# The statement of `l.LHS.term1` from a concrete realization hypothesis

`SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst` is the statement
of `l.LHS.term1`.  This module does not import it.  Instead its conclusion is
restated here character for character as the goal of `lhs_term1_statement_of_cocycle`, with a
single named hypothesis `hRealization` whose tail — from `gradHatW` to the two
conjuncts of the realization — is binder for binder the hypothesis
`hStationaryAnchor` of `LHSTerm1Final.lhs_term1_of_stationaryAnchor`.

## The carrier

`hRealization` is stated at the concrete carrier, not the abstract one: the
probability law is `P.toMeasure` on `ShellSeq d`, the cube is
`openCubeSet (originCube d (S.m : ℤ))`, and the invariant-measure argument of
`stationaryPotentialProjection` is the explicit
`ShellField.vaddInvariantMeasure hPrefix hJ2`, exactly as in the
`hStationaryAnchor` binder.  The carrier is `ShellSeq d` because that is where
the action's joint measurability is an instance
(`StationaryRealizationConcrete.instMeasurableVAdd₂ShellSeq`), which the
abstract statement's `MeasurableConstVAdd` does not supply.

## What is discharged

`lhs_term1_statement_of_cocycle` applies `lhs_term1_of_stationaryAnchor d hd`, so every
binder of the statement other than `hRealization` — the viscosity, the
shell law and the four standing laws, the non-degeneracy constants, the scale
selection, the unit direction, the test vector, the glued flux with its defining
formula, the Dirichlet response and its defining predicate — is discharged
inside the proof.  The proof is one application; no obligation migrates into the
statement.

## What remains

`hRealization` is the realization of the stationary potential response at the
concrete carrier.  As written it carries no stationarity cocycle, because the
`hStationaryAnchor` binder it mirrors carries none: the chain that consumes it
supplies the cocycle for the concrete glued flux by `sandwichFlux_cocycle`, which is
available only at the specific flux family and not for an arbitrary `F`.  A
realization stated for an arbitrary field therefore has to carry the cocycle
explicitly; the theorem `lhs_term1_statement_of_cocycle` below accepts that
shape, with `sandwichFlux_cocycle` discharging the cocycle inside its proof.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

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
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal

noncomputable section

/-- **The `l.LHS.term1` conclusion from the concrete-carrier realization
with its stationarity cocycle.**

The conclusion is the statement verbatim, as in `l_LHS_term1_constFirst`.
The single named hypothesis `hRealization` is the concrete-carrier realization
in the shape in which an arbitrary-field realization must be stated: the
stationarity cocycle `F (x +ᵥ omega) y = F omega (y + x)` is a binder, as it is
in the abstract statement and in
`RealizationSecondConjunct.exists_realization_of_anchorPairing`.  It is binder
for binder — with `M := S.m` — the concrete target statement, specialized to
`Ω = ShellSeq d` and `μ = P.toMeasure`.  Inside
the proof the cocycle for the concrete glued flux
`F = (κ_{L'} − κ_{ℓ'}) p` is produced by `sandwichFlux_cocycle`, so no cocycle
clause reaches the surface of the statement. -/
theorem lhs_term1_statement_of_cocycle (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hRealization : ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (S : ScaleSelection)
        (F : ShellSeq d → Vec d → Vec d) (gradHatW : ShellSeq d → Vec d),
      (∀ (omega : ShellSeq d) (x y : Vec d), F (x +ᵥ omega) y = F omega (y + x)) →
      ∀ (hFmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
          (hGmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
        (hGmemLp.toLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (gradHatW omega))) =
          -@stationaryPotentialProjection d (ShellSeq d) _
            P.toMeasure _ _
            (ShellField.vaddInvariantMeasure hPrefix hJ2)
            (hFmemLp.toLp (fun omega : ShellSeq d =>
              HilbertVec.ofVec (F omega 0))) →
        ∃ uReal : ShellSeq d →
          H1Function (openCubeSet (originCube d (S.m : ℤ))),
          (∀ᵐ omega ∂P.toMeasure,
            (uReal omega).grad =ᵐ[volumeMeasureOn
                (openCubeSet (originCube d (S.m : ℤ)))]
              fun x => gradHatW (x +ᵥ omega)) ∧
          (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function
              (openCubeSet (originCube d (S.m : ℤ))),
            ∫ x in openCubeSet (originCube d (S.m : ℤ)),
                vecDot ((uReal omega).grad x)
                  (phi.toH1Function.grad x) =
              -∫ x in openCubeSet (originCube d (S.m : ℤ)),
                vecDot (F omega x) (phi.toH1Function.grad x))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P), ShellLawJ1Restriction d P →
          ∀ (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P), ShellLawJ4 d P →
          ∀ (cStar K : ℝ), ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ (S : ScaleSelection), ScalesOrdering S →
          ∀ (e : Vec d), Homogenization.vecNormSq e = 1 →
            Homogenization.Book.Ch02.vecNorm e = 1 →
            ∀ (p : Vec d), p = testVector nu S.LPrime P S.n e →
            ∀ (F : ShellSeq d → Vec d → Vec d),
              (∀ omega : ShellSeq d, F omega = fun x =>
                Homogenization.matVecMul
                  (SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.LPrime x -
                    SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.ellPrime x) p) →
              ∀ (w : ShellSeq d →
                  Homogenization.H10Function
                    (Homogenization.openCubeSet
                      (Homogenization.originCube d (S.m : ℤ)))),
                (∀ omega : ShellSeq d,
                  IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega)
                    (w omega)) →
                |(∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                  ℝ≥0∞).toReal -
                  cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
                (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  obtain ⟨C, hC, hmain⟩ := lhs_term1_of_stationaryAnchor d hd
  refine ⟨C, hC, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e he
    hunit p hp F hF w hwD
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e he
    hunit p hp F hF w hwD
    (fun gradHatW hFmemLp hGmemLp hproj =>
      hRealization P hPrefix hJ2 S F gradHatW
        (sandwichFlux_cocycle S p F hF) hFmemLp hGmemLp hproj)

end

end SuperdiffusionCLT.Section3.Terms
