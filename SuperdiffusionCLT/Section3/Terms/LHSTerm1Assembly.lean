/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.LHSTerm1FrozenReduction
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section3.Setup.ShellFluxWitnessesB
public import SuperdiffusionCLT.Section3.Setup.ShellFluxWitnessesC

/-!
# `l.LHS.term1` with the Neumann sandwich as its one residue

`lhs_of_chain` (`Section3/Terms/LHSTerm1FrozenReduction.lean`) reduces
`l.LHS.term1` to four obligations, `hDmeas`, `hSandwich`, `hZl4` and
`hZhmGe`.  Three of them are proved here:

* `hDmeas` — the `ω`-measurability of the cube-energy map of the Dirichlet
  response — by `Section3.Setup.aestronglyMeasurable_vecCubeLpENorm_grad`
  (`Section3/Setup/ResponseMeasurabilityB.lean`).  That theorem is stated for
  the `Setup` predicate `IsDirichletResponse omega LPrime ellPrime m p w`, which
  is definitionally `IsCubeDirichletResponse (originCube d (m : ℤ))
  (fun x => matVecMul (streamCutoff omega LPrime x - streamCutoff omega
  ellPrime x) p) w` (`Section3/Setup/Scales.lean`, `IsDirichletResponse`), so the
  `hwD` binder and the defining clause `hF` of the response field
  `F` deliver it verbatim.
* `hZl4` — the scale-free `L̲⁴` envelope of the centred shell flux — by
  `Section3.Setup.exists_shellFluxL4Witness_scaleFree`
  (`Section3/Setup/ShellFluxWitnessesC.lean`), whose statement is the `hZl4`
  binder verbatim with the d-only constant `shellFluxL4Const d`.
* `hZhmGe` — the `r > m` form of `e.jk.Hminus.endpoint` — by
  `Section3.Setup.exists_shellFluxHatNegWitness_scaleFree`
  (`Section3/Setup/ShellFluxWitnessesB.lean`), whose statement is the `hZhmGe`
  binder verbatim with the d-only constant `shellFluxLipConst d`.

The two theorems take the envelope constants as hypotheses of the form
`const ≤ C`, not as bare positivity, so `lhs_of_sandwich` fixes them itself: the
chain is applied at `Cz = 1 + shellFluxL4Const d` and
`Cge = 1 + shellFluxLipConst d`, which dominate the required constants by
`le_add_of_nonneg_left` and are positive by the nonnegativity of the constants.
The constant `C` of the conclusion depends on them through the chain
(`l_LHS_term1_of_apriori` takes them as its `Cl4`, `ChmGe`), so the existential
of the conclusion absorbs the choice and the statement carries none of
the four discharged binders.

`lhs_of_sandwich` is therefore the statement of
`SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst` once more, with
exactly one explicit residue binder: `hSandwich`, the projection triple
(`hFmemLp`, `gradHatW`, `hGmemLp`, `hproj`), the Neumann response `wN` and the
two inequalities of `e.energy.comparison.N.D`, in the shape the chain consumes.
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

/-- **`l.LHS.term1` with the constant quantified first, up to the energy
sandwich.**  The binders and the conclusion are the statement of
`SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst` verbatim; the
single added binder `hSandwich` is the one obligation of `lhs_of_chain`
(`Section3/Terms/LHSTerm1FrozenReduction.lean`) that is not discharged here: the
projection triple, the Neumann response and the two clauses of
`e.energy.comparison.N.D`.  The three discharged
obligations `hDmeas`, `hZl4` and `hZhmGe` are produced inside the proof from
`aestronglyMeasurable_vecCubeLpENorm_grad`,
`exists_shellFluxL4Witness_scaleFree` and
`exists_shellFluxHatNegWitness_scaleFree`, at the constants
`1 + shellFluxL4Const d` and `1 + shellFluxLipConst d`, and the chain is applied
unchanged. -/
theorem lhs_of_sandwich
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
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
                (hSandwich : ∃ (hInvS : VAddInvariantMeasure (Vec d) (ShellSeq d)
                      P.toMeasure)
                  (hFmemLp : MemLp (fun omega : ShellSeq d =>
                      HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
                  (gradHatW : ShellSeq d → Vec d)
                  (hGmemLp : MemLp (fun omega : ShellSeq d =>
                      HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
                  (wN : ShellSeq d →
                    H1MeanZeroFunction
                      (openCubeSet (originCube d (S.m : ℤ)))),
                  (hGmemLp.toLp fun omega : ShellSeq d =>
                      HilbertVec.ofVec (gradHatW omega)) =
                    -@stationaryPotentialProjection d (ShellSeq d)
                      _ P.toMeasure _ _ hInvS
                      (hFmemLp.toLp fun omega : ShellSeq d =>
                        HilbertVec.ofVec (F omega 0)) ∧
                  (∀ omega : ShellSeq d,
                    IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega)
                      (wN omega)) ∧
                  (∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
                    ∫⁻ omega : ShellSeq d,
                      ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ)
                        ∂P.toMeasure) ∧
                  (∫⁻ omega : ShellSeq d,
                      ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ)
                        ∂P.toMeasure ≤
                    ∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (wN omega).toH1Function.grad ^ (2 : ℕ)
                          ∂P.toMeasure)) →
                |(∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                  ℝ≥0∞).toReal -
                  cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
                (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  classical
  -- the two envelope constants of the discharged witnesses, inflated to be
  -- strictly positive so the chain's `Cl4` and `ChmGe` accept them
  have hCz : 0 < 1 + shellFluxL4Const d := by
    have h := shellFluxL4Const_nonneg d
    linarith only [h]
  have hCge : 0 < 1 + shellFluxLipConst d := by
    have h := shellFluxLipConst_nonneg d
    linarith only [h]
  obtain ⟨Clhs, hClhs, hmain⟩ := lhs_of_chain d hd (1 + shellFluxL4Const d)
    (1 + shellFluxLipConst d) hCz hCge
  refine ⟨Clhs, hClhs, ?_⟩
  intro nu hnu _hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e he hunit
    p hp F hF w hwD hSandwich
  -- the translation invariance of the sequence law, from the prefix and J2
  have hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure :=
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.vaddInvariantMeasure
      hPrefix hJ2
  -- the `ω`-measurability of the cube-energy map: the `Setup` predicate
  -- `IsDirichletResponse` is `IsCubeDirichletResponse` on the flux
  -- of the defining clause `hF`, so the carrier delivers the measurability theorem
  have hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega) := by
    intro omega
    have h0 : IsCubeDirichletResponse (originCube d (S.m : ℤ))
        (fun x => Homogenization.matVecMul
          (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.LPrime x -
            SuperdiffusionCLT.Frozen.Section2.streamCutoff omega S.ellPrime x)
          p) (w omega) := by
      rw [← hF omega]
      exact hwD omega
    exact h0
  have hDmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (w omega).toH1Function.grad) P.toMeasure :=
    aestronglyMeasurable_vecCubeLpENorm_grad hw
  -- the two scale-free witness families, at the inflated constants
  obtain ⟨Zl4, hZl40, hZl4Meas, hZl4BigO, hZl4Bound⟩ :=
    exists_shellFluxL4Witness_scaleFree hPrefix hJ1V2 hJ2 hJ3 hJ4 S p
      (1 + shellFluxL4Const d) (le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1))
  obtain ⟨ZhmGe, hZhmGe0, hZhmGeMeas, hZhmGeBigO, hZhmGeBound⟩ :=
    exists_shellFluxHatNegWitness_scaleFree hJ3 S p (1 + shellFluxLipConst d)
      (le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1))
  exact hmain nu hnu _hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder
    e he hunit p hp F hF w hwD hDmeas hSandwich
    ⟨Zl4, hZl40, hZl4Meas, hZl4BigO, hZl4Bound⟩
    ⟨ZhmGe, hZhmGe0, hZhmGeMeas, hZhmGeBigO, hZhmGeBound⟩

end

end SuperdiffusionCLT.Section3.Terms