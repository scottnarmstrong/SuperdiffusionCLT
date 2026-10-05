/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyApriori
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# `l.LHS.term1`, with its missing inputs named

`SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst`
asks for the display `e.nabla.w.lower.bound` with the constant
quantified before every piece of Section 3 data and with **only** the printed
hypotheses: the standing shell laws, `0 < nu ≤ 1`, the scale selection with
`ScalesOrdering`, and the defining data of the displayed objects.

This module states that statement once more, under the name `lhs_of_chain`,
with exactly the same binders and conclusion, plus four
explicitly named binders, one for each input that the chain
`SuperdiffusionCLT.Section3.Setup.l_LHS_term1_of_apriori` needs and that the
statement does not carry.  Everything else the chain consumes is
discharged inside the proof:

* `ShellLawJ1` from `ShellLawJ1Restriction`
  (`Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction`);
* the translation invariance of `P` from the prefix law and J2
  (`Frozen.Assumptions.ShellField.vaddInvariantMeasure`);
* the `hJ5app` display of `a.j.nondeg` at the block `(ℓ', L']`, from the
  `nondegenerate` field of the `ShellLawJ5` binder itself;
* the two per-shell response families `wDr`, `wNr` of the block `(ℓ', L']`, by
  solvability (`exists_isCubeDirichletResponse`, `exists_isCubeNeumannResponse`)
  on the shell flux, which is square integrable on the cube
  (`memVectorL2_shellFlux`).

The four named binders are the residue, in the exact shape the chain consumes:

* `hDmeas`: the `ω`-measurability of the cube-energy map of the given Dirichlet
  response.  The print's `E[⨍|∇w|²]` is a genuine expectation, and the
  statement quantifies `w` over every realization of the Dirichlet-response
  predicate, so the measurability has to come from the response carrier and the
  measurability of the flux, not from the statement.
* `hSandwich`: the projection triple of the flux together with the two
  inequalities of `e.energy.comparison.N.D` and the Neumann
  response.  The projection triple alone is supplied by
  `Section3.Setup.stationary_projection_bridge`; the Neumann response exists by
  `exists_isCubeNeumannResponse`; the two inequalities are the substance.  The
  route to them is `Section3.Setup.energy_sandwich_of_stationary`, which
  additionally consumes the realization `u` of the stationary potential gradient
  with `hgrad`, `hueq`, the joint measurability `hjointG`, `hjointF`, the
  measurability of the Neumann energy map, the cocycle of stationarity
  and `hDmeas`.
* `hZl4`: the `L̲⁴` bound of the paper as one family with the scale-free
  constant `Cz`.  The witness `Zl4Witness` needs the gate
  `2 * shellFluxValueEnvelopeAmplitude d (S.m) ≤ Cl4`, which grows with `S.m`;
  a constant fixed before the scale selection cannot serve through it.
* `hZhmGe`: the `r > S.m` form of `e.jk.Hminus.endpoint` as
  one family with the scale-free constant `Cge`.  The pointwise clause of the
  witness needs the same scale-dependent gate, and the `Γ₂` clause at
  `Cge * |p| * 3^{-(r - S.m)}` is not covered by any available result: it is the deterministic
  Poincaré step the print takes from `a.j.reg`.

The conclusion is that of the statement, unchanged.
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

/-- **`l.LHS.term1` with the constant quantified first, from the chain.**
The binders and the conclusion between the markers are the statement of
`SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst` verbatim; the
two d-only constants `Cz`, `Cge` and the four binders `hDmeas`, `hSandwich`,
`hZl4`, `hZhmGe` are the inputs the chain
`l_LHS_term1_of_apriori` consumes that the statement does not carry.  The
proof discharges `ShellLawJ1`, the translation invariance of `P`, the block
display `hJ5app` of `ShellLawJ5` and the two per-shell response
families; it applies the chain unchanged. -/
theorem lhs_of_chain
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Cz Cge : ℝ) (hCz : 0 < Cz) (hCge : 0 < Cge) :
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
                (hDmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
                    vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                      (w omega).toH1Function.grad) P.toMeasure) →
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
                (hZl4 : ∃ Zl4 : ℕ → ShellSeq d → ℝ,
                  (∀ r omega, 0 ≤ Zl4 r omega) ∧
                  (∀ r, Measurable (Zl4 r)) ∧
                  (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
                    IsBigO P.toMeasure (gammaSigma 2) (Zl4 r)
                      (Cz * Book.Ch02.vecNorm p)) ∧
                  (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
                    vecCubeLpENorm (originCube d (S.m : ℤ)) 4
                      (fun x => shellFlux omega r p x -
                        volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                          (shellFlux omega r p)) ≤
                      ENNReal.ofReal (Zl4 r omega))) →
                (hZhmGe : ∃ ZhmGe : ℕ → ShellSeq d → ℝ,
                  (∀ r omega, 0 ≤ ZhmGe r omega) ∧
                  (∀ r, Measurable (ZhmGe r)) ∧
                  (∀ r ∈ Finset.Ioc S.m S.LPrime,
                    IsBigO P.toMeasure (gammaSigma 2) (ZhmGe r)
                      (Cge * Book.Ch02.vecNorm p *
                        (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ)))) ∧
                  (∀ r ∈ Finset.Ioc S.m S.LPrime, ∀ omega : ShellSeq d,
                    vecHatNegENormOrderOne (originCube d (S.m : ℤ))
                      (fun x => shellFlux omega r p x -
                        volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                          (shellFlux omega r p)) ≤
                      ENNReal.ofReal (ZhmGe r omega))) →
                |(∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                  ℝ≥0∞).toReal -
                  cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
                (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  classical
  obtain ⟨Clhs, hClhs, hmain⟩ := l_LHS_term1_of_apriori d hd Cz Cge hCz hCge
  refine ⟨Clhs, hClhs, ?_⟩
  intro nu hnu _hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e he hunit
    p hp F hF w hwD hDmeas hSandwich hZl4 hZhmGe
  have _hd := hd
  -- the restriction form `ShellLawJ1Restriction` implies the integral form `ShellLawJ1`
  have hJ1 : ShellLawJ1 d P :=
    SuperdiffusionCLT.Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction
      hJ1V2
  -- the translation invariance of the sequence law, from the prefix and J2
  have hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure :=
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.vaddInvariantMeasure
      hPrefix hJ2
  -- the projection triple, the Neumann response and the two sandwich clauses
  obtain ⟨_hInvS, hFmemLp, gradHatW, hGmemLp, wN, hproj, hwN, hlow, hup⟩ :=
    hSandwich
  -- the two witness families
  obtain ⟨Zl4, hZl40, hZl4Meas, hZl4BigO, hZl4Bound⟩ := hZl4
  obtain ⟨ZhmGe, hZhmGe0, hZhmGeMeas, hZhmGeBigO, hZhmGeBound⟩ := hZhmGe
  -- the per-shell responses, by solvability on every shell
  have hDexist : ∀ (r : ℕ) (omega : ShellSeq d),
      ∃ v : H10Function (openCubeSet (originCube d (S.m : ℤ))),
        IsCubeDirichletResponse (originCube d (S.m : ℤ)) (shellFlux omega r p) v :=
    fun r omega => exists_isCubeDirichletResponse (originCube d (S.m : ℤ))
      (memVectorL2_shellFlux (originCube d (S.m : ℤ)) r omega p)
  have hNexist : ∀ (r : ℕ) (omega : ShellSeq d),
      ∃ v : H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))),
        IsCubeNeumannResponse (originCube d (S.m : ℤ)) (shellFlux omega r p) v :=
    fun r omega => exists_isCubeNeumannResponse (originCube d (S.m : ℤ))
      (memVectorL2_shellFlux (originCube d (S.m : ℤ)) r omega p)
  choose wDr hwDr using hDexist
  choose wNr hwNr using hNexist
  -- the block display of `ShellLawJ5`, at the block `(ℓ', L']`
  have hlt : S.ellPrime < S.LPrime :=
    lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime
  have hJ5app : |‖blockPotentialResponse P S.ellPrime S.LPrime
          (blockRegLaw_stationary hPrefix hJ2 S.ellPrime S.LPrime) e
          (memLp_originForcing_blockRegLaw hJ3 S.ellPrime S.LPrime e
            hunit)‖ ^ 2 -
        cStar * Real.log 3 * ((S.LPrime - S.ellPrime : ℕ) : ℝ)| ≤ K :=
    hJ5.nondegenerate S.ellPrime S.LPrime hlt e hunit
  exact hmain nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 hInv cStar K S hSorder e he hunit
    p hp F hF gradHatW w wN hwD hwN hDmeas hFmemLp hGmemLp hproj hlow hup hJ5app
    wDr wNr (fun r _hr omega => hwDr r omega) (fun r _hr omega => hwNr r omega)
    Zl4 hZl40 hZl4Meas hZl4BigO hZl4Bound ZhmGe hZhmGe0
    hZhmGeMeas hZhmGeBigO hZhmGeBound

end

end SuperdiffusionCLT.Section3.Terms