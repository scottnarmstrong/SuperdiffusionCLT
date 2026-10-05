/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.EnergySandwichBridge
public import SuperdiffusionCLT.Section3.Setup.StationaryProjectionBridge
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB

/-!
# The dischargeable inputs of the `hSandwich` obligation of `l.LHS.term1`

`lhs_of_sandwich` (in `Section3/Terms/LHSTerm1Assembly.lean`) proves
`l.LHS.term1` with one residue: the existential `hSandwich` of
`lhs_of_chain` (in `Section3/Terms/LHSTerm1FrozenReduction.lean`) —
the invariant measure, the projection triple, the Neumann response and the two
inequalities of `e.energy.comparison.N.D`.  This module
discharges every part of it that the library already supplies, and states the
residue as the two inputs it actually needs.

* `streamCutoff_vadd` and `sandwichFlux_cocycle`: the stationarity cocycle
  `F (x +ᵥ omega) y = F omega (y + x)` of the cocycle binder, for the
  concrete flux `F = (k_{L'} − k_{ℓ'}) p`, from the shell translation
  (`ShellField.translate_apply`, `ShellField.vadd_eq_translate`) and the
  pointwise reading of the cutoff (`streamCutoff_apply`).
* `lhs_sandwich_of_neumannMeas_of_realization`: the `hSandwich` existential of
  `lhs_of_chain` supplied up to two inputs — the measurability transfer for the
  Neumann energy map and the realization block of the stationary potential
  field.  Everything else is discharged inside: the invariant measure by
  `ShellField.vaddInvariantMeasure`, the projection triple by
  `Section3.Setup.stationary_projection_bridge` (with
  `p = lam • e`, i.e. the `testVector` shape of the statement, since
  `testVector` is a scalar multiple of `e` by definition), the Neumann response
  by `exists_isCubeNeumannResponse` at the square integrability
  `memVectorL2_dirichletRhsField` of the concrete flux, the measurability of the
  Dirichlet energy map by `aestronglyMeasurable_vecCubeLpENorm_grad`, and both
  inequalities by `Section3.Setup.energy_sandwich_of_stationary` — the
  statement `Frozen.Section3.responseFields_stationary` at the cube `cu_m`.

The two surviving inputs are, in the shape the master assembly
(the `hData` residue of `Section3/Setup/MasterIdentityResidue.lean`) carries them:

* `hNmeas`: the Neumann twin of `aestronglyMeasurable_vecCubeLpENorm_grad`, for
  an arbitrary selection of the Neumann response — the Dirichlet twin runs
  through the uniqueness of the response gradient class and the continuity of
  the Dirichlet solution operator; no Neumann solution-operator statement is
  available (see `Section3/Setup/ResponseMeasurabilityB.lean`).
* `hReal`: the realization of the stationary potential gradient on the cube as
  an `H¹` field with its weak gradient the sample field, solving the interior
  identity against the flux, together with the joint measurability of the two
  sample fields — primitive data of the statement
  `Frozen.Section3.responseFields_stationary`, and the `hReal` conjunct
  of the `hData` residue of the master assembly verbatim.
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
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The stationarity cocycle of the concrete flux -/

/-- The infrared cutoff of the translated shell sequence is the translated
cutoff: the translation action on `ShellSeq d` is the pointwise shell
translation, and each shell acts by precomposition with `x ↦ x + z`. -/
theorem streamCutoff_vadd (omega : ShellSeq d) (L : ℕ) (x y : Vec d) :
    streamCutoff (x +ᵥ omega) L y = streamCutoff omega L (y + x) := by
  simp only [streamCutoff_apply, Pi.vadd_apply, ShellField.vadd_eq_translate,
    ShellField.translate_apply]

/-- **The stationarity cocycle of the sandwich flux.**  The cocycle
binder `F (x +ᵥ omega) y = F omega (y + x)` for the concrete flux
`F = (k_{L'} − k_{ℓ'}) p` of the defining clause `hF`: the translated
cutoff is the translated argument (`streamCutoff_vadd`), so the two readings of
the flux agree. -/
theorem sandwichFlux_cocycle (S : ScaleSelection) (p : Vec d)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
    (omega : ShellSeq d) (x y : Vec d) :
    F (x +ᵥ omega) y = F omega (y + x) := by
  simp only [hF, streamCutoff_vadd]

/-- **The `testVector` is a scalar multiple of the direction.**  The `p = lam • e`
shape the projection bridge consumes, with
`lam = shom_{L',*}^{-1/2}(cu_n)`. -/
theorem testVector_eq_smul [NeZero d] (nu : ℝ) (LPrime : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (e : Vec d) :
    testVector nu LPrime P n e = sigmaBarStarInvSqrt nu LPrime P n • e := rfl

/-! ## The `hSandwich` obligation up to its two real inputs -/

/-- **The `hSandwich` existential of `lhs_of_chain`, supplied up to the Neumann
energy measurability and the realization block.**

Of the five witnesses and four conjuncts of the obligation
(see `lhs_of_chain` in `Section3/Terms/LHSTerm1FrozenReduction.lean`), this theorem
discharges four witnesses and the first two conjuncts:

* `hInvS` — by `ShellField.vaddInvariantMeasure` on the prefix law and `J2`;
* `hFmemLp`, `gradHatW`, `hGmemLp`, `hproj` — by
  `Section3.Setup.stationary_projection_bridge`, at
  `lam = shom_{L',*}^{-1/2}(cu_n)`, which is what `p = testVector …`
  is by definition (`testVector_eq_smul`);
* `wN` and the Neumann conjunct — by `exists_isCubeNeumannResponse` at the
  square integrability `memVectorL2_dirichletRhsField` of the concrete flux.

The two inequalities are `Section3.Setup.energy_sandwich_of_stationary`, whose
remaining inputs are exactly the two hypotheses `hNmeas` and `hReal` here: the
Neumann twin of the Dirichlet energy measurability, and the realization block of
the stationary potential gradient (the `hReal` conjunct of the `hData` residue
of the master assembly, verbatim).  The stationarity cocycle
binders are discharged internally by `sandwichFlux_cocycle`, and the Dirichlet
energy measurability by `aestronglyMeasurable_vecCubeLpENorm_grad`. -/
theorem lhs_sandwich_of_neumannMeas_of_realization
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
    (w : ShellSeq d →
      H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega) (w omega))
    (hNmeas : ∀ (wN : ShellSeq d →
        H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
      (∀ omega : ShellSeq d,
        IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega)) →
      AEStronglyMeasurable (fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wN omega).toH1Function.grad) P.toMeasure)
    (hReal : ∀ (gradHatW : ShellSeq d → Vec d)
        (hFmemLp : MemLp (fun omega : ShellSeq d =>
          HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
        (hGmemLp : MemLp (fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
      (hGmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) =
        -@stationaryPotentialProjection d (ShellSeq d) _ P.toMeasure _ _
          (ShellField.vaddInvariantMeasure hPrefix hJ2)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) →
      ∃ uReal : ShellSeq d → H1Function (openCubeSet (originCube d (S.m : ℤ))),
        (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
            HilbertVec.ofVec (gradHatW (z.2 +ᵥ z.1)))
          (P.toMeasure.prod
            (normalizedCubeMeasure (originCube d (S.m : ℤ))))) ∧
        (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
            HilbertVec.ofVec (F (z.2 +ᵥ z.1) 0))
          (P.toMeasure.prod
            (normalizedCubeMeasure (originCube d (S.m : ℤ))))) ∧
        (∀ᵐ omega ∂P.toMeasure,
          (uReal omega).grad =ᵐ[volumeMeasureOn
              (openCubeSet (originCube d (S.m : ℤ)))]
            fun x => gradHatW (x +ᵥ omega)) ∧
        (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function
            (openCubeSet (originCube d (S.m : ℤ))),
          ∫ x in openCubeSet (originCube d (S.m : ℤ)),
              vecDot ((uReal omega).grad x) (phi.toH1Function.grad x) =
            -∫ x in openCubeSet (originCube d (S.m : ℤ)),
              vecDot (F omega x) (phi.toH1Function.grad x))) :
    ∃ (hInvS : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure)
      (hFmemLp : MemLp (fun omega : ShellSeq d =>
          HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
      (gradHatW : ShellSeq d → Vec d)
      (hGmemLp : MemLp (fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
      (wN : ShellSeq d →
        H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
      (hGmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) =
        -@stationaryPotentialProjection d (ShellSeq d) _ P.toMeasure _ _ hInvS
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) ∧
      (∀ omega : ShellSeq d,
        IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega)) ∧
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) ∧
      (∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure) := by
  classical
  -- piece 1: the translation invariance of the sequence law
  have hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure :=
    ShellField.vaddInvariantMeasure hPrefix hJ2
  -- piece 2: the projection triple, at `p = lam • e`
  obtain ⟨hFmemLp, gradHatW, hGmemLp, hproj⟩ :=
    stationary_projection_bridge (P := P) S hSorder hJ3 e hunit lam p hp F hF
  -- piece 3: the square integrability of the concrete flux on the cube
  have hmemL2 : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (F omega) := by
    intro omega
    have h := memVectorL2_dirichletRhsField omega S.LPrime S.ellPrime S.m p
    have heq : dirichletRhsField omega S.LPrime S.ellPrime p = F omega := by
      show (fun x : Vec d => matVecMul
        (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
        = F omega
      exact (hF omega).symm
    rw [heq] at h
    exact h
  -- piece 3: the Neumann response, shell by shell
  choose wN hwN using fun omega : ShellSeq d =>
    exists_isCubeNeumannResponse (originCube d (S.m : ℤ)) (hmemL2 omega)
  -- the ω-measurability of the cube-energy map of the Dirichlet response
  have hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega) := by
    intro omega
    have h0 : IsCubeDirichletResponse (originCube d (S.m : ℤ))
        (fun x => matVecMul
          (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p) (w omega) := by
      rw [← hF omega]
      exact hwD omega
    exact h0
  have hDmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (w omega).toH1Function.grad) P.toMeasure :=
    aestronglyMeasurable_vecCubeLpENorm_grad hw
  -- pieces 4 and 5: the two inequalities, from the realization block
  obtain ⟨uReal, hjointG, hjointF, hgrad, hueq⟩ :=
    hReal gradHatW hFmemLp hGmemLp hproj
  obtain ⟨hlow, hup⟩ := energy_sandwich_of_stationary d hd P S F gradHatW w wN
    hDmeas (hNmeas wN hwN) uReal hjointG hjointF hgrad hueq
    (sandwichFlux_cocycle S p F hF) hFmemLp hGmemLp hproj hwD hwN
  exact ⟨hInv, hFmemLp, gradHatW, hGmemLp, wN, hproj, hwN, hlow, hup⟩

end

end SuperdiffusionCLT.Section3.Terms