/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsStationary
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyOrderOneB

/-!
# The energy sandwich at the pigeonhole cube, from the stationary comparison

The energy comparison `e.energy.comparison.N.D` of the paper, as the two binders
`hlow` and `hup` of `l_LHS_term1_constFirst_of_shellData`.

`energy_sandwich_of_stationary` is the statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_stationary` applied at
the cube `cu_m` of a scale selection, with its conclusion specialized to the
`P.toMeasure` carrier of the shell-sequence probability law and stated as the
conjunction of the two G-shaped conjuncts, so a downstream lemma may bind them
by name exactly as `l_LHS_term1_constFirst_of_shellData` does.  Nothing is
re-proved: the proof is one application of `responseFields_stationary`.

## Which binders `responseFields_stationary` forces here

`responseFields_stationary` consumes thirteen hypotheses at `M`, a general
probability carrier `Ω` and measure `μ`; all thirteen are carried here, each
verbatim in the same shape (only `M := S.m`, `Ω := ShellSeq d` and
`μ := P.toMeasure` are instantiated, and the leading underscores of its names
are dropped, since every one of them is used by the application):

* the **realization** binders that `l_LHS_term1_constFirst_of_shellData` does
  not carry at all: `u` (the `H¹` realization of the stationary potential
  gradient on the cube), `hjointG` and `hjointF` (joint measurability of the two
  sample fields on `P.toMeasure × normalizedCubeMeasure`), `hgrad` (the weak
  gradient of `u` is the sample field `x ↦ ∇ŵ(x + omega)`) and `hueq` (the
  interior identity `u` solves against `F`);
* the **data** binders that the G lemma carries under the same names and that
  are re-carried here so the application closes: `hwDmeas`, `hwNmeas`,
  `hcocycle` (the cocycle identity of stationarity, there an anonymous `→`
  hypothesis), `hFmemLp`, `hGmemLp`, `hproj`, `hwD`, `hwN`.

The `[AddAction (Vec d) Ω]` and `[MeasurableConstVAdd (Vec d) Ω]` binders are
discharged by instance search, not taken as hypotheses: on `ShellSeq d` they are
the pointwise actions over `ℕ` of the global `ShellField.addAction` and
`ShellField.sequenceMeasurableConstVAdd` (from the shell-law assumption J5), so
the `+ᵥ` of every hypothesis here and the `+ᵥ` inside the hypotheses of
`responseFields_stationary` are the same instance.  The
`[VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]` binder is carried
exactly as `l_LHS_term1_constFirst_of_shellData` carries it.

The conclusion is the conjunction of the two G binders verbatim: the lower half
binds `vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (wD omega).toH1Function.grad ^
2` against `‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ 2`, the upper half the other
way round with `wN`, both as `∫⁻` over `omega : ShellSeq d` against
`P.toMeasure`.  No reshaping was needed: the conclusion already uses the same
carrier, the same cube and the same pointwise `∫⁻` quantifier as the G binders.

## Main result

* `energy_sandwich_of_stationary`: the `hlow`/`hup` pair from
  `responseFields_stationary`.
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

/-- **`e.energy.comparison.N.D` at the cube `cu_m` of the scale selection**, the
statement `responseFields_stationary` specialized to the shell-sequence
carrier, with its conclusion the conjunction of the two binders `hlow` and `hup`
of `l_LHS_term1_constFirst_of_shellData` verbatim.

Every hypothesis is that of `responseFields_stationary`, in the same shape,
with `M := S.m`, `Ω := ShellSeq d` and `μ := P.toMeasure`; nothing is added and
nothing is re-proved. -/
theorem energy_sandwich_of_stationary (d : ℕ) (hd : 2 ≤ d)
    (P : ProbabilityMeasure (ShellSeq d))
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (S : ScaleSelection)
    (F : ShellSeq d → Vec d → Vec d) (gradHatW : ShellSeq d → Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (wN : ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
    (hwDmeas : AEStronglyMeasurable
      (fun omega => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (S.m : ℤ)) 2 (wD omega).toH1Function.grad) P.toMeasure)
    (hwNmeas : AEStronglyMeasurable
      (fun omega => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (S.m : ℤ)) 2 (wN omega).toH1Function.grad) P.toMeasure)
    (u : ShellSeq d → H1Function (openCubeSet (originCube d (S.m : ℤ))))
    (hjointG : AEStronglyMeasurable
      (fun p : ShellSeq d × Vec d => HilbertVec.ofVec (gradHatW (p.2 +ᵥ p.1)))
      (P.toMeasure.prod (normalizedCubeMeasure (originCube d (S.m : ℤ)))))
    (hjointF : AEStronglyMeasurable
      (fun p : ShellSeq d × Vec d => HilbertVec.ofVec (F (p.2 +ᵥ p.1) 0))
      (P.toMeasure.prod (normalizedCubeMeasure (originCube d (S.m : ℤ)))))
    (hgrad : ∀ᵐ omega ∂P.toMeasure,
      (u omega).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))]
        fun x => gradHatW (x +ᵥ omega))
    (hueq : ∀ᵐ omega ∂P.toMeasure,
      ∀ phi : H10Function (openCubeSet (originCube d (S.m : ℤ))),
        ∫ x in openCubeSet (originCube d (S.m : ℤ)),
            vecDot ((u omega).grad x) (phi.toH1Function.grad x) =
          -∫ x in openCubeSet (originCube d (S.m : ℤ)),
            vecDot (F omega x) (phi.toH1Function.grad x))
    (hcocycle : ∀ (omega : ShellSeq d) (x y : Vec d),
      F (x +ᵥ omega) y = F omega (y + x))
    (hFmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hproj : (hGmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) =
        -stationaryPotentialProjection (μ := P.toMeasure)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega) (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega)) :
    (∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) ∧
      (∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure) :=
  SuperdiffusionCLT.Frozen.Section3.responseFields_stationary d hd
    P.toMeasure F gradHatW S.m wD wN hwDmeas hwNmeas u hjointG hjointF hgrad hueq
    hcocycle hFmemLp hGmemLp hproj hwD hwN

end

end SuperdiffusionCLT.Section3.Setup