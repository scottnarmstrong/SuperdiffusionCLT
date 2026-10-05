/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.StationaryRealization
public import SuperdiffusionCLT.Probability.RealizationAbstractClose

/-!
# Stationary potential realization

The printed source is `l.abstract.response.fields` (Section 3), with its use on a cube.

The action carrier is `[MeasurableVAdd₂ (Vec d) Ω]` (the action map
`(x, ω) ↦ x +ᵥ ω` jointly measurable), which implies the weaker `[MeasurableConstVAdd (Vec d) Ω]`
(each translate measurable). The weaker assumption would not suffice: the statement is false
under it, already at dimension two with zero forcing, on a
measure-preserving action with measurable translates but a non-jointly-measurable action map.
Joint measurability is what makes the translated sample field `x ↦ gradHatW (x +ᵥ ω)` measurable
in `x` and the Fubini transfer between `Ω` and the cube available; the paper's stationary
random fields are jointly measurable, so this is the reading the source intends.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

/--
The assumption for the stationary potential response.
The theorem is constant-free: the source lemma introduces no new comparison
constant, so `d` and `hd` are the first binders.  The
measure/action binders formalize the printed stationary probability carrier;
`_hcocycle` is exactly the printed stationarity of `F`; `hF` is the printed
finite second moment at the origin; and `hG` plus `hproj` are the typing and
L² potential/solenoidal characterization needed to express the printed
stationary potential field.  No response-function, Neumann, Dirichlet, or
product-measurability hypothesis is included.  The conclusion supplies the
actual cube `H¹` realization, its translated-gradient identity, and the
interior weak equation used in the proof of `e.energy.comparison.N.D`.
-/
theorem SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization.{u}
    (d : ℕ) (hd : 2 ≤ d) :
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      [AddAction (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
      [VAddInvariantMeasure (Vec d) Ω μ]
      (F : Ω → Vec d → Vec d) (gradHatW : Ω → Vec d) (M : ℕ),
      (_hcocycle : ∀ (ω : Ω) (x y : Vec d), F (x +ᵥ ω) y = F ω (y + x)) →
      ∀ hF : MemLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)) 2 μ,
      ∀ hG : MemLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) 2 μ,
      (hG.toLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) =
        -SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection
          (μ := μ) (hF.toLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)))) →
      ∃ uReal : Ω → H1Function (openCubeSet (originCube d (M : ℤ))),
        (∀ᵐ ω ∂μ,
          (uReal ω).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
            fun x => gradHatW (x +ᵥ ω)) ∧
        (∀ᵐ ω ∂μ, ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
          ∫ x in openCubeSet (originCube d (M : ℤ)),
              vecDot ((uReal ω).grad x) (φ.toH1Function.grad x) =
            -∫ x in openCubeSet (originCube d (M : ℤ)),
              vecDot (F ω x) (φ.toH1Function.grad x))
    := by
  have _hdim : 2 ≤ d := hd
  intro Ω _ μ _ _ _ _ F gradHatW M hcocycle hF hG hproj
  exact SuperdiffusionCLT.Probability.Stationary.realizationAbstractClose_exists_realization
    (μ := μ) M F gradHatW hcocycle hF hG hproj

end
