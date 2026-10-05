/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.FullField
public import MarkovProcess.Feller.Semigroup
public import MarkovProcess.Semigroup.Generator
public import MarkovProcess.FiniteTime.ProjectiveFamily
public import MarkovProcess.Trajectory.Equivariance
public import MarkovProcess.Main

/-!
# The process of `∇·(ν Id + k)∇` and the rescaled operators: statement carriers

The classical divergence-form operator, the generator characterisation of the Feller process of
`e.sde.intro`, continuous-path laws with prescribed finite-dimensional distributions, path
rescaling, and the operators `L^ε` of `e.A.ep`.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess

variable {d : ℕ}

/-- The classical divergence-form operator `c ∇·(a ∇φ)(x) = c ∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ ∂ⱼ φ)(x)`. -/
noncomputable def divForm (c : ℝ) (a : CoeffField d) (φ : Vec d → ℝ) (x : Vec d) : ℝ :=
  c * ∑ i : Fin d,
    fderiv ℝ (fun y => ∑ j : Fin d, a y i j * fderiv ℝ φ y (Pi.single j 1)) x (Pi.single i 1)

/-- `f ∈ C₀(ℝ^d)`: `f` is the underlying function of an element of `C₀(Vec d, ℝ)`. -/
def IsC0Function (f : Vec d → ℝ) : Prop :=
  ∃ g : C₀(Vec d, ℝ), ⇑g = f

/-- `S` is a conservative Feller semigroup on `C₀(ℝ^d)` whose generator is `∇·(a∇·)` on every
`u ∈ C² ∩ C₀` with `∇·(a∇u) ∈ C₀`. -/
def IsDivergenceFormFeller (a : CoeffField d) (S : SubMarkovKernelSemigroup (Vec d)) : Prop :=
  S.IsConservative ∧
    ∃ hF : S.IsFellerKernelSemigroup,
      ∀ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 (⇑u) → (∀ x, v x = divForm 1 a (⇑u) x) →
        ∃ hu : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu⟩ = v

/-- `Q x` is a probability law on continuous paths with the finite-dimensional distributions
of `S` started at `x`, for every `x`. -/
def IsContinuousPathLaw (S : SubMarkovKernelSemigroup (Vec d))
    (Q : Vec d → Measure (ContinuousPath (Vec d))) : Prop :=
  ∀ x, IsProbabilityMeasure (Q x) ∧
    ∀ I : Finset ℝ≥0, (Q x).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel S I x

/-- The path `t ↦ a • ω (c t)`. -/
noncomputable def scalePath (a : ℝ) (c : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    ContinuousPath (Vec d) :=
  (ContinuousMap.mk (fun x : Vec d => a • x) (continuous_const_smul a)).comp
    (ω.comp (ContinuousPath.timeScaling c))

/-- `½ (2 c⋆ |log ε|)^{-1/2}`, the prefactor of `L^ε` (`e.A.ep`). -/
noncomputable def opScale (cStar ε : ℝ) : ℝ :=
  (1 / 2) * ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹

/-- `τ_ε = ε^{-2} (8 c⋆ |log ε|)^{-1/2}` (`e.tau.ep.def`). -/
noncomputable def timeScale (cStar ε : ℝ) : ℝ :=
  (ε ^ 2)⁻¹ * ((8 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹

/-- `a^ε(x) = ν Id + (k - k(0))(x/ε)`. -/
noncomputable def epCoeff (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε : ℝ) : CoeffField d :=
  fun x => SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (ε⁻¹ • x)

end SuperdiffusionCLT.Section8
