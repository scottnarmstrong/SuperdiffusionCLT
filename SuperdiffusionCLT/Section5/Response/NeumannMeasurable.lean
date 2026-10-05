/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.NeumannRealizationInputs
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilitySelection

/-!
# Measurability in the sample of the Neumann response gradient

The Neumann response lives in the zero-average space `H1MeanZeroFunction`, so
the additive constant is normalized away by the carrier and no selection of the
constant is involved: as in the Dirichlet case, the weak-gradient class is the
continuous (`1`-Lipschitz) solution operator `cubeNeumannGradClass` applied to
the measurable flux class, and every selection has that class.  This follows
`ResponseMeasurabilitySelection`, reusing `cubeNeumannGradClass`
of `Section3/Terms/NeumannRealizationInputs.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms

noncomputable section

variable {d : ℕ}

/-- **Measurability of the Neumann response gradient of `e.def.w`**, every
selection, no hypothesis beyond the response predicate. -/
theorem measurable_gradToHilbertVectorL2_of_isCubeNeumannResponse_rhsField
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {w : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
        (originCube d (m : ℤ)) (dirichletRhsField omega LPrime ellPrime p) (w omega)) :
    Measurable (fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2) :=
  measurable_gradToHilbertVectorL2_neumannResponse hw

/-- The Neumann cube-energy map is `Measurable` (no measure) for every selection. -/
theorem measurable_vecCubeLpENorm_grad_of_isCubeNeumannResponse
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {w : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
        (originCube d (m : ℤ)) (dirichletRhsField omega LPrime ellPrime p) (w omega)) :
    Measurable (fun omega : ShellSeq d =>
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) := by
  have hfun : (fun omega : ShellSeq d =>
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^
            ((1 : ENNReal) / 2).toReal *
          ‖(w omega).toH1Function.gradToHilbertVectorL2‖ₑ :=
    funext fun omega => vecCubeLpENorm_grad_eq_enorm_gradToHilbertVectorL2 _
  rw [hfun]
  exact (continuous_enorm.measurable.comp
    (measurable_gradToHilbertVectorL2_neumannResponse hw)).const_mul _

/-- **Satisfiability.**  A responding family for the concrete flux exists at
every sample, so the hypothesis `hw` above is inhabited. -/
example (LPrime ellPrime m : ℕ) (p : Vec d) :
    ∃ w : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (m : ℤ))),
      ∀ omega : ShellSeq d, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
        (originCube d (m : ℤ)) (dirichletRhsField omega LPrime ellPrime p) (w omega) :=
  ⟨fun omega => Classical.choose
      (SuperdiffusionCLT.Section3.ResponseFields.exists_isCubeNeumannResponse _
        (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)),
    fun omega => Classical.choose_spec
      (SuperdiffusionCLT.Section3.ResponseFields.exists_isCubeNeumannResponse _
        (memVectorL2_dirichletRhsField omega LPrime ellPrime m p))⟩

end

end SuperdiffusionCLT.Section5
