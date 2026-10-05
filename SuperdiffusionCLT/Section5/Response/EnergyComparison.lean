/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.Nondeg
public import SuperdiffusionCLT.Section5.Response.NeumannMeasurable
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsStationary
public import SuperdiffusionCLT.Frozen.Section3.StationaryPotentialRealization
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyD
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section3.Terms.LHSSandwichInputs

/-!
# The stationary comparison for the energy clause of `lem.response`

In the proof of `lem.response`, for the flux `hshellFlux nu P m h · e` on the cube `cu_Kc`,
the Dirichlet and Neumann cube energies are sandwiched around the whole-space energy
`E |grad w^_e(0)|^2`,
`E ‖∇w_D‖² ≤ E |∇ŵ_e(0)|² ≤ E ‖∇w_N‖²`, and `‖∇w_N‖² = ‖∇w_D‖² + ‖∇w_N - ∇w_D‖²`.

* `abs_toReal_neumann_sub_wholeSpaceEnergy_le`: the Neumann twin of the Dirichlet display.
* `wholeSpace_sandwich_hshellFlux`: the sandwich at `ShellSeq d`, from
  `responseFields_stationary` and `stationaryPotentialRealization`, with the joint
  measurability discharged from the measure-preserving action map.
* `abs_energy_sub_hshell_le`: both energies against `cStar (log 3) h shom_{m-h}^{-2}`, given the
  second-moment bound of the gap `∇w_N - ∇w_D` (the output of the weak-norm bound) and the
  nondegeneracy clause.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Probability.Stationary
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The Neumann twin of `abs_toReal_sub_wholeSpaceEnergy_le`: from the two halves of the sandwich
and the gap identity, `|E ‖∇w_N‖² - E |∇ŵ(0)|²| ≤ B` for any bound `B` of the gap moment. -/
theorem abs_toReal_neumann_sub_wholeSpaceEnergy_le {P : ProbabilityMeasure (ShellSeq d)} {M : ℕ}
    {F : ShellSeq d → Vec d → Vec d} {gradHatW : ShellSeq d → Vec d}
    {wD : ShellSeq d → H10Function (openCubeSet (originCube d (M : ℤ)))}
    {wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))}
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (M : ℤ)) (F omega) (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (M : ℤ)) (F omega) (wN omega))
    (hwDmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad) P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d =>
      HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hlow : ∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure ≤
      ∫⁻ omega : ShellSeq d,
        ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure)
    (hup : ∫⁻ omega : ShellSeq d,
        ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
      ∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure)
    {B : ℝ} (hB : 0 ≤ B)
    (hgapB : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x -
          (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal B) :
    |(∫⁻ omega : ShellSeq d, vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure : ℝ≥0∞).toReal -
        wholeSpaceEnergy P.toMeasure gradHatW| ≤ B := by
  have hEtop : (∫⁻ omega : ShellSeq d,
      ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    lintegral_enorm_sq_ofVec_ne_top hGmemLp
  have hAtop : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
      (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := ne_top_of_le_ne_top hEtop hlow
  have hmeasA : AEMeasurable (fun omega : ShellSeq d => vecCubeLpENorm
      (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ))
      P.toMeasure := hwDmeas.aemeasurable.pow_const 2
  have hsum : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure) =
      (∫⁻ omega : ShellSeq d, vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure) +
        ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x -
            (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure := by
    rw [← lintegral_add_left' hmeasA]
    exact lintegral_congr fun omega =>
      vecCubeLpENorm_two_sq_energy_gap (hwN omega) (hwD omega)
  have hNle : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure) ≤
      (∫⁻ omega : ShellSeq d,
        ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) + ENNReal.ofReal B := by
    rw [hsum]
    exact add_le_add hlow hgapB
  have hfin : (∫⁻ omega : ShellSeq d,
      ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) + ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hEtop, ENNReal.ofReal_ne_top⟩
  have hNtoReal := ENNReal.toReal_mono hfin hNle
  rw [ENNReal.toReal_add hEtop ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hB] at hNtoReal
  have hNtop : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := ne_top_of_le_ne_top hfin hNle
  have hEle := ENNReal.toReal_mono hNtop hup
  rw [wholeSpaceEnergy, abs_of_nonneg (sub_nonneg.2 hEle)]
  linarith only [hNtoReal]

/-- The flux `hshellFlux` is the Dirichlet right-hand side of the concrete cutoffs at `p = shom⁻¹ e`. -/
theorem hshellFlux_eq_dirichletRhsField [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (omega : ShellSeq d) (e : Vec d) :
    hshellFlux nu P m h omega e =
      dirichletRhsField omega m (m - h)
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ • e) := by
  funext x
  simp only [hshellFlux, dirichletRhsField, matVecMul_smul_right]

/-- The stationarity cocycle of `hshellFlux`. -/
theorem hshellFlux_cocycle [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (e : Vec d) (omega : ShellSeq d) (x y : Vec d) :
    hshellFlux nu P m h (x +ᵥ omega) e y = hshellFlux nu P m h omega e (y + x) := by
  simp only [hshellFlux, streamCutoff_vadd]

end

end SuperdiffusionCLT.Section5
