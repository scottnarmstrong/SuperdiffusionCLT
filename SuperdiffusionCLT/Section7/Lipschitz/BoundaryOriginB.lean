/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryOrigin
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliL
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section7.Lipschitz.SigmaWindow
public import SuperdiffusionCLT.Section7.Analytic.Geometry.CubeFormDomainsB
public import SuperdiffusionCLT.Section6.Prereq.GammaMax
public import SuperdiffusionCLT.Section7.MinimalScale.Translate
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlarge

/-!
# The boundary Lipschitz estimate in the frame of the centre

Assembly of the boundary case analysis `lip_bdry_cases` with the cube-form boundary domains
`g1q_cube_form`, the `L²` proposition on them, the boundary Caccioppoli estimate (taken as the
hypothesis `hCB`), the interior estimate `lip_interior_origin` and the window of `σ̄`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **The boundary estimate in the frame of the centre** (the display `e.Dir.new.C01.boundary`
at a centre `y ∈ t • U`, with the oscillation about the mean on the left and, on a cube that
meets the frontier, the flatness relative to the datum `g`): assembly of `lip_bdry_cases`
with `g1q_cube_form`, `l2_prop`, the boundary Caccioppoli block `hCB`, `lip_interior_origin` and
the window of `σ̄`. -/
theorem lip_boundary_origin (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
        ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
        ∀ m n : ℕ,
        X0 omega ≤ (3 : ℝ) ^ m →
        Lhat ≤ (m : ℝ) →
        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
        n ≤ m →
        (∀ k : Fin d → ℤ,
        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
        -- e.Dir.new.full.good
        Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9)
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) ≤
        ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        -- e.Dir.new.reg.ellipticity
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
        C ∧
        -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
        (∀ u : Homogenization.AHarmonicFunction
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (fun x => Homogenization.matVecMul
        (nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P • (1 : Homogenization.Mat d))
        (u.toH1.grad x))) ≤
        ENNReal.ofReal
        (C *
        Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
        ENNReal.ofReal
        (C *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ∃ w : Homogenization.AHarmonicFunction
        (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet
        (Homogenization.originCube d ((n : ℤ) - 1))),
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2
        (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal
        (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x =>
        Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
        -- e.Dir.new.sstar.close
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) +
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaStarCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) ≤
        C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
        -- e.Dir.new.k.bounds
        ENNReal.ofReal ((m : ℝ)⁻¹) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (m : ℤ)) ∞
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
        SuperdiffusionCLT.Section2.Norms.matHatNegENorm
        (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
        ENNReal.ofReal ((m : ℝ) ^ ρ))
    (hS5 :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∃ M : ℕ,
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∀ m : ℕ, M ≤ m →
        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K))
    (hCB :
        ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ openCubeSet (originCube d 0) →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
          ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
          ∀ E : ℝ, 0 ≤ E →
          ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d))
            (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
            (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
            ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
            ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma ρ)
              (fun omega => Real.log (X0 omega)) Lhat ∧
            ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ (t : ℝ) (j : ℕ), (3 : ℝ) ^ j ≤ t → y ∈ t • U →
              X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ j → Lhat ≤ (j : ℝ) →
              LipCaccBdryS
                (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
                (sigmaBarInfinite nu j P) C E (translateSet (-y) (t • U)) 0 j) :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ openCubeSet (originCube d 0) →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∀ (B E : ℝ), 0 ≤ B → 0 ≤ E →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ n m' : ℕ, n < m' →
          (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) → Lhat ≤ (n : ℝ) →
          X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ n →
          ∀ t : ℝ, (3 : ℝ) ^ m' ≤ t → y ∈ t • U →
          ∀ (f g : Vec d → ℝ) (F G1 G2 : ℝ)
            (u : H1Function (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U))),
            ContDiff ℝ 2 g → 0 ≤ F → 0 ≤ G1 → 0 ≤ G2 →
            (∀ x ∈ shiftCube (0 : Vec d) (m' : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
            (∀ x ∈ shiftCube (0 : Vec d) (m' : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
            (∀ᵐ x ∂volume.restrict (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U)),
              |f x| ≤ F) →
            IsWeakSolutionOn
              (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
              (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U)) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn
              (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U))
              (shiftCube (0 : Vec d) (m' : ℤ)) (fun x => u.toFun x - g x) →
            AEStronglyMeasurable f
              (volume.restrict (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U))) →
            ∀ R : ℝ,
              R = C * (((3 : ℝ)⁻¹) ^ m' *
                  (lipL2 (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U))
                      (fun x => u.toFun x -
                        ⨍ w in shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U),
                          u.toFun w) +
                    lipL2 (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U))
                      (fun x => u.toFun x - g x)) +
                (sigmaBarInfinite nu m' P)⁻¹ * (3 : ℝ) ^ m' * F +
                ((m' : ℝ) - (n : ℝ)) * G1 + (n : ℝ) ^ (-E) * (3 : ℝ) ^ m' * G2) →
            (Real.sqrt (sigmaBarInfinite nu m' P))⁻¹ * Real.sqrt nu *
                lipGradL2 (shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-y) (t • U)) u.grad +
              ((3 : ℝ)⁻¹) ^ n *
                lipL2 (shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-y) (t • U))
                  (fun x => u.toFun x -
                    ⨍ w in shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-y) (t • U),
                      u.toFun w) ≤ R ∧
            (¬ shiftCube (0 : Vec d) (n : ℤ) ⊆ translateSet (-y) (t • U) →
              ((3 : ℝ)⁻¹) ^ n *
                lipL2 (shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-y) (t • U))
                  (fun x => u.toFun x - g x) ≤ R) := by
  intro U hU hU0
  obtain ⟨r, M₁, M₂, D, hUu⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  have hr : 0 < r := hUu.2.1
  obtain ⟨ag, r', M₁', M₂', D', cg, CP, hr', -, -, hg1q⟩ := g1q_cube_form hU
  obtain ⟨CL2, hCL2, hL2'⟩ := l2_prop d hd hInputs hS5 r' M₁' M₂' D' 3
  obtain ⟨CCB, hCCB, hCB'⟩ := hCB U hU hU0
  obtain ⟨CI, cI, hCI, hcI, hI'⟩ := lip_interior_origin d hd hInputs hS5
    (fun r' M₁' M₂' D' A => l2_prop d hd hInputs hS5 r' M₁' M₂' D' A) (ca_interior d hd hInputs hS5)
  obtain ⟨Cin, hCinDef⟩ : ∃ Cin : ℝ, Cin = max (max CL2 (2 * CCB)) CI := ⟨_, rfl⟩
  have hCin1 : 1 ≤ Cin := by
    rw [hCinDef]; exact le_trans hCL2 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCinL2 : CL2 ≤ Cin := by
    rw [hCinDef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCinCB : 2 * CCB ≤ Cin := by
    rw [hCinDef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCinI : CI ≤ Cin := by rw [hCinDef]; exact le_max_right _ _
  obtain ⟨Cb, c, N₀, hCb, hc, hdet⟩ :=
    lip_bdry_cases d hd Cin M₁ |M₂| r hCin1 hr (abs_nonneg _) ag 3
  refine ⟨Cb, hCb, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 B E hB hE
  obtain ⟨Lh2, hLh2, hL2P⟩ := hL2' nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨LhB, hLhB, hCBP⟩ := hCB' nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 E hE
  obtain ⟨LhI, hLhI, hIP⟩ := hI' nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨Ls, hLs⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar K
  obtain ⟨cw, hcwDef⟩ : ∃ cw : ℝ, cw = min (c / 8) (cI / 2) := ⟨_, rfl⟩
  have hcw0 : 0 < cw := by rw [hcwDef]; exact lt_min (by positivity) (by positivity)
  have hcw1 : cw ≤ c / 8 := by rw [hcwDef]; exact min_le_left _ _
  have hcw2 : cw ≤ cI / 2 := by rw [hcwDef]; exact min_le_right _ _
  obtain ⟨Lw, hLw, hwin⟩ := window_consequences cw ε ρ hcw0 hε hρ.le hρ1.le
  obtain ⟨Lw2, hLw2, hwin2⟩ := lip_bdry_origin_win hε hρ1 hB hcw0
  obtain ⟨Lt, hLt, hthr⟩ := lip_interior_origin_thresh ε ρ nu hε hρ.le hnu
  obtain ⟨Cg, hCg0, hCg⟩ := lip_bdry_origin_bigO_max3 hρ
  have hLab0 : 0 ≤ Cg * (Cg * (Lh2 + LhB) + LhI) := by
    have : 0 ≤ Cg * (Lh2 + LhB) := mul_nonneg hCg0.le (by linarith only [hLh2, hLhB])
    exact mul_nonneg hCg0.le (by linarith only [this, hLhI])
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hLs0 : (0 : ℝ) ≤ Ls := Nat.cast_nonneg _
  refine ⟨Lh2 + LhB + LhI + Cg * (Cg * (Lh2 + LhB) + LhI) + Ls + Lw + Lw2 + Lt + N₀, ?_, ?_⟩
  · linarith only [hLh2, hLhB, hLhI, hLab0, hLs0, hLw, hLw2, hLt, hN0]
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xa, hXam, hXa1, hXaO, hXaP⟩ := hL2P P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xb, hXbm, hXb1, hXbO, hXbP⟩ := hCBP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xc, hXcm, hXc1, hXcO, hXcP⟩ := hIP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hLs' := hLs P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun ω => max (max (Xa ω) (Xb ω)) (Xc ω), (hXam.max hXbm).max hXcm,
    fun ω => le_trans (hXa1 ω) (le_trans (le_max_left _ _) (le_max_left _ _)), ?_, ?_⟩
  · refine (hCg (by linarith only [hLh2]) (by linarith only [hLhB]) (by linarith only [hLhI])
      hXa1 hXb1 hXc1 hXaO hXbO hXcO).mono_scale ?_
    linarith only [hLh2, hLhB, hLhI, hLs0, hLw, hLw2, hLt, hN0]
  · intro y
    have hell := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving.ae
      (w0_ae_isElliptic_bounded hJ3 hnu)
    filter_upwards [hXaP y, hXbP y, hXcP y, hell] with ω hA hBl hC hEll
    intro n m' hnm hwin' hLn hX t htm' hyt f g F G1 G2 u hg hF hG1 hG2 hDg hD2g hFae hsol hz hfm R hR
    generalize Section6.fullCoefficientRecentered nu (ShellField.translateSequence y ω) = a
      at hA hBl hC hEll hsol
    have hLhn : LhI ≤ (n : ℝ) := by
      linarith only [hLn, hLh2, hLhB, hLab0, hLs0, hLw, hLw2, hLt, hN0]
    have hLsn : (Ls : ℝ) ≤ n := by
      linarith only [hLn, hLh2, hLhB, hLhI, hLab0, hLw, hLw2, hLt, hN0]
    have hLwn : Lw ≤ (n : ℝ) := by
      linarith only [hLn, hLh2, hLhB, hLhI, hLab0, hLs0, hLw2, hLt, hN0]
    have hLw2n : Lw2 ≤ (n : ℝ) := by
      linarith only [hLn, hLh2, hLhB, hLhI, hLab0, hLs0, hLw, hLt, hN0]
    have hLtn : Lt ≤ (n : ℝ) := by
      linarith only [hLn, hLh2, hLhB, hLhI, hLab0, hLs0, hLw, hLw2, hN0]
    have hN0n : (N₀ : ℝ) ≤ n := by
      linarith only [hLn, hLh2, hLhB, hLhI, hLab0, hLs0, hLw, hLw2, hLt]
    have hLh2n : Lh2 ≤ (n : ℝ) := by
      linarith only [hLn, hLhB, hLhI, hLab0, hLs0, hLw, hLw2, hLt, hN0, hLh2]
    have hLhBn : LhB ≤ (n : ℝ) := by
      linarith only [hLn, hLh2, hLhI, hLab0, hLs0, hLw, hLw2, hLt, hN0, hLhB]
    have hn5 : (5 : ℝ) ≤ n := le_trans hLt hLtn
    have hnm' : (n : ℝ) < m' := by exact_mod_cast hnm
    have hm'w : Lw ≤ (m' : ℝ) := le_trans hLwn hnm'.le
    have hm'w2 : Lw2 ≤ (m' : ℝ) := le_trans hLw2n hnm'.le
    have hwin3 : (m' : ℝ) - n ≤ cw * (deltaScale ε ρ (m' : ℝ))⁻¹ := by
      have := hwin2 (m' : ℝ) hm'w2
      linarith only [hwin', this]
    obtain ⟨hhalf, hn2, -, hsm, -⟩ := hwin (m' : ℝ) (n : ℝ) hm'w hnm'.le hwin3
    have hδm : 0 < deltaScale ε ρ (m' : ℝ) := deltaScale_pos hε (by linarith only [hn5, hnm'])
    have hkf : ∀ k : ℕ, n ≤ k → k ≤ m' → (n : ℝ) ≤ k ∧ (k : ℝ) ≤ m' ∧ (m' : ℝ) / 2 ≤ k ∧
        (2 : ℝ) ≤ k ∧ 0 ≤ deltaScale ε ρ (k : ℝ) ∧
        deltaScale ε ρ (k : ℝ) ≤ 2 * deltaScale ε ρ (m' : ℝ) := by
      intro k h1 h2
      have h1' : (n : ℝ) ≤ k := by exact_mod_cast h1
      have h2' : (k : ℝ) ≤ m' := by exact_mod_cast h2
      have h3 : (m' : ℝ) / 2 ≤ k := by linarith only [hhalf, h1']
      have h4 : (2 : ℝ) ≤ k := by linarith only [hn2, h1']
      exact ⟨h1', h2', h3, h4, (deltaScale_pos hε (by linarith only [h4])).le,
        deltaScale_le_two_mul ε ρ hε.le hρ.le hρ1.le h4 h3 h2'⟩
    have hsw : ∀ k : ℕ, n ≤ k → k ≤ m' → 1 ≤ sigmaBarInfinite nu k P ∧
        sigmaBarInfinite nu k P ≤ (k : ℝ) ∧
        sigmaBarInfinite nu m' P ≤ 2 * sigmaBarInfinite nu k P ∧
        sigmaBarInfinite nu k P ≤ 2 * sigmaBarInfinite nu m' P := by
      intro k h1 h2
      obtain ⟨h1', -, h3, -⟩ := hkf k h1 h2
      refine hLs' k m' ?_ h2 ?_
      · have : (Ls : ℝ) ≤ k := le_trans hLsn h1'
        exact_mod_cast this
      · have : (m' : ℝ) ≤ 2 * k := by linarith only [h3]
        exact_mod_cast this
    have hblks : ∀ k : ℕ, n ≤ k → k ≤ m' →
        1 ≤ sigmaBarInfinite nu k P ∧
          sigmaBarInfinite nu m' P ≤ 2 * sigmaBarInfinite nu k P ∧
          sigmaBarInfinite nu k P ≤ 2 * sigmaBarInfinite nu m' P ∧
          0 ≤ 2 * deltaScale ε ρ (k : ℝ) ∧
          ((k : ℝ) ^ 3)⁻¹ * Real.sqrt (sigmaBarInfinite nu k P) ≤
            2 * deltaScale ε ρ (k : ℝ) * Real.sqrt nu ∧
          ((k : ℝ) ^ 3)⁻¹ * sigmaBarInfinite nu k P ≤ 1 := by
      intro k h1 h2
      obtain ⟨hs1, hsk, hs2, hs3⟩ := hsw k h1 h2
      obtain ⟨h1', -, h3, h4, h5, -⟩ := hkf k h1 h2
      have hkL : Lt ≤ (k : ℝ) := le_trans hLtn h1'
      obtain ⟨t1, t2⟩ := hthr k (sigmaBarInfinite nu k P) hkL hs1 hsk
      have hc1 : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by have : (5 : ℝ) ≤ k := le_trans hn5 h1'; exact_mod_cast (by linarith only [this] : (1 : ℝ) ≤ k))]
        simp
      have hk5 : (5 : ℝ) ≤ k := le_trans hn5 h1'
      have hδ1 : deltaScale ε ρ (((k - 1 : ℕ)) : ℝ) ≤ 2 * deltaScale ε ρ (k : ℝ) :=
        deltaScale_le_two_mul ε ρ hε.le hρ.le hρ1.le (by rw [hc1]; linarith only [hk5])
          (by rw [hc1]; linarith only [hk5]) (by rw [hc1]; linarith only)
      refine ⟨hs1, hs2, hs3, by linarith only [h5], ?_, t2⟩
      calc ((k : ℝ) ^ 3)⁻¹ * Real.sqrt (sigmaBarInfinite nu k P)
          ≤ deltaScale ε ρ (((k - 1 : ℕ)) : ℝ) * Real.sqrt nu := t1
        _ ≤ 2 * deltaScale ε ρ (k : ℝ) * Real.sqrt nu :=
          mul_le_mul_of_nonneg_right hδ1 (Real.sqrt_nonneg _)
    have hsum : ∑ k ∈ Finset.Icc n m', 2 * deltaScale ε ρ (k : ℝ) ≤ c := by
      have h1 : ∑ k ∈ Finset.Icc n m', 2 * deltaScale ε ρ (k : ℝ) ≤
          ∑ _k ∈ Finset.Icc n m', 4 * deltaScale ε ρ (m' : ℝ) :=
        Finset.sum_le_sum fun k hk => by
          rw [Finset.mem_Icc] at hk
          obtain ⟨-, -, -, -, -, h6⟩ := hkf k hk.1 hk.2
          linarith only [h6]
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_add,
        Nat.cast_one] at h1
      have h2 : (m' : ℝ) - n + 1 ≤ 2 * ((m' : ℝ) - n) := by
        have : (n : ℝ) + 1 ≤ m' := by exact_mod_cast hnm
        linarith only [this]
      have h3 : ((m' : ℝ) + 1 - n) * (4 * deltaScale ε ρ (m' : ℝ)) ≤
          (2 * ((m' : ℝ) - n)) * (4 * deltaScale ε ρ (m' : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [h2]) (by linarith only [hδm])
      have h4 : ((m' : ℝ) - n) * deltaScale ε ρ (m' : ℝ) ≤ cw := hsm
      nlinarith only [h1, h3, h4, hcw1]
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htm'
    have hUW := lip_bdry_origin_uniform hUu ht0 y
    have hk3t : ∀ k : ℕ, k ≤ m' → (3 : ℝ) ^ k ≤ t := fun k hk =>
      le_trans (pow_le_pow_right₀ (by norm_num) hk) htm'
    have hXk : ∀ k : ℕ, n ≤ k →
        max (max (Xa (ShellField.translateSequence y ω)) (Xb (ShellField.translateSequence y ω)))
          (Xc (ShellField.translateSequence y ω)) ≤ (3 : ℝ) ^ k := fun k hk =>
      le_trans hX (pow_le_pow_right₀ (by norm_num) hk)
    have hVfam : ∀ k : ℕ, n ≤ k → k ≤ m' → ∃ V : Set (Vec d), IsOpen V ∧
        Metric.ball (0 : Vec d) ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ translateSet (-y) (t • U) ⊆ V ∧
        V ⊆ Metric.ball (0 : Vec d) ((3 : ℝ) ^ k / 2) ∩ translateSet (-y) (t • U) ∧
        LipL2Block a nu (sigmaBarInfinite nu k P) (2 * deltaScale ε ρ (k : ℝ)) Cin 3 k V := by
      intro k h1 h2
      obtain ⟨h1', -, -, -, h5, h6⟩ := hkf k h1 h2
      obtain ⟨V₀, e1, e2, e3, -, -, -⟩ := hg1q t k ht0 (hk3t k h2) y hyt
      have hV₀o : IsOpen V₀ := g1f_isOpen_of_rescaled (by positivity) y e3
      refine ⟨translateSet (-y) V₀, lip_bdry_origin_isOpen_translate hV₀o _, ?_, ?_, ?_⟩
      · rintro x ⟨hx1, hx2⟩
        rw [mem_translateSet_iff_sub_mem] at hx2 ⊢
        exact e1 ⟨(lip_bdry_origin_mem_ball_iff y x _).1 hx1, hx2⟩
      · intro x hx
        rw [mem_translateSet_iff_sub_mem] at hx
        have := e2 hx
        exact ⟨(lip_bdry_origin_mem_ball_iff y x _).2 this.1, by
          rw [mem_translateSet_iff_sub_mem]; exact this.2⟩
      · have hsub : translateSet (-y) V₀ ⊆ Section6.engCube d k := by
          rw [lip_interior_origin_engCube_eq_ball]
          intro x hx
          rw [mem_translateSet_iff_sub_mem] at hx
          exact (lip_bdry_origin_mem_ball_iff y x _).2 (e2 hx).1
        have hU' : IsUniformC11Domain (((3 : ℝ) ^ k)⁻¹ • translateSet (-y) V₀) r' M₁' M₂' D' := by
          rw [← lip_bdry_origin_image_eq]; exact e3
        have hbl := hA k (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (hXk k h1)))
          (by linarith only [hLh2n, h1', hLh2, hLhBn]) _ hsub hU'
        exact (hbl.mono_const h5 hCinL2).mono_delta (by linarith only [hCin1]) (by linarith only [h5])
    have hcacc : ∀ k : ℕ, n ≤ k → k ≤ m' →
        LipCaccBdryS a nu (sigmaBarInfinite nu k P) Cin E (translateSet (-y) (t • U)) 0 k := by
      intro k h1 h2
      obtain ⟨h1', -⟩ := hkf k h1 h2
      obtain ⟨hs1, -, -, -⟩ := hsw k h1 h2
      have := hBl t k (hk3t k h2) hyt
        (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hXk k h1))
        (by linarith only [hLhBn, h1', hLh2n])
      exact this.monoC (by linarith only [hs1]) (by linarith only [hs1]) (by linarith only [hs1])
        (by linarith only [hCCB]) hCinCB
    have hint : ∀ l k : ℕ, n ≤ l → l < k → k ≤ m' → shiftCube (0 : Vec d) (k : ℤ) ⊆
        translateSet (-y) (t • U) →
        LipIntAt a nu (sigmaBarInfinite nu k P) Cin 0 l k := by
      intro l k hl hlk hk _
      obtain ⟨hs1, -, -, -⟩ := hsw k (le_trans hl hlk.le) hk
      obtain ⟨-, -, -, -, -, h6⟩ := hkf k (le_trans hl hlk.le) hk
      have hlf : (n : ℝ) ≤ l := by exact_mod_cast hl
      have hkf' : (k : ℝ) ≤ m' := by exact_mod_cast hk
      have hcond : ((k : ℝ) - l) * deltaScale ε ρ (k : ℝ) ≤ cI := by
        have h7 : (k : ℝ) - l ≤ m' - n := by linarith only [hlf, hkf']
        have h8 : ((k : ℝ) - l) * deltaScale ε ρ (k : ℝ) ≤
            ((m' : ℝ) - n) * (2 * deltaScale ε ρ (m' : ℝ)) := by
          have hk0 : 0 ≤ (k : ℝ) - l := by
            have : (l : ℝ) < k := by exact_mod_cast hlk
            linarith only [this]
          exact mul_le_mul h7 h6 (by
            obtain ⟨-, -, -, -, h5, -⟩ := hkf k (le_trans hl hlk.le) hk
            exact h5) (by linarith only [hnm'])
        nlinarith only [h8, hsm, hcw2]
      have hLIl : LhI ≤ (l : ℝ) := le_trans hLhn hlf
      have := hC k l hlk hcond hLIl
        (le_trans (le_max_right _ _) (hXk l hl))
      exact lip_bdry_origin_intAt_mono this (by linarith only [hs1]) hCinI
    have hW0 : (0 : Vec d) ∈ translateSet (-y) (t • U) := lip_bdry_origin_zero_mem hyt
    have hrU : r * (3 : ℝ) ^ m' ≤ t * r := by
      have := mul_le_mul_of_nonneg_left htm' hr.le
      linarith only [this, mul_comm r t]
    have hMU : M₂ / t * (3 : ℝ) ^ m' ≤ |M₂| := by
      have h1 : M₂ / t * (3 : ℝ) ^ m' = M₂ * ((3 : ℝ) ^ m' / t) := by ring
      have h2 : (3 : ℝ) ^ m' / t ≤ 1 := by rw [div_le_one ht0]; exact htm'
      have h3 : 0 ≤ (3 : ℝ) ^ m' / t := by positivity
      rw [h1]
      calc M₂ * ((3 : ℝ) ^ m' / t) ≤ |M₂| * ((3 : ℝ) ^ m' / t) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h3
        _ ≤ |M₂| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |M₂| := mul_one _
    obtain ⟨Lam, hLam⟩ := hEll (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-y) (t • U))
      (by
        rw [lip_bdry_approx_shiftCube_eq_ball]
        exact Metric.isBounded_ball.subset Set.inter_subset_left)
      ((lip_bdry_approx_isOpen_cube (0 : Vec d) m').inter hUW.1).measurableSet
    have hNn : N₀ ≤ n := by
      have : (N₀ : ℝ) ≤ n := hN0n
      exact_mod_cast this
    exact hdet a (translateSet (-y) (t • U)) (t * r) (M₂ / t) (t * D) nu E nu Lam
      (fun k => sigmaBarInfinite nu k P) (fun k => 2 * deltaScale ε ρ (k : ℝ)) 0 n m' hnu hE hNn hnm
      hblks hsum hUW hrU hMU hW0 hLam hnu hcacc hVfam hint f g F G1 G2 u hg hF hG1 hG2 hDg hD2g
      hFae hsol hz hfm R hR

/-- Witness for the geometric and numerical hypotheses of `lip_boundary_origin`: the Euclidean ball
of radius `1/2` is a smooth domain inside the unit cube, the scales `n = 2 < m' = 3` satisfy the
window for `B = 1`, the centre `0` lies in the dilate `3^{m'} • U`, and the zero function is a
weak solution with zero right-hand side and vanishing localized trace for the datum `g = 0`. -/
example [NeZero d] (a : CoeffField d) :
    ∃ (U : Set (Vec d)) (n m' : ℕ) (B t : ℝ), IsSmoothBoundedDomain U ∧
      U ⊆ openCubeSet (originCube d 0) ∧ 0 ≤ B ∧ n < m' ∧
      (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) ∧ (3 : ℝ) ^ m' ≤ t ∧
      (0 : Vec d) ∈ t • U ∧
      ∃ u : H1Function (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-(0 : Vec d)) (t • U)),
        IsWeakSolutionOn a (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-(0 : Vec d)) (t • U))
          u 0 (fun _ => 0) ∧
        LocalizedZeroTraceFunctionOn
          (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-(0 : Vec d)) (t • U))
          (shiftCube (0 : Vec d) (m' : ℤ)) (fun x => u.toFun x - (0 : Vec d → ℝ) x) := by
  have hU : IsSmoothBoundedDomain (Section6.euclidBall (d := d) (1 / 2)) :=
    w0_isSmoothBoundedDomain_euclidBall (by norm_num)
  have hUc : Section6.euclidBall (d := d) (1 / 2) ⊆ openCubeSet (originCube d 0) := by
    intro x hx
    rw [Section6.mem_euclidBall] at hx
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have h1 : x i * x i ≤ vecNormSq x := by
      unfold vecNormSq vecDot
      exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
        (Finset.mem_univ i)
    have h2 : |x i| < 1 / 2 := by
      refine abs_lt_of_sq_lt_sq ?_ (by norm_num)
      nlinarith only [h1, hx]
    rw [abs_lt] at h2
    simp only [zpow_zero, mul_one]
    exact h2
  have hl3 := b2c_one_lt_log3
  have h0 : (0 : Vec d) ∈ ((3 : ℝ) ^ 3) • Section6.euclidBall (d := d) (1 / 2) :=
    ⟨0, Section6.zero_mem_euclidBall (by norm_num), smul_zero _⟩
  refine ⟨Section6.euclidBall (d := d) (1 / 2), 2, 3, 1, (3 : ℝ) ^ 3, hU, hUc, zero_le_one,
    by norm_num, ?_, le_rfl, h0, ?_⟩
  · push_cast
    linarith only [hl3]
  · set S := shiftCube (0 : Vec d) ((3 : ℕ) : ℤ) ∩ translateSet (-(0 : Vec d))
      (((3 : ℝ) ^ 3) • Section6.euclidBall (d := d) (1 / 2)) with hS
    refine ⟨(0 : H10Function S).toH1Function, ?_, ?_⟩
    · intro φ
      have h0 : ∀ x, (0 : H10Function S).toH1Function.grad x = 0 := fun _ => rfl
      simp [vecDot, matVecMul, h0]
    · have := localizedZeroTraceFunctionOn_of_h10_any (V := shiftCube (0 : Vec d) ((3 : ℕ) : ℤ))
        (0 : H10Function S)
      simpa using this

end SuperdiffusionCLT.Section7
