/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryB
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryOriginB
public import SuperdiffusionCLT.Section7.Lipschitz.Frame
public import SuperdiffusionCLT.Section7.Lipschitz.SigmaWindow
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlargeB
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputsB
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# The boundary Lipschitz estimate on the fine grid

The display `e.Dir.new.C01.boundary` for centres `z` of the grid `3^{n - s} ℤ^d`, with the
oscillation about the mean on the left and, on a cube that meets the frontier, the flatness
relative to the datum `g`.  One random scale `X` serves every centre of the grid: the estimate in
the frame of the centre (`lip_boundary_origin`) holds almost surely at every lattice point, the
scale of the translated samples is controlled on the grid by `b2_gridMax_scale` and enlarged
logarithmically (`b2c_enl`), with the exponent `B + s` accounting for the `3^{sd}` times finer grid.
The estimate at the scale `m'` is moved to the scale `m` through the window of `σ̄`
(`lip_sigma_window`) and the datum exponent `E + 1`.
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

/-- **The boundary large-scale Lipschitz estimate on the fine grid** (`e.Dir.new.C01.boundary`,
with the oscillation on the left and the flatness relative
to `g` on a cube that meets the frontier). -/
theorem lip_boundary_fine (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
      ∀ (A s : ℕ) (B E : ℝ), 0 ≤ B → 0 ≤ E →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ m n m' : ℕ, n < m' → m' ≤ m → m ≤ m' + A →
          (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) → Lhat ≤ (n : ℝ) → X omega ≤ (3 : ℝ) ^ n →
          ∀ t : ℝ, (3 : ℝ) ^ m' ≤ t → t ≤ (3 : ℝ) ^ m →
          ∀ z ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2)), z ∈ t • U →
          ∀ (f g : Vec d → ℝ), ContDiff ℝ 2 g →
          ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ t • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
              (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
              (shiftCube z (m' : ℤ)) (fun x => u.toFun x - g x) →
            ∀ R : ℝ≥0∞,
              R = ENNReal.ofReal (C * (3 : ℝ) ^ (-(m' : ℝ))) *
                  (lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) +
                    lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x)) +
                ENNReal.ofReal (C * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m') *
                  eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) +
                ENNReal.ofReal (C * ((m' : ℝ) - (n : ℝ))) *
                  eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
                ENNReal.ofReal (C * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                  eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
                    (volume.restrict (shiftCube z (m' : ℤ))) →
            -- e.Dir.new.C01.boundary, with the oscillation kept on the left
            ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) ≤ R ∧
              -- on a cube that meets the boundary, the solution itself is flat relative to `g`
              (¬ shiftCube z (n : ℤ) ⊆ t • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R) := by
  intro U hU hU0
  obtain ⟨r, M₁, M₂, D, hUu⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  obtain ⟨C0, hC0, H0⟩ := lip_boundary_origin d hd hInputs hS5 hCB U hU hU0
  refine ⟨4 * C0, by linarith only [hC0], ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A s B E hB hE
  obtain ⟨Lh0, hLh0, H1⟩ := H0 nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 B (E + 1) hB
    (by linarith only [hE])
  obtain ⟨Ls, hLs⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar K
  have hN : (0 : ℝ) ≤ B + s := by positivity
  obtain ⟨Cg, hCg1, hG⟩ := b2_gridMax_scale d hN hρ (A + 2)
  have hC1 := b2c_C1_nonneg (B + s) hN (A + 2)
  have h3 := b2c_one_lt_log3
  have hlogL : 0 ≤ Real.log Lh0 := Real.log_nonneg hLh0
  have hpow : 1 ≤ (1 + Real.log Lh0) ^ ρ⁻¹ :=
    Real.one_le_rpow (by linarith only [hlogL]) (inv_nonneg.2 hρ.le)
  obtain ⟨Lam, hLamDef⟩ : ∃ Lam : ℝ, Lam = max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹)
      (Real.exp ((A + 2 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hLam0 : Lh0 ≤ Lam := by
    rw [hLamDef]
    refine le_trans ?_ (le_max_left _ _)
    calc Lh0 = 1 * Lh0 * 1 := by ring
      _ ≤ Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹ := by
        have hL0 : 0 ≤ Lh0 := by linarith only [hLh0]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hCg1 hL0) hpow zero_le_one (by positivity)
  have hLam1 : 1 ≤ Lam := by linarith only [hLam0, hLh0]
  have hκ : 0 ≤ B + (s : ℝ) + 1 := by linarith only [hN]
  have ha : 0 ≤ 1 + 4 * (B + (s : ℝ) + 1) * Real.log 3 := by
    have : 0 ≤ Real.log 3 := by linarith only [h3]
    positivity
  have hB0 : 0 ≤ (b2c_C1 (B + s) (A + 2) + 3 * (B + (s : ℝ) + 1) + (b2c_n0 (B + s) : ℝ)) *
      Real.log 3 := by
    have : 0 ≤ Real.log 3 := by linarith only [h3]
    have : (0 : ℝ) ≤ b2c_n0 (B + s) := Nat.cast_nonneg _
    positivity
  have ha1 : 1 ≤ 1 + 4 * (B + (s : ℝ) + 1) * Real.log 3 := by
    have : 0 ≤ Real.log 3 := by linarith only [h3]
    have : 0 ≤ 4 * (B + (s : ℝ) + 1) * Real.log 3 := by positivity
    linarith only [this]
  obtain ⟨Lsc, hLscDef⟩ : ∃ Lsc : ℝ, Lsc = (1 + 4 * (B + (s : ℝ) + 1) * Real.log 3) * Lam +
      (b2c_C1 (B + s) (A + 2) + 3 * (B + (s : ℝ) + 1) + (b2c_n0 (B + s) : ℝ)) * Real.log 3 :=
    ⟨_, rfl⟩
  have hLsc : Lam ≤ Lsc := by rw [hLscDef]; nlinarith only [ha1, hB0, hLam1]
  have h4E : 0 < (4 : ℝ) ^ (E + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hLs0 : (0 : ℝ) ≤ Ls := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  refine ⟨Lsc + Ls + A + (4 : ℝ) ^ (E + 1) + (16 * B ^ 2 + 1),
    by nlinarith only [hLsc, hLam1, hLs0, hA0, h4E, sq_nonneg B], ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX01, hX0O, hX0P⟩ := H1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xs, hXs, hXs1, hXsO, hXsae⟩ := hG P hPrefix hJ2 X0 hX0m Lh0 hLh0 hX0O
  have hLs' := hLs P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun omega => b2c_enl (B + s + 1) (b2c_C1 (B + s) (A + 2)) (b2c_n0 (B + s)) (Xs omega),
    b2c_enl_measurable hXs _ _ _, fun omega => b2c_enl_ge_one _ _ _ _, ?_, ?_⟩
  · have := b2c_enl_isBigO (μ := P.toMeasure) (κ := B + s + 1) (C := b2c_C1 (B + s) (A + 2))
      hκ hC1 (b2c_n0 (B + s)) hXs1 hXsO
    rw [← hLamDef] at this
    refine this.mono_scale ?_
    rw [← hLscDef] at *
    linarith only [hLs0, hA0, h4E, sq_nonneg B]
  · have hlat := b2_ae_forall_lattice d hX0P
    filter_upwards [hlat, hXsae, lip_frame d hJ3 hnu] with ω hlatω hsω hfr
    intro m n m' hnm' hm'm hmA hwin hLn hX t htm' htm z hz hzt f g hg u hu hzero R hR
    have hpos1 : (0 : ℝ) < 1 := one_pos
    have hn : (n : ℝ) < m' := by exact_mod_cast hnm'
    have hLsc0 : 0 ≤ Lsc := by linarith only [hLsc, hLam1]
    have hLn' : Lsc + Ls + A + (4 : ℝ) ^ (E + 1) + (16 * B ^ 2 + 1) ≤ (m' : ℝ) :=
      le_trans hLn hn.le
    have hLam_m : Lam ≤ (m' : ℝ) := by
      nlinarith only [hLn', hLsc, hLs0, hA0, h4E, sq_nonneg B]
    have hLh0_n : Lh0 ≤ (n : ℝ) := by
      have : Lam ≤ (n : ℝ) := by nlinarith only [hLn, hLsc, hLs0, hA0, h4E, sq_nonneg B]
      linarith only [hLam0, this]
    have hLs_m : (Ls : ℝ) ≤ m' := by nlinarith only [hLn', hLsc0, hLs0, hA0, h4E, sq_nonneg B]
    have hA_m : (A : ℝ) ≤ m' := by nlinarith only [hLn', hLsc0, hLs0, hA0, h4E, sq_nonneg B]
    have hE4_m : (4 : ℝ) ^ (E + 1) ≤ (m' : ℝ) := by
      nlinarith only [hLn', hLsc0, hLs0, hA0, h4E, sq_nonneg B]
    have hB_m : 16 * B ^ 2 + 1 ≤ (m' : ℝ) := by
      nlinarith only [hLn', hLsc0, hLs0, hA0, h4E, sq_nonneg B]
    have hmA' : m ≤ 2 * m' := by
      have : A ≤ m' := by exact_mod_cast hA_m
      omega
    obtain ⟨hn0m', hXsn⟩ := b2c_enl_spec_succ hN (A + 2) hnm' hX
    have hgrid := hsω m' (by rw [← hLamDef]; exact hLam_m) hXsn
    have hnKle := lip_fine_nK_le hB s hn0m' hwin
    have hzgrid : z ∈ gridPts d ((nK (B + s) m' : ℤ) - 3) ((3 : ℝ) ^ (m' + (A + 2))) := by
      refine b2_gridPts_mono (j := (n : ℤ) - s) ?_ (by positivity) ?_ hz
      · have : ((nK (B + s) m' : ℕ) : ℤ) ≤ (n : ℤ) - s := by exact_mod_cast hnKle
        omega
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hnKn : nK (B + s) m' ≤ n := by
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have : (nK (B + s) m' : ℝ) ≤ n := by linarith only [hnKle, hs0]
      exact_mod_cast this
    have hX0z : X0 (ShellField.translateSequence z ω) ≤ (3 : ℝ) ^ n :=
      le_trans (hgrid z hzgrid) (pow_le_pow_right₀ (by norm_num) hnKn)
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htm'
    have hUo : IsOpen (t • U) := (hUu.smul ht0).1
    have hzlat : z ∈ b2_latticePts d := b2_gridPts_subset_lattice (by positivity) hz
    have hO := hlatω z hzlat n m' hnm' hwin hLh0_n hX0z t htm' hzt
    obtain ⟨-, -, hσ1, hσ2⟩ := hLs' m' m (by exact_mod_cast hLs_m) hm'm hmA'
    have hσ' := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos (nu := nu) (m := m')
      hnu hPrefix hJ2 hJ3 hJ4 (P := P)
    have hσ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos (nu := nu) (m := m)
      hnu hPrefix hJ2 hJ3 hJ4 (P := P)
    have hnE := lip_fine_numeric hB hE hm'm hmA (by exact_mod_cast hA_m) hB_m hE4_m hwin
    exact lip_fine_main (a := Section6.fullCoefficientRecentered nu ω)
      (a' := Section6.fullCoefficientRecentered nu (ShellField.translateSequence z ω)) hC0 rfl hσ hσ'
      hσ1 hσ2 hnm' hm'm hnE hUo hzt
      (fun f u hu => hfr z _ ((lip_bdry_approx_isOpen_cube z m').inter hUo)
        (by
          rw [lip_bdry_approx_shiftCube_eq_ball]
          exact Metric.isBounded_ball.subset Set.inter_subset_left) f u hu)
      hO f g hg u hu hzero R hR

/-- Witness for the geometric and numerical hypotheses of `lip_boundary_fine`: the Euclidean ball
of radius `1/2` is a smooth domain inside the unit cube, the scales `n = 2 < m' = m = 3` (with
`A = 0`, `s = 1`, `B = 1`) satisfy the window, the centre `0` lies on the grid and in the dilate
`3^{m'} • U`, and the zero function is a weak solution with zero right-hand side and vanishing
localized trace for the datum `g = 0`. -/
example [NeZero d] (a : CoeffField d) :
    ∃ (U : Set (Vec d)) (A s n m' m : ℕ) (B t : ℝ), IsSmoothBoundedDomain U ∧
      U ⊆ openCubeSet (originCube d 0) ∧ 0 ≤ B ∧ n < m' ∧ m' ≤ m ∧ m ≤ m' + A ∧
      (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ) ∧ (3 : ℝ) ^ m' ≤ t ∧ t ≤ (3 : ℝ) ^ m ∧
      (0 : Vec d) ∈ gridPts d ((n : ℤ) - s) ((3 : ℝ) ^ (m + 2)) ∧ (0 : Vec d) ∈ t • U ∧
      ∃ u : H1Function (shiftCube (0 : Vec d) (m' : ℤ) ∩ t • U),
        IsWeakSolutionOn a (shiftCube (0 : Vec d) (m' : ℤ) ∩ t • U) u 0 (fun _ => 0) ∧
        LocalizedZeroTraceFunctionOn (shiftCube (0 : Vec d) (m' : ℤ) ∩ t • U)
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
  refine ⟨Section6.euclidBall (d := d) (1 / 2), 0, 1, 2, 3, 3, 1, (3 : ℝ) ^ 3, hU, hUc,
    zero_le_one, by norm_num, le_rfl, le_rfl, ?_, le_rfl, le_rfl,
    rc_zero_mem_gridPts _ (by positivity), h0, ?_⟩
  · push_cast
    linarith only [hl3]
  · set S := shiftCube (0 : Vec d) ((3 : ℕ) : ℤ) ∩
      (((3 : ℝ) ^ 3) • Section6.euclidBall (d := d) (1 / 2)) with hS
    refine ⟨(0 : H10Function S).toH1Function, ?_, ?_⟩
    · intro φ
      have h0 : ∀ x, (0 : H10Function S).toH1Function.grad x = 0 := fun _ => rfl
      simp [vecDot, matVecMul, h0]
    · have := localizedZeroTraceFunctionOn_of_h10_any (V := shiftCube (0 : Vec d) ((3 : ℕ) : ℤ))
        (0 : H10Function S)
      simpa using this

end SuperdiffusionCLT.Section7
