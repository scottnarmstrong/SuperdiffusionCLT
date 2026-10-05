/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.SmoothC
public import SuperdiffusionCLT.Section7.Linfty.PropC

/-!
# The `L^∞` homogenization proposition `p.Dirichlet.Linfty.blackbox`

`linf_prop`: the text of the binder `hLinf` of `s5_superdiffusivity`, from the
inputs `hInputs`, `hS5` and the boundary Lipschitz estimate `hLipB` on a fine grid of
centres. The proposition for a smooth datum (`linf_smooth_large`) is the one of `linf_smooth` with
the constant `C` at least any given `C₀`; `linf_prop_of_smooth` removes the smoothness of the datum.
-/

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

private theorem linf_pe_nat_a (k : ℕ) : k ≤ 2 * k := by omega

private theorem linf_pe_nat_b {m k : ℕ} (h : m + 5 ≤ k) : m + 1 ≤ k := by omega

private theorem linf_pe_nat_c {m j k : ℕ} (h : j ≤ m + 3) (hm : m + 5 ≤ k) : j < k - 1 := by
  omega

private theorem linf_pe_Cp_nonneg {Kp Cin cθ cΛ : ℝ} (hKp : 0 ≤ Kp) (hCin : 0 ≤ Cin)
    (hcθ : 0 ≤ cθ) : 0 ≤ linfCp Kp Cin cθ cΛ := by
  unfold linfCp; positivity

/-- **The smooth-datum proposition with a constant as large as needed**: the proposition for a
smooth datum of `linf_smooth`, with the constant `C` of the statement at least any given `C₀`
(the proof takes `C` as a maximum of thresholds, to which `C₀` is added). -/
theorem linf_smooth_large (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    (hLipB :
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
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R)) :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ kc2_Q0 d → ∀ C₀ : ℝ,
    ∃ C : ℝ, C₀ ≤ C ∧ 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ (n : ℕ) (R : ℝ), C ≤ (n : ℝ) → Lhat ≤ (nK C n : ℝ) →
          X0 omega ≤ (3 : ℝ) ^ nK C n → (3 : ℝ) ^ n < 3 * R → R ≤ (3 : ℝ) ^ n →
          ∀ (f gt : Vec d → ℝ) (F G : ℝ), ContDiff ℝ (⊤ : ℕ∞) gt → 0 ≤ F → 0 ≤ G →
            AEStronglyMeasurable f (volume.restrict (R • U)) →
            (∀ᵐ x ∂volume.restrict (R • U), |f x| ≤ F) → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
            (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ G / (3 : ℝ) ^ nK C n) →
          ∀ v vh : H1Function (R • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (R • U) v f
              (fun _ => 0) →
            MemH10 (R • U) (fun x => v.toFun x - gt x) →
            IsWeakSolutionOn (fun _ => sigmaBarInfinite nu n P • (1 : Mat d)) (R • U) vh f
              (fun _ => 0) →
            MemH10 (R • U) (fun x => vh.toFun x - gt x) →
            eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict (R • U)) +
                hMinusOneVec (R • U) (fun x => v.grad x - vh.grad x) +
                hMinusOneVec (R • U) (fun x =>
                  matVecMul ((sigmaBarInfinite nu n P)⁻¹ •
                    (Section6.fullCoefficientRecentered nu omega x -
                      volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                        (Section6.fullStreamRecentered omega))) (v.grad x) - vh.grad x) ≤
              ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) *
                ((sigmaBarInfinite nu n P)⁻¹ * (3 : ℝ) ^ (2 * n) * F +
                  Real.log (n : ℝ) * (3 : ℝ) ^ n * G)) := by

  intro U hU hUQ C₀
  have hU0 : U ⊆ openCubeSet (originCube d 0) := linf_smooth_hU0 hU.1 hUQ
  obtain ⟨s0, B₀, Cd, Cloc, CH, cθ, hB₀, hCd, hCloc, hCH, hcθ, Hs⟩ :=
    linf_smooth_sample hd hU hU0
  obtain ⟨Cin, hCin, Hin⟩ := l2b_ae_cell d hd hInputs
  obtain ⟨Cf, hCf, Hf⟩ := linf_field d hd hInputs
  obtain ⟨Cl, hCl, Hlip⟩ := hLipB U hU hU0
  have hp1 := linf_smooth_one_le_power hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set p : ℝ := deGiorgiPower d with hp
  set A₀ : ℝ := 6 * p + 20 with hA₀
  obtain ⟨N, hN1, HN⟩ := linf_scale_choice A₀ 2 (1 / (2 * (d : ℝ)))
    (by rw [hA₀]; linarith only [hp1]) (by norm_num) (by positivity)
  have hN0 : 0 ≤ N := by linarith only [hN1]
  have hKp0 : 0 ≤ l2e_Kp d := by
    have hB : 0 ≤ l2e_bumpB d := (abs_nonneg _).trans (l2e_bump_bound d 0)
    unfold l2e_Kp
    positivity
  set Y₀ : ℝ := Cd * (l2e_Kp d * Cin + 1) * (Cloc * Cl * (CH + N + 7)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by
    have h1 : 0 ≤ Cin := by linarith only [hCin]
    have h2 : 0 ≤ Cl := by linarith only [hCl]
    exact mul_nonneg (mul_nonneg hCd (add_nonneg (mul_nonneg hKp0 h1) zero_le_one))
      (mul_nonneg (mul_nonneg hCloc h2) (add_nonneg (add_nonneg hCH hN0) (by norm_num)))
  set C₁ : ℝ := 2 * Cd * (l2e_Kp d * Cin + 1) * (Cloc * Cl * (CH + N + 7) + 1) with hC₁
  set C : ℝ := max (max C₁ (N + 1)) C₀ with hCdef
  have hC1 : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCN : N + 1 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := by linarith only [hCN, hN0]
  refine ⟨C, le_max_right _ _, by linarith only [hCN, hN1], ?_⟩
  intro nu hnu hnu1 cStar hcStar Kc ε ρ hε hε1 hρ hρ1
  set M : ℝ := max (max Cin Cf) N with hM
  have hCinM : Cin ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hCfM : Cf ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hNM : N ≤ M := le_max_right _ _
  obtain ⟨L1, hL1, H1⟩ := Hin nu hnu hnu1 cStar hcStar Kc ε ρ M hε hε1 hρ hρ1 hCinM
  obtain ⟨L2, hL2, H2⟩ := Hf nu hnu hnu1 cStar hcStar Kc ε ρ M hε hε1 hρ hρ1 hCfM
  obtain ⟨L3, hL3, H3⟩ := Hlip nu hnu hnu1 cStar hcStar Kc ε ρ hε hε1 hρ hρ1 1 s0 (2 * N)
    (2 * C) (mul_nonneg zero_le_two hN0) (mul_nonneg zero_le_two hC0)
  obtain ⟨Lσ, Hσ⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar Kc
  set cΛ : ℝ := (1 + Cf) ^ 2 with hcΛ
  set cq : ℝ := ((1 + Cf) ^ 2) ^ (p + 1) with hcq
  have hcq0 : 0 ≤ cq := Real.rpow_nonneg (by positivity) _
  set Cp : ℝ := linfCp (l2e_Kp d) Cin cθ cΛ with hCp
  have hCp0 : 0 ≤ Cp := by
    have : 0 ≤ Cin := by linarith only [hCin]
    exact linf_pe_Cp_nonneg hKp0 this hcθ
  obtain ⟨kδ, hkδ1, Hδ⟩ := linf_smooth_delta_small hρ1 (c := 1 / (2 * (Y₀ + 1)))
    (one_div_pos.2 (mul_pos two_pos (add_pos_of_nonneg_of_pos hY₀0 one_pos)))
  set cρ : ℝ := (3 * Real.log (2 : ℝ)) ^ ρ⁻¹ with hcρ
  have hcρ0 : 0 ≤ cρ := Real.rpow_nonneg
    (by have := Real.log_pos (one_lt_two : (1 : ℝ) < 2); positivity) _
  set L12 : ℝ := cρ * (L1 + L2) with hL12
  set Lsc : ℝ := cρ * (L12 + L3) with hLsc
  set Lhat : ℝ := max (max Lsc (max L1 (max L2 L3))) (max (max (Lσ : ℝ) (1 / nu))
    (max (max kδ (Cp * (cq + 1) / ε)) (max B₀ (max (4 * N ^ 2) 3)))) with hLhat
  have hall : Lsc ≤ Lhat ∧ L1 ≤ Lhat ∧ L2 ≤ Lhat ∧ L3 ≤ Lhat ∧ (Lσ : ℝ) ≤ Lhat ∧
      1 / nu ≤ Lhat ∧ kδ ≤ Lhat ∧ Cp * (cq + 1) / ε ≤ Lhat ∧ B₀ ≤ Lhat ∧ 4 * N ^ 2 ≤ Lhat ∧
      (3 : ℝ) ≤ Lhat := by
    simp only [hLhat, le_max_iff, le_refl, true_or, or_true, and_self]
  obtain ⟨hLsc, hLL1, hLL2, hLL3, hLσ, hLν, hLδ, hLε, hLB, hLN, hL3'⟩ := hall
  refine ⟨Lhat, by linarith only [hL3'], ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X1, hX1m, hX11, hX1O, hae1⟩ := H1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X2, hX2m, hX21, hX2O, hae2⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X3, hX3m, hX31, hX3O, hae3⟩ := H3 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hO12 := Section6.l9_log_max_bigO hρ (by linarith only [hL1]) (by linarith only [hL2])
    le_rfl hX21 hX1O hX2O
  have hO := Section6.l9_log_max_bigO hρ (by positivity) (by linarith only [hL3]) hLsc hX31
    hO12 hX3O
  refine ⟨fun ω => max (max (X1 ω) (X2 ω)) (X3 ω), (hX1m.max hX2m).max hX3m,
    fun ω => le_max_of_le_left (le_max_of_le_left (hX11 ω)), hO, ?_⟩
  filter_upwards [hae1, hae2, hae3, Section6.ae_centered_eq_recentered_add_skew hJ3 nu] with
    ω h1 h2 h3 hsk
  intro k R hCk hLk hXk hR1 hR2 f gt F G hgt hF hG hfm hfF hgtG hgt2G v vh hv hvmem hvh hvhmem
  -- the scale
  have hnCk : nK C k ≤ k := nK_le C k
  have hkL : Lhat ≤ (k : ℝ) := hLk.trans (by exact_mod_cast hnCk)
  have hk3 : (3 : ℝ) ≤ k := hL3'.trans hkL
  have hk3n : 3 ≤ k := by exact_mod_cast hk3
  have hk1 : (1 : ℝ) ≤ k := by linarith only [hk3]
  have hk0 : (0 : ℝ) < k := by linarith only [hk3]
  have hk1n : 1 ≤ k := Nat.le_trans (by norm_num) hk3n
  have hN3 : 1 ≤ N * Real.log 3 := by
    have := linf_smooth_one_le_log_three
    nlinarith only [this, hN1]
  obtain ⟨-, hck, -⟩ := l2e_ceil_facts (lt_of_lt_of_le one_pos hN1) hN3 hk3 (hLN.trans hkL)
  set m : ℕ := nK N k with hm
  have hnCm : nK C k ≤ m := by
    have := linf_scale_nK_le_sub hN0 0 (by simp only [Nat.cast_zero, add_zero]; exact hCN) hk3n
    simpa using this
  have hmB : B₀ * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ k :=
    linf_smooth_B0 hN1 hk3 (hLN.trans hkL) (hLB.trans hkL)
  have hm5 : m + 5 ≤ k := by
    have h1 : (3 : ℝ) ^ (m + 5) ≤ (3 : ℝ) ^ k := by
      have e : (3 : ℝ) ^ (m + 5) = 243 * (3 : ℝ) ^ m := by ring
      rw [e]
      have : 243 * (3 : ℝ) ^ m ≤ B₀ * (3 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hB₀ (by positivity)
      linarith only [this, hmB]
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
  have hX0m : max (max (X1 ω) (X2 ω)) (X3 ω) ≤ (3 : ℝ) ^ m :=
    hXk.trans (pow_le_pow_right₀ (by norm_num) hnCm)
  have hX1k : X1 ω ≤ (3 : ℝ) ^ k :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans
      (hX0m.trans (pow_le_pow_right₀ (by norm_num) ((Nat.le_add_right m 5).trans hm5)))
  have hX2k : X2 ω ≤ (3 : ℝ) ^ k :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans
      (hX0m.trans (pow_le_pow_right₀ (by norm_num) ((Nat.le_add_right m 5).trans hm5)))
  have hX3m : X3 ω ≤ (3 : ℝ) ^ m := (le_max_right _ _).trans hX0m
  have hLm : Lhat ≤ (m : ℝ) := hLk.trans (by exact_mod_cast hnCm)
  -- the window of `σ̄`
  set σ : ℝ := sigmaBarInfinite nu k P with hσdef
  obtain ⟨hσ1, hσk, -, -⟩ := Hσ P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 k k
    (by exact_mod_cast (hLσ.trans hkL)) le_rfl (linf_pe_nat_a k)
  -- the inputs at the sample
  have hR0 : 0 < R := by
    have : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    linarith only [hR1, this]
  have hWK := (linf_smooth_dom hU0 hR0 hR2).1
  obtain ⟨hid, hell⟩ := h2 k hX2k (hLL2.trans hkL)
  obtain ⟨K₀, hK₀s, hK₀⟩ := hsk k
  have hcellw := h1 k m hX1k (hLL1.trans hkL) (linf_smooth_inwin hN0 hNM hk1n hck)
    (linf_pe_nat_b hm5) (R • U) hWK
  have hηs : ∀ w : Vec d, (∃ i, 1 < |w i|) → li1_bump d w = 0 := (l2c_mollifier_witness d).2.2.2
  -- the numerical thresholds
  have hkν : 1 ≤ (k : ℝ) * nu := by
    have h := hLν.trans hkL
    rw [div_le_iff₀ hnu] at h
    exact h
  have hδb := l2e_delta_bounds hk3 hε hε1 hρ hρ1
  have hδ0 : 0 ≤ deltaScale ε ρ k := le_trans (by positivity) hδb.1
  obtain ⟨hΛ1, hΛ2, hΛ3⟩ := linf_smooth_Lambda (k := (k : ℝ)) (ρ := ρ) (Cf := Cf) (p := p) hk1
    hnu hkν hnu1 hρ1.le (by linarith only [hCf]) (by linarith only [hp1])
  have hsc : (k : ℝ) ^ A₀ * ((3 : ℝ) ^ m / (3 : ℝ) ^ k) ^ (1 / (2 * (d : ℝ))) ≤
      (k : ℝ) ^ (-2 : ℝ) := by
    rw [linf_smooth_ratio hck]
    have h := HN k hk3n 1 1 one_pos (by rw [inv_le_one₀ hk0]; exact hk1) one_pos hk1
    simp only [Real.one_rpow, mul_one] at h
    exact h
  have hϖ := linf_smooth_varpi (k := (k : ℝ)) (ε := ε) (ρ := ρ) (Cp := Cp) (cq := cq)
    (aq := 6 * (p + 1)) (A₀ := A₀) hk3 hε hε1 hρ hρ1 hCp0 hcq0 (by linarith only [hp1])
    (by rw [hA₀]; linarith only [hp1]) (Real.rpow_nonneg (by positivity) _) hsc
    (hLε.trans hkL)
  have hsmall : Y₀ * deltaScale ε ρ k ≤ 1 / 2 := by
    have hδs := Hδ k ε (hLδ.trans hkL) hε hε1
    calc Y₀ * deltaScale ε ρ k ≤ Y₀ * (1 / (2 * (Y₀ + 1))) :=
          mul_le_mul_of_nonneg_left hδs hY₀0
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (mul_pos two_pos (add_pos_of_nonneg_of_pos hY₀0 one_pos))
            (by norm_num)]
          linarith only [hY₀0]
  have h3k1R : (3 : ℝ) ^ (k - 1) ≤ R := by
    have e : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; exact (Nat.sub_add_cancel hk1n).symm
    linarith only [hR1, e]
  have hD0 : 0 ≤ σ⁻¹ * (3 : ℝ) ^ (2 * k) * F + Real.log (k : ℝ) * (3 : ℝ) ^ k * G := by
    have hlg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
    have hσ0 : 0 ≤ σ := by linarith only [hσ1]
    exact add_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hσ0) (pow_nonneg (by norm_num) _)) hF)
      (mul_nonneg (mul_nonneg hlg (pow_nonneg (by norm_num) _)) hG)
  refine (Hs (Section6.fullCoefficientRecentered nu ω)
    (fun x => nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField ω
        (cubeSet (originCube d (k : ℤ))) x) K₀
    (volumeAverageMat (cubeSet (originCube d (k : ℤ))) (Section6.fullStreamRecentered ω))
    nu σ ((nu + Cf * (k : ℝ) ^ (1 + ρ)) ^ 2 / nu) cΛ (cq * (k : ℝ) ^ (6 * (p + 1))) Cin Cl N
    (2 * C) (deltaScale ε ρ k) ρ k m (nK C k) R hnu hnu1 hkν hσ1 hσk hk3 hδ0 hδb.2 hρ1.le hCin
    hCl hN0 (by positivity) hΛ1 hΛ2 hΛ3 hmB (linf_smooth_window hN0 hk3n)
    (linf_smooth_Epow hC0 hk1n) hϖ hsmall hR1 hR2 hK₀s (fun x => hK₀ x) (fun x => hid x)
    hell ?_ f gt F G hgt hF hG hfm hfF hgtG hgt2G ?_ v vh hv hvmem hvh hvhmem).trans ?_
  · intro u f' hfm' hsol kk hcs x hx
    obtain ⟨b1, b3⟩ := hcellw u f' hfm' hsol (li1_bump d) (l2e_bumpB d) (l2e_bumpL d)
      (l2e_bump_bound d) (l2e_bump_lipschitz d) hηs kk hcs x hx
    simp only [zpow_natCast] at b1 b3
    rw [← hσdef] at b1 b3
    constructor
    · refine b1.trans (le_of_eq ?_)
      simp only [l2e_b, l2e_aC, deltaScale, l2e_Kp, pow_succ]
      ring_nf
    · refine b3.trans (le_of_eq ?_)
      simp only [l2e_b, l2e_aC, l2e_e, l2e_g, deltaScale, l2e_Kp, pow_succ]
      ring_nf
  · intro j hj1 hj2 z hz hzU u hu hloc Rr hRr
    exact h3 k j (k - 1) (linf_pe_nat_c hj2 hm5) (Nat.sub_le k 1)
      (Nat.sub_add_cancel hk1n).symm.le (linf_smooth_lipwin hN0 hk3n hj1)
      (hLL3.trans (hLm.trans (by exact_mod_cast hj1)))
      (hX3m.trans (pow_le_pow_right₀ (by norm_num) hj1)) R h3k1R hR2 z hz hzU f gt
      (hgt.of_le (by simp)) u hu hloc Rr hRr
  · refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hδ0) hD0

/-- **`p.Dirichlet.Linfty.blackbox`**: the text of the binder `hLinf` of
`s5_superdiffusivity`, from `hInputs`, `hS5` and the boundary Lipschitz estimate `hLipB`. -/
theorem linf_prop (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    (hLipB :
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
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R))
    :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ kc2_Q0 d →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
        ∃ Lhat : ℝ, 1 ≤ Lhat ∧
          ∀ (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
            (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
            (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
            (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
            ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma ρ)
                (fun omega => Real.log (X0 omega)) Lhat ∧
              ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                ∀ (n : ℕ) (R : ℝ), C ≤ (n : ℝ) →
                  Lhat ≤ (((n : ℤ) - ⌈C * Real.log (n : ℝ)⌉ : ℤ) : ℝ) →
                  X0 omega ≤ (3 : ℝ) ^ ((n : ℤ) - ⌈C * Real.log (n : ℝ)⌉) →
                  (3 : ℝ) ^ n < 3 * R → R ≤ (3 : ℝ) ^ n →
                  ∀ W : Set (Vec d), W = R • U →
                  ∀ (f : Vec d → ℝ) (g u uhom : H1Function W),
                    IsDirichletSolution
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) W f g u →
                    IsDirichletSolution
                      (fun _ => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P •
                        (1 : Mat d)) W f g uhom →
                      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict W) +
                        hMinusOneVec W (fun x => u.grad x - uhom.grad x) +
                        hMinusOneVec W (fun x =>
                          matVecMul ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ •
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega x -
                              volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Section6.fullStreamRecentered omega)))
                            (u.grad x) - uhom.grad x) ≤
                      ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) *
                          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ *
                            (3 : ℝ) ^ (2 * n))) *
                        eLpNorm f ⊤ (volume.restrict W) +
                      ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) * Real.log (n : ℝ) *
                          (3 : ℝ) ^ n) *
                        eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict W) :=
  linf_prop_of_smooth d hd hInputs hS5 (linf_smooth_large d hd hInputs hS5 hLipB)

end SuperdiffusionCLT.Section7
