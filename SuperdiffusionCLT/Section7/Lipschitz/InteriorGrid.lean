/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Interior
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlargeB
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputsB

/-!
# The interior Lipschitz estimate on the grid of translates

One random scale serves every centre of the grid `3^{n_N(n) - 3} ℤ^d ∩ {‖y‖_∞ ≤ 3^{n+A}}`: the
interior estimate centred at `y` (`lip_interior`) with the scale of the translated samples
controlled on the grid (`b2_gridMax_scale`) and enlarged logarithmically (`b2c_enl`) so that the
same `N` serves in the threshold and in the grid.
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

/-- **The interior estimate on the grid of translates**: one random scale `X` serves
every centre of the grid `3^{nK N n - 3} ℤ^d` with `|y|_∞ ≤ 3^{n + A}`, in the shape of the
hypotheses of `Frozen.Section7.interior_pointwise` (same `N` in the threshold and in the grid). -/
theorem lip_interior_grid (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    (hL2 :
        ∀ (r' M₁' M₂' D' : ℝ) (A : ℕ),
            ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
              ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
                (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
                ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
                ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ,
                  X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ k → Lhat ≤ (k : ℝ) →
                  ∀ V : Set (Vec d), V ⊆ Section6.engCube d k →
                    IsUniformC11Domain (((3 : ℝ) ^ k)⁻¹ • V) r' M₁' M₂' D' →
                    LipL2Block
                      (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
                      (sigmaBarInfinite nu k P) (deltaScale ε ρ (k : ℝ)) C A k V )
    (hCA :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
              ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
                (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
                ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
                ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ,
                  X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ k → Lhat ≤ (k : ℝ) →
                  LipCaccInt
                    (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
                    (sigmaBarInfinite nu k P) C 1 k) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∀ (A : ℕ) (N : ℝ), 0 ≤ N →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ n : ℕ, Lhat ≤ (nK N n : ℝ) → X omega ≤ (3 : ℝ) ^ nK N n →
          ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
          ∀ m l : ℕ, nK N n ≤ l → l < m →
            ((m : ℝ) - (l : ℝ)) * deltaScale ε ρ (m : ℝ) ≤ c →
            ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
              IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
                (shiftCube y (m : ℤ)) u f (fun _ => 0) →
              ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
                    lpBar (shiftCube y (l : ℤ)) 2 (fun x => eucNorm (u.grad x)) +
                  ENNReal.ofReal ((3 : ℝ) ^ (-(l : ℝ))) *
                    lpBar (shiftCube y (l : ℤ)) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube y (l : ℤ), u.toFun w) ≤
                ENNReal.ofReal (C * (3 : ℝ) ^ (-(m : ℝ))) *
                    lpBar (shiftCube y (m : ℤ)) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube y (m : ℤ), u.toFun w) +
                  ENNReal.ofReal (C * (sigmaBarInfinite nu m P)⁻¹ * (3 : ℝ) ^ m) *
                    eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ))) := by
  obtain ⟨C, c, hC, hc, hmain⟩ := lip_interior d hd hInputs hS5 hL2 hCA
  refine ⟨C, c, hC, hc, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A N hN
  obtain ⟨Lh0, hLh0, hP⟩ := hmain nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨Cg, hCg, hG⟩ := b2_gridMax_scale d hN hρ A
  have hC1 := b2c_C1_nonneg N hN A
  have h3 := b2c_one_lt_log3
  have hlogL : 0 ≤ Real.log Lh0 := Real.log_nonneg hLh0
  have hpow : 1 ≤ (1 + Real.log Lh0) ^ ρ⁻¹ :=
    Real.one_le_rpow (by linarith only [hlogL]) (inv_nonneg.2 hρ.le)
  have hLam1 : Lh0 ≤ max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹) (Real.exp (A : ℝ)) := by
    refine le_trans ?_ (le_max_left _ _)
    calc Lh0 = 1 * Lh0 * 1 := by ring
      _ ≤ Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹ := by
        gcongr
  have hexp : 1 ≤ Real.exp (A : ℝ) := Real.one_le_exp (Nat.cast_nonneg A)
  have hB : 0 ≤ (b2c_C1 N A + 3 * 1 + (b2c_n0 N : ℝ)) * Real.log 3 :=
    mul_nonneg (by linarith only [hC1, (Nat.cast_nonneg (b2c_n0 N) : (0 : ℝ) ≤ _)])
      (by linarith only [h3])
  have ha : 1 ≤ 1 + 4 * (1 : ℝ) * Real.log 3 := by linarith only [h3]
  set Lam : ℝ := max (Cg * Lh0 * (1 + Real.log Lh0) ^ ρ⁻¹) (Real.exp (A : ℝ)) with hLam
  have hLam1' : 1 ≤ Lam := le_trans hexp (le_max_right _ _)
  have hLhat : Lam ≤ (1 + 4 * (1 : ℝ) * Real.log 3) * Lam +
      (b2c_C1 N A + 3 * 1 + (b2c_n0 N : ℝ)) * Real.log 3 := by
    nlinarith only [ha, hB, hLam1']
  refine ⟨(1 + 4 * (1 : ℝ) * Real.log 3) * Lam +
    (b2c_C1 N A + 3 * 1 + (b2c_n0 N : ℝ)) * Real.log 3, le_trans hLam1' hLhat, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX01, hX0O, hX0P⟩ := hP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xs, hXs, hXs1, hXsO, hXsae⟩ := hG P hPrefix hJ2 X0 hX0m Lh0 hLh0 hX0O
  refine ⟨fun omega => b2c_enl 1 (b2c_C1 N A) (b2c_n0 N) (Xs omega),
    b2c_enl_measurable hXs _ _ _, fun omega => b2c_enl_ge_one _ _ _ _, ?_, ?_⟩
  · exact b2c_enl_isBigO (μ := P.toMeasure) (κ := 1) (C := b2c_C1 N A) zero_le_one hC1
      (b2c_n0 N) hXs1 hXsO
  · have hlat := b2_ae_forall_lattice d hX0P
    filter_upwards [hlat, hXsae] with omega hlatω hsω
    intro n hLn hXn y hy m l hnl hlm hwin f u hu
    obtain ⟨-, hXsn⟩ := b2c_enl_spec hN A n hXn
    have hnK : (nK N n : ℝ) ≤ n := by exact_mod_cast nK_le N n
    have hLamn : Lam ≤ (n : ℝ) := le_trans (le_trans hLhat hLn) hnK
    have hgrid := hsω n hLamn hXsn y hy
    have hlK : (nK N n : ℝ) ≤ l := by exact_mod_cast hnl
    have hLhl : Lh0 ≤ (l : ℝ) := le_trans hLam1 (le_trans hLhat (le_trans hLn hlK))
    have hX3 : X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ l :=
      le_trans hgrid (pow_le_pow_right₀ (by norm_num) hnl)
    have hyl : y ∈ b2_latticePts d :=
      b2_gridPts_subset_lattice (by positivity) hy
    exact hlatω y hyl m l hlm hwin hLhl hX3 f u hu

/-- Witness: the grid is non-empty, it contains the centre `0`. -/
example [NeZero d] (N : ℝ) (n A : ℕ) :
    (0 : Vec d) ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)) :=
  rc_zero_mem_gridPts _ (by positivity)

end SuperdiffusionCLT.Section7
