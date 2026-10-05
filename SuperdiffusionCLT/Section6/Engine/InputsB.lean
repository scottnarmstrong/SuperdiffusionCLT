/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import SuperdiffusionCLT.Section6.Prereq.SigmaBarWindow
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.Book.Ch03.Definitions
public import SuperdiffusionCLT.Section6.Engine.Inputs

/-!
# One-block inputs of the engine, almost surely

The sharp-scale inputs, taken as a hypothesis, give the gradient-free harmonic
approximation, Caccioppoli, Poincaré and the corrected affines on one almost-sure event.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- **The one-block inputs, almost surely**: the sharp-scale inputs at
`ε = 1` and `M = C` give, for the recentered full field and every scale above the minimal scale,
the gradient-free harmonic approximation on a block of `Hb` scales, Caccioppoli, Poincaré, and a
linear family of corrected affines. `L̂` and `X₀` do not depend on the block length `Hb`; only
the deterministic threshold `m1 Hb` does. -/
theorem eng_inputs (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
                              ENNReal.ofReal ((m : ℝ) ^ ρ)) :
    ∃ Cin : ℝ, 1 ≤ Cin ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ (Lhat : ℝ) (m1 : ℕ → ℕ), 1 ≤ Lhat ∧
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
                      GrowthElliptic (fullCoefficientRecentered nu omega) ∧
                      (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n)
                        (fullCoefficientRecentered nu omega)) ∧
                      ∀ Hb j : ℕ, X0 omega ≤ (3 : ℝ) ^ j → Lhat ≤ (j : ℝ) → m1 Hb ≤ j →
                        -- hHA at top scale `j`
                        (∀ t : ℕ, t ≤ j → j + 2 ≤ t + Hb →
                          ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
                            IsSolOn (fullCoefficientRecentered nu omega) (engCube d t) u g →
                            ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
                              IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
                                cubeL2 (t - 3) (fun x => u x - w x) ≤
                                  Cin * ((j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ)) *
                                    (3 : ℝ) ^ t * cubeFlat t u) ∧
                        -- hHC and hHP at scale `j`
                        (∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
                          IsSolOn (fullCoefficientRecentered nu omega) (engCube d j) u g →
                            cubeGradL2 (j - 2) g ≤
                                Cin * Real.sqrt
                                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu j P / nu) * cubeFlat j u ∧
                              Real.sqrt
                                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu j P / nu) * cubeFlat j u ≤
                                Cin * cubeGradL2 j g) ∧
                        -- the corrected affines of `□_j`
                        ∃ W : Vec d →ₗ[ℝ] (Vec d → ℝ), ∀ e : Vec d,
                          (∃ g : Vec d → Vec d,
                            IsSolOn (fullCoefficientRecentered nu omega) (engCube d j)
                              (W e) g) ∧
                            cubeFlat j (fun x => W e x - vecDot e x) ≤
                              Cin * ((j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ)) *
                                engNorm e := by
  obtain ⟨C₁, hC₁, hin⟩ := hInputs
  obtain ⟨Cc, hCc1, hCc⟩ := eng_cacc_cube d C₁ hC₁
  obtain ⟨Cp, hCp1, hCp⟩ := eng_poinc_cube d C₁ hC₁
  obtain ⟨Cr, hCr1, hCr⟩ := eng_corrector_cube d
  obtain ⟨Ch, hCh1, hCh⟩ := eng_harmonic_cube d C₁ hC₁
  refine ⟨max (max Cc Cp) (max Cr Ch), le_trans hCc1 (le_trans (le_max_left _ _)
    (le_max_left _ _)), ?_⟩
  have hcc : Cc ≤ max (max Cc Cp) (max Cr Ch) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hcp : Cp ≤ max (max Cc Cp) (max Cr Ch) := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcr : Cr ≤ max (max Cc Cp) (max Cr Ch) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hch : Ch ≤ max (max Cc Cp) (max Cr Ch) := le_trans (le_max_right _ _) (le_max_right _ _)
  generalize max (max Cc Cp) (max Cr Ch) = Cin at hcc hcp hcr hch ⊢
  intro ρ hρ0 hρ1 nu hnu0 hnu1 cStar hcS K
  obtain ⟨Lhat, hL1, hP⟩ := hin nu hnu0 hnu1 cStar hcS K 1 ρ C₁ one_pos le_rfl hρ0 hρ1 le_rfl
  obtain ⟨L0, hL0⟩ := eng_sigma_growth d hd nu cStar K 1 hnu0 hnu1 hcS one_pos
  have hpar := fun Hb : ℕ => eng_params ((1 - ρ) / 2) 1 (by linarith only [hρ1]) one_pos Hb
  choose m0 hm03 hm0a _hm0b using hpar
  refine ⟨Lhat, fun Hb => max (max (Hb + 1) L0) (max (m0 Hb) ⌈Real.exp (Hb : ℝ)⌉₊), hL1, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX01, hX0O, hae⟩ := hP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hX0m, hX01, hX0O, ?_⟩
  filter_upwards [hae, eng_ae_field d hJ3 hnu0] with omega hω hF
  refine ⟨hF.1, hF.2.1, ?_⟩
  intro Hb j hXj hLj hm1
  have hHb : Hb + 1 ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm1
  have hL0j : L0 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm1
  have hm0j : m0 Hb ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm1
  have hexj : ⌈Real.exp (Hb : ℝ)⌉₊ ≤ j :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm1
  have hj3 : 3 ≤ j := le_trans (hm03 Hb) hm0j
  have hσ : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu j P :=
    (hL0 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 j j hL0j le_rfl).1
  have hδ0 : 0 ≤ (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ) := (hm0a Hb j hm0j).1
  have hδ1 : (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ) ≤ 1 := by
    have := (hm0a Hb j hm0j).2
    have hHb0 : (0 : ℝ) ≤ (Hb : ℝ) := Nat.cast_nonneg _
    nlinarith only [this, hδ0, hHb0]
  have hHbc : (Hb : ℤ) ≤ ⌈C₁ * Real.log (j : ℝ)⌉ := ea5_block_le_ceil hC₁ hexj
  have hell := fun n : ℕ => (hF.2.2 j n).1
  have hsym := fun x : Vec d => (hF.2.2 j 0).2.1 x
  have hsol := fun n : ℕ => (hF.2.2 j n).2.2
  have hwin : ∀ n : ℕ, (j : ℤ) - Hb ≤ n → n ≤ j →
      HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
          (MultiscaleExponent.finite 2) (ea5_field nu omega j)
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu j P • (1 : Mat d)) ≤
        (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ) ∧
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu j P)⁻¹ *
            LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
              (ea5_field nu omega j) +
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu j P *
            (lambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
              (ea5_field nu omega j))⁻¹ ≤ C₁ := by
    intro n hn1 hn2
    obtain ⟨hg, hr, -⟩ := (hω j n hXj hLj (by omega) hn2).1 0 (ea5_zero_shift_incl hn2)
    simp only [ea5_shift_eq, one_mul] at hg hr
    exact ⟨hg, hr⟩
  have hsymc : ∀ n : ℕ, ∀ x ∈ cubeSet (originCube d (n : ℤ)),
      symmPart (ea5_field nu omega j x) = nu • (1 : Mat d) := fun n x _ => (hsym x)
  refine ⟨?_, ?_, ?_⟩
  · intro t htj hjt u g hu
    have ht3 : 3 ≤ t := by omega
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ := hell t
    have hu' := (hsol t u g).1 hu
    have hreg := (hwin t (by omega) htj).2
    have hg := (hwin (t - 2) (by omega) (by omega)).1
    have e2 : ((t - 2 : ℕ) : ℤ) = (t : ℤ) - 2 := by omega
    rw [e2] at hg
    obtain ⟨w, gw, hw, hb⟩ := hCh t ht3 hEll hlam hle hσ hnu0 (hsymc t) hreg hg hδ0 u g hu'
    refine ⟨w, gw, hw, hb.trans ?_⟩
    exact ea5_mono3 hch hδ0 (by positivity) (cubeFlat_nonneg _ _)
  · intro u g hu
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ := hell j
    have hu' := (hsol j u g).1 hu
    have hreg := (hwin j (by omega) le_rfl).2
    have h1 := hCc j (by omega) hEll hlam hle hσ hnu0 (hsymc j) hreg u g hu'
    have h2 := hCp j hEll hlam hle hσ hnu0 (hsymc j) hreg u g hu'
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · exact ea5_mono_sqrt hcc (cubeFlat_nonneg _ _)
    · exact ea5_mono1 hcp (cubeL2_nonneg _ _)
  · obtain ⟨lam, Lam, hlam, hle, hEll⟩ := hell j
    obtain ⟨W, hW⟩ := hCr j hEll hlam hle hσ hnu0 (hsymc j) (hwin j (by omega) le_rfl).1 hδ1
    refine ⟨W, fun e => ?_⟩
    obtain ⟨⟨g, hg⟩, hb⟩ := hW e
    refine ⟨⟨g, (hsol j _ g).2 hg⟩, hb.trans ?_⟩
    exact ea5_mono2 hcr hδ0 (engNorm_nonneg _)

/-- The non-law parameter hypotheses of `eng_inputs` are satisfiable: the dimension, and the
parameters `ρ`, `nu`, `cStar`, `K` of the conclusion. -/
example : ∃ (d : ℕ) (_ : NeZero d), 2 ≤ d ∧
    ∃ ρ nu cStar K : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < nu ∧ nu ≤ 1 ∧ 0 < cStar ∧ K = 0 :=
  ⟨2, ⟨by norm_num⟩, le_rfl, 1 / 2, 1, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, rfl⟩

end SuperdiffusionCLT.Section6
