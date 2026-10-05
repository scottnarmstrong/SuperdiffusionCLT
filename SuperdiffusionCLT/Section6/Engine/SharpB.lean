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
public import SuperdiffusionCLT.Section6.Engine.Sharp

/-!
# The sharp-scale engine

From the sharp-scale inputs (taken as the hypothesis) to the sharp-scale statement:
the order of the constants is fixed, the almost-sure event of the one-block inputs is used at
the sample's minimal scale, and the three conclusions come from the chain of one-block steps.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

/-- **The engine**: `p.C1beta.sharp` from `l.sharp.scale.inputs`. Both statements are those of
the corresponding declarations in `Frozen.Section6`. -/
theorem c1beta_sharp_of_inputs (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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

    ∃ C : ℝ, 1 ≤ C ∧
      ∀ γ ρ : ℝ, 0 < γ → γ < 1 → 0 < ρ → ρ < 1 →
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ Ctail : ℝ, 0 < Ctail ∧
                ∀ (P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                      hPrefix hJ2 hJ3 →
                  ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                    Homogenization.IndependentSums.IsBigOWith P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma ρ)
                      (fun omega => Real.log (X omega)) Ctail ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      -- Liouville theorem
                      (Module.finrank ℝ
                          (Submodule.span ℝ
                            (SuperdiffusionCLT.Section6.growthSpace
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              γ)) = 1 + d ∧
                        ∀ γ' : ℝ, 0 < γ' → γ' < 1 →
                          SuperdiffusionCLT.Section6.growthSpace
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              γ' =
                            SuperdiffusionCLT.Section6.growthSpace
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              γ) ∧
                      -- flatness at every scale
                      (∀ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) γ,
                        ∀ r : ℝ, X omega ≤ r →
                          (⨅ e : Homogenization.Vec d,
                              SuperdiffusionCLT.Section6.ballL2 r
                                (fun x => φ x - Homogenization.vecDot e x -
                                  ∫ y, φ y ∂SuperdiffusionCLT.Section6.ballMeasure r)) ≤
                            ENNReal.ofReal
                                (C * Real.log r ^ (-((1 - ρ) / 2)) * Real.log (Real.log r)) *
                              SuperdiffusionCLT.Section6.ballL2 r φ) ∧
                      -- large-scale C^{1,γ} estimate
                      (∀ R : ℝ, X omega ≤ R →
                        ∀ (u : Homogenization.Vec d → ℝ)
                          (g : Homogenization.Vec d → Homogenization.Vec d),
                          SuperdiffusionCLT.Section6.IsBallSolution
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              R u g →
                            ∃ φ ∈ SuperdiffusionCLT.Section6.growthSpace
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                                γ,
                              ∃ gφ : Homogenization.Vec d → Homogenization.Vec d,
                                SuperdiffusionCLT.Section6.IsEntireSolution
                                    (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                      nu omega) φ gφ ∧
                                  ∀ r : ℝ, X omega ≤ r → r < R →
                                    SuperdiffusionCLT.Section6.ballGradL2 r
                                        (fun x => g x - gφ x) ≤
                                      ENNReal.ofReal (C * (r / R) ^ γ) *
                                        SuperdiffusionCLT.Section6.ballGradL2 R g) := by
  obtain ⟨Cin, hCin, hev⟩ := eng_inputs d hd hInputs
  obtain ⟨C, C0, hC1, hdet⟩ := eng_deterministic d Cin 2 hCin (by norm_num)
  refine ⟨4 * C, by linarith only [hC1], ?_⟩
  intro γ ρ hγ0 hγ1 hρ0 hρ1 nu hnu0 hnu1 cStar hcStar K
  obtain ⟨Lhat, m1, hL1, hP⟩ := hev ρ hρ0 hρ1 nu hnu0 hnu1 cStar hcStar K
  choose! κ c Hb hκ hc hdetγ using hdet
  have hsg := fun g (h0 : 0 < g) (h1 : g < 1) =>
    eng_sigma_growth d hd nu cStar K (κ g) hnu0 hnu1 hcStar (hκ g h0 h1)
  choose! L0 hL0 using hsg
  have hpar := fun g (h0 : 0 < g) (h1 : g < 1) =>
    eng_params ((1 - ρ) / 2) (c g) (by linarith only [hρ1]) (hc g h0 h1) (Hb g)
  choose! m0 hm03 hm0δ hm0a using hpar
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℝ → ℕ, ∀ g, Mf g =
      max (max (m0 g) (L0 g)) (max (max (m1 (Hb g)) (Hb g + d + 5)) 5) := ⟨_, fun _ => rfl⟩
  have hMa : ∀ g, m0 g ≤ Mf g := fun g => by rw [hMf]; omega
  have hMb : ∀ g, L0 g ≤ Mf g := fun g => by rw [hMf]; omega
  have hMc : ∀ g, m1 (Hb g) ≤ Mf g := fun g => by rw [hMf]; omega
  have hMd : ∀ g, Hb g + d + 5 ≤ Mf g := fun g => by rw [hMf]; omega
  have hMe : ∀ g, 5 ≤ Mf g := fun g => by rw [hMf]; omega
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCt : 0 < 3 * Lhat + ((Mf γ : ℝ) + (C0 : ℝ) + 1) * Real.log 3 := by
    have : 0 ≤ ((Mf γ : ℝ) + (C0 : ℝ) + 1) * Real.log 3 := by positivity
    linarith only [this, hL1]
  refine ⟨3 * Lhat + ((Mf γ : ℝ) + (C0 : ℝ) + 1) * Real.log 3, hCt, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX01, hX0O, hae⟩ := hP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨hXm, hX1, hXO, hXcov⟩ :=
    eng_scale_tail P.toMeasure ρ Lhat hρ0 hρ1 hL1 (Mf γ) C0 X0 hX0m hX01 hX0O
  refine ⟨_, hXm, hX1, hXO, ?_⟩
  filter_upwards [hae] with omega hω
  obtain ⟨hGE, hEll, hblk⟩ := hω
  obtain ⟨hXle, hLle⟩ := hXcov omega
  -- the three scale-wise facts
  have hh2 : ∀ g : ℝ, 0 < g → g < 1 → ∀ mstar : ℕ, Mf g ≤ mstar → ∀ j : ℕ, mstar ≤ j →
      0 ≤ (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ) ∧
        (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ) * ((Hb g : ℝ) + 1) ≤ c g :=
    fun g h0 h1 mstar hm j hj => (hm0δ g h0 h1) j (le_trans (hMa g) (le_trans hm hj))
  have hh3 : ∀ g : ℝ, 0 < g → g < 1 → ∀ mstar : ℕ, Mf g ≤ mstar → ∀ i j : ℕ, mstar ≤ i → i ≤ j →
      (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ) ≤
        (i : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (i : ℝ) :=
    fun g h0 h1 mstar hm i j hi hij => (hm0a g h0 h1) i j (le_trans (hMa g) (le_trans hm hi)) hij
  have hh4 : ∀ g : ℝ, 0 < g → g < 1 → ∀ mstar : ℕ, Mf g ≤ mstar → ∀ k m : ℕ, mstar ≤ k → k ≤ m →
      0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P / nu ∧
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m + 1) P / nu ≤
          2 * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P / nu) ∧
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu k P / nu ≤
          2 * (9 : ℝ) ^ (κ g * ((m : ℝ) - (k : ℝ))) *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P / nu) :=
    fun g h0 h1 mstar hm k m hk hkm =>
      ec6_div_growth nu 2 (κ g) hnu0
        (fun j => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu j P) (L0 g)
        (hL0 g h0 h1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5) k m
        (le_trans (hMb g) (le_trans hm hk)) hkm
  have app := fun (g : ℝ) (h0 : 0 < g) (h1 : g < 1) (mstar : ℕ) (hm : Mf g ≤ mstar)
      (hX : X0 omega ≤ (3 : ℝ) ^ mstar) (hL : Lhat ≤ (mstar : ℝ)) =>
    hdetγ g h0 h1 (fullCoefficientRecentered nu omega)
      (fun j : ℕ => (j : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (j : ℝ))
      (fun j : ℕ => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu j P / nu) mstar
      (le_trans (hMd g) hm) (hh2 g h0 h1 mstar hm) (hh3 g h0 h1 mstar hm) hGE hEll
      (hh4 g h0 h1 mstar hm)
      (fun j hj => hblk (Hb g) j
        (le_trans hX (pow_le_pow_right₀ (by norm_num) hj))
        (le_trans hL (by exact_mod_cast hj))
        (le_trans (hMc g) (le_trans hm hj)))
  set N := ⌈max Lhat (Real.logb 3 (X0 omega))⌉₊ with hN
  have appg : ∀ g : ℝ, 0 < g → g < 1 →
      Module.finrank ℝ (Submodule.span ℝ
        (growthSpace (fullCoefficientRecentered nu omega) g)) = 1 + d := by
    intro g h0 h1
    refine (app g h0 h1 (Mf g + (Mf γ + N)) (Nat.le_add_right _ _)
      (le_trans hXle (pow_le_pow_right₀ (by norm_num) (by omega)))
      (le_trans hLle (by exact_mod_cast (by omega)))).1
  have hmst : Mf γ ≤ Mf γ + N := Nat.le_add_right _ _
  have hA := app γ hγ0 hγ1 (Mf γ + N) hmst hXle hLle
  refine ⟨⟨hA.1, fun g h0 h1 => ec6_growth_eq _ hGE γ g (appg γ hγ0 hγ1) (appg g h0 h1)⟩, ?_, ?_⟩
  · intro φ hφ r hr
    obtain ⟨k, hk1, hk2, hk3⟩ := ec6_scale (Mf γ + N) r
      (le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hr)
    have h5 : 5 ≤ k := by have := hMe γ; omega
    have hfl := hA.2.1 φ hφ k r hk1 hk2 hk3
    have hrate := eng_rate_convert ((1 - ρ) / 2) (by linarith only [hρ1])
      (by linarith only [hρ0]) k r h5 hk2 hk3
    refine le_trans hfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have hCpos : 0 ≤ C := by linarith only [hC1]
    calc C * ((k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ))
        ≤ C * (4 * (Real.log r ^ (-((1 - ρ) / 2)) * Real.log (Real.log r))) :=
          mul_le_mul_of_nonneg_left hrate hCpos
      _ = 4 * C * Real.log r ^ (-((1 - ρ) / 2)) * Real.log (Real.log r) := by ring
  · intro R hR u g hsol
    obtain ⟨φ, hφ, gφ, hent, hest⟩ := hA.2.2 R hR u g hsol
    refine ⟨φ, hφ, gφ, hent, fun r hr hrR => ?_⟩
    refine le_trans (hest r hr hrR) (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have hr0 : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le one_pos (hX1 omega)) hr
    have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR.le
    have hnn : 0 ≤ (r / R) ^ γ := Real.rpow_nonneg (div_nonneg hr0.le hR0.le) _
    have hCpos : 0 ≤ C := by linarith only [hC1]
    nlinarith only [mul_nonneg hCpos hnn]

/-- The non-law hypotheses of `c1beta_sharp_of_inputs` are satisfiable: `d = 2`. -/
example : ∃ d : ℕ, ∃ _ : NeZero d, 2 ≤ d := ⟨2, ⟨by norm_num⟩, le_rfl⟩

end SuperdiffusionCLT.Section6
