/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.TheoremAAssemblyB
public import SuperdiffusionCLT.Section8.Root.GeneratorsO
public import SuperdiffusionCLT.Section8.Root.DtExpO
public import SuperdiffusionCLT.Section8.Root.AnnealedDtE
public import SuperdiffusionCLT.Frozen.Section7.WhitneyPoincare
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds

/-!
# Theorem A from the root theorem, the large-scale Holder estimate, the interior pointwise
estimate and the boundary estimate

The statement is that of `SuperdiffusionCLT.Frozen.Section8.theoremA`.  The Whitney-Poincare
inequality and the variance asymptotics are proved theorems, used directly.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal Topology
open Homogenization MeasureTheory Filter SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

/-- **Theorem A** from `hRoot`, `hHolder`, `hIP` (the statements of the registered Section 7
theorems) and the boundary `L^infty`-`L^2` estimate `hBdry`. -/
theorem thmA_final
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hRoot : ∀ (d : ℕ) [NeZero d], 2 ≤ d →
      ∀ α β : ℝ, 0 < α → α ≤ 1 → 0 < β → β ≤ 1 → β + 2 * α < 1 →
        ∀ U : Set (Homogenization.Vec d),
          SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∃ C : ℝ, 1 ≤ C ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable Z ∧
                      -- e.Z.integrability
                      (∀ ξ : ℝ, 1 ≤ ξ →
                        P.toMeasure {omega | ξ ≤ Z omega} ≤
                          ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                          ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                            -- e.BVPs
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                  SuperdiffusionCLT.Section7.epField nu omega ε x)
                                U f g u →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
                            -- e.homogenization.error
                            MeasureTheory.eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
                                  (MeasureTheory.volume.restrict U) +
                                SuperdiffusionCLT.Section7.hMinusOneVec U
                                  (fun x => u.grad x - uhom.grad x) +
                                SuperdiffusionCLT.Section7.hMinusOneVec U
                                  (fun x =>
                                    Homogenization.matVecMul
                                        (((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                          SuperdiffusionCLT.Section7.epFieldCentered
                                            nu omega ε U x)
                                        (u.grad x) -
                                      uhom.grad x) ≤
                              ENNReal.ofReal (C * |Real.log ε| ^ (-α)) *
                                (MeasureTheory.eLpNorm
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
                                    (MeasureTheory.volume.restrict U) +
                                  MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U)))
    (hHolder :
      ∀ γ σ : ℝ, 0 < γ → γ < 1 → 0 < σ → σ < 1 →
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ C : ℝ, 1 ≤ C ∧
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
                    Measurable X ∧ (∀ omega, 2 ≤ X omega) ∧
                    -- e.large.scale.Holder.X
                    (∀ t : ℝ, 2 ≤ t →
                      P.toMeasure.real {omega | t < X omega} ≤
                        C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      -- Liouville theorem, e.Liouville.Calpha
                      (∀ (u : Homogenization.Vec d → ℝ)
                          (G : Homogenization.Vec d → Homogenization.Vec d),
                        SuperdiffusionCLT.Section6.IsEntireSolution
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            u G →
                        Filter.liminf
                            (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)) *
                              SuperdiffusionCLT.Section6.ballL2 r u)
                            Filter.atTop = 0 →
                        ∃ c : ℝ, u =ᵐ[MeasureTheory.volume] fun _ => c) ∧
                      -- e.large.scale.Holder
                      (∀ R : ℝ, X omega ≤ R →
                        ∀ (f : Homogenization.Vec d → ℝ)
                          (u : Homogenization.H1Function
                            (SuperdiffusionCLT.Section6.euclidBall (d := d) R)),
                          SuperdiffusionCLT.Section7.IsWeakSolutionOn
                              (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                              (SuperdiffusionCLT.Section6.euclidBall R) u f (fun _ => 0) →
                          ∀ r : ℝ, X omega ≤ r → r ≤ R / 2 →
                            MeasureTheory.eLpNorm
                                (fun x => u.toFun x -
                                  ∫ y, u.toFun y ∂SuperdiffusionCLT.Section6.ballMeasure r)
                                ⊤
                                (MeasureTheory.volume.restrict
                                  (SuperdiffusionCLT.Section6.euclidBall r)) ≤
                              ENNReal.ofReal (C * (r / R) ^ γ) *
                                (SuperdiffusionCLT.Section6.ballL2 R
                                    (fun x => u.toFun x -
                                      ∫ y, u.toFun y
                                        ∂SuperdiffusionCLT.Section6.ballMeasure R) +
                                  ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                                    MeasureTheory.eLpNorm f ⊤
                                      (MeasureTheory.volume.restrict
                                        (SuperdiffusionCLT.Section6.euclidBall R)))))
    (hIP :
      ∃ C c N : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ N ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
                ∀ A : ℕ,
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
                      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                        Homogenization.IndependentSums.IsBigO P.toMeasure
                          (Homogenization.IndependentSums.gammaSigma ρ)
                          (fun omega => Real.log (X omega)) Lhat ∧
                        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                            ∂P.toMeasure,
                          ∀ m n : ℕ,
                            n < m →
                            ((m : ℝ) - (n : ℝ)) *
                                (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
                            Lhat ≤ (SuperdiffusionCLT.Section7.nK N n : ℝ) →
                            X omega ≤ (3 : ℝ) ^ SuperdiffusionCLT.Section7.nK N n →
                            ∀ y ∈ SuperdiffusionCLT.Section7.gridPts d
                                ((SuperdiffusionCLT.Section7.nK N n : ℤ) - 3)
                                ((3 : ℝ) ^ (n + A)),
                              ∀ (f : Homogenization.Vec d → ℝ)
                                (u : Homogenization.H1Function
                                  (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))),
                                SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                    (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                      nu omega)
                                    (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))
                                    u f (fun _ => 0) →
                                -- e.Dir.new.interior.pointwise
                                MeasureTheory.eLpNorm
                                    (fun x => u.toFun x -
                                      ⨍ z in SuperdiffusionCLT.Section7.shiftCube y (n : ℤ),
                                        u.toFun z)
                                    ⊤
                                    (MeasureTheory.volume.restrict
                                      (SuperdiffusionCLT.Section7.shiftCube y (n : ℤ))) ≤
                                  ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
                                    (SuperdiffusionCLT.Section7.lpBar
                                        (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ)) 2
                                        (fun x => u.toFun x -
                                          ⨍ z in SuperdiffusionCLT.Section7.shiftCube y
                                              (m : ℤ),
                                            u.toFun z) +
                                      ENNReal.ofReal
                                          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                              nu m P)⁻¹ *
                                            (3 : ℝ) ^ (2 * (m : ℝ))) *
                                        MeasureTheory.eLpNorm f ⊤
                                          (MeasureTheory.volume.restrict
                                            (SuperdiffusionCLT.Section7.shiftCube y
                                              (m : ℤ)))))
    (hBdry :
      ∃ CB : ℝ, 1 ≤ CB ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K ρ : ℝ, 0 < ρ → ρ < 1 →
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
                  Measurable X ∧ (∀ ω, 1 ≤ X ω) ∧
                  (∃ Ct : ℝ, 1 ≤ Ct ∧ ∀ t : ℝ, 2 ≤ t →
                    P.toMeasure.real {ω | t < X ω} ≤
                      Ct * Real.exp (-(Ct⁻¹ * Real.log t ^ ρ))) ∧
                  ∀ᵐ ω ∂P.toMeasure, ∀ R : ℝ, X ω ≤ R →
                    ∀ u : H10Function (euclidBall (d := d) R),
                      IsWeakSolutionOn (fullCoefficientRecentered nu ω)
                          (decayEst_ann (R / 8) R)
                          (u.toH1Function.restrict (decayEst_ann_isOpen _ _)
                            (decayEst_ann_subset _ _)) (fun _ => 0) (fun _ => 0) →
                      eLpNorm u.toH1Function.toFun ⊤
                          (volume.restrict (decayEst_ann (d := d) (R / 3) R)) ≤
                        ENNReal.ofReal CB *
                          lpBar (decayEst_ann (d := d) (R / 4) R) 2
                            (fun x => u.toH1Function.toFun x -
                              ⨍ z in decayEst_ann (d := d) (R / 4) R, u.toH1Function.toFun z)) :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          -- the process exists, and e.convinlaw
          (∀ (P : MeasureTheory.ProbabilityMeasure
                (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
            (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
            (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
            (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
            (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∃ S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                    (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) S ∧
                  ∃ Q : Homogenization.Vec d →
                      MeasureTheory.Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d)),
                    SuperdiffusionCLT.Section8.IsContinuousPathLaw S Q) ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ (S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d))
                (Q : Homogenization.Vec d →
                  MeasureTheory.Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d))),
                SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                    (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) S →
                SuperdiffusionCLT.Section8.IsContinuousPathLaw S Q →
                ∀ (x₀ : Homogenization.Vec d)
                  (F : BoundedContinuousFunction
                    (MarkovProcess.ContinuousPath (Homogenization.Vec d)) ℝ),
                  Filter.Tendsto
                    (fun ε : ℝ => ∫ w, F (SuperdiffusionCLT.Section8.scalePath
                        (|Real.log (ε ^ 2)| ^ (-(1 / 4 : ℝ)) * ε) ((ε ^ 2)⁻¹).toNNReal w)
                      ∂(Q x₀))
                    (𝓝[>] 0)
                    (𝓝 (∫ w, F (SuperdiffusionCLT.Section8.scalePath
                        (Real.sqrt (2 * Real.sqrt cStar)) 1 w)
                      ∂(SuperdiffusionCLT.Section8.Brownian.brownianMotion d 0)))) ∧
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
            ∃ C : ℝ, 1 ≤ C ∧
              -- e.Dt.exp
              (∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∀ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                    MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                  (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      (S omega)) →
                  ∀ t : ℝ, 10 ≤ t →
                    (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      MeasureTheory.Integrable (fun y => Homogenization.vecNormSq y)
                        ((S omega) t.toNNReal (0 : Homogenization.Vec d))) ∧
                    P.toMeasure
                        {omega |
                          C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
                            |(1 / t) * (∫ y, Homogenization.vecNormSq y
                                  ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) -
                                2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                              (1 / t) * Homogenization.vecNormSq
                                (∫ y, y ∂((S omega) t.toNNReal (0 : Homogenization.Vec d)))} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β)))) ∧
              -- e.annealed.Dt
              ∀ p : ℝ, 1 ≤ p →
                ∃ Cp : ℝ, 1 ≤ Cp ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∀ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                        MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                      (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                          (S omega)) →
                      ∀ t : ℝ, 10 ≤ t →
                        AEMeasurable
                            (fun omega => ∫ y, Homogenization.vecNormSq y
                              ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) P.toMeasure ∧
                          AEMeasurable
                            (fun omega =>
                              ∫ y, y ∂((S omega) t.toNNReal (0 : Homogenization.Vec d)))
                            P.toMeasure ∧
                          (∫⁻ omega,
                              ENNReal.ofReal
                                (|(1 / t) * (∫ y, Homogenization.vecNormSq y
                                        ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) -
                                      2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| ^ p +
                                  ((1 / t) * Homogenization.vecNormSq
                                    (∫ y, y ∂((S omega) t.toNNReal
                                      (0 : Homogenization.Vec d)))) ^ p)
                              ∂P.toMeasure) ^ (1 / p) ≤
                            ENNReal.ofReal (Cp * Real.log t ^ ((1 : ℝ) / 4 + δ))
    := by
  have hWhitney := SuperdiffusionCLT.Frozen.Section7.whitney_poincare d hd
  have hSigma := SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd
  have hGen := gen_generators d hd hRoot hHolder hWhitney hSigma hIP hBdry
  have hDt := dtExp_clause d hd hRoot
  have hAnn := annDt_clause d hDt
  exact thmA_of_parts d hd hGen hDt hAnn

end SuperdiffusionCLT.Section8
