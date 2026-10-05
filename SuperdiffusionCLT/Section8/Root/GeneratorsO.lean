/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsN
public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateK
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance
public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInput
public import SuperdiffusionCLT.Section8.Prereq.FieldRegularity

/-!
# The convergence of the generators (`p.generators`)

`gen_generators` is the statement of `SuperdiffusionCLT.Frozen.Section8.generators`, with
the analytic inputs of the proof as explicit hypotheses: the root theorem `hRoot`, the
large-scale Holder estimate `hHolder`, the Whitney-Poincare inequality `hWhitney`, the
variance asymptotics `hSigma`, the interior pointwise estimate `hIP`, and the boundary
`L^infty`-`L^2` estimate `hBdry`.

For `u ∈ C_c^∞`, supported in a ball of radius `ρ`, the function `u^ε` is the dilate by `ρ` of the
whole-space solution of the rescaled problem, the limit of the Dirichlet solutions on the balls.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

/-- **`p.generators`**, from the analytic inputs of its proof. -/
theorem gen_generators
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
                      (∀ ξ : ℝ, 1 ≤ ξ →
                        P.toMeasure {omega | ξ ≤ Z omega} ≤
                          ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                          ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                  SuperdiffusionCLT.Section7.epField nu omega ε x)
                                U f g u →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
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
                                  MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U))
    )
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
                                      (SuperdiffusionCLT.Section6.euclidBall R))))
    )
    (hWhitney :
      ∀ U : Set (Homogenization.Vec d),
        SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
        U ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∀ ρ D M : ℝ, 0 < ρ → ρ < 1 → 1 ≤ D → C ≤ M →
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
                        -- e.Dir.new.Whitney.minscale.tail
                        Homogenization.IndependentSums.IsBigO P.toMeasure
                          (Homogenization.IndependentSums.gammaSigma ρ)
                          (fun omega => Real.log (X omega)) Lhat ∧
                        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                            ∂P.toMeasure,
                          ∀ (t : ℝ) (m : ℕ),
                            X omega ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
                            -- e.Dir.new.Whitney.Poincare.assumption.scaled
                            (∀ φ : Homogenization.H1Function (t • U),
                              MeasureTheory.eLpNorm
                                  (fun x => φ.toFun x -
                                    ⨍ z in SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                        ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉),
                                      φ.toFun z)
                                  2
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) ≤
                                ENNReal.ofReal (D * (3 : ℝ) ^ m) *
                                  MeasureTheory.eLpNorm
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (φ.grad x))
                                    2
                                    (MeasureTheory.volume.restrict
                                      (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                        ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉)))) →
                            ∀ (f : Homogenization.Vec d → ℝ)
                              (u : Homogenization.H1Function (t • U)),
                              SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega)
                                  (t • U) u f (fun _ => 0) →
                              -- e.Dir.new.Whitney.Poincare
                              SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                  (fun x => u.toFun x - ⨍ z in t • U, u.toFun z) ≤
                                ENNReal.ofReal
                                    (C * D * (3 : ℝ) ^ m *
                                      (Real.sqrt
                                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                          nu m P))⁻¹ *
                                      Real.sqrt nu) *
                                  SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                    (fun x => SuperdiffusionCLT.Section7.eucNorm (u.grad x)) +
                                ENNReal.ofReal
                                    (C * D *
                                      (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) *
                                      nu⁻¹) *
                                  SuperdiffusionCLT.Section7.lpBar (t • U) 2 f
    )
    (hSigma :
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
                        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)
    )
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
                              ⨍ z in decayEst_ann (d := d) (R / 4) R, u.toH1Function.toFun z))
    :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ (P : MeasureTheory.ProbabilityMeasure
                (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
            (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
            (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
            (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ u : Homogenization.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
                ∃ uep : ℝ → Homogenization.Vec d → ℝ,
                  (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
                    ContDiff ℝ 2 (uep ε) ∧
                      SuperdiffusionCLT.Section8.IsC0Function (uep ε) ∧
                      SuperdiffusionCLT.Section8.IsC0Function
                        (SuperdiffusionCLT.Section8.divForm
                          (SuperdiffusionCLT.Section8.opScale cStar ε)
                          (SuperdiffusionCLT.Section8.epCoeff nu omega ε) (uep ε))) ∧
                  -- e.homogenization.giveth
                  Filter.Tendsto
                    (fun ε : ℝ => ⨆ x : Homogenization.Vec d, ENNReal.ofReal |uep ε x - u x|)
                    (𝓝[>] 0) (𝓝 0) ∧
                  -- e.RHS.converge
                  Filter.Tendsto
                    (fun ε : ℝ => ⨆ x : Homogenization.Vec d,
                      ENNReal.ofReal
                        |SuperdiffusionCLT.Section8.divForm
                            (SuperdiffusionCLT.Section8.opScale cStar ε)
                            (SuperdiffusionCLT.Section8.epCoeff nu omega ε) (uep ε) x -
                          (1 / 2) * SuperdiffusionCLT.Section8.Brownian.vecLaplacian u x|)
                    (𝓝[>] 0) (𝓝 0)
    := by
  intro nu hnu hnu1 cs hcs K P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Cd, hCd1, HdAll⟩ := decayEst_linfty d hd hHolder hWhitney hSigma hIP hBdry (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) nu hnu hnu1 cs hcs K
  obtain ⟨Xd, hXdm, hXd3, -, hXdae⟩ := HdAll P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hrootm : ∀ m : ℕ, 16 ≤ m → ∃ (C : ℝ) (Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ),
      1 ≤ C ∧ ∀ᵐ ω ∂P.toMeasure, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z ω ≤ ε⁻¹ →
      ∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclidBall (d := d) (m : ℝ))),
      IsDirichletSolution (fun x => opScale cs ε • epField nu ω ε x)
        (euclidBall (m : ℝ)) (fun x => f x - 0 * u.toFun x) g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall (m : ℝ))
        (fun x => f x - 0 * uhom.toFun x) g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ))) ≤
        ENNReal.ofReal (4 * (C * |Real.log ε| ^ (-(1 / 8 : ℝ)))) *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclidBall (m : ℝ))) +
            eLpNorm (fun x => f x - 0 * u.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ)))) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    obtain ⟨C, hC, H⟩ := resEst_resolvent_estimate d hd hRoot (1 / 8) (1 / 8) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (euclidBall (m : ℝ))
      (w0_isSmoothBoundedDomain_euclidBall hm0) nu hnu hnu1 cs hcs K
    obtain ⟨Z, -, -, hZ⟩ := H P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
    refine ⟨C, Z, hC, ?_⟩
    filter_upwards [hZ] with ω h ε hε hε2 hZε f g u uhom hu huh
    exact (h ε hε hε2 hZε 0 le_rfl).1 f g u uhom hu huh
  choose! Cm Zm hCm1 hZae using hrootm
  have hrootAll : ∀ᵐ ω ∂P.toMeasure, ∀ m : ℕ, 16 ≤ m → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      Zm m ω ≤ ε⁻¹ →
      ∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclidBall (d := d) (m : ℝ))),
      IsDirichletSolution (fun x => opScale cs ε • epField nu ω ε x)
        (euclidBall (m : ℝ)) (fun x => f x - 0 * u.toFun x) g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall (m : ℝ))
        (fun x => f x - 0 * uhom.toFun x) g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ))) ≤
        ENNReal.ofReal (4 * (Cm m * |Real.log ε| ^ (-(1 / 8 : ℝ)))) *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclidBall (m : ℝ))) +
            eLpNorm (fun x => f x - 0 * u.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ)))) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : 16 ≤ m
    · filter_upwards [hZae m hm] with ω h _ using h
    · exact Filter.Eventually.of_forall fun ω h => absurd h hm
  have hDae := fieldInput_ae_data hPrefix hJ3 hnu
  have hSae := fieldReg_ae_contDiff_two_fullStreamRecentered hJ3
  have hEllae := SuperdiffusionCLT.Section7.w0_ae_isElliptic_rescaled hJ3 hnu
  filter_upwards [hXdae, hDae, hSae, hEllae, hrootAll] with ω hdec hDω hSω hEllω hrt
  obtain ⟨Dω⟩ := hDω
  intro u hu hcsu
  exact gen_core hd hnu hcs Dω hSω hEllω (γ := 1 / 2) (Cd := Cd) (Xd := Xd ω) (by norm_num)
    (by linarith only [hCd1]) (by linarith only [hXd3 ω]) hdec (α := 1 / 8) (by norm_num) Cm
    (fun m => Zm m ω) (fun m hm => by linarith only [hCm1 m hm]) hrt hu hcsu

end SuperdiffusionCLT.Section8
