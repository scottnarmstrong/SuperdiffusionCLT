/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateJ
public import SuperdiffusionCLT.Section8.Prereq.SuperdiffusivePoincareB
public import SuperdiffusionCLT.Section8.Prereq.LinftyL2D

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# The decay estimate (`l.decay.estimate.Linfty`)

For `u ∈ H¹₀(B_R)` with `-L^ε u = F`, `F ∈ L²(B_1)` of mean zero supported in `B_1` (for instance
`F = ∇·f`, `f ∈ C_c^∞(B_1)`), almost surely, for `ε⁻¹ ≥ X` and `8 ≤ r ≤ R`,

`‖u‖_{L^∞(B_R \ B_r)} ≤ C r^{2-γ-d} ‖F‖_{L²(B_1)}`

The estimate is proved by dilation to the unit scale,
where `a = ν Id + (k - k(0))`, from the duality argument with the large-scale Hölder estimate, the
superdiffusive Poincaré inequality, and the `L^∞`-`L²` estimates.

The four analytic inputs are taken as hypotheses in the form of the statements they come from:
`hHolder` (`t.large.scale.Holder`), `hWhitney`/`hSigma` (the inputs of the superdiffusive Poincaré
inequality), `hIP` (the interior pointwise estimate behind `l.inproof.Linfty.L2`), and `hBdry`, the
boundary `L^∞`-`L²` estimate of `l.inproof.Linfty.L2` for `u ∈ H¹₀(B_R)` (`T:15283`).
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal Pointwise

/-- **The decay estimate** (`l.decay.estimate.Linfty`). -/
theorem decayEst_linfty (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
                              ⨍ z in decayEst_ann (d := d) (R / 4) R, u.toH1Function.toFun z)) :
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
                  Measurable X ∧ (∀ ω, 3 ≤ X ω) ∧
                  (∃ Ct : ℝ, 1 ≤ Ct ∧ ∀ t : ℝ, 2 ≤ t →
                    P.toMeasure.real {ω | t < X ω} ≤
                      Ct * Real.exp (-(Ct⁻¹ * Real.log t ^ σ))) ∧
                  ∀ᵐ ω ∂P.toMeasure, ∀ ε : ℝ, 0 < ε → X ω ≤ ε⁻¹ →
                    ∀ r R : ℝ, 8 ≤ r → r ≤ R →
                      ∀ (u : H10Function (euclidBall (d := d) R)) (F : Vec d → ℝ),
                        MemLp F 2 (volume.restrict (euclidBall (d := d) 1)) →
                        (∀ x, x ∉ euclidBall (d := d) 1 → F x = 0) →
                        (∫ x in euclidBall (d := d) 1, F x = 0) →
                        IsWeakSolutionOn (fun x => opScale cStar ε • epCoeff nu ω ε x)
                          (euclidBall R) u.toH1Function F (fun _ => 0) →
                        eLpNorm u.toH1Function.toFun ⊤
                            (volume.restrict (euclidBall (d := d) R \ euclidBall r)) ≤
                          ENNReal.ofReal (C * r ^ (-((d : ℝ) - 2 + γ))) *
                            eLpNorm F 2 (volume.restrict (euclidBall (d := d) 1)) := by
  intro γ σ hγ0 hγ1 hσ0 hσ1 nu hnu hnu1 cs hcs K
  obtain ⟨CH, hCH1, hHolP⟩ := hHolder γ σ hγ0 hγ1 hσ0 hσ1 nu hnu hnu1 cs hcs K
  obtain ⟨CPo, hCPo1, hPoAll⟩ := sdPoinc_superdiffusive_poincare d hWhitney hSigma
  obtain ⟨Lhat, hLhat1, hPoP⟩ := hPoAll nu hnu hnu1 cs hcs K σ hσ0 hσ1
  obtain ⟨CL, hCL1, hLinAll⟩ := linfL2_interior d hIP (1 / (12 * (d : ℝ))) 2
    (by have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
        positivity) (by norm_num)
  obtain ⟨CB, hCB1, hBdAll⟩ := hBdry
  refine ⟨max 1 (decayEst_Cmacro d γ nu cs CH CPo CL CB), le_max_left _ _, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨XH, hXHm, -, hXHt, hXHae⟩ := hHolP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨XP, hXPm, hXP1, hXPO, hXPae⟩ := hPoP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨XL, hXLm, hXL1, ⟨CtL, hCtL1, hXLt⟩, hXLae⟩ :=
    hLinAll nu hnu hnu1 cs hcs K σ hσ0 hσ1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨XB, hXBm, hXB1, ⟨CtB, hCtB1, hXBt⟩, hXBae⟩ :=
    hBdAll nu hnu hnu1 cs hcs K σ hσ0 hσ1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  -- the tail of the Poincaré scale
  obtain ⟨CPt, hCPt1, hXPt⟩ := decayEst_tail_of_isBigO (μ := P.toMeasure) (X := XP)
    hLhat1 hσ0 hXPO
  -- the transposed scales
  obtain ⟨XH', hXH'm, hXH't, hXH'ae⟩ := decayEst_transpose_scale hJ4 nu
    (Ψ := fun x b => ∀ R : ℝ, x ≤ R → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R)),
      IsWeakSolutionOn b (euclidBall R) w f (fun _ => 0) →
      ∀ r : ℝ, x ≤ r → r ≤ R / 2 →
        eLpNorm (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) r) ⊤
            (volume.restrict (euclidBall r)) ≤
          ENNReal.ofReal (CH * (r / R) ^ γ) *
            (ballL2 R (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) R) +
              ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R))))
    (by linarith only [hCH1]) hXHm hXHt (hXHae.mono fun ω h => h.2)
  obtain ⟨XP', hXP'm, hXP't, hXP'ae⟩ := decayEst_transpose_scale hJ4 nu
    (Ψ := fun x b => ∀ R : ℝ, x ≤ R → ∀ (f : Vec d → ℝ) (w : H1Function (euclidBall (d := d) R)),
      IsWeakSolutionOn b (euclidBall R) w f (fun _ => 0) →
      lpBar (euclidBall (d := d) R) 2 (fun x => w.toFun x - ⨍ z in euclidBall R, w.toFun z) ≤
        ENNReal.ofReal (CPo * R * cs ^ (-(1 / 4 : ℝ)) * Real.sqrt nu *
            Real.log R ^ (-(1 / 4 : ℝ))) *
          lpBar (euclidBall R) 2 (fun x => eucNorm (w.grad x)) +
        ENNReal.ofReal (CPo * R ^ 2 * nu⁻¹ * Real.log R ^ (-(100 : ℝ))) *
          lpBar (euclidBall R) 2 f)
    (by linarith only [hCPt1]) hXPm hXPt hXPae
  have hXLt' : ∀ t : ℝ, 2 ≤ t →
      P.toMeasure.real {ω | t < XL ω} ≤ CtL * Real.exp (-(CtL⁻¹ * Real.log t ^ σ)) := fun t ht =>
    (measureReal_mono (fun ω (hω : t < XL ω) => (le_of_lt hω : t ≤ XL ω))).trans
      (hXLt t (by linarith only [ht]))
  -- the combined scale
  have t12 := decayEst_tail_max (μ := P.toMeasure) hCH1 hCPt1 hXH't hXP't
  have tLB := decayEst_tail_max (μ := P.toMeasure) hCtL1 hCtB1 hXLt' hXBt
  have t0 := decayEst_tail_max (μ := P.toMeasure) (by linarith only [hCH1, hCPt1])
    (by linarith only [hCtL1, hCtB1]) t12 tLB
  have tX := decayEst_tail_max_three (μ := P.toMeasure)
    (show 1 ≤ CH + CPt + (CtL + CtB) by linarith only [hCH1, hCPt1, hCtL1, hCtB1]) hσ0 t0
  have hexAe := decayEst_exist_ae hJ3 hJ4 hnu
  refine ⟨fun ω => max (max (max (XH' ω) (XP' ω)) (max (XL ω) (XB ω))) 3,
    ((hXH'm.max hXP'm).max (hXLm.max hXBm)).max measurable_const, fun ω => le_max_right _ _,
    ⟨_, by nlinarith only [hCH1, hCPt1, hCtL1, hCtB1, Real.exp_pos (Real.log 3 ^ σ)], tX⟩, ?_⟩
  filter_upwards [hXH'ae, hXP'ae, hXLae, hXBae, hexAe] with ω hH hP hL hB hex
  intro ε hε hεX r R hr8 hrR u F hF hsF hmF hu
  set Y : ℝ := max (max (max (XH' ω) (XP' ω)) (max (XL ω) (XB ω))) 3 with hY
  have hY3 : 3 ≤ Y := le_max_right _ _
  have hYH : XH' ω ≤ Y := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hYP : XP' ω ≤ Y := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hYL : XL ω ≤ Y := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hYB : XB ω ≤ Y := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hmac := decayEst_macro hd hnu hcs hγ0 (by linarith only [hCH1]) (by linarith only [hCPo1])
    (by linarith only [hCL1]) (by linarith only [hCB1]) hY3 ω hex
    (fun R' hR' f w hw r' hr' hr'2 => hH R' (hYH.trans hR') f w hw r' (hYH.trans hr') hr'2)
    (fun R' hR' f w hw => hP R' (hYP.trans hR') f w hw)
    (fun s hs W V hVW hball hW w hw => hL s (hYL.trans hs) W V hVW hball hW w hw)
    (fun R' hR' u' hw => hB R' (hYB.trans hR') u' hw) hε hεX hr8 hrR u F hF hsF hmF hu
  refine hmac.trans ?_
  have hr0 : 0 ≤ r ^ (-((d : ℝ) - 2 + γ)) := Real.rpow_nonneg (by linarith only [hr8]) _
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hr0)) le_rfl


/-- Satisfiability of the non-law hypotheses of `decayEst_linfty`: zero solution, zero source. -/
example (d : ℕ) [NeZero d] (cs nu ε R : ℝ) (ω : ShellSeq d) :
    ∃ (u : H10Function (euclidBall (d := d) R)) (F : Vec d → ℝ),
      MemLp F 2 (volume.restrict (euclidBall (d := d) 1)) ∧
      (∀ x, x ∉ euclidBall (d := d) 1 → F x = 0) ∧
      (∫ x in euclidBall (d := d) 1, F x = 0) ∧
      IsWeakSolutionOn (fun x => opScale cs ε • epCoeff nu ω ε x) (euclidBall R)
        u.toH1Function F (fun _ => 0) := by
  refine ⟨0, fun _ => 0, ?_, fun _ _ => rfl, by simp, ?_⟩
  · exact MemLp.zero'
  · intro φ
    have hg : ∀ x, (H10Function.toH1Function (0 : H10Function (euclidBall (d := d) R))).grad x =
        0 := fun _ => rfl
    simp [vecDot, matVecMul, hg]

end

end

end SuperdiffusionCLT.Section8
