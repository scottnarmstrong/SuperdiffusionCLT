/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Lemma.AssemblyD

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# Assembly of `l.sharp.scale.inputs`

The statement of `Frozen.Section6.sharp_scale_inputs`, proved from the Section 5 sharp bounds
`hS5` (the statement of `Frozen.Section5.sigmaBar_sharp_bounds`). The constant is the maximum of
the constants of the bullets, the scale `L̂` the maximum of their scales, of the threshold
making `δ_m ≤ 1`, and of the combined tail scale; `X₀` is the maximum of the scale of the
full-field bullet and the scale of the tail bullet; the almost-sure event intersects those of the
two scales and the almost-sure ellipticity of the full centered field.
-/

namespace SuperdiffusionCLT.Section6

open MeasureTheory

/-- **`l.sharp.scale.inputs`**, with the Section 5 sharp bounds as the hypothesis `hS5`. -/
theorem sharp_scale_inputs_of_sigmaBar_sharp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
                      C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) :
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
                          ENNReal.ofReal ((m : ℝ) ^ ρ)
    := by
  obtain ⟨C3, hC31, H3⟩ := full_good_exists d hd hS5
  obtain ⟨C2, hC21, H2⟩ := l2_tail d hd
  obtain ⟨Cr, hCr1, hR⟩ := l9_reg_sstar_cube d
  obtain ⟨Cu, hCu1, hU⟩ := l9_flux_grad_harm_cube d
  have hC3 : C3 ≤ max (max C3 C2) (max Cr Cu) := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : C2 ≤ max (max C3 C2) (max Cr Cu) := (le_max_right _ _).trans (le_max_left _ _)
  have hCr : Cr ≤ max (max C3 C2) (max Cr Cu) := (le_max_left _ _).trans (le_max_right _ _)
  have hCu : Cu ≤ max (max C3 C2) (max Cr Cu) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max (max C3 C2) (max Cr Cu), le_trans hC31 hC3, ?_⟩
  intro nu hnu0 hnu1 cStar hc K ε ρ M hε0 hε1 hρ0 hρ1 hM
  obtain ⟨Lh3, hL31, hH3⟩ := H3 nu hnu0 hnu1 cStar hc K ε ρ M hε0 hε1 hρ0 hρ1
    (hC3.trans hM)
  obtain ⟨Lh2, hL21, hH2⟩ := H2 nu hnu0 hnu1 cStar hc K ρ M 1 hρ0 hρ1 (hC2.trans hM) one_pos
    le_rfl
  obtain ⟨N, hN⟩ := l9_delta_threshold hε1 hρ1
  have hLsum : (0 : ℝ) ≤ (3 * Real.log (2 : ℝ)) ^ ρ⁻¹ * (Lh3 + Lh2) := by
    have : (0 : ℝ) < 3 * Real.log 2 := by
      have := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
      linarith only [this]
    have h1 : (0 : ℝ) ≤ (3 * Real.log 2) ^ ρ⁻¹ := Real.rpow_nonneg this.le _
    have h2 : (0 : ℝ) ≤ Lh3 + Lh2 := by linarith only [hL31, hL21]
    exact mul_nonneg h1 h2
  refine ⟨max 1 (max ((3 * Real.log (2 : ℝ)) ^ ρ⁻¹ * (Lh3 + Lh2)) (max (max Lh3 Lh2) N)),
    le_max_left _ _, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X3, hX3m, hX3O, hX3ae⟩ := hH3 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X2, hX2m, hX21, hX2O, -, hX2K⟩ := hH2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun omega => max (X3 omega) (X2 omega), hX3m.max hX2m,
    fun omega => le_trans (hX21 omega) (le_max_right _ _), ?_, ?_⟩
  · refine l9_log_max_bigO hρ0 (by linarith only [hL31]) (by linarith only [hL21])
      ((le_max_left _ _).trans (le_max_right _ _)) hX21 hX3O hX2O
  · filter_upwards [hX3ae, hX2K, l9_ae_exists_ell_centered hJ3 hnu0] with omega h3 h2 hell
    intro m n hX0 hL hw hnm
    have hLm : max 1 (max ((3 * Real.log (2 : ℝ)) ^ ρ⁻¹ * (Lh3 + Lh2))
        (max (max Lh3 Lh2) N)) ≤ (m : ℝ) := hL
    have hm1 : (1 : ℝ) ≤ m := (le_max_left _ _).trans hLm
    have hLh3 : Lh3 ≤ (m : ℝ) := by
      have h1 : max Lh3 Lh2 ≤ (m : ℝ) :=
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLm
      exact (le_max_left _ _).trans h1
    have hNm : N ≤ (m : ℝ) :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLm
    have hX3m' : X3 omega ≤ (3 : ℝ) ^ m := (le_max_left _ _).trans hX0
    have hX2m' : X2 omega ≤ (3 : ℝ) ^ m := (le_max_right _ _).trans hX0
    refine ⟨fun k himg => ?_, h2 m hX2m'⟩
    have hσ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu0 m hPrefix hJ2
      hJ3 hJ4
    have hE := h3 m n hX3m' hLh3 hw hnm k himg
    have hδ := hN m hNm hm1
    have hEll := hell m n (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
    obtain ⟨hreg, hsst⟩ := hR _ hCr nu _ _ omega m n k hσ hEll hE hδ
    exact ⟨hE, hreg, hU _ hCu nu _ _ omega m n k hnu0 hσ himg hEll hE hδ, hsst⟩

/-- Satisfiability of the non-law parameter hypotheses of the assembled statement:
`ν = 1`, `c⋆ = 1`, `ε = 1`, `ρ = 1/2`, `M = C`, and the constant `C ≥ 1` is arbitrary. -/
example (C : ℝ) (hC : 1 ≤ C) :
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧
      (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ C ≤ C ∧ 1 ≤ C :=
  ⟨one_pos, le_rfl, one_pos, one_pos, le_rfl, by norm_num, by norm_num, le_rfl, hC⟩

end SuperdiffusionCLT.Section6
