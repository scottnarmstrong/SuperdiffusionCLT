/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.Centering
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummabilityAllScales

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# Centring: the window clause on the good event

For every `σ > 0` there is a measurable random scale `K ≥ 27`, with `log K` of order one in `Γ_{2σ}`,
such that almost surely, for every `m` with `K ≤ 3^m`, the window clause of the statement
`streamIncrement_scale_estimates` holds at scale `m` with `δ = 1/2`.  The statement of that
theorem is taken as a hypothesis `hV6`, as in the other consumers; the
summability guard is discharged from the law assumption J3.

## Main results

* `Section7.kc1_window_ae`: the almost-sure window clause.
-/

namespace SuperdiffusionCLT.Section7

open MeasureTheory

/-- **The window clause on the good event.** -/
theorem kc1_window_ae (d : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (hV6 :
        ∃ C₂ : ℝ,
          ∀ s : ℝ, 0 < s → s < 1 →
            ∃ C₀ C₁ : ℝ,
              ∀ p : ℝ, 1 < p →
                ∃ C : ℝ,
                  ∀ P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    (∀ l m n : ℕ, n < m → m ≤ l →
                        (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                          Measurable X ∧
                            Homogenization.IndependentSums.IsBigO P.toMeasure
                              (Homogenization.IndependentSums.gammaSigma 2) X
                              (C * (3 : ℝ) ^ (s * (m : ℝ))) ∧
                            ∀ omega,
                              SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                  (Homogenization.originCube d (l : ℤ)) s
                                  (ENNReal.ofReal p)
                                  (fun x =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega n m x) ≤
                                ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ))
                                    (ENNReal.ofReal p)
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal
                                    (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ)) ∞
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                                    (Homogenization.originCube d (l : ℤ)) s
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega))) ∧
                      (∀ l n : ℕ,
                          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ᵐ omega ∂P.toMeasure,
                                (⨆ M : {M : ℕ // n < M},
                                  SuperdiffusionCLT.Section2.Norms.cubeEuclideanGagliardoESeminorm
                                    (Homogenization.originCube d (l : ℤ)) s 2
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n M.1 x)) ≤
                                  ENNReal.ofReal (X omega)) ∧
                      (∀ delta : ℝ, 0 < delta → delta < 1 →
                          ∀ sigma : ℝ, 0 < sigma →
                            ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                              Measurable Kfun ∧
                                (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
                                Homogenization.IndependentSums.IsBigO P.toMeasure
                                  (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                                  (fun omega => Real.log (Kfun omega))
                                  (C₀ *
                                    (C₁ * delta⁻¹ *
                                        Real.sqrt (sigma⁻¹ *
                                          Real.log (Real.exp 1 + C₂ * delta⁻¹ * sigma⁻¹))) ^
                                      sigma⁻¹) ∧
                                ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                                    ∂P.toMeasure,
                                  (∀ i : ℕ,
                                      Summable fun k : ℕ =>
                                        SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                          (Homogenization.openCubeSet
                                            (Homogenization.originCube d (i : ℤ)))
                                          (omega k)) →
                                    ((∀ m : ℕ,
                                        Kfun omega ≤ (3 : ℝ) ^ m →
                                    (ENNReal.ofReal ((m : ℝ)⁻¹) *
                                          SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                            (Homogenization.originCube d (m : ℤ)) ∞
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ m) *
                                          (∑' k : ℕ,
                                            ENNReal.ofReal
                                              (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                                (Homogenization.openCubeSet
                                                  (Homogenization.originCube d (m : ℤ)))
                                                (omega (m + 1 + k)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                                          SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                            (Homogenization.originCube d (m : ℤ)) s 2
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) ≤
                                      ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                                      ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                                        ∀ n : ℕ,
                                          (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                                            n ≤ m →
                                              ∀ Q : Homogenization.TriadicCube d,
                                                Q.scale = (n : ℤ) →
                                                  Homogenization.cubeCenter Q ∈
                                                      Homogenization.cubeSet
                                                        (Homogenization.originCube d (m : ℤ)) →
                                                    Homogenization.Book.Ch02.matrixOperatorNorm
                                                        (Homogenization.volumeAverageMat
                                                          (Homogenization.cubeSet Q)
                                                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                                            omega
                                                            (Homogenization.cubeSet
                                                              (Homogenization.originCube d (m : ℤ))))) ≤
                                                      A * Real.log (B * (m : ℝ)) * delta *
                                                        (m : ℝ) ^ sigma) ∧
                                      ∀ x : Homogenization.Vec d,
                                  Homogenization.Book.Ch02.matrixOperatorNorm
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) x -
                                          SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                                    C *
                                      Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                                        (2 * (1 + sigma))))) :
    ∃ Cσ : ℝ,
      ∀ P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∃ K : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma (2 * σ))
              (fun omega => Real.log (K omega)) Cσ ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m →
                ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ,
                  (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) → n ≤ m →
                    ∀ Q : Homogenization.TriadicCube d, Q.scale = (n : ℤ) →
                      Homogenization.cubeCenter Q ∈
                          Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                        Homogenization.Book.Ch02.matrixOperatorNorm
                            (Homogenization.volumeAverageMat (Homogenization.cubeSet Q)
                              (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (m : ℤ))))) ≤
                          A * Real.log (B * (m : ℝ)) * (1 / 2 : ℝ) * (m : ℝ) ^ σ := by
  obtain ⟨C₂, hC₂⟩ := hV6
  obtain ⟨C₀, C₁, hC₁⟩ := hC₂ (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨C, hC⟩ := hC₁ 2 (by norm_num)
  refine ⟨C₀ * (C₁ * ((1 / 2 : ℝ))⁻¹ *
      Real.sqrt (σ⁻¹ * Real.log (Real.exp 1 + C₂ * ((1 / 2 : ℝ))⁻¹ * σ⁻¹))) ^ σ⁻¹,
    fun P hPre hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨-, -, hK⟩ := hC P hPre hJ1 hJ2 hJ3 hJ4
  obtain ⟨K, hKm, hK27, hKO, hKae⟩ := hK (1 / 2) (by norm_num) (by norm_num) σ hσ
  refine ⟨K, hKm, hK27, hKO, ?_⟩
  have hsum :=
    SuperdiffusionCLT.Section2.Cutoff.ae_forall_summable_shellDerivLinftyNorm_originCube
      (P := P) hJ3
  filter_upwards [hKae, hsum] with omega h1 h2 m hm
  exact ((h1 h2).1 m hm).2

end SuperdiffusionCLT.Section7
