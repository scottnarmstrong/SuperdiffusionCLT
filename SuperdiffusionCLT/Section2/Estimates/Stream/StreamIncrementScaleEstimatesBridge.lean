/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementGagliardoSup
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyClause
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLpClause
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockAssemblyD
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementNegNormClause
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

/-!
# The shell-increment estimates from the individual clauses

`lpClause_input` is clause (b) of
`SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates`
(the `L̲^p` clause, from `IncrementLpClause`), stated exactly as that theorem binds
it, and the second theorem of this module composes the five
clause estimates — the `Ĥ^{-s}` clause (a), the `L^∞` clause (c) in the
integral lane transported through `shellLawJ1_of_shellLawJ1Restriction`, the `H^s`
clause (d), the almost-sure Gagliardo clause (e) — and the "Moreover" block
`moreover_block` into the whole statement. The proof
of that theorem is the application of the second to the first.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.HighContrast
open Homogenization.IndependentSums

theorem lpClause_input (d : ℕ) :
      ∀ s : ℝ, 0 < s → s < 1 →
        ∀ p : ℝ, 1 < p →
          ∃ Clp : ℝ,
            ∀ C : ℝ, Clp ≤ C →
              ∀ P : MeasureTheory.ProbabilityMeasure
                  (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                ∀ l m n : ℕ, n < m → m ≤ l →
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
                      (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) := by
  intro s hs hs1 p hp
  refine ⟨lpClauseConst d p, ?_⟩
  intro C hC P hPrefix hJ1 hJ2 hJ3 hJ4 l m n hnm hml
  exact exists_witness_cubeLpENorm_finiteShellIncrement hPrefix hJ1 hJ2 hJ3 hJ4 s p
    hs hs1 hp.le C hC hnm hml


theorem streamIncrement_scale_estimates_of_clauses (d : ℕ)
    (hLp :
      ∀ s : ℝ, 0 < s → s < 1 →
        ∀ p : ℝ, 1 < p →
          ∃ Clp : ℝ,
            ∀ C : ℝ, Clp ≤ C →
              ∀ P : MeasureTheory.ProbabilityMeasure
                  (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                ∀ l m n : ℕ, n < m → m ≤ l →
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
                      (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega))) :
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
                                    (2 * (1 + sigma))))
    := by
  refine ⟨moreoverLogArgConst, ?_⟩
  intro s hs hs1
  refine ⟨moreoverAmpOuterConst, moreoverAmpInnerConst d s, ?_⟩
  intro p hp
  obtain ⟨Clp, hClp⟩ := hLp s hs hs1 p hp
  refine ⟨max (incrementNegNormConst d s p)
      (max Clp
        (max (largeCubeLinftyConst d)
          (max (hsClauseConst d s) (max (gagliardoSupConst d s) 4)))), ?_⟩
  intro P hPrefix hJ1 hJ2 hJ3 hJ4
  have hp1 : (1 : ℝ) ≤ p := hp.le
  have hJ1' : ShellLawJ1 d P := shellLawJ1_of_shellLawJ1Restriction hJ1
  set C : ℝ := max (incrementNegNormConst d s p)
      (max Clp
        (max (largeCubeLinftyConst d)
          (max (hsClauseConst d s) (max (gagliardoSupConst d s) 4)))) with hCdef
  have hC1 : incrementNegNormConst d s p ≤ C := by
    rw [hCdef]; exact le_max_left _ _
  have hC2 : Clp ≤ C := by
    rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hC3 : largeCubeLinftyConst d ≤ C := by
    rw [hCdef]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hC4 : hsClauseConst d s ≤ C := by
    rw [hCdef]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hC5 : gagliardoSupConst d s ≤ C := by
    rw [hCdef]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))
  have hC6 : (4 : ℝ) ≤ C := by
    rw [hCdef]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))
  refine ⟨?_, ?_, ?_⟩
  · intro l m n hnm hml
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨X, hXm, hXt, hXp⟩ :=
        exists_witness_matHatNegENorm_finiteShellIncrement hPrefix hJ1' hJ3 hJ4
          hs hs1 hp hnm hml
      refine ⟨X, hXm, hXt.mono_scale ?_, hXp⟩
      exact mul_le_mul_of_nonneg_right hC1
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    · exact hClp C hC2 P hPrefix hJ1 hJ2 hJ3 hJ4 l m n hnm hml
    · exact exists_witness_cubeLpENormInfty_finiteShellIncrement hPrefix hJ1' hJ2 hJ3
        hJ4 C s p hs hs1 hp1 hnm hml hC3
    · exact hsClause_of_shellLaws hPrefix hJ1 hJ2 hJ3 hJ4 s p hs hs1 hp1 C hC4 hnm hml
  · intro l n
    exact gagliardoSupClause_of_shellLaws hPrefix hJ1 hJ2 hJ3 hJ4 s p hs hs1 hp1 C hC5 n l
  · exact moreover_block hPrefix hJ1 hJ2 hJ3 hJ4 hs hs1 hC6

end SuperdiffusionCLT.Section2.Estimates.Stream
