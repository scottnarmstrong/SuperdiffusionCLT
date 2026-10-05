/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.TheoremAAssembly
public import SuperdiffusionCLT.Section8.Convergence.GeneratorToPathLawC

/-!
# Theorem A from its three parts

Clause (i) is the generator proposition through `genPath_clause_i`.  Clauses (ii) and (iii) are
taken for some semigroup-valued function of the sample satisfying the specification almost surely;
since the semigroup of the specification is almost surely unique, they hold for every such
function.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal Topology

namespace SuperdiffusionCLT.Section8

open MeasureTheory

/-- **Clause (i) for every pair of the specification.** -/
theorem thmA_clause_i {d : ℕ} [NeZero d] (nu cStar : ℝ) (hc : 0 < cStar)
    {P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hgen : ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
      ∀ u : Homogenization.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
        ∃ uep : ℝ → Homogenization.Vec d → ℝ,
          (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
            ContDiff ℝ 2 (uep ε) ∧ IsC0Function (uep ε) ∧
              IsC0Function (divForm (opScale cStar ε) (epCoeff nu omega ε) (uep ε))) ∧
          Filter.Tendsto
            (fun ε : ℝ => ⨆ x : Homogenization.Vec d, ENNReal.ofReal |uep ε x - u x|)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
          Filter.Tendsto
            (fun ε : ℝ => ⨆ x : Homogenization.Vec d,
              ENNReal.ofReal
                |divForm (opScale cStar ε) (epCoeff nu omega ε) (uep ε) x -
                  (1 / 2) * Brownian.vecLaplacian u x|)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
      ∀ (S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d))
        (Q : Homogenization.Vec d →
          Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d))),
        IsDivergenceFormFeller (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) S →
        IsContinuousPathLaw S Q →
        ∀ (x₀ : Homogenization.Vec d)
          (F : BoundedContinuousFunction
            (MarkovProcess.ContinuousPath (Homogenization.Vec d)) ℝ),
          Filter.Tendsto
            (fun ε : ℝ => ∫ w, F (scalePath (|Real.log (ε ^ 2)| ^ (-(1 / 4 : ℝ)) * ε)
                ((ε ^ 2)⁻¹).toNNReal w) ∂(Q x₀))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (∫ w, F (scalePath (Real.sqrt (2 * Real.sqrt cStar)) 1 w)
              ∂(Brownian.brownianMotion d 0))) := by
  filter_upwards [hgen] with omega h S Q hS hQ x₀ F
  exact Convergence.genPath_clause_i d nu cStar hc omega h hS hQ x₀ F

/-- **Theorem A from its three parts.**  The statement is the printed one; the
hypotheses are the generator proposition `hGen`, the quenched variance statement `hDt` and the
annealed statement `hAnn`, the last two for some semigroup-valued function of the sample that
satisfies the specification almost surely. -/
theorem thmA_of_parts
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hGen : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
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
                    (𝓝[>] 0) (𝓝 0))
    (hDt : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
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
                ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                    MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                  (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      (S omega)) ∧
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
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β))))
    (hAnn : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
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
                      ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                          MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                        (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                          SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            (S omega)) ∧
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
                            ENNReal.ofReal (Cp * Real.log t ^ ((1 : ℝ) / 4 + δ)))
    :
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
  have _hd := hd
  intro nu hnu hnu1 cStar hc K
  refine ⟨fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ⟨thmA_existence hPrefix hJ3 hnu, ?_⟩, ?_⟩
  · exact thmA_clause_i nu cStar hc (hGen nu hnu hnu1 cStar hc K P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5)
  · intro δ β hδ0 hδ1 hβ0 hβ1
    obtain ⟨C, hC1, hC⟩ := hDt nu hnu hnu1 cStar hc K δ β hδ0 hδ1 hβ0 hβ1
    refine ⟨C, hC1, ?_, ?_⟩
    · intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 S hS t ht
      obtain ⟨S₁, hS₁, h⟩ := hC P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
      have heq := thmA_ae_eq hPrefix hJ3 hnu hS₁ hS
      obtain ⟨h1, h2⟩ := h t ht
      refine ⟨?_, ?_⟩
      · filter_upwards [heq, h1] with omega hω hI
        rw [← hω]
        exact hI
      · have hset : {omega | C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
              |(1 / t) * (∫ y, Homogenization.vecNormSq y
                    ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) -
                  2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                (1 / t) * Homogenization.vecNormSq
                  (∫ y, y ∂((S omega) t.toNNReal (0 : Homogenization.Vec d)))} =ᵐ[P.toMeasure]
            {omega | C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
              |(1 / t) * (∫ y, Homogenization.vecNormSq y
                    ∂((S₁ omega) t.toNNReal (0 : Homogenization.Vec d))) -
                  2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                (1 / t) * Homogenization.vecNormSq
                  (∫ y, y ∂((S₁ omega) t.toNNReal (0 : Homogenization.Vec d)))} := by
          filter_upwards [heq] with omega hω
          simp only [hω]
        rw [measure_congr hset]
        exact h2
    · intro p hp
      obtain ⟨Cp, hCp1, hCp⟩ := hAnn nu hnu hnu1 cStar hc K δ β hδ0 hδ1 hβ0 hβ1 p hp
      refine ⟨Cp, hCp1, ?_⟩
      intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 S hS t ht
      obtain ⟨S₁, hS₁, h⟩ := hCp P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
      have heq := thmA_ae_eq hPrefix hJ3 hnu hS₁ hS
      obtain ⟨h1, h2, h3⟩ := h t ht
      refine ⟨h1.congr ?_, h2.congr ?_, ?_⟩
      · filter_upwards [heq] with omega hω
        rw [hω]
      · filter_upwards [heq] with omega hω
        rw [hω]
      · refine le_of_eq_of_le (congrArg (fun z => z ^ (1 / p)) ?_) h3
        refine lintegral_congr_ae ?_
        filter_upwards [heq] with omega hω
        rw [hω]

end SuperdiffusionCLT.Section8
