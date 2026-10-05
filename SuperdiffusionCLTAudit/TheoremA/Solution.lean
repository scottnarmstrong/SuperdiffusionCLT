module

public import SuperdiffusionCLTAudit.TheoremA.SolutionBasic
public import SuperdiffusionCLTAudit.TheoremA.Support.Bridge

/-!
# Theorem A — comparator solution

Proves the challenge's `theoremA` from the library's `SuperdiffusionCLT.Frozen.Section8.theoremA`,
transporting every clause along the bridges of `Support/Bridge.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ZeroAtInfty Matrix.Norms.Elementwise

/- The library's measurable-space instance on `Vec d` is definitionally equal to Mathlib's product
σ-algebra, which the challenge uses; it is switched off here so that the statement elaborates with exactly
the challenge's instances. -/
attribute [-instance] Homogenization.instMeasurableSpaceVec

namespace SuperdiffusionCLT.StatementAudit.TheoremA

/-! ## 8. Theorem A -/

/-- **Theorem A** (quenched superdiffusive invariance principle). For `ν ∈ (0, 1]`, `c⋆ > 0` and
`K`, and every shell law `P` satisfying the standing assumptions and (J1)–(J5)
(standard Brownian motion exists: the heat kernels have a continuous-path law `W`):
* for `P`-a.e. `ω` a diffusion with generator `∇·(ν Id + k − k(0))∇` exists (a semigroup `S`
  and continuous-path laws `Q`), and for `P`-a.e. `ω`, every such `S`, `Q`, starting point
  `x₀` and bounded continuous `F` on paths, `E_{Q x₀}[F(|log ε²|^{-1/4} ε X_{·/ε²})]` converges
  as `ε → 0⁺` to `E[F(√(2 c⋆^{1/2}) W)]`, `W` a standard Brownian motion (the law `W 0` of any
  continuous-path law of the heat kernels started at `0`);
* for `δ ∈ (0, 1/4)`, `β ∈ (0, 4δ)` there is `C` such that for `t ≥ 10` the quenched second
  moment `E⁰|X_t|²` is integrable and
  `P(|t⁻¹ E⁰|X_t|² − 2 d c⋆^{1/2} (log t)^{1/2}| + t⁻¹ |E⁰ X_t|² > C (log t)^{1/4+δ})
  ≤ C exp(−C⁻¹ (log t)^β)`, and for `p ≥ 1` the annealed `L^p` norm of the same quantity is
  at most `C_p (log t)^{1/4+δ}`. -/
theorem theoremA (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∃ W : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw (heatKernel d) W) ∧
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          (∀ P : ProbabilityMeasure (ℕ → ShellField d),
            ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K →
            (∀ᵐ ω ∂P.toMeasure, ∃ S : SubMarkovKernelSemigroup (Vec d),
                IsDivergenceFormFeller (fullCoefficientRecentered nu ω) S ∧
                  ∃ Q : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw S Q) ∧
            ∀ᵐ ω ∂P.toMeasure,
              ∀ (S : SubMarkovKernelSemigroup (Vec d))
                (Q : Vec d → Measure (ContinuousPath (Vec d))),
                IsDivergenceFormFeller (fullCoefficientRecentered nu ω) S →
                IsContinuousPathLaw S Q →
                ∀ (x₀ : Vec d) (F : BoundedContinuousFunction (ContinuousPath (Vec d)) ℝ)
                  (W : Vec d → Measure (ContinuousPath (Vec d))),
                  IsContinuousPathLaw (heatKernel d) W →
                  Tendsto
                    (fun ε : ℝ ↦ ∫ w, F (scalePath
                        (|Real.log (ε ^ 2)| ^ (-(1 / 4 : ℝ)) * ε) ((ε ^ 2)⁻¹).toNNReal w)
                      ∂(Q x₀))
                    (𝓝[>] 0)
                    (𝓝 (∫ w, F (scalePath (Real.sqrt (2 * Real.sqrt cStar)) 1 w) ∂(W 0)))) ∧
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
            ∃ C : ℝ, 1 ≤ C ∧
              (∀ P : ProbabilityMeasure (ℕ → ShellField d),
                ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P →
                ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K →
                ∀ S : (ℕ → ShellField d) → SubMarkovKernelSemigroup (Vec d),
                  (∀ᵐ ω ∂P.toMeasure,
                    IsDivergenceFormFeller (fullCoefficientRecentered nu ω) (S ω)) →
                  ∀ t : ℝ, 10 ≤ t →
                    (∀ᵐ ω ∂P.toMeasure,
                      Integrable (fun y ↦ vecNormSq y) ((S ω) t.toNNReal (0 : Vec d))) ∧
                    P.toMeasure
                        {ω | C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
                            |(1 / t) * (∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d))) -
                                2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                              (1 / t) * vecNormSq (∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β)))) ∧
              ∀ p : ℝ, 1 ≤ p →
                ∃ Cp : ℝ, 1 ≤ Cp ∧
                  ∀ P : ProbabilityMeasure (ℕ → ShellField d),
                    ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P →
                    ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K →
                    ∀ S : (ℕ → ShellField d) → SubMarkovKernelSemigroup (Vec d),
                      (∀ᵐ ω ∂P.toMeasure,
                        IsDivergenceFormFeller (fullCoefficientRecentered nu ω) (S ω)) →
                      ∀ t : ℝ, 10 ≤ t →
                        AEMeasurable (fun ω ↦ ∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d)))
                            P.toMeasure ∧
                          AEMeasurable (fun ω ↦ ∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))
                            P.toMeasure ∧
                          (∫⁻ ω, ENNReal.ofReal
                                (|(1 / t) * (∫ y, vecNormSq y ∂((S ω) t.toNNReal (0 : Vec d))) -
                                      2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| ^ p +
                                  ((1 / t) * vecNormSq
                                    (∫ y, y ∂((S ω) t.toNNReal (0 : Vec d)))) ^ p)
                              ∂P.toMeasure) ^ (1 / p) ≤
                            ENNReal.ofReal (Cp * Real.log t ^ ((1 : ℝ) / 4 + δ)) := by
  have L := SuperdiffusionCLT.Frozen.Section8.theoremA d hd
  refine ⟨brownian_exists, fun nu hnu hnu1 cStar hc K ↦ ?_⟩
  obtain ⟨hA, hB⟩ := L nu hnu hnu1 cStar hc K
  refine ⟨fun P hPre hJ2 hJ3 hJ1 hJ4 hJ5 ↦ ?_, fun δ β hδ hδ' hβ hβ' ↦ ?_⟩
  · have hPre' := shellLawPrefix_lib hPre
    have hJ2' := shellLawJ2_lib hJ2
    have hJ3' := shellLawJ3_lib hJ3
    obtain ⟨hex, hconv⟩ := hA P hPre' hJ2' hJ3' (shellLawJ1Restriction_lib hJ1)
      (shellLawJ4_lib hJ4) (shellLawJ5_lib hPre' hJ2' hJ3' hJ5)
    refine ⟨?_, ?_⟩
    · filter_upwards [hex] with ω hω
      obtain ⟨S, hS, Q, hQ⟩ := hω
      exact ⟨SubMarkovKernelSemigroup.ofLib S, (isDivergenceFormFeller_iff _ _).mpr hS, Q,
        (isContinuousPathLaw_iff S Q).mpr hQ⟩
    · filter_upwards [hconv] with ω hω
      intro S Q hS hQ x₀ F W hW
      rw [eq_brownianMotion hW]
      exact hω S.toLib Q ((isDivergenceFormFeller_iff _ _).mp hS)
        ((isContinuousPathLaw_iff S.toLib Q).mp hQ) x₀ F
  · obtain ⟨C, hC, hexp, hann⟩ := hB δ β hδ hδ' hβ hβ'
    refine ⟨C, hC, fun P hPre hJ2 hJ3 hJ1 hJ4 hJ5 S hS t ht ↦ ?_, fun p hp ↦ ?_⟩
    · have hPre' := shellLawPrefix_lib hPre
      have hJ2' := shellLawJ2_lib hJ2
      have hJ3' := shellLawJ3_lib hJ3
      exact hexp P hPre' hJ2' hJ3' (shellLawJ1Restriction_lib hJ1) (shellLawJ4_lib hJ4)
        (shellLawJ5_lib hPre' hJ2' hJ3' hJ5) (fun ω ↦ (S ω).toLib)
        (hS.mono fun ω h ↦ (isDivergenceFormFeller_iff _ _).mp h) t ht
    · obtain ⟨Cp, hCp, hP⟩ := hann p hp
      refine ⟨Cp, hCp, fun P hPre hJ2 hJ3 hJ1 hJ4 hJ5 S hS t ht ↦ ?_⟩
      have hPre' := shellLawPrefix_lib hPre
      have hJ2' := shellLawJ2_lib hJ2
      have hJ3' := shellLawJ3_lib hJ3
      exact hP P hPre' hJ2' hJ3' (shellLawJ1Restriction_lib hJ1) (shellLawJ4_lib hJ4)
        (shellLawJ5_lib hPre' hJ2' hJ3' hJ5) (fun ω ↦ (S ω).toLib)
        (hS.mono fun ω h ↦ (isDivergenceFormFeller_iff _ _).mp h) t ht

end SuperdiffusionCLT.StatementAudit.TheoremA
