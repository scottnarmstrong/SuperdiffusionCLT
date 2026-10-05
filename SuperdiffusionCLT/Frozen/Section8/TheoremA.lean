/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.TheoremAFinal
public import SuperdiffusionCLT.Section8.Prereq.LinftyL2BdryE
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryClosed
public import SuperdiffusionCLT.Frozen.Section7.Superdiffusivity
public import SuperdiffusionCLT.Frozen.Section7.LargeScaleHolder
public import SuperdiffusionCLT.Frozen.Section7.InteriorPointwise
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Section8.Brownian.BrownianMotion
public import SuperdiffusionCLT.Section8.Brownian.HeatGenerator
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import MarkovProcess.Feller.Semigroup
public import MarkovProcess.Semigroup.Generator
public import MarkovProcess.FiniteTime.ProjectiveFamily
public import MarkovProcess.Lifetime.ExitTime
public import MarkovProcess.Trajectory.Equivariance
public import MarkovProcess.Main
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal Topology

/-- **Theorem A `t.A`** (quenched superdiffusive invariance principle),
with `e.convinlaw`, `e.Dt.exp` and `e.annealed.Dt`; the process of `e.sde.intro` is
identified through its generator.

Readings.

* **The process.** `X` is a continuous-path law `Q` of a conservative Feller semigroup `S` on
  `C₀(ℝ^d)` whose generator acts as `∇·(ν Id + k)∇` on every `u ∈ C² ∩ C₀` with
  `∇·((ν Id + k)∇u) ∈ C₀` (`IsDivergenceFormFeller`, `IsContinuousPathLaw`). The first
  clause asserts that such `S` and `Q` exist almost surely; every other clause holds for every
  such `S` and `Q`. The field is `fullCoefficientRecentered nu ω = ν Id + (k - k(0))`.
* `c⋆` and `K` are the explicit J5 parameters. The constant `C` may depend on `K`
  (the print lists `C(β, δ, c⋆, ν, d)`; every lemma of the proof depends on `K`).
* **`e.convinlaw`.** Convergence in law on `C([0,∞); ℝ^d)` with the locally uniform
  (compact-open) topology is convergence of `∫ F` for every bounded continuous `F`. The
  rescaled path is `t ↦ |log ε²|^{-1/4} ε X_{t/ε²}` (`scalePath`), the limit is
  `√(2 c⋆^{1/2}) W` with `W` standard Brownian motion (`brownianMotion d 0`), along
  `ε → 0⁺`, for the process started at any `x₀` (`e.sde.intro`: `X_0 = x_0`); the limit is
  Brownian motion started at `0`. The null set does not depend on `S`, `Q`, `x₀`, `F`.
* **`e.Dt.exp`, `e.annealed.Dt`.** `E⁰[|X_t|²]` and `E⁰[X_t]` are integrals against the
  transition law `S t 0`; `|·|` is Euclidean (`vecNormSq`). Integrability of `|y|²` (hence of
  `y`) under `S t 0` for a.e. sample is asserted, so no Bochner junk value enters. The event of
  `e.Dt.exp` is a set of samples (outer measure if not measurable). The annealed clause asserts
  a.e.-measurability of both quenched moments and bounds the `ℝ≥0∞` integral, `p`-th root
  included, as printed; `C` depends also on `p` there.
* **Order of constants.** For each `δ ∈ (0, 1/4)`, `β ∈ (0, 4δ)`: `C` after `ν, c⋆, K, δ, β`
  and before the law, as printed; for each `p ≥ 1`, `C_p` likewise. `t ∈ [10, ∞)`.
* Every printed power is `Real.rpow` (`ENNReal.rpow` for the `1/p` root). -/
theorem SuperdiffusionCLT.Frozen.Section8.theoremA
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
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
  exact SuperdiffusionCLT.Section8.thmA_final d hd
    SuperdiffusionCLT.Frozen.Section7.superdiffusivity
    (SuperdiffusionCLT.Frozen.Section7.large_scale_holder d hd)
    (SuperdiffusionCLT.Frozen.Section7.interior_pointwise d hd)
    (SuperdiffusionCLT.Section8.linfL2_boundary d hd
      (SuperdiffusionCLT.Section7.lip_boundary_fine_closed d hd
        (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
        (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)))
