/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section3.Terms.SstarClosed
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

@[expose] public section

/-- **Proposition `p.sstar.lower.bound`**, the suboptimal lower bound on the
renormalized diffusivities, under the standing molecular-diffusivity range `nu ∈ (0,1]` and the
standing multiscale stream assumption `a.multiscale.stream`.

There are `C(d) ∈ [1,∞)` and `c(d) ∈ (0,1/2]` such that, for every `L, m ∈ ℕ`
with `L ≥ m ≥ L/2` and `m` above the threshold `e.L.vs.nu`, read with a correction of the
printed text (see `ERRATA.md`): the two
iterated logarithms carry `3 + ν⁻¹ + c⋆⁻¹` in place of the printed `3 + ν⁻¹`,
so that the absorption step of the proof is available for every
`c⋆ > 0`. Both

* the annealed bound `e.sstar.lower.bound`
  `σ̄_L ≥ σ̄_{L,*}(cu_m) ≥ c c⋆^{3/2} ν² m^{1/2} log^{-9/2}(ν⁻¹ m)`, and
* the quenched bound `e.sstar.lower.bound.quenched`
  `s_{L,*}^{-1}(cu_m) ≤ C ν^{-2} c⋆^{-3/2} m^{-1/2} log^{9/2}(ν⁻¹ m) Id +
  O_{Γ₂}(C ν^{-2} 3^{-m/8}) Id`

hold, where `σ̄_L = lim_{r→∞} σ̄_{L,*}(cu_r)` is `sigmaBarInfinite` and the
matrix-valued Orlicz error is read, per the notational convention of the paper, as a
measurable scalar random variable `X` with `X = O_{Γ₂}(·)` multiplying `Id` in
the Loewner order.

The range-of-dependence assumption is `ShellLawJ1Restriction` (the restriction form), which is implied by
the integral form `ShellLawJ1` (`shellLawJ1_of_shellLawJ1Restriction`), so the statement is the weaker one.

The hypothesis `hd : 2 ≤ d` is included: the paper treats `d ≥ 2` throughout, and every
statement this proof consumes carries `2 ≤ d`. The threshold correction is applied to
both summands: the second logarithm reads
`log(3 + ν⁻¹ + c⋆⁻¹ + K)` in place of `log(3 + ν⁻¹ + K)`. With the printed threshold
the absorption step fails for small `c⋆` and large `K`
(for instance at `c⋆ = exp(-t²)`, `K = t⁸`); with
the joint logarithm it holds for every `c⋆ ∈ (0,2]` and `K > 0`
(`rootChainAbsorptionC_full_joint_log_threshold`). -/
theorem SuperdiffusionCLT.Frozen.Section3.sigmaBarStar_lower_bound
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
              hPrefix hJ2 hJ3 →
          ∀ L m : ℕ, m ≤ L → L ≤ 2 * m →
            C * cStar ^ (-(3 : ℝ)) *
                (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
                    Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
                  (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) ≤ (m : ℝ) →
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ≤
                SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ∧
              c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 2) *
                    Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
                SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ∧
            ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 2) X
                  (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8))) ∧
                ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                  Homogenization.MatLoewnerLE
                    (Homogenization.sigmaStarInvCoarse
                      (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField)
                    ((C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
                            (m : ℝ) ^ (-((1 : ℝ) / 2)) *
                            Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) •
                        (1 : Homogenization.Mat d) +
                      X omega • (1 : Homogenization.Mat d))
    := by
  exact SuperdiffusionCLT.Section3.Terms.sstar_closed d hd
