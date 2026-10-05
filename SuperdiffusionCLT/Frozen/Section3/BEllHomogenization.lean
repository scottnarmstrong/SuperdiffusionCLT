/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Section3.HighContrast.BEllAssembly
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

@[expose] public section

/-- **Lemma `l.b.ell.homogenization`**, the high-contrast-to-low-contrast
comparison of the two annealed diagonal blocks, under the standing
molecular-diffusivity range `nu ∈ (0,1]` and the standing multiscale stream
assumption `a.multiscale.stream` of the paper.

There is `C(d) ∈ (0,∞)` such that, if `n ≥ C log²(ν⁻¹ L)`, then for every `ℓ ∈ ℕ`
with `n < ℓ ≤ L`,
`σ̄_ℓ(cu_n) ≤ C ν^{-4} (ℓ - n + log²(ν⁻¹ ℓ))⁴ σ̄_{ℓ,*}(cu_n)`.

This is the printed form, whose external input is the `exp(log²)` high-contrast entry theorem
realizing [AK, Theorem 3.1]; an improved polynomial version is a separate declaration.

Two points differ from the printed statement:

* the range-of-dependence assumption is the restriction version `ShellLawJ1Restriction`, in
  place of the integral version `ShellLawJ1`; `ShellLawJ1Restriction` implies `ShellLawJ1`
  (`shellLawJ1_of_shellLawJ1Restriction`), so the statement is weaker than the one with `ShellLawJ1`; and
* the cube scale is restricted to `1 ≤ n` (a correction of the printed text; see `ERRATA.md`):
  the printed argument does not cover the degenerate corner `ν = 1`, `L = 1`, `n = 0`,
  `l = 1`. -/
theorem SuperdiffusionCLT.Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ n L : ℕ, 1 ≤ n → C * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 ≤ (n : ℝ) →
            ∀ l : ℕ, n < l → l ≤ L →
              SuperdiffusionCLT.Section2.Annealed.sigmaBarScalar nu l P
                  (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) ≤
                C * nu ^ (-(4 : ℝ)) *
                    (((l - n : ℕ) : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ 2) ^ 4 *
                  SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu l P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
    := by
  classical
  by_cases hd : 2 ≤ d
  · obtain ⟨C, hC, h⟩ :=
      SuperdiffusionCLT.Section3.HighContrast.sigmaBar_le_sigmaBarStar_homogenization_of_shellRestrictionRangeDependence
        d hd
    exact ⟨C, hC, fun nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 ↦
      h nu hnu hnu1 P hPrefix
        ((SuperdiffusionCLT.Section3.HighContrast.shellLawJ1Restriction_iff_shellRestrictionRangeDependence
          P).1 hJ1) hJ2 hJ3 hJ4⟩
  · exact ⟨1, one_pos, fun nu _ _ P hPrefix _ _ _ _ n L _ _ l _ _ ↦
      absurd hPrefix.dimension hd⟩
