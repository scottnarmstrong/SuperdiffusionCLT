/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section5.Root.RootClosure
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-- **Proposition `p.one.step.sharp`** (Section 5), display `e.approximate.recurrence`:

> There exist `C(d) < ∞` and `M(c⋆, ν, nondegconst, d) ∈ ℕ` such that, for every `n ∈ ℕ` with
> `n ≥ M` and every `h ∈ ℕ ∩ [1, shom_n]`,
> `|shom_{n+h} - shom_n - c⋆ (log 3) shom_n^{-1} h| ≤ C (log² n + nondegconst) shom_n^{-1}`.

Readings.

* shom_n is `sigmaBarInfinite nu n P`, as in `sigmaBar_sharp_bounds`.
* `h ∈ ℕ ∩ [1, shom_n]` is `1 ≤ h` and `(h : ℝ) ≤ shom_n`.
* **Order of constants** as in `sigmaBar_sharp_bounds`: `C(d)` first; `M` after `ν, c⋆, K` and
  before the law `P`.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section5.sigmaBar_approximate_recurrence
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
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
                  ∀ n : ℕ, M ≤ n →
                    ∀ h : ℕ, 1 ≤ h →
                      (h : ℝ) ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P →
                        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (n + h) P -
                            SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P -
                            cStar * Real.log 3 *
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ *
                                (h : ℝ)| ≤
                          C * (Real.log (n : ℝ) ^ (2 : ℝ) + K) *
                            (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹
    := by
  exact SuperdiffusionCLT.Section5.sigmaBar_approximate_recurrence_closed d hd
