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

/-- **Theorem `t.sstar.sharp.bounds`** (Section 5), display `e.sm.sharp.bounds`:

> There exist constants `C(d) < ∞` and `M(c⋆, ν, nondegconst, d) < ∞` such that, for every
> `m ∈ ℕ` with `m ≥ M`,
> `|shom_m - (2 c⋆ (log 3) m)^{1/2}| ≤ C c⋆^{-1} (log² m + nondegconst)`.

Readings.

* shom_m is the infinite-volume annealed diffusivity of the cutoff field `a_m` (`e.homs.defs`),
  the carrier `sigmaBarInfinite nu m P` of the Section 3 and Section 4 statements.
* `c⋆` and `nondegconst` are the `cStar` and `K` of `ShellLawJ5`; `ν ∈ (0,1]`.
* **Order of constants.** `C` depends on `d` only and is bound first. `M` is bound after
  `ν, c⋆, K` and before the law `P`: the print says `M` depends only on `(c⋆, ν, nondegconst, d)`.
  This is the binder position of `L_g` in `sigmaBar_cutoff_comparison`.
* `0 < c⋆` is stated before `M` (as in `sigmaBar_cutoff_comparison`); it also follows from
  `ShellLawJ5`, so it adds nothing.
* The print has one display and no further clause: no statement uniform over a second cutoff,
  and none for the field without cutoff.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds
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
                  ∀ m : ℕ, M ≤ m →
                    |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
                        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                      C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)
    := by
  exact SuperdiffusionCLT.Section5.sigmaBar_sharp_bounds_closed d hd
