/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section4.HomogBelow.Main
public import SuperdiffusionCLT.Frozen.Section4.MixingBelowCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SuperdiffusionCLT.Frozen.Section4.LNaught

@[expose] public section

/-- **Proposition `p.homog.below`** (Homogenization below the infrared cutoff), Section 4:

> There exists a constant `C(d) < ∞` such that, for every `alpha ∈ [0,1)`
> and `M ∈ [1,∞)` and for every `L,m ∈ ℕ` satisfying
> `L ≥ L_0(CM,alpha,cstar,nu)` and `m ≥ L - M L^alpha log^3 L`, we have the
> estimate (`e.ass.valid`)
> `|shom_L^{-1} shom_L(cu_m) - Id| + |shom_L shom_{L,*}^{-1}(cu_m) - Id|`
> `≤ C shom_L^{-2}(L - m + C log^2 L)_+ + C m^{-3000}`.

## `L_0`

The scale `L_0` is the function `lNaught` of `Frozen.Section4.lNaught`.

## Reading choices

* **The scalars, not matrices.** shom_L, shom_L(cu_m), shom_{L,*}(cu_m)
  are real-valued carriers
  (`sigmaBarInfinite`, `sigmaBarSeq`, `sigmaBarStarInv(Seq)`), matching the
  scalar reading of the same objects in `sigmaBarStar_lower_bound`. So
  `|shom_L^{-1}shom_L(cu_m) - Id|` is literally `Real.abs` of the real number
  `shom_L^{-1} * shom_L(cu_m) - 1`: there is no matrix square root to
  interpret and no sandwich form to invoke (unlike
  `ellipticity_below_cutoff` and the mixing statement, whose displays genuinely
  conjugate a non-scalar block matrix). `Id` becomes the real number `1`.
* **shom_L in both slots is the same `sigmaBarInfinite`.** The infinite-volume
  `σ̄_L` (`e.homs.defs`) is read as `sigmaBarInfinite nu L P`
  (`σ̄_L = lim_r σ̄_{L,*}(cu_r)`), as in `sigmaBarStar_lower_bound`; the reciprocity
  of the upper-block and lower-block limits is not needed to *state* this
  proposition, only to prove it.
* **`L ≥ L_0(CM,alpha,cstar,nu)`: which `C` feeds `lNaught`'s universal-
  constant argument?** The print's `L_0` display (`e.Lnaught.def`) hides an
  independent "universal constant `C`, chosen so large that ..." inside its
  own definition, unrelated a priori to *this* proposition's own `C(d)`. Both
  are simply "some constant depending only on `d`", and the print never
  distinguishes them or asks that they differ, so the literal (not
  strengthened) Lean reading reuses the single outer witness `C` for both
  roles: `lNaught C (C * M) alpha cStar nu K`. (The alternative:
  existentially quantifying a second, independent constant for `L_0`'s
  internal slot - would only weaken the statement, since a smaller/looser
  choice is always available by taking the max of both; the shared-witness
  reading is therefore not stronger than that alternative, and matches the
  print's own single-`C` bookkeeping more literally.)
* **`K` (`nondegconst`) and `c⋆` are threaded through `ShellLawJ5`.** `c⋆`
  occurs explicitly in `L_0`'s argument list, so (by the convention of
  the formalization) `ShellLawJ5 d P cStar K hPrefix hJ2 hJ3` is included, binding
  both `cStar` and `K` to the law `P`, exactly as `sigmaBarStar_lower_bound`
  does (this proposition's own proof invokes `p.sstar.lower.bound`,
  per the remark immediately preceding `p.homog.below`: "We
  have defined `L_0` in such a way that Proposition `p.sstar.lower.bound`
  yields ..."). `J1`-`J4` and the prefix are the standing multiscale-stream
  data, as in the same statement.
* **`(L - m + C log^2 L)_+`.** The whole sum sits inside the positive part
  (not just `L - m`), so it is real subtraction/addition followed by
  `max 0 (·)`, not `ℕ`-truncated subtraction of `L` and `m` alone.
* **Every printed power is `Real.rpow`** (`shom_L^{-2}`, `L^alpha`, `log^3 L`,
  `log^2 L`, `m^{-3000}`), matching the convention of the formalization (e.g.
  `nu ^ (-(2:ℝ))` in `sigmaBarStar_lower_bound`), including the positive-integer
  exponents `3` and `2`, for uniformity with the genuinely non-integer
  `L^alpha`.
* **Hypothesis discipline.** No hypothesis beyond the printed ranges
  (`0 ≤ alpha`, `alpha < 1`, `1 ≤ M`, the two scale conditions) and the
  standing shell laws is added; in particular the proof's own intermediate
  constant `K(d) ≥ C_{(e.initial.L.condition)}` is a proof
  step, not carried into the statement. -/
theorem SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
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
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L m : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P)⁻¹ *
                    SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P m -
                  1| +
                |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P *
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P m -
                    1| ≤
                  C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^
                      (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ))
    := by
  exact SuperdiffusionCLT.Section4.HomogBelow.homogBelow_main d hd (SuperdiffusionCLT.Frozen.Section4.mixing_below_cutoff d hd)
