/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyFinalB
public import SuperdiffusionCLT.Frozen.Section4.HomogenizationBelowCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SuperdiffusionCLT.Frozen.Section4.LNaught

@[expose] public section

/-- **Lemma `l.shomm.vs.shomell`** (Section 4):

> There exists a constant `C(d)` such that, for every `alpha ∈ [0,1)`,
> `M ∈ [1,∞)` and `L, ell ∈ ℕ` satisfying `L ≥ ell ≥ L_0(CM,alpha,cstar,nu)`
> and `ell ≥ L - M L^alpha log^3 L`, we have (`e.sL.vs.sell`)
> `|shom_ell^{-1} shom_L - Id| ≤ C M L^alpha shom_L^{-2} log^3 L ≤ 1/2`.
> Moreover, there exists a deterministic scale `L_g(cstar,nu,d) ∈ ℕ` such
> that, for every `L ≥ L_g`, (`e.sL.growth`)
> `C^{-1} cstar^{3/2} nu^2 L^{1/2} log^{-9/2} L ≤ shom_L ≤`
> `C cstar^{-3/2} nu^{-2} L^{1/2} log^{9/2} L`.

Both displays share the *same* `C(d)`: the paper never introduces a second
constant for the growth display ("Moreover, there exists a deterministic
scale ..." only `L_g` is newly bound, not a new `C`), and the growth
display's `C` sits in the same paragraph as the first display's. The statement
therefore has one `∃ C`, shared by two conjuncts, mirroring the paper's own
"There exists `C` ... Moreover there exists `L_g` ..." two-part structure.

## Reading choices

* **Scalars, not matrices**, as in `homogenization_below_cutoff`: shom_ell
  and shom_L are `sigmaBarInfinite`, real-valued, and `Id` is the real number
  `1`. No sandwich form is needed.
* **`L_0`'s shared-`C` reading** is carried over unchanged from
  `homogenization_below_cutoff`: `lNaught C (C * M) alpha cStar nu K`.
* **What `L_g(c⋆,ν,d)` may depend on.** Reading the argument list `(c⋆,ν,d)`
  literally as excluding `K` would make the statement
  **stronger than the paper, and likely false**: `e.sL.growth` is derived
  from `p.sstar.lower.bound` (`sigmaBarStar_lower_bound`) via the
  proof of the lemma, and that statement's own threshold —
  `C c⋆^{-3}(log³(3+ν⁻¹+c⋆⁻¹)·loglog(3+ν⁻¹+c⋆⁻¹) + (1+K)log(3+ν⁻¹+c⋆⁻¹+K)) ≤
  m` — depends on `K` explicitly (the `(1+K)log(...+K)` term grows without
  bound in `K`). So the scale from which the growth bound can be guaranteed
  genuinely depends on `K`, and a single `K`-independent `Lg` (uniform over
  arbitrarily large `K`) is not what the proof delivers. Moreover, the paper's
  convention — "the dependence on `nondegconst` is suppressed in the
  argument list throughout" — is the *same* suppression already used for
  `L_0(M,alpha,cstar,nu)` itself (which also depends on `K` while listing
  only `(M,alpha,cstar,nu)`, see `lNaught`), so `L_g(c⋆,ν,d)` is
  read the same way: `K` is a suppressed, not absent, dependency.
  **So `K` DOES enter `L_g`.** The binder order places
  `∃ Lg : ℕ` *after* `∀ nu, ∀ cStar, ∀ K` and *before* `∀ P, (shell laws) →
  ShellLawJ5 ... →`, so `Lg` depends on `(d,ν,c⋆,K)` but not on the specific law `P`
  itself; `Lg` remains "deterministic" in the sense of not depending on the
  sample path or on which law realizes a given `(c⋆,K)`, which is the only
  part of "deterministic" the proof actually needs or delivers.
* **The first display (`e.sL.vs.sell`) keeps the ordinary `nu cStar K` /
  `ShellLawJ5` prefix**, as in `homogenization_below_cutoff` and
  `sigmaBarStar_lower_bound`, since it is not subject to the `L_g`-scoping question
  (no existential scale is bound there at all).
* **The chained inequality `... ≤ ... ≤ 1/2`** is stated as the conjunction
  of both inequalities (the printed relative bound, and that same quantity's
  bound by `1/2`), not merely the weaker end-to-end consequence.
* **Every printed power is `Real.rpow`**, as in `homogenization_below_cutoff`; `9/2`
  and `3/2` are genuine non-integer rpow exponents, `2` and `3` are rpow for
  uniformity. -/
theorem SuperdiffusionCLT.Frozen.Section4.sigmaBar_cutoff_comparison (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      -- `e.sL.vs.sell`
      (∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
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
            ∀ L ell : ℕ, ell ≤ L →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              |(SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu ell P)⁻¹ *
                    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P -
                  1| ≤
                C * M * (L : ℝ) ^ alpha *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^
                    (-(2 : ℝ)) *
                  Real.log (L : ℝ) ^ (3 : ℝ) ∧
              C * M * (L : ℝ) ^ alpha *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P) ^
                    (-(2 : ℝ)) *
                  Real.log (L : ℝ) ^ (3 : ℝ) ≤
                (1 : ℝ) / 2) ∧
      -- `e.sL.growth`
      (∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ Lg : ℕ,
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                  ∀ L : ℕ, Lg ≤ L →
                    C⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
                        Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) ≤
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ∧
                    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P ≤
                      C * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
                        Real.log (L : ℝ) ^ ((9 : ℝ) / 2))
    := by
  exact SuperdiffusionCLT.Section4.SigmaBarComparison.sbAsm_mainB d hd (SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff d hd)
