/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorPointwiseF
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz

@[expose] public section

open scoped ENNReal Pointwise

/-- **Lemma `l.Dirichlet.interior.pointwise`** (interior pointwise oscillation),
display `e.Dir.new.interior.pointwise`, under the standing setup (`e.Dir.new.delta`), in the
translated grid form described below.

Readings.

* `δ_m = ε m^{-(1-ρ)/2} log m` is written out and `m - n ≤ c δ_m⁻¹` is
  `(m - n) δ_m ≤ c`; shom_m is `sigmaBarInfinite nu m P`;
  `n - ⌈N log n⌉` is `nK N n`. The printed `m ≥ L̂` follows from `n < m` and
  `L̂ ≤ n - ⌈N log n⌉`. The parameter `M` of the standing setup does not occur in the
  statement.
* The field is `fullCoefficientRecentered nu ω = ν Id + (k - k(0))`; `u` solves
  `-∇·a∇u = f` in the translated cube `y + cu_m` (`shiftCube y m`, open), tested against
  `H¹₀`. `f` is any function; the right side is `⊤` unless `f ∈ L^∞(y + cu_m)`.
* **Translates and the minimal scale.** The printed statement is for the cubes centered at the
  origin and the scale `X₀ = X₀(0)`. Here one random scale `X`, with
  `log X = O_{Γ_ρ}(L̂)`, serves every center `y` of the grid `3^{n - ⌈N log n⌉ - 3} ℤ^d` with
  `|y|_∞ ≤ 3^{n + A}`, for a fixed `A ∈ ℕ` on which `L̂` and `X` depend (`y = 0` is the
  printed statement).
* **Order of constants.** `C(d)`, `c(d)`, `N(d)` first; `L̂` after
  `ν, c⋆, K, ε, ρ, A` and before the law; `X` after the law, measurable, `≥ 1`.
* Almost surely in the sample.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section7.interior_pointwise
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C c N : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ N ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∀ A : ℕ,
                ∃ Lhat : ℝ, 1 ≤ Lhat ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                      Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ρ)
                        (fun omega => Real.log (X omega)) Lhat ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ m n : ℕ,
                          n < m →
                          ((m : ℝ) - (n : ℝ)) *
                              (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
                          Lhat ≤ (SuperdiffusionCLT.Section7.nK N n : ℝ) →
                          X omega ≤ (3 : ℝ) ^ SuperdiffusionCLT.Section7.nK N n →
                          ∀ y ∈ SuperdiffusionCLT.Section7.gridPts d
                              ((SuperdiffusionCLT.Section7.nK N n : ℤ) - 3)
                              ((3 : ℝ) ^ (n + A)),
                            ∀ (f : Homogenization.Vec d → ℝ)
                              (u : Homogenization.H1Function
                                (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))),
                              SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                  (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                    nu omega)
                                  (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))
                                  u f (fun _ => 0) →
                              -- e.Dir.new.interior.pointwise
                              MeasureTheory.eLpNorm
                                  (fun x => u.toFun x -
                                    ⨍ z in SuperdiffusionCLT.Section7.shiftCube y (n : ℤ),
                                      u.toFun z)
                                  ⊤
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.shiftCube y (n : ℤ))) ≤
                                ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
                                  (SuperdiffusionCLT.Section7.lpBar
                                      (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ)) 2
                                      (fun x => u.toFun x -
                                        ⨍ z in SuperdiffusionCLT.Section7.shiftCube y
                                            (m : ℤ),
                                          u.toFun z) +
                                    ENNReal.ofReal
                                        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                            nu m P)⁻¹ *
                                          (3 : ℝ) ^ (2 * (m : ℝ))) *
                                      MeasureTheory.eLpNorm f ⊤
                                        (MeasureTheory.volume.restrict
                                          (SuperdiffusionCLT.Section7.shiftCube y
                                            (m : ℤ))))
    := by
  exact SuperdiffusionCLT.Section7.ip_interior_pointwise d hd
    (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
