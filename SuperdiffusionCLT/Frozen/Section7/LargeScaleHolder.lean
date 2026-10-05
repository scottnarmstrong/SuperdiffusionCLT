/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderRootE
public import SuperdiffusionCLT.Frozen.Section7.InteriorPointwise
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz

@[expose] public section

open scoped ENNReal Pointwise

/-- **Theorem `t.large.scale.Holder`** (large-scale `C^{0,γ}` estimate),
with `e.large.scale.Holder.X`, `e.Liouville.Calpha`, `e.LSH.pde` and `e.large.scale.Holder`.

Readings as in `Frozen.Section6.c1beta` (field, balls, entire solutions).

* The field `a` is `fullCoefficientRecentered nu ω = ν Id + (k - k(0))`. `B_r` is the open
  Euclidean ball `euclidBall r`; `‖·‖_{L̲²(B_r)}` is `ballL2 r`, and `(u)_{B_r}` the integral
  against `ballMeasure r`.
* **Liouville.** `u ∈ H¹_loc(ℝ^d)` with `-∇·a∇u = 0` in `ℝ^d` is `IsEntireSolution a u G`; the
  conclusion "`u` is constant" is almost-everywhere equality with a constant. The `liminf` is
  over real `r → ∞`, computed in `ℝ≥0∞`.
* **The estimate.** `u ∈ H¹(B_R)` solving `e.LSH.pde` is `IsWeakSolutionOn a (euclidBall R) u f 0`
  (tested against `H¹₀(B_R)`); `f` is any function, the right side being `⊤` unless
  `f ∈ L^∞(B_R)`. `r` ranges over the reals in `[X, R/2]`.
* **Order of constants.** `C(γ, σ, ν, c⋆, K, d)` after all its parameters and before the law;
  `X ≥ 2` after the law, measurable, with `P[X > t] ≤ C exp(-C⁻¹ (log t)^σ)` for `t ≥ 2`. One
  `C` serves the tail and the estimate, as printed.
* Both statements hold almost surely.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section7.large_scale_holder
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ γ σ : ℝ, 0 < γ → γ < 1 → 0 < σ → σ < 1 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
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
                ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧ (∀ omega, 2 ≤ X omega) ∧
                  -- e.large.scale.Holder.X
                  (∀ t : ℝ, 2 ≤ t →
                    P.toMeasure.real {omega | t < X omega} ≤
                      C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    -- Liouville theorem, e.Liouville.Calpha
                    (∀ (u : Homogenization.Vec d → ℝ)
                        (G : Homogenization.Vec d → Homogenization.Vec d),
                      SuperdiffusionCLT.Section6.IsEntireSolution
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                          u G →
                      Filter.liminf
                          (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)) *
                            SuperdiffusionCLT.Section6.ballL2 r u)
                          Filter.atTop = 0 →
                      ∃ c : ℝ, u =ᵐ[MeasureTheory.volume] fun _ => c) ∧
                    -- e.large.scale.Holder
                    (∀ R : ℝ, X omega ≤ R →
                      ∀ (f : Homogenization.Vec d → ℝ)
                        (u : Homogenization.H1Function
                          (SuperdiffusionCLT.Section6.euclidBall (d := d) R)),
                        SuperdiffusionCLT.Section7.IsWeakSolutionOn
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            (SuperdiffusionCLT.Section6.euclidBall R) u f (fun _ => 0) →
                        ∀ r : ℝ, X omega ≤ r → r ≤ R / 2 →
                          MeasureTheory.eLpNorm
                              (fun x => u.toFun x -
                                ∫ y, u.toFun y ∂SuperdiffusionCLT.Section6.ballMeasure r)
                              ⊤
                              (MeasureTheory.volume.restrict
                                (SuperdiffusionCLT.Section6.euclidBall r)) ≤
                            ENNReal.ofReal (C * (r / R) ^ γ) *
                              (SuperdiffusionCLT.Section6.ballL2 R
                                  (fun x => u.toFun x -
                                    ∫ y, u.toFun y
                                      ∂SuperdiffusionCLT.Section6.ballMeasure R) +
                                ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                                  MeasureTheory.eLpNorm f ⊤
                                    (MeasureTheory.volume.restrict
                                      (SuperdiffusionCLT.Section6.euclidBall R))))
    := by
  exact SuperdiffusionCLT.Section7.hr_large_scale_holder d hd
    (SuperdiffusionCLT.Frozen.Section7.interior_pointwise d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
