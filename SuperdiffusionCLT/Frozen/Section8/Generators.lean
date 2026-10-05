/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsO
public import SuperdiffusionCLT.Section8.Prereq.LinftyL2BdryE
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryClosed
public import SuperdiffusionCLT.Frozen.Section7.Superdiffusivity
public import SuperdiffusionCLT.Frozen.Section7.LargeScaleHolder
public import SuperdiffusionCLT.Frozen.Section7.InteriorPointwise
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Frozen.Section7.WhitneyPoincare
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

/-- **Proposition `p.generators`** (convergence of the generators),
with `e.A.ep.recall`.

Readings.

* `L^ε = ½ (2 c⋆ |log ε|)^{-1/2} ∇·(ν Id + k(·/ε))∇` is
  `divForm (opScale cStar ε) (epCoeff nu ω ε)`, with the recentered field
  `fullCoefficientRecentered nu ω = ν Id + (k - k(0))`; the constant skew matrix `k(0)` is
  invisible to `∇·(·∇u)` on `C²` functions.
* `u ∈ C_c^∞(ℝ^d)` is `ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u`; `C²` is `ContDiff ℝ 2`;
  `f ∈ C₀(ℝ^d)` is `IsC0Function f` (the underlying function of an element of `C₀(Vec d, ℝ)`).
* The family `{u^ε}` is indexed by `ε ∈ (0, 1/2]`; the two limits are taken along
  `ε → 0⁺`. `‖·‖_{L^∞(ℝ^d)}` of these continuous functions is the pointwise supremum, written
  in `ℝ≥0∞` so that no `sSup` junk value enters. `½Δu` is `(1/2) * vecLaplacian u`.
* The statement holds almost surely; the null set
  does not depend on `u`, as printed. No process occurs. -/
theorem SuperdiffusionCLT.Frozen.Section8.generators
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ (P : MeasureTheory.ProbabilityMeasure
                (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
            (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
            (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
            (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ u : Homogenization.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
                ∃ uep : ℝ → Homogenization.Vec d → ℝ,
                  (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
                    ContDiff ℝ 2 (uep ε) ∧
                      SuperdiffusionCLT.Section8.IsC0Function (uep ε) ∧
                      SuperdiffusionCLT.Section8.IsC0Function
                        (SuperdiffusionCLT.Section8.divForm
                          (SuperdiffusionCLT.Section8.opScale cStar ε)
                          (SuperdiffusionCLT.Section8.epCoeff nu omega ε) (uep ε))) ∧
                  -- e.homogenization.giveth
                  Filter.Tendsto
                    (fun ε : ℝ => ⨆ x : Homogenization.Vec d, ENNReal.ofReal |uep ε x - u x|)
                    (𝓝[>] 0) (𝓝 0) ∧
                  -- e.RHS.converge
                  Filter.Tendsto
                    (fun ε : ℝ => ⨆ x : Homogenization.Vec d,
                      ENNReal.ofReal
                        |SuperdiffusionCLT.Section8.divForm
                            (SuperdiffusionCLT.Section8.opScale cStar ε)
                            (SuperdiffusionCLT.Section8.epCoeff nu omega ε) (uep ε) x -
                          (1 / 2) * SuperdiffusionCLT.Section8.Brownian.vecLaplacian u x|)
                    (𝓝[>] 0) (𝓝 0)
    := by
  exact SuperdiffusionCLT.Section8.gen_generators d hd
    SuperdiffusionCLT.Frozen.Section7.superdiffusivity
    (SuperdiffusionCLT.Frozen.Section7.large_scale_holder d hd)
    (SuperdiffusionCLT.Frozen.Section7.whitney_poincare d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
    (SuperdiffusionCLT.Frozen.Section7.interior_pointwise d hd)
    (SuperdiffusionCLT.Section8.linfL2_boundary d hd
      (SuperdiffusionCLT.Section7.lip_boundary_fine_closed d hd
        (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
        (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)))
