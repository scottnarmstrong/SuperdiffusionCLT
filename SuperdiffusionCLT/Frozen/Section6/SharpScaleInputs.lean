/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section6.Lemma.AssemblyE
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.PDE.Harmonic
public import Homogenization.Book.Ch03.Definitions

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-- **Lemma `l.sharp.scale.inputs`** (with `e.Dir.new.delta` and `e.Dir.new.hm`).

Readings.

* `δ_m = ε m^{-(1-ρ)/2} log m` and `h_m = ⌈M log m⌉` are written out; shom_m is
  `sigmaBarInfinite nu m P`.
* The full centered field `a - (k)_{cu_m}` is `ν Id + centeredStreamField ω cu_m`, the carrier
  of the full-field conjunct of `Frozen.Section4.minimal_scales`. `z + cu_n` with
  `z = 3^{n-3} k` is rendered by translating the field to the origin cube;
  `z + cu_n ⊆ cu_m` is the image condition
  of `minimal_scales`. The four per-cube bullets are stated for every admissible `k`, which is
  the printed maximum over `z`.
* `𝒜(z + cu_n; a)`, `s(z + cu_n; a)` and `s_*(z + cu_n; a)` are taken for the centered field:
  subtracting the constant skew matrix `(k)_{cu_m}` changes neither the solution space nor
  `s`, `s_*`, and the uncentered `a` is not a defined object (its series diverges).
* `3^{-n/4} ‖·‖_{H̲^{-1/4}(z + cu_n)}` is CoarseGraining's
  `scaleNormalizedDualNegativeBesovVectorNormTwo _ (1/4)`, which carries the factor
  `3^{-n/4}`; for `s = 1/4 < 1/2` the zero-trace and full `H^{1/4}` test classes coincide.
* `Λ_{1/4,1}`, `λ_{1/4,1}` are `LambdaSq`, `lambdaSq` at `MultiscaleExponent.finite 1`;
  `|·|` on matrices is `matNorm`; `[·]_{Ĥ^{-1/4}(cu_m)}` and `‖·‖_{L^∞(cu_m)}` are the carriers
  of `streamIncrement_scale_estimates`.
* **Order of constants.** `C(d)` first; `L̂` after `ν, c⋆, K, ε, ρ, M` and before the law, as
  printed. `X₀` is random, measurable, `≥ 1`, with `log X₀ = O_{Γ_ρ}(L̂)`; the estimates hold
  almost surely.
* Every printed power is `Real.rpow`; `shom^{1/2}` is `Real.sqrt`. -/
theorem SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
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
                  ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma ρ)
                      (fun omega => Real.log (X0 omega)) Lhat ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ m n : ℕ,
                        X0 omega ≤ (3 : ℝ) ^ m →
                        Lhat ≤ (m : ℝ) →
                        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
                        n ≤ m →
                        (∀ k : Fin d → ℤ,
                          (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                              Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                            Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                          -- e.Dir.new.full.good
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) (1 / 9)
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite 2)
                              (fun x => nu • (1 : Homogenization.Mat d) +
                                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                                (1 : Homogenization.Mat d)) ≤
                            ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
                          -- e.Dir.new.reg.ellipticity
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
                                Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
                                  (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
                                  (fun x => nu • (1 : Homogenization.Mat d) +
                                    SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                      omega
                                      (Homogenization.cubeSet
                                        (Homogenization.originCube d (m : ℤ)))
                                      ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
                              SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
                                (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
                                  (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
                                  (fun x => nu • (1 : Homogenization.Mat d) +
                                    SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                      omega
                                      (Homogenization.cubeSet
                                        (Homogenization.originCube d (m : ℤ)))
                                      ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
                            C ∧
                          -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
                          (∀ u : Homogenization.AHarmonicFunction
                              (fun x => nu • (1 : Homogenization.Mat d) +
                                SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                  (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
                            ENNReal.ofReal
                                (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
                                  (Homogenization.originCube d (n : ℤ)) (1 / 4)
                                  (fun x => Homogenization.matVecMul
                                    (nu • (1 : Homogenization.Mat d) +
                                      SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                        omega
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (m : ℤ)))
                                        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
                                      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                          nu m P • (1 : Homogenization.Mat d))
                                    (u.toH1.grad x))) ≤
                              ENNReal.ofReal
                                  (C *
                                    Real.sqrt
                                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                        nu m P) *
                                    (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
                                    Real.sqrt nu) *
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                  (Homogenization.originCube d (n : ℤ)) 2
                                  (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
                            ENNReal.ofReal
                                (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
                                  (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
                              ENNReal.ofReal
                                  (C *
                                    (Real.sqrt
                                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                        nu m P))⁻¹ *
                                    Real.sqrt nu) *
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                  (Homogenization.originCube d (n : ℤ)) 2
                                  (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
                            ∃ w : Homogenization.AHarmonicFunction
                                (fun _ => (1 : Homogenization.Mat d))
                                (Homogenization.openCubeSet
                                  (Homogenization.originCube d ((n : ℤ) - 1))),
                              ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                                  SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d ((n : ℤ) - 1)) 2
                                    (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
                                ENNReal.ofReal
                                    (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
                                      (Real.sqrt
                                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                          nu m P))⁻¹ *
                                      Real.sqrt nu) *
                                  SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (n : ℤ)) 2
                                    (fun x =>
                                      Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
                          -- e.Dir.new.sstar.close
                          Homogenization.matNorm
                                ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu m P)⁻¹ •
                                  Homogenization.sigmaCoarse
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (n : ℤ)))
                                    (fun x => nu • (1 : Homogenization.Mat d) +
                                      SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                        omega
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (m : ℤ)))
                                        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
                                  1) +
                              Homogenization.matNorm
                                ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu m P)⁻¹ •
                                  Homogenization.sigmaStarCoarse
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (n : ℤ)))
                                    (fun x => nu • (1 : Homogenization.Mat d) +
                                      SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                        omega
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (m : ℤ)))
                                        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
                                  1) ≤
                            C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
                        -- e.Dir.new.k.bounds
                        ENNReal.ofReal ((m : ℝ)⁻¹) *
                            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                              (Homogenization.originCube d (m : ℤ)) ∞
                              (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
                          ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
                            SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                              (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
                              (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
                                (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
                          ENNReal.ofReal ((m : ℝ) ^ ρ)
    := by
  exact SuperdiffusionCLT.Section6.sharp_scale_inputs_of_sigmaBar_sharp d hd
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
