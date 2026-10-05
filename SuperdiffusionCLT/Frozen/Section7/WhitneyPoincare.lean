/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyAssemblyE
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz

@[expose] public section

open scoped ENNReal Pointwise

/-- **Lemma `l.Dirichlet.Whitney.Poincare`** (coarse-grained Poincaré inequality in dilated
domains), with
`e.Dir.new.Whitney.minscale.tail`, the Poincaré assumption in its scaled form
`e.Dir.new.Whitney.Poincare.assumption.scaled` and `e.Dir.new.Whitney.Poincare`;
`h_m = ⌈M log m⌉` (`e.Dir.new.hm`).

Readings.

* **The domain.** `U ⊆ cu_0` is a smooth bounded domain (the print says Lipschitz). The dilate
  is `t • U` for a real `t` with `3^{m-1} < t ≤ 3^m`; `t = 3^m` is the printed `U_m`, and the
  other values are the family `3^m (λ U)`, `λ ∈ (1/3, 1]`, which the print uses with one
  random scale.
* **`U_int` and the Poincaré assumption.** `whitneyInterior (t • U) (m - h_m)` is the union of
  the cubes `z + cu_{m-h_m}`, `z ∈ 3^{m-h_m} ℤ^d ∩ (t • U)`, with
  `z + cu_{m-h_m+3} ⊆ t • U`: the printed `U_int`, dilated. The assumption is the scaled one,
  `‖φ - (φ)_{U_int}‖_{L²(U_int)} ≤ D 3^m ‖∇φ‖_{L²(U_int)}`, required of the restrictions to
  `U_int` of the functions `φ ∈ H¹(t • U)`.
* The field is `fullCoefficientRecentered nu ω`; `u ∈ H¹(t • U)` solves `-∇·a∇u = f` tested
  against `H¹₀`; `f` is any function, the right side being `⊤` unless `f ∈ L²`.
  shom_m is `sigmaBarInfinite nu m P`; `|∇u|` is Euclidean; the normalized norms are `lpBar`.
* **Order of constants.** `C(U, d)` first; `L̂` after `ν, c⋆, K, ρ, D, M` (with `M ≥ C`) and
  before the law; `X ≥ 1` after the law, measurable, with `log X = O_{Γ_ρ}(L̂)`.
* Almost surely in the sample.
* Every printed power is `Real.rpow`; `shom^{1/2}` is `Real.sqrt`. -/
theorem SuperdiffusionCLT.Frozen.Section7.whitney_poincare
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ U : Set (Homogenization.Vec d),
      SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
      U ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∀ ρ D M : ℝ, 0 < ρ → ρ < 1 → 1 ≤ D → C ≤ M →
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
                      -- e.Dir.new.Whitney.minscale.tail
                      Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ρ)
                        (fun omega => Real.log (X omega)) Lhat ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ (t : ℝ) (m : ℕ),
                          X omega ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
                          -- e.Dir.new.Whitney.Poincare.assumption.scaled
                          (∀ φ : Homogenization.H1Function (t • U),
                            MeasureTheory.eLpNorm
                                (fun x => φ.toFun x -
                                  ⨍ z in SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉),
                                    φ.toFun z)
                                2
                                (MeasureTheory.volume.restrict
                                  (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                    ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) ≤
                              ENNReal.ofReal (D * (3 : ℝ) ^ m) *
                                MeasureTheory.eLpNorm
                                  (fun x => SuperdiffusionCLT.Section7.eucNorm (φ.grad x))
                                  2
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉)))) →
                          ∀ (f : Homogenization.Vec d → ℝ)
                            (u : Homogenization.H1Function (t • U)),
                            SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                  nu omega)
                                (t • U) u f (fun _ => 0) →
                            -- e.Dir.new.Whitney.Poincare
                            SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                (fun x => u.toFun x - ⨍ z in t • U, u.toFun z) ≤
                              ENNReal.ofReal
                                  (C * D * (3 : ℝ) ^ m *
                                    (Real.sqrt
                                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                        nu m P))⁻¹ *
                                    Real.sqrt nu) *
                                SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                  (fun x => SuperdiffusionCLT.Section7.eucNorm (u.grad x)) +
                              ENNReal.ofReal
                                  (C * D *
                                    (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) *
                                    nu⁻¹) *
                                SuperdiffusionCLT.Section7.lpBar (t • U) 2 f
    := by
  exact SuperdiffusionCLT.Section7.wh3_whitney_poincare d hd
    (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
