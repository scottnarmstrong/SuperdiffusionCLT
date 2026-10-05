/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRootF
public import SuperdiffusionCLT.Section7.Linfty.PropE
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryClosed
public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz

@[expose] public section

open scoped ENNReal Pointwise

/-- **Theorem `t.superdiffusivity`** (quantitative homogenization of the Dirichlet problem),
with `e.Z.integrability`, `e.BVPs` and
`e.homogenization.error`.

Readings.

* **The field.** `ν Id + k^ε` is `epField nu ω ε`, that is `x ↦ ν Id + (k - k(0))(x/ε)` for the
  recentered stream matrix `fullCoefficientRecentered` (the raw series for `k` diverges; a
  constant skew matrix changes neither the weak solutions of `e.BVPs` nor
  `k^ε - (k^ε)_U`). `ν Id + k^ε - (k^ε)_U` is `epFieldCentered nu ω ε U`, the average being
  taken entrywise over `U`.
* **The boundary value problems** `e.BVPs` are `IsDirichletSolution a U f g u`: `u ∈ H¹(U)` is
  a weak solution of `-∇·(a∇u) = f` tested against `H¹₀(U)` and `u - g ∈ H¹₀(U)`, with
  `a = (2 c⋆ |log ε|)^{-1/2} (ν Id + k^ε)` and `a = Id`. The statement is for every such pair
  of solutions.
* `f ∈ L^∞(U)`, `g ∈ W^{1,∞}(U)`: `f` is any function and `g ∈ H¹(U)`; the right side is
  computed in `ℝ≥0∞` and is `⊤` unless `f` and `∇g` are essentially bounded, so no
  boundedness hypothesis is carried. `|∇g|` is the Euclidean length (`eucNorm`).
* `[F]_{H^{-1}(U)}` is `hMinusOneVec U F`, the sum over the components of `F` of the
  volume-normalized dual seminorm against `H¹₀(U)` functions (`wMinusOneBar U 2`); it differs
  from the printed seminorm by factors depending only on `(U, d)`, which the constant absorbs.
* **Order of constants.** `C(U, β, α, c⋆, ν, K, d)` after all its parameters and before the law;
  `Z` after the law, measurable, with the printed tail for every `ξ ≥ 1`. One `C` serves the
  tail and the estimate, as printed.
* Almost surely in the sample; the null set does
  not depend on `ε`, `f`, `g`, `u`, `uhom`.
* Every printed power is `Real.rpow`. -/
theorem SuperdiffusionCLT.Frozen.Section7.superdiffusivity
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ α β : ℝ, 0 < α → α ≤ 1 → 0 < β → β ≤ 1 → β + 2 * α < 1 →
      ∀ U : Set (Homogenization.Vec d),
        SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
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
                  ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable Z ∧
                    -- e.Z.integrability
                    (∀ ξ : ℝ, 1 ≤ ξ →
                      P.toMeasure {omega | ξ ≤ Z omega} ≤
                        ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                        ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                          -- e.BVPs
                          SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                SuperdiffusionCLT.Section7.epField nu omega ε x)
                              U f g u →
                          SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
                          -- e.homogenization.error
                          MeasureTheory.eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
                                (MeasureTheory.volume.restrict U) +
                              SuperdiffusionCLT.Section7.hMinusOneVec U
                                (fun x => u.grad x - uhom.grad x) +
                              SuperdiffusionCLT.Section7.hMinusOneVec U
                                (fun x =>
                                  Homogenization.matVecMul
                                      (((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                        SuperdiffusionCLT.Section7.epFieldCentered
                                          nu omega ε U x)
                                      (u.grad x) -
                                    uhom.grad x) ≤
                            ENNReal.ofReal (C * |Real.log ε| ^ (-α)) *
                              (MeasureTheory.eLpNorm
                                  (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
                                  (MeasureTheory.volume.restrict U) +
                                MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U))
    := by
  exact SuperdiffusionCLT.Section7.s5_superdiffusivity d hd
    (SuperdiffusionCLT.Section7.linf_prop d hd
      (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
      (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
      (SuperdiffusionCLT.Section7.lip_boundary_fine_closed d hd
        (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
        (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)))
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
    (SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d)
