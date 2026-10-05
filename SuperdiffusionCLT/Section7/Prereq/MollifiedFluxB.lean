/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.MollifiedFlux
public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaC

/-!
# The local mollified flux and full-flux bounds

Displays `e.Dir.new.local.flux.mollified` and
`e.Dir.new.local.fullflux.mollified`.

From the statement of `sharp_scale_inputs` (the hypothesis `hInputs`, as in `r1_rhs_blackbox`):
almost surely, for every aligned cube `y + z + □_{n+1}` inside `y + □_m`, with the field
`ν Id + k(y + z + ·)` on the origin cube `□_{n+1}` and a weak solution `u` there with right-hand side
`f`, at every point `x0` of `□_n` the mollifications at scale `3^n` of the flux defect
`(a - σ̄ Id) ∇u`, of the gradient `∇u` and of the full flux `a ∇u` are bounded by the right sides of
`r1_rhs_blackbox` at the scale `n + 1`, times the mollifier constant `3^d (6L + A)`.  The estimate is
`r1_rhs_blackbox` at the scale `n + 1` (the aligned cube `z + □_{n+1}` is itself a cube of the grid
`3^{n-2} ℤ^d`) composed with `m1_mollify_dual_le`.
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

/-- **The local mollified flux, gradient and full flux** (`e.Dir.new.local.flux.mollified`,
`e.Dir.new.local.fullflux.mollified`). -/
theorem m1_mollified_flux (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ)) :
 ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P), SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P → SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P → SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
    ∀ y : Homogenization.Vec d, ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n + 1 ≤ m → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) + x) '' Homogenization.cubeSet (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) ⊆ Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) → ∀ (u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)))) (f : Homogenization.Vec d → ℝ), SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun x => nu • (1 : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d ((n + 1 : ℕ) : ℤ))) u f (fun _ => 0) →
    ∀ (η : Homogenization.Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) → LipschitzWith L η →
    (∀ w, (∃ i, 1 < |w i|) → η w = 0) → ∀ x0 ∈ Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)),
    (ENNReal.ofReal ‖SuperdiffusionCLT.Section7.a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun x => Homogenization.matVecMul ((nu • (1 : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) + x)) - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) (u.grad x)) x0‖ ≤
      ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) * (ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq (u.grad x))) + ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) (ENNReal.ofReal (SuperdiffusionCLT.Section7.sobStar d)).conjExponent f)) ∧
    (ENNReal.ofReal ‖SuperdiffusionCLT.Section7.a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (u.grad) x0‖ ≤ ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) * (ENNReal.ofReal (C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq (u.grad x))) + ENNReal.ofReal ((C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu + C) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) (ENNReal.ofReal (SuperdiffusionCLT.Section7.sobStar d)).conjExponent f)) ∧
    (ENNReal.ofReal ‖SuperdiffusionCLT.Section7.a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun x => Homogenization.matVecMul (nu • (1 : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) + x)) (u.grad x)) x0‖ ≤
      ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) * (ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq (u.grad x))) + ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) (ENNReal.ofReal (SuperdiffusionCLT.Section7.sobStar d)).conjExponent f) + ENNReal.ofReal ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (3 ^ d * (6 * (L : ℝ) + A))) * (ENNReal.ofReal (C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq (u.grad x))) + ENNReal.ofReal ((C * (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu + C) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n + 1 : ℕ) : ℤ)) (ENNReal.ofReal (SuperdiffusionCLT.Section7.sobStar d)).conjExponent f)))
 := by
  obtain ⟨Cb, hCb, H⟩ := b2_translated_inputs d hInputs
  obtain ⟨Cd, hCd, hstep⟩ := r1_step hd
  refine ⟨max Cb Cd, le_trans hCb (le_max_left _ _), ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hCM
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1
    ((le_max_left _ _).trans hCM)
  refine ⟨Lhat, hL, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, fun y => ?_⟩
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [hae y, hqmp.ae (Section6.l9_ae_exists_ell_centered hJ3 hnu)] with omega hω hell m n
    hX hLm hn1 hn2 k himg u f hu η A L hηA hηL hη0 x0 hx0
  have hn1' : (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ ((n + 1 : ℕ) : ℤ) :=
    hn1.trans (by push_cast; omega)
  obtain ⟨hAg, hkb⟩ := hω m (n + 1) hX hLm hn1' hn2
  obtain ⟨-, -, hbul, -⟩ := hAg k himg
  have hm1 : (1 : ℝ) ≤ m := hL.trans hLm
  have hσ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  obtain ⟨lam, Lam, hl⟩ := hell m (n + 1) (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ))
  have hfield : (fun x : Homogenization.Vec d => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega)
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
          ((fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) + x)) =
      fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.translateSet y
            (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))))
          (y + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) + x) := by
    funext x
    rw [b2_csf_translate_apply, b2_add_assoc_aux]
  rw [hfield] at hl
  obtain ⟨hflux, hgrad⟩ := hstep (max Cb Cd) Cb (le_max_left _ _) (le_max_right _ _) nu ε ρ _ m (n + 1) _ y
    (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (k i : ℝ)) hnu hε
    hm1 hσ hCb (fun x => Section6.HarmonicApprox.symmPart_centeredStreamField_add nu omega _ x)
    ⟨lam, Lam, hl⟩ himg _ hkb (fun v => ⟨(hbul v).1, (hbul v).2.1⟩) u f hu
  have hEll := hl.mono (isOpen_openCubeSet _).measurableSet (openCubeSet_subset_cubeSet _)
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hηA 0)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hK : 0 ≤ 3 ^ d * (6 * (L : ℝ) + A) := by positivity
  have hS0 : 0 ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P := hσ.le
  have e1 := ENNReal.ofReal_le_ofReal (m1_mollify_flux_le n hηA hηL hη0 hx0 hEll
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) u)
  have e2 := ENNReal.ofReal_le_ofReal (m1_mollify_grad_le n hηA hηL hη0 hx0 u)
  have e3 := ENNReal.ofReal_le_ofReal (m1_mollify_fullflux_le n hηA hηL hη0 hx0 hEll hS0 u)
  rw [ENNReal.ofReal_mul hK] at e1 e2
  have r1 := e1.trans (mul_le_mul' le_rfl hflux)
  have r2 := e2.trans (mul_le_mul' le_rfl hgrad)
  refine ⟨r1, r2, e3.trans ?_⟩
  refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ ?_)
  · rw [ENNReal.ofReal_mul hK]
    exact mul_le_mul' le_rfl hflux
  · rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hS0 hK)]
    exact mul_le_mul' le_rfl hgrad

/-- Satisfiability witness for the non-law hypotheses of `m1_mollified_flux` (deterministic
core, `d = 2`, `n = 0`): the identity field on `□_1`, the tent mollifier, the base point `0 ∈ □_0`,
and a weak solution of `-Δu = 1`; the three mollified estimates hold for these data. -/
example : ∃ (η : Vec 2 → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) ∧ LipschitzWith L η ∧
    (∀ w, (∃ i, 1 < |w i|) → η w = 0) ∧ η 0 = 1 ∧
    ∃ (u : H1Function (openCubeSet (originCube 2 ((0 + 1 : ℕ) : ℤ)))) (f : Vec 2 → ℝ),
      f = (fun _ => 1) ∧
      IsWeakSolutionOn (fun _ => (1 : Mat 2)) (openCubeSet (originCube 2 ((0 + 1 : ℕ) : ℤ)))
        u f (fun _ => 0) ∧
      ‖a16_mollify 2 ((3 : ℝ) ^ ((0 : ℕ) : ℤ)) η
          (fun y => matVecMul ((fun _ => (1 : Mat 2)) y) (u.grad y)) 0‖ ≤
        3 ^ 2 * (6 * (L : ℝ) + A) *
          Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube 2 ((0 + 1 : ℕ) : ℤ)) (1 / 4)
            (fun y => matVecMul ((fun _ => (1 : Mat 2)) y - (0 : ℝ) • (1 : Mat 2)) (u.grad y)) +
        0 * (3 ^ 2 * (6 * (L : ℝ) + A) *
          Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube 2 ((0 + 1 : ℕ) : ℤ)) (1 / 4) u.grad) := by
  obtain ⟨η, A, L, hA, hL, hη, h0⟩ := a16_exists_profile 2
  have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 ((0 + 1 : ℕ) : ℤ)))) :=
    ⟨by
      simpa only [volumeMeasureOn, zero_add, Nat.cast_one, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using
        (isBounded_openCubeSet (originCube 2 ((0 + 1 : ℕ) : ℤ))).measure_lt_top⟩
  obtain ⟨u, hu, -⟩ := w0_dirichlet_exists (U := openCubeSet (originCube 2 ((0 + 1 : ℕ) : ℤ)))
    (isOpen_openCubeSet _) (isBoundedDomain_openCubeSet _)
    (Section6.ew1_ellip _ (measurableSet_openCubeSet _)) (f := fun _ => (1 : ℝ)) (memLp_const 1) 0
  refine ⟨η, A, L, hA, hL, hη, h0, u, fun _ => 1, rfl, hu, ?_⟩
  refine m1_mollify_fullflux_le 0 hA hL hη ?_ (Section6.ew1_ellip _ (measurableSet_openCubeSet _))
    (le_refl (0 : ℝ)) u
  rw [mem_cubeSet_originCube_iff]
  intro i
  simp only [Pi.zero_apply]
  constructor <;> norm_num

end SuperdiffusionCLT.Section7
