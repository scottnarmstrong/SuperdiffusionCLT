/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.Book.Ch03.Definitions
public import SuperdiffusionCLT.Section7.MinimalScale.Translate

/-!
# Sharp-scale inputs on translated ambient cubes

The statement of `Frozen.Section6.sharp_scale_inputs` is for the field centered on the origin cube
`cu_m`.  For a vector `y`, the centered stream carrier of the translated sample `τ_y ω` on `cu_m`
is the carrier of `ω` centered on `translateSet y cu_m = y + cu_m`, read from the base point `y`
(`centeredStreamField_translateSequence`).  The hypothesis `hInputs` is the statement of
`Frozen.Section6.sharp_scale_inputs`; the conclusion is the same statement for every `y`,
with the field `ν Id + centeredStreamField ω (y + cu_m) (y + z + x)` on the origin cube in the
variable `x`, where `z = 3^{n-3} k` is the sub-cube shift of that statement, and with the
scale `X₀ ∘ τ_y`.

Which translations that statement covers by itself: the shifts `z = 3^{n-3} k` of the
bullets, for sub-cubes `z + cu_n ⊆ cu_m` of the ambient cube centered at the origin and with the
field centered on `cu_m`.  It does not cover a different ambient cube `y + cu_m` with the field
centered there, nor the minimal scale `X₀ ∘ τ_y`; those are supplied here, for every `y`.
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open MeasureTheory

/-- The carrier of the translated sample, read from the base point `y`. -/
theorem b2_csf_translate_apply {d : ℕ} (y : Homogenization.Vec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (U : Set (Homogenization.Vec d))
    (x : Homogenization.Vec d) :
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) U x =
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.translateSet y U) (y + x) := by
  rw [centeredStreamField_translateSequence, add_comm]

/-- The same identity, as an identity of functions. -/
theorem b2_csf_translate_fun {d : ℕ} (y : Homogenization.Vec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (U : Set (Homogenization.Vec d)) :
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) U =
      fun x => SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.translateSet y U) (y + x) :=
  funext fun x => b2_csf_translate_apply y omega U x

theorem b2_add_assoc_aux {d : ℕ} (y z x : Homogenization.Vec d) : y + (z + x) = y + z + x :=
  (add_assoc y z x).symm

/-- **Translated sharp-scale inputs.**  From the statement of `sharp_scale_inputs` (the
hypothesis `hInputs`), for every vector `y` the bullets hold, almost surely, for the field
`ν Id + centeredStreamField ω (y + cu_m)` read from the base point `y + z`, under the translated
scale `X₀ ∘ τ_y`; `X₀` itself keeps its measurability, lower bound and `Γ_ρ` bound.  The constants
`C` and `L̂` are those of `hInputs`. -/
theorem b2_translated_inputs (d : ℕ) [NeZero d]
    (hInputs :
      ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ, 0
        < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
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
        omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0 omega
        ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m → (∀ k :
        Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
        d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
        x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 : Homogenization.Mat
        d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ)
        - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1 :
        Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ)
        - 3) * (k i : ℝ)) + x) - SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 -
        ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C * (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ∃ w :
        Homogenization.AHarmonicFunction (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) - 1))), ENNReal.ofReal ((3
        : ℝ) ^ (-(n : ℝ))) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
        Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        - 1) + Homogenization.matNorm ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
        m P)⁻¹ • Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d
        (n : ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m : ℝ)⁻¹)
        * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m : ℤ)) ∞
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m :
        ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm (Homogenization.originCube d
        (m : ℤ)) (1 / 4) 2 (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ) ^
        ρ)) :
  ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ, 0 < ε
    → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : MeasureTheory.ProbabilityMeasure
    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (hPrefix :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
    SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
    Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma ρ)
    (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ y : Homogenization.Vec d, ∀ᵐ omega :
    SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ m →
    Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m → (∀ k : Fin d → ℤ, (fun x
    => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) '' Homogenization.cubeSet
    (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet (Homogenization.originCube d (m :
    ℤ)) → Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) (1 / 9)
    Homogenization.MultiscaleExponent.infinity (Homogenization.MultiscaleExponent.finite 2) (fun x
    => nu • (1 : Homogenization.Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ ((n :
    ℤ) - 3) * (k i : ℝ)) + x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
    (1 : Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Homogenization.LambdaSq
    (Homogenization.originCube d (n : ℤ)) (1 / 4) (Homogenization.MultiscaleExponent.finite 1) (fun
    x => nu • (1 : Homogenization.Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ ((n :
    ℤ) - 3) * (k i : ℝ)) + x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
    (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
    (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ ((n :
    ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
    Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
    (Homogenization.translateSet y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))))
    (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet
    (Homogenization.originCube d (n : ℤ))), ENNReal.ofReal
    (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1 :
    Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
    (Homogenization.translateSet y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))))
    (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat d))
    (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) /
    2)) * Real.log (m : ℝ)) * Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
    (u.toH1.grad x))) ∧ ENNReal.ofReal
    (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C * (Real.sqrt
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2 (fun x
    => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ∃ w :
    Homogenization.AHarmonicFunction (fun _ => (1 : Homogenization.Mat d))
    (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) - 1))), ENNReal.ofReal ((3 :
    ℝ) ^ (-(n : ℝ))) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube
    d ((n : ℤ) - 1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ)
    ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2 (fun x
    => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
    ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
    Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) (fun x
    => nu • (1 : Homogenization.Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ ((n :
    ℤ) - 3) * (k i : ℝ)) + x)) - 1) + Homogenization.matNorm
    ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
    Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
    (fun x => nu • (1 : Homogenization.Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ ((n :
    ℤ) - 3) * (k i : ℝ)) + x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
    ENNReal.ofReal ((m : ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (Homogenization.originCube d (m : ℤ)) ∞ ((fun x =>
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + x))) + ENNReal.ofReal ((3
    : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
    (Homogenization.originCube d (m : ℤ)) (1 / 4) 2 ((fun x =>
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + x))) ≤ ENNReal.ofReal ((m
    : ℝ) ^ ρ) := by
  obtain ⟨C, hC, H⟩ := hInputs
  refine ⟨C, hC, ?_⟩
  intro nu hnu hnu1 cStar hcStar K eps rho M heps heps1 hrho hrho1 hCM
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K eps rho M heps heps1 hrho hrho1 hCM
  refine ⟨Lhat, hL, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, fun y => ?_⟩
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [hqmp.ae hae] with omega hω m n hX hLm hn1 hn2
  obtain ⟨hA, hB⟩ := hω m n hX hLm hn1 hn2
  refine ⟨fun k hk => ?_, ?_⟩
  · have hfield : (fun x : Homogenization.Vec d => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField
            (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega)
            (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) =
        fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (Homogenization.translateSet y
              (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))))
            (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) := by
      funext x
      rw [b2_csf_translate_apply, b2_add_assoc_aux]
    have hAk := hA k hk
    rw [hfield] at hAk
    simpa only [b2_csf_translate_apply, b2_csf_translate_fun, b2_add_assoc_aux] using hAk
  · simpa only [b2_csf_translate_apply, b2_csf_translate_fun, b2_add_assoc_aux] using hB

end SuperdiffusionCLT.Section7
