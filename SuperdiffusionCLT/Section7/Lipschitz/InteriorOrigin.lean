/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InteriorOriginB
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorOriginC
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarmC
public import SuperdiffusionCLT.Section7.Lipschitz.SigmaWindow
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section7.MinimalScale.Translate
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section6.Prereq.GammaMax
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
# The interior Lipschitz estimate in the frame of the centre

Assembly of the interior engine with the `L²` block on the rounded cubes, the Caccioppoli block
and the window of `σ̄`.  The `L²` proposition, the interior Caccioppoli estimate and the harmonic
approximation from the `L²` block enter as hypotheses `hL2`, `hCA`, `hHarm`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **C1c — the interior estimate in the frame of the centre** (assembly of the interior engine
with `l2_prop` on the rounded cubes, `ca_interior` and the window of `σ̄`). -/
theorem lip_interior_origin (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
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
        ENNReal.ofReal ((m : ℝ) ^ ρ))
    (hS5 :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∃ M : ℕ,
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∀ m : ℕ, M ≤ m →
        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K))
    (hL2 :
        ∀ (r' M₁' M₂' D' : ℝ) (A : ℕ),
            ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
              ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
                (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
                ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
                ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ,
                  X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ k → Lhat ≤ (k : ℝ) →
                  ∀ V : Set (Vec d), V ⊆ Section6.engCube d k →
                    IsUniformC11Domain (((3 : ℝ) ^ k)⁻¹ • V) r' M₁' M₂' D' →
                    LipL2Block
                      (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
                      (sigmaBarInfinite nu k P) (deltaScale ε ρ (k : ℝ)) C A k V )
    (hCA :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
              ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
              ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
                (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
                ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
                ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ,
                  X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ k → Lhat ≤ (k : ℝ) →
                  LipCaccInt
                    (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
                    (sigmaBarInfinite nu k P) C 1 k) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ m n : ℕ, n < m →
          ((m : ℝ) - (n : ℝ)) * deltaScale ε ρ (m : ℝ) ≤ c → Lhat ≤ (n : ℝ) →
          X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ n →
          LipIntAt (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
            nu (sigmaBarInfinite nu m P) C 0 n m  := by
  have _hI := hInputs
  obtain ⟨N, r, M₁, M₂, D, hr, hfam⟩ := lip_interior_origin_family (d := d)
  obtain ⟨CL2, hCL2, hL2'⟩ := hL2 (1 / 2 * r) M₁ (M₂ / (1 / 2)) (1 / 2 * D) 3
  obtain ⟨CCA, hCCA, hCA'⟩ := hCA
  have hCin0 : 1 ≤ 2 * max CL2 CCA := by
    have := le_max_left CL2 CCA
    linarith only [this, hCL2]
  obtain ⟨CH, hCH, hH⟩ := lip_int_harm_of_l2 d hd (2 * max CL2 CCA) hCin0 3
  have hCin : 1 ≤ max (4 * CH) (2 * CCA) := le_trans (by linarith only [hCH]) (le_max_left _ _)
  obtain ⟨Cc, cc, k₀, hCc, hcc, hcore⟩ :=
    lip_interior_origin_core d (max (4 * CH) (2 * CCA)) hCin
  refine ⟨Cc, cc / 2, hCc, by positivity, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨Lh2, hLh2, hL2P⟩ := hL2' nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨LhA, hLhA, hCAP⟩ := hCA' nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨Ls, hLs⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar K
  obtain ⟨Lw, hLw, hwin⟩ := window_consequences (cc / 2) ε ρ (by positivity) hε hρ.le hρ1.le
  obtain ⟨Lt, hLt, hthr⟩ := lip_interior_origin_thresh ε ρ nu hε hρ.le hnu
  obtain ⟨Cg, hCg0, hCg⟩ := Section6.exists_isBigO_gammaSigma_max_two_add hρ
  refine ⟨max (max Lh2 LhA) (max (Cg * (Lh2 + LhA)) (max (Ls : ℝ) (max Lw (max Lt
    ((k₀ : ℝ) + 2))))), le_trans hLh2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xa, hXam, hXa1, hXaO, hXaP⟩ := hL2P P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xb, hXbm, hXb1, hXbO, hXbP⟩ := hCAP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hLs' := hLs P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun ω => max (Xa ω) (Xb ω), hXam.max hXbm,
    fun ω => le_trans (hXa1 ω) (le_max_left _ _), ?_, ?_⟩
  · have hlog : (fun ω => Real.log (max (Xa ω) (Xb ω))) =
        fun ω => max (Real.log (Xa ω)) (Real.log (Xb ω)) := by
      funext ω
      rcases le_total (Xa ω) (Xb ω) with h | h
      · rw [max_eq_right h, max_eq_right (Real.log_le_log (by linarith only [hXa1 ω]) h)]
      · rw [max_eq_left h, max_eq_left (Real.log_le_log (by linarith only [hXb1 ω]) h)]
    rw [hlog]
    refine (hCg (by linarith only [hLh2]) (by linarith only [hLhA]) hXaO hXbO).mono_scale ?_
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro y
    have hell := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving.ae
      (w0_ae_isElliptic_bounded hJ3 hnu)
    filter_upwards [hXaP y, hXbP y, hell] with ω hA hB hE
    intro m n hnm hsmall hLn hX
    generalize Section6.fullCoefficientRecentered nu (ShellField.translateSequence y ω) = a
      at hA hB hE ⊢
    have hXa : Xa (ShellField.translateSequence y ω) ≤ (3 : ℝ) ^ n := le_trans (le_max_left _ _) hX
    have hXb : Xb (ShellField.translateSequence y ω) ≤ (3 : ℝ) ^ n := le_trans (le_max_right _ _) hX
    have hLn1 : Lh2 ≤ (n : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLn
    have hLn2 : LhA ≤ (n : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLn
    have hrest : ∀ L : ℝ, L ≤ max (Cg * (Lh2 + LhA)) (max (Ls : ℝ) (max Lw (max Lt ((k₀ : ℝ) + 2)))) →
        L ≤ (n : ℝ) := fun L hL => le_trans hL (le_trans (le_max_right _ _) hLn)
    have hLsn : (Ls : ℝ) ≤ n := hrest _ (le_trans (le_max_left _ _) (le_max_right _ _))
    have hLwn : Lw ≤ (n : ℝ) :=
      hrest _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    have hLtn : Lt ≤ (n : ℝ) :=
      hrest _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hk0n : (k₀ : ℝ) + 2 ≤ n :=
      hrest _ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hk0n' : k₀ + 2 ≤ n := by exact_mod_cast hk0n
    have hn5 : (5 : ℝ) ≤ n := le_trans hLt hLtn
    have hn5' : 5 ≤ n := by exact_mod_cast hn5
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm.le
    have hδm : 0 < deltaScale ε ρ (m : ℝ) := deltaScale_pos hε (by linarith only [hn5, hnm'])
    have hwin' : (m : ℝ) - n ≤ (cc / 2) * (deltaScale ε ρ (m : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hδm]; exact hsmall
    obtain ⟨hhalf, hn2, -, -, -⟩ := hwin (m : ℝ) (n : ℝ) (le_trans hLwn hnm') hnm' hwin'
    have hm2n : m ≤ 2 * n := by
      have : (m : ℝ) ≤ 2 * n := by linarith only [hhalf]
      exact_mod_cast this
    have hδk : ∀ k : ℕ, n ≤ k → k ≤ m → 0 ≤ deltaScale ε ρ (k : ℝ) ∧
        deltaScale ε ρ (k : ℝ) ≤ 2 * deltaScale ε ρ (m : ℝ) := by
      intro k h1 h2
      have h1' : (n : ℝ) ≤ k := by exact_mod_cast h1
      have h2' : (k : ℝ) ≤ m := by exact_mod_cast h2
      refine ⟨(deltaScale_pos hε (by linarith only [hn5, h1'])).le, ?_⟩
      exact deltaScale_le_two_mul ε ρ hε.le hρ.le hρ1.le (by linarith only [hn2, h1'])
        (by linarith only [hhalf, h1']) h2'
    have hsum : ∑ k ∈ Finset.Icc (n + 1) m, deltaScale ε ρ (k : ℝ) ≤ cc := by
      have h1 : ∑ k ∈ Finset.Icc (n + 1) m, deltaScale ε ρ (k : ℝ) ≤
          ∑ _k ∈ Finset.Icc (n + 1) m, 2 * deltaScale ε ρ (m : ℝ) :=
        Finset.sum_le_sum fun k hk => by
          rw [Finset.mem_Icc] at hk
          exact (hδk k (by omega) hk.2).2
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_add_right,
        Nat.cast_sub hnm.le] at h1
      linarith only [h1, hsmall]
    have hsw : ∀ k₁ k₂ : ℕ, n ≤ k₁ → k₁ ≤ k₂ → k₂ ≤ m →
        1 ≤ sigmaBarInfinite nu k₁ P ∧ sigmaBarInfinite nu k₁ P ≤ (k₁ : ℝ) ∧
          sigmaBarInfinite nu k₂ P ≤ 2 * sigmaBarInfinite nu k₁ P ∧
          sigmaBarInfinite nu k₁ P ≤ 2 * sigmaBarInfinite nu k₂ P := by
      intro k₁ k₂ h1 h2 h3
      refine hLs' k₁ k₂ ?_ h2 (by omega)
      have : (Ls : ℝ) ≤ k₁ := le_trans hLsn (by exact_mod_cast h1)
      exact_mod_cast this
    have hCinm : max (4 * CH) (2 * CCA) ≥ 2 * CCA := le_max_right _ _
    have hblk : ∀ k, n + 1 ≤ k → k ≤ m →
        LipCaccInt a nu (sigmaBarInfinite nu k P) (max (4 * CH) (2 * CCA)) 1 k ∧
          LipHarmInt a (sigmaBarInfinite nu k P) (deltaScale ε ρ (k : ℝ))
            (max (4 * CH) (2 * CCA)) k := by
      intro k hk1 hk2
      obtain ⟨hs1, hsk, -, -⟩ := hsw k k (by omega) le_rfl hk2
      have hspos : 0 < sigmaBarInfinite nu k P := by linarith only [hs1]
      have hkn : (n : ℝ) ≤ k := by exact_mod_cast (by omega : n ≤ k)
      have hkn1 : (n : ℝ) + 1 ≤ k := by exact_mod_cast hk1
      have hCAk : LipCaccInt a nu (sigmaBarInfinite nu k P) CCA 1 k :=
        hB k (le_trans hXb (pow_le_pow_right₀ (by norm_num) (by omega)))
          (by linarith only [hLn2, hkn])
      refine ⟨hCAk.mono hspos (by linarith only [hspos]) (by linarith only [hspos])
        (by linarith only [hCCA]) hCinm, ?_⟩
      have hk1' : 1 ≤ k - 1 := by omega
      obtain ⟨hVo, hV2, hV1, hVu⟩ := hfam (k - 1) hk1'
      have hcast : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hL2k : LipL2Block a nu (sigmaBarInfinite nu (k - 1) P)
          (deltaScale ε ρ (((k - 1 : ℕ)) : ℝ)) CL2 3 (k - 1) (g1_V d N (k - 1) 0) :=
        hA (k - 1) (le_trans hXa (pow_le_pow_right₀ (by norm_num) (by omega)))
          (by rw [hcast]; linarith only [hLn1, hkn1]) _ hV2 hVu
      have e : k - 1 - 1 = k - 2 := by omega
      rw [e] at hV1
      obtain ⟨Lam, hLam⟩ := hE (Section6.engCube d k) (by
        rw [lip_interior_origin_engCube_eq_ball]; exact Metric.isBounded_ball)
        (isOpen_openCubeSet _).measurableSet
      obtain ⟨hs1', hsk', h10, h01⟩ := hsw (k - 1) k (by omega) (by omega) hk2
      have hs0pos : 0 < sigmaBarInfinite nu (k - 1) P := by linarith only [hs1']
      have hkL : Lt ≤ (k : ℝ) := le_trans hLtn hkn
      have hk1r : (1 : ℝ) ≤ k := by linarith only [hn5, hkn]
      have hth := hthr k (sigmaBarInfinite nu (k - 1) P) hkL hs1'
        (by rw [hcast] at hsk'; linarith only [hsk'])
      have hδ0 : 0 ≤ deltaScale ε ρ (((k - 1 : ℕ)) : ℝ) := by
        refine (deltaScale_pos hε ?_).le
        rw [hcast]; linarith only [hn5, hkn]
      have hδ10 : deltaScale ε ρ (((k - 1 : ℕ)) : ℝ) ≤ 2 * deltaScale ε ρ (k : ℝ) := by
        refine deltaScale_le_two_mul ε ρ hε.le hρ.le hρ1.le (by rw [hcast]; linarith only [hn5, hkn])
          (by rw [hcast]; linarith only [hn5, hkn]) (by rw [hcast]; linarith only)
      have hh := lip_interior_origin_harm_step hCL2 hCCA hH (by linarith only [hCH]) a nu
        (sigmaBarInfinite nu (k - 1) P) (sigmaBarInfinite nu k P)
        (deltaScale ε ρ (((k - 1 : ℕ)) : ℝ)) (deltaScale ε ρ (k : ℝ)) nu Lam k
        (g1_V d N (k - 1) 0) hnu hs0pos hspos h10 h01 hδ0 hδ10 (by omega) hth.1 hth.2 hVo hV1 hV2
        hLam hnu hL2k hCAk
      exact hh.mono hspos (by linarith only [hspos]) (hδk k (by omega) hk2).1
        (by linarith only [(hδk k (by omega) hk2).1]) (by linarith only [hCH])
        (by linarith only [le_max_left (4 * CH) (2 * CCA)])
    exact hcore a nu (fun k => sigmaBarInfinite nu k P) (fun k => deltaScale ε ρ (k : ℝ)) n m hnu
      hk0n' hnm
      (fun k h1 h2 => by
        obtain ⟨a1, -, a3, a4⟩ := hsw k m h1 h2 le_rfl
        exact ⟨by linarith only [a1], a3, a4⟩)
      (fun k h1 h2 => (hδk k h1 h2).1) hsum hblk

end SuperdiffusionCLT.Section7
