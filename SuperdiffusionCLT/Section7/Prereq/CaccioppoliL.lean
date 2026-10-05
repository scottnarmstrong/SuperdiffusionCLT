/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliK
public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section6.Engine.FieldAE

/-!
# The interior superdiffusive Caccioppoli inequality, almost-sure form

`ca_interior`: for the recentered field of every translated sample `τ_y ω`, almost surely and for
every scale `k` with `X₀(τ_y ω) ≤ 3^k` and `L̂ ≤ k`, the block `LipCaccInt` holds with loss of one
scale.  The inputs are the statements `sharp_scale_inputs` (`hInputs`) and
`sigmaBar_sharp_bounds` (`hS5`).
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

/-- **`e.Dir.new.Cacc.interior`**, in the frame of the centre. -/
theorem ca_interior (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) :
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
            (sigmaBarInfinite nu k P) C 1 k := by
  obtain ⟨Cb, hCb, H⟩ := b2_translated_inputs d hInputs
  obtain ⟨Cd, hCd0, hstep⟩ := r1_step hd
  obtain ⟨CS, hCS, HS⟩ := hS5
  have hC1 : 1 ≤ max Cb Cd := le_trans hCb (le_max_left _ _)
  have hCfin : 0 ≤ max (ca1_Cfin d (4 * (max Cb Cd) ^ 2)) 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨Real.sqrt (max (ca1_Cfin d (4 * (max Cb Cd) ^ 2)) 1),
    Real.one_le_sqrt.2 (le_max_right _ _), ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨M0, hM0⟩ := scale_separation_ceil 4 1 1 (by norm_num) one_pos
  obtain ⟨L0, hL0, hsep⟩ := hM0 nu 1 hnu one_pos
  obtain ⟨Lhat0, hLhat0, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ (max (max Cb M0) 1) hε hε1 hρ hρ1
    (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨MS, hMS⟩ := HS nu hnu hnu1 cStar hcStar K
  obtain ⟨Lw, hLw1, hLw⟩ := ca1w_sigma_window cStar CS K hcStar hCS
  obtain ⟨Lg, hLg1, hLg⟩ := ca1w_log_le_rpow ((1 - ρ) / 2) (by linarith only [hρ1])
  obtain ⟨Lc, hLc1, hLc⟩ := ceil_log_le_mul (max (max Cb M0) 1) 1 one_pos
  refine ⟨max Lhat0 (max Lw (max Lg (max Lc (max L0 (max (1 + 4 * (d : ℝ))
    (max (5 * (max Cb Cd) ^ 2) (max (MS : ℝ) 21))))))), le_trans hLhat0 (le_max_left _ _), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hXm, hX1, hXO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hXm, hX1, hXO.mono_scale (le_max_left _ _), fun y => ?_⟩
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [hae y, hqmp.ae (Section6.l9_ae_exists_ell_centered hJ3 hnu),
    hqmp.ae (Section6.eng_ae_field d hJ3 hnu), ca1w_ae_continuous hPrefix hJ2 hJ3 nu y,
    w0_ae_isWeakSolutionOn_translateSet_iff_recentered hPrefix hJ2 hJ3 nu y]
    with omega hω hell heng hcont hbr m hX hLm
  obtain ⟨hLm0, hLmw, hLmg, hLmc, hLm0', hLm1, hLm5, hLmS, hLm21⟩ : Lhat0 ≤ (m : ℝ) ∧ Lw ≤ (m : ℝ) ∧
      Lg ≤ (m : ℝ) ∧ Lc ≤ (m : ℝ) ∧ L0 ≤ (m : ℝ) ∧ 1 + 4 * (d : ℝ) ≤ (m : ℝ) ∧
      5 * (max Cb Cd) ^ 2 ≤ (m : ℝ) ∧ (MS : ℝ) ≤ (m : ℝ) ∧ (21 : ℝ) ≤ (m : ℝ) := by
    simpa only [max_le_iff] using hLm
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm1 : (1 : ℝ) ≤ m := by linarith only [hLm21]
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hMge : (1 : ℝ) ≤ max (max Cb M0) 1 := le_max_right _ _
  -- the grid depth
  have hlog3 : (3 : ℝ) ≤ Real.log m := by
    have h1 : (3 : ℝ) ≤ Real.log 21 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      have h4 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ this (Real.exp_pos 1).le (by norm_num)
      have h5 : (2.7182818286 : ℝ) ^ 3 ≤ 21 := by norm_num
      linarith only [h4, h5]
    exact h1.trans (Real.log_le_log (by norm_num) hLm21)
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ, (h : ℤ) = ⌈max (max Cb M0) 1 * Real.log m⌉ := by
    refine ⟨(⌈max (max Cb M0) 1 * Real.log m⌉).toNat, ?_⟩
    refine Int.toNat_of_nonneg ?_
    have hM0' : 0 ≤ max (max Cb M0) 1 := by linarith only [hMge]
    have hlg : 0 ≤ Real.log m := by linarith only [hlog3]
    exact Int.ceil_nonneg (mul_nonneg hM0' hlg)
  have hh3 : 3 ≤ h := by
    have : (3 : ℝ) ≤ (h : ℝ) := by
      have h1 : (h : ℝ) = (⌈max (max Cb M0) 1 * Real.log m⌉ : ℝ) := by
        rw [← hhdef]; simp
      rw [h1]
      refine le_trans ?_ (Int.le_ceil _)
      nlinarith only [hMge, hlog3]
    exact_mod_cast this
  have hhm : h ≤ m := by
    have h1 : (h : ℝ) = (⌈max (max Cb M0) 1 * Real.log m⌉ : ℝ) := by
      rw [← hhdef]; simp
    have h2 := hLc m hLmc
    have : (h : ℝ) ≤ m := by rw [h1]; linarith only [h2]
    exact_mod_cast this
  obtain ⟨n, hnh⟩ : ∃ n : ℕ, n + h = m := ⟨m - h, Nat.sub_add_cancel hhm⟩
  have hn1 : (m : ℤ) - ⌈max (max Cb M0) 1 * Real.log m⌉ ≤ (n : ℤ) := by
    rw [← hhdef]
    have : (m : ℤ) = n + h := by exact_mod_cast hnh.symm
    omega
  have hn2 : n ≤ m := by omega
  obtain ⟨hA, hkb⟩ := hω m n hX hLm0 hn1 hn2
  -- the diffusivity window
  have hσ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  have hSwin := hLw (m : ℝ) (sigmaBarInfinite nu m P) hLmw
    (hMS P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 m (by exact_mod_cast hLmS))
  -- the small parameter
  have hlg : 0 ≤ Real.log m := by linarith only [hlog3]
  have hδ0 : 0 ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m :=
    mul_nonneg (mul_nonneg hε.le (Real.rpow_nonneg hm0.le _)) hlg
  have hδ1 : ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m ≤ 1 := by
    have h1 := hLg (m : ℝ) hLmg
    have h2 : (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m ≤ 1 := by
      calc (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m ≤ (m : ℝ) ^ (-((1 - ρ) / 2)) * (m : ℝ) ^ ((1 - ρ) / 2) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hm0.le _)
        _ = 1 := by
            rw [← Real.rpow_add hm0]; simp
    have h3 : 0 ≤ (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m := mul_nonneg (Real.rpow_nonneg hm0.le _) hlg
    calc ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m = ε * ((m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log m) := by ring
      _ ≤ 1 * 1 := mul_le_mul hε1 h2 h3 zero_le_one
      _ = 1 := one_mul 1
  -- scale separation
  have hmaster : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) * ((m : ℝ) / nu) ^ 4 ≤ (m : ℝ)⁻¹ := by
    have hwin : ((n : ℤ) : ℝ) ≤ (m : ℝ) - ⌈max (max Cb M0) 1 * Real.log m⌉ := by
      have h1 : (h : ℝ) = (⌈max (max Cb M0) 1 * Real.log m⌉ : ℝ) := by
        rw [← hhdef]; simp
      have h2 : (n : ℝ) + h = m := by exact_mod_cast hnh
      have h3 : (((n : ℤ) : ℝ)) = (n : ℝ) := by simp
      rw [h3]
      linarith only [h1, h2]
    exact ca1w_master_conv hnu (hsep _ (le_trans (le_max_right _ _) (le_max_left _ _)) (m : ℝ) (n : ℤ) 1
      hLm0' zero_le_one (by linarith only [hm1]) hwin)
  -- the field
  obtain ⟨kf, hkfdef⟩ : ∃ kf : Vec d → Mat d, kf = fun x =>
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (translateSet y (cubeSet (originCube d (m : ℤ)))) x := ⟨_, rfl⟩
  have hsymm : ∀ x, symmPart (nu • (1 : Mat d) + kf x) = nu • (1 : Mat d) := by
    intro x
    rw [hkfdef]
    exact Section6.HarmonicApprox.symmPart_centeredStreamField_add nu omega _ x
  have hfield : ∀ x, SuperdiffusionCLT.Section2.Carriers.centeredStreamField
      (ShellField.translateSequence y omega) (cubeSet (originCube d (m : ℤ))) x = kf (y + x) := by
    intro x
    rw [hkfdef]
    exact b2_csf_translate_apply y omega _ x
  have hellA : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m : ℤ)))
      (fun x => nu • (1 : Mat d) + kf (y + x)) := by
    obtain ⟨lam, Lam, hl⟩ := hell m m 0
    refine ⟨lam, Lam, ?_⟩
    have hl' := hl.mono (isOpen_openCubeSet _).measurableSet (openCubeSet_subset_cubeSet _)
    simpa only [zero_add, hfield] using hl'
  have hcontA : Continuous (fun x => kf (y + x)) := by
    have := hcont m
    simpa only [hfield] using this
  have hbd : ∀ x ∈ openCubeSet (originCube d (m : ℤ)),
      Book.Ch02.matrixOperatorNorm (kf (y + x)) ≤ (m : ℝ) ^ (1 + ρ) := by
    have hae' := r1_ae_opnorm_k (originCube d (m : ℤ)) (g := fun x => kf (y + x)) hm1 _
      (by rw [hkfdef]; exact hkb)
    exact ca1w_opnorm_pointwise _ hcontA hae'
  have hop : ∀ x ∈ openCubeSet (originCube d (m : ℤ)), ∀ v : Vec d,
      eucNorm (matVecMul (nu • (1 : Mat d) + kf (y + x)) v) ≤ (nu + (m : ℝ) ^ (1 + ρ)) * eucNorm v :=
    fun x hx v => ca1w_hop hnu.le (kf (y + x)) (hbd x hx) v
  have hνS : nu ≤ sigmaBarInfinite nu m P := by linarith only [hSwin.1, hnu1]
  have hflux : ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
        (fun x => matVecMul (Section6.fullCoefficientRecentered nu
          (ShellField.translateSequence y omega) x) (u.grad x)) := by
    intro u
    obtain ⟨lam, Lam, hE⟩ := heng.2.1 m
    exact memVectorL2_matVecMul_of_isEllipticFieldOn hE (MemLp.of_eval fun i => u.gradMemL2 i)
  have hfinU : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))) :=
    ⟨by
      simpa only [volumeMeasureOn, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using
        (isBounded_openCubeSet (originCube d (m : ℤ))).measure_lt_top⟩
  refine ca1w_lip_of_core (A := fun x => nu • (1 : Mat d) + kf (x + y))
    (Cf := ca1_Cfin d (4 * (max Cb Cd) ^ 2)) m (by exact_mod_cast hm1)
    hσ hnu (Real.one_le_sqrt.2 (le_max_right _ _)) ?_ hflux ?_ ?_
  · rw [Real.sq_sqrt hCfin]
    exact le_max_left _ _
  · intro u f hfl hu
    rw [hkfdef]
    exact (hbr m (isOpen_openCubeSet _) hfinU u f _ hfl).2 hu
  · intro u f hf hu'
    have e : (fun x : Vec d => nu • (1 : Mat d) + kf (x + y)) =
        fun x => nu • (1 : Mat d) + kf (y + x) := funext fun x => by rw [add_comm x y]
    rw [e] at hu'
    refine ca1w_scale hd m n h hnh hh3 kf y hC1 hnu hnu1 hνS hSwin.2 hρ1.le hδ0 hδ1 hLm1 hLm5 hmaster
      hellA hsymm hop ?_ u hf hu' _
    intro k' himg u f hu
    obtain ⟨-, -, hbul, -⟩ := hA k' himg
    obtain ⟨lam, Lam, hl⟩ := hell m n (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k' i : ℝ))
    subst hkfdef
    have hl' : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
        (fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (translateSet y (cubeSet (originCube d (m : ℤ))))
          (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k' i : ℝ)) + x)) := by
      refine ⟨lam, Lam, ?_⟩
      have hfun : (fun x => nu • (1 : Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField (ShellField.translateSequence y omega)
            (cubeSet (originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k' i : ℝ)) + x)) =
          fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (translateSet y (cubeSet (originCube d (m : ℤ))))
            (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k' i : ℝ)) + x) := by
        funext x
        rw [b2_csf_translate_apply, b2_add_assoc_aux]
      rw [hfun] at hl
      exact hl
    exact hstep (max Cb Cd) Cb (le_max_left _ _) (le_max_right _ _) nu ε ρ _ m n _ y _ hnu hε hm1 hσ hCb
      hsymm hl' himg _ hkb (fun v => ⟨(hbul v).1, (hbul v).2.1⟩) u f hu

/-- **Satisfiability witness.** The block `LipCaccInt` holds for the identity field of `ℝ²`
(`ν = s = 1`) at the scale `3`, so the conclusion of `ca_interior` speaks about a non-empty class of
solutions. -/example : ∃ C : ℝ, 1 ≤ C ∧ LipCaccInt (fun _ : Vec 2 => (1 : Mat 2)) 1 1 C 1 3 := by
  obtain ⟨K, hK, hD⟩ := r1_ofReal_dual_le 2
  have hz : ∀ (R : TriadicCube 2) (u' : H1Function (openCubeSet (originCube 2 R.scale))) (x : Vec 2),
      matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) x - (1 : ℝ) • (1 : Mat 2)) (u'.grad x) = (0 : Vec 2) := by
    intro R u' x; funext i; simp [matVecMul]
  have hBB : ∀ R ∈ descendantsAtDepth (originCube 2 ((3 : ℕ) : ℤ)) 3,
      ∀ (u' : H1Function (openCubeSet (originCube 2 R.scale))) (f' : Vec 2 → ℝ),
      IsWeakSolutionOn (fun x => (fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift R))
        (openCubeSet (originCube 2 R.scale)) u' f' (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube 2 R.scale)
          (1 / 4 : ℝ) (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift R) -
            (1 : ℝ) • (1 : Mat 2)) (u'.grad x))) ≤
        ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale)
            (ENNReal.ofReal (sobStar 2)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube 2 R.scale)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale)
            (ENNReal.ofReal (sobStar 2)).conjExponent f' := by
    intro R _ u' f' _
    refine ⟨?_, ?_⟩
    · have e : (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift R) -
          (1 : ℝ) • (1 : Mat 2)) (u'.grad x)) = fun _ => (0 : Vec 2) := by
        funext x i; simp [matVecMul]
      rw [e]
      refine le_trans (hD _ (fun _ => (0 : Vec 2)) (fun i => memLp_const 0)
        (by simp [vecNormSq, vecDot])) ?_
      simp [SuperdiffusionCLT.Section2.Norms.cubeLpENorm, vecNormSq, vecDot]
    · refine le_trans (hD _ u'.grad (r1_memLp_grad_comp _ u') (r1_memLp_grad_eucNorm _ u')) ?_
      simp
  have hcore : ∀ (u : H1Function (openCubeSet (originCube 2 ((3 : ℕ) : ℤ)))) (f : Vec 2 → ℝ),
      MemLp f 2 (volume.restrict (openCubeSet (originCube 2 ((3 : ℕ) : ℤ)))) →
      IsWeakSolutionOn (fun _ : Vec 2 => (1 : Mat 2)) (openCubeSet (originCube 2 ((3 : ℕ) : ℤ))) u f
        (fun _ => 0) →
      (1 : ℝ) * cubeLpNorm (originCube 2 (((3 : ℕ) : ℤ) - 1)) (2 : ℝ≥0∞)
          (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
        ca1_Cfin 2 (K ^ 2) * ((1 : ℝ) * (3 : ℝ) ^ (-2 * ((3 : ℕ) : ℤ)) *
            cubeLpNorm (originCube 2 ((3 : ℕ) : ℤ)) (2 : ℝ≥0∞)
              (fun x => u.toFun x - cubeAverage (originCube 2 ((3 : ℕ) : ℤ)) u.toFun) ^ 2 +
          (1 : ℝ)⁻¹ * (3 : ℝ) ^ (2 * ((3 : ℕ) : ℤ)) *
            cubeLpNorm (originCube 2 ((3 : ℕ) : ℤ)) (2 : ℝ≥0∞) f ^ 2) := by
    intro u f hf hu
    exact ca1_interior_det (d := 2) (le_refl 2) ((3 : ℕ) : ℤ) 3 (le_refl 3)
      (A := fun _ => (1 : Mat 2)) (lam := 1) (Lam := 1)
      (ν := 1) (Λ := 1) (S := 1) (α1 := 0) (β1 := 0) (α2 := K) (β2 := 0) (Cα := K ^ 2)
      (Section6.ew1_ellip _ (measurableSet_openCubeSet _)) one_pos zero_le_one
      (fun x _ => by
        ext i j
        simp [symmPart, Matrix.one_apply, eq_comm])
      (fun x _ v => by simp [r1_matVecMul_one]) le_rfl le_rfl le_rfl hK le_rfl (sq_nonneg K)
      (by simp) (by norm_num) (by norm_num) (by norm_num) u hf hu hBB _
  refine ⟨Real.sqrt (max (ca1_Cfin 2 (K ^ 2)) 1), Real.one_le_sqrt.2 (le_max_right _ _), ?_⟩
  refine ca1w_lip_of_core (A := fun _ : Vec 2 => (1 : Mat 2)) (Cf := ca1_Cfin 2 (K ^ 2)) 3
    (by norm_num) one_pos one_pos (Real.one_le_sqrt.2 (le_max_right _ _)) ?_ ?_ (fun u f _ hu => hu) hcore
  · rw [Real.sq_sqrt (le_trans zero_le_one (le_max_right _ _))]
    exact le_max_left _ _
  · intro u
    have : (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) x) (u.grad x)) = u.grad := by
      funext x; simp [r1_matVecMul_one]
    rw [this]
    exact MemLp.of_eval fun i => u.gradMemL2 i

end SuperdiffusionCLT.Section7
