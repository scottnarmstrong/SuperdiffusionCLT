/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryW
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliK
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliE
public import SuperdiffusionCLT.Section7.Lipschitz.CarriersS
public import SuperdiffusionCLT.Section7.Prereq.Domains
public import SuperdiffusionCLT.Section7.Analytic.Geometry.Atlas
public import SuperdiffusionCLT.Section6.Engine.FieldAE
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance
public import SuperdiffusionCLT.Section7.Analytic.Geometry.WhitneyBallB

/-!
# The boundary superdiffusive Caccioppoli inequality, almost-sure form

`ca_boundary`: for the recentered field of every translated sample `τ_y ω`, almost surely, for every
real dilation `t ≥ 3^j` with `y ∈ t U` and every scale `j` with `X₀(τ_y ω) ≤ 3^j` and `L̂ ≤ j`,
the block `LipCaccBdryS` holds on `(t U - y) ∩ □_j` with loss of one scale and the exponent `E`
(a correction of the printed text; see `ERRATA.md`) for the `C²` datum.  The inputs are the
statements `sharp_scale_inputs` (`hInputs`) and `sigmaBar_sharp_bounds` (`hS5`).
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

theorem ca2w_x_small {d : ℕ} (hd1 : 1 ≤ d) {ν : ℝ} {m n N : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hm1 : (1 : ℝ) ≤ m) (hN1 : 1 ≤ N)
    (hsep : (m : ℝ) ^ (8 : ℝ) * ν ^ (-(8 : ℝ)) * (1 : ℝ) ^ (8 : ℝ) *
      (3 : ℝ) ^ ((1 / (d : ℝ)) * (((n : ℤ) : ℝ) - (m : ℝ))) ≤ ((m : ℝ) ^ N)⁻¹) :
    (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) ≤ (m : ℝ)⁻¹ := by
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  obtain ⟨yy, hyydef⟩ : ∃ yy : ℝ, yy = (3 : ℝ) ^ ((1 / (d : ℝ)) * (((n : ℤ) : ℝ) - (m : ℝ))) := ⟨_, rfl⟩
  have hyy0 : 0 < yy := by rw [hyydef]; positivity
  have hxyy : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) = yy ^ d := by
    rw [hyydef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (1 / (d : ℝ) * (((n : ℤ) : ℝ) - (m : ℝ))) * (d : ℝ) = (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) := by
      push_cast; field_simp
    rw [this, Real.rpow_intCast, zpow_sub₀ (by norm_num), zpow_natCast]
  have hsep' : (m : ℝ) ^ 8 * (ν ^ 8)⁻¹ * yy ≤ ((m : ℝ) ^ N)⁻¹ := by
    have e1 : (m : ℝ) ^ (8 : ℝ) = (m : ℝ) ^ 8 := by exact_mod_cast Real.rpow_natCast (m : ℝ) 8
    have e2 : ν ^ (-(8 : ℝ)) = (ν ^ 8)⁻¹ := by
      rw [Real.rpow_neg hν.le]; congr 1; exact_mod_cast Real.rpow_natCast ν 8
    rw [e1, e2, Real.one_rpow, mul_one, ← hyydef] at hsep
    exact hsep
  have hmN : (m : ℝ) ≤ (m : ℝ) ^ N := by
    calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m : ℝ) ^ N := pow_le_pow_right₀ hm1 hN1
  have hq1 : 1 ≤ (m : ℝ) ^ 8 * (ν ^ 8)⁻¹ := by
    have h1 : 1 ≤ (m : ℝ) ^ 8 := one_le_pow₀ hm1
    have h2 : 1 ≤ (ν ^ 8)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]; exact pow_le_one₀ hν.le hν1
    nlinarith only [h1, h2]
  have hyyN : yy ≤ ((m : ℝ) ^ N)⁻¹ := by
    refine le_trans ?_ hsep'
    calc yy = 1 * yy := (one_mul _).symm
      _ ≤ ((m : ℝ) ^ 8 * (ν ^ 8)⁻¹) * yy := mul_le_mul_of_nonneg_right hq1 hyy0.le
      _ = _ := by ring
  have hyy1 : yy ≤ 1 := by
    refine hyyN.trans ?_
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ hm1
  rw [hxyy]
  refine (pow_le_of_le_one hyy0.le hyy1 (by omega)).trans (hyyN.trans ?_)
  rw [inv_le_inv₀ (by positivity) hm0]
  exact hmN

/-- **`e.Dir.new.Cacc.boundary` in local form**, in the frame of
the centre `y ∈ U_m`, with the exponent `E`. -/
theorem ca_boundary (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    (U : Set (Vec d)) (hU : IsSmoothBoundedDomain U)
    (hU0 : U ⊆ openCubeSet (originCube d 0)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∀ E : ℝ, 0 ≤ E →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ (t : ℝ) (j : ℕ), (3 : ℝ) ^ j ≤ t → y ∈ t • U →
          X0 (ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ j → Lhat ≤ (j : ℝ) →
          LipCaccBdryS
            (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega)) nu
            (sigmaBarInfinite nu j P) C E (translateSet (-y) (t • U)) 0 j := by
  have _hU0 := hU0
  obtain ⟨Cb, hCb, H⟩ := b2_translated_inputs d hInputs
  obtain ⟨Cd, hCd0, hstep⟩ := r1_step hd
  obtain ⟨CS, hCS, HS⟩ := hS5
  obtain ⟨r0, M1, M2, D0, hUu⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  have hr0 : 0 < r0 := hUu.2.1
  have hC1 : 1 ≤ max Cb Cd := le_trans hCb (le_max_left _ _)
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  obtain ⟨cd0, hcd0, hden0⟩ := ca2_density d M1
  have hcden : 0 < cd0 * (min (1 / 6) r0) ^ d := by
    have : 0 < min (1 / 6 : ℝ) r0 := lt_min (by norm_num) hr0
    positivity
  have hρ0 : 0 < min r0 1 := lt_min hr0 one_pos
  have hCth0 : 0 ≤ ca2_Cth d (min r0 1) M1 := ca2_Cth_nonneg d hρ0 M1
  have hCB0 : 0 ≤ ca2_CB d := by
    unfold ca2_CB ca2_C1
    positivity
  obtain ⟨Cth, hCthdef⟩ : ∃ Cth : ℝ, Cth = ca2_Cth d (min r0 1) M1 := ⟨_, rfl⟩
  obtain ⟨cden, hcdendef⟩ : ∃ cden : ℝ, cden = cd0 * (min (1 / 6) r0) ^ d := ⟨_, rfl⟩
  obtain ⟨Kτ, hKτdef⟩ : ∃ Kτ : ℝ, Kτ = max 1 (4 * ca2_CB d * Cth ^ (1 / (d : ℝ))) := ⟨_, rfl⟩
  obtain ⟨Cdet, hCdetdef⟩ : ∃ Cdet : ℝ, Cdet = ca2_Cdet d (4 * (max Cb Cd) ^ 2) := ⟨_, rfl⟩
  have hcden : 0 < cden := by
    have : 0 < min (1 / 6 : ℝ) r0 := lt_min (by norm_num) hr0
    rw [hcdendef]; positivity
  have hρ0 : 0 < min r0 1 := lt_min hr0 one_pos
  have hCth0 : 0 ≤ Cth := by rw [hCthdef]; exact ca2_Cth_nonneg d hρ0 M1
  have hCB0 : 0 ≤ ca2_CB d := by
    unfold ca2_CB ca2_C1
    positivity
  have hKτ1 : 1 ≤ Kτ := by rw [hKτdef]; exact le_max_left _ _
  have hKτdef' : 4 * ca2_CB d * Cth ^ (1 / (d : ℝ)) ≤ Kτ := by rw [hKτdef]; exact le_max_right _ _
  have hCdet0 : 0 ≤ Cdet := by
    rw [hCdetdef]
    unfold ca2_Cdet ca2_Cal ca2_c8
    have hKb := cubeBesovW12EmbeddingConstant_nonneg d
    positivity
  refine ⟨max 1 (Cdet / cden), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 E hE
  obtain ⟨M0, hM0⟩ := scale_separation_ceil 8 (1 / (d : ℝ)) (⌈E⌉₊ + 1) (by norm_num) (by positivity)
  obtain ⟨L0, hL0, hsep⟩ := hM0 nu 1 hnu one_pos
  obtain ⟨Lhat0, hLhat0, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ (max (max Cb M0) 1) hε hε1 hρ hρ1
    (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨MS, hMS⟩ := HS nu hnu hnu1 cStar hcStar K
  obtain ⟨Lw, hLw1, hLw⟩ := ca1w_sigma_window cStar CS K hcStar hCS
  obtain ⟨Lg, hLg1, hLg⟩ := ca1w_log_le_rpow ((1 - ρ) / 2) (by linarith only [hρ1])
  obtain ⟨Lc, hLc1, hLc⟩ := ceil_log_le_mul (max (max Cb M0) 1) 1 one_pos
  obtain ⟨Lx, hLxdef⟩ : ∃ Lx : ℝ, Lx = max (2 / min r0 1) (max Cth (max 1 (Kτ * (1 + 4 * d)))) := ⟨_, rfl⟩
  refine ⟨max Lhat0 (max Lw (max Lg (max Lc (max L0 (max (1 + 4 * (d : ℝ))
    (max (5 * (max Cb Cd) ^ 2) (max (MS : ℝ) (max 21 Lx)))))))), le_trans hLhat0 (le_max_left _ _), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hXm, hX1, hXO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hXm, hX1, hXO.mono_scale (le_max_left _ _), fun y => ?_⟩
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [hae y, hqmp.ae (Section6.l9_ae_exists_ell_centered hJ3 hnu),
    hqmp.ae (Section6.eng_ae_field d hJ3 hnu), ca1w_ae_continuous hPrefix hJ2 hJ3 nu y,
    w0_ae_isWeakSolutionOn_translateSet_iff_recentered hPrefix hJ2 hJ3 nu y]
    with omega hω hell heng hcont hbr t m hjt hy hX hLm
  obtain ⟨hLm0, hLmw, hLmg, hLmc, hLm0', hLm1, hLm5, hLmS, hLm21, hLmx⟩ : Lhat0 ≤ (m : ℝ) ∧ Lw ≤ (m : ℝ) ∧
      Lg ≤ (m : ℝ) ∧ Lc ≤ (m : ℝ) ∧ L0 ≤ (m : ℝ) ∧ 1 + 4 * (d : ℝ) ≤ (m : ℝ) ∧
      5 * (max Cb Cd) ^ 2 ≤ (m : ℝ) ∧ (MS : ℝ) ≤ (m : ℝ) ∧ (21 : ℝ) ≤ (m : ℝ) ∧ Lx ≤ (m : ℝ) := by
    simpa only [max_le_iff] using hLm
  rw [hLxdef] at hLmx
  simp only [max_le_iff] at hLmx
  obtain ⟨hLmρ, hLmCth, -, hLmK⟩ := hLmx
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
  have hwin : ((n : ℤ) : ℝ) ≤ (m : ℝ) - ⌈max (max Cb M0) 1 * Real.log m⌉ := by
    have h1 : (h : ℝ) = (⌈max (max Cb M0) 1 * Real.log m⌉ : ℝ) := by
      rw [← hhdef]; simp
    have h2 : (n : ℝ) + h = m := by exact_mod_cast hnh
    have h3 : (((n : ℤ) : ℝ)) = (n : ℝ) := by simp
    rw [h3]
    linarith only [h1, h2]
  have hsepR := hsep _ (le_trans (le_max_right _ _) (le_max_left _ _)) (m : ℝ) (n : ℤ) 1
    hLm0' zero_le_one (by linarith only [hm1]) hwin
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
  -- the set `W = t U - y`
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hjt
  have hW := ca2_W_uniform hUu ht y
  have hWo : IsOpen (translateSet (-y) (t • U)) := hW.1
  have hDo : IsOpen (openCubeSet (originCube d (m : ℤ)) ∩ translateSet (-y) (t • U)) :=
    (isOpen_openCubeSet _).inter hWo
  have hfinD : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d (m : ℤ)) ∩
      translateSet (-y) (t • U))) :=
    ⟨by
      simpa only [volumeMeasureOn, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using
        ((isBounded_openCubeSet (originCube d (m : ℤ))).subset Set.inter_subset_left).measure_lt_top⟩
  -- the geometry
  have hxs : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) ≤ (m : ℝ)⁻¹ :=
    ca2w_x_small hd1 hnu hnu1 hm1 (Nat.succ_pos _) hsepR
  have hx2 : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (m : ℤ) ≤ min r0 1 / 2 := by
    refine hxs.trans ?_
    rw [inv_eq_one_div, div_le_div_iff₀ hm0 (by norm_num)]
    have : 2 / min r0 1 ≤ m := hLmρ
    rw [div_le_iff₀ hρ0] at this
    linarith only [this]
  have hBW := ca2w_measure_B hd hUu y hy m h n hnh hh3 hjt hx2
  have hdenW : cden * cubeVolume (originCube d (m : ℤ)) ≤
      (volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ translateSet (-y) (t • U))).toReal := by
    have h1 := hden0 hUu ht y hy m hjt
    rw [rc_shiftCube_zero] at h1
    have hfin : volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ translateSet (-y) (t • U)) ≠ ⊤ :=
      ((isBounded_openCubeSet (originCube d ((m : ℤ) - 1))).subset Set.inter_subset_left).measure_lt_top.ne
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    rw [ca2_cubeVolume_originCube, hcdendef]
    have e : cd0 * min (1 / 6) r0 ^ d * (((3 : ℝ) ^ m) ^ d) = cd0 * min (1 / 6) r0 ^ d * ((3 : ℝ) ^ (m : ℤ)) ^ d := by
      rw [zpow_natCast]
    nlinarith only [h2, e]
  have hC0 : 0 < max 1 (Cdet / cden) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ca2w_main (a := Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
    (W := translateSet (-y) (t • U)) (E := E) (C := max 1 (Cdet / cden)) (Cth := Cth) (cden := cden)
    (Kτ := Kτ) (N := ⌈E⌉₊ + 1) hd m n h hnh hh3 kf y hC1 hnu hnu1 hνS hSwin.2 hρ1.le hδ0 hδ1 hLm1 hLm5
    hellA hsymm hop ?_ hWo hC0 ?_ ?_ hCth0 hcden hdenW (by rw [hCthdef]; exact hBW) hsepR
    (Nat.succ_pos _) (by have := Nat.le_ceil E; push_cast; linarith only [this]) hKτ1 hLmCth hLmK hKτdef'
    (by rw [← hCdetdef]; exact le_max_right _ _)
  · -- the shifted blackbox bounds
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
  · -- the flux is square integrable
    intro u
    obtain ⟨lam, Lam, hE⟩ := heng.2.1 m
    have hE' := hE.mono (hDo.measurableSet) Set.inter_subset_left
    exact memVectorL2_matVecMul_of_isEllipticFieldOn hE' (MemLp.of_eval fun i => u.gradMemL2 i)
  · -- the bridge between the two forms of the equation
    intro u f hfl hu
    have h1 := (hbr m hDo hfinD u f _ hfl).2 hu
    have e : (fun x : Vec d => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (translateSet y (cubeSet (originCube d (m : ℤ)))) (x + y)) =
        fun x => nu • (1 : Mat d) + kf (y + x) := funext fun x => by rw [hkfdef, add_comm x y]
    rw [e] at h1
    exact h1

/-- Witness for the non-law hypotheses of `ca2_boundary_det`: the identity field on `□_m` of `ℝ²`
cut by the empty set, `ν = S = Λ = 1`, all weak-norm coefficients `0`, the zero solution with zero
datum, and the scales `m = h = 3`. -/
example (m : ℤ) (h : ℕ) (hm : m = 3) (hh : h = 3) : True := by
  have hW : IsOpen (∅ : Set (Vec 2)) := isOpen_empty
  have hE : ∀ R : TriadicCube 2, openCubeSet R ⊆ (∅ : Set (Vec 2)) → False := by
    intro R hR
    have hc : triadicCubeShift R ∈ openCubeSet R := by
      rw [ca1_mem_openCube_iff]
      intro k
      have : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
      simp [this]
    exact hR hc
  have hℓ : ∀ R ∈ descendantsAtDepth (originCube 2 m) h, cubeScaleFactor R = (1 : ℝ) := by
    intro R hR
    have h0 := scale_eq_sub_of_mem_descendantsAtDepth hR
    have h1 : R.scale = 0 := by rw [h0]; simp [originCube, hm, hh]
    simp [cubeScaleFactor, h1]
  have hL27 : (27 : ℝ) * 1 ≤ (3 : ℝ) ^ m := by
    rw [hm]; norm_num
  have := ca2_boundary_det (d := 2) (le_refl 2) 0 le_rfl m h hW
    (A := fun _ => (1 : Mat 2)) (lam := 1) (Lam := 1)
    (Section6.ew1_ellip _ (measurableSet_openCubeSet _ |>.inter MeasurableSet.empty))
    (ν := 1) (Λ := 1) (S := 1) (α1 := 0) (β1 := 0) (α2 := 0) (β2 := 0) (ϑ := 0) (τ := 1 / 27) (ℓ := 1)
    one_pos zero_le_one (fun x _ => by ext i j; simp [symmPart, Matrix.one_apply, eq_comm])
    (fun x _ v => by simp [r1_matVecMul_one]) le_rfl le_rfl le_rfl le_rfl le_rfl (by simp)
    (by rw [hm]; norm_num)
    (0 : H1Function (openCubeSet (originCube 2 m) ∩ ∅)) (f := fun _ => 0) (by
      have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube 2 m) ∩ (∅ : Set (Vec 2)))) :=
        ⟨by simp⟩
      exact memLp_const 0)
    (fun φ => by simp [matVecMul, vecDot])
    (fun R hR hsub => absurd hsub (fun h => hE R h))
    (by norm_num) hℓ hL27
    (γ := fun _ => 0) contDiff_const (G1 := 0) (G2 := 0) le_rfl le_rfl (by simp) (by simp)
    (by
      intro η _ _ _
      refine ⟨0, ?_⟩
      funext x
      show (0 : H10Function (openCubeSet (originCube 2 m) ∩ ∅)).toH1Function.toFun x = _
      simp
      rfl)
    le_rfl zero_le_one (by simp [ca2_Bset]) (by rw [hm]; norm_num) (by norm_num) (by norm_num)
    (by
      have h2 : ((0 : ℝ)) ^ (1 / ((2 : ℕ) : ℝ)) = 0 := Real.zero_rpow (by norm_num)
      rw [h2]; norm_num)
  trivial

/-- Witness for the domain hypotheses of `ca_boundary`: the Euclidean ball of radius `1/2` is a
nonempty smooth bounded domain inside the unit origin cube. -/
example [NeZero d] : ∃ U : Set (Vec d), IsSmoothBoundedDomain U ∧ U ⊆ openCubeSet (originCube d 0) ∧
    U.Nonempty :=
  ⟨Section6.euclidBall (d := d) (1 / 2), w0_isSmoothBoundedDomain_euclidBall (by norm_num),
    wpd_ball_subset_cube, ⟨0, by simp [Section6.euclidBall, vecNormSq, vecDot]⟩⟩

end SuperdiffusionCLT.Section7
