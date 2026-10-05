/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonRootTail
public import SuperdiffusionCLT.Section4.SigmaBarComparison.Growth
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Section4.LNaught

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

/-- The threshold `hat L_2` of `p.minimal.scales`, with the
proposition's own constant `C` in both `L_0` slots. -/
def srootMS_Lhat2 (C expon delta s M cStar nu nondeg : ℝ) : ℝ :=
  max
    (SuperdiffusionCLT.Frozen.Section4.lNaught C
      (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
      (1 - expon) cStar nu nondeg)
    (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon)
      cStar nu nondeg)

/-- The deterministic term of `e.new.mixing.attempt` at `(CE, s, K, shom_m, m)`. -/
def srootMS_det (CE s K sig : ℝ) (m : ℕ) : ℝ :=
  CE * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * sig⁻¹ * Real.log (m : ℝ)

/-- The `Γ_2` amplitude of `e.new.mixing.attempt`. -/
def srootMS_A1 (CE s K sig : ℝ) (m : ℕ) : ℝ :=
  CE * s⁻¹ * K ^ ((1 : ℝ) / 2) * sig⁻¹ * Real.log (m : ℝ) ^ ((1 : ℝ) / 2)

/-- The `Γ_{2/3}` amplitude of `e.new.mixing.attempt`. -/
def srootMS_A2 (CE : ℝ) (m : ℕ) : ℝ :=
  CE * (m : ℝ) ^ (-(1000 : ℝ))

/-- The right side `δ shom_m^{-1} m^ρ log m` of `e.minscale.bounds.E`. -/
def srootMS_target (delta sig expon : ℝ) (m : ℕ) : ℝ :=
  delta * sig⁻¹ * (m : ℝ) ^ expon * Real.log (m : ℝ)


/-- The finite union bound at one scale: the event that some admissible
`(n, k)` has `thr < f n k + g n k`. -/
theorem srootMS_measureReal_biUnion_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {d : ℕ} (S : ℕ → (Fin d → ℤ) → Set Ω) (a b h R : ℕ) (e : ℝ)
    (hS : ∀ n k, μ.real (S n k) ≤ e) (hab : b - a ≤ h) :
    μ.real (⋃ n ∈ Finset.Icc a b,
        ⋃ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(R : ℤ)) (R : ℤ)), S n k) ≤
      (((h : ℝ) + 1) * (2 * (R : ℝ) + 1) ^ d) * e := by
  have he : 0 ≤ e := le_trans measureReal_nonneg (hS 0 0)
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => measureReal_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun k _ => hS n k) ?_
  simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Int.card_Icc, Nat.card_Icc]
  have h1 : ((b + 1 - a : ℕ) : ℝ) ≤ (h : ℝ) + 1 := by
    have : b + 1 - a ≤ h + 1 := by omega
    exact_mod_cast this
  have h2 : (((R : ℤ) + 1 - -(R : ℤ)).toNat : ℝ) = 2 * (R : ℝ) + 1 := by
    have : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
    rw [this]; push_cast; ring
  rw [Nat.cast_pow, h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) he


/-- **Skeleton of `p.minimal.scales`.** Every input is a named hypothesis:

* `hE` is the body of `mathcalE_bounds` (`p.new.mixing.attempt`),
  copied verbatim;
* `hThr` is the threshold comparison of `e.new.mixing.minscale.thresholds`:
  the mixing threshold `L_0(C s⁻¹ K, 1/2)` at
  `K = C M s⁻¹` lies below `hat L_2`;
* `hOneScale` is the arithmetic of `e.new.mixing.minscale.one.scale`:
  after the union bound over `n` and `z`, the tails of the
  two random terms of `e.new.mixing.attempt` at level
  `δ shom_m^{-1} m^ρ log m - (deterministic term)` sum to at most
  `m^{-2} exp(-(2 log 3 · m / hat L_2)^{2ρ})`, which is summable in `m` and
  gives the `Γ_{2ρ}` tail of `log X` at amplitude exactly `hat L_2`.

The growth bound `shom_m ≤ C ν⁻¹ (1 + m)` (`e.sL.growth`, crude form) is
`sbAsm_crude_growth_bound`; the union bound, the minimal-scale
construction and the final assembly are proved here. -/
theorem srootMS_minimal_scales_of_inputs (d : ℕ) [NeZero d]
    (hE :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            ∀ K : ℝ, C ≤ K →
              ∀ m n : ℕ,
                SuperdiffusionCLT.Frozen.Section4.lNaught C (C * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
                m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n →
                n ≤ m →
                ∀ k : Fin d → ℤ,
                                    (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                  ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X1 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma 2) X1
                        (C * s⁻¹ * K ^ ((1 : ℝ) / 2) *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ∧
                    Measurable X2 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma (2 / 3)) X2
                        (C * (m : ℝ) ^ (-(1000 : ℝ))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ L : ℕ, (m : ℝ) - C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                    nu omega L
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))).toCoeffField
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) +
                            Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                nu • (1 : Homogenization.Mat d) +
                                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                    omega
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))
                                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) ≤
                            C * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) *
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu m P)⁻¹ *
                                Real.log (m : ℝ) +
                              X1 omega + X2 omega)
    (hThr : ∀ CE : ℝ, 1 ≤ CE → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < nondeg →
        ∀ (expon delta s M : ℝ), 0 < expon → expon < 1 / 2 → 0 < delta → delta ≤ 1 →
          0 < s → s ≤ 1 → 1 ≤ M →
            SuperdiffusionCLT.Frozen.Section4.lNaught CE (CE * s⁻¹ * (C * M * s⁻¹)) (1 / 2) cStar nu nondeg ≤
              srootMS_Lhat2 C expon delta s M cStar nu nondeg)
    (hOneScale : ∀ CE Cg : ℝ, 1 ≤ CE → 1 ≤ Cg → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < nondeg →
        ∀ (expon delta s M : ℝ), 0 < expon → expon < 1 / 2 → 0 < delta → delta ≤ 1 →
          0 < s → s ≤ 1 → 1 ≤ M →
            4 * Real.log 3 ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg ∧
            ∀ (sig : ℝ) (m : ℕ), srootMS_Lhat2 C expon delta s M cStar nu nondeg ≤ (m : ℝ) →
              0 < sig → sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ)) →
                1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
                    (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m) ∧
                1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
                    (2 * srootMS_A2 CE m) ∧
                (((⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ : ℝ) + 1) *
                    (2 * (3 : ℝ) ^ (⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ + 3) + 1) ^ d) *
                  (Real.exp (-(((srootMS_target delta sig expon m -
                        srootMS_det CE s (C * M * s⁻¹) sig m) /
                        (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m)) ^ (2 : ℝ))) +
                    Real.exp (-(((srootMS_target delta sig expon m -
                        srootMS_det CE s (C * M * s⁻¹) sig m) /
                        (2 * srootMS_A2 CE m)) ^ ((2 : ℝ) / 3)))) ≤
                  (((m : ℝ) ^ 2)⁻¹) *
                    Real.exp (-((2 * Real.log 3 * (m : ℝ) /
                      srootMS_Lhat2 C expon delta s M cStar nu nondeg) ^ (2 * expon)))) :

    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ (expon delta s M : ℝ),
            0 < expon → expon < 1 / 2 →
            0 < delta → delta ≤ 1 →
            0 < s → s ≤ 1 →
            1 ≤ M →
            ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma (2 * expon))
                  (fun omega => Real.log (X omega))
                  (max
                    (SuperdiffusionCLT.Frozen.Section4.lNaught C
                      (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
                      (1 - expon) cStar nu nondeg)
                    (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon) cStar nu
                      nondeg)) ∧
              ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                ∀ m n : ℕ,
                  max
                      (SuperdiffusionCLT.Frozen.Section4.lNaught C
                        (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
                        (1 - expon) cStar nu nondeg)
                      (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon) cStar nu
                        nondeg) ≤
                    (m : ℝ) →
                  X omega ≤ (3 : ℝ) ^ m →
                  m - ⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ ≤ n →
                  n ≤ m →
                  (∀ L : ℕ, m ≤ L →
                    ∀ k : Fin d → ℤ,
                                            (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                            Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                          Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                      Homogenization.HomogenizationErrorOnCube
                          (Homogenization.originCube d (n : ℤ)) s
                          Homogenization.MultiscaleExponent.infinity
                          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                          (fun x =>
                            (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                nu omega L
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (m : ℤ)))).toCoeffField
                              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                            (1 : Homogenization.Mat d)) ≤
                        delta *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          (m : ℝ) ^ expon * Real.log (m : ℝ)) ∧
                  (∀ k : Fin d → ℤ,
                                        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                    Homogenization.HomogenizationErrorOnCube
                        (Homogenization.originCube d (n : ℤ)) s
                        Homogenization.MultiscaleExponent.infinity
                        (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                        (fun x =>
                          nu • (1 : Homogenization.Mat d) +
                            SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                              omega
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (m : ℤ)))
                              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                          (1 : Homogenization.Mat d)) ≤
                      delta *
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                            P)⁻¹ *
                        (m : ℝ) ^ expon * Real.log (m : ℝ))
    := by
  obtain ⟨CE, hCE1, hEm⟩ := hE
  obtain ⟨Cg, hCg1, hGrow⟩ :=
    SuperdiffusionCLT.Section4.SigmaBarComparison.sbAsm_crude_growth_bound d
  obtain ⟨C1, hC11, hThrC⟩ := hThr CE hCE1
  obtain ⟨C2, hC21, hOneC⟩ := hOneScale CE Cg hCE1 hCg1
  refine ⟨max (max C1 C2) CE, le_trans hC11 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 expon delta s M hexp0 hexp1
    hdel0 hdel1 hs0 hs1 hM
  set C : ℝ := max (max C1 C2) CE with hCdef
  have hC1C : C1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2C : C2 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCEC : CE ≤ C := le_max_right _ _
  have hcS : 0 < cStar := hJ5.cStar_pos
  have hcS2 : cStar ≤ 2 := SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5.cStar_le_two hJ5
  have hnd : 0 < nondeg := hJ5.K_pos
  have hThr' := hThrC C hC1C nu cStar nondeg hnu hnu1 hcS hcS2 hnd expon delta s M hexp0 hexp1
    hdel0 hdel1 hs0 hs1 hM
  obtain ⟨hLh, hOne⟩ := hOneC C hC2C nu cStar nondeg hnu hnu1 hcS hcS2 hnd expon delta s M
    hexp0 hexp1 hdel0 hdel1 hs0 hs1 hM
  set Lh : ℝ := srootMS_Lhat2 C expon delta s M cStar nu nondeg with hLhdef
  set K : ℝ := C * M * s⁻¹ with hKdef
  have hCEK : CE ≤ K := by
    have hsinv : 1 ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs1
    have hCM : C ≤ C * M := le_mul_of_one_le_right (by linarith only [hCE1, hCEC]) hM
    have hCMs : C * M ≤ C * M * s⁻¹ :=
      le_mul_of_one_le_right (by linarith only [hCE1, hCEC, hCM]) hsinv
    linarith only [hCEC, hCM, hCMs]
  set Adm : ℕ → ℕ → (Fin d → ℤ) → Prop := fun m n k =>
    (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) with hAdm
  set Prem : ℕ → ℕ → (Fin d → ℤ) → Prop := fun m n k =>
    SuperdiffusionCLT.Frozen.Section4.lNaught CE (CE * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) ∧
      m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n ∧ n ≤ m ∧ Adm m n k with hPrem
  have hEx : ∀ (m n : ℕ) (k : Fin d → ℤ),
      ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Prem m n k →
        Measurable X1 ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2) X1
            (srootMS_A1 CE s K (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)
              m) ∧
        Measurable X2 ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma (2 / 3)) X2 (srootMS_A2 CE m) ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
          ∀ L : ℕ, (m : ℝ) - CE * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
            Homogenization.HomogenizationErrorOnCube
                (Homogenization.originCube d (n : ℤ)) s
                Homogenization.MultiscaleExponent.infinity
                (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                (fun x =>
                  (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                      nu omega L
                      (Homogenization.cubeSet
                        (Homogenization.originCube d (m : ℤ)))).toCoeffField
                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                  (1 : Homogenization.Mat d)) +
              Homogenization.HomogenizationErrorOnCube
                (Homogenization.originCube d (n : ℤ)) s
                Homogenization.MultiscaleExponent.infinity
                (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                (fun x =>
                  nu • (1 : Homogenization.Mat d) +
                    SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                      omega
                      (Homogenization.cubeSet
                        (Homogenization.originCube d (m : ℤ)))
                      ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                  (1 : Homogenization.Mat d)) ≤
              srootMS_det CE s K
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) m +
                X1 omega + X2 omega := by
    intro m n k
    by_cases hp : Prem m n k
    · obtain ⟨X1, X2, h⟩ := hEm nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1
        K hCEK m n hp.1 hp.2.1 hp.2.2.1 k hp.2.2.2
      exact ⟨X1, X2, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose X1 X2 hX using hEx
  set sig : ℕ → ℝ := fun m =>
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P with hsig
  set thr : ℕ → ℝ := fun m =>
    srootMS_target delta (sig m) expon m - srootMS_det CE s K (sig m) m with hthr
  set S : ℕ → ℕ → (Fin d → ℤ) → Set (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
    fun m n k => {ω | Prem m n k ∧ thr m < X1 m n k ω + X2 m n k ω} with hSdef
  set hh : ℕ → ℕ := fun m => ⌈K * Real.log (m : ℝ)⌉₊ with hhh
  set Bad : ℕ → Set (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) := fun m =>
    if Lh ≤ (m : ℝ) then
      ⋃ n ∈ Finset.Icc (m - hh m) m,
        ⋃ k ∈ Fintype.piFinset
            (fun _ : Fin d => Finset.Icc (-((3 ^ (hh m + 3) : ℕ) : ℤ)) ((3 ^ (hh m + 3) : ℕ) : ℤ)),
          S m n k
    else ∅ with hBad
  have hSmeas : ∀ m n k, MeasurableSet (S m n k) := by
    intro m n k
    by_cases hp : Prem m n k
    · have hXk := hX m n k hp
      have heq : S m n k = {ω | thr m < X1 m n k ω + X2 m n k ω} := by
        ext ω; simp only [hSdef, Set.mem_ofPred_eq, hp, true_and]
      rw [heq]
      exact measurableSet_lt measurable_const (hXk.1.add hXk.2.2.1)
    · have heq : S m n k = ∅ := by
        ext ω; simp only [hSdef, Set.mem_ofPred_eq, hp, false_and, Set.mem_empty_iff_false]
      rw [heq]
      exact MeasurableSet.empty
  have hBadMeas : ∀ m, MeasurableSet (Bad m) := by
    intro m
    by_cases hm : Lh ≤ (m : ℝ)
    · simp only [hBad, hm, ↓reduceIte]
      exact Finset.measurableSet_biUnion _ fun n _ =>
        Finset.measurableSet_biUnion _ fun k _ => hSmeas m n k
    · simp only [hBad, hm, ↓reduceIte]
      exact MeasurableSet.empty
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLhpos : 0 < Lh := lt_of_lt_of_le (by positivity) hLh
  have hsigpos : ∀ m, 0 < sig m := fun m =>
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  have hlogm : ∀ m : ℕ, Lh ≤ (m : ℝ) → 0 < Real.log (m : ℝ) := by
    intro m hm
    refine Real.log_pos ?_
    have h13 : (1 : ℝ) < 4 * Real.log 3 := by
      have := SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
      linarith only [this]
    linarith only [h13, hLh, hm]
  have hKpos : 0 < K := lt_of_lt_of_le (by linarith only [hCE1]) hCEK
  have hper : ∀ m : ℕ, P.toMeasure.real (Bad m) ≤
      (((m : ℝ) ^ 2)⁻¹) * Real.exp (-((2 * Real.log 3 * (m : ℝ) / Lh) ^ (2 * expon))) := by
    intro m
    by_cases hm : Lh ≤ (m : ℝ)
    · simp only [hBad, hm, ↓reduceIte]
      obtain ⟨hT1, hT2, hcount⟩ := hOne (sig m) m hm (hsigpos m)
        (hGrow nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 m)
      have hA1 : 0 < srootMS_A1 CE s K (sig m) m := by
        have := hlogm m hm
        have := hsigpos m
        unfold srootMS_A1
        positivity
      have hA2 : 0 < srootMS_A2 CE m := by
        have := hlogm m hm
        have hm0 : (0 : ℝ) < m := by
          by_contra hc
          push Not at hc
          have : Real.log (m : ℝ) = 0 := by
            rw [le_antisymm hc (Nat.cast_nonneg m), Real.log_zero]
          linarith only [this, hlogm m hm]
        unfold srootMS_A2
        have : 0 < (m : ℝ) ^ (-(1000 : ℝ)) := Real.rpow_pos_of_pos hm0 _
        positivity
      have hSb : ∀ n k, P.toMeasure.real (S m n k) ≤
          Real.exp (-((thr m / (2 * srootMS_A1 CE s K (sig m) m)) ^ (2 : ℝ))) +
            Real.exp (-((thr m / (2 * srootMS_A2 CE m)) ^ ((2 : ℝ) / 3))) := by
        intro n k
        by_cases hp : Prem m n k
        · have hXk := hX m n k hp
          have heq : S m n k = {ω | thr m < X1 m n k ω + X2 m n k ω} := by
            ext ω; simp only [hSdef, Set.mem_ofPred_eq, hp, true_and]
          rw [heq]
          exact srootMS_measureReal_lt_add_le hA1 hA2 hXk.2.1 hXk.2.2.2.1 hT1 hT2
        · have heq : S m n k = ∅ := by
            ext ω; simp only [hSdef, Set.mem_ofPred_eq, hp, false_and, Set.mem_empty_iff_false]
          rw [heq, measureReal_empty]
          positivity
      refine le_trans (srootMS_measureReal_biUnion_le (S m) (m - hh m) m (hh m) (3 ^ (hh m + 3))
        _ hSb (by omega)) ?_
      have hcast : ((3 ^ (hh m + 3) : ℕ) : ℝ) = (3 : ℝ) ^ (hh m + 3) := by push_cast; rfl
      rw [hcast]
      exact hcount
    · simp only [hBad, hm, ↓reduceIte, measureReal_empty]
      positivity
  obtain ⟨X, hXmeas, hXO, hXae⟩ := srootMS_minimalScale (μ := P.toMeasure) hBadMeas hLh
    (by positivity : (0 : ℝ) < 2 * expon) hper
  refine ⟨X, hXmeas, hXO, ?_⟩
  have hEae : ∀ᵐ ω ∂P.toMeasure, ∀ (m n : ℕ) (k : Fin d → ℤ), Prem m n k →
      ∀ L : ℕ, (m : ℝ) - CE * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
        Homogenization.HomogenizationErrorOnCube
            (Homogenization.originCube d (n : ℤ)) s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite (2 : ℝ))
            (fun x =>
              (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                  nu ω L
                  (Homogenization.cubeSet
                    (Homogenization.originCube d (m : ℤ)))).toCoeffField
                ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
            (sig m • (1 : Homogenization.Mat d)) +
          Homogenization.HomogenizationErrorOnCube
            (Homogenization.originCube d (n : ℤ)) s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite (2 : ℝ))
            (fun x =>
              nu • (1 : Homogenization.Mat d) +
                SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                  ω
                  (Homogenization.cubeSet
                    (Homogenization.originCube d (m : ℤ)))
                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
            (sig m • (1 : Homogenization.Mat d)) ≤
          srootMS_det CE s K (sig m) m + X1 m n k ω + X2 m n k ω := by
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    by_cases hp : Prem m n k
    · filter_upwards [(hX m n k hp).2.2.2.2] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hp
  filter_upwards [hXae, hEae] with ω hgood hEω m n hLm hXm3 hn1 hn2
  have hnotBad : ω ∉ Bad m := hgood m hXm3
  have hbound : ∀ k : Fin d → ℤ, Adm m n k →
      ∀ L : ℕ, (m : ℝ) - CE * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
        Homogenization.HomogenizationErrorOnCube
            (Homogenization.originCube d (n : ℤ)) s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite (2 : ℝ))
            (fun x =>
              (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                  nu ω L
                  (Homogenization.cubeSet
                    (Homogenization.originCube d (m : ℤ)))).toCoeffField
                ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
            (sig m • (1 : Homogenization.Mat d)) +
          Homogenization.HomogenizationErrorOnCube
            (Homogenization.originCube d (n : ℤ)) s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite (2 : ℝ))
            (fun x =>
              nu • (1 : Homogenization.Mat d) +
                SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                  ω
                  (Homogenization.cubeSet
                    (Homogenization.originCube d (m : ℤ)))
                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
            (sig m • (1 : Homogenization.Mat d)) ≤
          srootMS_target delta (sig m) expon m := by
    intro k hk L hL
    have hp : Prem m n k := ⟨le_trans hThr' hLm, hn1, hn2, hk⟩
    have hle : X1 m n k ω + X2 m n k ω ≤ thr m := by
      by_contra hlt
      push Not at hlt
      apply hnotBad
      have hLm' : Lh ≤ (m : ℝ) := hLm
      simp only [hBad, hLm', ↓reduceIte]
      refine Set.mem_iUnion₂.2 ⟨n, Finset.mem_Icc.2 ⟨hn1, hn2⟩, ?_⟩
      refine Set.mem_iUnion₂.2 ⟨k, Fintype.mem_piFinset.2 fun i => ?_, ⟨hp, hlt⟩⟩
      have hi := srootMS_abs_index_le hn2 hk i
      have hn1' : m - hh m ≤ n := hn1
      have hmn : m - n + 3 ≤ hh m + 3 := by omega
      have hpow : (3 : ℤ) ^ (m - n + 3) ≤ (3 : ℤ) ^ (hh m + 3) :=
        pow_le_pow_right₀ (by norm_num) hmn
      have hcast : (((3 ^ (hh m + 3) : ℕ)) : ℤ) = (3 : ℤ) ^ (hh m + 3) := by push_cast; rfl
      rw [hcast, Finset.mem_Icc]
      exact abs_le.1 (le_trans hi hpow)
    have hE1 := hEω m n k hp L hL
    have hthrm : thr m = srootMS_target delta (sig m) expon m - srootMS_det CE s K (sig m) m :=
      rfl
    linarith only [hE1, hle, hthrm]
  have hstart : (m : ℝ) - CE * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
    have : 0 ≤ CE * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) := by
      have : 0 < s⁻¹ := inv_pos.2 hs0
      positivity
    linarith only [this]
  refine ⟨fun L hL k hk => ?_, fun k hk => ?_⟩
  · have hmL : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have h := hbound k hk L (le_trans hstart hmL)
    have h0 := srootMS_homErr_nonneg (Homogenization.originCube d (n : ℤ)) hs0.le
      (fun x =>
        nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField ω
            (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
            ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
      (sig m • (1 : Homogenization.Mat d))
    exact le_trans (le_add_of_nonneg_right h0) h
  · have h := hbound k hk m hstart
    have h0 := srootMS_homErr_nonneg (Homogenization.originCube d (n : ℤ)) hs0.le
      (fun x =>
        (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff nu ω m
            (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))).toCoeffField
          ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
      (sig m • (1 : Homogenization.Mat d))
    exact le_trans (le_add_of_nonneg_left h0) h


end

end SuperdiffusionCLT.Section4.MinimalScales
