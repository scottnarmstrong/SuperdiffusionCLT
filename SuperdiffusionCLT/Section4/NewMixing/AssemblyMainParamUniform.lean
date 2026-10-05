/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyFixedUniform
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyMain
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyScale
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyT0StrongA
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyT0StrongB
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyRefCompare
public import SuperdiffusionCLT.Section4.NewMixing.RatioBound
public import SuperdiffusionCLT.Section4.NewMixing.Nu4Threshold
public import SuperdiffusionCLT.Section4.NewMixing.T0Refinement

/-!
# `newMixParam_main_uniform_of_inputs`: the uniform-in-`h0` form

Lemma `l.new.mixing.parameterized`. The statement is the one recorded in `ParamStatement.lean`.
Its two carried hypotheses are the homogenization-below-cutoff statement `hHomog` and the
cutoff comparison `hComp`.

The proof combines:

* the scale construction with its witnesses identified (`AssemblyScale.lean`);
* the reference comparison from `hHomog` and the cutoff localization
  (`AssemblyRefCompare.lean`), the ratio bound `newMixRatio_bound`;
* the `T_0` refinement uniform in the test direction and sign
  (`AssemblyT0StrongA.lean`, `AssemblyT0StrongB.lean`);
* the energy bound and the passage to the doubled response at fixed parameters
  (`AssemblyMainB.lean`, `AssemblyBridge.lean`);

and one shared constant `C`, to which every threshold is folded with `lNaught_mono_both` and
`newMixAsm_lNaught_le_half`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **`l.new.mixing.parameterized`, uniform in the skew shift `h0`.** The witnesses `X1, X2` are
chosen before `h0`; the amplitude of `X2` is `C m^{-5000}` and its factor is
`1 + shom⁻¹ ‖h0‖²`. The only carried hypothesis is `hHomog`. -/
theorem newMixParam_main_uniform_of_inputs (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hHomog : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L m : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
                  (L : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P m - 1| +
                  |sigmaBarInfinite nu L P * sigmaBarStarInvSeq nu L P m - 1| ≤
                C * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
            ∀ L m r : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu
                nondeg ≤ (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu
                nondeg ≤ (m : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    ∀ eta : Homogenization.BlockVec d,
                      SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
                        Homogenization.Book.Ch02.doubledResponseJ
                          (Homogenization.Book.Ch02.cubeDomain
                            (Homogenization.originCube d (m : ℤ)))
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
                        C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                            (-(2 : ℝ)) *
                            ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                              max 0 ((L : ℝ) - (m : ℝ)) +
                              K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                          X1 omega +
                          (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                                (-(1 : ℝ)) *
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega := by
  have hProv := newMixAsm_refCompare_of_homog d hd hHomog
  obtain ⟨Cs, hCs1, hScale⟩ := newMixAsm_scaleExplicit
  obtain ⟨CA, CenvA, hCA1, hCenvA1, hA⟩ := newMixAsm_t0Strong_branchA d hd
  obtain ⟨CB, CenvB, hCB1, hCenvB1, hB⟩ := newMixAsm_t0Strong_branchB d hd
  obtain ⟨Cv, hCv1, hV⟩ := newMixParam_G_h0_PeSigma_le d
  obtain ⟨CR, hCR1, hRat⟩ := newMixRatio_bound d hd
  obtain ⟨Cref, Cp, hCref1, hCp1, hP⟩ := hProv Cs hCs1
  set C3₀ : ℝ := 4 / ((100000 : ℝ) ^ 2 * (Real.log 2) ^ (12 : ℝ)) with hC3₀def
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC3₀nn : 0 ≤ C3₀ := by rw [hC3₀def]; positivity
  set mom : ℝ := finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) with hmomdef
  set Cfin : ℝ := max 100000 (max Cs (max CA (max CB (max Cp (max (2 * CR)
    (max (CR * Cref) (max ((5 / 4 : ℝ) * 2 * (d : ℝ) ^ 2 * mom * Cs)
    (max (CenvA * (10 * Cv * C3₀ + 1)) (max (CenvB * (10 * Cv * C3₀ + 1))
      (2 * Cref + 2 * (5 / 4 : ℝ)))))))))))
    with hCfindef
  have hCfin100000 : (100000 : ℝ) ≤ Cfin := le_max_left _ _
  have hMR : ∀ {a b c : ℝ}, c ≤ b → c ≤ max a b := fun h => h.trans (le_max_right _ _)
  have hML : ∀ {a b c : ℝ}, c ≤ a → c ≤ max a b := fun h => h.trans (le_max_left _ _)
  have hCs : Cs ≤ Cfin := by rw [hCfindef]; exact hMR (hML le_rfl)
  have hCA : CA ≤ Cfin := by rw [hCfindef]; exact hMR (hMR (hML le_rfl))
  have hCB : CB ≤ Cfin := by rw [hCfindef]; exact hMR (hMR (hMR (hML le_rfl)))
  have hCp : Cp ≤ Cfin := by rw [hCfindef]; exact hMR (hMR (hMR (hMR (hML le_rfl))))
  have hCR2 : 2 * CR ≤ Cfin := by
    rw [hCfindef]; exact hMR (hMR (hMR (hMR (hMR (hML le_rfl)))))
  have hCRref : CR * Cref ≤ Cfin := by
    rw [hCfindef]; exact hMR (hMR (hMR (hMR (hMR (hMR (hML le_rfl))))))
  have hCa : (5 / 4 : ℝ) * 2 * (d : ℝ) ^ 2 * mom * Cs ≤ Cfin := by
    rw [hCfindef]; exact hMR (hMR (hMR (hMR (hMR (hMR (hMR (hML le_rfl)))))))
  have hCbA : CenvA * (10 * Cv * C3₀ + 1) ≤ Cfin := by
    rw [hCfindef]; exact hMR (hMR (hMR (hMR (hMR (hMR (hMR (hMR (hML le_rfl))))))))
  have hCbB : CenvB * (10 * Cv * C3₀ + 1) ≤ Cfin := by
    rw [hCfindef]; exact hMR (hMR (hMR (hMR (hMR (hMR (hMR (hMR (hMR (hML le_rfl)))))))))
  have hCc : 2 * Cref + 2 * (5 / 4 : ℝ) ≤ Cfin := by
    rw [hCfindef]; exact hMR (hMR (hMR (hMR (hMR (hMR (hMR (hMR (hMR (hMR le_rfl)))))))))
  refine ⟨Cfin, le_trans (by norm_num) hCfin100000, ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M K hα0 hα1 hM hK
    L m r hL hm hLm hLr
  have hcStar : 0 < cStar := hJ5.cStar_pos
  have hcStar2 : cStar ≤ 2 := hJ5.cStar_le_two
  have hnondeg : 0 ≤ nondeg := hJ5.K_pos.le
  have hMK : (0 : ℝ) ≤ M + K := by linarith only [hM, hK]
  -- threshold folding to the shared constant
  have hfold : ∀ c : ℝ, 0 ≤ c → c ≤ Cfin →
      SuperdiffusionCLT.Frozen.Section4.lNaught c (c * (M + K)) alpha cStar nu nondeg ≤
        (L : ℝ) ∧
      SuperdiffusionCLT.Frozen.Section4.lNaught c (c * (M + K)) alpha cStar nu nondeg ≤
        (m : ℝ) := by
    intro c hc0 hcle
    have hmono := SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both
      (C := c) (C' := Cfin) (M := c * (M + K)) (M' := Cfin * (M + K)) (alpha := alpha)
      (cStar := cStar) (nu := nu) (K := nondeg) hc0 hcle (mul_nonneg hc0 hMK)
      (mul_le_mul_of_nonneg_right hcle hMK) hnondeg hcStar hnu hα1
    exact ⟨le_trans hmono hL, le_trans hmono hm⟩
  obtain ⟨ell, n, hnell, hellm, hellL, hLell, hLr2, hr2L, hgap, hellnb, hnr, hrn, h200, hcase,
      hL8, hLn⟩ :=
    hScale alpha M K cStar nu nondeg hα0 hα1 hM hK hcStar hcStar2 hnu hnu1 hnondeg L m r
      (hfold Cs (by linarith only [hCs1]) hCs).1 (hfold Cs (by linarith only [hCs1]) hCs).2
      hLm hLr
  have hRC := hP nu cStar K nondeg hnu hnu1 hK P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M hα0 hα1 hM
    L m ell r n (hfold Cp (by linarith only [hCp1]) hCp).1 hLm hnell hellm hellL hLell hLr2 hr2L
    hgap hellnb hnr hrn h200 hL8 hLn
  have hthr : SuperdiffusionCLT.Frozen.Section4.lNaught CR (CR * (Cref * (M + K))) alpha
      cStar nu nondeg ≤ (L : ℝ) / 2 := by
    have hhalf := newMixAsm_lNaught_le_half (C := CR) (C' := Cfin) (M := CR * (Cref * (M + K)))
      (M' := Cfin * (M + K)) (alpha := alpha) (cStar := cStar) (nu := nu) (K := nondeg)
      (by linarith only [hCR1]) hCR2
      (mul_nonneg (by linarith only [hCR1]) (mul_nonneg (by linarith only [hCref1]) hMK))
      (by
        have : CR * (Cref * (M + K)) = (CR * Cref) * (M + K) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hCRref hMK)
      hnondeg hcStar hnu hα0 hα1
    linarith only [hhalf, hL]
  have hRatio := hRat CR le_rfl Cref hCref1 nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg P
    hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M K hα0 hα1 hM hK L m r ell n hthr hLm hLr2 hRC
    (5 / 4 : ℝ) le_rfl
  -- numeric facts at the scales
  have hnm : n ≤ m := by omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hL2m : (L : ℝ) ≤ 2 * (m : ℝ) := by
    have : (ell : ℝ) < (m : ℝ) := by exact_mod_cast hellm
    linarith only [hLell, this]
  have hnu4 : nu ^ (-(4 : ℝ)) ≤ C3₀ * (L : ℝ) := by
    have hMK2 : 2 * Cfin ≤ Cfin * (M + K) := by
      have : (2 : ℝ) ≤ M + K := by linarith only [hM, hK]
      have h0' : (0 : ℝ) ≤ Cfin := by linarith only [hCfin100000]
      nlinarith only [this, h0']
    have h1 := newMixParam_nu4_le_linear_L (C := Cfin) (M := Cfin * (M + K)) (alpha := alpha)
      (cStar := cStar) (nu := nu) (K := nondeg) hCfin100000 hMK2 hnondeg
      hcStar hcStar2 hnu hnu1 hα0 hα1 hL
    have h2 : 4 / (Cfin ^ 2 * (Real.log 2) ^ (12 : ℝ)) ≤ C3₀ := by
      rw [hC3₀def]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hsq : (100000 : ℝ) ^ 2 ≤ Cfin ^ 2 := pow_le_pow_left₀ (by norm_num) hCfin100000 2
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hLnn)
  rcases hcase with ⟨hcA, hellA, hnA⟩ | ⟨hcB, hellB, hnB⟩
  · obtain ⟨X0, hX0meas, hX0BigO, hX0bound⟩ :=
      hA M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg r L m ell n P
        hPrefix hJ1 hJ2 hJ3 hJ4 (hfold CA (by linarith only [hCA1]) hCA).1
        (hfold CA (by linarith only [hCA1]) hCA).2 hLm hLr hcA hellA hnA
    exact newMixAsm_fixed_uniform d (Cenv := CenvA) (Cv := Cv) (C3 := C3₀) (Cratio := 5 / 4) (Cs := Cs)
      hnu hnu1 hK hPrefix hJ2 hJ3 hJ4 hCref1 hnm hellL hRC (by norm_num) hRatio hCs1 hgap
      (by linarith only [hCenvA1]) (by linarith only [hCv1]) hC3₀nn hm1 hL2m
      (by exact_mod_cast hr2L) hnu4 hCa hCbA hCc
      (fun h0 hh0 e he sigma hsigma2 => hV nu hnu hnu1 r P hPrefix hJ2 hJ3 hJ4 e he sigma hsigma2 h0 hh0)
      hX0meas hX0BigO (fun h0 hh0 e he sigma hsigma2 omega => hX0bound e he sigma hsigma2 h0 hh0 omega)
  · obtain ⟨X0, hX0meas, hX0BigO, hX0bound⟩ :=
      hB M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg r L m ell n P
        hPrefix hJ1 hJ2 hJ3 hJ4 (hfold CB (by linarith only [hCB1]) hCB).1
        (hfold CB (by linarith only [hCB1]) hCB).2 hLm hLr hcB hellB hnB
    exact newMixAsm_fixed_uniform d (Cenv := CenvB) (Cv := Cv) (C3 := C3₀) (Cratio := 5 / 4) (Cs := Cs)
      hnu hnu1 hK hPrefix hJ2 hJ3 hJ4 hCref1 hnm hellL hRC (by norm_num) hRatio hCs1 hgap
      (by linarith only [hCenvB1]) (by linarith only [hCv1]) hC3₀nn hm1 hL2m
      (by exact_mod_cast hr2L) hnu4 hCa hCbB hCc
      (fun h0 hh0 e he sigma hsigma2 => hV nu hnu hnu1 r P hPrefix hJ2 hJ3 hJ4 e he sigma hsigma2 h0 hh0)
      hX0meas hX0BigO (fun h0 hh0 e he sigma hsigma2 omega => hX0bound e he sigma hsigma2 h0 hh0 omega)


/-- The range hypotheses of `newMixParam_main_uniform_of_inputs` are satisfiable at
`L = m = r = ⌈L₀⌉`, by `newMixAsm_threshold_witness`. -/
example (C : ℝ) :
    ∃ L m r : ℕ,
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (1 + 1)) 0 2 1 1 ≤ (L : ℝ) ∧
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (1 + 1)) 0 2 1 1 ≤ (m : ℝ) ∧
      (L : ℝ) - 1 * (L : ℝ) ^ (0 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) ∧
      |(L : ℝ) - (r : ℝ)| ≤ 1 * Real.log (L : ℝ) :=
  newMixAsm_threshold_witness (C := C) (M := 1) (K := 1) (alpha := 0) (cStar := 2) (nu := 1)
    (nondeg := 1) le_rfl le_rfl

end
end SuperdiffusionCLT.Section4.NewMixing
