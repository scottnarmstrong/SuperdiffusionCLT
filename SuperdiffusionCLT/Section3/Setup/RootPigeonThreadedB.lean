/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Setup.RootPigeonThreaded

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms

noncomputable section

/-- The root's first bracket with its pigeonhole scalar passed into the master
bridge, while the localization comparisons are still supplied by the anchor. -/
theorem rootPig_assembled_of_anchors (d : ℕ) [NeZero d] :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (CM c0 C K cStar Knd nu CL Ceta : ℝ) (L : ℕ)
        (P : ProbabilityMeasure (ShellSeq d)),
        0 ≤ CM → 0 < c0 → cutoffEnvelopeConst d ≤ C → 64 ≤ C → (1 : ℝ) ≤ K →
        0 < cStar → 0 < nu → nu ≤ 1 → 1 ≤ L →
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        smallnessParameter c0 cStar ≤ 1 →
        (11 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) →
        Real.log C ≤ Real.log (nu⁻¹ * (L : ℝ)) →
        20 * (K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1) *
            (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) ≤
          smallnessParameter c0 cStar * (L : ℝ) →
        CM * Real.sqrt c0 ≤ 1 / 8 →
        CM * (L : ℝ) ^ (-(500 : ℝ)) ≤ cStar / 8 →
        4 * CM * (1 + Knd + K * Real.log (nu⁻¹ * (L : ℝ))) *
            Real.log (nu⁻¹ * (L : ℝ)) ≤
          optimalWindowConst C c0 * cStar ^ (3 : ℕ) * (L : ℝ) →
        4 * CB * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) ≤ (L : ℝ) →
        0 < CL →
        IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹ ≤ Ceta →
        Ceta ≤ nu⁻¹ * (L : ℝ) →
        8056 ≤ K * Real.log 3 →
        (∀ mm nn LL : ℕ, nn ≤ mm → mm ≤ LL →
            ∀ U : Book.Ch02.Domain d,
              (U : Set (Vec d)) ⊆ openCubeSet (originCube d (nn : ℤ)) →
              ∃ X : ShellSeq d → ℝ,
                Measurable X ∧
                IndependentSums.IsBigO P.toMeasure
                    (IndependentSums.gammaSigma 1) X
                    (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - nn : ℕ) : ℝ))) ∧
                  ∀ omega : ShellSeq d,
                    MatLoewnerLE
                        ((1 - X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                          (coefficientCutoff nu omega mm).toCoeffField)
                        (sigmaStarInvCoarse (U : Set (Vec d))
                          (coefficientCutoff nu omega LL).toCoeffField) ∧
                      MatLoewnerLE
                        (sigmaStarInvCoarse (U : Set (Vec d))
                          (coefficientCutoff nu omega LL).toCoeffField)
                        ((1 + X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                          (coefficientCutoff nu omega mm).toCoeffField)) →
        (∀ S : ScaleSelection, S.L = L →
            S.h = optimalWindow C (smallnessParameter c0 cStar) nu L →
            S.a = scaleOffset K nu L → ScalesOrdering S →
            2 * S.h ≤ S.m → 100 * S.a ≤ S.h → 10 ≤ S.h → L / 4 < S.n →
            L / 4 + 2 * S.h ≤ S.m → S.m ≤ L / 2 →
            sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤
              (1 + smallnessParameter c0 cStar) * sigmaBarStarInvSeq nu S.L P S.m →
            cStar * (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n ≤
              CM * (smallnessParameter c0 cStar + (S.L : ℝ) ^ (-(1000 : ℝ))) ^
                  ((1 : ℝ) / 2) *
                (sigmaBarSeq nu S.ell P S.n +
                  (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n) +
              CM * (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) *
                sigmaBarStarInvSeq nu S.LPrime P S.n) →
        ∀ mbar : ℕ, mbar ≤ L → L ≤ 2 * mbar →
          sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) ≤
              sigmaBarInfinite nu L P ∧
            sstarLowerBoundConst CB (logEnvelopeConst K) 2
                  (optimalWindowConst C c0) (2 * CM + 1) / 2 *
                cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (mbar : ℝ) ^ ((1 : ℝ) / 2) *
                Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
              sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) := by
  obtain ⟨CB, hCB, hAss⟩ := rootPig_assembled d
  refine ⟨CB, hCB, ?_⟩
  intro CM c0 C K cStar Knd nu CL Ceta L P hCM hc0 hCenv hClarge hK hcStar
    hnu hnu1 hL hPrefix hJ1 hJ2 hJ3 hJ4 hdelta1 hlog hlogCle hThresh hc0small
    hthrSmall hThreshAbs hThreshBell hCL hCeta hCT hKlog3 hLocAnchor hMaster
  refine hAss CM c0 C K cStar Knd nu L P hCM hc0 hCenv hClarge hK hcStar
    hnu hnu1 hL hPrefix hJ1 hJ2 hJ3 hJ4 hdelta1 hlog hlogCle hThresh hc0small
    hthrSmall hThreshAbs hThreshBell ?_
  -- the two localization bridges, at every selected `S`
  intro S hSL hSh hSa hord hhm hha h10 hn4 hmlow hmhigh hPigeonScalar
  have hlogpos : (0 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by linarith only [hlog]
  have hCeta0 : (0 : ℝ) ≤ Ceta := by
    have hc := crudeLowerConst_pos d
    have hg := IndependentSums.gammaMomentConst_pos (σ := (1 : ℝ)) one_pos
    have : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 1 * CL *
        (crudeLowerConst d)⁻¹ := by positivity
    linarith only [this, hCeta]
  -- the scale facts of `e.scales.ordering`
  have hn_ell : S.n ≤ S.ell := le_of_lt hord.n_lt_ell
  have hell_LP : S.ell ≤ S.LPrime := by
    have h1 := hord.ell_lt_ellPrime
    have h2 := hord.ellPrime_lt_m
    have h3 := hord.m_lt_LPrime
    omega
  have hm_LP : S.m ≤ S.LPrime := le_of_lt hord.m_lt_LPrime
  have hLP_L : S.LPrime ≤ S.L := le_of_lt hord.LPrime_lt_L
  have hn_m : S.n ≤ S.m := by
    have h1 := hord.n_lt_ell
    have h2 := hord.ell_lt_ellPrime
    have h3 := hord.ellPrime_lt_m
    omega
  have hLP1 : 1 ≤ S.LPrime := by
    have h1 := hord.n_lt_ell
    have h2 := hord.ell_lt_ellPrime
    have h3 := hord.ellPrime_lt_m
    have h4 := hord.m_lt_LPrime
    omega
  have hL1S : 1 ≤ S.L := by rw [hSL]; exact hL
  have hgap1 : S.ell - S.n = S.a := by have := S.n_add_a; omega
  have hgap2 : S.LPrime - S.m = 2 * S.a := by have := S.LPrime_eq; omega
  have haOff : S.a = scaleOffset K nu L := hSa
  -- the two localization errors are absorbed
  have hk6 : 6 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((S.a : ℕ) : ℝ) * Real.log 3 := by
    rw [haOff]
    exact six_log_le_scaleOffset_mul_log_three hKlog3 hlogpos
  have hk6' : 6 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((2 * S.a : ℕ) : ℝ) * Real.log 3 := by
    have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hcast : ((2 * S.a : ℕ) : ℝ) = 2 * ((S.a : ℕ) : ℝ) := by push_cast; ring
    have hann : (0 : ℝ) ≤ ((S.a : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : ((S.a : ℕ) : ℝ) * Real.log 3 ≤ 2 * ((S.a : ℕ) : ℝ) * Real.log 3 := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hann) hlog3
      linarith only [this]
    rw [hcast]
    linarith only [hk6, hstep]
  have heta1 : localizationEta Ceta nu S.LPrime (S.ell - S.n) ≤ 1 := by
    rw [hgap1]
    have hmono := localizationEta_mono_scale hCeta0 hnu hLP_L S.a
    rw [hSL] at hmono
    refine le_trans hmono ?_
    rw [localizationEta]
    exact localization_error_le_one hnu hnu1 hL hCeta0 hCT hk6
  have heta2 : localizationEta Ceta nu S.L (S.LPrime - S.m) ≤ 3 := by
    rw [hSL, hgap2, localizationEta]
    have h := localization_error_le_one (k := 2 * S.a) hnu hnu1 hL hCeta0 hCT hk6'
    linarith only [h]
  -- `e.localization.s.star.annealed.applied` at `(ℓ, L')` on `cu_n` and at
  -- `(L', L)` on `cu_m`
  have hcomp1 := annealed_cutoff_localization (k := S.n) (LPrime := S.ell)
    (L := S.LPrime) hnu hnu1 hCL hLP1 hell_LP hPrefix hJ2 hJ3 hJ4 hCeta
    (hLocAnchor S.ell S.n S.LPrime hn_ell hell_LP)
  have hcomp2 := annealed_cutoff_localization (k := S.m) (LPrime := S.LPrime)
    (L := S.L) hnu hnu1 hCL hL1S hLP_L hPrefix hJ2 hJ3 hJ4 hCeta
    (hLocAnchor S.LPrime S.m S.L hm_LP hLP_L)
  exact ⟨hMaster S hSL hSh hSa hord hhm hha h10 hn4 hmlow hmhigh hPigeonScalar,
    localization_bridge_one hnu hPrefix hJ2 hJ3 hJ4 heta1 hcomp1,
    localization_bridge_two hnu hPrefix hJ2 hJ3 hJ4 hn_m heta2 hcomp2⟩

end

end SuperdiffusionCLT.Section3.Setup
