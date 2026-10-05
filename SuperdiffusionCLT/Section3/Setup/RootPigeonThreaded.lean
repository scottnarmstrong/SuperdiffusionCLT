/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ScaleAssemblyB

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Terms
open scoped ENNReal

noncomputable section

/-! ## The assembled lower bound -/

/-- **The root's own proof of `p.sstar.lower.bound`, assembled**.

The scale selection of `exists_scaleSelection_of_threshold`, the scale
conditions of `ScaleAssembly`, the ten consequences proved above, the
homogenization statement through `exists_bell_bound` and the removal of the
pigeonhole scale through `lower_bound_transfer` are composed with
`Terms.sstar_lower_bound_of_terms`.  The conclusion is the root's first
conjunct `σ̄_{L,*}(cu_m̄) ≤ σ̄_L` (which is
`sigmaBarStarScalar_originCube_le_sigmaBarInfinite`) together with its second
conjunct `e.sstar.lower.bound` at every prescribed `m̄` with `L/2 ≤ m̄ ≤ L`.

The constant is `CB` from the homogenization statement, quantified first exactly as
the paper quantifies its own; every other constant of the conclusion is an explicit
expression in the binders.

**The single carried bridge is `hBridges`.** Its selected-scale input includes
the final `sigmaBarStarInvSeq` ratio
from `exists_scaleSelection_of_threshold`; the proof retains that pigeonhole
component and rewrites its outer scale with `hSL` before calling the bridge.

Its three output conjuncts are

1. the master inequality at the selected scales, which
   `master_inequality_of_selection` reduces to the five term bounds
   `l.LHS.term1`, `e.RHS.term1`-`e.RHS.term4` and the master identity
   `e.ellsep.testing`; and
2, 3. the two balanced localization comparisons,
   `σ̄_{ℓ,*}(cu_n) ≤ 2σ̄_{L',*}(cu_n)` and `¼σ̄_{L',*}(cu_n) ≤ σ̄_{L,*}(cu_m)`,
   whose source is `Frozen.Section2.cutoff_localization` (the printed
   `e.localization.s.star`), not the averaged gauged comparison
   `localization_average` of `Frozen/Section2/LocalizationAverage.lean`.

The remaining hypotheses are the print's own: the choice of `c₀`,
the largeness of `C` (`64 ≤ C`), the
largeness of `K` and the four uses of the threshold `e.L.vs.nu`.  No upper bound
on `c⋆` is assumed: the factor `C(δ + L^{-1000})^{1/2}` is carried
into the conclusion's constant, exactly as the print carries it into its
unspecified `c(d)`. -/
theorem rootPig_assembled (d : ℕ) [NeZero d] :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (CM c0 C K cStar Knd nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)),
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
        (∀ S : ScaleSelection, S.L = L →
            S.h = optimalWindow C (smallnessParameter c0 cStar) nu L →
            S.a = scaleOffset K nu L → ScalesOrdering S →
            2 * S.h ≤ S.m → 100 * S.a ≤ S.h → 10 ≤ S.h → L / 4 < S.n →
            L / 4 + 2 * S.h ≤ S.m → S.m ≤ L / 2 →
            sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤
              (1 + smallnessParameter c0 cStar) * sigmaBarStarInvSeq nu S.L P S.m →
            (cStar * (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n ≤
                CM * (smallnessParameter c0 cStar + (S.L : ℝ) ^ (-(1000 : ℝ))) ^
                    ((1 : ℝ) / 2) *
                  (sigmaBarSeq nu S.ell P S.n +
                    (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n) +
                CM * (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) *
                  sigmaBarStarInvSeq nu S.LPrime P S.n) ∧
              (sigmaBarStarInvSeq nu S.ell P S.n)⁻¹ ≤
                2 * (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ ∧
              (1 / 4 : ℝ) * (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ ≤
                sigmaBarStarScalar nu S.L P (cubeSet (originCube d (S.m : ℤ)))) →
        ∀ mbar : ℕ, mbar ≤ L → L ≤ 2 * mbar →
          sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) ≤
              sigmaBarInfinite nu L P ∧
            sstarLowerBoundConst CB (logEnvelopeConst K) 2
                  (optimalWindowConst C c0) (2 * CM + 1) / 2 *
                cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (mbar : ℝ) ^ ((1 : ℝ) / 2) *
                Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
              sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) := by
  obtain ⟨CB, hCB, hbellAll⟩ := exists_bell_bound d
  refine ⟨CB, hCB, ?_⟩
  intro CM c0 C K cStar Knd nu L P hCM hc0 hCenv hClarge hK hcStar hnu hnu1
    hL hPrefix hJ1 hJ2 hJ3 hJ4 hdelta1 hlog hlogCle hThresh hc0small hthrSmall
    hThreshAbs hThreshBell hBridges mbar hmbarL hLmbar
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hClarge
  have hdelta : 0 < smallnessParameter c0 cStar := smallnessParameter_pos hc0 hcStar
  have hlog1 : (1 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by linarith only [hlog]
  have hlogpos : (0 : ℝ) < Real.log (nu⁻¹ * (L : ℝ)) := by linarith only [hlog1]
  have hK2 : (0 : ℝ) ≤ K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 :=
    mul_nonneg (by linarith only [hK]) (sq_nonneg _)
  obtain ⟨S, hSL, hSh, hSa, hord, hhm, hha, h10, hn4, hmlow, hmhigh, -, hPigeonScalar⟩ :=
    exists_scaleSelection_of_threshold hnu L hPrefix hJ2 hJ3 hJ4 hnu1 hL hdelta
      hdelta1 hK hlog hCenv hClarge hThresh
  have hPigeonScalarS :
      sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤
        (1 + smallnessParameter c0 cStar) * sigmaBarStarInvSeq nu S.L P S.m := by
    rw [hSL]
    exact hPigeonScalar
  obtain ⟨hMaster, hLocal1, hLocal2⟩ :=
    hBridges S hSL hSh hSa hord hhm hha h10 hn4 hmlow hmhigh hPigeonScalarS
  -- the scale facts
  have hellL : S.ell ≤ S.L := by
    have h1 := hord.ell_lt_ellPrime
    have h2 := hord.ellPrime_lt_m
    have h3 := hord.m_lt_LPrime
    have h4 := hord.LPrime_lt_L
    omega
  have hn1 : 1 ≤ S.n := by omega
  have hell1 : 1 ≤ S.ell := by have := hord.n_lt_ell; omega
  have hlogSL : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)) := by rw [hSL]; exact hlog1
  -- the ten hypotheses of `Terms.sstar_lower_bound_of_terms`
  have hSmallC : CM * (smallnessParameter c0 cStar +
      (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤ cStar / 4 := by
    rw [hSL]
    exact smallness_relative hCM hc0.le hcStar.le hc0small hthrSmall
  have hCDE : (0 : ℝ) < 2 * CM + 1 := by linarith only [hCM]
  have hFactor : CM * (smallnessParameter c0 cStar +
      (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤ 2 * CM + 1 := by
    rw [hSL]
    exact smallness_absolute hCM hc0.le hdelta1 hL
  have hHsizeL : optimalWindowConst C c0 * cStar ^ (2 : ℕ) * (L : ℝ) ≤
      (S.h : ℝ) * Real.log (nu⁻¹ * (L : ℝ)) := by
    rw [hSh]
    exact optimalWindow_size hC1 hnu hL hdelta rfl hlog1 hlogCle hK2 hThresh
  have hHsize : optimalWindowConst C c0 * cStar ^ (2 : ℕ) * (S.L : ℝ) ≤
      (S.h : ℝ) * Real.log (nu⁻¹ * (S.L : ℝ)) := by rw [hSL]; exact hHsizeL
  have hLowerAbs : CM * (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) ≤
      cStar * (S.h : ℝ) / 4 := by
    rw [hSL]
    exact lowerOrder_absorption hcStar hlogpos hHsizeL hThreshAbs
  have hLn4 : (L : ℝ) ≤ 4 * (S.n : ℝ) := by
    have hnat : L ≤ 4 * S.n := by omega
    exact_mod_cast hnat
  have hnbig : CB * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) ≤ (S.n : ℝ) := by
    rw [hSL]
    linarith only [hThreshBell, hLn4]
  have hbell := hbellAll nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S.n S.ell S.L hn1
    hnbig hord.n_lt_ell hellL
  have haK : ((S.a : ℕ) : ℝ) ≤ K * Real.log (nu⁻¹ * (S.L : ℝ)) + 1 := by
    rw [hSL, hSa]
    exact le_of_lt (scaleOffset_lt_add_one
      (mul_nonneg (by linarith only [hK]) hlogpos.le))
  have hQ := q_envelope hnu hnu1 hK hlogSL hell1 hellL haK
  obtain ⟨hLogm, hlogcomp0⟩ := log_pigeon_range hnu hnu1 hlog hmlow (by omega : 1 ≤ S.h)
  have hlogcomp : Real.log (nu⁻¹ * (S.L : ℝ)) ≤ 2 * Real.log (nu⁻¹ * (S.m : ℝ)) := by
    rw [hSL]; exact hlogcomp0
  have hmL : (S.m : ℝ) ≤ (S.L : ℝ) := by
    have hnat : S.m ≤ S.L := by rw [hSL]; omega
    exact_mod_cast hnat
  have hm1R : (1 : ℝ) ≤ (S.m : ℝ) := by
    have hnat : 1 ≤ S.m := by omega
    exact_mod_cast hnat
  -- the bound at the pigeonhole scale
  have hkey := sstar_lower_bound_of_terms CM CB (logEnvelopeConst K) 2
    (optimalWindowConst C c0) (2 * CM + 1) hCB
    (logEnvelopeConst_pos (by linarith only [hK])) (by norm_num)
    (optimalWindowConst_pos (by linarith only [hC1]) hc0) hCDE nu hnu P
    hPrefix hJ2 hJ3 hJ4 cStar Knd K (smallnessParameter c0 cStar) hcStar S hMaster
    hFactor hSmallC hLowerAbs hbell hQ hLocal1 hLocal2 hHsize hlogSL hLogm
    hlogcomp hmL hm1R
  -- the removal of the pigeonhole scale
  have hmono : sigmaBarStarScalar nu S.L P (cubeSet (originCube d (S.m : ℤ))) ≤
      sigmaBarStarScalar nu S.L P (cubeSet (originCube d (mbar : ℤ))) :=
    sigmaBarStarScalar_originCube_mono hnu S.L hPrefix hJ2 hJ3 hJ4 (by omega)
  have hmm : (S.m : ℝ) ≤ (mbar : ℝ) := by
    have hnat : S.m ≤ mbar := by omega
    exact_mod_cast hnat
  have hmbar4 : (mbar : ℝ) ≤ 4 * (S.m : ℝ) := by
    have hnat : mbar ≤ 4 * S.m := by omega
    exact_mod_cast hnat
  refine ⟨sigmaBarStarScalar_originCube_le_sigmaBarInfinite hnu L hPrefix hJ2 hJ3
    hJ4 mbar, ?_⟩
  have hcnn : (0 : ℝ) ≤ sstarLowerBoundConst CB (logEnvelopeConst K) 2
      (optimalWindowConst C c0) (2 * CM + 1) :=
    (sstarLowerBoundConst_pos hCB (logEnvelopeConst_pos (by linarith only [hK]))
      (by norm_num) (optimalWindowConst_pos (by linarith only [hC1]) hc0) hCDE).le
  have hfinal := lower_bound_transfer (m := S.m) (mbar := mbar) hcnn hcStar.le hnu
    hm1R (by linarith only [hLogm]) hmm hmbar4 (le_trans hkey hmono)
  rw [hSL] at hfinal
  exact hfinal


end

end SuperdiffusionCLT.Section3.Setup
