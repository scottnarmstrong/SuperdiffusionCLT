/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PrintedSlot
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Energy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3DeltaEtaClose
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PigRatioCloseB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PigRatioSelection
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB
public import SuperdiffusionCLT.Section3.Terms.SstarAnnealedResidue

/-!
# The V6 conclusion for `l.RHS.term3` (`rhs_term3_constFirst`)

`Frozen/Section3/RHSTerm3.lean` states the V6 telescope: the V5 telescope
(itself the V4 telescope plus `_hPigeonScalar`)
with two further binders right after `_hPigeonScalar`,

* `_hDeltaEtaLeOne : delta + etaL ≤ 1`, the printed smallness premise, and
* `_hEtaL`, the printed definition of `η_L` relaxed from `=` to
  `≤` and read with the statement's own constant `C`,

carrying the pigeonhole-selected-scales identity `_hPigeonScalar` at the
cutoff `L` (`sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤
(1 + delta) * sigmaBarStarInvSeq nu S.L P S.m`).  `v6SealFacing_main` proves
this conclusion from `hFluxUniform` and `hCgConstant`, exactly the two
analytical hypotheses that the V4 theorem still carries, kept
syntactically identical to that theorem's shapes (the elaborated types are equal; the
source text differs only in namespace qualification).  No weakening of
`hFluxUniform` or `hCgConstant` is used or needed here: their own telescopes
never mention `_hPigeonScalar`, `_hDeltaEtaLeOne` or `_hEtaL`, and adding those
binders to them would not make either easier to supply.  The remaining two of
the V4 theorem's four named inputs, `hPigRatio` and `hPigeon`, are
derived per instance from `_hPigeonScalar`, `_hDeltaEtaLeOne` and `_hEtaL`
through the localization chain (`term3_locAnchor_of_conjunct1`,
`SuperdiffusionCLT.Section3.Setup.annealed_cutoff_localization`,
`SuperdiffusionCLT.Section3.Setup.localizationEta_mono_gap`,
`SuperdiffusionCLT.Section3.Setup.pigeon_scalar_at_lower_cutoff`,
`sigmaBarStarInvSeq_le_of_abs_pigeon`, `abs_one_sub_inv_mul_le_of_le_mul`), so
no `hCT` datum is needed: `_hDeltaEtaLeOne` and `_hEtaL` alone bound the
localization error by `1/6` (and a fortiori by the `1/4` that the helper
below records as its working bound).

The witnessing constant is `max C0 (6 * pigRatioCeta d CL)`, where `C0` is
the witness of the V4 estimates and `CL := |localizationConst d| + 1`
is the same nonnegative bound on the (possibly negative) localization
constant used throughout the term-3 chain.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

/-- **The pigeonhole scalar at cutoff `L'`**, from the cutoff-`L` datum
`_hPigeonScalar`, the smallness premise `_hDeltaEtaLeOne` and the tie `htie`
(`6 * localizationEta (pigRatioCeta d CL) nu S.L (S.LPrime - S.m) ≤ etaL`,
supplied by `_hEtaL` at the chain's own localization constant): no `hCT`
datum is needed, since the tie and `_hDeltaEtaLeOne` already force the
cutoff-`L` localization error at `1/4`. -/
theorem rhsTerm3Statement_pigeonScalar {d : ℕ} [NeZero d] {nu delta etaL CL : ℝ}
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hCL : 0 < CL)
    (hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL)
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m)
    (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL) (hde1 : delta + etaL ≤ 1)
    (htie : 6 * SuperdiffusionCLT.Section3.Setup.localizationEta
        (pigRatioCeta d CL) nu S.L (S.LPrime - S.m) ≤ etaL)
    (hpig : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P
        (S.m - 2 * S.h) ≤
      (1 + delta) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.L P S.m) :
    |SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu S.LPrime P
          (Homogenization.cubeSet (Homogenization.originCube d (S.m : ℤ))) *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar nu S.LPrime P
          (Homogenization.cubeSet (Homogenization.originCube d ((S.m - 2 * S.h : ℕ) : ℤ))) -
        1| ≤ delta + etaL := by
  have hCeta0 : (0 : ℝ) ≤ pigRatioCeta d CL := pigRatioCeta_nonneg d hCL.le
  have hL1S : 1 ≤ S.L := one_le_L_of_scalesOrdering hSorder
  have hm_LP : S.m ≤ S.LPrime := le_of_lt hSorder.m_lt_LPrime
  have hLP_L : S.LPrime ≤ S.L := le_of_lt hSorder.LPrime_lt_L
  have hkLP : S.m - 2 * S.h ≤ S.LPrime := by omega
  have hkm : S.m - 2 * S.h ≤ S.m := by omega
  have hgapk : S.LPrime - S.m ≤ S.LPrime - (S.m - 2 * S.h) := by omega
  have hLocAnchor := term3_locAnchor_of_conjunct1 d CL hloc nu hnu hnu1 P hJ3
  have hlocm := SuperdiffusionCLT.Section3.Setup.annealed_cutoff_localization
    (k := S.m) (LPrime := S.LPrime) (L := S.L) hnu hnu1 hCL hL1S hLP_L hPrefix hJ2 hJ3 hJ4
    (pigRatioCeta_le_self d CL) (hLocAnchor S.LPrime S.m S.L hm_LP hLP_L)
  have hlock0 := SuperdiffusionCLT.Section3.Setup.annealed_cutoff_localization
    (k := S.m - 2 * S.h) (LPrime := S.LPrime) (L := S.L) hnu hnu1 hCL hL1S hLP_L hPrefix hJ2 hJ3
    hJ4 (pigRatioCeta_le_self d CL) (hLocAnchor S.LPrime (S.m - 2 * S.h) S.L hkLP hLP_L)
  have hlock := le_trans hlock0
    (SuperdiffusionCLT.Section3.Setup.localizationEta_mono_gap hCeta0 hnu S.L hgapk)
  have heta0 :=
    SuperdiffusionCLT.Section3.Setup.localizationEta_nonneg hCeta0 hnu S.L (S.LPrime - S.m)
  have heta4 : SuperdiffusionCLT.Section3.Setup.localizationEta (pigRatioCeta d CL) nu S.L
      (S.LPrime - S.m) ≤ 1 / 4 := by
    linarith only [htie, hde1, hdelta]
  have hdelta1 : delta ≤ 1 := by linarith only [hde1, hetaL]
  have h := SuperdiffusionCLT.Section3.Setup.pigeon_scalar_at_lower_cutoff hnu hPrefix hJ2
    hJ3 hJ4 hdelta hdelta1 heta0 heta4 hkm hpig hlocm hlock
  linarith only [h, htie]

/-- `hPigRatio` at cutoff `L'` and comparability `4`, from the pigeonhole
scalar. -/
theorem rhsTerm3Statement_pigRatio {d : ℕ} [NeZero d] {nu eps : ℝ}
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hnu : 0 < nu) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (habs : |SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu S.LPrime P
          (Homogenization.cubeSet (Homogenization.originCube d (S.m : ℤ))) *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar nu S.LPrime P
          (Homogenization.cubeSet (Homogenization.originCube d ((S.m - 2 * S.h : ℕ) : ℤ))) -
        1| ≤ eps) :
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) ≤
      4 * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n := by
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  have hr := sigmaBarStarInvSeq_le_of_abs_pigeon hnu S.LPrime hPrefix hJ2 hJ3 hJ4 hnm heps habs
  have hpos :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3
      hJ4 S.n
  have hstep : (1 + eps) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime
      P S.n ≤ 4 * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n :=
    mul_le_mul_of_nonneg_right (by linarith only [heps1]) hpos.le
  exact le_trans hr hstep

/-- `hPigeon` at cutoff `L'`, from the pigeonhole scalar. -/
theorem rhsTerm3Statement_pigeon {d : ℕ} [NeZero d] {nu eps : ℝ}
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hnu : 0 < nu) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (habs : |SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu S.LPrime P
          (Homogenization.cubeSet (Homogenization.originCube d (S.m : ℤ))) *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar nu S.LPrime P
          (Homogenization.cubeSet (Homogenization.originCube d ((S.m - 2 * S.h : ℕ) : ℤ))) -
        1| ≤ eps) :
    |1 - (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ eps := by
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  have hside : S.m - 2 * S.h ≤ S.n := by have := hSorder.m_lt; omega
  have hr := sigmaBarStarInvSeq_le_of_abs_pigeon hnu S.LPrime hPrefix hJ2 hJ3 hJ4
    (le_refl S.m) heps habs
  have hba : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n :=
    SuperdiffusionCLT.Section2.Annealed.antitone_sigmaBarStarInvSeq hnu S.LPrime hPrefix hJ2
      hJ3 hJ4 hnm
  have hac : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) :=
    SuperdiffusionCLT.Section2.Annealed.antitone_sigmaBarStarInvSeq hnu S.LPrime hPrefix hJ2
      hJ3 hJ4 hside
  have ha :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3
      hJ4 S.n
  have hb :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3
      hJ4 S.m
  have h1e : 0 ≤ 1 - eps := by linarith only [heps1]
  have hstep : (1 - eps) * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime
      P S.n ≤ SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m := by
    have e1 := mul_le_mul_of_nonneg_left (le_trans hac hr) h1e
    have e2 : (1 - eps) * ((1 + eps) *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m) =
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m -
          eps ^ 2 * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime
            P S.m := by ring
    have e3 : 0 ≤ eps ^ 2 *
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.m :=
      mul_nonneg (sq_nonneg eps) hb.le
    linarith only [e1, e2, e3]
  exact abs_one_sub_inv_mul_le_of_le_mul ha hba hstep

end SuperdiffusionCLT.Section3.Terms
