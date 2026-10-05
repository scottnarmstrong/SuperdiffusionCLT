/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniform
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxUniformPart0
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscSurvivors
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Measurable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Integrable

/-!
# The sample-side clauses of the uniform flux estimate

The printed block weight is measurable as a countable sum of finite maxima.
Its fourth moment follows from the clause-2 `Γ₁` tail.  The energy membership
and product integrability follow from the deterministic energy integrability
and Hölder's inequality.  The seminorm flux membership is supplied by the
already established flux measurability and moment result.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

private theorem fluxSample_measurable_blockMax {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (R : TriadicCube d) (k : ℕ) :
    Measurable (fun omega : ShellSeq d => fluxUniformBlockMax nu L omega R k) := by
  let s := descendantsAtDepth R k
  have hs : s.Nonempty := descendantsAtDepth_nonempty R k
  have hsup : Measurable (s.sup' hs fun Q omega =>
      (translatedBlockNorm nu L omega Q).toNNReal) :=
    Finset.measurable_sup' hs (fun Q _ =>
      (measurable_translatedBlockNorm hnu L Q).real_toNNReal)
  have heq : (s.sup' hs fun Q omega =>
      (translatedBlockNorm nu L omega Q).toNNReal) =
    fun omega => fluxUniformBlockMax nu L omega R k := by
    funext omega
    change (s.sup' hs (fun Q omega' =>
      (translatedBlockNorm nu L omega' Q).toNNReal) omega) =
        s.sup (fun Q => (translatedBlockNorm nu L omega Q).toNNReal)
    simp only [Finset.sup'_apply, Finset.sup'_eq_sup hs]
  rw [← heq]
  exact hsup

private theorem fluxSample_measurable_blockWeightE {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (R : TriadicCube d) :
    Measurable (fun omega : ShellSeq d => fluxUniformBlockWeightE nu L omega R) := by
  unfold fluxUniformBlockWeightE
  refine Measurable.tsum fun k => ?_
  have hmax := fluxSample_measurable_blockMax hnu L R k
  have hmaxE : Measurable (fun omega : ShellSeq d =>
      (fluxUniformBlockMax nu L omega R k : ℝ≥0∞)) := hmax.coe_nnreal_ennreal
  have hpow : Measurable (fun omega : ShellSeq d =>
      (fluxUniformBlockMax nu L omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4)) :=
    ENNReal.continuous_rpow_const.measurable.comp hmaxE
  exact measurable_const.mul hpow

private theorem fluxSample_measurable_blockWeight {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (R : TriadicCube d) :
    Measurable (fun omega : ShellSeq d =>
      (fluxUniformBlockWeightE nu L omega R).toReal) :=
  (fluxSample_measurable_blockWeightE hnu L R).ennreal_toReal

/-- The printed block weight is measurable on the sample space. -/
theorem fluxSample_aemeasurable_blockWeight {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (R : TriadicCube d) :
    AEMeasurable (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P e omega R)
      P.toMeasure := by
  have h := fluxSample_measurable_blockWeight hnu S.LPrime R
  simpa only [fluxUniformBlockWeight] using h.aemeasurable

private theorem fluxSample_memLp_blockWeight {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e : Vec d) (hSorder : ScalesOrdering S) {Cb : ℝ} (hCb : 0 < Cb)
    {R : TriadicCube d}
    (hTail : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P e omega R)
      (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4))) :
    MemLp (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P e omega R)
      (ENNReal.ofReal (4 : ℝ)) P.toMeasure := by
  have hL : (0 : ℝ) < (S.LPrime : ℝ) := by
    exact_mod_cast (Nat.zero_le S.m).trans_lt hSorder.m_lt_LPrime
  have hK : 0 < Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) :=
    mul_pos hCb (Real.rpow_pos_of_pos (mul_pos hL (inv_pos.mpr hnu)) _)
  exact rhsTerm3Integrable_memLp_block P hK
    (fluxSample_aemeasurable_blockWeight hnu S P e R) hTail

private theorem fluxSample_integrable_energy_mul_block {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e : Vec d) (hSorder : ScalesOrdering S) {Cb : ℝ} (hCb : 0 < Cb)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m)
    (hTail : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P e omega R)
      (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4))) :
    Integrable (fun omega : ShellSeq d =>
      oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
        fluxUniformBlockWeight nu S P e omega R) P.toMeasure := by
  have hconj : Real.HolderConjugate ((4 : ℝ) / 3) 4 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  let : ENNReal.HolderTriple (ENNReal.ofReal ((4 : ℝ) / 3))
      (ENNReal.ofReal (4 : ℝ)) 1 := hconj.ennrealOfReal
  have hnm : S.n ≤ S.m :=
    (hSorder.n_lt_ell.trans (hSorder.ell_lt_ellPrime.trans hSorder.ellPrime_lt_m)).le
  exact (rhsTerm3Integrable_memLp_energy hnu P S hnm e hR).integrable_mul
    (fluxSample_memLp_blockWeight hnu P S e hSorder hCb hTail)

/-- **The uniform seminorm flux estimate with only the two printed flux-chain
steps left as hypotheses.**  The block weight is the fixed series of Part 0;
the sample-side clauses of `fluxUniform_of_gaps` are supplied here. -/
theorem fluxSample_fluxUniform_main (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hPointwise : ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (e : Vec d) (_he : vecNormSq e = 1),
        ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
          seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
            C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
              (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
                fluxUniformBlockWeight nu S P e omega R))
    (hBlockOrlicz : ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (_e : Vec d) (_he : vecNormSq _e = 1)
        (R : TriadicCube d), R ∈ largeCubeSubcubes d S.n S.m →
        IsBigO P.toMeasure (gammaSigma 1)
            (fun omega : ShellSeq d => fluxUniformBlockWeight nu S P _e omega R)
            (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4))) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (e : Vec d) (_he : vecNormSq e = 1)
        (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)),
      ∀ R ∈ largeCubeSubcubes d S.n S.m,
        ∫ omega : ShellSeq d,
            seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤
          C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
            (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
            (∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^
              ((3 : ℝ) / 4) := by
  obtain ⟨C1, hC1, hPointwise⟩ := hPointwise
  obtain ⟨Cb, hCb, hBlockOrlicz⟩ := hBlockOrlicz
  refine fluxUniform_of_gaps d hd C1 Cb hC1 hCb
    (fluxUniformBlockWeight (d := d)) ?_ ?_
  · exact fluxUniformBlockWeight_nonneg
  · intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM
      hHundredALeH hWindowVsOffset hOffsetLower e he _delta _etaL _hdelta _hetaL _w _hw
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hPointwise nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM
        hHundredALeH hWindowVsOffset hOffsetLower e he
    · exact hBlockOrlicz nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
        hTwoHLeM hHundredALeH hWindowVsOffset hOffsetLower e he
    · intro R hR
      exact memLp_seminormFluxNeg_of_aestronglyMeasurable hnu P hPrefix hJ2 hJ3 hJ4
        S hSorder e hR (rhsTerm3Measurable_aestronglyMeasurable_flux hnu S P e hR)
    · intro R hR
      have htail := hBlockOrlicz nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
        hTwoHLeM hHundredALeH hWindowVsOffset hOffsetLower e he R hR
      exact fluxSample_integrable_energy_mul_block hnu P S e hSorder hCb hR htail
    · intro R hR
      have hnm : S.n ≤ S.m :=
        (hSorder.n_lt_ell.trans (hSorder.ell_lt_ellPrime.trans hSorder.ellPrime_lt_m)).le
      exact rhsTerm3Integrable_memLp_energy hnu P S hnm e hR
    · intro R hR
      exact fluxSample_memLp_blockWeight hnu P S e hSorder hCb
        (hBlockOrlicz nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
          hTwoHLeM hHundredALeH hWindowVsOffset hOffsetLower e he R hR)

end

end SuperdiffusionCLT.Section3.Terms
