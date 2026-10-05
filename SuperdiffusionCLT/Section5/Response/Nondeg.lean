/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyC
public import SuperdiffusionCLT.Section3.Setup.StationaryProjectionBridge
public import SuperdiffusionCLT.Section5.Carriers.BlockOffset

/-!
# Nondegeneracy of the shell block `(m - h, m]` for the whole-space response energy

The use of `e.nondeg` in `lem.response`: the nondegeneracy clause applied with
`(n, m) = (m - h, m)` gives, for `|e| = 1`,
`|E |grad w^_e(0)|^2 - c⋆ (log 3) h shom_{m-h}^{-2}| ≤ K shom_{m-h}^{-2}`,
where `w^_e` is the whole-space potential of the flux `hshellFlux nu P m h · e`
`= shom_{m-h}^{-1} (k_m - k_{m-h}) e`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Probability.Stationary

noncomputable section

variable {d : ℕ}

/-- **`e.nondeg` at `(m - h, m)` for the whole-space energy of the flux `hshellFlux`.** -/
theorem abs_wholeSpaceEnergy_hshellFlux_sub_le [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) {cStar K : ℝ}
    (hJ5 : ShellLawJ5 d P cStar K hPrefix hJ2 hJ3)
    (nu : ℝ) {m h : ℕ} (h1 : 1 ≤ h) (hh : h ≤ m) (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (gradHatW : ShellSeq d → Vec d)
    (hFmemLp : MemLp (fun omega : ShellSeq d =>
      HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) 2 P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d =>
      HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hproj : (hGmemLp.toLp fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) =
      -stationaryPotentialProjection (μ := P.toMeasure)
        (hFmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (hshellFlux nu P m h omega e 0))) :
    |wholeSpaceEnergy P.toMeasure gradHatW -
        cStar * Real.log 3 * (h : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))| ≤
      K * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
        (-(2 : ℝ)) := by
  have hhm : m - h ≤ m := Nat.sub_le m h
  set s := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P with hs
  have he : vecNormSq e = 1 := by
    have hh2 := vecNorm_sq_eq_vecNormSq e
    rw [hunit] at hh2
    simpa using hh2.symm
  have hp : s⁻¹ • e = s⁻¹ • e := rfl
  have hF : ∀ omega : ShellSeq d, hshellFlux nu P m h omega e = fun x =>
      matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x) (s⁻¹ • e) := by
    intro omega
    funext x
    simp only [hshellFlux, matVecMul_smul_right]
    rfl
  have key := abs_wholeSpaceEnergy_sub_cStar_mul_le hPrefix hJ2 hJ3 (cStar := cStar) (K := K)
    hhm e hunit he s⁻¹ (s⁻¹ • e) hp (hshellFlux nu P m h · e)
    hF gradHatW hFmemLp hGmemLp hproj (hJ5.nondegenerate (m - h) m
      (by omega) e hunit)
  have hn : vecNormSq (s⁻¹ • e) = s ^ (-(2 : ℝ)) := by
    rw [vecNormSq_smul, he, mul_one, Real.rpow_neg_eq_inv_rpow, Real.rpow_two, inv_pow]
  rw [hn, Nat.sub_sub_self hh] at key
  exact key

/-- Witness for the non-law hypotheses: the origin sample of `hshellFlux` is square integrable. -/
theorem memLp_hshellFlux_origin [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P)
    (nu : ℝ) (m h : ℕ) (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1) :
    MemLp (fun omega : ShellSeq d =>
      HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) 2 P.toMeasure := by
  set s := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P
  have hfun : (fun omega : ShellSeq d => HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) =
      fun omega => s⁻¹ • ∑ l ∈ Finset.Ioc (m - h) m, shellOriginForcing e l omega := by
    funext omega
    have h1 := finiteShellIncrement_apply_eq_streamCutoff_sub omega (Nat.sub_le m h) (0 : Vec d)
    have h2 := originForcing_finiteShellIncrement e (m - h) m omega
    have h3 : hshellFlux nu P m h omega e 0 = s⁻¹ • matVecMul
        (finiteShellIncrement omega (m - h) m 0) e := by
      simp only [hshellFlux, h1]
      rfl
    rw [h3, ← h2, ofVec_smul]
    rfl
  have hsum : MemLp (fun omega : ShellSeq d =>
      ∑ l ∈ Finset.Ioc (m - h) m, shellOriginForcing e l omega) 2 P.toMeasure :=
    memLp_finsetSum (Finset.Ioc (m - h) m) fun l _ => hJ3.memLp_shellOriginForcing e hunit l
  rw [hfun]
  exact hsum.const_smul s⁻¹

/-- Witness: the non-law hypotheses of `abs_wholeSpaceEnergy_hshellFlux_sub_le` (`hFmemLp`,
`gradHatW`, `hGmemLp`, `hproj`) are jointly satisfiable, so the displayed bound is not an
implication from an empty antecedent. -/
theorem exists_gradHatW_hshellFlux [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) (m h : ℕ) (e : Vec d)
    (hunit : Book.Ch02.vecNorm e = 1) :
    ∃ (hFmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) 2 P.toMeasure)
      (gradHatW : ShellSeq d → Vec d)
      (hGmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
      (hGmemLp.toLp fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) =
        -stationaryPotentialProjection (μ := P.toMeasure)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) := by
  have hF := memLp_hshellFlux_origin hJ3 nu m h e hunit
  obtain ⟨g, hG, hp⟩ := exists_gradHatW_neg_stationaryPotentialProjection
    (mu := P.toMeasure) hF
  exact ⟨hF, g, hG, hp⟩

end

end SuperdiffusionCLT.Section5
