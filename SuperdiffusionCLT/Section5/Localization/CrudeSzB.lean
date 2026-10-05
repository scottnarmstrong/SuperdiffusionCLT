/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzA

/-!
# The per-cube bound for `⟪S_z, S_z⟫`

`ofReal_pairing_le`: for the constant-offset minimizer `S` on `Q = z + cu_n`,
`⟪S, S⟫ ≤ ρ_Q · 2Λ · (2 + ‖g_D‖²_{L̲²(Q)} + ‖g_N‖²_{L̲²(Q)})`, where `ρ_Q` is the ellipticity
ratio of `bfA_m(Q)` and `Λ` dominates `bfE_m`-weights times `shom^{∓1}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields

variable {d : ℕ}

/-- The real inequality behind `ofReal_pairing_le`. -/
theorem pairing_le_real [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {Lam : ℝ} (hσ : 0 < sigmaBarInfinite nu (m - h) P)
    (hL1 : envelopeUpperScalar d nu m * (sigmaBarInfinite nu (m - h) P)⁻¹ ≤ Lam)
    (hL2 : envelopeLowerScalar d nu * sigmaBarInfinite nu (m - h) P ≤ Lam)
    {e e' : Vec d} (he : vecNormSq e ≤ 1) (he' : vecNormSq e' ≤ 1) (Q : TriadicCube d)
    (gD gN : Vec d → Vec d) {S : BlockState d}
    (hS : IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
      (constBlockState (blockSlope nu (m - h) P Q e e' gD gN)) S) :
    blockPairingAverage (cubeSet Q) (coefficientCutoff nu omega m).toCoeffField S S ≤
      envelopeRatio m Q omega * (2 * Lam) *
        (2 + vecNormSq (volumeAverageVec (cubeSet Q) gD) +
          vecNormSq (volumeAverageVec (cubeSet Q) gN)) := by
  obtain ⟨lam, LamE, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
  rw [blockPairingAverage_self_eq_coarseBlockMatrix Q hEll _ hS]
  set σ := sigmaBarInfinite nu (m - h) P with hσdef
  set a := volumeAverageVec (cubeSet Q) gD with ha
  set b := volumeAverageVec (cubeSet Q) gN with hb
  have hq := blockVecDot_le_envelope hnu omega m Q (σ ^ (-(1 : ℝ) / 2) • (e' + a))
    (σ ^ ((1 : ℝ) / 2) • (e + b))
  have hslope : blockSlope nu (m - h) P Q e e' gD gN =
      (σ ^ (-(1 : ℝ) / 2) • (e' + a), σ ^ ((1 : ℝ) / 2) • (e + b)) := rfl
  rw [hslope]
  refine hq.trans ?_
  rw [vecNormSq_smul, vecNormSq_smul, rpow_neg_half_sq hσ, rpow_half_sq hσ]
  have hρ : 0 ≤ envelopeRatio m Q omega := by
    have := one_le_envelopeRatio m Q omega
    linarith only [this]
  have h1 := vecNormSq_add_le e' a
  have h2 := vecNormSq_add_le e b
  have hn1 := vecNormSq_nonneg (e' + a)
  have hn2 := vecNormSq_nonneg (e + b)
  have hu := envelopeUpperScalar_pos hnu d m
  have hl := envelopeLowerScalar_pos hnu d
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have t1 : envelopeUpperScalar d nu m * (σ⁻¹ * vecNormSq (e' + a)) ≤
      Lam * (2 * (1 + vecNormSq a)) := by
    rw [← mul_assoc]
    refine mul_le_mul hL1 ?_ hn1 ?_
    · linarith only [h1, he']
    · have : 0 ≤ envelopeUpperScalar d nu m * σ⁻¹ := by positivity
      linarith only [this, hL1]
  have t2 : envelopeLowerScalar d nu * (σ * vecNormSq (e + b)) ≤
      Lam * (2 * (1 + vecNormSq b)) := by
    rw [← mul_assoc]
    refine mul_le_mul hL2 ?_ hn2 ?_
    · linarith only [h2, he]
    · have : 0 ≤ envelopeLowerScalar d nu * σ := by positivity
      linarith only [this, hL2]
  have : envelopeRatio m Q omega * (envelopeUpperScalar d nu m * (σ⁻¹ * vecNormSq (e' + a)) +
      envelopeLowerScalar d nu * (σ * vecNormSq (e + b))) ≤
      envelopeRatio m Q omega * (Lam * (2 * (1 + vecNormSq a)) + Lam * (2 * (1 + vecNormSq b))) :=
    mul_le_mul_of_nonneg_left (add_le_add t1 t2) hρ
  refine this.trans (le_of_eq ?_)
  ring

/-- **The per-cube bound for `⟪S_z, S_z⟫`** in `ℝ≥0∞`, in terms of the ellipticity ratio of
`bfA_m(Q)` and the `L̲²` norms of the two fields on `Q`. -/
theorem ofReal_pairing_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {Lam : ℝ} (hσ : 0 < sigmaBarInfinite nu (m - h) P)
    (hL1 : envelopeUpperScalar d nu m * (sigmaBarInfinite nu (m - h) P)⁻¹ ≤ Lam)
    (hL2 : envelopeLowerScalar d nu * sigmaBarInfinite nu (m - h) P ≤ Lam)
    {e e' : Vec d} (he : vecNormSq e ≤ 1) (he' : vecNormSq e' ≤ 1) (Q : TriadicCube d)
    {gD gN : Vec d → Vec d} (hD : MemVectorL2 (openCubeSet Q) gD)
    (hN : MemVectorL2 (openCubeSet Q) gN) {S : BlockState d}
    (hS : IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
      (constBlockState (blockSlope nu (m - h) P Q e e' gD gN)) S) :
    ENNReal.ofReal
        (blockPairingAverage (cubeSet Q) (coefficientCutoff nu omega m).toCoeffField S S) ≤
      ENNReal.ofReal (envelopeRatio m Q omega) * ENNReal.ofReal (2 * Lam) *
        (2 + vecCubeLpENorm Q 2 gD ^ (2 : ℕ) + vecCubeLpENorm Q 2 gN ^ (2 : ℕ)) := by
  have hreal := pairing_le_real hnu P m h omega hσ hL1 hL2 he he' Q gD gN hS
  have hρ : 0 ≤ envelopeRatio m Q omega := by
    have := one_le_envelopeRatio m Q omega
    linarith only [this]
  have hLam : 0 ≤ Lam := by
    have hu := envelopeUpperScalar_pos hnu d m
    have : 0 ≤ envelopeUpperScalar d nu m * (sigmaBarInfinite nu (m - h) P)⁻¹ := by
      have := inv_pos.2 hσ
      positivity
    linarith only [this, hL1]
  have hJa : ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) gD)) ≤
      vecCubeLpENorm Q 2 gD ^ (2 : ℕ) := by
    have e1 : volumeAverageVec (cubeSet Q) gD = volumeAverageVec (openCubeSet Q) gD := by
      funext i
      exact volumeAverage_cubeSet_eq_openCubeSet Q _
    rw [e1]
    exact SuperdiffusionCLT.Section3.Terms.ofReal_vecNormSq_volumeAverageVec_le hD
  have hJb : ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) gN)) ≤
      vecCubeLpENorm Q 2 gN ^ (2 : ℕ) := by
    have e1 : volumeAverageVec (cubeSet Q) gN = volumeAverageVec (openCubeSet Q) gN := by
      funext i
      exact volumeAverage_cubeSet_eq_openCubeSet Q _
    rw [e1]
    exact SuperdiffusionCLT.Section3.Terms.ofReal_vecNormSq_volumeAverageVec_le hN
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  have hna := vecNormSq_nonneg (volumeAverageVec (cubeSet Q) gD)
  have hnb := vecNormSq_nonneg (volumeAverageVec (cubeSet Q) gN)
  have h2L : 0 ≤ 2 * Lam := by linarith only [hLam]
  have e2 : ENNReal.ofReal (2 + vecNormSq (volumeAverageVec (cubeSet Q) gD) +
      vecNormSq (volumeAverageVec (cubeSet Q) gN)) =
      2 + ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) gD)) +
        ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet Q) gN)) := by
    rw [ENNReal.ofReal_add (by linarith only [hna]) hnb, ENNReal.ofReal_add (by norm_num) hna]
    norm_num
  rw [ENNReal.ofReal_mul (mul_nonneg hρ h2L), ENNReal.ofReal_mul hρ, e2]
  gcongr

end SuperdiffusionCLT.Section5
