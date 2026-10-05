/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolumeBelow

/-!
# The uniform polynomial lower bound on `t_L`

The bounded-gap base case needs a lower bound
on `t_L := sigmaBarStarInvScalar nu L P (cu_n)` in terms of `nu, L` alone
(uniform in the cube index `n`), so that the exponentially small error term
`E` in the scale conversion `t_ell ≤ t_L + E` (see `TermGaugeFinalB.lean`) can be absorbed
once `ell - n` is large enough (a fixed number of `log(nu⁻¹ L)`).

The chain: `Section2/Annealed/InfiniteVolume.lean`'s
`inv_sigmaBarScalar_zero_le_sigmaBarStarInvScalar` gives the uniform-in-`j`
bound `(shom_L(cu_0))⁻¹ ≤ shom_{L,*}^{-1}(cu_j) = t_L`; and
`Section2/Annealed/InfiniteVolumeBelow.lean`'s `sigmaBarSeq_le_envelopeUpperScalar`
gives the crude upper bound `shom_L(cu_0) ≤ envelopeUpperScalar d nu L =
nu + 2 C(d) nu⁻¹ L` (using `max 1 L = L` for `L ≥ 1`). Since `0 < nu ≤ 1`
gives `nu ≤ nu⁻¹`, and `L ≥ 1` gives `nu⁻¹ ≤ nu⁻¹ L`, the envelope is itself
below `(1 + 2 C(d)) nu⁻¹ L`, so inverting the whole chain gives the clean
polynomial (in fact linear) lower bound `t_L ≥ nu / ((1 + 2 C(d)) L)`.

## Main result

* `mixBase_tL_lowerBound`: `nu / ((1 + 2 * cutoffEnvelopeConst d) * L) ≤
  sigmaBarStarInvScalar nu L P (cubeSet (originCube d j))`, for `0 < nu ≤ 1`,
  `1 ≤ L`, `0 ≤ j`, and the four standing shell laws.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-- **The uniform polynomial lower bound on `t_L`.** For `0 < nu ≤ 1`,
`1 ≤ L`, and every cube index `j ≥ 0`,
`nu / ((1 + 2 cutoffEnvelopeConst d) * L) ≤ sigmaBarStarInvScalar nu L P
(cubeSet (originCube d j))`. -/
theorem mixBase_tL_lowerBound [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {L : ℕ} (hL1 : 1 ≤ L) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {j : ℤ} (hj : 0 ≤ j) :
    nu / ((1 + 2 * cutoffEnvelopeConst d) * (L : ℝ)) ≤
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) := by
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hCpos : 0 < cutoffEnvelopeConst d := cutoffEnvelopeConst_pos d
  have hSigPos : 0 < sigmaBarScalar nu L P (cubeSet (originCube d (0 : ℤ))) :=
    sigmaBarScalar_originCube_pos hnu L hPrefix hJ2 hJ3 hJ4 (0 : ℤ)
  -- Step 1: the uniform lower bound `(shom_L(cu_0))⁻¹ ≤ t_L`.
  have h1 :
      (sigmaBarScalar nu L P (cubeSet (originCube d (0 : ℤ))))⁻¹ ≤
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) :=
    inv_sigmaBarScalar_zero_le_sigmaBarStarInvScalar hnu L hPrefix hJ2 hJ3 hJ4 hj
  -- Step 2: the crude envelope upper bound on `shom_L(cu_0)`.
  have h2 :
      sigmaBarScalar nu L P (cubeSet (originCube d (0 : ℤ))) ≤
        envelopeUpperScalar d nu L := by
    simpa [sigmaBarSeq] using sigmaBarSeq_le_envelopeUpperScalar hnu L hPrefix hJ2 hJ3 hJ4 0
  -- Step 3: the envelope itself is below `(1 + 2 C(d)) nu⁻¹ L`.
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := by
    have := inv_anti₀ hnu hnu1
    simpa using this
  have hnunuinv : nu ≤ nu⁻¹ := hnu1.trans hnuinv1
  have hnuinvL : nu⁻¹ ≤ nu⁻¹ * (L : ℝ) :=
    le_mul_of_one_le_right (inv_pos.mpr hnu).le hLR
  have hnuL : nu ≤ nu⁻¹ * (L : ℝ) := hnunuinv.trans hnuinvL
  have h3 :
      envelopeUpperScalar d nu L ≤ (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ) := by
    have hmaxL : max (1 : ℝ) (L : ℝ) = (L : ℝ) := max_eq_right hLR
    have hexpand :
        (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ) =
          nu⁻¹ * (L : ℝ) + 2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := by ring
    unfold envelopeUpperScalar
    rw [hmaxL, hexpand]
    linarith only [hnuL]
  -- Chain steps 1-3 and invert.
  have hSigLeB :
      sigmaBarScalar nu L P (cubeSet (originCube d (0 : ℤ))) ≤
        (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ) := h2.trans h3
  have hinv :
      ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ))⁻¹ ≤
        (sigmaBarScalar nu L P (cubeSet (originCube d (0 : ℤ))))⁻¹ :=
    inv_anti₀ hSigPos hSigLeB
  have hfinal :
      ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ))⁻¹ ≤
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) :=
    hinv.trans h1
  have hCsum_pos : (0 : ℝ) < 1 + 2 * cutoffEnvelopeConst d := by linarith only [hCpos]
  have hCne : (1 + 2 * cutoffEnvelopeConst d) ≠ 0 := hCsum_pos.ne'
  have hnune : nu ≠ 0 := hnu.ne'
  have hLne : (L : ℝ) ≠ 0 := hLpos.ne'
  have heq :
      ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ))⁻¹ =
        nu / ((1 + 2 * cutoffEnvelopeConst d) * (L : ℝ)) := by
    field_simp
  rwa [heq] at hfinal

end

end SuperdiffusionCLT.Section4.Mixing
