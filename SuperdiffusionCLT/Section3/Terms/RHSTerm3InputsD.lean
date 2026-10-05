/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsC

/-!
# Display 2 of `e.bL.to.bhomell` from the anchors

The statements are those of `l.RHS.term3` and `e.bL.to.bhomell` in the paper.

## Display 2

The paper states: *"Combining this with `e.nablaw.Lt`, we get
`∑_i E[|avsum_{z ∈ 3^nℤ^d ∩ cu_k} Y_z^{(i)}|²]^{1/2} E[‖∇w‖⁴_{L̲⁴(cu_m)}]^{1/2}
≤ Cν⁻²(m−ℓ')ℓ3^{−d(k−ℓ)/2} ≤ Cν⁻²(m−ℓ')L'3^{−2d(ℓ'−ℓ)/(d+4)}`."*

`blockDev_of_concentration` is that display on the carriers of this development: the
concentration bound `blockDeviation_concentration` of
`Section3/Terms/RHSTerm3InputsC.lean` at the coarse-block scale
`k = coarseBlockScale d S` of `l.RHS.term3#coarse-block-scale-choice`, the
fourth-moment form `nablaW4_of_regbounds` of `e.nablaw.Lt`, the crude bound
`|p|² ≤ ν⁻¹`, the envelope `bfE_ℓ ≤ Cν⁻¹L'`, and the two exponent comparisons

* `2d(ℓ'−ℓ)/(d+4) ≤ d(k−ℓ)/2` (`coarse_block_scale_choice`), and
* `L'−ℓ = h+3a ≤ 2h = 2(m−ℓ')` (the window comparison `4a ≤ h`).

## Main results

* `coarseBlockDevMoment`, `blockDevConst`, `blockDev_of_concentration`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The printed deviation moment and its constant -/

/-- **`∑_i E[|avsum_{z∈D} Y_z^{(i)}|²]^{1/2}`**, the left-hand factor of the
display of `e.bL.to.bhomell`: the sum over the coordinate directions of the second
moments of the lattice averages of the centred coarse blocks. -/
def coarseBlockDevMoment [NeZero d] (nu : ℝ) (ell nn : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (D : Finset (TriadicCube d)) : ℝ :=
  ∑ i : Fin d, Real.sqrt (∫ omega : ShellSeq d,
    |((D.card : ℝ))⁻¹ *
        ∑ z ∈ D, blockDeviation nu ell P nn (Pi.single i (1 : ℝ)) omega z| ^ (2 : ℕ)
    ∂P.toMeasure)

/-- The constant `C2` of display 2: the `d` coordinate directions, the
concentration constant, the colour count `(√d+2)^d` of the printed partition,
the envelope constant `1 + 2C_env(d)` of `bfE_ℓ`, the window comparison factor
`2` twice, and the `e.nablaw.Lt` constant `Cw`. -/
def blockDevConst (d : ℕ) (C0 Cw : ℝ) : ℝ :=
  4 * C0 * (d : ℝ) * blockConcentrationConst *
    Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
    (1 + 2 * cutoffEnvelopeConst d) * Cw

theorem blockDevConst_nonneg (d : ℕ) {C0 Cw : ℝ} (hC0 : 0 ≤ C0) (hCw : 0 ≤ Cw) :
    0 ≤ blockDevConst d C0 Cw := by
  have h1 := blockConcentrationConst_nonneg
  have h2 : (0 : ℝ) ≤ Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) :=
    Real.sqrt_nonneg _
  have h3 := cutoffEnvelopeConst_pos d
  rw [blockDevConst]
  have h4 : (0 : ℝ) ≤ 1 + 2 * cutoffEnvelopeConst d := by linarith only [h3]
  positivity

/-! ## The three elementary comparisons of display 2 -/

/-- The standard basis vector is a unit vector of `Vec d`. -/
private theorem vecNormSq_single (i : Fin d) : vecNormSq (Pi.single i (1 : ℝ)) = 1 := by
  show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
  rw [vecDot_single_left]
  simp

/-- **`bfE_ℓ + shom_ℓ(cu_n) ≤ Cν⁻¹L'`**, the passage from the envelope
amplitude of `l.bfAm.ellip` to the printed factor `ν⁻¹ℓ ≤ ν⁻¹L'` of `e.bL.to.bhomell`.
Both `ν ≤ ν⁻¹L'` and `1 ∨ ℓ ≤ L'` use `ν ≤ 1` and `1 ≤ L'`. -/
theorem envelopeUpperScalar_add_sigmaBarSeq_le [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {ell nn LPrime : ℕ} (hL1 : 1 ≤ LPrime)
    (hellL : ell ≤ LPrime) :
    envelopeUpperScalar d nu ell + sigmaBarSeq nu ell P nn ≤
      2 * (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * ((LPrime : ℕ) : ℝ) := by
  have hsb := sigmaBarSeq_le_envelopeUpperScalar hnu ell hPrefix hJ2 hJ3 hJ4 nn
  have hCe := cutoffEnvelopeConst_pos d
  have hL0 : (1 : ℝ) ≤ ((LPrime : ℕ) : ℝ) := by exact_mod_cast hL1
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hmax : max 1 ((ell : ℕ) : ℝ) ≤ ((LPrime : ℕ) : ℝ) := by
    refine max_le hL0 ?_
    exact_mod_cast hellL
  have hone : (1 : ℝ) ≤ nu⁻¹ * ((LPrime : ℕ) : ℝ) := by
    have h := mul_le_mul hnuinv hL0 zero_le_one (le_trans zero_le_one hnuinv)
    rw [one_mul] at h
    exact h
  have hnuL : nu ≤ nu⁻¹ * ((LPrime : ℕ) : ℝ) := le_trans hnu1 hone
  have hterm : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 ((ell : ℕ) : ℝ) ≤
      2 * cutoffEnvelopeConst d * nu⁻¹ * ((LPrime : ℕ) : ℝ) := by
    have hc : (0 : ℝ) ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hmax hc
  have hexp : 2 * (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * ((LPrime : ℕ) : ℝ) =
      2 * (nu⁻¹ * ((LPrime : ℕ) : ℝ)) +
        2 * (2 * cutoffEnvelopeConst d * nu⁻¹ * ((LPrime : ℕ) : ℝ)) := by
    ring
  have henv : envelopeUpperScalar d nu ell =
      nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 ((ell : ℕ) : ℝ) := rfl
  rw [henv] at hsb ⊢
  linarith only [hsb, hnuL, hterm, hexp]

/-- **The exponent comparison of display 2**: `2d(ℓ'−ℓ)/(d+4) ≤ d(k−ℓ)/2` at
the coarse-block scale `k` of `l.RHS.term3#coarse-block-scale-choice`, i.e. the
second inequality of the display.  It is the third conjunct of
`coarse_block_scale_choice` multiplied by `d/2`; here the ceiling in the
definition of `k` works in the favourable direction, so no rounding constant
appears. -/
theorem rpow_concentration_le_interp (S : ScaleSelection) (hS : S.ell ≤ S.ellPrime) :
    (3 : ℝ) ^ (-((d : ℝ) * ((coarseBlockScale d S - S.ell : ℕ) : ℝ)) / 2) ≤
      (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) * ((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  obtain ⟨hlk, -, h3, -⟩ := coarse_block_scale_choice d S hS
  have hcast1 : ((coarseBlockScale d S - S.ell : ℕ) : ℝ) =
      (coarseBlockScale d S : ℝ) - (S.ell : ℝ) := by
    rw [Nat.cast_sub hlk]
  have hcast2 : ((S.ellPrime - S.ell : ℕ) : ℝ) = (S.ellPrime : ℝ) - (S.ell : ℝ) := by
    rw [Nat.cast_sub hS]
  have hdhalf : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hstep : (d : ℝ) / 2 * ((4 / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ))) ≤
      (d : ℝ) / 2 * ((coarseBlockScale d S : ℝ) - (S.ell : ℝ)) :=
    mul_le_mul_of_nonneg_left h3 hdhalf
  have hid : (d : ℝ) / 2 * ((4 / ((d : ℝ) + 4)) * ((S.ellPrime : ℝ) - (S.ell : ℝ)))
      = 2 * (d : ℝ) / ((d : ℝ) + 4) * ((S.ellPrime : ℝ) - (S.ell : ℝ)) := by
    have hd : ((d : ℝ) + 4) ≠ 0 := by positivity
    field_simp
    ring
  rw [hid] at hstep
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [hcast1, hcast2]
  linarith only [hstep]

/-- **`L' − ℓ ≤ 2h`**: the printed envelope `L'−ℓ = h+3a` of the scale
selection together with the window comparison `4a ≤ h`. -/
theorem LPrime_sub_ell_le_two_mul_window {S : ScaleSelection}
    (hKlog : 4 * ((S.a : ℕ) : ℝ) ≤ ((S.h : ℕ) : ℝ)) :
    ((S.LPrime - S.ell : ℕ) : ℝ) ≤ 2 * ((S.h : ℕ) : ℝ) := by
  have h4 : 4 * S.a ≤ S.h := by exact_mod_cast hKlog
  have hid := S.LPrime_sub_ell
  have hnat : S.LPrime - S.ell ≤ 2 * S.h := by omega
  exact_mod_cast hnat

/-- `m − ℓ' = h`, the printed factor of display 2. -/
theorem m_sub_ellPrime_cast (S : ScaleSelection) :
    ((S.m - S.ellPrime : ℕ) : ℝ) = ((S.h : ℕ) : ℝ) := by
  have h := S.ellPrime_add_h
  have hnat : S.m - S.ellPrime = S.h := by omega
  rw [hnat]

/-! ## Display 2 of `e.bL.to.bhomell` -/

/-- **Display 2 of `e.bL.to.bhomell`**, on the carriers of this
development, i.e. the hypothesis `hBlockDev` of
`e.RHS.term3` at

* the coarse-block scale `k = coarseBlockScale d S` of
  `l.RHS.term3#coarse-block-scale-choice`,
* the fine lattice `D = descendantsAtDepth z' (k−n)`, the scale-`n` sub-cubes of
  a scale-`k` cube `z'` (the printed `3^nℤ^d ∩ cu_k`), and
* the deviation moment `coarseBlockDevMoment`, the printed
  `∑_i E[|avsum_z Y_z^{(i)}|²]^{1/2}`.

The proof is the printed one: `blockDeviation_concentration` on each of the `d`
coordinate directions, the fourth-moment form `nablaW4_of_regbounds` of
`e.nablaw.Lt`, the crude bound `|p|² ≤ ν⁻¹` (`e.p-bound-crude`), the envelope
`bfE_ℓ + shom_ℓ(cu_n) ≤ Cν⁻¹L'`, the window comparison `L'−ℓ ≤ 2h = 2(m−ℓ')`
and the exponent comparison `2d(ℓ'−ℓ)/(d+4) ≤ d(k−ℓ)/2`. -/
theorem blockDev_of_concentration [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {Creg C0 : ℝ} (hCreg : 1 ≤ Creg) (hC0 : 0 ≤ C0)
    {Zw : ShellSeq d → ℝ} (hZwmeas : Measurable Zw)
    (hZwbigO : IsBigO P.toMeasure (gammaSigma 2) Zw
      (Creg * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZwbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Zw omega))
    (hKlog : 4 * ((S.a : ℕ) : ℝ) ≤ ((S.h : ℕ) : ℝ))
    {z' : TriadicCube d} (hz' : z'.scale = ((coarseBlockScale d S : ℕ) : ℤ)) :
    C0 * (coarseBlockDevMoment nu S.ell S.n P
          (descendantsAtDepth z' (coarseBlockScale d S - S.n)) *
        gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2)) ≤
      blockDevConst d C0 (nablaW4SqrtConst Creg) * nu ^ (-(2 : ℝ)) *
          (((S.m - S.ellPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) *
          ((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have hellP : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  obtain ⟨hlk, hkP, -, -⟩ := coarse_block_scale_choice d S hellP
  have hL1 : 1 ≤ S.LPrime := by
    have := hSorder.m_lt_LPrime
    omega
  have hellL : S.ell ≤ S.LPrime := by
    have h1 := hSorder.ell_lt_ellPrime
    have h2 := hSorder.ellPrime_lt_m
    have h3 := hSorder.m_lt_LPrime
    omega
  -- the concentration bound in each coordinate direction
  have hconc : ∀ i : Fin d,
      Real.sqrt (∫ omega : ShellSeq d,
          |(((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                blockDeviation nu S.ell P S.n (Pi.single i (1 : ℝ)) omega z| ^ (2 : ℕ)
          ∂P.toMeasure) ≤
        blockConcentrationConst *
            Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
            (envelopeUpperScalar d nu S.ell + sigmaBarSeq nu S.ell P S.n) *
          (3 : ℝ) ^ (-((d : ℝ) *
            ((coarseBlockScale d S - S.ell : ℕ) : ℝ)) / 2) := fun i =>
    blockDeviation_concentration hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlk
      (vecNormSq_single i) hz'
  -- the sum over the `d` directions
  have hsum : coarseBlockDevMoment nu S.ell S.n P
        (descendantsAtDepth z' (coarseBlockScale d S - S.n)) ≤
      (d : ℝ) * (blockConcentrationConst *
          Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
          (envelopeUpperScalar d nu S.ell + sigmaBarSeq nu S.ell P S.n) *
        (3 : ℝ) ^ (-((d : ℝ) *
          ((coarseBlockScale d S - S.ell : ℕ) : ℝ)) / 2)) := by
    rw [coarseBlockDevMoment]
    refine le_trans (Finset.sum_le_sum fun i _ => hconc i) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the three replacements inside that bound
  have hbs0 : (0 : ℝ) ≤ blockConcentrationConst *
      Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) :=
    mul_nonneg blockConcentrationConst_nonneg (Real.sqrt_nonneg _)
  have hKbig0 : (0 : ℝ) ≤ 2 * (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ *
      ((S.LPrime : ℕ) : ℝ) := by
    have hCe := cutoffEnvelopeConst_pos d
    have hnu0 : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
    have hL0 : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ 1 + 2 * cutoffEnvelopeConst d := by linarith only [hCe]
    positivity
  have hK0 : (0 : ℝ) ≤ envelopeUpperScalar d nu S.ell + sigmaBarSeq nu S.ell P S.n := by
    have h1 := envelopeUpperScalar_pos hnu d S.ell
    have h2 := sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n
    linarith only [h1, h2]
  have hEpos : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) *
      ((coarseBlockScale d S - S.ell : ℕ) : ℝ)) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hE'0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) *
      ((S.ellPrime - S.ell : ℕ) : ℝ))) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hbig : blockConcentrationConst *
        Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
        (envelopeUpperScalar d nu S.ell + sigmaBarSeq nu S.ell P S.n) *
      (3 : ℝ) ^ (-((d : ℝ) * ((coarseBlockScale d S - S.ell : ℕ) : ℝ)) / 2) ≤
      blockConcentrationConst *
          Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
          (2 * (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * ((S.LPrime : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) *
          ((S.ellPrime - S.ell : ℕ) : ℝ))) := by
    have hA := mul_le_mul_of_nonneg_left
      (envelopeUpperScalar_add_sigmaBarSeq_le (nn := S.n) hnu hnu1 hPrefix hJ2 hJ3 hJ4
        hL1 hellL)
      hbs0
    exact mul_le_mul hA (rpow_concentration_le_interp S hellP) hEpos.le
      (mul_nonneg hbs0 hKbig0)
  have hDvb : coarseBlockDevMoment nu S.ell S.n P
        (descendantsAtDepth z' (coarseBlockScale d S - S.n)) ≤
      (d : ℝ) * (blockConcentrationConst *
          Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
          (2 * (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * ((S.LPrime : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) *
          ((S.ellPrime - S.ell : ℕ) : ℝ)))) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hbig (Nat.cast_nonneg d))
  -- the fourth moment of the response gradient
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]
    exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hnabla := nablaW4_of_regbounds d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e he
    p hp w hCreg hZwmeas hZwbigO hZwbound
  have hsig0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hsig : vecNormSq p ≤ nu⁻¹ := by
    rw [hpsq]
    exact sigmaBarStarInvSeq_le_nuInv hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hCw0 : (0 : ℝ) ≤ nablaW4SqrtConst Creg := nablaW4SqrtConst_nonneg Creg
  have hWb : gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) ≤
      nablaW4SqrtConst Creg * (2 * ((S.h : ℕ) : ℝ)) * nu⁻¹ := by
    refine le_trans hnabla ?_
    have h1 : nablaW4SqrtConst Creg * ((S.LPrime - S.ell : ℕ) : ℝ) ≤
        nablaW4SqrtConst Creg * (2 * ((S.h : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (LPrime_sub_ell_le_two_mul_window hKlog) hCw0
    have h2 : (0 : ℝ) ≤ nablaW4SqrtConst Creg * (2 * ((S.h : ℕ) : ℝ)) := by
      have : (0 : ℝ) ≤ ((S.h : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity
    exact mul_le_mul h1 hsig hsig0 h2
  have hW0 : (0 : ℝ) ≤ gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (gradResponseMoment_nonneg 4 4 P w) _
  have hDvb0 : (0 : ℝ) ≤ (d : ℝ) * (blockConcentrationConst *
      Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
      (2 * (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * ((S.LPrime : ℕ) : ℝ)) *
      (3 : ℝ) ^ (-(2 * (d : ℝ) / ((d : ℝ) + 4) *
        ((S.ellPrime - S.ell : ℕ) : ℝ)))) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have := mul_nonneg (mul_nonneg hbs0 hKbig0) hE'0
    exact mul_nonneg hd0 this
  have hprod := mul_le_mul hDvb hWb hW0 hDvb0
  have hnu2 : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hnu),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two, mul_inv]
  refine le_trans (mul_le_mul_of_nonneg_left hprod hC0) (le_of_eq ?_)
  rw [blockDevConst, hnu2, m_sub_ellPrime_cast S]
  ring

/-! ## `l.RHS.term3` from the anchors -/

end

end SuperdiffusionCLT.Section3.Terms
