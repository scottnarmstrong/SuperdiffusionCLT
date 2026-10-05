/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BlupRemainderTail
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsE
public import SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs
public import SuperdiffusionCLT.Probability.OrliczProduct

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# The tail assembly of the printed `e.blupbounds.remainder` witness

The deterministic core `blupbounds_operatorNorm_le` of the proof of `l.blupbounds`
(`BellUpscaleBoundRemainder.lean`) consumes the remainder display
`e.blupbounds.remainder` as a free hypothesis: a witness
`Z` with a `Γ_{1/2}` (hence `Γ_{1/3}`) tail at the printed amplitude
`C ν^{-3} ℓ 3^{-(m-n)}` — at the substituted scales `n < m < ℓ` of
`blupbounds_operatorNorm_le` this is `C ν^{-3} L' 3^{-(ℓ-n)}` — together with a pointwise
form of the localized display.  This module assembles that witness from the two
`Γ₁` factors of the printed proof:

* **The localization scalar `D`.**  The D-estimate on translated cubes
  (`dEstimate_gammaSigma_one_translatedCube`,
  `BlupRemainderTail.lean`) gives
  `D = O_{Γ₁}(C ν^{-2} 3^{-(m-n)})` at the localization scales `(n, m, L)` —
  for the blup scales `(S.n, S.ell, S.LPrime)` the printed amplitude
  `C ν^{-2} 3^{-(ℓ-n)}`.
* **The quadratic carrier.**  The printed display
  `Q·bfA_m(U)Q ≤ 2|b_m(U)| + 2|ħ_U|²|σ_{m,*}^{-1}(U)|` is carried by
  `2·|b_m(z + cu_n)| + 2 ν^{-1} |(k_m - k_ℓ)_{z + cu_n} e|²` through the
  crude quenched ellipticity bound `σ_{*}^{-1} ≤ ν^{-1} Id`
  (`matLoewnerLE_sigmaStarInvCoarse_cutoffCube`).  Its `Γ₁` tail is the sum of
  the `e.Enaught.vs.A.and.Ahom` envelope `|b_m| = O_{Γ₁}(bfE_m)` (with the
  envelope scalar folded into `ν^{-1} L'` for `L' ≥ m ≥ 1`) and the squared
  printed display `|(k_m − k_ℓ)_{cu_n} e|² =
  O_{Γ₁}(C (ℓ − m))` transported to the translated cube.
* **The product.**  The two `Γ₁` factors multiply into a `Γ_{1/2}` tail at the
  product amplitude (`isBigO_gammaSigma_mul`, the multiplication constant of
  `e.multGammasig`), which `isBigO_gammaSigma_of_exponent_le` weakens to the
  printed `Γ_{1/3}` index.  The amplitude algebra
  `ν^{-2} · ν^{-1} = ν^{-3}` and `3^{-(m-n)}` gives the printed amplitude
  `C ν^{-3} L' 3^{-(ℓ-n)}` exactly.

## What remains of the pointwise block display

The witness `blupRemainderZrem` carries the pointwise domination in the
*carrier form* `D · (2|b_m| + 2ν^{-1}|ħ_U e|²) ≤ Zrem`.  Two steps separate
this from the pointwise conjunct of the reduction, which compares
`|b_{L'} − b_m|` with `|b_m| + 2·q(e) + Zrem` at the tested quadratic form
`q(e) = ħ_U^t σ_{m,*}^{-1}(U) ħ_U e`:

1. The deterministic two-term decomposition of the print (the initial
   decomposition display together with the Young step at
   `ep = 1`) at the block carriers — the `blupbounds_operatorNorm_le` machinery produces
   this in the *operator-norm* form, whose quadratic slot is the operator norm
   `|σ_{m,*}^{-1/2} ħ_U|²`, strictly larger than the tested form `q(e)`.
   The tested reading is a *stronger* hypothesis than the printed display; the
   surrounding development uses the tested reading, so the deterministic
   instantiation is not derivable from `blupbounds_operatorNorm_le` as it stands.
2. The scale bookkeeping: the witness here is stated at the fixed scale triple
   `(nn, ell, L)` with the cube realizing scale `nn` (`z.scale = nn`), which is
   the shape the consumer applies; cubes of other scales are covered by the
   same statement with their own `nn ≤ ell`.
-/

namespace SuperdiffusionCLT.Section3.Terms

open scoped MatrixOrder

variable {d : ℕ}

noncomputable section

/-! ## The constants of the tail assembly -/

/-- The `d`-only tail constant of the quadratic carrier: the `Γ₁` triangle
constant times the sum of the two Young amounts' tail constants — the folded
`e.Enaught` envelope constant and the squared increment-display constant. -/
def blupQuadTailConst (d : ℕ) : ℝ :=
  gammaTriangleConst 1 *
    (2 * (1 + 2 * cutoffEnvelopeConst d) + 2 * streamTailConst d)

/-- The quadratic-carrier tail constant is positive. -/
theorem blupQuadTailConst_pos (hd : 0 < d) : 0 < blupQuadTailConst d := by
  have hst : 0 < streamTailConst d := streamTailConst_pos hd
  unfold blupQuadTailConst
  refine mul_pos IndependentSums.gammaTriangleConst_pos ?_
  refine add_pos (mul_pos (by norm_num) ?_) (mul_pos (by norm_num) hst)
  exact add_pos (by norm_num)
    (mul_pos (by norm_num) (cutoffEnvelopeConst_pos d))

/-- The `d`-only constant of the printed `Γ_{1/3}` remainder of
`e.blupbounds.remainder`: the multiplication constant of `e.multGammasig`
at `σ₁ = σ₂ = 1` times the two factor constants. -/
def blupRemainderConst (d : ℕ) : ℝ :=
  orliczProductConst 1 1 * dEstimateConst d * blupQuadTailConst d

/-! ## The quadratic carrier of the localized display -/

/-- **The quadratic carrier of the localized display** (the printed
`2|b_m(U)| + 2|ħ_U|² |σ_{m,*}^{-1}(U)|` at the
carriers used here): twice the coarse block envelope plus twice the crude quenched
ellipticity bound `σ_{m,*}^{-1}(U) ≤ ν^{-1} Id` applied to the squared tested
stream increment. -/
def blupQuadCarrier (nu : ℝ) (ell L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  2 * translatedBlockNorm nu ell omega z +
    2 * nu⁻¹ * translatedStreamNormSq ell L e omega z

/-- The quadratic carrier is a measurable observable of the shell sequence. -/
theorem measurable_blupQuadCarrier [NeZero d] {nu : ℝ} (hnu : 0 < nu) (ell L : ℕ)
    (e : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => blupQuadCarrier nu ell L e omega z := by
  unfold blupQuadCarrier
  exact (Measurable.const_mul (measurable_translatedBlockNorm hnu ell z) 2).add
    (Measurable.const_mul (measurable_translatedStreamNormSq ell L e z) (2 * nu⁻¹))

/-- The printed envelope scalar `bfE_m = ν + 2Cν^{-1}(1 ∨ m)` folds into
`C ν^{-1} m` for `m ≥ 1` and `ν ≤ 1`. -/
theorem envelopeUpperScalar_le_nuInv_mul {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    envelopeUpperScalar d nu m ≤ (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (m : ℝ) := by
  have hinv : (1 : ℝ) ≤ nu⁻¹ := by
    have h := inv_anti₀ hnu hnu1
    rwa [inv_one] at h
  have hmax : max 1 (m : ℝ) = (m : ℝ) := by
    exact max_eq_right (by exact_mod_cast hm)
  unfold envelopeUpperScalar
  rw [hmax]
  have hnu_le : nu ≤ nu⁻¹ * (m : ℝ) := by
    have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hstep := mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg m)
    rw [one_mul] at hstep
    linarith only [hnu1, h1m, hstep]
  calc nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * (m : ℝ)
      ≤ nu⁻¹ * (m : ℝ) + 2 * cutoffEnvelopeConst d * nu⁻¹ * (m : ℝ) :=
        by linarith only [hnu_le]
    _ = (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (m : ℝ) := by ring

/-- **The `Γ₁` tail of the quadratic carrier** (the probabilistic half of the
printed display `Q·bfA_m(U)Q ≤ O_{Γ₁}(C ν^{-1} ℓ)`): at the
carriers used here the quadratic carrier of the localization is
`O_{Γ₁}(C(d) ν^{-1} ℓ)`, with the `d`-only constant `blupQuadTailConst d`.

The proof sums the two `Γ₁` tails by the triangle inequality: the
`e.Enaught` envelope `|b_m(z + cu_n)| = O_{Γ₁}(bfE_m)` with the envelope scalar
folded into `ν^{-1} ℓ` (hence into `ν^{-1} ℓ'`), and the squared printed display
transported to the translated cube
(`isBigO_gammaSigma_translatedStreamNormSq` from the centred-cube form
`isBigO_gammaSigma_translatedStreamNormSq_originCube`). -/
theorem isBigO_gammaSigma_one_blupQuadCarrier [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (nn ell L : ℕ) (hnl : nn < ell) (hlL : ell < L)
    (e : Vec d) (he : vecNormSq e = 1) (z : TriadicCube d)
    (hz : z.scale = (nn : ℤ)) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => blupQuadCarrier nu ell L e omega z)
      (blupQuadTailConst d * nu⁻¹ * (L : ℝ)) := by
  have hdn : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hPrefix.dimension
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hdn
  -- the envelope amount
  have hE := isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 ell z
  have hE2 := hE.const_mul (show (0 : ℝ) ≤ 2 by norm_num)
  have hEm : Measurable fun omega : ShellSeq d =>
      2 * translatedBlockNorm nu ell omega z :=
    Measurable.const_mul (measurable_translatedBlockNorm hnu ell z) 2
  -- the stream term: the squared increment display on the centred cube of the
  -- cube's scale, transported to the cube
  have hS0 := isBigO_gammaSigma_translatedStreamNormSq_originCube (P := P) hPrefix
    hJ2 hJ3 hJ4 (nn := nn) (l := ell) (L := L) hnl.le hlL he
  have hSz : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        translatedStreamNormSq ell L e omega (originCube d z.scale))
      (streamTailConst d * ((L - ell : ℕ) : ℝ)) := by
    rw [hz]
    exact hS0
  have hS := isBigO_gammaSigma_translatedStreamNormSq (P := P) hPrefix hJ2 (l := ell)
    (L := L) e (Q := z) hSz
  have hS2 := hS.const_mul
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (inv_nonneg.mpr hnu.le))
  have hSm : Measurable fun omega : ShellSeq d =>
      (2 * nu⁻¹) * translatedStreamNormSq ell L e omega z :=
    Measurable.const_mul (measurable_translatedStreamNormSq ell L e z) (2 * nu⁻¹)
  -- the triangle sum
  have hE2amp : 0 < 2 * envelopeUpperScalar d nu ell := by
    refine mul_pos (by norm_num) (envelopeUpperScalar_pos hnu d ell)
  have hS2amp : 0 < (2 * nu⁻¹) * (streamTailConst d * ((L - ell : ℕ) : ℝ)) := by
    have hcast : (0 : ℝ) < ((L - ell : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.sub_pos_of_lt hlL)
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr hnu))
      (mul_pos (streamTailConst_pos hdn) hcast)
  have htri := isBigO_gammaSigma_add_of_isBigO (sigma := 1)
    (show (0 : ℝ) < 1 by norm_num) hE2amp hS2amp hE2 hS2 hEm hSm
  -- the amplitude bookkeeping
  have hinv0 : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hEL : (ell : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr hlL.le
  have hsub : ((L - ell : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L ell
  have hterm1 : 2 * envelopeUpperScalar d nu ell ≤
      2 * ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ)) := by
    refine mul_le_mul_of_nonneg_left (le_trans
      (envelopeUpperScalar_le_nuInv_mul hnu hnu1 d (by omega : (1 : ℕ) ≤ ell)) ?_)
      (by norm_num)
    exact mul_le_mul_of_nonneg_left hEL
      (mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((cutoffEnvelopeConst_pos d).le)))
        (inv_nonneg.mpr hnu.le))
  have hterm2 : (2 * nu⁻¹) * (streamTailConst d * ((L - ell : ℕ) : ℝ)) ≤
      2 * streamTailConst d * nu⁻¹ * (L : ℝ) := by
    calc (2 * nu⁻¹) * (streamTailConst d * ((L - ell : ℕ) : ℝ))
        ≤ (2 * nu⁻¹) * (streamTailConst d * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsub (streamTailConst_pos hdn).le)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hinv0)
      _ = 2 * streamTailConst d * nu⁻¹ * (L : ℝ) := by ring
  refine htri.mono_scale ?_
  have hS : 2 * envelopeUpperScalar d nu ell +
      (2 * nu⁻¹) * (streamTailConst d * ((L - ell : ℕ) : ℝ)) ≤
      (2 * (1 + 2 * cutoffEnvelopeConst d) + 2 * streamTailConst d) * nu⁻¹ *
        (L : ℝ) := by
    calc 2 * envelopeUpperScalar d nu ell +
          (2 * nu⁻¹) * (streamTailConst d * ((L - ell : ℕ) : ℝ))
        ≤ 2 * ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (L : ℝ)) +
          2 * streamTailConst d * nu⁻¹ * (L : ℝ) := by linarith only [hterm1, hterm2]
      _ = (2 * (1 + 2 * cutoffEnvelopeConst d) + 2 * streamTailConst d) * nu⁻¹ *
          (L : ℝ) := by ring
  unfold blupQuadTailConst
  exact le_trans (mul_le_mul_of_nonneg_left hS
    (IndependentSums.gammaTriangleConst_pos (σ := (1 : ℝ))).le) (le_of_eq (by ring))

/-! ## The `Γ_{1/3}` remainder witness -/

/-- **The printed remainder witness of `e.blupbounds.remainder`** at the localized display: the
product of the printed localization scalar `D = ν^{-1} M + ν^{-2} M²`
(`translatedIncrementD` at the scale triple `(nn, ell, L)` on the cube translated by
`triadicCubeShift z`) with the quadratic carrier `blupQuadCarrier` of the localized display. -/
def blupRemainderZrem (nu : ℝ) (nn ell L : ℕ) (e : Vec d) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  translatedIncrementD nu (triadicCubeShift z) nn ell L omega *
    blupQuadCarrier nu ell L e omega z

/-- The remainder witness is a measurable observable of the shell sequence. -/
theorem measurable_blupRemainderZrem [NeZero d] {nu : ℝ} (hnu : 0 < nu) (nn ell L : ℕ)
    (e : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => blupRemainderZrem nu nn ell L e omega z := by
  unfold blupRemainderZrem
  exact (measurable_translatedIncrementD nu (triadicCubeShift z) nn ell L).mul
    (measurable_blupQuadCarrier hnu ell L e z)

/-- **The printed `Γ_{1/3}` remainder of `e.blupbounds.remainder`** (item 5 of
the reduction obligation): at the scale triple `nn < ell < L` and on every cube of scale `nn`, the
remainder witness `blupRemainderZrem` has the printed `Γ_{1/3}` tail at the
amplitude `C(d) ν^{-3} ℓ' 3^{-(ℓ-nn)}`, and it dominates the localized display
carrier `D · (2|b_ell| + 2ν^{-1}|ħ e|²)` pointwise.

The proof multiplies the two `Γ₁` factors — the localization scalar `D`
(`dEstimate_gammaSigma_one_translatedCube`, whose witness is the carrier
itself) and the quadratic carrier (`isBigO_gammaSigma_one_blupQuadCarrier`) —
by `isBigO_gammaSigma_mul` at `σ₁ = σ₂ = 1`, whose product index
`1·1/(1+1) = 1/2` is weakened to the printed `Γ_{1/3}` index by
`isBigO_gammaSigma_of_exponent_le`; the amplitude algebra
`ν^{-2} · ν^{-1} = ν^{-3}` folds the product amplitude into the printed
`C(d) ν^{-3} ℓ' 3^{-(ℓ-nn)}`. -/
theorem blupRemainderZrem_gammaSigma_one_third [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (nn ell L : ℕ) (hnl : nn < ell) (hlL : ell < L)
    (e : Vec d) (he : vecNormSq e = 1) (z : TriadicCube d)
    (hz : z.scale = (nn : ℤ)) :
    IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
      (fun omega : ShellSeq d => blupRemainderZrem nu nn ell L e omega z)
      (blupRemainderConst d * nu ^ (-(3 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ)))) := by
  -- the localization scalar and its `Γ₁` tail
  obtain ⟨Z, hZm, hZbig, hZdom⟩ :=
    dEstimate_gammaSigma_one_translatedCube hnu hnu1 hPrefix hJ3 nn ell L hnl hlL
      (triadicCubeShift z)
  have hq2 : 0 ≤ nu ^ (-(2 : ℝ)) := by
    have hrw : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, pow_two, mul_inv]
    rw [hrw]
    positivity
  have hDnn : ∀ omega : ShellSeq d,
      0 ≤ translatedIncrementD nu (triadicCubeShift z) nn ell L omega := by
    intro omega
    unfold translatedIncrementD
    have hosc := translatedIncrementOscBound_nonneg (triadicCubeShift z) nn ell L omega
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr hnu.le) hosc)
      (mul_nonneg hq2 (sq_nonneg _))
  have hZnn : ∀ omega : ShellSeq d, 0 ≤ Z omega := fun omega =>
    le_trans (hDnn omega) (hZdom omega)
  have hDfun := hZbig.of_abs_le fun omega => by
    rw [abs_of_nonneg (hDnn omega), abs_of_nonneg (hZnn omega)]
    exact hZdom omega
  -- the quadratic carrier and its `Γ₁` tail
  have hQ := isBigO_gammaSigma_one_blupQuadCarrier hnu hnu1 hPrefix hJ2 hJ3 hJ4 nn ell L
    hnl hlL e he z hz
  have hA1nn : 0 ≤ dEstimateConst d * nu ^ (-(2 : ℝ)) *
      (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ))) := by
    refine mul_nonneg (mul_nonneg ?_ hq2)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    unfold dEstimateConst
    have hosc0 : 0 ≤ oscTailConst d := by
      unfold oscTailConst
      exact mul_nonneg (upperShellFluxConst_nonneg d)
        IndependentSums.gammaTriangleConst_pos.le
    exact mul_nonneg IndependentSums.gammaTriangleConst_pos.le
      (add_nonneg hosc0 (sq_nonneg _))
  -- the product and its amplitude
  have hdn : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hPrefix.dimension
  have hinv0 : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hA2nn : 0 ≤ blupQuadTailConst d * nu⁻¹ * (L : ℝ) :=
    mul_nonneg (mul_nonneg (blupQuadTailConst_pos hdn).le hinv0) (Nat.cast_nonneg L)
  have hprod := isBigO_gammaSigma_mul (σ₁ := (1 : ℝ)) (σ₂ := (1 : ℝ))
    (by norm_num) (by norm_num) hA1nn hA2nn hDfun hQ
  have hrpow : nu ^ (-(3 : ℝ)) = nu ^ (-(2 : ℝ)) * nu⁻¹ := by
    have hsum : (-(2 : ℝ)) + (-(1 : ℝ)) = -(3 : ℝ) := by norm_num
    rw [← Real.rpow_neg_one, ← Real.rpow_add hnu, hsum]
  have hamp : (dEstimateConst d * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ)))) *
      (blupQuadTailConst d * nu⁻¹ * (L : ℝ)) =
      (dEstimateConst d * blupQuadTailConst d) * nu ^ (-(3 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-(((ell - nn : ℕ) : ℝ))) := by
    rw [hrpow]
    ring
  refine isBigO_gammaSigma_of_exponent_le
    (show ((1 : ℝ) / 3) ≤ ((1 : ℝ) * 1 / ((1 : ℝ) + 1)) by norm_num) ?_
  refine hprod.mono_scale ?_
  exact le_of_eq (by rw [hamp]; unfold blupRemainderConst; ring)

end

end SuperdiffusionCLT.Section3.Terms