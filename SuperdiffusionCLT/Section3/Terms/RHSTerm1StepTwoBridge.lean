/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnchorsConstFirstB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoOrderOneC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1

/-!
# Step 2 of `l.RHS.term1`: the multiscale bound for an `L̲²` flux

The printed second display of Step 2, `e.decompose.flux.u.n.second`, reads

`E[|⨍_{cu_m} ∇w·(a_ℓ∇ũ_n − q̃)|] ≤ Cν^{-1}(ℓm(m−ℓ))^{1/2}3^{-(ℓ'−ℓ)}`,

and the printed derivation obtains it from the `ℓ²`-in-scales
multiscale line

`E[‖F‖²_{Ĥ̲^{-1}(cu_m)}] ≤ C ∑_{k≤m} 3^{2k} avsum_{z∈3^kℤ^d∩cu_m} E[|(F)_{z+cu_k}|²]`

together with `p.concentration` on `3^ℓ`-blocks.  That multiscale line is not an
inequality: it fails by a factor equal to the number of active scales (and so
does its expectation form for a general stationary field).  The true
multiscale Poincare inequality is `ℓ¹` in scales, and squaring it costs exactly
`(m−ℓ)`, which is sharp for the field at hand because each scale-`k` block
average concentrates.  So the honest size of the display is

`E[|⨍_{cu_m} ∇w·(a_ℓ∇ũ_n − q̃)|] ≤ Cν^{-1}(ℓm)^{1/2}(m−ℓ)3^{-(ℓ'−ℓ)}`,

the printed one times `(m−ℓ)^{1/2} ≤ (2h)^{1/2}`; this is a correction of the
printed text (see `ERRATA.md`).  The printed `e.RHS.term1` is nevertheless
**unchanged**: its closing coarsening of Step 3 already loses more, since
`(ℓm)^{1/2}(m−ℓ) ≤ 4ℓh ≤ 4ℓ²h`.

This file proves `hminus_second_moment_memLp`: the third display of Step 2 at a named constant,
for an `L̲²` centred flux, so with no continuity hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (vecHatNegENormOrderOne)

noncomputable section

/-! ## The third display of Step 2 for an `L̲²` centred flux -/

private theorem threeRpowNegTwoNatBr (k : ℕ) :
    (3 : ℝ) ^ (-(2 * (k : ℝ))) = ((9 : ℝ) ^ k)⁻¹ := by
  rw [Real.rpow_neg (by norm_num),
    show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, pow_mul]
  norm_num

/-- **The third display of Step 2 at a named constant, with no continuity
hypothesis**, in the
order-one carrier and with the honest `ℓ¹` count:
`E[‖a_ℓ∇ũ_n − q̃‖²_{Ĥ̲^{-1}(cu_m)}] ≤ C ν^{-2} ℓ m (m−ℓ)² 3^{2(ℓ−m)} shom_{L',*}`.

This is the version of the third display with a continuity binder `hCont`, with that
binder removed: the multiscale line is taken in the `L̲²`
form `RHSTerm1StepTwoOrderOneC.lintegral_vecHatNegENormOrderOne_sq_le_memLp`, which the
already present `hMemLp` feeds.  This matters because the centred glued flux is
genuinely discontinuous: `GluedField.gluedGradientField` is a sum of indicators
of disjoint triadic sub-cubes. -/
theorem hminus_second_moment_memLp {d : ℕ} [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (uTildeGlued : ShellSeq d → Vec d → Vec d) (qTilde : Vec d)
    (hMemLp : ∀ omega : ShellSeq d,
      MemLp (hilbertifyVecField (fun x =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde)) 2
        (normalizedCubeMeasure (originCube d (S.m : ℤ))))
    (huT : uTildeGlued =
      gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (hQTilde : ENNReal.ofReal (Real.sqrt (vecNormSq qTilde)) ≤
      (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x))) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
    (hMeasDepth : ∀ j : ℕ, AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x) - qTilde))) P.toMeasure)
    (hMeasL2 : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x) - qTilde)) P.toMeasure)
    (Cc : ℝ) (hCc : 1 ≤ Cc)
    (hConcDepth : ∀ j : ℕ,
      (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x) - qTilde)) ∂P.toMeasure : ℝ≥0∞) ≤
        ENNReal.ofReal (Cc *
            (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ))
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x) - qTilde)) ∂P.toMeasure : ℝ≥0∞)) :
    (∫⁻ omega : ShellSeq d,
        (vecHatNegENormOrderOne (originCube d (S.m : ℤ))
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde)) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (hminusSecondMomentConstFirst d Cc * nu ^ (-(2 : ℝ)) *
        ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
        (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)) := by
  have hlm : S.ell < S.m := lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m
  have hL2 := l2_second_moment_bridge' d hnu hnu1 hPrefix hJ2 hJ3 hJ4 S hSorder e
    uTildeGlued qTilde hMemLp huT hQTilde
  have hmain := lintegral_vecHatNegENormOrderOne_sq_le_memLp hd P S.ell S.m hlm
    (fun omega => fun x => matVecMul
      ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (uTildeGlued omega x) - qTilde) hMemLp hMeasDepth hMeasL2 Cc hCc hConcDepth
  refine le_trans (le_trans hmain (mul_le_mul' le_rfl hL2)) ?_
  have hc1 : (1 : ℝ) ≤ multiscaleOrderOneConst d := one_le_multiscaleOrderOneConst d
  have hc0 : (0 : ℝ) ≤ multiscaleOrderOneConst d := le_trans zero_le_one hc1
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans zero_le_one hCc
  have hCL0 : (0 : ℝ) ≤ hminusL2Const d := le_trans zero_le_one (one_le_hminusL2Const d)
  have hnu2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hsig0 : (0 : ℝ) ≤ vecNormSq (fluxSlot nu S.LPrime P S.n e) := vecNormSq_nonneg _
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hJeq : ((9 : ℝ) ^ (S.m - S.ell))⁻¹ =
      (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) := by
    rw [← threeRpowNegTwoNatBr (S.m - S.ell), Nat.cast_sub (le_of_lt hlm)]
    congr 1
    ring
  rw [hJeq]
  set D : ℝ := ((S.m - S.ell : ℕ) : ℝ) with hD
  set W : ℝ := (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) with hW
  have hD0 : (0 : ℝ) ≤ D := by rw [hD]; positivity
  have hW0 : (0 : ℝ) ≤ W := by rw [hW]; exact Real.rpow_nonneg (by norm_num) _
  have hrest0 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) *
      ((S.ell : ℝ) * (S.m : ℝ) * D ^ (2 : ℕ)) * W *
      vecNormSq (fluxSlot nu S.LPrime P S.n e) := by positivity
  have hle : 12 * multiscaleOrderOneConst d ^ (2 : ℕ) * Cc * hminusL2Const d ≤
      hminusSecondMomentConstFirst d Cc := le_max_right _ _
  have hfin := mul_le_mul_of_nonneg_right hle hrest0
  calc 12 * multiscaleOrderOneConst d ^ (2 : ℕ) * Cc * D ^ (2 : ℕ) * W *
        (hminusL2Const d * nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ)) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
      = (12 * multiscaleOrderOneConst d ^ (2 : ℕ) * Cc * hminusL2Const d) *
          (nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ) * D ^ (2 : ℕ)) * W *
            vecNormSq (fluxSlot nu S.LPrime P S.n e)) := by ring
    _ ≤ hminusSecondMomentConstFirst d Cc *
          (nu ^ (-(2 : ℝ)) * ((S.ell : ℝ) * (S.m : ℝ) * D ^ (2 : ℕ)) * W *
            vecNormSq (fluxSlot nu S.LPrime P S.n e)) := hfin
    _ = hminusSecondMomentConstFirst d Cc * nu ^ (-(2 : ℝ)) *
          ((S.ell : ℝ) * (S.m : ℝ) * D ^ (2 : ℕ)) * W *
          vecNormSq (fluxSlot nu S.LPrime P S.n e) := by ring

/-! ## `e.decompose.flux.u.n.second` at a named constant -/

/-! ## The closing coarsening of Step 3 -/

/-! ## `e.decompose.flux.u.n.second` at the honest rate, constant first -/

/-! ## The closing coarsening of Step 3 at the honest Step-2 rate -/

/-! ## `e.RHS.term1` from the honest second step -/

end

end SuperdiffusionCLT.Section3.Terms
