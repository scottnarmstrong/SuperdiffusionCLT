/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BlockConcentrationInputs
public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# `hCgBound`, the small inputs: the `Γ₁` envelope of `|b_{L'}|` and its second moment

The proof of the display `e.RHS.term3.A` consumes, among its inputs,
the ellipticity estimate `hEllip`,

`(∫ omega, |b_{L'}(cu_n)|²) ^ (1/4) ≤ Cb (L' ν⁻¹) ^ (1/2)`,

an envelope coming from `l.bfAm.ellip` and `e.Enaught.mixing`.  This
module proves it, with no dependence on the printed data `h` of the
obligation, from the `Γ₁` envelope of the carrier `translatedBlockNorm`
(`isBigO_gammaSigma_translatedBlockNorm_envelope`).

The two steps are:

* `integral_sq_le_of_isBigOWith_gammaSigma_one` — the `Γ₁` second moment: a
  nonnegative observable with `Y = O_{Γ₁}(K)` has `E[Y²] ≤ (2 γ(K))²` with `γ`
  the Chapter 4 moment-growth constant `gammaMomentConst 1` of
  `Homogenization.IndependentSums`.  It is the `σ = 1`, `p = 2` instance of the
  `Γ_σ` moment lemma `integral_rpow_le_of_isBigOWith_gammaSigma`.
* `translatedBlockNorm_sqMoment_envelope` — the envelope of `|b_{L'}(z + cu_n)|`
  and its second moment combined: `(∫ |b_{L'}|²)^{1/4} ≤ bEllipConst d
  (L' ν⁻¹)^{1/2}`, the exact shape of the binder `hEllip` of
  `w_average_difference` at the carrier
  `bNormSq omega = translatedBlockNorm nu S.LPrime omega z ^ 2`.  The constant
  `bEllipConst d` is a `d`-only scalar, as the printed statement demands.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

/-- The `Γ₁` second moment: a nonnegative observable with `Y = O_{Γ₁}(K)` —
the tail relation `P[Y > t K] ≤ exp(-t)` for `t ≥ 1` — has annealed second
moment `E[Y²] ≤ (2 γ(K))²`, with `γ` the Chapter 4 moment-growth constant
`gammaMomentConst 1` of the `Γ_σ` class.  This is the `σ = 1`, `p = 2`
instance of the tail-to-moment lemma
`Homogenization.IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma`,
which computes the second moment of the stretched-exponential tail class. -/
theorem integral_sq_le_of_isBigOWith_gammaSigma_one {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {Y : Omega → ℝ} {K : ℝ}
    (hK : 0 < K) (hYnn : ∀ omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : IsBigOWith mu (gammaSigma 1) Y K) :
    ∫ omega, Y omega ^ (2 : ℝ) ∂mu ≤ (2 * gammaMomentConst 1 * K) ^ (2 : ℝ) := by
  have hp : (1 : ℝ) ≤ 2 := by norm_num
  have hbound := integral_rpow_le_of_isBigOWith_gammaSigma (σ := 1) (p := 2)
    one_pos hK hp hYnn hYm hY
  have hexp : ((2 : ℝ) ^ ((1 : ℝ)⁻¹)) = 2 := by
    rw [show ((1 : ℝ)⁻¹ : ℝ) = 1 from inv_one, Real.rpow_one]
  rw [hexp] at hbound
  have hreorder : gammaMomentConst 1 * 2 * K = 2 * gammaMomentConst 1 * K := by ring
  rw [hreorder] at hbound
  exact hbound

/-- The `d`-only constant of the `hEllip` envelope: the square root of the
product of the `Γ₁` second-moment amplitude `2 γ(K)` (with `γ` the Chapter 4
moment-growth constant `gammaMomentConst 1`) and the deterministic factor
`1 + 2 C` of the envelope scale `envelopeUpperScalar`. -/
noncomputable def bEllipConst (d : ℕ) : ℝ :=
  (2 * gammaMomentConst 1 * (1 + 2 * cutoffEnvelopeConst d)) ^ ((1 : ℝ) / 2)

theorem two_mul_gammaMomentConst_one_nonneg : (0 : ℝ) ≤ 2 * gammaMomentConst 1 := by
  have h1 : (0 : ℝ) < gammaMomentConst 1 := gammaMomentConst_pos one_pos
  linarith only [h1]

theorem one_add_two_mul_cutoffEnvelopeConst_nonneg (d : ℕ) :
    (0 : ℝ) ≤ 1 + 2 * cutoffEnvelopeConst d := by
  have h2 : (0 : ℝ) < cutoffEnvelopeConst d := cutoffEnvelopeConst_pos d
  linarith only [h2]

theorem bEllipConst_nonneg (d : ℕ) : 0 ≤ bEllipConst d := by
  unfold bEllipConst
  exact Real.rpow_nonneg
    (mul_nonneg two_mul_gammaMomentConst_one_nonneg
      (one_add_two_mul_cutoffEnvelopeConst_nonneg d)) ((1 : ℝ) / 2)

/-- **The second moment of the `Γ₁` envelope of `|b_{L'}|`**: for every
translated cube `z + cu_n`, the annealed fourth root of the second moment of
the carrier `translatedBlockNorm` is bounded by the `d`-only scalar
`bEllipConst d` times `(L' ν⁻¹) ^ (1/2)`:

`(∫ |b_{L'}(z + cu_n)|²) ^ (1/4) ≤ bEllipConst d (L' ν⁻¹) ^ (1/2)`.

This is the `hEllip` display of the proof of `e.RHS.term3.A` at the carrier `translatedBlockNorm`:
the constant is `d`-only, and the only standing inputs are the cutoff ellipticity `ν`,
its bound `ν ≤ 1`, the shell-law hypotheses, and `1 ≤ L'`.  The proof reads the
`Γ₁` envelope `isBigO_gammaSigma_translatedBlockNorm_envelope` through
the `Γ₁` second moment (`integral_sq_le_of_isBigOWith_gammaSigma_one`) and
rescales the deterministic envelope scale
`envelopeUpperScalar d nu L = nu + 2 C ν⁻¹ (1 ∨ L')` by `ν ≤ ν⁻¹ ≤ L' ν⁻¹`. -/
theorem translatedBlockNorm_sqMoment_envelope {d : ℕ} [NeZero d] {nu : ℝ}
    {P : ProbabilityMeasure (ShellSeq d)} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (hL : 1 ≤ ((L : ℕ) : ℝ)) (z : TriadicCube d) :
    (∫ omega : ShellSeq d, translatedBlockNorm nu L omega z ^ (2 : ℝ) ∂P.toMeasure) ^
        ((1 : ℝ) / 4) ≤
      bEllipConst d * (((L : ℕ) : ℝ) * nu⁻¹) ^ ((1 : ℝ) / 2) := by
  set A : ℝ := envelopeUpperScalar d nu L with hAdef
  set X : ShellSeq d → ℝ := fun omega => translatedBlockNorm nu L omega z with hXdef
  -- the amplitude, the observable, and its `Γ₁` envelope
  have hA : 0 < A := envelopeUpperScalar_pos hnu d L
  have hnn : ∀ omega : ShellSeq d, 0 ≤ X omega := fun omega =>
    Book.Ch02.matrixOperatorNorm_nonneg _
  have hmeas : AEMeasurable X P.toMeasure :=
    (measurable_translatedBlockNorm hnu L z).aemeasurable
  have hO := isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 L z
  have hwith : IsBigOWith P.toMeasure (gammaSigma 1) X A :=
    hO.of_le fun omega => le_abs_self _
  -- the second moment through the `Γ₁` moment lemma
  have hsq : ∫ omega : ShellSeq d, X omega ^ (2 : ℝ) ∂P.toMeasure ≤
      (2 * gammaMomentConst 1 * A) ^ (2 : ℝ) :=
    integral_sq_le_of_isBigOWith_gammaSigma_one hA hnn hmeas hwith
  have hintnn : (0 : ℝ) ≤ ∫ omega : ShellSeq d, X omega ^ (2 : ℝ) ∂P.toMeasure :=
    MeasureTheory.integral_nonneg fun omega => Real.rpow_nonneg (hnn omega) (2 : ℝ)
  have hM : (0 : ℝ) ≤ 2 * gammaMomentConst 1 * A :=
    mul_nonneg two_mul_gammaMomentConst_one_nonneg hA.le
  -- the fourth root of the second moment
  have hroot : (∫ omega : ShellSeq d, X omega ^ (2 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      (2 * gammaMomentConst 1) ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) := by
    have hstep := Real.rpow_le_rpow hintnn hsq (show (0 : ℝ) ≤ (1 : ℝ) / 4 by norm_num)
    have hexp2 : ((2 * gammaMomentConst 1 * A) ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) =
        (2 * gammaMomentConst 1) ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) := by
      calc ((2 * gammaMomentConst 1 * A) ^ (2 : ℝ)) ^ ((1 : ℝ) / 4)
          = (2 * gammaMomentConst 1 * A) ^ ((2 : ℝ) * ((1 : ℝ) / 4)) :=
            (Real.rpow_mul hM (2 : ℝ) ((1 : ℝ) / 4)).symm
        _ = (2 * gammaMomentConst 1 * A) ^ ((1 : ℝ) / 2) := by
            rw [show ((2 : ℝ) * ((1 : ℝ) / 4)) = (1 : ℝ) / 2 from (by ring : (2 : ℝ) *
              ((1 : ℝ) / 4) = (1 : ℝ) / 2)]
        _ = (2 * gammaMomentConst 1) ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) :=
            Real.mul_rpow two_mul_gammaMomentConst_one_nonneg hA.le
    rw [hexp2] at hstep
    exact hstep
  -- the deterministic rescaling of the envelope scale
  set T : ℝ := (((L : ℕ) : ℝ) * nu⁻¹) with hTdef
  have hLnn : (0 : ℝ) ≤ ((L : ℕ) : ℝ) := by
    have h0 : (0 : ℕ) ≤ L := Nat.zero_le L
    exact_mod_cast h0
  have hTnn : (0 : ℝ) ≤ T :=
    mul_nonneg hLnn (le_of_lt (inv_pos.2 hnu))
  have hkey : nu * nu ≤ 1 := by
    calc nu * nu ≤ 1 * nu := mul_le_mul_of_nonneg_right hnu1 hnu.le
      _ = nu := one_mul nu
      _ ≤ 1 := hnu1
  have hnuinv : nu ≤ nu⁻¹ := by
    have h2 : nu * nu ≤ nu⁻¹ * nu := by
      rw [inv_mul_cancel₀ hnu.ne']
      exact hkey
    exact le_of_mul_le_mul_right h2 hnu
  have hTge : nu⁻¹ ≤ T := by
    rw [hTdef, mul_comm]
    exact le_mul_of_one_le_right (le_of_lt (inv_pos.2 hnu)) hL
  have hnuT : nu ≤ T := le_trans hnuinv hTge
  have hAeq : A = nu + 2 * cutoffEnvelopeConst d * T := by
    rw [hAdef, envelopeUpperScalar, max_eq_right hL, hTdef]
    ring
  have hCnn : (0 : ℝ) ≤ 1 + 2 * cutoffEnvelopeConst d :=
    one_add_two_mul_cutoffEnvelopeConst_nonneg d
  have hexpand : (1 + 2 * cutoffEnvelopeConst d) * T =
      T + 2 * cutoffEnvelopeConst d * T := by ring
  have hAT : A ≤ (1 + 2 * cutoffEnvelopeConst d) * T := by
    rw [hAeq, hexpand]
    linarith only [hnuT]
  -- the conclusion
  have hscale : A ^ ((1 : ℝ) / 2) ≤
      (1 + 2 * cutoffEnvelopeConst d) ^ ((1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2) := by
    have h1 : A ^ ((1 : ℝ) / 2) ≤ ((1 + 2 * cutoffEnvelopeConst d) * T) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hA.le hAT (show (0 : ℝ) ≤ (1 : ℝ) / 2 by norm_num)
    rw [Real.mul_rpow hCnn hTnn] at h1
    exact h1
  have hjoin : (2 * gammaMomentConst 1) ^ ((1 : ℝ) / 2) *
      (1 + 2 * cutoffEnvelopeConst d) ^ ((1 : ℝ) / 2) =
      (2 * gammaMomentConst 1 * (1 + 2 * cutoffEnvelopeConst d)) ^ ((1 : ℝ) / 2) :=
    (Real.mul_rpow two_mul_gammaMomentConst_one_nonneg hCnn).symm
  have hCrootnn : (0 : ℝ) ≤
      (2 * gammaMomentConst 1 * (1 + 2 * cutoffEnvelopeConst d)) ^ ((1 : ℝ) / 2) :=
    bEllipConst_nonneg d
  have hfin : (2 * gammaMomentConst 1) ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2) ≤
      bEllipConst d * T ^ ((1 : ℝ) / 2) := by
    unfold bEllipConst
    refine le_trans (mul_le_mul_of_nonneg_left hscale
      (Real.rpow_nonneg two_mul_gammaMomentConst_one_nonneg ((1 : ℝ) / 2))) ?_
    rw [← mul_assoc, hjoin]
  rw [hTdef]
  exact le_trans hroot hfin

end SuperdiffusionCLT.Section3.Terms