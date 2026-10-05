/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsGateB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm4Anchors

/-!
# `l.RHS.term4` joined to `l.w.basic.regbounds`

Lemma `l.RHS.term4`, with display `e.RHS.term4`, and Lemma `l.w.basic.regbounds`.

The term-4 chain (see `Section3/Terms/RHSTerm4Anchors.lean`) has one hypothesis left, the
fractional `H̲^{1/2}` estimate `e.nablaw.Lt` of the response gradient.  That estimate is the
third conclusion of `l.w.basic.regbounds`, proved in
the response-field development.  The two shapes
agree in every carrier and in the amplitude and differ in exactly one place: the regbounds
conclusion holds `∀ᵐ omega ∂P.toMeasure`, while the pointwise form of the term-4 chain asks for
it at every `omega`.

## Why the a.e. form is the right one

The pointwise form is not recoverable from the a.e. one.  A witness `Z` bounds
`cubeHsENorm (cu_m) (1/2) (∇w(ω))` by `ENNReal.ofReal (Z ω)`, which is never
`⊤`; on the exceptional null set the half norm may well be `⊤`, and no
modification of `Z` can repair that.  So the term-4 chain is re-proved here with
the a.e. hypothesis instead.

Only two steps of the pointwise term-4 chain see the hypothesis pointwise: the
domination of the pairing density by `|p| |X₁| |X₂|`, and the fractional duality
of the proof, whose finiteness binder is read off the same clause.  Both
become a.e. statements, and the single `lintegral_mono` of the integral chain
becomes `lintegral_mono_ae`.  Everything else — the multiplication rule
`l.o.gamma2.mult`, the square root, the second moment, and the closing identity
`|p|² = shom^{-1}_{L',*}` — is untouched, and is isolated below in the abstract
lemma `abs_integral_le_of_isBigO_gammaSigma_two_mul_ae`.

## Main results

* `abs_integral_le_of_isBigO_gammaSigma_two_mul_ae`: the integral chain of
  the end of the proof of `l.RHS.term4`, with the domination assumed only almost surely.
* `l_RHS_term4_constFirst_ae`, `l_RHS_term4_of_anchors_ae`,
  `l_RHS_term4_of_gate_ae`: the three term-4 shapes (constant first; on the two `Γ₂`
  witnesses alone; on the `H̲^{1/2}` estimate alone), with `hWhalf` (and, in the first,
  `hDual`) in their a.e. forms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

/-! ## The closing integral chain, with an a.e. domination -/

/-- **The closing chain of `l.RHS.term4`**, isolated from its carriers: a real
observable `f` dominated **almost surely** by `v |X₁| |X₂|`, with `X₁ = O_{Γ₂}(A₁)` and
`X₂ = O_{Γ₂}(A₂)`, has

`|E[f]| ≤ v · 4 A₁ A₂`.

The multiplication rule `l.o.gamma2.mult` gives `|X₁ X₂| = O_{Γ₁}(2 A₁ A₂)`
(the constant `orliczProductConst 2 2 = 2`), its square root is `O_{Γ₂}` at the
square root amplitude, and the second moment of a `Γ₂` variable costs the factor
`1 + Γ(2) = 2`; the product of the two twos is the printed `4`.  The domination
enters only through `lintegral_mono_ae`. -/
theorem abs_integral_le_of_isBigO_gammaSigma_two_mul_ae
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X₁ X₂ f : Omega → ℝ} {A₁ A₂ v : ℝ}
    (hX₁m : Measurable X₁) (hX₂m : Measurable X₂)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hv : 0 ≤ v)
    (hX₁O : IsBigO mu (gammaSigma 2) X₁ A₁)
    (hX₂O : IsBigO mu (gammaSigma 2) X₂ A₂)
    (hdom : ∀ᵐ omega ∂mu,
      ENNReal.ofReal |f omega| ≤
        ENNReal.ofReal (v * (|X₁ omega| * |X₂ omega|))) :
    |∫ omega, f omega ∂mu| ≤ v * ((4 : ℝ) * (A₁ * A₂)) := by
  have hZnn : ∀ omega : Omega, (0 : ℝ) ≤ |X₁ omega| * |X₂ omega| :=
    fun omega => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h₁' : IsBigOWith mu (gammaSigma (2 : ℝ))
      (fun omega => |X₁ omega|) A₁ := hX₁O
  have h₂' : IsBigOWith mu (gammaSigma (2 : ℝ))
      (fun omega => |X₂ omega|) A₂ := hX₂O
  have hC22 : Probability.orliczProductConst (2 : ℝ) (2 : ℝ) = (2 : ℝ) := by
    rw [Probability.orliczProductConst,
      show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = (1 : ℝ) from by norm_num, Real.rpow_one]
  -- the multiplication rule `l.o.gamma2.mult`
  have hprod : IsBigOWith mu (gammaSigma (1 : ℝ))
      (fun omega => |X₁ omega| * |X₂ omega|) ((2 : ℝ) * (A₁ * A₂)) := by
    have hprod₀ :=
      Probability.isBigOWith_gammaSigma_mul (σ₁ := (2 : ℝ)) (σ₂ := (2 : ℝ))
        zero_lt_two zero_lt_two hA₁.le hA₂.le
        (fun _omega => abs_nonneg _) (fun _omega => abs_nonneg _) h₁' h₂'
    rw [show ((2 : ℝ) * (2 : ℝ)) / ((2 : ℝ) + (2 : ℝ)) = (1 : ℝ) from by norm_num,
      hC22] at hprod₀
    exact hprod₀
  have hK : (0 : ℝ) < (2 : ℝ) * (A₁ * A₂) := by positivity
  -- the square root of the product
  have hpow : IsBigOWith mu (gammaSigma (2 : ℝ))
      (fun omega => (|X₁ omega| * |X₂ omega|) ^ ((1 : ℝ) / 2))
      (((2 : ℝ) * (A₁ * A₂)) ^ ((1 : ℝ) / 2)) := by
    have h := Probability.isBigOWith_gammaSigma_rpow_fwd (mu := mu)
      (σ := (1 : ℝ)) (p := (1 : ℝ) / 2)
      (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hK.le hZnn hprod
    rw [show (1 : ℝ) / ((1 : ℝ) / 2) = (2 : ℝ) from by norm_num] at h
    exact h
  have hKA : (0 : ℝ) < ((2 : ℝ) * (A₁ * A₂)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hK ((1 : ℝ) / 2)
  have hZm : Measurable (fun omega => |X₁ omega| * |X₂ omega|) :=
    (continuous_abs.measurable.comp hX₁m).mul (continuous_abs.measurable.comp hX₂m)
  have hYm : AEMeasurable
      (fun omega => (|X₁ omega| * |X₂ omega|) ^ ((1 : ℝ) / 2)) mu :=
    hZm.aemeasurable.pow measurable_const.aemeasurable
  have hIsBigO : IsBigO mu (gammaSigma (2 : ℝ))
      (fun omega => (|X₁ omega| * |X₂ omega|) ^ ((1 : ℝ) / 2))
      (((2 : ℝ) * (A₁ * A₂)) ^ ((1 : ℝ) / 2)) :=
    (Probability.isBigOWith_iff_isBigO_of_nonneg
      (fun omega => Real.rpow_nonneg (hZnn omega) ((1 : ℝ) / 2))).mp hpow
  have hLHSmass : ∀ omega : Omega,
      |(|X₁ omega| * |X₂ omega|) ^ ((1 : ℝ) / 2)| ^ (((2 : ℕ) : ℝ))
        = |X₁ omega| * |X₂ omega| := by
    intro omega
    rw [abs_of_nonneg (Real.rpow_nonneg (hZnn omega) ((1 : ℝ) / 2)),
      ← Real.rpow_mul (hZnn omega),
      show ((1 : ℝ) / 2) * (((2 : ℕ) : ℝ)) = (1 : ℝ) from by norm_num, Real.rpow_one]
  -- the second moment
  have hint : ∫ omega, |X₁ omega| * |X₂ omega| ∂mu ≤ (4 : ℝ) * (A₁ * A₂) := by
    have hstep := Probability.abs_moment_le_of_isBigO_gammaSigma_two (mu := mu)
      (X := fun omega => (|X₁ omega| * |X₂ omega|) ^ ((1 : ℝ) / 2))
      hKA hYm hIsBigO (2 : ℕ)
    simp only [hLHSmass] at hstep
    rw [← Real.rpow_mul hK.le] at hstep
    rw [show (((1 : ℝ) / 2) * (((2 : ℕ) : ℝ)) = (1 : ℝ)) from by norm_num,
      Real.rpow_one] at hstep
    rw [show (((2 : ℕ) : ℝ) / 2 + 1) = (2 : ℝ) from by norm_num,
      Real.Gamma_two] at hstep
    rw [show ((2 : ℝ) * (A₁ * A₂)) * (1 + 1) = ((4 : ℝ) * (A₁ * A₂)) from by ring]
      at hstep
    exact hstep
  have hYnn : ∀ omega : Omega, (0 : ℝ) ≤ v * (|X₁ omega| * |X₂ omega|) :=
    fun omega => mul_nonneg hv (hZnn omega)
  have hZint : MeasureTheory.Integrable
      (fun omega => v * (|X₁ omega| * |X₂ omega|)) mu := by
    have hbase : MeasureTheory.Integrable
        (fun omega => |X₁ omega| * |X₂ omega|) mu := by
      have hcast : (fun omega => |X₁ omega| * |X₂ omega|) =
          fun omega =>
            |(fun omega => (|X₁ omega| * |X₂ omega|) ^ ((1 : ℝ) / 2)) omega|
              ^ (((2 : ℕ) : ℝ)) := by
        funext omega
        exact (hLHSmass omega).symm
      rw [hcast]
      exact Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two hKA hYm
        hIsBigO (2 : ℕ)
    exact hbase.const_mul v
  have hYmeas : Measurable (fun omega => v * (|X₁ omega| * |X₂ omega|)) :=
    measurable_const.mul hZm
  have hLint : ENNReal.ofReal
      (∫ omega, v * (|X₁ omega| * |X₂ omega|) ∂mu)
      = ∫⁻ omega, ENNReal.ofReal (v * (|X₁ omega| * |X₂ omega|)) ∂mu :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hZint
      (Filter.Eventually.of_forall (fun omega => hYnn omega))
  have hfin : (∫⁻ omega,
      ENNReal.ofReal (v * (|X₁ omega| * |X₂ omega|)) ∂mu) ≠ (⊤ : ℝ≥0∞) := by
    rw [← hLint]
    exact ENNReal.ofReal_ne_top
  have hYbound : ∫ omega, v * (|X₁ omega| * |X₂ omega|) ∂mu
      ≤ v * ((4 : ℝ) * (A₁ * A₂)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hint hv
  calc |∫ omega, f omega ∂mu|
      ≤ ENNReal.toReal (∫⁻ omega, ENNReal.ofReal |f omega| ∂mu) := by
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_lintegral_norm (fun omega => f omega)
    _ ≤ ENNReal.toReal
        (∫⁻ omega, ENNReal.ofReal (v * (|X₁ omega| * |X₂ omega|)) ∂mu) :=
        ENNReal.toReal_mono hfin (lintegral_mono_ae hdom)
    _ = ∫ omega, v * (|X₁ omega| * |X₂ omega|) ∂mu :=
        (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (f := fun omega => v * (|X₁ omega| * |X₂ omega|))
          (Filter.Eventually.of_forall (fun omega => hYnn omega))
          hYmeas.aestronglyMeasurable).symm
    _ ≤ v * ((4 : ℝ) * (A₁ * A₂)) := hYbound

/-! ## `e.RHS.term4`, constant first, on a.e. inputs -/

/-- **`l.RHS.term4`** (`e.RHS.term4`), with the constant quantified first,
with the two clauses that the proof reads pointwise weakened to their almost
sure forms: the `H̲^{1/2}` bound of `_hWhalf` and the fractional duality
`_hDual` of the proof.  The `W^{-1/2,2}` clause `_hKminussp` stays pointwise,
because the duality binder of `hDual_of_isDirichletResponse` needs the finiteness
of that half norm at the very `omega` at which it is applied.

The witness is unchanged: `termFourConst C₁ C₂ = max 1 (4 C₁ C₂)`. -/
theorem l_RHS_term4_constFirst_ae
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁) (C₂ : ℝ) (hC₂ : 1 ≤ C₂) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
        (_hKminussp : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C₁ * (3 : ℝ) ^ (((S.ellPrime : ℕ) : ℝ) / 2)) ∧
          ∀ omega : ShellSeq d,
            Section2.Norms.matHatNegENorm (originCube d (S.m : ℤ))
                ((1 : ℝ) / 2) (2 : ℝ≥0∞)
                (fun x => streamCutoff omega S.ellPrime x -
                  streamCutoff omega S.ell x) ≤
              ENNReal.ofReal (X omega))
        (_hWhalf : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C₂ * (Real.sqrt (vecNormSq p) *
              (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ) / 2)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
                (hilbertifyVecField (w omega).toH1Function.grad) ≤
              ENNReal.ofReal (X omega))
        (_hDual : ∀ᵐ omega ∂P.toMeasure,
          |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                streamCutoff omega S.ell y)
                  ((w omega).toH1Function.grad y)))| ≤
            (Section2.Norms.matHatNegENorm (originCube d (S.m : ℤ))
                  ((1 : ℝ) / 2) (2 : ℝ≥0∞)
                  (fun x => streamCutoff omega S.ellPrime x -
                    streamCutoff omega S.ell x)).toReal *
              (Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ))
                  ((1 : ℝ) / 2)
                  (hilbertifyVecField (w omega).toH1Function.grad)).toReal *
              vecNorm p),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y)
                ((w omega).toH1Function.grad y)))
          ∂P.toMeasure| ≤
          C * (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) := by
  have _ := hd
  refine ⟨termFourConst C₁ C₂, one_le_termFourConst C₁ C₂, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    hKminussp hWhalf hDual
  have _ := hnu1
  have _ := hJ1V2
  have _ := hSorder
  have _ := hw
  obtain ⟨X₁, hX₁m, hX₁O, hX₁pt⟩ := hKminussp
  obtain ⟨X₂, hX₂m, hX₂O, hX₂pt⟩ := hWhalf
  set pairDens : ShellSeq d → ℝ := fun omega =>
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
      (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
        streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
  set negNorm : ShellSeq d → ℝ≥0∞ := fun omega =>
    Section2.Norms.matHatNegENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
      (2 : ℝ≥0∞)
      (fun x => streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
  set cubeNorm : ShellSeq d → ℝ≥0∞ := fun omega =>
    Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
      (hilbertifyVecField (w omega).toH1Function.grad)
  set a : ℝ := (((S.ellPrime : ℕ) : ℝ) / 2)
  -- the closing identity: |p|² = shom⁻¹ = (sigmaBarStarInvSqrt)²
  have hSeq : vecNormSq p =
      Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
  have hsqrtsq : (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ)
      = Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n :=
    sq_sigmaBarStarInvSqrt hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hSeqpos : 0 < Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n :=
    Section2.Annealed.sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hSpos : (0 : ℝ) < Real.sqrt (vecNormSq p) := by
    rw [hSeq]
    exact Real.sqrt_pos.2 hSeqpos
  have hsqrtv : Real.sqrt (vecNormSq p) = vecNorm p := by
    rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg p)]
  have hsqv : vecNorm p * Real.sqrt (vecNormSq p) = vecNormSq p := by
    rw [hsqrtv, ← vecNorm_sq_eq_vecNormSq, pow_two]
  -- the two printed amplitudes are positive
  have hA₁a : (0 : ℝ) < (3 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hA₁ : (0 : ℝ) < C₁ * (3 : ℝ) ^ a :=
    mul_pos (lt_of_lt_of_le zero_lt_one hC₁) hA₁a
  have hA₂b : (0 : ℝ) < Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-a) :=
    mul_pos hSpos (Real.rpow_pos_of_pos (by norm_num) (-a))
  have hA₂ : (0 : ℝ) < C₂ * (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-a)) :=
    mul_pos (lt_of_lt_of_le zero_lt_one hC₂) hA₂b
  -- the pointwise domination of the pairing density, almost surely
  have htoRealAbs : ∀ r : ℝ, (ENNReal.ofReal r).toReal ≤ |r| := by
    intro r
    rcases le_total 0 r with hpos | hneg
    · rw [ENNReal.toReal_ofReal hpos]
      exact le_abs_self (r : ℝ)
    · rw [ENNReal.ofReal_eq_zero.2 hneg, ENNReal.toReal_zero]
      exact abs_nonneg _
  have hdom : ∀ᵐ omega ∂P.toMeasure,
      ENNReal.ofReal |pairDens omega| ≤
        ENNReal.ofReal (vecNorm p * (|X₁ omega| * |X₂ omega|)) := by
    filter_upwards [hX₂pt, hDual] with omega hX₂ptw hDualw
    have hmono₁ : (negNorm omega).toReal ≤ |X₁ omega| :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hX₁pt omega)).trans
        (htoRealAbs (X₁ omega))
    have hmono₂ : (cubeNorm omega).toReal ≤ |X₂ omega| :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hX₂ptw).trans
        (htoRealAbs (X₂ omega))
    have hprodle : (negNorm omega).toReal * (cubeNorm omega).toReal
        ≤ |X₁ omega| * |X₂ omega| :=
      mul_le_mul hmono₁ hmono₂ ENNReal.toReal_nonneg (abs_nonneg _)
    refine ENNReal.ofReal_le_ofReal (le_trans hDualw ?_)
    have hv : (0 : ℝ) ≤ vecNorm p := vecNorm_nonneg p
    calc (negNorm omega).toReal * (cubeNorm omega).toReal * vecNorm p
        ≤ |X₁ omega| * |X₂ omega| * vecNorm p :=
          mul_le_mul_of_nonneg_right hprodle hv
      _ = vecNorm p * (|X₁ omega| * |X₂ omega|) := by ring
  -- the integral chain, with the domination read almost surely
  have hchain := abs_integral_le_of_isBigO_gammaSigma_two_mul_ae
    (mu := P.toMeasure) (f := pairDens) hX₁m hX₂m hA₁ hA₂ (vecNorm_nonneg p)
    hX₁O hX₂O hdom
  -- the chain stops at `4 C₁ C₂ |p|²`, and `|p|² = shom⁻¹` is the closing step
  have hex : (3 : ℝ) ^ a * (3 : ℝ) ^ (-a) = (1 : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < (3 : ℝ)),
      show a + -a = (0 : ℝ) from by ring, Real.rpow_zero]
  have hval : vecNorm p * ((4 : ℝ) * ((C₁ * (3 : ℝ) ^ a) *
      (C₂ * (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-a)))))
      = ((4 : ℝ) * C₁ * C₂) * vecNormSq p := by
    calc vecNorm p * ((4 : ℝ) * ((C₁ * (3 : ℝ) ^ a) *
          (C₂ * (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-a)))))
        = (((4 : ℝ) * C₁ * C₂) * (vecNorm p * Real.sqrt (vecNormSq p))) *
          ((3 : ℝ) ^ a * (3 : ℝ) ^ (-a)) := by ring
      _ = ((4 : ℝ) * C₁ * C₂) * vecNormSq p := by rw [hex, hsqv]; ring
  have hsig : (0 : ℝ) ≤ (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) :=
    sq_nonneg _
  calc |∫ omega, pairDens omega ∂P.toMeasure|
      ≤ vecNorm p * ((4 : ℝ) * ((C₁ * (3 : ℝ) ^ a) *
          (C₂ * (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-a))))) := hchain
    _ = ((4 : ℝ) * C₁ * C₂) * vecNormSq p := hval
    _ = ((4 : ℝ) * C₁ * C₂) *
        (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) := by
        rw [hsqrtsq, ← hSeq]
    _ ≤ termFourConst C₁ C₂ *
        (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hsig

/-! ## `e.RHS.term4` on the a.e. `H̲^{1/2}` estimate -/

/-- **`l.RHS.term4`** on the two `Γ₂` witnesses alone, exactly as
the same statement, with the `H̲^{1/2}` clause `_hWhalf` read
almost surely.  The fractional duality is discharged by
`hDual_of_isDirichletResponse`; since its `H̲^{1/2}` finiteness binder now holds
only off a null set, the duality itself is produced almost surely, which is what
`l_RHS_term4_constFirst_ae` consumes. -/
theorem l_RHS_term4_of_anchors_ae
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁) (C₂ : ℝ) (hC₂ : 1 ≤ C₂) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
        (_hKminussp : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C₁ * (3 : ℝ) ^ (((S.ellPrime : ℕ) : ℝ) / 2)) ∧
          ∀ omega : ShellSeq d,
            Section2.Norms.matHatNegENorm (originCube d (S.m : ℤ))
                ((1 : ℝ) / 2) (2 : ℝ≥0∞)
                (fun x => streamCutoff omega S.ellPrime x -
                  streamCutoff omega S.ell x) ≤
              ENNReal.ofReal (X omega))
        (_hWhalf : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C₂ * (Real.sqrt (vecNormSq p) *
              (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ) / 2)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
                (hilbertifyVecField (w omega).toH1Function.grad) ≤
              ENNReal.ofReal (X omega)),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y)
                ((w omega).toH1Function.grad y)))
          ∂P.toMeasure| ≤
          C * (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) := by
  obtain ⟨C, hC1, hmain⟩ := l_RHS_term4_constFirst_ae d hd C₁ hC₁ C₂ hC₂
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    hKminussp hWhalf
  have hlow : S.ell ≤ S.ellPrime := hSorder.ell_lt_ellPrime.le
  have hhigh : S.ellPrime ≤ S.LPrime := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := hSorder.m_lt_LPrime
    omega
  obtain ⟨X₁, hX₁m, hX₁O, hX₁pt⟩ := hKminussp
  obtain ⟨X₂, hX₂m, hX₂O, hX₂pt⟩ := hWhalf
  refine hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    ⟨X₁, hX₁m, hX₁O, hX₁pt⟩ ⟨X₂, hX₂m, hX₂O, hX₂pt⟩ ?_
  filter_upwards [hX₂pt] with omega hX₂ptw
  exact hDual_of_isDirichletResponse hd omega hlow hhigh p (w omega) (hw omega)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hX₁pt omega))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hX₂ptw)

/-! ## `e.RHS.term4` on the a.e. `H̲^{1/2}` estimate, gate discharged -/

/-- **`l.RHS.term4`** (`e.RHS.term4`), on the single
remaining hypothesis — the fractional `H̲^{1/2}` estimate of `e.nablaw.Lt` —
read almost surely.  This is the shape in which
`l.w.basic.regbounds` proves it. -/
theorem l_RHS_term4_of_gate_ae
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (C₂ : ℝ) (hC₂ : 1 ≤ C₂) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
        (_hWhalf : ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IsBigO P.toMeasure (gammaSigma 2) X
            (C₂ * (Real.sqrt (vecNormSq p) *
              (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ) / 2)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
                (hilbertifyVecField (w omega).toH1Function.grad) ≤
              ENNReal.ofReal (X omega)),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y)
                ((w omega).toH1Function.grad y)))
          ∂P.toMeasure| ≤
          C * (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) := by
  obtain ⟨CTwo, hgateS⟩ :=
    SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨CZero, COne, hgateP⟩ := hgateS ((1 : ℝ) / 2) (by norm_num) (by norm_num)
  obtain ⟨Cg, hgateG⟩ := hgateP (2 : ℝ) (by norm_num)
  have hC₁ : (1 : ℝ) ≤ |Cg| + 1 := by
    have := abs_nonneg Cg
    linarith only [this]
  obtain ⟨C, hC1, hmain⟩ := l_RHS_term4_of_anchors_ae d hd (|Cg| + 1) hC₁ C₂ hC₂
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw hWhalf
  have _ := CZero
  have _ := COne
  have _ := CTwo
  have hlt : S.ell < S.ellPrime := hSorder.ell_lt_ellPrime
  have hle : S.ellPrime ≤ S.m := hSorder.ellPrime_lt_m.le
  have hKm := exists_kmnWminussp_of_gate (P := P) (C := Cg) (l := S.m)
    (m := S.ellPrime) (n := S.ell) hlt.le
    ((hgateG P hPrefix hJ1V2 hJ2 hJ3 hJ4).1 S.m S.ellPrime S.ell hlt hle).1
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    hKm hWhalf

/-! ## The join: `e.RHS.term4` from `l.w.basic.regbounds` -/

end

end SuperdiffusionCLT.Section3.Terms
