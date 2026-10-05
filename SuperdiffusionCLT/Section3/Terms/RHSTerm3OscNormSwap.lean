/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscMeanZero
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Duality
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscMembership
public import SuperdiffusionCLT.Section3.Terms.MultiscalePoincareFlux
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB

/-!
# The norm swap: `3^n` on the flux side instead of the carrier

The printed duality pairs the hatted negative norm of the flux with the carrier
`[∇w − (∇w)_{z+cu_n}]_{\underline H^1(z+cu_n)}` without any power of `3`.  The
chain with the *centred*-gradient carrier — which carries the
zero-order Poincare summand, and with it the scale factor `3^n` — pairs it
instead with the order-one hatted norm `vecHatNegENormOrderOne` of the flux.  This
module moves the scale factor from the carrier to the flux: the seminorm carrier
(the dual of the centred test class `CentredSeminormTestField`) is paired with the
order-one hatted norm of the flux, at the price of a comparison constant.

## The comparison: one direction is a theorem, the other is false

* `vecHatNegENormOrderOne Q F ≤ centredSeminormNegNorm Q F` is **false** at every
  `d ≥ 2`.  A nonzero *constant* flux is the witness: members of the centred
  class have mean-zero fields, so the
  centred-class norm of `fun _ => c` is `0`, while the order-one class contains
  the mean-zero affine potential `x ↦ c·x − ⍍_Q (c··)`, whose gradient is `c`
  and whose Hessian vanishes, giving `vecHatNegENormOrderOne Q (fun _ => c) ≥
  vecNormSq c > 0`.
* `centredSeminormNegNorm Q F ≤ ofReal (3^{scale Q} · (C_d + 3)) · vecHatNegENormOrderOne Q F`
  is a **theorem** for every `L²(Q)` flux (`centredSeminormNegNorm_le_vecHatNegENormOrderOne`),
  with `C_d = (originCubeMeanZeroH1CoerciveEstimate d 0).constant`.

The constant of the surviving direction is the *per-cube* scale factor
`3^{scale Q}·(C_d + 3)`: it is not removable, because the centred class controls
only the Hessian while the order-one class controls the gradient itself.

## The consequence for the display

The comparison constant carries `3^{scale R} = 3^n` on every scale-`n` sub-cube,
so the flux moment gains `3^{3n/2}` while the carrier drops the `(3^n)³` of the
zero-order Poincare summand of the centred-gradient carrier: the swap relocates the `3^n`
without changing the product, and does not by itself make `CB` scale-free.
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
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (vecHatTestH1ENorm vecHatNegENormOrderOne ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul)

noncomputable section

variable {d : ℕ}

/-! ## The mean-zero property of the centred test class

The class `CentredSeminormTestField` centres the gradient by the average of the
*same* gradient over the *same* cube, so every member field is mean zero.  The
docstring of the class records this; the two lemmas below prove it, and they are
what makes a constant flux invisible to the centred-class norm. -/

/-! ## Direction 1 is false: the constant-flux witness -/

/-! ## Direction 2 holds: the centred norm is dominated by the order-one hatted
norm of the flux, at the price of the per-cube scale factor

The comparison constant is `3^{scale Q}·(C_d + 3)`, and it is *exactly* the
per-cube Poincaré constant: the centred class controls the Hessian while the
order-one class controls the gradient, and `3^{scale Q}·C_d` is the exchange
rate between them (`vecCubeLpENorm_toField_le`).  The extra `3` absorbs the
`(1 + 3^{scale Q})·eps` error of the smooth approximation at a level `eps` small
enough that `(1 + 3^{scale Q})·eps ≤ 3^{scale Q}`. -/

/-- **The density input of the comparison.**  For every member `T` of the centred
class and every `eps > 0` there is a smooth mean-zero potential `g` whose order-one
test norm is at most `3^{scale Q}·(C_d + 3)` and which approximates `T.toField`
in `L̲²(Q)` to within `eps`.  The potential is the output of
`exists_centeredOrderOneTestPotential`; the level is what its displayed constant
costs, with `vecCubeLpENorm_toField_le` and the class level `T.seminorm_le_one`
used, and the approximation error absorbed by the scale factor. -/
theorem exists_smooth_test_of_centred_member {Q : TriadicCube d}
    (T : CentredSeminormTestField Q) {eps : ℝ} (heps : 0 < eps) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      volumeAverage (cubeSet Q) g = 0 ∧
      vecHatTestH1ENorm Q g ≤ ENNReal.ofReal ((3 : ℝ) ^ ((Q.scale : ℝ)) *
        ((originCubeMeanZeroH1CoerciveEstimate d 0).constant + 3)) ∧
      vecCubeLpENorm Q 2 (fun x => T.toField x - euclideanGradient g x) ≤
        ENNReal.ofReal eps := by
  have hCd0 : 0 ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hspos : 0 < (3 : ℝ) ^ ((Q.scale : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) ((Q.scale : ℝ))
  have h1s : (0 : ℝ) < 1 + (3 : ℝ) ^ ((Q.scale : ℝ)) := by linarith only [hspos]
  set δ : ℝ := min eps
    ((3 : ℝ) ^ ((Q.scale : ℝ)) / (1 + (3 : ℝ) ^ ((Q.scale : ℝ)))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min heps (div_pos hspos h1s)
  have hδeps : δ ≤ eps := by
    rw [hδdef]
    exact min_le_left _ _
  have hδs : (1 + (3 : ℝ) ^ ((Q.scale : ℝ))) * δ ≤ (3 : ℝ) ^ ((Q.scale : ℝ)) := by
    have hle : δ ≤ (3 : ℝ) ^ ((Q.scale : ℝ)) / (1 + (3 : ℝ) ^ ((Q.scale : ℝ))) := by
      rw [hδdef]
      exact min_le_right _ _
    refine le_trans (mul_le_mul_of_nonneg_left hle (le_of_lt h1s)) ?_
    rw [mul_div_cancel₀ _ (ne_of_gt h1s)]
  obtain ⟨g, hgc, hmz, hnorm, hclose⟩ :=
    exists_centeredOrderOneTestPotential (Q := Q) T.hess (eps := δ) hδpos
  refine ⟨g, hgc, hmz, ?_, ?_⟩
  · refine le_trans hnorm (ENNReal.ofReal_le_ofReal ?_)
    have hA : (vecCubeLpENorm Q 2 (fun x : Vec d => T.pot.grad x -
        volumeAverageVec (openCubeSet Q) T.pot.grad)).toReal ≤
        (3 : ℝ) ^ ((Q.scale : ℝ)) *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant := by
      have hC0 : 0 ≤ cubeScaleFactor Q *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
        mul_nonneg (le_of_lt (by
          simpa only [cubeScaleFactor] using
            zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)) hCd0
      have h := ENNReal.toReal_le_of_le_ofReal hC0 (vecCubeLpENorm_toField_le T)
      have hscale : cubeScaleFactor Q = (3 : ℝ) ^ ((Q.scale : ℝ)) :=
        (Real.rpow_intCast 3 Q.scale).symm
      rwa [hscale] at h
    have hB : (Section2.Norms.cubeLpENorm Q 2 (fun x : Vec d =>
        HilbertMat.ofMat (fun i j => T.hess.hess i j x))).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) T.seminorm_le_one
      rwa [ENNReal.toReal_one] at h
    have hB' : (3 : ℝ) ^ ((Q.scale : ℝ)) * (Section2.Norms.cubeLpENorm Q 2
        (fun x : Vec d => HilbertMat.ofMat (fun i j => T.hess.hess i j x))).toReal ≤
        (3 : ℝ) ^ ((Q.scale : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hB (le_of_lt hspos)
    linarith only [hA, hB', hδs, hspos]
  · exact le_trans hclose (ENNReal.ofReal_le_ofReal hδeps)

/-- **Direction 2 of the comparison is a theorem.**  For every `L²(Q)` flux `F`
the centred-class negative norm is dominated by the order-one hatted negative
norm of `F`, at the price of `3^{scale Q}·(C_d + 3)` with
`C_d = (originCubeMeanZeroH1CoerciveEstimate d 0).constant`.  The proof feeds the
dense smooth test potentials of `exists_smooth_test_of_centred_member` to the
order-one duality `ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul`. -/
theorem centredSeminormNegNorm_le_vecHatNegENormOrderOne {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    centredSeminormNegNorm Q F ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((Q.scale : ℝ)) *
        ((originCubeMeanZeroH1CoerciveEstimate d 0).constant + 3)) *
      vecHatNegENormOrderOne Q F := by
  have hCd0 : 0 ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hspos : 0 < (3 : ℝ) ^ ((Q.scale : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) ((Q.scale : ℝ))
  have hKpos : 0 < (3 : ℝ) ^ ((Q.scale : ℝ)) *
      ((originCubeMeanZeroH1CoerciveEstimate d 0).constant + 3) :=
    mul_pos hspos (by linarith only [hCd0])
  refine centredSeminormNegNorm_le fun T => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (le_abs_self _)) ?_
  exact ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul hKpos hF
    (memLp_hilbertifyVecField_toField T)
    (fun eps heps => exists_smooth_test_of_centred_member (Q := Q) T heps)

/-! ## The scaled flux norm

`centredSeminormNegNorm_le_vecHatNegENormOrderOne` costs the per-cube comparison
constant `K_R = 3^{scale R}·(C_d + 3)`.  Carrying `K_R` on the flux side leaves
the seminorm carrier — and with it the constant-one Poincare step — untouched,
and the printed duality then holds *unconditionally*: the seminorm carrier
against the order-one hatted norm of the flux, at the price of the comparison. -/

/-! ## `_hPoincare` at the seminorm carrier, with constant one -/

/-- **The deterministic sub-cube Poincare average at the seminorm carrier, in
`L̲⁸` form.**  The constant-one `L̲³` tiling lemma composed with the monotonicity
`cubeLpENorm_mono_exponent`: no scale factor and no constant. -/
theorem centredSeminormAt_avsum_le_hessCubeEight {n m : ℕ}
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v) :
    ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)⁻¹) *
        ∑ R ∈ largeCubeSubcubes d n m, (ENNReal.ofReal (centredSeminormAt H R)) ^ (3 : ℕ) ≤
      (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))) ^ (3 : ℕ) := by
  refine le_trans (centredSeminormAt_avsum_le_hessCubeThree (d := d) H) ?_
  refine pow_le_pow_left' ?_ 3
  have hmeasOrig : AEStronglyMeasurable
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      (normalizedCubeMeasure (originCube d (m : ℤ))) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact ((memLp_hessMat_of_weakHessian (originCube d (m : ℤ)) H).smul_measure
      ENNReal.ofReal_ne_top).aestronglyMeasurable
  exact cubeLpENorm_mono_exponent (originCube d (m : ℤ)) (by norm_num) hmeasOrig

/-- **The third moment of the seminorm carrier is integrable as soon as the
carrier is in `L³(P)`.**  It supplies the `hintR` input of
`seminormCarrier_hPoincare` from the display's `_hMemOsc`. -/
theorem memLp_imp_seminormThirdInt {d : ℕ} [NeZero d] {n m : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (HD : (omega : ShellSeq d) →
      HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) (w omega).toH1Function)
    (h : ∀ R ∈ largeCubeSubcubes d n m,
      MemLp (fun omega : ShellSeq d => centredSeminormAt (HD omega) R)
        (ENNReal.ofReal (3 : ℝ)) P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d n m,
      Integrable (fun omega : ShellSeq d =>
        centredSeminormAt (HD omega) R ^ (3 : ℝ)) P.toMeasure := by
  intro R hR
  have h1 : Integrable (fun omega : ShellSeq d =>
      ‖centredSeminormAt (HD omega) R‖ ^ (3 : ℝ)) P.toMeasure := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3)] using
      (h R hR).integrable_norm_rpow
        (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))) ENNReal.ofReal_ne_top
  refine h1.congr (Filter.Eventually.of_forall fun omega => ?_)
  show ‖centredSeminormAt (HD omega) R‖ ^ (3 : ℝ) =
    centredSeminormAt (HD omega) R ^ (3 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (centredSeminormAt_nonneg (HD omega) R)]

/-- **`_hPoincare` of `_hOscBound`, discharged at the seminorm carrier with
constant one.**  This is that binder of `rhs_term3_B` at
`centredSeminormAt (HD omega) R` with `Cpo = 1`, free of `S`, `nu`, `P` and every
scale.  Its inputs are `hintR` (from the display's `_hMemOsc`, via
`memLp_imp_seminormThirdInt`) and `hfin` (from the `Γ₂` envelope of
`l_w_basic_regbounds_window`, via `integrable_abs_rpow_of_isBigO_gammaSigma_two`). -/
theorem seminormCarrier_hPoincare {d : ℕ} [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)}
    (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (HD : (omega : ShellSeq d) →
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function)
    (hintR : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        centredSeminormAt (HD omega) R ^ (3 : ℝ)) P.toMeasure)
    (hfin : (∫⁻ omega : ShellSeq d,
        (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ)
        ∂P.toMeasure) ≠ ⊤) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            centredSeminormAt (HD omega) R ^ (3 : ℝ) ∂P.toMeasure ≤
      (∫⁻ omega : ShellSeq d,
        (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ)
        ∂P.toMeasure).toReal := by
  have hnonneg : ∀ omega : ShellSeq d, 0 ≤ ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
      ∑ R ∈ largeCubeSubcubes d S.n S.m,
        centredSeminormAt (HD omega) R ^ (3 : ℝ) := by
    intro omega
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun R _ => ?_)
    exact Real.rpow_nonneg (centredSeminormAt_nonneg (HD omega) R) _
  have hpoint : ∀ omega : ShellSeq d, ENNReal.ofReal
        (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            centredSeminormAt (HD omega) R ^ (3 : ℝ)) ≤
      (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ) := by
    intro omega
    have ha := centredSeminormAt_avsum_le_hessCubeEight (d := d) (n := S.n) (m := S.m)
      (v := (w omega).toH1Function) (HD omega)
    have hper : ∀ R ∈ largeCubeSubcubes d S.n S.m,
        ENNReal.ofReal (centredSeminormAt (HD omega) R ^ (3 : ℝ)) =
          (ENNReal.ofReal (centredSeminormAt (HD omega) R)) ^ (3 : ℕ) := by
      intro R _
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        ENNReal.ofReal_pow (centredSeminormAt_nonneg (HD omega) R) 3]
    calc ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              centredSeminormAt (HD omega) R ^ (3 : ℝ))
        = ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              ENNReal.ofReal (centredSeminormAt (HD omega) R ^ (3 : ℝ)) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_sum_of_nonneg
              (fun R _ => Real.rpow_nonneg (centredSeminormAt_nonneg (HD omega) R) _)]
      _ = ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              (ENNReal.ofReal (centredSeminormAt (HD omega) R)) ^ (3 : ℕ) := by
          rw [Finset.sum_congr rfl fun R hR => hper R hR]
      _ ≤ (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ) := ha
  have hIntF : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          centredSeminormAt (HD omega) R ^ (3 : ℝ)) P.toMeasure :=
    (integrable_finsetSum _ fun R hR => hintR R hR).const_mul _
  have hsumint : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            centredSeminormAt (HD omega) R ^ (3 : ℝ) ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            centredSeminormAt (HD omega) R ^ (3 : ℝ) ∂P.toMeasure := by
    have h1 : ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            centredSeminormAt (HD omega) R ^ (3 : ℝ) ∂P.toMeasure =
        ∫ omega : ShellSeq d,
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            centredSeminormAt (HD omega) R ^ (3 : ℝ) ∂P.toMeasure :=
      (integral_finsetSum _ fun R hR => hintR R hR).symm
    rw [h1, ← integral_const_mul]
  have hLHS : ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            centredSeminormAt (HD omega) R ^ (3 : ℝ) ∂P.toMeasure =
      (∫⁻ omega : ShellSeq d, ENNReal.ofReal
        (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            centredSeminormAt (HD omega) R ^ (3 : ℝ)) ∂P.toMeasure).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hnonneg) hIntF.aestronglyMeasurable
  rw [hsumint, hLHS]
  exact ENNReal.toReal_mono hfin (lintegral_mono hpoint)

/-! ## The display at the seminorm carrier, with `_hCS` and `_hPoincare`
both discharged -/

end

end SuperdiffusionCLT.Section3.Terms
