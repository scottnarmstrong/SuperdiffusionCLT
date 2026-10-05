/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Steps
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsB

/-!
# The remaining bridge hypotheses of `l.RHS.term3`

The proof of `e.RHS.term3` carries the printed displays of its proof as
explicit hypotheses.  `RHSTerm3Inputs` supplies the
carriers and the one-sided input of the averaged quadratic tail; this module
supplies

* the `∇w` displays `e.nablaw.Lt` in the two forms the proof uses, from the
  conclusion of the first conjunct of `l.w.basic.regbounds`
  (`RegboundsB`) in its exact shape;
* the scale bookkeeping `hScaleId` and `hKlog` of
  `averaged_quadratic_tail`, from `e.scale.selection` and `e.h.restrictions`;
* the displays `hNablaW4` and `hDisp1` of `e.RHS.term3`.

## References

The statements used are `e.h.restrictions`, `e.scale.selection`, `e.scales.ordering`,
`l.w.basic.regbounds`, `sigma-star-carrier-swap` and `holder-split` of the paper.
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

noncomputable section

variable {d : ℕ}

/-! ## The scale bookkeeping of the averaged quadratic tail -/

/-- **`hScaleId` of `averaged_quadratic_tail`**: `n − (m − 2h) = h − 2a`, the
identity the paper states as
`n − (m − 2h) = h − 2⌈K log(ν⁻¹L)⌉`, with `a = ⌈K log(ν⁻¹L)⌉` the offset
of `e.scale.selection`.  It uses `m = n + h + 2a` (`e.scale.selection`), `2a < h`
(`e.scales.ordering`) and the pigeonhole side condition `2h ≤ m`, which is what
makes the natural-number subtraction `m − 2h` faithful. -/
theorem scaleId_sub_pigeonRange {S : ScaleSelection} (hS : ScalesOrdering S)
    (hm : 2 * S.h ≤ S.m) :
    (((S.n - (S.m - 2 * S.h) : ℕ)) : ℝ) = ((S.h : ℕ) : ℝ) - 2 * ((S.a : ℕ) : ℝ) := by
  have h1 := S.m_eq_n_add
  have h2 := hS.m_lt
  have hah : 2 * S.a < S.h := by omega
  have h3 : S.n - (S.m - 2 * S.h) = S.h - 2 * S.a := by omega
  have hle : 2 * S.a ≤ S.h := le_of_lt hah
  rw [h3, Nat.cast_sub hle]
  push_cast
  ring

/-! ## `e.nablaw.Lt`: the second and fourth moments of the response gradient -/

/-- **`E[‖∇w‖^k_{L̲^r(cu_m)}]`**, the two moments `WL2` and `WL4` of
`l.RHS.term3#holder-split`: the `k`-th moment of the normalized
`L̲^r` norm of the response gradient on the pigeonhole cube. -/
def gradResponseMoment {m : ℕ} (r : ℝ≥0∞) (k : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))) : ℝ :=
  (∫⁻ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (m : ℤ)) r (w omega).toH1Function.grad) ^ k
    ∂P.toMeasure).toReal

theorem gradResponseMoment_nonneg {m : ℕ} (r : ℝ≥0∞) (k : ℕ)
    (P : ProbabilityMeasure (ShellSeq d))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))) :
    0 ≤ gradResponseMoment r k P w :=
  ENNReal.toReal_nonneg

/-- The constant of the fourth-moment form of `e.nablaw.Lt`: the fourth power
of the constant of `l.w.basic.regbounds` times the fourth Orlicz moment factor
`1 + Γ(3)` of `l.moments.gamma.psi`. -/
def nablaW4Const (C : ℝ) : ℝ := C ^ (4 : ℕ) * (1 + Real.Gamma 3)

theorem one_le_nablaW4Const {C : ℝ} (hC : 1 ≤ C) : 1 ≤ nablaW4Const C := by
  have hG : (0 : ℝ) < Real.Gamma 3 := Real.Gamma_pos_of_pos (by norm_num)
  have hC4 : (1 : ℝ) ≤ C ^ (4 : ℕ) := one_le_pow₀ hC
  rw [nablaW4Const]
  have h1 : (1 : ℝ) * (1 + Real.Gamma 3) ≤ C ^ (4 : ℕ) * (1 + Real.Gamma 3) :=
    mul_le_mul_of_nonneg_right hC4 (by linarith only [hG])
  linarith only [h1, hG]

/-- **`E[‖∇w‖⁴_{L̲⁴(cu_m)}] ≤ C h²|p|⁴`**, the fourth-moment form of
`e.nablaw.Lt` used in the proof of `e.RHS.term3`.

`hZmeas`, `hZbigO`, `hZbound` are the first conjunct of
`l.w.basic.regbounds` (`e.nablaw.Lt`) in its exact shape, i.e.
its conclusion at the constant `C`: an
`L̲^8(cu_m)` bound on the response gradient by a `Γ₂` envelope of amplitude
`C|p|h^{1/2}`.  The derivation is the one of the second-moment display of Step 1
(`gradW_l2_second_moment_bound`): the exponent downgrade
`‖·‖_{L̲⁴} ≤ ‖·‖_{L̲⁸}` on the probability measure of the cube, followed by the
fourth-moment bound of `l.moments.gamma.psi`. -/
theorem gradW_l4_fourth_moment_of_regbounds
    (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega)) :
    gradResponseMoment (m := S.m) 4 4 P w ≤
      nablaW4Const C * ((S.h : ℝ) ^ (2 : ℕ) * vecNormSq p ^ (2 : ℕ)) := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hh1 : 1 ≤ S.h := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := S.ellPrime_add_h
    omega
  have hhR : (0 : ℝ) < (S.h : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hh1
  have hpn : (0 : ℝ) < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hhalf : (0 : ℝ) < (S.h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hhR _
  have hA : (0 : ℝ) < C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_pos hC0 (mul_pos (Real.sqrt_pos.2 hpn) hhalf)
  have hptr : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) := by
    intro omega
    have hdown : vecCubeLpENorm (originCube d (S.m : ℤ)) 4
        (w omega).toH1Function.grad ≤
        vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad :=
      vecCubeLpENorm_mono_exponent (originCube d (S.m : ℤ)) (by norm_num)
        (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
          (w omega).toH1Function.grad_memVectorL2)
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (4 : ℕ) :=
          pow_le_pow_left' (le_trans (le_trans hdown (hZbound omega)) habs) 4
      _ = ENNReal.ofReal (|Z omega| ^ (4 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 4).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) := by
          rw [Real.rpow_natCast]
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((4 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZmeas.aemeasurable hZbigO 4
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hA hZmeas.aemeasurable hZbigO 4
  have hAsq : (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ^ (((4 : ℕ) : ℝ)) *
      (1 + Real.Gamma (((4 : ℕ) : ℝ) / 2 + 1)) =
      nablaW4Const C * ((S.h : ℝ) ^ (2 : ℕ) * vecNormSq p ^ (2 : ℕ)) := by
    have hsq : Real.sqrt (vecNormSq p) ^ (4 : ℕ) = vecNormSq p ^ (2 : ℕ) := by
      have h2 : Real.sqrt (vecNormSq p) ^ (2 : ℕ) = vecNormSq p :=
        Real.sq_sqrt (le_of_lt hpn)
      calc Real.sqrt (vecNormSq p) ^ (4 : ℕ)
          = (Real.sqrt (vecNormSq p) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
        _ = vecNormSq p ^ (2 : ℕ) := by rw [h2]
    have hhsq : ((S.h : ℝ) ^ ((1 : ℝ) / 2)) ^ (4 : ℕ) = (S.h : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((S.h : ℝ) ^ ((1 : ℝ) / 2)) 4,
        ← Real.rpow_mul (le_of_lt hhR)]
      rw [show ((1 : ℝ) / 2 * ((4 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [Real.rpow_natCast, show (((4 : ℕ) : ℝ)) / 2 + 1 = 3 by norm_num,
      mul_pow, mul_pow, hsq, hhsq, nablaW4Const]
    ring
  have hlint : (∫⁻ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
        (w omega).toH1Function.grad) ^ (4 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (nablaW4Const C *
        ((S.h : ℝ) ^ (2 : ℕ) * vecNormSq p ^ (2 : ℕ))) := by
    calc (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
          (w omega).toH1Function.grad) ^ (4 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            ENNReal.ofReal (|Z omega| ^ (((4 : ℕ) : ℝ))) ∂P.toMeasure :=
          lintegral_mono hptr
      _ = ENNReal.ofReal (∫ omega : ShellSeq d, |Z omega| ^ (((4 : ℕ) : ℝ)) ∂P.toMeasure) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (nablaW4Const C *
            ((S.h : ℝ) ^ (2 : ℕ) * vecNormSq p ^ (2 : ℕ))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← hAsq]
          exact hmom
  exact ENNReal.toReal_le_of_le_ofReal
    (by have := one_le_nablaW4Const hC; positivity) hlint

/-- The constant of the second-moment form of `e.nablaw.Lt`. -/
def nablaW2Const (C : ℝ) : ℝ := C ^ (2 : ℕ) * (1 + Real.Gamma 2)

theorem one_le_nablaW2Const {C : ℝ} (hC : 1 ≤ C) : 1 ≤ nablaW2Const C := by
  have hG : (0 : ℝ) < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
  have hC2 : (1 : ℝ) ≤ C ^ (2 : ℕ) := one_le_pow₀ hC
  rw [nablaW2Const]
  have h1 : (1 : ℝ) * (1 + Real.Gamma 2) ≤ C ^ (2 : ℕ) * (1 + Real.Gamma 2) :=
    mul_le_mul_of_nonneg_right hC2 (by linarith only [hG])
  linarith only [h1, hG]

/-- **`E[‖∇w‖²_{L̲²(cu_m)}] ≤ C h|p|²`**, the second-moment form of
`e.nablaw.Lt` used in the proof of `e.RHS.term3`, with the constant written explicitly.  Same
hypotheses and same derivation as `gradW_l4_fourth_moment_of_regbounds`. -/
theorem gradW_l2_second_moment_bound
    (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega)) :
    gradResponseMoment (m := S.m) 2 2 P w ≤ nablaW2Const C * ((S.h : ℝ) * vecNormSq p) := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hh1 : 1 ≤ S.h := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := S.ellPrime_add_h
    omega
  have hhR : (0 : ℝ) < (S.h : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hh1
  have hpn : (0 : ℝ) < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hhalf : (0 : ℝ) < (S.h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hhR _
  have hA : (0 : ℝ) < C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_pos hC0 (mul_pos (Real.sqrt_pos.2 hpn) hhalf)
  have hptr : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
    intro omega
    have hdown : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (w omega).toH1Function.grad ≤
        vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad :=
      vecCubeLpENorm_mono_exponent (originCube d (S.m : ℤ)) (by norm_num)
        (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
          (w omega).toH1Function.grad_memVectorL2)
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (2 : ℕ) :=
          pow_le_pow_left' (le_trans (le_trans hdown (hZbound omega)) habs) 2
      _ = ENNReal.ofReal (|Z omega| ^ (2 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
          rw [Real.rpow_natCast]
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((2 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZmeas.aemeasurable hZbigO 2
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hA hZmeas.aemeasurable hZbigO 2
  have hAsq : (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ^ (((2 : ℕ) : ℝ)) *
      (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1)) =
      nablaW2Const C * ((S.h : ℝ) * vecNormSq p) := by
    have hsq : Real.sqrt (vecNormSq p) ^ (2 : ℕ) = vecNormSq p :=
      Real.sq_sqrt (le_of_lt hpn)
    have hhsq : ((S.h : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (S.h : ℝ) := by
      rw [← Real.rpow_natCast ((S.h : ℝ) ^ ((1 : ℝ) / 2)) 2,
        ← Real.rpow_mul (le_of_lt hhR)]
      norm_num
    rw [Real.rpow_natCast, show (((2 : ℕ) : ℝ)) / 2 + 1 = 2 by norm_num,
      mul_pow, mul_pow, hsq, hhsq, nablaW2Const]
    ring
  have hlint : (∫⁻ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (nablaW2Const C * ((S.h : ℝ) * vecNormSq p)) := by
    calc (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) ∂P.toMeasure :=
          lintegral_mono hptr
      _ = ENNReal.ofReal (∫ omega : ShellSeq d, |Z omega| ^ (((2 : ℕ) : ℝ)) ∂P.toMeasure) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (nablaW2Const C * ((S.h : ℝ) * vecNormSq p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← hAsq]
          exact hmom
  exact ENNReal.toReal_le_of_le_ofReal
    (by have := one_le_nablaW2Const hC; positivity) hlint

/-- The constant of `hNablaW4`: the square root of the fourth-moment
constant. -/
def nablaW4SqrtConst (C : ℝ) : ℝ := Real.sqrt (nablaW4Const C)

theorem nablaW4SqrtConst_nonneg (C : ℝ) : 0 ≤ nablaW4SqrtConst C := Real.sqrt_nonneg _

/-- The window is at most the printed envelope `L' − ℓ = h + 3a`. -/
theorem window_le_LPrime_sub_ell (S : ScaleSelection) :
    ((S.h : ℕ) : ℝ) ≤ ((S.LPrime - S.ell : ℕ) : ℝ) := by
  have h := S.LPrime_sub_ell
  have : S.h ≤ S.LPrime - S.ell := by omega
  exact_mod_cast this

/-- **`hNablaW4` of `e.RHS.term3`**:
`E[‖∇w‖⁴_{L̲⁴(cu_m)}]^{1/2} ≤ C h|p|² ≤ C(L'−ℓ)|p|²`.  The hypotheses are
the first conjunct of `l.w.basic.regbounds` in its exact shape; the passage from
`h` to `L'−ℓ` is the printed `h ≤ L'−ℓ`. -/
theorem nablaW4_of_regbounds
    (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega)) :
    gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) ≤
      nablaW4SqrtConst C * ((S.LPrime - S.ell : ℕ) : ℝ) * vecNormSq p := by
  have hmom := gradW_l4_fourth_moment_of_regbounds d nu hnu P hPrefix hJ2 hJ3 hJ4 S
    hSorder e he p hp w hC hZmeas hZbigO hZbound
  have hK0 : (0 : ℝ) ≤ nablaW4Const C := le_trans zero_le_one (one_le_nablaW4Const hC)
  have hq0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hh0 : (0 : ℝ) ≤ ((S.h : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrw : gradResponseMoment (m := S.m) 4 4 P w ^ ((1 : ℝ) / 2) =
      Real.sqrt (gradResponseMoment (m := S.m) 4 4 P w) :=
    (Real.sqrt_eq_rpow _).symm
  have hsq : nablaW4Const C * (((S.h : ℕ) : ℝ) ^ (2 : ℕ) * vecNormSq p ^ (2 : ℕ)) =
      (nablaW4SqrtConst C * (((S.h : ℕ) : ℝ) * vecNormSq p)) ^ (2 : ℕ) := by
    rw [nablaW4SqrtConst, mul_pow, Real.sq_sqrt hK0, mul_pow]
  have hstep : Real.sqrt (gradResponseMoment (m := S.m) 4 4 P w) ≤
      nablaW4SqrtConst C * (((S.h : ℕ) : ℝ) * vecNormSq p) := by
    refine le_trans (Real.sqrt_le_sqrt hmom) ?_
    rw [hsq, Real.sqrt_sq
      (mul_nonneg (nablaW4SqrtConst_nonneg C) (mul_nonneg hh0 hq0))]
  rw [hrw]
  refine le_trans hstep ?_
  have hle : ((S.h : ℕ) : ℝ) * vecNormSq p ≤
      ((S.LPrime - S.ell : ℕ) : ℝ) * vecNormSq p :=
    mul_le_mul_of_nonneg_right (window_le_LPrime_sub_ell S) hq0
  calc nablaW4SqrtConst C * (((S.h : ℕ) : ℝ) * vecNormSq p)
      ≤ nablaW4SqrtConst C * (((S.LPrime - S.ell : ℕ) : ℝ) * vecNormSq p) :=
        mul_le_mul_of_nonneg_left hle (nablaW4SqrtConst_nonneg C)
    _ = nablaW4SqrtConst C * ((S.LPrime - S.ell : ℕ) : ℝ) * vecNormSq p := by ring

/-- **`hDisp1` of `e.bL.to.bhomell` and `e.RHS.term3`**:
*"`e.nablaw.Lt` gives the sharper
factor `h|p|²`, and since `h ≤ L' − ℓ`,
`shom_ℓ(cu_n)E[‖∇w‖²_{L̲²(cu_m)}] ≤ C shom_ℓ(cu_n)(L'−ℓ)shom_{L',*}^{-1}(cu_n)`"*.
The identity `|p|² = shom_{L',*}^{-1}(cu_n)` is
`vecNormSq_testVector`. -/
theorem disp1_of_regbounds
    (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    {C0 C : ℝ} (hC0 : 0 ≤ C0) (hC : 1 ≤ C)
    {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZbound : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega)) :
    C0 * ((d : ℝ) * sigmaBarSeq nu S.ell P S.n) *
        gradResponseMoment (m := S.m) 2 2 P w ≤
      C0 * (d : ℝ) * nablaW2Const C * (sigmaBarSeq nu S.ell P S.n *
        (((S.LPrime - S.ell : ℕ) : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n)) := by
  have hmom := gradW_l2_second_moment_bound d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e he
    p hp w hC hZmeas hZbigO hZbound
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]
    exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  rw [hpsq] at hmom
  set sb : ℝ := sigmaBarSeq nu S.ell P S.n with hsbdef
  set sg : ℝ := sigmaBarStarInvSeq nu S.LPrime P S.n with hsgdef
  have hsb0 : (0 : ℝ) ≤ sb :=
    le_of_lt (sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n)
  have hsg0 : (0 : ℝ) ≤ sg :=
    le_of_lt (sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n)
  have hK0 : (0 : ℝ) ≤ nablaW2Const C := le_trans zero_le_one (one_le_nablaW2Const hC)
  have hcoef : (0 : ℝ) ≤ C0 * ((d : ℝ) * sb) := by positivity
  have hcoef2 : (0 : ℝ) ≤ C0 * (d : ℝ) * nablaW2Const C := by positivity
  have hstep1 : C0 * ((d : ℝ) * sb) * gradResponseMoment (m := S.m) 2 2 P w ≤
      C0 * ((d : ℝ) * sb) * (nablaW2Const C * (((S.h : ℕ) : ℝ) * sg)) :=
    mul_le_mul_of_nonneg_left hmom hcoef
  have hstep2 : sb * (((S.h : ℕ) : ℝ) * sg) ≤
      sb * (((S.LPrime - S.ell : ℕ) : ℝ) * sg) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (window_le_LPrime_sub_ell S) hsg0) hsb0
  have hstep3 : C0 * (d : ℝ) * nablaW2Const C * (sb * (((S.h : ℕ) : ℝ) * sg)) ≤
      C0 * (d : ℝ) * nablaW2Const C * (sb * (((S.LPrime - S.ell : ℕ) : ℝ) * sg)) :=
    mul_le_mul_of_nonneg_left hstep2 hcoef2
  have hring : C0 * ((d : ℝ) * sb) * (nablaW2Const C * (((S.h : ℕ) : ℝ) * sg)) =
      C0 * (d : ℝ) * nablaW2Const C * (sb * (((S.h : ℕ) : ℝ) * sg)) := by ring
  linarith only [hstep1, hstep3, hring]

end

end SuperdiffusionCLT.Section3.Terms
