/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1LocalizationB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoOrderOne
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Constant-first pieces of `l.RHS.term1`

Every display of the term-1 chain is stated as `∃ C : ℝ, 1 ≤ C ∧ …` **after**
the section data, so none of them can be transported into a statement whose
constant comes first.  This module and its companion `RHSTerm1AnchorsConstFirstB`
restate the chain with every constant named, and prove `e.RHS.term1` with the
constant quantified first and with every input the chain discharges discharged.

Here: the `Γ₂` second-moment passage, the three displays of Step 1 and the
closing Cauchy-Schwarz of Step 1, the `H̲¹` display of Step 2, and the two
arithmetic passages the companion module uses.
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

noncomputable section

/-! ## The second moment of a `Γ₂` envelope -/

/-- **`l.moments.gamma.psi` at `k = 2`, in `ℝ≥0∞`**: an `ℝ≥0∞` quantity
dominated by a `Γ₂` envelope of amplitude `A` has second moment at most
`A²(1 + Γ(2))`.  The constant is explicit. -/
theorem lintegral_sq_le_of_gammaTwo_envelope {d : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} {X : ShellSeq d → ℝ≥0∞}
    {Z : ShellSeq d → ℝ} {A : ℝ} (hA : 0 < A) (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z A)
    (hX : ∀ omega : ShellSeq d, X omega ≤ ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d, (X omega) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (A ^ (2 : ℕ) * (1 + Real.Gamma 2)) := by
  have hptr : ∀ omega : ShellSeq d,
      (X omega) ^ (2 : ℕ) ≤ ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
    intro omega
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (X omega) ^ (2 : ℕ) ≤ (ENNReal.ofReal |Z omega|) ^ (2 : ℕ) :=
          pow_le_pow_left' (le_trans (hX omega) habs) 2
      _ = ENNReal.ofReal (|Z omega| ^ (2 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by rw [Real.rpow_natCast]
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((2 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZmeas.aemeasurable hZbigO 2
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hA hZmeas.aemeasurable hZbigO 2
  have hval : A ^ (((2 : ℕ) : ℝ)) * (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1)) =
      A ^ (2 : ℕ) * (1 + Real.Gamma 2) := by
    rw [Real.rpow_natCast, show (((2 : ℕ) : ℝ)) / 2 + 1 = 2 by norm_num]
  calc (∫⁻ omega : ShellSeq d, (X omega) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞)
      ≤ ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) ∂P.toMeasure :=
        lintegral_mono hptr
    _ = ENNReal.ofReal (∫ omega : ShellSeq d,
          |Z omega| ^ (((2 : ℕ) : ℝ)) ∂P.toMeasure) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun omega =>
            Real.rpow_nonneg (abs_nonneg _) _)).symm
    _ ≤ ENNReal.ofReal (A ^ (((2 : ℕ) : ℝ)) *
          (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1))) := ENNReal.ofReal_le_ofReal hmom
    _ = ENNReal.ofReal (A ^ (2 : ℕ) * (1 + Real.Gamma 2)) := by rw [hval]

/-! ## The first display of Step 1, at a named constant -/

/-- `1 ≤ ℓ` and `n ≤ ℓ`, from `e.scales.ordering` alone. -/
private theorem ellFactsCF (S : ScaleSelection) (hSorder : ScalesOrdering S) :
    1 ≤ S.ell ∧ S.n ≤ S.ell :=
  ⟨lt_of_le_of_lt (Nat.zero_le _) hSorder.n_lt_ell, le_of_lt hSorder.n_lt_ell⟩

/-- `3^n (3^ℓ)⁻¹ = 3^{-(ℓ-n)}` for `n ≤ ℓ`. -/
private theorem threePowCancelCF {n l : ℕ} (hnl : n ≤ l) :
    (3 : ℝ) ^ ((n : ℝ)) * ((3 : ℝ) ^ l)⁻¹ = (3 : ℝ) ^ (-(((l - n : ℕ) : ℝ))) := by
  have hpow : ((3 : ℝ) ^ l)⁻¹ = (3 : ℝ) ^ (-((l : ℝ))) := by
    rw [← Real.rpow_natCast (3 : ℝ) l, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), Nat.cast_sub hnl]
  ring_nf

/-- The constant of the first display of Step 1: the constant of
the localized flux second-moment estimate, written out. -/
def fluxL2ConstFirst (d : ℕ) (Cloc : ℝ) : ℝ :=
  fluxL2HighMomentConst Cloc (coeffCubeLinftyMomentConst d)
    (shellDerivHighBridgeConst d)

theorem one_le_fluxL2ConstFirst (d : ℕ) (Cloc : ℝ) :
    1 ≤ fluxL2ConstFirst d Cloc :=
  one_le_fluxL2HighMomentConst _ _ _

/-- **The first display of Step 1 at a named constant**:
`E[‖a_ℓ(∇u_n − ∇ũ_n)‖²_{L̲²(cu_r)}] ≤ C ν^{-3} ℓ² 3^{-(ℓ-n)} shom_{L',*}(cu_n)`.
This is the localized flux second-moment estimate with its
existential constant replaced by the witness `fluxL2ConstFirst d Cloc`. -/
theorem flux_l2_second_moment_explicit {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (uNGlued uTildeGlued : ShellSeq d → Vec d → Vec d) (r : ℕ)
    (Cloc : ℝ) (hCloc : 1 ≤ Cloc)
    (hLocalized : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x - uTildeGlued omega x))) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e)) *
        ((∫⁻ omega : ShellSeq d,
            (coeffCubeLinftyENorm nu S.ell S.ell omega) ^ (4 : ℕ)
          ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2)) *
        ((∫⁻ omega : ShellSeq d,
            (shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega) ^ (2 : ℕ)
          ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))) :
    (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x - uTildeGlued omega x))) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (fluxL2ConstFirst d Cloc *
        (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)) := by
  obtain ⟨hl1, hnl⟩ := ellFactsCF S hSorder
  set Ca : ℝ := coeffCubeLinftyMomentConst d with hCa
  set Chigh : ℝ := shellDerivHighBridgeConst d with hChigh
  have hCa1 : (1 : ℝ) ≤ Ca := one_le_coeffCubeLinftyMomentConst hPrefix
  have hCh1 : (1 : ℝ) ≤ Chigh := one_le_shellDerivHighBridgeConst d
  have hCa0 : (0 : ℝ) ≤ Ca := le_trans (by norm_num) hCa1
  have hCh0 : (0 : ℝ) ≤ Chigh := le_trans (by norm_num) hCh1
  have hCloc0 : (0 : ℝ) ≤ Cloc := le_trans (by norm_num) hCloc
  have hsig0 : (0 : ℝ) ≤ vecNormSq (fluxSlot nu S.LPrime P S.n e) := vecNormSq_nonneg _
  have hnu3 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have h3n : (0 : ℝ) ≤ (3 : ℝ) ^ ((S.n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hMoment : (∫⁻ omega : ShellSeq d,
      (coeffCubeLinftyENorm nu S.ell S.ell omega) ^ (4 : ℕ)
    ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (Ca * (1 + (S.ell : ℝ)) ^ (2 : ℕ)) := by
    refine le_trans (sqrt_fourth_moment_coeffCubeLinftyENorm_le hPrefix hJ2 hJ3 hJ4
      (le_of_lt hnu) hnu1 (le_refl S.ell)) (le_of_eq ?_)
    rw [hCa]
    congr 1
    ring
  have hDerivHigh := deriv_high_bridge (d := d) hPrefix hJ3 S hSorder
  refine le_trans hLocalized ?_
  have hstep := mul_le_mul' (mul_le_mul' (le_refl
      (ENNReal.ofReal (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)))) hMoment) hDerivHigh
  refine le_trans hstep ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcancel := threePowCancelCF hnl
  have hkey : (Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)) *
      (Ca * (1 + (S.ell : ℝ)) ^ (2 : ℕ)) * (Chigh * ((3 : ℝ) ^ S.ell)⁻¹) =
      (Cloc * Ca * Chigh) * nu ^ (-(3 : ℝ)) * ((1 + (S.ell : ℝ)) ^ (2 : ℕ)) *
        ((3 : ℝ) ^ ((S.n : ℝ)) * ((3 : ℝ) ^ S.ell)⁻¹) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e) := by ring
  rw [hkey, hcancel]
  have hlR : (1 : ℝ) ≤ (S.ell : ℝ) := by exact_mod_cast hl1
  have hsquare : (1 + (S.ell : ℝ)) ^ (2 : ℕ) ≤ 4 * (S.ell : ℝ) ^ (2 : ℕ) := by
    have hsum : 1 + (S.ell : ℝ) ≤ 2 * (S.ell : ℝ) := by linarith only [hlR]
    have hnn : (0 : ℝ) ≤ 1 + (S.ell : ℝ) := by linarith only [hlR]
    calc (1 + (S.ell : ℝ)) ^ (2 : ℕ) ≤ (2 * (S.ell : ℝ)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hnn hsum 2
      _ = 4 * (S.ell : ℝ) ^ (2 : ℕ) := by ring
  have hbase : (0 : ℝ) ≤ (Cloc * Ca * Chigh) * nu ^ (-(3 : ℝ)) := by positivity
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hmono : (Cloc * Ca * Chigh) * nu ^ (-(3 : ℝ)) * ((1 + (S.ell : ℝ)) ^ (2 : ℕ)) ≤
      (Cloc * Ca * Chigh) * nu ^ (-(3 : ℝ)) * (4 * (S.ell : ℝ) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hsquare hbase
  have hle : (Cloc * Ca * Chigh) * 4 ≤ fluxL2ConstFirst d Cloc := le_max_right _ _
  have hrest : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
      (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by positivity
  have hfin := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hle hrest) hsig0
  calc (Cloc * Ca * Chigh) * nu ^ (-(3 : ℝ)) * ((1 + (S.ell : ℝ)) ^ (2 : ℕ)) *
        ((3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)
      ≤ (Cloc * Ca * Chigh) * nu ^ (-(3 : ℝ)) * (4 * (S.ell : ℝ) ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono h3d) hsig0
    _ = (Cloc * Ca * Chigh) * 4 * (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e) := by ring
    _ ≤ fluxL2ConstFirst d Cloc *
          (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
            (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e) := hfin

/-! ## The third display of Step 1, at a named constant -/

/-- **The constant of the third display of Step 1**: the printed second-moment
constant `1 + γ(2) = 1 + Γ(2)` of `l.moments.gamma.psi` times the square of the
amplitude constant of `e.nablaw.Lt`. -/
def gradWL2ConstFirst (C : ℝ) : ℝ := max 1 (C ^ (2 : ℕ) * (1 + Real.Gamma 2))

theorem one_le_gradWL2ConstFirst (C : ℝ) : 1 ≤ gradWL2ConstFirst C :=
  le_max_left _ _

/-- **The third display of Step 1 at a named constant**:
`E[‖∇w‖²_{L̲²(cu_m)}] ≤ C h |p|²`.  `hRegL8` is the first clause of
`e.nablaw.Lt` at the constant `C`, whose own constant is quantified before the
data in `l_w_basic_regbounds_window`. -/
theorem gradW_l2_second_moment_explicit {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (C : ℝ) (hC : 1 ≤ C)
    (hRegL8 : ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ∧
      ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
          ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (gradWL2ConstFirst C * (S.h : ℝ) * vecNormSq p) := by
  obtain ⟨Z, hZmeas, hZbigO, hZbound⟩ := hRegL8
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hh1 : 1 ≤ S.h := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := S.ellPrime_add_h
    omega
  have hhR : (0 : ℝ) < (S.h : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hh1
  have hpn : (0 : ℝ) < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hhalf : (0 : ℝ) < (S.h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hhR _
  have hA : (0 : ℝ) < C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_pos hC0 (mul_pos (Real.sqrt_pos.2 hpn) hhalf)
  have hdown : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega) := by
    intro omega
    refine le_trans ?_ (hZbound omega)
    exact vecCubeLpENorm_mono_exponent (originCube d (S.m : ℤ)) (by norm_num)
      (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
        (w omega).toH1Function.grad_memVectorL2)
  refine le_trans (lintegral_sq_le_of_gammaTwo_envelope hA hZmeas hZbigO hdown)
    (ENNReal.ofReal_le_ofReal ?_)
  have hval : (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ^ (2 : ℕ) *
      (1 + Real.Gamma 2) =
      (C ^ (2 : ℕ) * (1 + Real.Gamma 2)) * (S.h : ℝ) * vecNormSq p := by
    have hsq : Real.sqrt (vecNormSq p) ^ (2 : ℕ) = vecNormSq p :=
      Real.sq_sqrt (le_of_lt hpn)
    have hhsq : ((S.h : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (S.h : ℝ) := by
      rw [← Real.rpow_natCast ((S.h : ℝ) ^ ((1 : ℝ) / 2)) 2,
        ← Real.rpow_mul (le_of_lt hhR)]
      norm_num
    rw [mul_pow, mul_pow, hsq, hhsq]
    ring
  rw [hval]
  have hrest : (0 : ℝ) ≤ (S.h : ℝ) * vecNormSq p := by positivity
  have hle : C ^ (2 : ℕ) * (1 + Real.Gamma 2) ≤ gradWL2ConstFirst C := le_max_right _ _
  have := mul_le_mul_of_nonneg_right hle hrest
  calc C ^ (2 : ℕ) * (1 + Real.Gamma 2) * (S.h : ℝ) * vecNormSq p
      = C ^ (2 : ℕ) * (1 + Real.Gamma 2) * ((S.h : ℝ) * vecNormSq p) := by ring
    _ ≤ gradWL2ConstFirst C * ((S.h : ℝ) * vecNormSq p) := this
    _ = gradWL2ConstFirst C * (S.h : ℝ) * vecNormSq p := by ring

/-! ## Three elementary passages -/

private theorem addSqLeCF (x y : ℝ≥0∞) :
    (x + y) ^ (2 : ℕ) ≤ 4 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
  have h1 : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · calc x + y ≤ y + y := add_le_add h le_rfl
        _ = 2 * max x y := by rw [max_eq_right h]; ring
    · calc x + y ≤ x + x := add_le_add le_rfl h
        _ = 2 * max x y := by rw [max_eq_left h]; ring
  have h2 : (max x y) ^ (2 : ℕ) ≤ x ^ (2 : ℕ) + y ^ (2 : ℕ) := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc (x + y) ^ (2 : ℕ) ≤ (2 * max x y) ^ (2 : ℕ) := pow_le_pow_left' h1 2
    _ = 4 * (max x y) ^ (2 : ℕ) := by ring
    _ ≤ 4 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) := mul_le_mul' le_rfl h2

/-- The square root of an `ENNReal.ofReal` bound. -/
theorem rpowHalfOfRealCF {x : ℝ≥0∞} {u : ℝ} (hu : 0 ≤ u)
    (h : x ≤ ENNReal.ofReal u) :
    x ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (Real.sqrt u) := by
  calc x ^ ((1 : ℝ) / 2) ≤ (ENNReal.ofReal u) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt u) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg hu (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]

/-- `√(ν^{-s}) = ν^{-s/2}`. -/
theorem sqrtRpowNegCF {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Real.sqrt (nu ^ (-s)) = nu ^ (-(s / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hnu)]
  ring_nf

/-- The closing arithmetic of Step 1, after the cancellation `|p|² σ = 1`. -/
private theorem step1ArithCF {nu : ℝ} (hnu : 0 < nu) (C3 C0 hh l t pn sig : ℝ)
    (hC3 : 1 ≤ C3) (hC0 : 1 ≤ C0) (hh0 : 0 ≤ hh) (hl0 : 0 ≤ l)
    (hpn0 : 0 ≤ pn) (hps : pn * sig = 1) :
    Real.sqrt (C3 * hh * pn) *
        Real.sqrt (8 * (C0 * (nu ^ (-(3 : ℝ)) * l ^ (2 : ℕ) * (3 : ℝ) ^ (-t)) * sig)) =
      Real.sqrt (8 * (C3 * C0)) * nu ^ (-((3 : ℝ) / 2)) *
        (l * hh ^ ((1 : ℝ) / 2)) * (3 : ℝ) ^ (-(t / 2)) := by
  have hnu3 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have h3t : (0 : ℝ) ≤ (3 : ℝ) ^ (-t) := Real.rpow_nonneg (by norm_num) _
  have hC30 : (0 : ℝ) ≤ C3 := le_trans (by norm_num) hC3
  have hC00 : (0 : ℝ) ≤ C0 := le_trans (by norm_num) hC0
  have hfirst : (0 : ℝ) ≤ C3 * hh * pn := by positivity
  rw [← Real.sqrt_mul hfirst]
  have hcollect : (C3 * hh * pn) *
      (8 * (C0 * (nu ^ (-(3 : ℝ)) * l ^ (2 : ℕ) * (3 : ℝ) ^ (-t)) * sig)) =
      (8 * (C3 * C0)) * hh * (nu ^ (-(3 : ℝ))) * (l ^ (2 : ℕ)) * ((3 : ℝ) ^ (-t)) *
        (pn * sig) := by ring
  rw [hcollect, hps, mul_one, Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), sqrtRpowNegCF hnu 3, Real.sqrt_sq hl0,
    Real.sqrt_eq_rpow hh]
  have h3 : Real.sqrt ((3 : ℝ) ^ (-t)) = (3 : ℝ) ^ (-(t / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  rw [h3]
  ring

/-! ## Step 1 at a named constant -/

/-- **`e.decompose.flux.u.n.first` at named constants**:
`E[‖∇w‖_{L̲²}(‖a_ℓ(∇u_n − ∇ũ_n)‖_{L̲²} + |q̃ − q|)] ≤ √(8C3C0) ν^{-3/2} ℓ h^{1/2}
3^{-(ℓ-n)/2}`. -/
theorem decompose_flux_first_explicit {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uNGlued uTildeGlued : ShellSeq d → Vec d → Vec d) (q qTilde : Vec d)
    (hMeasGradW : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad)
      P.toMeasure)
    (hMeasFlux : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uNGlued omega x - uTildeGlued omega x))) P.toMeasure)
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hFluxL2Sq : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x - uTildeGlued omega x))) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (C0 * (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)))
    (hqSq : vecNormSq (qTilde - q) ≤
      C0 * (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hGradWL2Sq : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (C3 * (S.h : ℝ) * vecNormSq p)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad *
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => matVecMul
                ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uNGlued omega x - uTildeGlued omega x)) +
            ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q))))
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.sqrt (8 * (C3 * C0)) * nu ^ (-((3 : ℝ) / 2)) *
        ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))) := by
  set T : ℝ := nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
    (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) with hT
  set sig : ℝ := vecNormSq (fluxSlot nu S.LPrime P S.n e) with hsig
  set A : ShellSeq d → ℝ≥0∞ := fun omega =>
    vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad with hA
  set B : ShellSeq d → ℝ≥0∞ := fun omega =>
    vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
        (uNGlued omega x - uTildeGlued omega x)) with hB
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q))) with hc
  have hT0 : (0 : ℝ) ≤ T := by
    rw [hT]
    have h1 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  have hsig0 : (0 : ℝ) ≤ sig := vecNormSq_nonneg _
  have hpn0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg _
  have hC00 : (0 : ℝ) ≤ C0 := le_trans (by norm_num) hC0
  have hC30 : (0 : ℝ) ≤ C3 := le_trans (by norm_num) hC3
  have hps : vecNormSq p * sig = 1 := by
    have hpos := sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
    rw [hp, hsig, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he,
      vecNormSq_fluxSlot hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact mul_inv_cancel₀ hpos.ne'
  have hcsq : c ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq (qTilde - q)) := by
    rw [hc, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (vecNormSq_nonneg _)]
  have hgroup : (∫⁻ omega : ShellSeq d, (B omega + c) ^ (2 : ℕ) ∂P.toMeasure) ≤
      ENNReal.ofReal (8 * (C0 * T * sig)) := by
    have hstep : (∫⁻ omega : ShellSeq d, (B omega + c) ^ (2 : ℕ) ∂P.toMeasure) ≤
        ∫⁻ omega : ShellSeq d, 4 * (B omega ^ (2 : ℕ) + c ^ (2 : ℕ)) ∂P.toMeasure :=
      lintegral_mono fun omega => addSqLeCF (B omega) c
    have hsplit : (∫⁻ omega : ShellSeq d, 4 * (B omega ^ (2 : ℕ) + c ^ (2 : ℕ))
          ∂P.toMeasure) =
        4 * ((∫⁻ omega : ShellSeq d, B omega ^ (2 : ℕ) ∂P.toMeasure) +
          c ^ (2 : ℕ)) := by
      rw [lintegral_const_mul' 4 _ (by norm_num),
        lintegral_add_right _ (measurable_const), lintegral_const, measure_univ,
        mul_one]
    have hsum : (∫⁻ omega : ShellSeq d, B omega ^ (2 : ℕ) ∂P.toMeasure) +
        c ^ (2 : ℕ) ≤ ENNReal.ofReal (2 * (C0 * T * sig)) := by
      rw [hcsq, show (2 : ℝ) * (C0 * T * sig) = C0 * T * sig + C0 * T * sig by ring,
        ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add hFluxL2Sq (ENNReal.ofReal_le_ofReal hqSq)
    calc (∫⁻ omega : ShellSeq d, (B omega + c) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ 4 * ((∫⁻ omega : ShellSeq d, B omega ^ (2 : ℕ) ∂P.toMeasure) +
            c ^ (2 : ℕ)) := le_trans hstep (le_of_eq hsplit)
      _ ≤ 4 * ENNReal.ofReal (2 * (C0 * T * sig)) := mul_le_mul' le_rfl hsum
      _ = ENNReal.ofReal (8 * (C0 * T * sig)) := by
          rw [show (8 : ℝ) * (C0 * T * sig) = 4 * (2 * (C0 * T * sig)) by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  have hcs := lintegral_mul_le_rpow_half_mul_rpow_half P A (fun omega => B omega + c)
    hMeasGradW (hMeasFlux.add aemeasurable_const)
  have hA2 : (∫⁻ omega : ShellSeq d, A omega ^ (2 : ℕ) ∂P.toMeasure) ^
      ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (Real.sqrt (C3 * (S.h : ℝ) * vecNormSq p)) :=
    rpowHalfOfRealCF (by positivity) hGradWL2Sq
  have hB2 : (∫⁻ omega : ShellSeq d, (B omega + c) ^ (2 : ℕ) ∂P.toMeasure) ^
      ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (Real.sqrt (8 * (C0 * T * sig))) :=
    rpowHalfOfRealCF (by positivity) hgroup
  have harith := step1ArithCF hnu C3 C0 (S.h : ℝ) (S.ell : ℝ)
    (((S.ell - S.n : ℕ) : ℝ)) (vecNormSq p) sig hC3 hC0
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpn0 hps
  calc (∫⁻ omega : ShellSeq d, A omega * (B omega + c) ∂P.toMeasure)
      ≤ (∫⁻ omega : ShellSeq d, A omega ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (∫⁻ omega : ShellSeq d, (B omega + c) ^ (2 : ℕ) ∂P.toMeasure) ^
            ((1 : ℝ) / 2) := hcs
    _ ≤ ENNReal.ofReal (Real.sqrt (C3 * (S.h : ℝ) * vecNormSq p)) *
          ENNReal.ofReal (Real.sqrt (8 * (C0 * T * sig))) := mul_le_mul' hA2 hB2
    _ = ENNReal.ofReal (Real.sqrt (C3 * (S.h : ℝ) * vecNormSq p) *
          Real.sqrt (8 * (C0 * T * sig))) :=
        (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
    _ = ENNReal.ofReal (Real.sqrt (8 * (C3 * C0)) * nu ^ (-((3 : ℝ) / 2)) *
          ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))) := by
        rw [show 8 * (C0 * T * sig) = 8 * (C0 * (nu ^ (-(3 : ℝ)) *
          (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) * sig) by rw [hT]]
        exact congrArg ENNReal.ofReal harith

/-! ## The second display of Step 1, at a named constant -/

/-- **The second display of Step 1 at a named constant**:
`|q̃ − q|² ≤ C ν^{-3} ℓ² 3^{-(ℓ-n)} shom_{L',*}(cu_n)`, from the Jensen passage
`hJensen` of the paper and the first display read on `cu_ℓ`. -/
theorem qDiff_sq_explicit {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (S : ScaleSelection) (e : Vec d)
    (uNGlued uTildeGlued : ShellSeq d → Vec d → Vec d) (q qTilde : Vec d)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hJensen : ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q))) ≤
      (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x - uTildeGlued omega x))) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
    (hFluxEll : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x - uTildeGlued omega x))) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (C0 * (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e))) :
    vecNormSq (qTilde - q) ≤
      C0 * (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e) := by
  have hnu3 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsig0 : (0 : ℝ) ≤ vecNormSq (fluxSlot nu S.LPrime P S.n e) := vecNormSq_nonneg _
  set u : ℝ := C0 * (nu ^ (-(3 : ℝ)) * (S.ell : ℝ) ^ (2 : ℕ) *
    (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
    vecNormSq (fluxSlot nu S.LPrime P S.n e) with hu
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  have hchain : ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q))) ≤
      ENNReal.ofReal (Real.sqrt u) :=
    le_trans hJensen (rpowHalfOfRealCF hu0 hFluxEll)
  have hsqrt : Real.sqrt (vecNormSq (qTilde - q)) ≤ Real.sqrt u :=
    (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg u)).1 hchain
  have hns0 : (0 : ℝ) ≤ vecNormSq (qTilde - q) := vecNormSq_nonneg _
  calc vecNormSq (qTilde - q) = (Real.sqrt (vecNormSq (qTilde - q))) ^ (2 : ℕ) :=
        (Real.sq_sqrt hns0).symm
    _ ≤ (Real.sqrt u) ^ (2 : ℕ) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    _ = u := Real.sq_sqrt hu0
/-! ## The `H̲¹` display of Step 2, at a named constant -/

/-- On a cube the volume-normalized `L̲^q` norms increase with the exponent. -/
private theorem cubeLpTwoLeEightCF {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E}
    (_hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    Section2.Norms.cubeLpENorm Q 2 f ≤ Section2.Norms.cubeLpENorm Q 8 f := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- **The constant of the `H̲¹` display of Step 2**: the two printed
second-moment constants of `l.moments.gamma.psi`, one for each half of the
`H̲¹(cu_m)` norm, and the factor `4` of `(x + y)² ≤ 4(x² + y²)`. -/
def h1SecondMomentConstFirst (CL CH : ℝ) : ℝ :=
  max 1 (4 * CL + 4 * (CH ^ (2 : ℕ) * (1 + Real.Gamma 2)))

theorem one_le_h1SecondMomentConstFirst (CL CH : ℝ) :
    1 ≤ h1SecondMomentConstFirst CL CH := le_max_left _ _

/-- **The second display of Step 2 at a named constant**, in the scaled order-one
carrier: `E[(3^m‖∇w‖_{H̲¹(cu_m)})²] ≤ C (1 + 2h) 3^{2h} |p|²`.  The factor
`1 + 2h` is the window factor, carried explicitly. -/
theorem h1_second_moment_explicit {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (HD : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
        (w omega).toH1Function)
    (hMeasHess : ∀ omega : ShellSeq d,
      AEStronglyMeasurable (fun x : Vec d =>
          HilbertMat.ofMat (fun i j => (HD omega).hess i j x))
        (normalizedCubeMeasure (originCube d (S.m : ℤ))))
    (hMeasGradW : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad)
      P.toMeasure)
    (CL : ℝ) (hCL : 1 ≤ CL)
    (hGradWL2Sq : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (CL * (S.h : ℝ) * vecNormSq p))
    (CH : ℝ) (hCH : 1 ≤ CH)
    (hRegHess : ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (CH * (Real.sqrt (vecNormSq p) *
          (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ∧
      ∀ omega : ShellSeq d,
        Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) ≤
          ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) *
          vecCubeH1ENorm (originCube d (S.m : ℤ))
            (w omega).toH1Function.grad
            (fun x => fun i j => (HD omega).hess i j x)) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (h1SecondMomentConstFirst CL CH * (1 + 2 * (S.h : ℝ)) *
        (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p) := by
  obtain ⟨Z, hZmeas, hZbigO, hZbound⟩ := hRegHess
  have hCH0 : (0 : ℝ) < CH := lt_of_lt_of_le (by norm_num) hCH
  have hCL0 : (0 : ℝ) ≤ CL := le_trans (by norm_num) hCL
  have hpn : (0 : ℝ) < vecNormSq p := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hhR : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg _
  have hsqrt1h : (0 : ℝ) < Real.sqrt (1 + (S.h : ℝ)) :=
    Real.sqrt_pos.2 (by linarith only [hhR])
  have h3lp : (0 : ℝ) < (3 : ℝ) ^ (-(S.ellPrime : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hA : (0 : ℝ) < CH * (Real.sqrt (vecNormSq p) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
    mul_pos hCH0 (mul_pos (Real.sqrt_pos.2 hpn) (mul_pos hsqrt1h h3lp))
  have hdown : ∀ omega : ShellSeq d,
      Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) ≤
        ENNReal.ofReal (Z omega) := fun omega =>
    le_trans (cubeLpTwoLeEightCF (originCube d (S.m : ℤ)) (hMeasHess omega))
      (hZbound omega)
  have hMsq := lintegral_sq_le_of_gammaTwo_envelope hA hZmeas hZbigO hdown
  -- the two halves of the scaled `H̲¹` norm
  set L : ShellSeq d → ℝ≥0∞ := fun omega =>
    vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad with hL
  set M : ShellSeq d → ℝ≥0∞ := fun omega =>
    Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) with hM
  have hscale : (((originCube d (S.m : ℤ)).scale : ℝ)) = (S.m : ℝ) :=
    Int.cast_natCast S.m
  have hmpos : (0 : ℝ) < (3 : ℝ) ^ ((S.m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpow2 : (ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ)))) ^ (2 : ℕ) =
      ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) := by
    rw [← ENNReal.ofReal_pow (le_of_lt hmpos)]
    congr 1
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((S.m : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hcancel : ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) *
      ENNReal.ofReal ((3 : ℝ) ^ (-((S.m : ℝ)))) = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hmpos),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hrewrite : ∀ omega : ShellSeq d,
      ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) *
          vecCubeH1ENorm (originCube d (S.m : ℤ))
            (w omega).toH1Function.grad
            (fun x => fun i j => (HD omega).hess i j x) =
        L omega + ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) * M omega := by
    intro omega
    refine (congrArg (ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) * ·) (vecCubeH1ENorm_eq _ _ _)).trans ?_
    rw [hscale, mul_add, ← mul_assoc, hcancel, one_mul]
  have hsqrt : ∀ omega : ShellSeq d,
      (ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) *
          vecCubeH1ENorm (originCube d (S.m : ℤ))
            (w omega).toH1Function.grad
            (fun x => fun i j => (HD omega).hess i j x)) ^ (2 : ℕ) ≤
        4 * (L omega ^ (2 : ℕ) +
          ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) * M omega ^ (2 : ℕ)) := by
    intro omega
    rw [hrewrite omega]
    refine le_trans (addSqLeCF (L omega)
      (ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) * M omega)) ?_
    refine mul_le_mul' le_rfl (add_le_add le_rfl (le_of_eq ?_))
    rw [mul_pow, hpow2]
  have hsplit : (∫⁻ omega : ShellSeq d,
      4 * (L omega ^ (2 : ℕ) +
        ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) * M omega ^ (2 : ℕ))
      ∂P.toMeasure : ℝ≥0∞) =
      4 * ((∫⁻ omega : ShellSeq d, L omega ^ (2 : ℕ) ∂P.toMeasure) +
        ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) *
          ∫⁻ omega : ShellSeq d, M omega ^ (2 : ℕ) ∂P.toMeasure) := by
    rw [lintegral_const_mul' 4 _ (by norm_num),
      lintegral_add_left' (hMeasGradW.pow_const 2),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (le_trans (lintegral_mono hsqrt) (le_of_eq hsplit)) ?_
  have hstep : (∫⁻ omega : ShellSeq d, L omega ^ (2 : ℕ) ∂P.toMeasure) +
      ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) *
        (∫⁻ omega : ShellSeq d, M omega ^ (2 : ℕ) ∂P.toMeasure) ≤
      ENNReal.ofReal (CL * (S.h : ℝ) * vecNormSq p) +
        ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) *
          ENNReal.ofReal ((CH * (Real.sqrt (vecNormSq p) *
            (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ^ (2 : ℕ) *
            (1 + Real.Gamma 2)) :=
    add_le_add hGradWL2Sq (mul_le_mul' le_rfl hMsq)
  refine le_trans (mul_le_mul' le_rfl hstep) ?_
  -- the closing real arithmetic
  have hGamma : (0 : ℝ) < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
  have hAsq : (CH * (Real.sqrt (vecNormSq p) *
        (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ^ (2 : ℕ) *
      (1 + Real.Gamma 2) =
      CH ^ (2 : ℕ) * (1 + Real.Gamma 2) * (1 + (S.h : ℝ)) *
        (3 : ℝ) ^ (-(2 * (S.ellPrime : ℝ))) * vecNormSq p := by
    have h1 : Real.sqrt (vecNormSq p) ^ (2 : ℕ) = vecNormSq p :=
      Real.sq_sqrt (le_of_lt hpn)
    have h2 : Real.sqrt (1 + (S.h : ℝ)) ^ (2 : ℕ) = 1 + (S.h : ℝ) :=
      Real.sq_sqrt (by linarith only [hhR])
    have h3 : ((3 : ℝ) ^ (-(S.ellPrime : ℝ))) ^ (2 : ℕ) =
        (3 : ℝ) ^ (-(2 * (S.ellPrime : ℝ))) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(S.ellPrime : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      ring_nf
    rw [mul_pow, mul_pow, mul_pow, h1, h2, h3]
    ring
  have hcast : (S.m : ℝ) = (S.ellPrime : ℝ) + (S.h : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) S.ellPrime_add_h.symm
  have hexp : (3 : ℝ) ^ (2 * (S.m : ℝ)) * (3 : ℝ) ^ (-(2 * (S.ellPrime : ℝ))) =
      (3 : ℝ) ^ (2 * (S.h : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hcast]
    congr 1
    ring
  have hprodE : ENNReal.ofReal ((3 : ℝ) ^ (2 * (S.m : ℝ))) *
      ENNReal.ofReal (CH ^ (2 : ℕ) * (1 + Real.Gamma 2) * (1 + (S.h : ℝ)) *
        (3 : ℝ) ^ (-(2 * (S.ellPrime : ℝ))) * vecNormSq p) =
      ENNReal.ofReal (CH ^ (2 : ℕ) * (1 + Real.Gamma 2) * (1 + (S.h : ℝ)) *
        (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    congr 1
    calc (3 : ℝ) ^ (2 * (S.m : ℝ)) * (CH ^ (2 : ℕ) * (1 + Real.Gamma 2) *
          (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(2 * (S.ellPrime : ℝ))) * vecNormSq p)
        = CH ^ (2 : ℕ) * (1 + Real.Gamma 2) * (1 + (S.h : ℝ)) *
            ((3 : ℝ) ^ (2 * (S.m : ℝ)) *
              (3 : ℝ) ^ (-(2 * (S.ellPrime : ℝ)))) * vecNormSq p := by ring
      _ = CH ^ (2 : ℕ) * (1 + Real.Gamma 2) * (1 + (S.h : ℝ)) *
            (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p := by rw [hexp]
  rw [hAsq, hprodE, ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; rfl,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3h : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * (S.h : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by linarith only [hhR])
  have h3h0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (S.h : ℝ)) := le_trans zero_le_one h3h
  have hpn0 : (0 : ℝ) ≤ vecNormSq p := le_of_lt hpn
  set K : ℝ := CH ^ (2 : ℕ) * (1 + Real.Gamma 2) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  set R : ℝ := (1 + 2 * (S.h : ℝ)) * (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p with hR
  have hR0 : (0 : ℝ) ≤ R := by rw [hR]; positivity
  have he1 : CL * ((S.h : ℝ) * vecNormSq p) ≤ CL * R := by
    refine mul_le_mul_of_nonneg_left ?_ hCL0
    rw [hR]
    have hh : (S.h : ℝ) ≤ (1 + 2 * (S.h : ℝ)) * (3 : ℝ) ^ (2 * (S.h : ℝ)) := by
      nlinarith only [hhR, h3h]
    have := mul_le_mul_of_nonneg_right hh hpn0
    linarith only [this]
  have he2 : K * ((1 + (S.h : ℝ)) * (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p) ≤
      K * R := by
    refine mul_le_mul_of_nonneg_left ?_ hK0
    rw [hR]
    have hbase : (1 + (S.h : ℝ)) ≤ 1 + 2 * (S.h : ℝ) := by linarith only [hhR]
    have hrest : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p := by positivity
    have := mul_le_mul_of_nonneg_right hbase hrest
    linarith only [this]
  have hle : 4 * CL + 4 * K ≤ h1SecondMomentConstFirst CL CH := by
    rw [hK]
    exact le_max_right _ _
  have hfin := mul_le_mul_of_nonneg_right hle hR0
  calc 4 * (CL * (S.h : ℝ) * vecNormSq p +
        K * (1 + (S.h : ℝ)) * (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p)
      = 4 * (CL * ((S.h : ℝ) * vecNormSq p) +
          K * ((1 + (S.h : ℝ)) * (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p)) := by ring
    _ ≤ 4 * (CL * R + K * R) := by linarith only [he1, he2]
    _ = (4 * CL + 4 * K) * R := by ring
    _ ≤ h1SecondMomentConstFirst CL CH * R := hfin
    _ = h1SecondMomentConstFirst CL CH * (1 + 2 * (S.h : ℝ)) *
          (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p := by ring

/-! ## The closing arithmetic of Step 2 -/

/-- The closing arithmetic of Step 2, after the cancellation `|p|² σ = 1` and
with `m = ℓ' + h`. -/
theorem step2ArithCF {nu : ℝ} (hnu : 0 < nu)
    (C4 C5 W X hh le lp mm pn sig : ℝ) (hC40 : 0 ≤ C4) (hC50 : 0 ≤ C5)
    (hW0 : 0 ≤ W) (hX0 : 0 ≤ X) (hpn0 : 0 ≤ pn) (hps : pn * sig = 1)
    (hmm : mm = lp + hh) :
    Real.sqrt (C4 * W * (3 : ℝ) ^ (2 * hh) * pn) *
        Real.sqrt (C5 * nu ^ (-(2 : ℝ)) * X * (3 : ℝ) ^ (2 * le - 2 * mm) * sig) =
      Real.sqrt (C4 * C5) * Real.sqrt W * nu ^ (-(1 : ℝ)) * Real.sqrt X *
        (3 : ℝ) ^ (-(lp - le)) := by
  have h3a : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * hh) := Real.rpow_nonneg (by norm_num) _
  have hnu2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hfirst : (0 : ℝ) ≤ C4 * W * (3 : ℝ) ^ (2 * hh) * pn := by positivity
  rw [← Real.sqrt_mul hfirst]
  have hcollect : (C4 * W * (3 : ℝ) ^ (2 * hh) * pn) *
      (C5 * nu ^ (-(2 : ℝ)) * X * (3 : ℝ) ^ (2 * le - 2 * mm) * sig) =
      C4 * C5 * W * nu ^ (-(2 : ℝ)) * X *
        ((3 : ℝ) ^ (2 * hh) * (3 : ℝ) ^ (2 * le - 2 * mm)) * (pn * sig) := by ring
  rw [hcollect, hps, mul_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hexp : 2 * hh + (2 * le - 2 * mm) = 2 * (le - lp) := by rw [hmm]; ring
  rw [hexp, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hnuhalf : Real.sqrt (nu ^ (-(2 : ℝ))) = nu ^ (-(1 : ℝ)) := by
    rw [sqrtRpowNegCF hnu 2]
    norm_num
  have h3half : Real.sqrt ((3 : ℝ) ^ (2 * (le - lp))) = (3 : ℝ) ^ (-(lp - le)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hnuhalf, h3half]
end

end SuperdiffusionCLT.Section3.Terms
