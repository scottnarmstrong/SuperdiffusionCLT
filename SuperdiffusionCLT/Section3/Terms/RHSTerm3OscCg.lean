/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst

/-!
# `hOscBound`: the small-cube oscillation term of `l.RHS.term3`

The display is `e.RHS.term3.B` of the paper, together with its proof.

`Section3/Terms/RHSTerm3StepsA2.lean` proves `rhs_term3_B`, whose conclusion is
exactly the binder `_hOscBound` of the term-3 statement, from four inputs.  This
module discharges one of them, `hOsc`, the second display of the proof of
`e.RHS.term3.B`, from the **second** clause of `e.nablaw.Lt`.

The clause is available with no hypothesis beyond `d` and `2 ≤ d`:
`l_w_basic_regbounds_window` (`Section3/ResponseFields/RegboundsWindowB.lean`)
proves all three clauses from the two statements
`responseFields_apriori_orderZero` and `streamIncrement_scale_estimates`.  Its
Hessian clause reads the `L̲⁸(cu_m)` cube norm of the weak Hessian of the
response against a `Γ₂` envelope of amplitude `C|p|√(1 + h)3^{-ℓ'}`, and the
weak Hessian exists unconditionally
(`exists_hasWeakHessianOn_of_isDirichletResponse`,
`Section3/Terms/RHSTerm4Anchors.lean`).

What is **not** discharged is the first inequality of the printed display, the
per-cube Poincaré inequality for the centered gradient on `z + cu_n`: the
normalized `H̲¹` and `L̲³` norms on a *translated* cube are not available in this form.
It is the single hypothesis `hPoincare` throughout this module, stated against
the `L̲⁸(cu_m)` Hessian norm of the clause; see `osc_avsum_third_moment_of_regbounds` for
the three deterministic steps it carries.

The union-bound loss `√(1 + h)`, which the Hessian clause carries, survives
into the constant of `hOsc` as `(1 + h)^{3/2}` and into `C_B`
as `(1 + h)^{1/2}`.  It is **not** absorbable into a `d`-only constant, and the
right side of `_hOscBound` has no slack in `h`, so `_hOscBound` cannot be
removed from the term-3 statement with its constant `C_B` still
quantified before the scale selection.

## Main results

* `toReal_lintegral_pow_le_of_isBigO_gammaSigma_two`: the `lintegral` form of
  the `Γ₂` moment step, for an `ℝ≥0∞`-valued observable.
* `hessW3_third_moment_of_regbounds`: the third moment of the response Hessian
  on `cu_m` from the second clause of `e.nablaw.Lt`.
* `osc_avsum_third_moment_of_regbounds`: `hOsc` of `rhs_term3_B`, discharged.
* `osc_bound_bridge`: `_hOscBound` in its exact shape, at the constant
  `oscBoundConst`.
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
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## From a `Γ₂` envelope to a `k`-th moment of an extended-real observable -/

/-- **The `k`-th moment of an `ℝ≥0∞`-valued observable dominated by a `Γ₂`
envelope.**  This is the `lintegral` form of the moment step of
`gradW_l4_fourth_moment_of_regbounds` (`Section3/Terms/RHSTerm3InputsB.lean`),
with the `ℝ≥0∞`-valued quantity left abstract: no measurability of the
observable is needed, because the `lintegral` is monotone unconditionally. -/
theorem toReal_lintegral_pow_le_of_isBigO_gammaSigma_two
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {N : Omega → ℝ≥0∞} {Z : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hZm : AEMeasurable Z mu)
    (hZ : IsBigO mu (gammaSigma 2) Z A)
    (hbound : ∀ omega, N omega ≤ ENNReal.ofReal (Z omega)) (k : ℕ) :
    (∫⁻ omega, N omega ^ k ∂mu).toReal ≤
      A ^ ((k : ℕ) : ℝ) * (1 + Real.Gamma (((k : ℕ) : ℝ) / 2 + 1)) := by
  have hGamma : (0 : ℝ) < Real.Gamma (((k : ℕ) : ℝ) / 2 + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hptr : ∀ omega, N omega ^ k ≤ ENNReal.ofReal (|Z omega| ^ ((k : ℕ) : ℝ)) := by
    intro omega
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc N omega ^ k ≤ (ENNReal.ofReal |Z omega|) ^ k :=
          pow_le_pow_left' ((hbound omega).trans habs) k
      _ = ENNReal.ofReal (|Z omega| ^ k) := (ENNReal.ofReal_pow (abs_nonneg _) k).symm
      _ = ENNReal.ofReal (|Z omega| ^ ((k : ℕ) : ℝ)) := by rw [Real.rpow_natCast]
  have hint : Integrable (fun omega => |Z omega| ^ ((k : ℕ) : ℝ)) mu :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZm hZ k
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hA hZm hZ k
  have hlint : (∫⁻ omega, N omega ^ k ∂mu) ≤
      ENNReal.ofReal (A ^ ((k : ℕ) : ℝ) * (1 + Real.Gamma (((k : ℕ) : ℝ) / 2 + 1))) := by
    calc (∫⁻ omega, N omega ^ k ∂mu)
        ≤ ∫⁻ omega, ENNReal.ofReal (|Z omega| ^ ((k : ℕ) : ℝ)) ∂mu := lintegral_mono hptr
      _ = ENNReal.ofReal (∫ omega, |Z omega| ^ ((k : ℕ) : ℝ) ∂mu) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (A ^ ((k : ℕ) : ℝ) *
            (1 + Real.Gamma (((k : ℕ) : ℝ) / 2 + 1))) := ENNReal.ofReal_le_ofReal hmom
  refine ENNReal.toReal_le_of_le_ofReal ?_ hlint
  have hApow : (0 : ℝ) < A ^ ((k : ℕ) : ℝ) := Real.rpow_pos_of_pos hA _
  positivity

/-! ## The third moment of the response Hessian on `cu_m` -/

/-- The constant of the third-moment form of the second clause of
`e.nablaw.Lt`: the third power of the constant of `l.w.basic.regbounds` times
the third Orlicz moment factor `1 + Γ(5/2)` of `l.moments.gamma.psi`. -/
def nablaW3Const (C : ℝ) : ℝ := C ^ (3 : ℕ) * (1 + Real.Gamma (5 / 2))

theorem nablaW3Const_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ nablaW3Const C := by
  have hG : (0 : ℝ) < Real.Gamma (5 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hC3 : (0 : ℝ) ≤ C ^ (3 : ℕ) := pow_nonneg hC 3
  rw [nablaW3Const]
  positivity

private theorem sqrt_pow_three {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ^ (3 : ℕ) = x ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) 3, ← Real.rpow_mul hx]
  norm_num

/-- **`E[‖∇²w‖³_{L̲⁸(cu_m)}] ≤ C(1 + h)^{3/2}|p|³3^{-3ℓ'}`**, the third-moment
form of the **second** clause of `e.nablaw.Lt` (`l.w.basic.regbounds`), which is the input the
second display of `e.RHS.term3.B` reads.

`hZmeas`, `hZbigO`, `hZbound` are that clause in its exact shape, i.e. the
second conclusion of `l_w_basic_regbounds_window`
(`Section3/ResponseFields/RegboundsWindowB.lean`) at the constant `C`: an
`L̲⁸(cu_m)` bound on the response Hessian by a `Γ₂` envelope of amplitude
`C|p|√(1 + h)3^{-ℓ'}`.  The factor `√(1 + h)` is the union-bound loss; it is
carried through to the conclusion, where it appears as `(1 + h)^{3/2}`.

The moment is the `lintegral` of the third power of the extended-real cube
norm, exactly as `gradResponseMoment` (`Section3/Terms/RHSTerm3InputsB.lean`)
is for the gradient; no measurability in `ω` is needed. -/
theorem hessW3_third_moment_of_regbounds
    {d : ℕ} [NeZero d] {P : ProbabilityMeasure (ShellSeq d)} {S : ScaleSelection}
    {p : Vec d} (hq : 0 < vecNormSq p) (H : ShellSeq d → Vec d → HilbertMat d)
    {C : ℝ} (hC : 0 < C) {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) *
        (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))))
    (hZbound : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ≤ ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ^ (3 : ℕ) ∂P.toMeasure).toReal ≤
      nablaW3Const C * ((1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) *
        (vecNormSq p ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))))) := by
  have hh0 : (0 : ℝ) < 1 + (S.h : ℝ) := by
    have := (Nat.cast_nonneg S.h : (0 : ℝ) ≤ (S.h : ℝ))
    linarith only [this]
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-(S.ellPrime : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hA : (0 : ℝ) < C * (Real.sqrt (vecNormSq p) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
    mul_pos hC (mul_pos (Real.sqrt_pos.2 hq) (mul_pos (Real.sqrt_pos.2 hh0) h3pos))
  have hmom := toReal_lintegral_pow_le_of_isBigO_gammaSigma_two hA hZmeas.aemeasurable
    hZbigO hZbound 3
  refine hmom.trans_eq ?_
  have hthree : ((3 : ℝ) ^ (-(S.ellPrime : ℝ))) ^ (3 : ℕ) =
      (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(S.ellPrime : ℝ))) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  rw [Real.rpow_natCast, show ((3 : ℕ) : ℝ) / 2 + 1 = 5 / 2 by norm_num,
    mul_pow, mul_pow, mul_pow, sqrt_pow_three (le_of_lt hq),
    sqrt_pow_three (le_of_lt hh0), hthree, nablaW3Const]
  ring

/-! ## `hOsc`: the second display of `e.RHS.term3.B` -/

/-- **`hOsc` of `rhs_term3_B`, discharged**: the second display of the proof of
`e.RHS.term3.B`

`avsum_z E[[∇w − (∇w)_{z+cu_n}]³_{H̲¹(z+cu_n)}] ≤ C ν^{-3/2}3^{-3ℓ'}`.

The source proves it in two moves: the per-cube Poincaré inequality for the
*centered* gradient, `avsum_z E[[·]³_{H̲¹(z+cu_n)}] ≤ C avsum_z E[‖∇²w‖³_{L̲³(z+cu_n)}]`,
and then `e.nablaw.Lt`.  The second move is what is proved here: it is
`hessW3_third_moment_of_regbounds` together with the crude bound
`|p|² = shom_{L',*}^{-1}(cu_n) ≤ ν⁻¹` (`sigmaBarStarInvSeq_le_nuInv`, the
sentence before `e.v.ky.energy`).

The first move is the hypothesis `hPoincare`.  It is stated against the form
of the second clause of `e.nablaw.Lt`, i.e. with the `L̲⁸(cu_m)` cube
norm of the Hessian on the right, because the normalized `L̲³` norm of a
Hessian on a *translated* cube `z + cu_n` is not available in this form.  Written that
way it carries three deterministic steps at once: the printed per-cube Poincaré
inequality, the exact sub-cube partition
`avsum_z ⨍_{z+cu_n} = ⨍_{cu_m}`, and the normalized-exponent
monotonicity `‖·‖_{L̲³(cu_m)} ≤ ‖·‖_{L̲⁸(cu_m)}`.

The factor `(1 + h)^{3/2}` in the constant is the third power of the union-bound
loss `√(1 + h)`, which the second clause of
`l_w_basic_regbounds_window` carries. -/
theorem osc_avsum_third_moment_of_regbounds
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {S : ScaleSelection} {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (H : ShellSeq d → Vec d → HilbertMat d)
    (oscH1 : ShellSeq d → TriadicCube d → ℝ)
    {C Cpo : ℝ} (hC : 0 < C) (hCpo : 0 ≤ Cpo)
    {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) *
        (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))))
    (hZbound : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ≤ ENNReal.ofReal (Z omega))
    (hPoincare : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, oscH1 omega R ^ (3 : ℝ) ∂P.toMeasure ≤
      Cpo * (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ^ (3 : ℕ) ∂P.toMeasure).toReal) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, oscH1 omega R ^ (3 : ℝ) ∂P.toMeasure ≤
      Cpo * nablaW3Const C * (1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) * nu ^ (-(3 / 2 : ℝ)) *
        (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))) := by
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]
    exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hq : 0 < vecNormSq p := by
    rw [hpsq]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hqle : vecNormSq p ^ ((3 : ℝ) / 2) ≤ nu ^ (-(3 / 2 : ℝ)) := by
    have hcrude : vecNormSq p ≤ nu⁻¹ := by
      rw [hpsq]
      exact sigmaBarStarInvSeq_le_nuInv hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
    have hstep := Real.rpow_le_rpow (le_of_lt hq) hcrude
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
    rwa [Real.inv_rpow (le_of_lt hnu), ← Real.rpow_neg (le_of_lt hnu)] at hstep
  have hM := hessW3_third_moment_of_regbounds (P := P) hq H hC hZmeas hZbigO hZbound
  have hmono : nablaW3Const C * ((1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) *
        (vecNormSq p ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))))) ≤
      nablaW3Const C * ((1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) *
        (nu ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))))) := by
    have hh : (0 : ℝ) ≤ (1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) := by
      refine Real.rpow_nonneg ?_ _
      have := (Nat.cast_nonneg S.h : (0 : ℝ) ≤ (S.h : ℝ))
      linarith only [this]
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hqle h3) hh) ?_
    exact nablaW3Const_nonneg (le_of_lt hC)
  have hfinal := mul_le_mul_of_nonneg_left (hM.trans hmono) hCpo
  refine hPoincare.trans (hfinal.trans_eq ?_)
  ring

/-! ## `hOscBound` -/

/-- The constant `C_B` of `e.RHS.term3.B` produced by `osc_bound_bridge`:
`C_w^{1/3}C_3^{2/3}` at `C_w = C_{Poincaré} C_{∇²w,3}(C_reg)(1 + h)^{3/2}`. -/
def oscBoundConst (Cpo C C3 : ℝ) (h : ℕ) : ℝ :=
  (Cpo * nablaW3Const C * (1 + (h : ℝ)) ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 3) *
    C3 ^ ((2 : ℝ) / 3)

/-- **`hOscBound` of the term-3 statement**, i.e.
`e.RHS.term3.B`, with the
input `hOsc` of `rhs_term3_B` **discharged** from the second clause of
`e.nablaw.Lt`.

The conclusion of `rhs_term3_B` at
`C_w = C_po·nablaW3Const C·(1 + h)^{3/2}`, with the binder `hOsc` replaced by
the second clause of `l.w.basic.regbounds` in its exact shape (`hZmeas`,
`hZbigO`, `hZbound`) and by the per-cube Poincaré step `hPoincare`; see
`osc_avsum_third_moment_of_regbounds` for what each of them carries.  The three
remaining source inputs `hCS`, `hFlux`, `hEnergy` of `rhs_term3_B` are
unchanged. -/
theorem osc_bound_bridge
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {S : ScaleSelection} (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    {p : Vec d} (hp : p = testVector nu S.LPrime P S.n e)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (H : ShellSeq d → Vec d → HilbertMat d)
    (oscH1 fluxNegNorm energyL2 : ShellSeq d → TriadicCube d → ℝ)
    {C Cpo C3 delta etaL : ℝ} (hC : 0 < C) (hCpo : 0 ≤ Cpo) (hC3 : 0 ≤ C3)
    (hde : 0 ≤ delta + etaL)
    (hOscNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ oscH1 omega R)
    (hFluxNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ fluxNegNorm omega R)
    (hEnergyNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ energyL2 omega R)
    (hCS : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      volumeAverage (openCubeSet R)
          (fun y => vecDot ((w omega).toH1Function.grad y -
              volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ≤
        oscH1 omega R * fluxNegNorm omega R)
    {Z : ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : IsBigO P.toMeasure (gammaSigma 2) Z
      (C * (Real.sqrt (vecNormSq p) *
        (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))))
    (hZbound : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ≤ ENNReal.ofReal (Z omega))
    (hPoincare : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, oscH1 omega R ^ (3 : ℝ) ∂P.toMeasure ≤
      Cpo * (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 8 (H omega) ^ (3 : ℕ) ∂P.toMeasure).toReal)
    (hFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d, fluxNegNorm omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤
        C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
          (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4))
    (hEnergy : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure ≤ delta + etaL)
    (hXint : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet R)
            (fun y => vecDot ((w omega).toH1Function.grad y -
                volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hOFint : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => oscH1 omega R * fluxNegNorm omega R) P.toMeasure)
    (hMemOsc : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => oscH1 omega R) (ENNReal.ofReal (3 : ℝ)) P.toMeasure)
    (hMemFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => fluxNegNorm omega R)
        (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            volumeAverage (openCubeSet R)
              (fun y => vecDot ((w omega).toH1Function.grad y -
                  volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y)))
        ∂P.toMeasure ≤
      oscBoundConst Cpo C C3 S.h * nu ^ (-(3 / 2 : ℝ)) *
        (delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) := by
  have hCwnn : (0 : ℝ) ≤ Cpo * nablaW3Const C * (1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) := by
    have hh : (0 : ℝ) ≤ (1 + (S.h : ℝ)) ^ ((3 : ℝ) / 2) := by
      refine Real.rpow_nonneg ?_ _
      have := (Nat.cast_nonneg S.h : (0 : ℝ) ≤ (S.h : ℝ))
      linarith only [this]
    exact mul_nonneg (mul_nonneg hCpo (nablaW3Const_nonneg (le_of_lt hC))) hh
  have hOsc := osc_avsum_third_moment_of_regbounds hnu hPrefix hJ2 hJ3 hJ4 he hp H
    oscH1 hC hCpo hZmeas hZbigO hZbound hPoincare
  simp only [oscBoundConst]
  exact rhs_term3_B hnu hnu1 P hSorder w uMgrad uNGlued oscH1 fluxNegNorm energyL2
    hCwnn hC3 hde hOscNonneg hFluxNonneg hEnergyNonneg hCS hOsc hFlux hEnergy
    hXint hOFint hMemOsc hMemFlux

/-! ## `hOsc` with the regularity gate discharged -/

end

end SuperdiffusionCLT.Section3.Terms
