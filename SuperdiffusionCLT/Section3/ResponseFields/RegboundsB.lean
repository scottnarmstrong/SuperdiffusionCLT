/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section3.ResponseFields.Regbounds
public import SuperdiffusionCLT.Section3.Setup.DirichletResponse
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-!
# `l.w.basic.regbounds`

This module supplies the constants and the centered-flux estimate for `e.nablaw.Lt` of the
paper; the estimate itself is assembled in `l_w_basic_regbounds_window`
(`RegboundsWindowB.lean`).

The response `w` of `e.def.w` is the Dirichlet response on `cu_m` of the flux
`F = (k_{L'} − k_{ℓ'})p`, and constants are harmless under the divergence, so
`w` is equally the Dirichlet response of `F − c` for every constant vector `c`.
Applying the deterministic a priori estimates of `l.abstract.response.fields`
to `F` and to `F` centered at the cube average of its upper shell bounds

* `‖∇w‖_{L̲^8(cu_m)}` by `‖F − c‖_{L̲^8(cu_m)}`,
* `‖∇²w‖_{L̲^8(cu_m)}` by `‖∇F‖_{L̲^8(cu_m)}`, and
* `‖∇w‖_{H̲^{1/2}(cu_m)}` by `‖F − c‖_{H̲^{1/2}(cu_m)}`,

and the three flux quantities are the three parenthesized terms of the printed
proof, estimated in `Regbounds.lean` and in the two theorems below.

## Main results

* `exists_witness_cubeHsENorm_centeredFlux`: the third parenthesized term.
* `regboundsConst`: the constant of `e.nablaw.Lt`, quantified **before** the scale selection,
  the shell law, the test vector and the response, so that it is the manuscript's `C(d)`-style
  constant: it depends only on the dimension and on the constants of the inputs.

## The inputs

The assembly of `e.nablaw.Lt` takes, as explicit hypotheses:

* the conclusion of the a priori anchor `responseFields_apriori_orderZero`;
* the `L̲^8`, `L̲²` and `H̲^{1/2}`-oscillation clauses of the shell-increment
  scale estimates at `(ℓ', m − 1, m)`, in their stated shapes; and
* the printed estimate `‖∇(k_{m−1} − k_{ℓ'})p‖_{L̲^8(cu_m)} = O_{Γ₂}(C|p|3^{-ℓ'})`
  for the shells **below** the cube scale.  The last one is carried because the
  shell derivative display `e.nabla.kmn.Linfty` is a small-cube statement: on
  `cu_m` it controls only the shells `k ≥ m`, and the printed proof gets the
  shells `k < m` from stationarity over the `3^{d(m−k)}` sub-cubes of `cu_m`,
  which is a separate input (see `RegboundsGateB.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The centered flux in `H̲^{1/2}(cu_m)` -/

/-- **The third parenthesized term of `l.w.basic.regbounds`**.  The `H̲^{1/2}` norm is
at most the sum of its weighted `L̲²` half — supplied by
`exists_witness_vecCubeLpENorm_centeredFlux` at `q = 2` — and its Gagliardo
half, which the printed proof takes from the oscillation clause of the
shell-increment estimates evaluated at the shell `L'`.  The weight `3^{-m/2}`
absorbs the `h^{1/2}` of the `L̲²` half through `m = ℓ' + h`, which is the
printed last step.  That oscillation clause holds almost surely, so the
conclusion does. -/
theorem exists_witness_cubeHsENorm_centeredFlux
    {S : ScaleSelection} (hS : ScalesOrdering S)
    {p : Vec d} (hp : 0 < vecNorm p)
    {K2 : ℝ} (hK2 : 0 < K2) {Y2 : ShellSeq d → ℝ} (hY2m : Measurable Y2)
    (hY2nn : ∀ omega, 0 ≤ Y2 omega)
    (hY2O : IsBigO P.toMeasure (gammaSigma 2) Y2
      (K2 * (vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2))))
    (hY2le : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x =>
            matVecMul (streamCutoff omega S.LPrime x -
              streamCutoff omega S.ellPrime x) p -
            volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
              (fun y => matVecMul (streamCutoff omega S.LPrime y -
                streamCutoff omega (S.m - 1) y) p)) ≤
        ENNReal.ofReal (Y2 omega))
    {CH : ℝ} (hCH : 0 < CH) {XH : ShellSeq d → ℝ} (hXHm : Measurable XH)
    (hXHO : IsBigO P.toMeasure (gammaSigma 2) XH
      (CH * (3 : ℝ) ^ (-(((1 : ℝ) / 2) * (S.ellPrime : ℝ)))))
    (hXHle : ∀ᵐ omega ∂P.toMeasure,
      (⨆ M : {M : ℕ // S.ellPrime < M},
        Section2.Norms.cubeEuclideanGagliardoESeminorm
          (originCube d (S.m : ℤ)) ((1 : ℝ) / 2) 2
          (fun x => (finiteShellIncrement omega S.ellPrime M.1 x : Mat d))) ≤
        ENNReal.ofReal (XH omega)) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧ (∀ omega, 0 ≤ Y omega) ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        ((gammaTriangleConst 2 * (K2 + CH)) *
          (vecNorm p * (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)))) ∧
      ∀ᵐ omega ∂P.toMeasure,
        Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
            (hilbertifyVecField fun x =>
              matVecMul (streamCutoff omega S.LPrime x -
                streamCutoff omega S.ellPrime x) p -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (fun y => matVecMul (streamCutoff omega S.LPrime y -
                  streamCutoff omega (S.m - 1) y) p)) ≤
          ENNReal.ofReal (Y omega) := by
  have hlt : S.ellPrime < S.LPrime := by
    have h1 := hS.ellPrime_lt_m
    have h2 := hS.m_lt_LPrime
    omega
  have hfull : S.ellPrime ≤ S.LPrime := hlt.le
  have hgpos : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  set dec : ℝ := (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) with hdecdef
  have hdecpos : 0 < dec := by
    rw [hdecdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  set wt : ℝ := ((3 : ℝ) ^ (S.m : ℤ)) ^ (-((1 : ℝ) / 2)) with hwtdef
  have hwtpos : 0 < wt := by
    rw [hwtdef]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hweight : Section2.Norms.cubeHsWeight (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
      = ENNReal.ofReal wt := by
    rw [Section2.Norms.cubeHsWeight, cubeScaleFactor_originCube, hwtdef]
  have hUO : IsBigO P.toMeasure (gammaSigma 2) (fun omega => wt * Y2 omega)
      (K2 * (vecNorm p * dec)) := by
    refine (hY2O.const_mul hwtpos.le).mono_scale ?_
    have hEq : wt * (K2 * (vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2))) =
        K2 * vecNorm p * (wt * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) := by ring
    rw [hEq]
    have hfac : (0 : ℝ) ≤ K2 * vecNorm p := mul_nonneg hK2.le hp.le
    have hstep := mul_le_mul_of_nonneg_left (cubeHsWeight_mul_rpow_h_le S) hfac
    refine hstep.trans (le_of_eq ?_)
    rw [hdecdef]
    ring
  have hXHO' : IsBigO P.toMeasure (gammaSigma 2) XH (CH * dec) := by
    have hexp : (-(((1 : ℝ) / 2) * (S.ellPrime : ℝ))) = -((S.ellPrime : ℝ) / 2) := by
      ring
    rw [hexp] at hXHO
    exact hXHO
  have hVO : IsBigO P.toMeasure (gammaSigma 2)
      (fun omega => vecNorm p * |XH omega|) (CH * (vecNorm p * dec)) := by
    refine ((isBigO_gammaSigma_abs.2 hXHO').const_mul hp.le).mono_scale
      (le_of_eq ?_)
    ring
  have hUm : Measurable (fun omega : ShellSeq d => wt * Y2 omega) :=
    Measurable.const_mul hY2m _
  have hVm : Measurable (fun omega : ShellSeq d => vecNorm p * |XH omega|) :=
    Measurable.const_mul (measurable_abs_of hXHm) _
  have hUnn : ∀ omega : ShellSeq d, 0 ≤ wt * Y2 omega := fun omega =>
    mul_nonneg hwtpos.le (hY2nn omega)
  have hVnn : ∀ omega : ShellSeq d, 0 ≤ vecNorm p * |XH omega| := fun omega =>
    mul_nonneg hp.le (abs_nonneg _)
  refine ⟨fun omega => wt * Y2 omega + vecNorm p * |XH omega|,
    Measurable.add hUm hVm, ?_, ?_, ?_⟩
  · exact fun omega => by linarith only [hUnn omega, hVnn omega]
  · have hsum := isBigO_gammaSigma_abs_add_pos (P := P)
      (X := fun omega => wt * Y2 omega)
      (Y := fun omega => vecNorm p * |XH omega|)
      (mul_pos hK2 (mul_pos hp hdecpos)) (mul_pos hCH (mul_pos hp hdecpos))
      hUm hVm hUO hVO
    have habs : (fun omega : ShellSeq d =>
        |wt * Y2 omega| + |(vecNorm p * |XH omega|)|) =
        fun omega : ShellSeq d => wt * Y2 omega + vecNorm p * |XH omega| := by
      funext omega
      rw [abs_of_nonneg (hUnn omega), abs_of_nonneg (hVnn omega)]
    rw [habs] at hsum
    refine hsum.mono_scale (le_of_eq ?_)
    ring
  · filter_upwards [hXHle] with omega homega
    refine le_trans (Section2.Norms.cubeHsENorm_le_add _ _ _) ?_
    have hL2 : Section2.Norms.cubeHsWeight (originCube d (S.m : ℤ)) ((1 : ℝ) / 2) *
        Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
          (hilbertifyVecField fun x =>
            matVecMul (streamCutoff omega S.LPrime x -
              streamCutoff omega S.ellPrime x) p -
            volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
              (fun y => matVecMul (streamCutoff omega S.LPrime y -
                streamCutoff omega (S.m - 1) y) p)) ≤
        ENNReal.ofReal (wt * Y2 omega) := by
      rw [hweight, ENNReal.ofReal_mul hwtpos.le]
      exact mul_le_mul' le_rfl (hY2le omega)
    have hGag : Section2.Norms.cubeEuclideanGagliardoESeminorm
        (originCube d (S.m : ℤ)) ((1 : ℝ) / 2) 2
        (hilbertifyVecField fun x =>
          matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (fun y => matVecMul (streamCutoff omega S.LPrime y -
              streamCutoff omega (S.m - 1) y) p)) ≤
        ENNReal.ofReal (vecNorm p * |XH omega|) := by
      refine le_trans (cubeEuclideanGagliardoESeminorm_streamFlux_sub_const_le
        (originCube d (S.m : ℤ)) ((1 : ℝ) / 2) omega hfull p _) ?_
      rw [ENNReal.ofReal_mul (vecNorm_nonneg p)]
      refine mul_le_mul' le_rfl ?_
      refine le_trans ?_ (le_trans homega
        (ENNReal.ofReal_le_ofReal (le_abs_self (XH omega))))
      exact le_iSup (f := fun M : {M : ℕ // S.ellPrime < M} =>
        Section2.Norms.cubeEuclideanGagliardoESeminorm
          (originCube d (S.m : ℤ)) ((1 : ℝ) / 2) 2
          (fun x => (finiteShellIncrement omega S.ellPrime M.1 x : Mat d)))
        ⟨S.LPrime, hlt⟩
    refine le_trans (add_le_add hL2 hGag) ?_
    rw [← ENNReal.ofReal_add (hUnn omega) (hVnn omega)]

/-! ## The constants -/

/-- The constant produced by one clause of the shell-increment scale estimates
at `(ℓ', m − 1, m)`: the deterministic shift `C (m−1−ℓ')^{1/2}` and the `Γ₂`
part `C p^{1/2} (m−1−ℓ')^{1/2}`, both absorbed into `h^{1/2}` by
`m − ℓ' = h`. -/
def regboundsGateConst (C r : ℝ) : ℝ :=
  gammaTriangleConst 2 * ((|C| + 1) + (|C| * r ^ ((1 : ℝ) / 2) + 1))

theorem regboundsGateConst_pos {C r : ℝ} (hr : 0 ≤ r) : 0 < regboundsGateConst C r := by
  have h2 : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  have h3 : (0 : ℝ) ≤ |C| * r ^ ((1 : ℝ) / 2) :=
    mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hr _)
  rw [regboundsGateConst]
  have h4 : (0 : ℝ) < (|C| + 1) + (|C| * r ^ ((1 : ℝ) / 2) + 1) := by
    linarith only [abs_nonneg C, h3]
  exact mul_pos h2 h4

/-- **The constant of `e.nablaw.Lt`.** It depends only on the dimension, on the
constant of the a priori response estimates, and on the constants of the three
shell-increment clauses and of the lower-shell Jacobian estimate; it does not
depend on the scale selection, on the shell law, on the test vector or on the
response. -/
def regboundsConst (d : ℕ) (Ca C8 C2 CH Cn : ℝ) : ℝ :=
  max 1
    (max (Ca * (gammaTriangleConst 2 *
        ((regboundsUpperConst d + 1) + regboundsGateConst C8 8)))
      (max (Ca * (gammaTriangleConst 2 * (regboundsJacobianConst d + Cn)))
        (Ca * (gammaTriangleConst 2 *
          (gammaTriangleConst 2 *
              ((regboundsUpperConst d + 1) + regboundsGateConst C2 2) + CH)))))

theorem one_le_regboundsConst (d : ℕ) (Ca C8 C2 CH Cn : ℝ) :
    1 ≤ regboundsConst d Ca C8 C2 CH Cn :=
  le_max_left _ _

end

end SuperdiffusionCLT.Section3.ResponseFields
