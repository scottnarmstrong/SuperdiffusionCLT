/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscNormSwap
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscMembership
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCg
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscProduct
public import SuperdiffusionCLT.Section3.Terms.MultiscalePoincareFlux
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB

/-!
# `_hOscBound` closed at the seminorm carrier

`RHSTerm3OscNormSwap` moved the scale factor `3^n` from the carrier (where it
sits in the centred-gradient carrier, the zero-order Poincare summand) onto the flux,
paying the per-cube comparison constant `K_R = 3^{scale R}·(C_d + 3)` of
`centredSeminormNegNorm_le_vecHatNegENormOrderOne`.  This module removes that
comparison constant from the duality step altogether, by reading the flux norm at
the seminorm carrier's **own** dual norm: the centred test class has the seminorm
`‖∇²g‖_{L̲²(Q)}`, so the negative norm built from that class is a genuine norm of
the flux, and the printed duality holds against it with **no** constant (it is
`centredSeminormDuality_subcube` read in real form, `oscBound_cs_seminorm` here).

* `seminormFluxNeg` is that norm in real form.  `_hCS` at the seminorm carrier
  against `seminormFluxNeg` is unconditional: the only input is the `L²(R)`
  membership of the glued flux, which is the telescope's
  `memLp_fluxFieldCarrier_gluedDiff`.
* `_hPoincare` at the seminorm carrier is `seminormCarrier_hPoincare` at the
  constant **one**; its finiteness input `hfin` is discharged from the `Γ₂`
  envelope of `l_w_basic_regbounds_window`
  (`oscHessian_lintegral_ne_top`), and its third-moment input `hintR` is
  carried and then reduced to a single a.e. strong measurability statement by
  `integrable_seminormThird_of_envelope`.
* The order-one hatted flux norm is **not** a valid partner: the comparison runs
  the other way at the price of `K_R`.  The two moments then cancel: `K_R` on
  every scale-`n` sub-cube is `3^n(C_d + 3)`, and
  `K_R^{3/2} = 3^{3n/2}(C_d + 3)^{3/2}` cancels the printed `3^{3n/2}` of the flux
  chain up to the `d`-only factor `(C_d + 3)^{3/2}`.  At the centred norm no
  cancellation is needed at all: `seminormFluxNeg` carries no scale, and the
  printed `3^{3n/2}` of the chain stays where the paper puts it.

The surviving constant `CB` is `max 1 (oscBoundConstBase 1 C C3)` with `C` the
`l_w_basic_regbounds_window` constant (a function of `d` and `hd` alone) and `C3`
a parameter fixed before the scale selection: it mentions neither `S`, nor `nu`,
nor `P`, nor any power of `3`.
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

noncomputable section

variable {d : ℕ}

/-! ## The flux norm of the seminorm carrier -/

/-- **The printed flux norm at the seminorm carrier.**  The display pairs its
centred gradient against the flux of the glued difference; at the seminorm
carrier the partner is the negative norm built from the
centred test class `CentredSeminormTestField R` of `RHSTerm3OscMeanZero` — the
dual of the seminorm `‖∇²g‖_{L̲²(R)}` itself, with no scale factor and no
constant.  Written in real form as the `toReal` of `centredSeminormNegNorm`. -/
def seminormFluxNeg {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) : ℝ :=
  (centredSeminormNegNorm R (fluxFieldCarrier nu S omega
    (oscGluedGradM nu hnu S P e omega) (oscGluedGradN nu hnu S P e omega))).toReal

/-- The seminorm flux norm is nonnegative: it is the `toReal` of an extended-real
norm. -/
theorem seminormFluxNeg_nonneg {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) :
    0 ≤ seminormFluxNeg nu hnu S P e omega R :=
  ENNReal.toReal_nonneg

/-- The glued flux field of the display is `L²(R)` on every cube: the
telescope's `memLp_fluxFieldCarrier_gluedDiff` at the two glued gradients
`oscGluedGradM`, `oscGluedGradN`. -/
theorem memLp_seminormFluxField {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) :
    MemLp (hilbertifyVecField (fluxFieldCarrier nu S omega
      (oscGluedGradM nu hnu S P e omega) (oscGluedGradN nu hnu S P e omega))) 2
      (normalizedCubeMeasure R) :=
  memLp_fluxFieldCarrier_gluedDiff hnu S omega S.LPrime S.LPrime S.m S.n S.m
    (fluxSlot nu S.LPrime P S.n e) R

/-! ## The `Γ₂` envelope of the Hessian, and `_hPoincare` at the seminorm carrier -/

/-- **The `Γ₂` envelope of `l_w_basic_regbounds_window`, at the seminorm
carrier's field.**  The second clause of the window regbounds gives a scalar `Z` with
`‖∇²w(ω)‖_{L̲⁸(cu_m)} ≤ Z(ω)` and `Z` in `Γ₂` with the printed constant; the
`Γ₂`-moment conversion makes `|Z|³` integrable.  Everything but the constants
`C`, `Z` is the ambient telescope, so this is the input `hfin` of the Poincare
step and the domination that reduces the carrier's third moment. -/
theorem oscHessian_envelope {d : ℕ} [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∃ (C : ℝ) (Z : ShellSeq d → ℝ), 0 < C ∧ Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (C * (Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
          (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ∧
      (∀ omega : ShellSeq d, Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
        (oscHessianField hd hSorder w hw omega) ≤ ENNReal.ofReal (Z omega)) ∧
      Integrable (fun omega : ShellSeq d => |Z omega| ^ ((3 : ℕ) : ℝ)) P.toMeasure := by
  obtain ⟨C, hC1, hregw⟩ := l_w_basic_regbounds_window d hd
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  obtain ⟨Z, hZmeas, hZbigO, hZbound⟩ :=
    (hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
      (testVector nu S.LPrime P S.n e) rfl w hw).2.1
      (fun omega => oscHessianWitness hd hSorder w hw omega)
  have hq : 0 < vecNormSq (testVector nu S.LPrime P S.n e) := by
    rw [vecNormSq_testVector (d := d) hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hA : 0 < C * (Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) :=
    mul_pos hCpos (mul_pos (Real.sqrt_pos.mpr hq) (mul_pos
      (Real.sqrt_pos.mpr (by positivity)) (Real.rpow_pos_of_pos (by norm_num) _)))
  exact ⟨C, Z, hCpos, hZmeas, hZbigO, hZbound,
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZmeas.aemeasurable hZbigO 3⟩

/-- **The third moment of the Hessian field is finite.**  Read from
`oscHessian_envelope`: the `L̲⁸` norm of the Hessian is dominated by the `Γ₂`
envelope, so `∫⁻ ‖∇²w‖⁸^3` is dominated by the finite `∫⁻ |Z|³`.  This is the
finiteness input `hfin` of the seminorm-carrier Poincare step, and it carries no
hypothesis beyond the ambient telescope. -/
theorem oscHessian_lintegral_ne_top {d : ℕ} [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
      (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
        (oscHessianField hd hSorder w hw omega)) ^ (3 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
  obtain ⟨C, Z, _hC, _hZmeas, _hZbigO, hZbound, hintZ⟩ :=
    oscHessian_envelope (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  have hbound : ∀ omega : ShellSeq d,
      (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
        (oscHessianField hd hSorder w hw omega)) ^ (3 : ℕ) ≤
      ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ)) := by
    intro omega
    have hb : Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
        (oscHessianField hd hSorder w hw omega) ≤ ENNReal.ofReal |Z omega| :=
      le_trans (hZbound omega) (ENNReal.ofReal_le_ofReal (le_abs_self _))
    calc (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
          (oscHessianField hd hSorder w hw omega)) ^ (3 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (3 : ℕ) := pow_le_pow_left' hb 3
      _ = ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast]
          exact (ENNReal.ofReal_pow (abs_nonneg (Z omega)) 3).symm
  have hle : (∫⁻ omega : ShellSeq d,
      (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
        (oscHessianField hd hSorder w hw omega)) ^ (3 : ℕ) ∂P.toMeasure) ≤
      ∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ))
        ∂P.toMeasure := lintegral_mono hbound
  have hlt : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ)) ∂P.toMeasure) < ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintZ
      (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (abs_nonneg _) _)]
    exact ENNReal.ofReal_lt_top
  exact ne_of_lt (lt_of_le_of_lt hle hlt)

/-- **`_hPoincare` of the display at the seminorm carrier, constant
one.**  This is that binder at carrier `centredSeminormAt (HD omega) R` and
`Cpo = 1`: free of `S`, `nu`, `P` and every power of `3`.  Its two inputs are
discharged: `hfin` by `oscHessian_lintegral_ne_top` from the ambient telescope,
and the third-moment integrability `hintR` of the carrier, which the next lemma
reduces further. -/
theorem oscBound_hPoincare_seminorm {d : ℕ} [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hintR : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        centredSeminormAt (oscHessianWitness hd hSorder w hw omega) R ^ (3 : ℝ))
        P.toMeasure) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
            centredSeminormAt (oscHessianWitness hd hSorder w hw omega) R ^ (3 : ℝ)
            ∂P.toMeasure ≤
      1 * (∫⁻ omega : ShellSeq d,
        (Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
          (oscHessianField hd hSorder w hw omega)) ^ (3 : ℕ) ∂P.toMeasure).toReal := by
  have hfin := oscHessian_lintegral_ne_top (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4
    S hSorder he w hw
  have h := seminormCarrier_hPoincare (d := d) (P := P) S w
    (fun omega => oscHessianWitness hd hSorder w hw omega) hintR hfin
  rw [one_mul]
  exact h

/-! ## `_hCS` at the seminorm carrier, with the seminorm's own flux norm -/

/-- **The printed duality at the seminorm carrier, against the
seminorm's own flux norm, with no constant.**  The carrier is
`centredSeminormAt H R = ‖∇²v‖_{L̲²(R)}` and the flux norm is
`seminormFluxNeg`, the dual of the same centred test class; the pairing of
`∇v − (∇v)_R` with the glued flux is at most their product.  This is
`centredSeminormDuality_subcube` in real form — no comparison constant, no scale
factor: the only input is the `L²(R)` membership of the glued flux, which the
telescope supplies (`memLp_seminormFluxField`). -/
theorem oscBound_cs_seminorm {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    {m : ℕ} {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v)
    {n : ℕ} {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) (omega : ShellSeq d) :
    volumeAverage (openCubeSet R) (fun y => vecDot
        (v.grad y - volumeAverageVec (openCubeSet R) v.grad)
        (fluxFieldCarrier nu S omega
          (oscGluedGradM nu hnu S P e omega) (oscGluedGradN nu hnu S P e omega) y)) ≤
      centredSeminormAt H R * seminormFluxNeg nu hnu S P e omega R := by
  set F : Vec d → Vec d := fluxFieldCarrier nu S omega
    (oscGluedGradM nu hnu S P e omega) (oscGluedGradN nu hnu S P e omega) with hFdef
  have hFmem : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R) := by
    rw [hFdef]
    exact memLp_seminormFluxField (d := d) hnu S P e omega R
  have hB0 : 0 ≤ centredSeminormAt H R := centredSeminormAt_nonneg H R
  have hNne : centredSeminormNegNorm R F ≠ ⊤ := centredSeminormNegNorm_ne_top hFmem
  have hreal : (|volumeAverage (cubeSet R) (fun x => vecDot
      (v.grad x - volumeAverageVec (openCubeSet R) v.grad) (F x))|) ≤
      centredSeminormAt H R * (centredSeminormNegNorm R F).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNne)
      (centredSeminormDuality_subcube (n := n) (m := m) H hR hFmem)
    rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hB0] at h
  have hcube : volumeAverage (openCubeSet R) (fun x => vecDot
      (v.grad x - volumeAverageVec (openCubeSet R) v.grad) (F x)) =
      volumeAverage (cubeSet R) (fun x => vecDot
      (v.grad x - volumeAverageVec (openCubeSet R) v.grad) (F x)) :=
    (volumeAverage_cubeSet_eq_openCubeSet R _).symm
  rw [hcube]
  refine le_trans (le_abs_self _) (le_trans hreal (le_of_eq ?_))
  rw [seminormFluxNeg, hFdef]

/-! ## Both binders discharged at once -/

/-! ## The display at the seminorm carrier -/

/-- **`_hOscBound` of the term-3 statement at the seminorm carrier.**
The conclusion is the display of the term-3 statement verbatim, at its rate
`3^{-(\ell'-n)/2}`, at a `CB` fixed before the scale selection:
`CB = max 1 (oscBoundConstBase 1 C C3)` with `C` the
`l_w_basic_regbounds_window` constant (a function of `d` and `hd` only) and `C3`
a parameter.  `CB` mentions neither `S`, nor `nu`, nor `P`, nor any power of
`3`.

The assembly re-instantiates the carrier-agnostic engine `osc_bound_bridge` at
the seminorm carrier `centredSeminormAt` and at the seminorm flux norm
`seminormFluxNeg`, with `_hCS := oscBound_cs_seminorm` (no constant), `_hPoincare :=
oscBound_hPoincare_seminorm` (constant one) and `_hXint := hXint_discharged`.

What remains as hypotheses: `_hFlux` at `seminormFluxNeg` (the printed flux
chain, with its printed `3^{3n/2}` intact and no scale factor on the norm),
`_hEnergy`, and the two sample-side memberships `_hMemOsc` (at the seminorm
carrier) and `_hMemFlux` (at `seminormFluxNeg`). -/
theorem term3_oscBound_seminorm (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C3 : ℝ) (hC3 : 0 ≤ C3) :
    ∃ CB : ℝ, 1 ≤ CB ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (e : Vec d) (_he : vecNormSq e = 1)
        (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
              seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)
              ∂P.toMeasure ≤
            C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
              (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
              (∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^
                ((3 : ℝ) / 4))
        (_hEnergy : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              ∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure ≤
          delta + etaL)
        (_hMemOsc : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          MemLp (fun omega : ShellSeq d =>
            centredSeminormAt (oscHessianWitness hd _hSorder w _hw omega) R)
            (ENNReal.ofReal (3 : ℝ)) P.toMeasure)
        (_hMemFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          MemLp (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R)
            (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure),
        ∫ omega : ShellSeq d,
            ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d S.n S.m,
                volumeAverage (openCubeSet R)
                  (fun y => vecDot ((w omega).toH1Function.grad y -
                      volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.m S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y)))
            ∂P.toMeasure ≤
          CB * nu ^ (-(3 / 2 : ℝ)) * (delta + etaL) ^ ((1 : ℝ) / 2) *
            ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) := by
  obtain ⟨C, hC1, hregw⟩ := l_w_basic_regbounds_window d hd
  refine ⟨max 1 (oscBoundConstBase 1 C C3), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hWindowVsOffset e he
    delta etaL hdelta hetaL w hw hFlux hEnergy hMemOsc hMemFlux
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  obtain ⟨Z, hZmeas, hZbigO, hZbound⟩ :=
    (hregw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
      (testVector nu S.LPrime P S.n e) rfl w hw).2.1
      (fun omega => oscHessianWitness hd hSorder w hw omega)
  have hPoinOne := oscBound_hPoincare_seminorm (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4
    S hSorder he w hw
    (memLp_imp_seminormThirdInt (n := S.n) (m := S.m)
      (fun omega => oscHessianWitness hd hSorder w hw omega) hMemOsc)
  have hCS : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      volumeAverage (openCubeSet R)
          (fun y => vecDot ((w omega).toH1Function.grad y -
              volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y))) ≤
        centredSeminormAt (oscHessianWitness hd hSorder w hw omega) R *
          seminormFluxNeg nu hnu S P e omega R :=
    fun omega R hR => oscBound_cs_seminorm (d := d) (R := R) hnu S P e
      (oscHessianWitness hd hSorder w hw omega) hR omega
  have hOFint : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        centredSeminormAt (oscHessianWitness hd hSorder w hw omega) R *
          seminormFluxNeg nu hnu S P e omega R) P.toMeasure :=
    oscSideCondition_hOFint (P := P) (n := S.n) (m := S.m)
      (fun omega R => centredSeminormAt (oscHessianWitness hd hSorder w hw omega) R)
      (fun omega R => seminormFluxNeg nu hnu S P e omega R)
      hMemOsc hMemFlux
  have hbridge := osc_bound_bridge hnu hnu1 hPrefix hJ2 hJ3 hJ4 hSorder he rfl w
    (fun omega y => gluedGradientField hnu S.LPrime S.m S.m
      (fluxSlot nu S.LPrime P S.n e) omega y)
    (fun omega y => gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega y)
    (oscHessianField hd hSorder w hw)
    (fun omega R => centredSeminormAt (oscHessianWitness hd hSorder w hw omega) R)
    (seminormFluxNeg nu hnu S P e)
    (fun omega R => oscEnergy nu hnu S P e omega R)
    hCpos (by norm_num : (0 : ℝ) ≤ 1) hC3 (add_nonneg hdelta hetaL)
    (fun omega R => centredSeminormAt_nonneg (oscHessianWitness hd hSorder w hw omega) R)
    (fun omega R => seminormFluxNeg_nonneg nu hnu S P e omega R)
    (fun omega R => oscEnergy_nonneg hnu S P e omega R)
    hCS hZmeas hZbigO hZbound hPoinOne hFlux hEnergy
    (hXint_discharged hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw)
    hOFint hMemOsc hMemFlux
  exact oscBoundConst_productForm_le (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hCpos) hC3
    hWindowVsOffset (by positivity) (by positivity) (by positivity) hbridge

/-! ## The carrier's third moment from measurability and the envelope -/

/-- **The third moment of the seminorm carrier is integrable as soon as the
carrier is a.e. strongly measurable.**  The constant-one tiling bound
`centredSeminormAt_avsum_le_hessCubeEight` gives, term by term, the per-cube
domination by the `Γ₂` envelope `Z`; with `|Z|³` integrable this makes the
third power of every `centredSeminormAt (HD omega) R` integrable.  This replaces
the `L³(P)` membership `_hMemOsc` of the display by the weaker pair (a.e. strong
measurability, this lemma); the measurability of the `Classical.choice`
weak-Hessian family is the one remaining measurability hypothesis. -/
theorem integrable_seminormThird_of_envelope {d : ℕ} [NeZero d] {n m : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)}
    {v : ShellSeq d → H1Function (openCubeSet (originCube d (m : ℤ)))}
    (HD : (omega : ShellSeq d) →
      HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) (v omega))
    {Z : ShellSeq d → ℝ}
    (hZbound : ∀ omega : ShellSeq d, Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 8
      (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) ≤ ENNReal.ofReal (Z omega))
    (hZint : Integrable (fun omega : ShellSeq d => |Z omega| ^ ((3 : ℕ) : ℝ)) P.toMeasure)
    (hmeas : ∀ R ∈ largeCubeSubcubes d n m,
      AEStronglyMeasurable (fun omega : ShellSeq d => centredSeminormAt (HD omega) R)
        P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d n m,
      Integrable (fun omega : ShellSeq d => centredSeminormAt (HD omega) R ^ (3 : ℝ))
        P.toMeasure := by
  intro R hR
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d n m).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨R, hR⟩)
  have hdom : ∀ omega : ShellSeq d,
      centredSeminormAt (HD omega) R ^ (3 : ℕ) ≤
        ((largeCubeSubcubes d n m).card : ℝ) * |Z omega| ^ ((3 : ℕ) : ℝ) := by
    intro omega
    have ha := centredSeminormAt_avsum_le_hessCubeEight (d := d) (n := n) (m := m)
      (v := v omega) (HD omega)
    have hterm : (ENNReal.ofReal (centredSeminormAt (HD omega) R)) ^ (3 : ℕ) ≤
        ∑ R' ∈ largeCubeSubcubes d n m,
          (ENNReal.ofReal (centredSeminormAt (HD omega) R')) ^ (3 : ℕ) :=
      Finset.single_le_sum
        (f := fun R' => (ENNReal.ofReal (centredSeminormAt (HD omega) R')) ^ (3 : ℕ))
        (fun R' _ => by positivity) hR
    have hstep : ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)⁻¹) *
        (ENNReal.ofReal (centredSeminormAt (HD omega) R)) ^ (3 : ℕ) ≤
        (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ) :=
      le_trans (mul_le_mul le_rfl hterm (by positivity) (by positivity)) ha
    have hZabs : Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) ≤
        ENNReal.ofReal |Z omega| :=
      le_trans (hZbound omega) (ENNReal.ofReal_le_ofReal (le_abs_self _))
    have hZcube : (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ)) := by
      calc (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (3 : ℕ)
          ≤ (ENNReal.ofReal |Z omega|) ^ (3 : ℕ) := pow_le_pow_left' hZabs 3
        _ = ENNReal.ofReal (|Z omega| ^ (3 : ℕ)) :=
            (ENNReal.ofReal_pow (abs_nonneg (Z omega)) 3).symm
        _ = ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ)) := by rw [Real.rpow_natCast]
    have hkey : ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        centredSeminormAt (HD omega) R ^ (3 : ℕ)) ≤
        ENNReal.ofReal (|Z omega| ^ ((3 : ℕ) : ℝ)) := by
      refine le_trans ?_ (le_trans hstep hZcube)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow
        (centredSeminormAt_nonneg (HD omega) R) 3]
    have hreal : ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        centredSeminormAt (HD omega) R ^ (3 : ℕ) ≤ |Z omega| ^ ((3 : ℕ) : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hkey
    have hmul : ((largeCubeSubcubes d n m).card : ℝ) *
        (((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
          centredSeminormAt (HD omega) R ^ (3 : ℕ)) =
        centredSeminormAt (HD omega) R ^ (3 : ℕ) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcardpos), one_mul]
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left hreal (le_of_lt hcardpos)
  have hIntNat : Integrable (fun omega : ShellSeq d =>
      centredSeminormAt (HD omega) R ^ (3 : ℕ)) P.toMeasure := by
    refine (hZint.const_mul ((largeCubeSubcubes d n m).card : ℝ)).mono'
      ((hmeas R hR).pow 3) (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (centredSeminormAt_nonneg (HD omega) R) 3)]
    exact hdom omega
  simpa only [Real.rpow_ofNat] using hIntNat

/-- **The display at the seminorm carrier, with the two memberships
reduced to measurability.**  Same conclusion as `term3_oscBound_seminorm` at the
same `CB`, but the sample-side `MemLp` binders `_hMemOsc`, `_hMemFlux` are
replaced by the strictly weaker data: the per-cube a.e. strong
measurability of the carrier and of the flux norm, the integrability of the flux
norm's `3/2` power, and nothing else.  The carrier's third-moment integrability
is derived here from the `Γ₂` envelope of `oscHessian_envelope` by
`integrable_seminormThird_of_envelope`, and both `L^q` memberships from their
measurability and power-integrability by `memLp_ofReal_of_integrable_rpow`.  So
what remains of `_hMemOsc` is a single measurability statement, and of
`_hMemFlux` a measurability statement plus a `3/2`-moment bound. -/
theorem term3_oscBound_seminorm_measurable (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C3 : ℝ) (hC3 : 0 ≤ C3) :
    ∃ CB : ℝ, 1 ≤ CB ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (e : Vec d) (_he : vecNormSq e = 1)
        (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d,
              seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)
              ∂P.toMeasure ≤
            C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
              (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
              (∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^
                ((3 : ℝ) / 4))
        (_hEnergy : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              ∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure ≤
          delta + etaL)
        (_hAEMOsc : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          AEStronglyMeasurable (fun omega : ShellSeq d =>
            centredSeminormAt (oscHessianWitness hd _hSorder w _hw omega) R)
            P.toMeasure)
        (_hAEMFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          AEStronglyMeasurable (fun omega : ShellSeq d =>
            seminormFluxNeg nu hnu S P e omega R) P.toMeasure)
        (_hIntFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
          Integrable (fun omega : ShellSeq d =>
            seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)) P.toMeasure),
        ∫ omega : ShellSeq d,
            ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d S.n S.m,
                volumeAverage (openCubeSet R)
                  (fun y => vecDot ((w omega).toH1Function.grad y -
                      volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.m S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y)))
            ∂P.toMeasure ≤
          CB * nu ^ (-(3 / 2 : ℝ)) * (delta + etaL) ^ ((1 : ℝ) / 2) *
            ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) := by
  obtain ⟨CB, hCB1, hCB⟩ := term3_oscBound_seminorm d hd C3 hC3
  refine ⟨CB, hCB1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hWindowVsOffset e he
    delta etaL hdelta hetaL w hw hFlux hEnergy hAEMOsc hAEMFlux hIntFlux
  obtain ⟨_C, Z, _hCpos, _hZmeas, _hZbigO, hZbound, hZint⟩ :=
    oscHessian_envelope (d := d) hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  have hIntOsc := integrable_seminormThird_of_envelope (n := S.n) (m := S.m) (P := P)
    (v := fun omega => (w omega).toH1Function)
    (fun omega => oscHessianWitness hd hSorder w hw omega) hZbound hZint hAEMOsc
  refine hCB nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hWindowVsOffset e he
    delta etaL hdelta hetaL w hw hFlux hEnergy ?_ ?_
  · exact fun R hR => memLp_ofReal_of_integrable_rpow (q := 3) (by norm_num)
      (fun omega => centredSeminormAt_nonneg (oscHessianWitness hd hSorder w hw omega) R)
      (hAEMOsc R hR) (hIntOsc R hR)
  · exact fun R hR => memLp_ofReal_of_integrable_rpow (q := (3 : ℝ) / 2) (by norm_num)
      (fun omega => seminormFluxNeg_nonneg nu hnu S P e omega R)
      (hAEMFlux R hR) (hIntFlux R hR)

end

end SuperdiffusionCLT.Section3.Terms
