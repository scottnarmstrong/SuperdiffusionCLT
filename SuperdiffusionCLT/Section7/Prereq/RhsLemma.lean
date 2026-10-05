/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationD
public import SuperdiffusionCLT.Section7.Analytic.CZ.CubePerturb
public import SuperdiffusionCLT.Section2.Norms.CubeLp

/-!
# The energy estimate for equations with a right-hand side

For a field `a` whose symmetric part is `ν Id` on a cube `□`, and `w ∈ H¹₀(□)` with
`-∇·(a∇w) = f` weakly, testing with `w` (the skew part of `a` drops out of the quadratic form) and
combining Hölder with the Sobolev inequality at `2^*` gives
`ν ‖∇w‖_{L̲²(□)} ≤ C 3^n ‖f‖_{L̲^{2_*}(□)}`, where `2_* = (2^*)'`.

## Main results

* `Section7.r1_energy_axis`: the unnormalized estimate on an axis cube.
* `Section7.r1_cubeLp_eq`: the normalized norm of a cube against the plain norm of the open cube.
* `Section7.r1_energy_cube`: the normalized estimate on a triadic cube.
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The quadratic form of a field whose symmetric part is `ν Id`. -/
theorem r1_matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem r1_quad_symm {A : Mat d} {nu : ℝ} (hA : symmPart A = nu • (1 : Mat d)) (ξ : Vec d) :
    vecDot (matVecMul A ξ) ξ = nu * vecNormSq ξ := by
  rw [vecDot_comm, ← vecDot_matVecMul_symmPart, hA, smul_matVecMul, r1_matVecMul_one,
    vecDot_smul_right]
  rfl

/-- The energy identity for a weak solution tested with itself. -/
theorem r1_energy_identity {U : Set (Vec d)} (hU : MeasurableSet U) {nu : ℝ} {a : CoeffField d}
    (hsym : ∀ x ∈ U, symmPart (a x) = nu • (1 : Mat d)) (w : H10Function U) (f : Vec d → ℝ)
    (hw : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) =
        ∫ x in U, f x * φ.toH1Function.toFun x) :
    nu * ∫ x in U, vecNormSq (w.toH1Function.grad x) = ∫ x in U, f x * w.toH1Function.toFun x := by
  rw [← hw w, ← integral_const_mul]
  exact (setIntegral_congr_fun hU fun x hx => r1_quad_symm (hsym x hx) _).symm


/-- The Hölder conjugate exponent `2_*` of the Sobolev exponent `2^*`. -/
theorem r1_holder_triple (hd : 2 ≤ d) :
    ENNReal.HolderTriple (ENNReal.ofReal (sobStar d)).conjExponent
      (ENNReal.ofReal (sobStar d)) 1 := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [two_lt_sobStar hd])
  have := (ENNReal.HolderConjugate.conjExponent h1).symm
  exact this

/-- Energy estimate on an axis cube, unnormalized. -/
theorem r1_energy_axis (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ {nu : ℝ}, 0 < nu →
      ∀ {a : CoeffField d}, (∀ x ∈ axisCube z L, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ (w : H10Function (axisCube z L)) (f : Vec d → ℝ),
      (∀ φ : H10Function (axisCube z L),
        ∫ x in axisCube z L, vecDot (matVecMul (a x) (w.toH1Function.grad x))
            (φ.toH1Function.grad x) =
          ∫ x in axisCube z L, f x * φ.toH1Function.toFun x) →
      ENNReal.ofReal nu * eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2
          (volume.restrict (axisCube z L)) ≤
        ENNReal.ofReal (C * L ^ ((d : ℝ) / sobStar d + (1 - (d : ℝ) / 2))) *
          eLpNorm f (ENNReal.ofReal (sobStar d)).conjExponent (volume.restrict (axisCube z L)) := by
  obtain ⟨C0, hC0, hS⟩ := cube_sobolev_sobStar hd
  refine ⟨C0, hC0, fun z L hL nu hnu a hsym w f hw => ?_⟩
  have hp : 2 < sobStar d := two_lt_sobStar hd
  have hp0 : 0 < sobStar d := by linarith only [hp]
  have hQm : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  set μ : Measure (Vec d) := volume.restrict (axisCube z L) with hμ
  set p := sobStar d with hpdef
  have htrip := r1_holder_triple hd
  set E := eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ with hE
  set F := eLpNorm f (ENNReal.ofReal p).conjExponent μ with hF
  set W := eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) μ with hW
  have hEtop : E ≠ ⊤ := (memLp_eucNorm_grad w.toH1Function).eLpNorm_ne_top
  -- Sobolev
  have hSob := hS z L hL w
  have hWE : W ≤ ENNReal.ofReal (L ^ ((d : ℝ) / p) * (C0 * L ^ (1 - (d : ℝ) / 2))) * E := by
    have e1 : ENNReal.ofReal (L ^ ((d : ℝ) / p)) * ENNReal.ofReal (L ^ (-(d : ℝ) / p)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hL]
      have : (d : ℝ) / p + -(d : ℝ) / p = 0 := by ring
      rw [this]; simp
    calc W = ENNReal.ofReal (L ^ ((d : ℝ) / p)) * (ENNReal.ofReal (L ^ (-(d : ℝ) / p)) * W) := by
          rw [← mul_assoc, e1, one_mul]
      _ ≤ ENNReal.ofReal (L ^ ((d : ℝ) / p)) * (ENNReal.ofReal (C0 * L ^ (1 - (d : ℝ) / 2)) * E) :=
          mul_le_mul_right hSob _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- energy identity and Hölder
  have hid := r1_energy_identity hQm hsym w f hw
  have hEsq : ENNReal.ofReal (∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x)) = E ^ 2 := by
    have h1 : E.toReal ^ 2 = ∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x) := by
      rw [hE, eLpNorm_two_toReal_sq (memLp_eucNorm_grad w.toH1Function),
        integral_eucNorm_grad_sq w.toH1Function]
    rw [← h1, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hEtop]
  have hI : ENNReal.ofReal nu * E ^ 2 ≤ F * W := by
    have h0 : 0 ≤ ∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x) :=
      integral_nonneg fun x => vecNormSq_nonneg _
    have hcalc : ENNReal.ofReal nu * E ^ 2 =
        ‖∫ x in axisCube z L, f x * w.toH1Function.toFun x‖ₑ := by
      rw [← hid, ← hEsq, ← ENNReal.ofReal_mul hnu.le, Real.enorm_of_nonneg (by positivity)]
    rw [hcalc]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_enorm_le_eLpNorm_one.trans ?_
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm_of_pos (μ := μ) (p := (ENNReal.ofReal p).conjExponent)
      (q := ENNReal.ofReal p) (r := 1) (f := f) (g := w.toH1Function.toFun)
      (fun x y : ℝ => x * y) 1 (by fun_prop) (Filter.Eventually.of_forall fun x => by simp)
      one_pos
    simpa using this
  by_cases hE0 : E = 0
  · rw [hE0]; simp
  · have h2 : E * (ENNReal.ofReal nu * E) ≤
        E * (F * ENNReal.ofReal (L ^ ((d : ℝ) / p) * (C0 * L ^ (1 - (d : ℝ) / 2)))) := by
      calc E * (ENNReal.ofReal nu * E) = ENNReal.ofReal nu * E ^ 2 := by ring
        _ ≤ F * W := hI
        _ ≤ F * (ENNReal.ofReal (L ^ ((d : ℝ) / p) * (C0 * L ^ (1 - (d : ℝ) / 2))) * E) :=
          mul_le_mul_right hWE _
        _ = _ := by ring
    have h3 := (ENNReal.mul_le_mul_iff_right hE0 hEtop).1 h2
    calc ENNReal.ofReal nu * E ≤ F * ENNReal.ofReal (L ^ ((d : ℝ) / p) * (C0 * L ^ (1 - (d : ℝ) / 2))) := h3
      _ = _ := by
        rw [mul_comm]
        congr 2
        rw [Real.rpow_add hL]
        ring


theorem r1_scaleFactor_pos (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

/-- The normalized `L^p` norm of a cube against the plain `L^p` norm of the open cube. -/
theorem r1_cubeLp_eq (Q : TriadicCube d) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {E : Type*}
    [NormedAddCommGroup E] (g : Vec d → E) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q p g =
      ENNReal.ofReal (cubeScaleFactor Q ^ (-((d : ℝ) / p.toReal))) *
        eLpNorm g p (volume.restrict (openCubeSet Q)) := by
  have hL := r1_scaleFactor_pos Q
  unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
  rw [normalizedCubeMeasure_eq_smul, eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hpt,
    smul_eq_mul]
  congr 1
  have h1 : (1 / p).toReal = 1 / p.toReal := by simp
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [h1, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 (by unfold cubeVolume; positivity))
    (by positivity)]
  congr 1
  unfold cubeVolume
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le,
    ← Real.rpow_neg hL.le]
  congr 1
  ring

theorem r1_conj_real (hd : 2 ≤ d) :
    ((ENNReal.ofReal (sobStar d)).conjExponent.toReal)⁻¹ + (sobStar d)⁻¹ = 1 := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [two_lt_sobStar hd])
  have := (ENNReal.HolderConjugate.conjExponent hq1).symm
  have hq0 : 0 < sobStar d := by linarith only [two_lt_sobStar hd]
  have h := ENNReal.HolderConjugate.inv_add_inv_eq_one (ENNReal.ofReal (sobStar d)).conjExponent
    (ENNReal.ofReal (sobStar d))
  have hp0 := ENNReal.HolderConjugate.ne_zero (ENNReal.ofReal (sobStar d)).conjExponent
    (ENNReal.ofReal (sobStar d))
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp0)
    (ENNReal.inv_ne_top.2 (by simpa using hq0)), ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hq0.le] at h2
  simpa using h2

theorem r1_conj_ne_top (hd : 2 ≤ d) : (ENNReal.ofReal (sobStar d)).conjExponent ≠ ⊤ := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [two_lt_sobStar hd])
  have := (ENNReal.HolderConjugate.conjExponent hq1).symm
  rw [ENNReal.HolderConjugate.ne_top_iff_ne_one (ENNReal.ofReal (sobStar d)).conjExponent
    (ENNReal.ofReal (sobStar d))]
  intro h
  have : sobStar d = 1 := by
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_ofReal (by linarith only [two_lt_sobStar hd]), ENNReal.toReal_one] at this
  linarith only [two_lt_sobStar hd, this]


/-- **Energy estimate on a cube, normalized.**  A weak solution `w ∈ H¹₀(□)` of
`-∇·(a∇w) = f` for a field with symmetric part `ν Id` satisfies
`ν ‖∇w‖_{L̲²(□)} ≤ C 3^n ‖f‖_{L̲^{2_*}(□)}`. -/
theorem r1_energy_cube (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d) {nu : ℝ}, 0 < nu →
      ∀ {a : CoeffField d}, (∀ x ∈ openCubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ (w : H10Function (openCubeSet Q)) (f : Vec d → ℝ),
      (∀ φ : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot (matVecMul (a x) (w.toH1Function.grad x))
            (φ.toH1Function.grad x) =
          ∫ x in openCubeSet Q, f x * φ.toH1Function.toFun x) →
      ENNReal.ofReal nu * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (w.toH1Function.grad x))) ≤
        ENNReal.ofReal (C * cubeScaleFactor Q) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
            (ENNReal.ofReal (sobStar d)).conjExponent f := by
  obtain ⟨C0, hC0, hE⟩ := r1_energy_axis hd
  refine ⟨C0, hC0, fun Q nu hnu a hsym w f hw => ?_⟩
  have hL := r1_scaleFactor_pos Q
  have key : ∀ U : Set (Vec d), U = axisCube (CubeCalderonZygmund.triadicCubeAxisCorner Q) (cubeScaleFactor Q) →
      (∀ x ∈ U, symmPart (a x) = nu • (1 : Mat d)) → ∀ (w : H10Function U),
      (∀ φ : H10Function U,
        ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) =
          ∫ x in U, f x * φ.toH1Function.toFun x) →
      ENNReal.ofReal nu * eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2
          (volume.restrict U) ≤
        ENNReal.ofReal (C0 * cubeScaleFactor Q ^ ((d : ℝ) / sobStar d + (1 - (d : ℝ) / 2))) *
          eLpNorm f (ENNReal.ofReal (sobStar d)).conjExponent (volume.restrict U) := by
    intro U hU
    subst hU
    exact fun hs w hw => hE _ _ hL hnu hs w f hw
  have h1 := key _ (CubeCalderonZygmund.openCubeSet_eq_axisCube_triadicCube Q) hsym w hw
  have hq0 : 0 < sobStar d := by linarith only [two_lt_sobStar hd]
  have hpt := r1_conj_ne_top hd
  have hp0 : (ENNReal.ofReal (sobStar d)).conjExponent ≠ 0 := by
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (sobStar d) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith only [two_lt_sobStar hd])
    have := (ENNReal.HolderConjugate.conjExponent hq1).symm
    exact ENNReal.HolderConjugate.ne_zero _ (ENNReal.ofReal (sobStar d))
  rw [r1_cubeLp_eq Q (by norm_num) (by norm_num), r1_cubeLp_eq Q hp0 hpt]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  set pr := (ENNReal.ofReal (sobStar d)).conjExponent.toReal with hpr
  have hconj := r1_conj_real hd
  rw [← hpr] at hconj
  have hd2 : (d : ℝ) / pr = d - d / sobStar d := by
    have : pr⁻¹ = 1 - (sobStar d)⁻¹ := by linarith only [hconj]
    rw [div_eq_mul_inv, this, div_eq_mul_inv]
    ring
  have hrw : ENNReal.ofReal nu * (ENNReal.ofReal (cubeScaleFactor Q ^ (-((d : ℝ) / 2))) *
        eLpNorm (fun x => Real.sqrt (vecNormSq (w.toH1Function.grad x))) 2
          (volume.restrict (openCubeSet Q))) =
      ENNReal.ofReal (cubeScaleFactor Q ^ (-((d : ℝ) / 2))) * (ENNReal.ofReal nu *
        eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 (volume.restrict (openCubeSet Q))) := by
    unfold eucNorm
    ring
  rw [hrw]
  calc ENNReal.ofReal (cubeScaleFactor Q ^ (-((d : ℝ) / 2))) * (ENNReal.ofReal nu *
        eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 (volume.restrict (openCubeSet Q)))
      ≤ ENNReal.ofReal (cubeScaleFactor Q ^ (-((d : ℝ) / 2))) *
        (ENNReal.ofReal (C0 * cubeScaleFactor Q ^ ((d : ℝ) / sobStar d + (1 - (d : ℝ) / 2))) *
          eLpNorm f (ENNReal.ofReal (sobStar d)).conjExponent
            (volume.restrict (openCubeSet Q))) := mul_le_mul_right h1 _
    _ = ENNReal.ofReal (C0 * cubeScaleFactor Q) * (ENNReal.ofReal
          (cubeScaleFactor Q ^ (-((d : ℝ) / pr))) *
          eLpNorm f (ENNReal.ofReal (sobStar d)).conjExponent
            (volume.restrict (openCubeSet Q))) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have e1 : cubeScaleFactor Q ^ (-((d : ℝ) / 2)) *
            (C0 * cubeScaleFactor Q ^ ((d : ℝ) / sobStar d + (1 - (d : ℝ) / 2))) =
            C0 * (cubeScaleFactor Q ^ (-((d : ℝ) / 2)) *
              cubeScaleFactor Q ^ ((d : ℝ) / sobStar d + (1 - (d : ℝ) / 2))) := by ring
        have e2 : C0 * cubeScaleFactor Q * cubeScaleFactor Q ^ (-((d : ℝ) / pr)) =
            C0 * (cubeScaleFactor Q ^ (1 : ℝ) * cubeScaleFactor Q ^ (-((d : ℝ) / pr))) := by
          rw [Real.rpow_one]; ring
        rw [e1, e2, ← Real.rpow_add hL, ← Real.rpow_add hL]
        congr 2
        rw [hd2]
        ring

end SuperdiffusionCLT.Section7
