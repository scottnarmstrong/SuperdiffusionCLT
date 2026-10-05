/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.MollifierB

/-!
# The elementary mollifier estimate

The elementary mollifier estimate of the paper:
`‖η ∗ F‖_{L^∞(z + cu_n)} ≤ C 3^{-n/4} ‖F‖_{H̲^{-1/4}(z + cu_{n+1})}`.

The negative norm is the scale-normalized genuine dual Besov norm of order `1/4` of
CoarseGraining (`scaleNormalizedDualNegativeBesovVectorNormTwo`), the one carried by the weak flux
and weak gradient conclusions of the sharp scale inputs.  The scalar estimate is the duality
bound of `y ↦ η_h (x - y)`; the vector estimate sums over components.  Here `h = 3^n` and the cube
has side `3h = 3^{n+1}`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section7

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The mollification `η_h ∗ F` of a vector field, componentwise, evaluated at `x`. -/
def a16_mollify (d : ℕ) (h : ℝ) (η : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d) : Vec d :=
  fun i => ∫ y, a16_kernel d h η (x - y) * F y i

/-- The scalar mollifier estimate. -/
theorem a16_scalar_mollifier_le (Q : TriadicCube d) {h : ℝ} (hh : 0 < h)
    (hc : cubeScaleFactor Q = 3 * h) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : ∀ y, dist y x ≤ h → y ∈ cubeSet Q) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    |∫ y, a16_kernel d h η (x - y) * f y| ≤
      3 ^ d * (6 * (L : ℝ) + A) * (3 * h) ^ (-(1 / 4 : ℝ)) *
        cubeBesovDualFullNorm Q (1 / 4) 2 2 f := by
  set g : Vec d → ℝ := fun y => a16_kernel d h η (x - y) with hg
  have hcpos : 0 < 3 * h := by positivity
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
  have hhd : 0 ≤ (h⁻¹) ^ d := pow_nonneg (inv_nonneg.mpr hh.le) d
  have hgc : Continuous g :=
    (a16_kernel_continuous hL.continuous).comp (continuous_const.sub continuous_id)
  have hmeas : Measurable g := hgc.measurable
  have hM : ∀ y, |g y| ≤ A * (h⁻¹) ^ d := fun y => a16_kernel_abs_le hh hA _
  set K : ℝ := (L : ℝ) * (h⁻¹) ^ d * h⁻¹ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; positivity
  have hLip : ∀ y y', |g y - g y'| ≤ K * dist y y' := by
    intro y y'
    have := a16_kernel_dist_le hh hL (x - y) (x - y')
    rw [dist_sub_left] at this
    calc |g y - g y'| ≤ _ := this
      _ = K * dist y y' := by rw [hK]; ring
  have hnorm := a16_testNorm_le Q hmeas hK0 hM hLip
  have hmem := a16_localMemLp Q hmeas hM
  rw [hc] at hnorm
  have hB0 : 2 * (K * (3 * h) ^ (3 / 4 : ℝ)) + (3 * h) ^ (-(1 / 4 : ℝ)) * (A * (h⁻¹) ^ d) =
      (3 * h) ^ (-(1 / 4 : ℝ)) * ((h⁻¹) ^ d * (6 * (L : ℝ) + A)) := by
    have : (3 * h) ^ (3 / 4 : ℝ) = (3 * h) ^ (-(1 / 4 : ℝ)) * (3 * h) := by
      rw [← Real.rpow_add_one hcpos.ne']
      norm_num
    rw [this, hK]
    field_simp
    ring
  rw [hB0] at hnorm
  have hBnn : 0 ≤ (3 * h) ^ (-(1 / 4 : ℝ)) * ((h⁻¹) ^ d * (6 * (L : ℝ) + A)) := by
    have : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    positivity
  have hpair :=
    Book.Ch01.Legacy.abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two_of_nonneg
      Q (1 / 4) f g (by norm_num) hf hBnn (fun N => by rw [← hc] at hnorm ⊢; exact hnorm N) hmem
  have hsupp : ∀ y, y ∉ cubeSet Q → g y * f y = 0 := by
    intro y hy
    have hgy : g y = 0 := by
      by_contra hne
      refine hy (hx y ?_)
      rw [dist_pi_le_iff hh.le]
      intro i
      by_contra hlt
      push Not at hlt
      apply hne
      refine a16_kernel_eq_zero hh hη (w := x - y) (i := i) ?_
      rw [Real.dist_eq] at hlt
      simpa only [Pi.sub_apply, abs_sub_comm] using hlt
    rw [hgy, zero_mul]
  have hint : ∫ y, g y * f y = ∫ y in cubeSet Q, g y * f y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hpr : cubeBesovPairing Q f g = (cubeVolume Q)⁻¹ * ∫ y in cubeSet Q, g y * f y := by
    unfold cubeBesovPairing cubeAverage
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hI : ∫ y, g y * f y = cubeVolume Q * cubeBesovPairing Q f g := by
    rw [hint, hpr, ← mul_assoc, mul_inv_cancel₀ hvol.ne', one_mul]
  show |∫ y, g y * f y| ≤ _
  rw [hI, abs_mul, abs_of_pos hvol]
  have hvolc : cubeVolume Q = (3 * h) ^ d := by
    rw [cubeVolume_eq_scaleFactor_pow, hc]
  have hhh : (3 * h) ^ d * (h⁻¹) ^ d = 3 ^ d := by
    rw [← mul_pow, mul_assoc, mul_inv_cancel₀ hh.ne', mul_one]
  calc cubeVolume Q * |cubeBesovPairing Q f g|
      ≤ cubeVolume Q * (cubeBesovDualFullNorm Q (1 / 4) 2 2 f *
        ((3 * h) ^ (-(1 / 4 : ℝ)) * ((h⁻¹) ^ d * (6 * (L : ℝ) + A)))) :=
        mul_le_mul_of_nonneg_left hpair hvol.le
    _ = ((3 * h) ^ d * (h⁻¹) ^ d) * (6 * (L : ℝ) + A) * (3 * h) ^ (-(1 / 4 : ℝ)) *
        cubeBesovDualFullNorm Q (1 / 4) 2 2 f := by
      rw [hvolc]; ring
    _ = _ := by rw [hhh]

/-- The scale-normalization factor of the vector dual norm is `(3h)^{-1/4}`. -/
theorem a16_scale_factor_eq (Q : TriadicCube d) :
    Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * ((Q.scale : ℤ) : ℝ)) =
      cubeScaleFactor Q ^ (-(1 / 4 : ℝ)) := by
  unfold cubeScaleFactor
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  show (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((Q.scale : ℤ) : ℝ)) = (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) * (-(1 / 4 : ℝ)))
  rw [mul_comm]

/-- The elementary mollifier estimate for a vector field, componentwise: the mollification at
`x` is bounded by the scale-normalized dual negative Besov norm of order `1/4` on the cube of side
`3h`, which contains the sup-ball of radius `h` around `x`. -/
theorem mollifier_apply_le_dualNegativeBesov (Q : TriadicCube d) {h : ℝ} (hh : 0 < h)
    (hc : cubeScaleFactor Q = 3 * h) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : ∀ y, dist y x ≤ h → y ∈ cubeSet Q) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) (i : Fin d) :
    |a16_mollify d h η F x i| ≤ 3 ^ d * (6 * (L : ℝ) + A) *
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hnn : ∀ j : Fin d, 0 ≤ cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun y => F y j) := fun j =>
    cubeBesovDualFullNorm_nonneg Q _ _ _ _ (by rw [hconj]; norm_num) (by rw [hconj]; norm_num)
  have h1 := a16_scalar_mollifier_le Q hh hc hA hL hη hx (hF i)
  have hi : cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun y => F y i) ≤
      ∑ j : Fin d, cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun y => F y j) :=
    Finset.single_le_sum (f := fun j => cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun y => F y j))
      (fun j _ => hnn j) (Finset.mem_univ i)
  have hC : 0 ≤ (3 : ℝ) ^ d * (6 * (L : ℝ) + A) := by
    have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
    have : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    positivity
  unfold Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
  rw [a16_scale_factor_eq, hc]
  show |∫ y, a16_kernel d h η (x - y) * F y i| ≤ _
  calc _ ≤ _ := h1
    _ = 3 ^ d * (6 * (L : ℝ) + A) * ((3 * h) ^ (-(1 / 4 : ℝ)) *
        cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun y => F y i)) := by ring
    _ ≤ 3 ^ d * (6 * (L : ℝ) + A) * ((3 * h) ^ (-(1 / 4 : ℝ)) *
        ∑ j : Fin d, cubeBesovDualFullNorm Q (1 / 4) 2 2 (fun y => F y j)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (by positivity) _)) hC

/-- The same estimate for the sup norm of the vector `η_h ∗ F (x)`. -/
theorem mollifier_norm_le_dualNegativeBesov (Q : TriadicCube d) {h : ℝ} (hh : 0 < h)
    (hc : cubeScaleFactor Q = 3 * h) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {x : Vec d}
    (hx : ∀ y, dist y x ≤ h → y ∈ cubeSet Q) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) :
    ‖a16_mollify d h η F x‖ ≤ 3 ^ d * (6 * (L : ℝ) + A) *
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hN : 0 ≤ Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F := by
    unfold Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Finset.sum_nonneg fun j _ =>
      cubeBesovDualFullNorm_nonneg Q _ _ _ _ (by rw [hconj]; norm_num) (by rw [hconj]; norm_num))
  have hnn : 0 ≤ 3 ^ d * (6 * (L : ℝ) + A) *
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F := by
    positivity
  exact (pi_norm_le_iff_of_nonneg hnn).2 fun i => by
    rw [Real.norm_eq_abs]
    exact mollifier_apply_le_dualNegativeBesov Q hh hc hA hL hη hx hF i

/-- Translation covariance of the mollification. -/
theorem a16_mollify_translate (h : ℝ) (η : Vec d → ℝ) (F : Vec d → Vec d) (z x : Vec d) :
    a16_mollify d h η F (z + x) = a16_mollify d h η (fun y => F (z + y)) x := by
  funext i
  unfold a16_mollify
  rw [← integral_add_left_eq_self (μ := volume) (fun y => a16_kernel d h η (z + x - y) * F y i) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [add_sub_add_left_eq_sub]

/-- The elementary mollifier estimate on a translated cube: for `x` in the
cube of side `3^n` centered at the origin, the mollification at scale `3^n` of the field `F` at
`z + x` is bounded by the normalized dual negative Besov norm of order `1/4` of `F (z + ·)` on
the origin cube of scale `n + 1`. -/
theorem mollifier_translate_le_dualNegativeBesov (n : ℤ) {η : Vec d → ℝ} {A : ℝ} {L : NNReal}
    (hA : ∀ w, |η w| ≤ A) (hL : LipschitzWith L η)
    (hη : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {z x : Vec d}
    (hx : x ∈ cubeSet (originCube d n)) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun y => F (z + y) i) 2 (normalizedCubeMeasure (originCube d (n + 1)))) :
    ‖a16_mollify d ((3 : ℝ) ^ n) η F (z + x)‖ ≤ 3 ^ d * (6 * (L : ℝ) + A) *
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n + 1)) (1 / 4)
        (fun y => F (z + y)) := by
  have hh : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hc : cubeScaleFactor (originCube d (n + 1)) = 3 * (3 : ℝ) ^ n := by
    unfold cubeScaleFactor originCube
    simp only
    rw [zpow_add_one₀ (by norm_num), mul_comm]
  rw [a16_mollify_translate]
  refine mollifier_norm_le_dualNegativeBesov (originCube d (n + 1)) hh hc hA hL hη ?_ hF
  intro y hy
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  intro i
  have hyi : |y i - x i| ≤ (3 : ℝ) ^ n := by
    have := (dist_pi_le_iff hh.le).1 hy i
    rwa [Real.dist_eq] at this
  rw [abs_le] at hyi
  obtain ⟨hx1, hx2⟩ := hx i
  have h3 : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num), mul_comm]
  rw [h3]
  constructor <;> nlinarith only [hyi.1, hyi.2, hx1, hx2]

/-- A mollifier profile meeting the hypotheses of the estimates: the tent function
`max 0 (1 - ‖w‖)`, bounded by `1`, `1`-Lipschitz, supported in the unit sup-ball, equal to `1` at `0`. -/
theorem a16_exists_profile (d : ℕ) :
    ∃ (η : Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) ∧ LipschitzWith L η ∧
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) ∧ η 0 = 1 := by
  refine ⟨fun w => max 0 (1 - ‖w‖), 1, 1, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by norm_num) (by linarith only [norm_nonneg w])
  · refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    rw [max_comm 0, max_comm 0 (1 - ‖w'‖)]
    calc |max (1 - ‖w‖) 0 - max (1 - ‖w'‖) 0| ≤ |(1 - ‖w‖) - (1 - ‖w'‖)| :=
          abs_max_sub_max_le_abs _ _ _
      _ = |‖w'‖ - ‖w‖| := by ring_nf
      _ ≤ ‖w - w'‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le w w'
  · intro w ⟨i, hi⟩
    have : 1 < ‖w‖ := lt_of_lt_of_le hi (by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm w i)
    exact max_eq_left (by linarith only [this])
  · simp

/-- Satisfiability witness: for the constant field `1`, at every scale, shift and the center of the
cube, some profile meets every non-law hypothesis and the estimate holds. -/
example (d : ℕ) (n : ℤ) (z : Vec d) :
    ∃ (η : Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) ∧ LipschitzWith L η ∧
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) ∧ η 0 = 1 ∧
      ‖a16_mollify d ((3 : ℝ) ^ n) η (fun _ _ => 1) (z + 0)‖ ≤ 3 ^ d * (6 * (L : ℝ) + A) *
        Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n + 1)) (1 / 4)
          (fun y => (fun (_ : Vec d) (_ : Fin d) => (1 : ℝ)) (z + y)) := by
  obtain ⟨η, A, L, hA, hL, hη, h0⟩ := a16_exists_profile d
  refine ⟨η, A, L, hA, hL, hη, h0, ?_⟩
  refine mollifier_translate_le_dualNegativeBesov n hA hL hη (F := fun _ _ => 1) ?_ ?_
  · rw [mem_cubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
    constructor <;> simp only [Pi.zero_apply] <;> linarith only [hp]
  · intro i
    exact memLp_const (1 : ℝ)

end

end Section7
end SuperdiffusionCLT
