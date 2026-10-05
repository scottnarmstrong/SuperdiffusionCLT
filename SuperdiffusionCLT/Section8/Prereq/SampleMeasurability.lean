/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.DivergenceForm.AlphaShiftedWeakSolution

/-!
# The weak solution depends Lipschitz-continuously on the coefficient

For two coefficient fields `a`, `b` on a set `U`, elliptic with the same lower constant `lam`
(and arbitrary upper constants), and within entrywise distance `δ` of each other on `U`, the value
components of the shifted weak solutions with the same datum `f` differ by at most
`d δ ‖f‖ / (min α lam)^2`.  The constant involves neither upper ellipticity constant.  This is the
continuity of the solution map used to prove measurability in the sample.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.ZeroTraceSobolev
open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

theorem sampleMeas_hilbert_eq_ofVecField (F : HilbertVectorL2 U) :
    F = toHilbertVectorL2OfVecField
      (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F)) := by
  calc
    F = vectorL2ToHilbertVectorL2 (U := U)
        (hilbertVectorL2ToVectorL2 (U := U) F) := by
          symm
          exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) F
    _ = vectorL2ToHilbertVectorL2 (U := U)
        (toVectorL2 (MeasureTheory.Lp.memLp
          (hilbertVectorL2ToVectorL2 (U := U) F))) := by
          congr 1
          exact (MeasureTheory.Lp.toLp_coeFn
            (hilbertVectorL2ToVectorL2 (U := U) F)
            (MeasureTheory.Lp.memLp
              (hilbertVectorL2ToVectorL2 (U := U) F))).symm
    _ = toHilbertVectorL2OfVecField
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := U) F)) := by
          rfl

theorem sampleMeas_inner_operator_eq_pairing {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (F G : HilbertVectorL2 U) :
    inner ℝ (hilbertCoeffOperator hEll F) G = coefficientPairing a U F G := by
  let f : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) F
  let g : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) G
  let hf : MemVectorL2 U (fun x => f x) := MeasureTheory.Lp.memLp f
  let hg : MemVectorL2 U (fun x => g x) := MeasureTheory.Lp.memLp g
  have hF : F = toHilbertVectorL2OfVecField hf := by
    simpa only [f, hf] using sampleMeas_hilbert_eq_ofVecField (U := U) F
  have hG : G = toHilbertVectorL2OfVecField hg := by
    simpa only [g, hg] using sampleMeas_hilbert_eq_ofVecField (U := U) G
  calc
    inner ℝ (hilbertCoeffOperator hEll F) G =
        inner ℝ
          (toHilbertVectorL2OfVecField
            (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf))
          (toHilbertVectorL2OfVecField hg) := by
            rw [hF, hG, hilbertCoeffOperator_toHilbertVectorL2OfVecField hEll hf]
    _ = ∫ x in U, vecDot (matVecMul (a x) (f x)) (g x)
          ∂MeasureTheory.volume :=
      inner_toHilbertVectorL2OfVecField_eq_integral
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hf) hg
    _ = coefficientPairing a U F G := by rfl

/-- A matrix with entries bounded by `δ` has operator norm at most `d δ`. -/
theorem sampleMeas_opNorm_applyMat_le {M : Mat d} {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ i j, |M i j| ≤ δ) : ‖HilbertVec.applyMat M‖ ≤ (d : ℝ) * δ := by
  refine HilbertVec.opNorm_applyMat_le_of_vec_bound (by positivity) fun ξ => ?_
  have hrow : ∀ i : Fin d, (matVecMul M ξ i) ^ 2 ≤ (d : ℝ) * δ ^ 2 * vecDot ξ ξ := by
    intro i
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) ξ
    have h2 : ∑ j : Fin d, M i j ^ 2 ≤ (d : ℝ) * δ ^ 2 := by
      calc ∑ j : Fin d, M i j ^ 2 ≤ ∑ _j : Fin d, δ ^ 2 :=
            Finset.sum_le_sum fun j _ => by
              have := hM i j
              nlinarith only [this, abs_nonneg (M i j), sq_abs (M i j)]
        _ = (d : ℝ) * δ ^ 2 := by simp
    have h3 : vecDot ξ ξ = ∑ j : Fin d, ξ j ^ 2 := by
      simp only [vecDot, sq]
    calc (matVecMul M ξ i) ^ 2 = (∑ j : Fin d, M i j * ξ j) ^ 2 := rfl
      _ ≤ (∑ j : Fin d, M i j ^ 2) * ∑ j : Fin d, ξ j ^ 2 := h1
      _ ≤ ((d : ℝ) * δ ^ 2) * ∑ j : Fin d, ξ j ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ = (d : ℝ) * δ ^ 2 * vecDot ξ ξ := by rw [h3]
  calc vecDot (matVecMul M ξ) (matVecMul M ξ) = ∑ i : Fin d, (matVecMul M ξ i) ^ 2 := by
        simp only [vecDot, sq]
    _ ≤ ∑ _i : Fin d, (d : ℝ) * δ ^ 2 * vecDot ξ ξ := Finset.sum_le_sum fun i _ => hrow i
    _ = ((d : ℝ) * δ) ^ 2 * vecDot ξ ξ := by simp; ring

/-- The coefficient pairings of two coefficient fields within entrywise distance `δ` on `U`
differ by at most `d δ ‖F‖ ‖G‖`. -/
theorem sampleMeas_abs_pairing_sub_le {a b : CoeffField d} {lam Lam lam' Lam' δ : ℝ}
    (hEa : IsEllipticFieldOn lam Lam U a) (hEb : IsEllipticFieldOn lam' Lam' U b)
    (hδ : 0 ≤ δ) (hab : ∀ y ∈ U, ∀ i j, |a y i j - b y i j| ≤ δ)
    (F G : HilbertVectorL2 U) :
    |coefficientPairing a U F G - coefficientPairing b U F G| ≤
      (d : ℝ) * δ * ‖F‖ * ‖G‖ := by
  rw [← sampleMeas_inner_operator_eq_pairing hEa, ← sampleMeas_inner_operator_eq_pairing hEb,
    ← inner_sub_left]
  have hmem : ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEa)).2
      (Filter.Eventually.of_forall fun _ hx => hx)
  have hnorm : ‖hilbertCoeffOperator hEa F - hilbertCoeffOperator hEb F‖ ≤
      ((d : ℝ) * δ) * ‖F‖ := by
    refine MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MeasureTheory.Lp.coeFn_sub (hilbertCoeffOperator hEa F)
      (hilbertCoeffOperator hEb F), ae_hilbertCoeffOperator_apply hEa F,
      ae_hilbertCoeffOperator_apply hEb F, hmem] with x h1 h2 h3 hx
    rw [h1, Pi.sub_apply, h2, h3]
    have hAm : (HilbertVec.applyMat (a x)) (F x) - (HilbertVec.applyMat (b x)) (F x) =
        HilbertVec.applyMat (a x - b x) (F x) := by
      rw [← sub_apply]
      congr 1
      ext v
      simp [HilbertVec.applyMat_apply, sub_matVecMul]
    rw [hAm]
    refine ((HilbertVec.applyMat (a x - b x)).le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_right
      (sampleMeas_opNorm_applyMat_le hδ fun i j => hab x hx i j) (norm_nonneg _)
  calc |inner ℝ (hilbertCoeffOperator hEa F - hilbertCoeffOperator hEb F) G| ≤
        ‖hilbertCoeffOperator hEa F - hilbertCoeffOperator hEb F‖ * ‖G‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
          (hilbertCoeffOperator hEa F - hilbertCoeffOperator hEb F) G
    _ ≤ (((d : ℝ) * δ) * ‖F‖) * ‖G‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = (d : ℝ) * δ * ‖F‖ * ‖G‖ := by ring

theorem sampleMeas_norm_gradient_le (u : ZeroTraceSobolev U) : ‖gradient u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The energy bound of the weak solution: `min α lam * ‖u‖ ≤ ‖f‖`. -/
theorem sampleMeas_solution_norm_le {a : CoeffField d} {α lam Lam : ℝ} (hα : 0 < α)
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U) :
    min α lam * ‖alphaShiftedSolution a hα hlam hEll f‖ ≤ ‖f‖ := by
  set u := alphaShiftedSolution a hα hlam hEll f with hu
  have hweak := alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f u
  have hlow := shiftedBilin_lower_bound (α := α) hEll u
  rw [shiftedBilin_apply, hweak] at hlow
  have h1 : inner ℝ f (toL2 u) ≤ ‖f‖ * ‖u‖ :=
    (real_inner_le_norm f (toL2 u)).trans
      (mul_le_mul_of_nonneg_left (norm_toL2_le u) (norm_nonneg _))
  rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
  · rw [← h0]; simp
  · have : min α lam * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ := hlow.trans h1
    exact le_of_mul_le_mul_right this hpos

/-- **Lipschitz dependence of the solution on the coefficient.** -/
theorem sampleMeas_solution_lipschitz {a b : CoeffField d} {α lam Lam Lam' δ : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hEa : IsEllipticFieldOn lam Lam U a)
    (hEb : IsEllipticFieldOn lam Lam' U b) (hδ : 0 ≤ δ)
    (hab : ∀ y ∈ U, ∀ i j, |a y i j - b y i j| ≤ δ) (f : ScalarL2 U) :
    ‖toL2 (alphaShiftedSolution a hα hlam hEa f) - toL2 (alphaShiftedSolution b hα hlam hEb f)‖ ≤
      (d : ℝ) * δ * ‖f‖ / (min α lam) ^ 2 := by
  set m := min α lam with hm
  have hm0 : 0 < m := lt_min hα hlam
  set u := alphaShiftedSolution a hα hlam hEa f with hu
  set w := alphaShiftedSolution b hα hlam hEb f with hw
  have hwn : m * ‖w‖ ≤ ‖f‖ := sampleMeas_solution_norm_le hα hlam hEb f
  have hwb : α * inner ℝ (toL2 w) (toL2 (u - w)) +
      coefficientPairing b U (gradient w) (gradient (u - w)) = inner ℝ f (toL2 (u - w)) :=
    alphaShiftedSolution_isAlphaShiftedWeakSolution b hα hlam hEb f (u - w)
  have hwa : α * inner ℝ (toL2 w) (toL2 (u - w)) +
      coefficientPairing a U (gradient w) (gradient (u - w)) =
      inner ℝ f (toL2 (u - w)) +
        (coefficientPairing a U (gradient w) (gradient (u - w)) -
          coefficientPairing b U (gradient w) (gradient (u - w))) := by
    linarith only [hwb]
  have hv : α * inner ℝ (toL2 u) (toL2 (u - w)) +
      coefficientPairing a U (gradient u) (gradient (u - w)) = inner ℝ f (toL2 (u - w)) :=
    alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEa f (u - w)
  have hlow := shiftedBilin_lower_bound (α := α) hEa (u - w)
  have hexp : shiftedBilin hEa α (u - w) (u - w) =
      -(coefficientPairing a U (gradient w) (gradient (u - w)) -
          coefficientPairing b U (gradient w) (gradient (u - w))) := by
    have e1 : shiftedBilin hEa α (u - w) (u - w) =
        shiftedBilin hEa α u (u - w) - shiftedBilin hEa α w (u - w) := by
      rw [map_sub (shiftedBilin hEa α) u w, sub_apply]
    rw [e1, shiftedBilin_apply, shiftedBilin_apply, hv, hwa]
    ring
  have hpair := sampleMeas_abs_pairing_sub_le hEa hEb hδ hab (gradient w) (gradient (u - w))
  have hgw : ‖gradient w‖ ≤ ‖w‖ := sampleMeas_norm_gradient_le w
  have hgv : ‖gradient (u - w)‖ ≤ ‖u - w‖ := sampleMeas_norm_gradient_le (u - w)
  have hdδ : 0 ≤ (d : ℝ) * δ := by positivity
  have h2 : (d : ℝ) * δ * ‖gradient w‖ * ‖gradient (u - w)‖ ≤ (d : ℝ) * δ * ‖w‖ * ‖u - w‖ := by
    have := mul_le_mul hgw hgv (norm_nonneg _) (norm_nonneg _)
    calc (d : ℝ) * δ * ‖gradient w‖ * ‖gradient (u - w)‖ =
        (d : ℝ) * δ * (‖gradient w‖ * ‖gradient (u - w)‖) := by ring
      _ ≤ (d : ℝ) * δ * (‖w‖ * ‖u - w‖) := mul_le_mul_of_nonneg_left this hdδ
      _ = _ := by ring
  have h3 : m * ‖u - w‖ * ‖u - w‖ ≤ (d : ℝ) * δ * ‖w‖ * ‖u - w‖ := by
    have := le_abs_self (-(coefficientPairing a U (gradient w) (gradient (u - w)) -
          coefficientPairing b U (gradient w) (gradient (u - w))))
    rw [abs_neg] at this
    linarith only [hlow, hexp, this, hpair, h2]
  have h4 : ‖u - w‖ ≤ (d : ℝ) * δ * ‖f‖ / m ^ 2 := by
    rcases eq_or_lt_of_le (norm_nonneg (u - w)) with h0 | hpos
    · rw [← h0]; positivity
    · have h5 : m * ‖u - w‖ ≤ (d : ℝ) * δ * ‖w‖ := le_of_mul_le_mul_right (by linarith only [h3]) hpos
      rw [le_div_iff₀ (by positivity)]
      have h6 : ‖w‖ * m ≤ ‖f‖ := by linarith only [hwn]
      calc ‖u - w‖ * m ^ 2 = (m * ‖u - w‖) * m := by ring
        _ ≤ ((d : ℝ) * δ * ‖w‖) * m := mul_le_mul_of_nonneg_right h5 hm0.le
        _ = (d : ℝ) * δ * (‖w‖ * m) := by ring
        _ ≤ (d : ℝ) * δ * ‖f‖ := mul_le_mul_of_nonneg_left h6 hdδ
  calc ‖toL2 u - toL2 w‖ = ‖toL2 (u - w)‖ := by rw [map_sub]
    _ ≤ ‖u - w‖ := norm_toL2_le _
    _ ≤ _ := h4

end

end SuperdiffusionCLT.Section8
