/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Truncation
public import SuperdiffusionCLT.Section7.Prereq.DirichletExistenceB

/-!
# Weak maximum principle on a bounded open set

Test the equation with `(u - M)₊ ∈ H¹₀(U)`.  Its gradient is `1_{u > M} ∇u` almost everywhere,
so the energy `∫ ∇v · a ∇v` vanishes, ellipticity gives `∇v = 0`, and the zero-trace Poincaré
inequality gives `v = 0`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

theorem volume_ne_top_of_isBoundedDomain (hUb : IsBoundedDomain U) : volume U ≠ ⊤ := by
  rcases exists_ball_superset_of_isBoundedDomain hUb with ⟨R, -, hUB⟩
  exact ((measure_mono hUB).trans_lt measure_ball_lt_top).ne

/-- The gradient of `H¹₀` function equal to `(u - M)₊` is `1_{u > M} ∇u` a.e. -/
theorem grad_ae_eq_posPartGrad (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U)
    (M : ℝ) (v : H10Function U)
    (hv : v.toH1Function.toFun = fun x => max (u.toFun x - M) 0) :
    ∀ᵐ x ∂(volumeMeasureOn U), v.toH1Function.grad x = posPartGrad u M x := by
  let p := positivePartOpen hU u M (memL2On_positivePart_of_finite u hfin M)
  have hcoord : ∀ i : Fin d, (fun x => v.toH1Function.grad x i) =ᵐ[volumeMeasureOn U]
      (fun x => p.grad x i) := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_memL2On (v.toH1Function.gradMemL2 i))
      (locallyIntegrableOn_of_memL2On (p.gradMemL2 i)) ?_ (p.hasWeakPartialDerivOn i)
    have h := v.toH1Function.hasWeakPartialDerivOn i
    rwa [hv] at h
  have hall := ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- Pointwise: the flux pairing against the truncated gradient is the energy of the truncation. -/
theorem flux_pair_eq (a : Mat d) (g G : Vec d) (M s : ℝ)
    (hG : G = {y : ℝ | M < y}.indicator (fun _ => g) s) :
    vecDot (matVecMul (a) g) G = vecDot (matVecMul a G) G := by
  by_cases h : M < s
  · have : G = g := by rw [hG]; simp [h]
    rw [this]
  · have : G = 0 := by rw [hG]; simp [h]
    rw [this]
    simp [vecDot, matVecMul]

theorem weakMaxPrinciple_core [NeZero d] (hU : IsOpen U) (hUb : IsBoundedDomain U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    (u : H1Function U) (hu : IsWeakSolutionOn a U u 0 0) {M : ℝ}
    (hM : MemH10 U (fun x => max (u.toFun x - M) 0)) :
    ∀ᵐ x ∂(volume.restrict U), u.toFun x ≤ M := by
  obtain ⟨v, hv⟩ := hM
  have hfin := volume_ne_top_of_isBoundedDomain hUb
  have hgrad := grad_ae_eq_posPartGrad hU hfin u M v hv
  -- the energy of `v` vanishes
  have hpair : ∀ᵐ x ∂(volumeMeasureOn U),
      vecDot (matVecMul (a x) (u.grad x)) (v.toH1Function.grad x) =
        vecDot (matVecMul (a x) (v.toH1Function.grad x)) (v.toH1Function.grad x) := by
    filter_upwards [hgrad] with x hx
    refine flux_pair_eq (a x) (u.grad x) _ M (u.toFun x) ?_
    rw [hx]
    rfl
  have hint0 : ∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x))
      (v.toH1Function.grad x) ∂volume = 0 := by
    have h := hu v
    have h0 : (∫ x in U, ((0 : Vec d → ℝ) x) * v.toH1Function.toFun x ∂volume) +
        ∫ x in U, vecDot ((0 : Vec d → Vec d) x) (v.toH1Function.grad x) ∂volume = 0 := by
      simp [vecDot]
    rw [h0] at h
    rw [← h]
    exact (integral_congr_ae hpair).symm
  by_cases hne : U.Nonempty
  swap
  · have h0 : volume.restrict U = 0 := by
      rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
    rw [h0]
    simp
  obtain ⟨x0, hx0⟩ := hne
  have hlam : 0 < lam := (hEll.2 x0 hx0).1
  set F := v.toH1Function.gradToHilbertVectorL2 with hF
  have hmem := v.toH1Function.grad_memVectorL2
  have hFeq : F = toHilbertVectorL2OfVecField hmem := rfl
  have hcoer := coeffOperator_coercive hEll F
  have hinner : inner ℝ (hilbertCoeffOperator hEll F) F = ∫ x in U,
      vecDot (matVecMul (a x) (v.toH1Function.grad x)) (v.toH1Function.grad x) ∂volume := by
    rw [hFeq, hilbertCoeffOperator_toHilbertVectorL2OfVecField]
    exact inner_toHilbertVectorL2OfVecField_eq_integral
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hmem) hmem
  rw [hinner, hint0] at hcoer
  have hF0 : ‖F‖ = 0 := by
    have : ‖F‖ ^ 2 ≤ 0 := by
      by_contra hc
      have := mul_pos hlam (not_le.mp hc)
      linarith only [this, hcoer]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  rcases h10_poincare_of_bounded hU hUb with ⟨C, hC0, hC⟩
  have hsum : v.toH1Function.gradientCoordL2NormSum ≤ 0 := by
    refine (H1Function.gradientCoordL2NormSum_le _).trans ?_
    have := H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2 v.toH1Function
    rw [← hF, hF0] at this
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) this
  have hs0 : ‖v.toH1Function.toScalarL2‖ ≤ 0 :=
    (hC v).trans (by nlinarith only [hsum, hC0])
  have hz : v.toH1Function.toScalarL2 = 0 := norm_le_zero_iff.mp hs0
  have hvz : v.toH1Function.toFun =ᵐ[volumeMeasureOn U] 0 := by
    have h1 := H1Function.coeFn_toScalarL2 v.toH1Function
    rw [hz] at h1
    filter_upwards [h1, Lp.coeFn_zero ℝ 2 (volumeMeasureOn U)] with x h1x h2x
    rw [← h1x, h2x]
  filter_upwards [hvz] with x hx
  have : max (u.toFun x - M) 0 = 0 := by
    have := congrFun hv x
    rw [← this]
    exact hx
  have := le_max_left (u.toFun x - M) 0
  linarith only [this, ‹max (u.toFun x - M) 0 = 0›]

end SuperdiffusionCLT.Section7
