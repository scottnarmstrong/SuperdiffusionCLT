/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateC
public import SuperdiffusionCLT.Section7.Prereq.RhsLemma

/-!
# The energy estimate for the adjoint solution

Test the adjoint equation with the solution itself (the identity `ν ‖∇v‖² = ∫ g v` of a field whose
symmetric part is `ν Id`), use that the source has mean zero to subtract a constant, and absorb the
Poincaré gain by the quadratic inequality `ν x² ≤ a x + b ⇒ x ≤ a/ν + √(b/ν)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section7

noncomputable section

variable {d : ℕ}

/-- The quadratic inequality behind the energy estimate. -/
theorem decayEst_quad {ν x a b : ℝ} (hν : 0 < ν) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ν * x ^ 2 ≤ a * x + b) : x ≤ a / ν + Real.sqrt (b / ν) := by
  by_contra hcon
  push Not at hcon
  set t := Real.sqrt (b / ν) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : ν * t ^ 2 = b := by
    rw [ht, Real.sq_sqrt (div_nonneg hb hν.le)]
    field_simp
  have h1 : a / ν + t < x := hcon
  have h2 : a < ν * x - ν * t := by
    have := mul_lt_mul_of_pos_left h1 hν
    rw [mul_add, mul_div_cancel₀ _ hν.ne'] at this
    linarith only [this]
  have hxt : t < x := by
    have : 0 ≤ a / ν := div_nonneg ha hν.le
    linarith only [h1, this]
  have h3 : ν * t * x < (ν * x - a) * x := by
    have hxpos : 0 < x := lt_of_le_of_lt ht0 hxt
    exact mul_lt_mul_of_pos_right (by linarith only [h2]) hxpos
  have h4 : ν * t ^ 2 ≤ ν * t * x := by
    have h5 : t ^ 2 ≤ t * x := by rw [sq]; exact mul_le_mul_of_nonneg_left hxt.le ht0
    have := mul_le_mul_of_nonneg_left h5 hν.le
    linarith only [this]
  linarith only [h, h3, h4, ht2]

/-- **Energy identity** for a zero-trace solution of the problem with matrix field `A` whose
symmetric part is `ν Id`: `ν ∫_U |∇v|² = ∫_U g v`. -/
theorem decayEst_energy (A : CoeffField d) (U : Set (Vec d)) (hU : MeasurableSet U) {ν : ℝ}
    (hsym : ∀ x ∈ U, symmPart (A x) = ν • (1 : Mat d)) (v : H10Function U) (g : Vec d → ℝ)
    (hv : IsWeakSolutionOn A U v.toH1Function g (fun _ => 0)) :
    ν * ∫ x in U, vecNormSq (v.toH1Function.grad x) = ∫ x in U, g x * v.toH1Function.toFun x := by
  refine r1_energy_identity hU hsym v g (fun φ => ?_)
  have := hv φ
  simpa [vecDot] using this

/-- **Gradient bound.**  `v ∈ H¹₀(U)` solves the problem for `A` (symmetric part `ν Id`) with a mean
zero source `g` supported in `S ⊆ S' ⊆ U`; if `v` satisfies the Poincaré-type inequality
`‖v - c‖_{L²(S')} ≤ P₁ ‖∇v‖_{L²(S')} + P₂ ‖g‖_{L²(S)}`, then
`‖∇v‖_{L²(U)} ≤ (P₁/ν + √(P₂/ν)) ‖g‖_{L²(S)}`. -/
theorem decayEst_grad_bound (A : CoeffField d) (U S S' : Set (Vec d)) (hU : MeasurableSet U)
    (hSS : S ⊆ S') (hS'U : S' ⊆ U) {ν : ℝ} (hν : 0 < ν)
    (hsym : ∀ x ∈ U, symmPart (A x) = ν • (1 : Mat d)) (v : H10Function U) (g : Vec d → ℝ)
    (hv : IsWeakSolutionOn A U v.toH1Function g (fun _ => 0)) (c P₁ P₂ : ℝ) (hP₁ : 0 ≤ P₁)
    (hP₂ : 0 ≤ P₂)
    (hsupp : ∀ x, x ∉ S → g x = 0) (hmean : ∫ x in S, g x = 0)
    (hg : MemLp g 2 (volume.restrict S)) (hgi : Integrable g (volume.restrict S))
    (hvS' : MemLp (fun x => v.toH1Function.toFun x - c) 2 (volume.restrict S'))
    (hP : Real.sqrt (∫ x in S', (v.toH1Function.toFun x - c) ^ 2) ≤
      P₁ * Real.sqrt (∫ x in S', vecNormSq (v.toH1Function.grad x)) +
        P₂ * Real.sqrt (∫ x in S, g x ^ 2)) :
    Real.sqrt (∫ x in U, vecNormSq (v.toH1Function.grad x)) ≤
      (P₁ / ν + Real.sqrt (P₂ / ν)) * Real.sqrt (∫ x in S, g x ^ 2) := by
  have hSU : S ⊆ U := hSS.trans hS'U
  have hvS : MemLp (fun x => v.toH1Function.toFun x - c) 2 (volume.restrict S) :=
    hvS'.mono_measure (Measure.restrict_mono hSS le_rfl)
  have hen := decayEst_energy A U hU hsym v g hv
  have hosc := decayEst_pairing_osc U S hU hSU g v.toH1Function.toFun c hsupp hmean hg hgi hvS
  have hgrad : Integrable (fun x => vecNormSq (v.toH1Function.grad x)) (volume.restrict U) := by
    unfold vecNormSq vecDot
    refine integrable_finsetSum _ fun i _ => ?_
    have := (v.toH1Function.gradMemL2 i).integrable_sq
    simpa [mul_self_eq_zero, sq] using this
  have hG0 : 0 ≤ ∫ x in U, vecNormSq (v.toH1Function.grad x) :=
    integral_nonneg fun x => by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hmono : ∫ x in S', vecNormSq (v.toH1Function.grad x) ≤
      ∫ x in U, vecNormSq (v.toH1Function.grad x) :=
    setIntegral_mono_set hgrad (Filter.Eventually.of_forall fun x => by
      unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Filter.Eventually.of_forall hS'U)
  have hvint : Integrable (fun x => (v.toH1Function.toFun x - c) ^ 2) (volume.restrict S') :=
    hvS'.integrable_sq
  have hmono2 : ∫ x in S, (v.toH1Function.toFun x - c) ^ 2 ≤
      ∫ x in S', (v.toH1Function.toFun x - c) ^ 2 :=
    setIntegral_mono_set hvint (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall hSS)
  set x := Real.sqrt (∫ x in U, vecNormSq (v.toH1Function.grad x)) with hx
  set N := Real.sqrt (∫ x in S, g x ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = ∫ x in U, vecNormSq (v.toH1Function.grad x) := Real.sq_sqrt hG0
  have hxx : Real.sqrt (∫ x in S', vecNormSq (v.toH1Function.grad x)) ≤ x :=
    Real.sqrt_le_sqrt hmono
  have h1 : Real.sqrt (∫ x in S, (v.toH1Function.toFun x - c) ^ 2) ≤
      P₁ * x + P₂ * N :=
    (Real.sqrt_le_sqrt hmono2).trans (hP.trans (by
      have := mul_le_mul_of_nonneg_left hxx hP₁
      linarith only [this]))
  have h2 : ν * x ^ 2 ≤ (P₁ * N) * x + P₂ * N ^ 2 := by
    rw [hx2, hen]
    have h3 := (le_abs_self _).trans hosc
    have h4 : Real.sqrt (∫ x in S, (v.toH1Function.toFun x - c) ^ 2) * N ≤
        (P₁ * x + P₂ * N) * N := mul_le_mul_of_nonneg_right h1 hN0
    linarith only [h3, h4]
  have h5 := decayEst_quad hν (mul_nonneg hP₁ hN0) (mul_nonneg hP₂ (sq_nonneg N)) h2
  have h6 : Real.sqrt (P₂ * N ^ 2 / ν) = Real.sqrt (P₂ / ν) * N := by
    rw [show P₂ * N ^ 2 / ν = P₂ / ν * N ^ 2 by ring, Real.sqrt_mul (div_nonneg hP₂ hν.le),
      Real.sqrt_sq hN0]
  rw [h6] at h5
  calc x ≤ P₁ * N / ν + Real.sqrt (P₂ / ν) * N := h5
    _ = (P₁ / ν + Real.sqrt (P₂ / ν)) * N := by ring

/-- Satisfiability: the identity field, zero solution and zero source on empty `S ⊆ S'`. -/
example (U : Set (Vec d)) (hU : MeasurableSet U) :
    Real.sqrt (∫ x in U, vecNormSq ((0 : H10Function U).toH1Function.grad x)) ≤
      ((0 : ℝ) / 1 + Real.sqrt ((0 : ℝ) / 1)) *
        Real.sqrt (∫ x in (∅ : Set (Vec d)), (fun _ : Vec d => (0 : ℝ)) x ^ 2) := by
  have hsym : ∀ x ∈ U, symmPart ((fun _ => (1 : Mat d)) x) = (1 : ℝ) • (1 : Mat d) := by
    intro x _
    funext i j
    simp only [symmPart, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hv : IsWeakSolutionOn (fun _ => (1 : Mat d)) U (0 : H10Function U).toH1Function
      (fun _ => 0) (fun _ => 0) := by
    intro φ
    have hg : ∀ x, (H10Function.toH1Function (0 : H10Function U)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, hg]
  have hg : ∀ x, (H10Function.toH1Function (0 : H10Function U)).toFun x = 0 := fun _ => rfl
  exact decayEst_grad_bound (fun _ => (1 : Mat d)) U ∅ ∅ hU (Set.Subset.refl _)
    (Set.empty_subset _) one_pos hsym 0 (fun _ => 0) hv 0 0 0 le_rfl le_rfl
    (fun _ _ => rfl) (by simp) (by simp) (by simp) (by simp [hg]) (by simp)

end

end SuperdiffusionCLT.Section8
