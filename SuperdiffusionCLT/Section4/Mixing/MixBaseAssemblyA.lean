/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseSplit

/-!
# Elementary helpers for the `hBase` assembly

* `mixBaseA_isBigO_add_const`, `mixBaseA_isBigO_zero`: a weak-Orlicz bound survives adding a
  constant that is at most the amplitude, and the zero function is `O_Ψ(A)` for `A ≥ 0`.
* `mixBaseA_avg_*`: linearity of `descendantsAverage` for constants, sums and scalings.
* `mixBaseA_blockVecDot_neg_*`, `mixBaseA_quad_neg`: sign behavior of the block bilinear form,
  used to read a one-sided bilinear bound at `(-p, q)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory

noncomputable section

variable {d : ℕ}

theorem mixBaseA_isBigO_add_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Ψ : ℝ → ℝ} {X : Ω → ℝ} {A δ : ℝ} (hX : IsBigO μ Ψ X A)
    (hδ : 0 ≤ δ) (hδA : δ ≤ A) : IsBigO μ Ψ (fun ω => X ω + δ) (2 * A) := by
  intro t ht
  refine (measureReal_mono ?_).trans (hX ht)
  intro ω hω
  have hω' : 2 * A * t < |X ω + δ| := hω
  show A * t < |X ω|
  have hA0 : 0 ≤ A := hδ.trans hδA
  have hAt : A ≤ A * t := le_mul_of_one_le_right hA0 ht
  have h1 : |X ω + δ| ≤ |X ω| + δ := by
    have := abs_add_le (X ω) δ
    rwa [abs_of_nonneg hδ] at this
  linarith only [hω', h1, hδA, hAt]

theorem mixBaseA_isBigO_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    IsBigO μ (gammaSigma σ) (fun _ : Ω => (0 : ℝ)) A := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hempty : upperTailEvent (fun _ : Ω => |(0 : ℝ)|) (A * t) = (∅ : Set Ω) := by
    apply Set.eq_empty_of_forall_notMem
    intro ω hω
    have h1 : A * t < |(0 : ℝ)| := hω
    rw [abs_zero] at h1
    linarith only [h1, mul_nonneg hA ht0]
  show μ.real (upperTailEvent (fun _ : Ω => |(0 : ℝ)|) (A * t)) ≤ (gammaSigma σ t)⁻¹
  rw [hempty, MeasureTheory.measureReal_empty]
  have hpsi1 : (1 : ℝ) ≤ gammaSigma σ t := IndependentSums.one_le_gammaSigma ht0
  positivity

theorem mixBaseA_avg_const (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  have hne : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    have := (descendantsAtDepth_nonempty Q j).card_pos
    exact_mod_cast this.ne'
  unfold descendantsAverage
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem mixBaseA_avg_sub (Q : TriadicCube d) (j : ℕ) (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R - G R) =
      descendantsAverage Q j F - descendantsAverage Q j G := by
  unfold descendantsAverage
  simp only [Finset.sum_sub_distrib, mul_sub]

theorem mixBaseA_blockVecDot_neg_left (p Y : BlockVec d) :
    blockVecDot (-p) Y = -blockVecDot p Y := by
  obtain ⟨p1, p2⟩ := p
  simp [blockVecDot, vecDot]
  ring

theorem mixBaseA_blockVecDot_neg_right (p Y : BlockVec d) :
    blockVecDot p (-Y) = -blockVecDot p Y := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨y1, y2⟩ := Y
  simp [blockVecDot, vecDot]
  ring

theorem mixBaseA_blockMatVecMul_neg (A : BlockMat d) (p : BlockVec d) :
    blockMatVecMul A (-p) = -blockMatVecMul A p := by
  obtain ⟨p1, p2⟩ := p
  ext i <;> simp [blockMatVecMul, matVecMul, Finset.sum_neg_distrib, add_comm]

theorem mixBaseA_quad_neg (A : BlockMat d) (p : BlockVec d) :
    blockVecDot (-p) (blockMatVecMul A (-p)) = blockVecDot p (blockMatVecMul A p) := by
  rw [mixBaseA_blockMatVecMul_neg, mixBaseA_blockVecDot_neg_left, mixBaseA_blockVecDot_neg_right,
    neg_neg]

end

end SuperdiffusionCLT.Section4.Mixing
