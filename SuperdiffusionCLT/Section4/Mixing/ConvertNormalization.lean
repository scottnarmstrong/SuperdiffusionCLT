/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.InvertB

/-!
# `p.mixing.P.three.prime#convert-to-L-normalization` 

The second half of this step in the paper reads: "Since the
homogenized block matrices are diagonal with scalar blocks, they commute, and
`bfAhom_L^{-1/2}(cu_n) = B^{-1/2} bfAhom_ℓ^{-1/2}(cu_n)`, we obtain [the
`L`-normalized bound]." Under the bilinear-sandwich reading used throughout
this development (`Section4/Mixing/AnnealedComparison.lean`,
`Section4/Mixing/InvertB.lean`), this substitution is never literally
performed: instead, the scalar quadratic-form domination `#invert-B` supplies
(`Q_ℓ(p) ≤ (1-t)⁻¹ Q_L(p)` for every `p`) directly converts an `ℓ`-normalized
sandwich bound on any fixed real bilinear form `F` into an `L`-normalized one
with the amplitude scaled by `(1-t)⁻¹`, with no matrix object named at all.
`mixMain_convertNormalization_bilinear` is exactly this conversion.

(The first half of this step in the paper -- combining `combine-terms-bound`'s
quenched bound on `bfA_L(z+cu_n) - bfAhom_ℓ(cu_n)` with
`#annealed-comparison`'s deterministic bound on `bfAhom_L(cu_n) -
bfAhom_ℓ(cu_n)` by the triangle inequality to reach a bound on
`bfA_L(z+cu_n) - bfAhom_L(cu_n)` -- is not part of this file: it needs the
actual quenched bilinear form from `combine-terms-bound`, and is carried out in
the consumers of `mixMain_convertNormalization_bilinear`, `MixBaseSplit.lean` and
`MixBaseWitnessB.lean`.)
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- **`#convert-to-L-normalization`, second half, bilinear
form.** `QA`, `QB` are the quadratic forms of two block-diagonal-scalar
matrices (`A = bfAhom_ℓ(cu_n)`, `B = bfAhom_L(cu_n)`); `hdom` is `#invert-B`'s
quadratic-form domination `QA(p) ≤ (1-t)⁻¹ QB(p)` (both halves of
`mixMain_invertB_scalar_bounds`, combined into one pointwise bound). Given any
real bilinear form `F` (indexed by an outer parameter `ω`, e.g. the sample
point) with an `A`-normalized sandwich bound of nonnegative amplitude `X`,
`F` also satisfies the `B`-normalized sandwich bound with amplitude
`X / (1 - t)`. -/
theorem mixMain_convertNormalization_bilinear {Ω : Type*}
    {QA QB : BlockVec d → ℝ} {t : ℝ}
    (hdom : ∀ p : BlockVec d, QA p ≤ (1 - t)⁻¹ * QB p)
    {F : Ω → BlockVec d → BlockVec d → ℝ} {X : Ω → ℝ}
    (hXnonneg : ∀ ω, 0 ≤ X ω)
    (hell : ∀ ω, ∀ p q : BlockVec d, 2 * F ω p q ≤ X ω * (QA p + QA q)) :
    ∀ ω, ∀ p q : BlockVec d, 2 * F ω p q ≤ (X ω / (1 - t)) * (QB p + QB q) := by
  intro ω p q
  have hpq : QA p + QA q ≤ (1 - t)⁻¹ * (QB p + QB q) := by
    have hp := hdom p
    have hq := hdom q
    nlinarith only [hp, hq]
  have hstep : X ω * (QA p + QA q) ≤ X ω * ((1 - t)⁻¹ * (QB p + QB q)) :=
    mul_le_mul_of_nonneg_left hpq (hXnonneg ω)
  have hrw : X ω * ((1 - t)⁻¹ * (QB p + QB q)) = (X ω / (1 - t)) * (QB p + QB q) := by
    rw [div_eq_mul_inv]; ring
  calc 2 * F ω p q ≤ X ω * (QA p + QA q) := hell ω p q
    _ ≤ X ω * ((1 - t)⁻¹ * (QB p + QB q)) := hstep
    _ = (X ω / (1 - t)) * (QB p + QB q) := hrw

/-- The quadratic-form domination `#invert-B` supplies, packaged from the two
scalar bounds of `mixMain_invertB_scalar_bounds`. -/
theorem mixMain_quadraticForm_dom_of_scalar_bounds
    {sell uell sL uL t : ℝ}
    (hs : sell ≤ sL / (1 - t)) (hu : uell ≤ uL / (1 - t))
    (p : BlockVec d) :
    sell * vecNormSq p.1 + uell * vecNormSq p.2 ≤
      (1 - t)⁻¹ * (sL * vecNormSq p.1 + uL * vecNormSq p.2) := by
  have hp1 : 0 ≤ vecNormSq p.1 := vecNormSq_nonneg p.1
  have hp2 : 0 ≤ vecNormSq p.2 := vecNormSq_nonneg p.2
  have hs' : sell ≤ (1 - t)⁻¹ * sL := by rw [← div_eq_inv_mul]; exact hs
  have hu' : uell ≤ (1 - t)⁻¹ * uL := by rw [← div_eq_inv_mul]; exact hu
  nlinarith only [mul_le_mul_of_nonneg_right hs' hp1, mul_le_mul_of_nonneg_right hu' hp2]

end

end SuperdiffusionCLT.Section4.Mixing
