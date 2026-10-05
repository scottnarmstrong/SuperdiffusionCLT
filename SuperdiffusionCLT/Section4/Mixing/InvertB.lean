/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.AnnealedComparison

/-!
# `p.mixing.P.three.prime#invert-B`

The source introduces `B := bfAhom_ℓ^{-1/2}(cu_n) bfAhom_L(cu_n) bfAhom_ℓ^{-1/2}(cu_n)`
and shows `|B - I_{2d}| ≤ 1/2`, concluding `|B^{-1/2}| ≤ C`. Since
`bfAhom_ℓ(cu_n)` and `bfAhom_L(cu_n)` are *both* block-diagonal scalar
matrices (`e.homs.defs.U`, `Section4/Mixing/AnnealedComparison.lean`), every
matrix in sight here is simultaneously diagonal, so under the
bilinear-sandwich reading the whole `B`,
`B^{-1/2}` apparatus reduces to ordinary real-number ratio algebra on the two
pairs of annealed scalars `(σ̄_ℓ(cu_n), σ̄_{ℓ,*}^{-1}(cu_n))` and
`(σ̄_L(cu_n), σ̄_{L,*}^{-1}(cu_n))`: no matrix square root or matrix inverse
is ever computed as a Lean operation, and `B` itself never needs to be named.

`mixMain_invertB_scalar_bounds` is both `#annealed-comparison`'s conclusion
`|B - I| ≤ 1/2` (its two "≤ (1+t) ·" halves) and `#invert-B`'s conclusion
`|B^{-1/2}| ≤ C` (its two "≥ 1/(1-t) ·⁻¹ ·" halves, i.e. the *reverse* ratio
bound, which is exactly what a bound on `B^{-1/2}` supplies) **read off the
same universally-quantified bilinear sandwich hypothesis** by plugging in the
four coordinate-vector pairs `p = q = (e_i, 0)`, `p = (e_i,0), q = (-e_i,0)`,
and their lower-block analogues. This matches the reading-choices doc of
`Frozen/Section2/MixingMinscale.lean`: "No sign hypothesis on `t` is needed:
the printed norm is nonnegative, so a negative value falsifies both sides at
once" — the single inequality `2 p·Hq ≤ t(p·Ap+q·Aq)` for *every* `p, q`
already contains both signs, because it holds in particular for `p ↦ -p`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

private theorem mixMain_single_vecNormSq (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ) : Vec d) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply]

private theorem mixMain_single_vecDot_neg_self (i : Fin d) :
    vecDot (Pi.single i (1 : ℝ) : Vec d) (-(Pi.single i (1 : ℝ) : Vec d)) = -1 := by
  simp [vecDot, Pi.single_apply]

/-- **`#annealed-comparison` and `#invert-B` together, in the bilinear
reading.** `H` is the block-diagonal-scalar difference `bfAhom_L(cu_n) -
bfAhom_ℓ(cu_n)` and `A` is the `ℓ`-normalizing matrix `bfAhom_ℓ(cu_n)`,
`sell, uell` its two positive scalars. The hypothesis `hsand` is the
sandwich-form reading of `|B - I_{2d}| ≤ t` (`t = 1/2` in the paper).
The four conclusions are the two directions of `#annealed-comparison`
(`sL ≤ (1+t) sell`, `uL ≤ (1+t) uell`) and the two directions of `#invert-B`
read as quadratic-form domination (`sell ≤ sL / (1-t)`, `uell ≤ uL / (1-t)`,
equivalent to `Aell ≤ (1-t)⁻¹ AL` in Loewner order, i.e. `|B^{-1/2}|² ≤
(1-t)⁻¹`). -/
theorem mixMain_invertB_scalar_bounds [NeZero d]
    {sell uell sL uL t : ℝ} (ht1 : t < 1)
    (H A : BlockMat d)
    (hHul : H.upperLeft = (sL - sell) • (1 : Mat d)) (hHur : H.upperRight = 0)
    (hHll : H.lowerLeft = 0) (hHlr : H.lowerRight = (uL - uell) • (1 : Mat d))
    (hAul : A.upperLeft = sell • (1 : Mat d)) (hAur : A.upperRight = 0)
    (hAll : A.lowerLeft = 0) (hAlr : A.lowerRight = uell • (1 : Mat d))
    (hsand : ∀ p q : BlockVec d,
        2 * blockVecDot p (blockMatVecMul H q) ≤
          t * (blockVecDot p (blockMatVecMul A p) + blockVecDot q (blockMatVecMul A q))) :
    sL ≤ (1 + t) * sell ∧ sell ≤ sL / (1 - t) ∧
      uL ≤ (1 + t) * uell ∧ uell ≤ uL / (1 - t) := by
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  set ei : Vec d := Pi.single i (1 : ℝ) with hei_def
  have hei_self : vecDot ei ei = 1 := mixMain_single_vecNormSq i
  have hei_neg : vecDot ei (-ei) = -1 := mixMain_single_vecDot_neg_self i
  have hzero_dot : vecDot (0 : Vec d) (0 : Vec d) = 0 := by simp [vecDot]
  have hzero_norm : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
  have hei_normSq : vecNormSq ei = 1 := mixMain_single_vecNormSq i
  have hneg_self : vecDot (-ei) (-ei) = 1 := by
    have heq : vecDot (-ei) (-ei) = vecDot ei ei := by simp [vecDot]
    rw [heq]; exact hei_self
  have hneg_normSq : vecNormSq (-ei) = 1 := hneg_self
  -- Upper block, `p = q = (ei, 0)`: gives `sL - sell ≤ t * sell`.
  have hupA := hsand (ei, 0) (ei, 0)
  rw [mixMain_blockDiagScalar_bilinear_cross_eq hHur hHll hHul hHlr,
      mixMain_blockDiagScalar_bilinear_eq hAur hAll hAul hAlr] at hupA
  simp only [hei_self, hzero_dot, hei_normSq, hzero_norm, mul_zero, add_zero] at hupA
  -- hupA : 2 * ((sL - sell) * 1) ≤ t * (sell * 1 + sell * 1)
  have hup : sL - sell ≤ t * sell := by nlinarith only [hupA]
  -- Upper block, `p = (ei, 0), q = (-ei, 0)`: gives `-(sL - sell) ≤ t * sell`.
  have hdnA := hsand (ei, 0) (-ei, 0)
  rw [mixMain_blockDiagScalar_bilinear_cross_eq hHur hHll hHul hHlr,
      mixMain_blockDiagScalar_bilinear_eq hAur hAll hAul hAlr,
      mixMain_blockDiagScalar_bilinear_eq hAur hAll hAul hAlr] at hdnA
  simp only [hei_neg, hzero_dot, hei_normSq, hzero_norm, hneg_normSq, mul_zero,
    add_zero] at hdnA
  have hdn : -(sL - sell) ≤ t * sell := by nlinarith only [hdnA]
  -- Lower block, `p = q = (0, ei)`: gives `uL - uell ≤ t * uell`.
  have hupB := hsand (0, ei) (0, ei)
  rw [mixMain_blockDiagScalar_bilinear_cross_eq hHur hHll hHul hHlr,
      mixMain_blockDiagScalar_bilinear_eq hAur hAll hAul hAlr] at hupB
  simp only [hei_self, hzero_dot, hei_normSq, hzero_norm, mul_zero, zero_add] at hupB
  have hup2 : uL - uell ≤ t * uell := by nlinarith only [hupB]
  -- Lower block, `p = (0, ei), q = (0, -ei)`: gives `-(uL - uell) ≤ t * uell`.
  have hdnB := hsand (0, ei) (0, -ei)
  rw [mixMain_blockDiagScalar_bilinear_cross_eq hHur hHll hHul hHlr,
      mixMain_blockDiagScalar_bilinear_eq hAur hAll hAul hAlr,
      mixMain_blockDiagScalar_bilinear_eq hAur hAll hAul hAlr] at hdnB
  simp only [hei_neg, hzero_dot, hei_normSq, hzero_norm, hneg_normSq, mul_zero,
    zero_add] at hdnB
  have hdn2 : -(uL - uell) ≤ t * uell := by nlinarith only [hdnB]
  have h1t : 0 < 1 - t := by linarith only [ht1]
  refine ⟨by linarith only [hup], ?_, by linarith only [hup2], ?_⟩
  · rw [le_div_iff₀ h1t]
    nlinarith only [hdn]
  · rw [le_div_iff₀ h1t]
    nlinarith only [hdn2]

end

end SuperdiffusionCLT.Section4.Mixing
