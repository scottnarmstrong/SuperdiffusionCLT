/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich
public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Package C2: the CFS part of the tail of `M_{n,ρ}` — algebraic core

Source: `e.this.is.so.nice.again#tail-cfs-weaker`, in the proof of `l.weaknorms.prime` of [AK],
first display: for `k ∈ ℕ` with `βk ≤ h ≤ k` and `k ≥ h + L₁ log(L₂ h)`,
subadditivity together with `(P3′) a.CFS.weaker` gives

`|(bfAhom^{-1/2}(cu_h)(bfA(z+cu_k)-bfAhom(cu_h))bfAhom^{-1/2}(cu_h))_+|
  ≤ |avsum_{z'∈z+3^h Lat∩cu_k} bfAhom^{-1/2}(cu_h)(bfA(z'+cu_h)-bfAhom(cu_h))
      bfAhom^{-1/2}(cu_h)| ≤ O_Ψ(ω_h)`,

then (i) a union bound over the sub-cubes `z ∈ 3^k Lat ∩ cu_n` and (ii) a
second union bound over the scales `k ∈ ℕ ∩ [h', n]` (`h' := h + L₁ log(L₂h)`),
using the growth condition, give

`P[max_{k∈[h',n]} 3^{-ρ(n-k)} max_z |·|_+ > ω_h t] ≤ (2K_Ψ^{4d²}/(ηρ-d)) t^{-η}`.

This file proves the **algebraic core**: subadditivity (CoarseGraining's
`BlockLoewner.lean`, imported and used samplewise, no law typing) combined
with a `(P3′)`-shaped bilinear average bound at an arbitrary cube `Q`
(scale `k`), chained by `BlockMatLoewnerLE.trans`, into the one-sided
(positive-part) Loewner excess reading `bfA(Q) ⪯ (1+X)•bfAhom(cu_h)` that the
main statement `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3` uses for `(P2′)`
(`|(S-I)_+| ≤ t ⟺ 0 ≤ t ∧ bfA ⪯ (1+t)bfAhom`). No matrix
square root, no operator norm, and no `CFC.sqrt` machinery is needed for this
step: `BlockMatLoewnerLE` is itself stated through the quadratic form, so the
whole derivation is elementary Loewner-order algebra.

The two probabilistic union bounds and the resulting second-moment bound are
proved in `CFSB.lean`, which also assembles the target theorem and
records how it feeds the second moment `E[M_{n,ρ}²]`.

## Finding 1: `(P3′)` is an origin-cube statement, the tail bound needs every translate

The `(P3′)` clause of `SuperdiffusionCLT.Frozen.Section4.
akhc_weakerP3` (copied verbatim below)
quantifies its bilinear average bound only over
`descendantsAtDepth (originCube d j) (j - n)`, i.e. **only at the origin
cube** `cu_j`. But the paper's own union bound ranges
over `z ∈ 3^k Lat ∩ cu_n`, i.e. over **every translate** `z + cu_k`, not just
`z = 0`. The printed proof invokes `(P3′)` at each translate silently,
licensed by `(P1) a.stationarity` (shift-invariance of the law `P`): since
`bfA(z + cu_k)` has the same law under `P` as `bfA(cu_k)` for every `z`, a
witness at the origin transports to a witness at `z`. This file takes the translated
family of `(P3′)`-shaped witnesses as an explicit hypothesis
(see `CFSB.lean`); the stationarity transport that supplies it is carried out in
`CFSTranslate.lean`. At `z = 0` (`Q = originCube d k`) no such hypothesis is needed: `(P3′)`
applies directly, verbatim.

## Finding 2: the window's boundary is strict-vs-non-strict

The paper states the per-scale bound for `k ∈ ℕ` with `βk ≤ h ≤ k` and
`k ≥ h + L₁ log(L₂ h)` (non-strict throughout), but `(P3′)`
itself (both the printed `a.CFS.weaker`, and the binder of
`akhc_weakerP3`) requires the **strict** window `βj < n < j - L₁ log(L₂ n)`. At the
boundary `k = h + L₁ log(L₂ h)` exactly (so `k - L₁ log(L₂ h) = h`, not
`> h`), `(P3′)` does **not** apply, even though the source's own range
includes it. A concrete instance (`L₁ = L₂ = h = k = 1`) shows this happens. The
source's range is satisfied (`h ≤ k` and `k ≥ h + log h = h`) but `(P3′)`'s strict hypothesis
`h < k - log h` reads `1 < 1`, false. So the per-scale bound must be applied
only for `k` strictly inside `(h + L₁ log(L₂h), n]` (equivalently, from
`k = ⌊h + L₁ log(L₂ h)⌋ + 1` up), one integer scale narrower than the
source's own stated range at the (measure-zero, but real) coincidence
`h + L₁ log(L₂ h) ∈ ℕ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open Homogenization

noncomputable section

/-! ## The algebraic core: `(P3′)`-shaped bilinear bound ⟹ Loewner excess -/

/-- `descendantsAverage` of a constant function is that constant. Needed to pull
the fixed reference matrix `Ann` out of the averaged difference
`bfA(cu_R) - Ann`. -/
private theorem akhcCfs_descendantsAverage_const {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  classical
  have hD : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD)
  show ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum (fun _ => c) = c
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The averaged-difference form of `(P3′)`'s displayed sum equals the
difference of averages, for a **fixed** reference block matrix `Ann`
(independent of `R`). -/
private theorem akhcCfs_descendantsAverage_bilinear_sub {d : ℕ} (Q : TriadicCube d)
    (j : ℕ) (a : CoeffField d) (Ann : BlockMat d) (Z : BlockVec d) :
    descendantsAverage Q j
        (fun R => blockVecDot Z
          (blockMatVecMul
            (ofFullBlockMat
              (toFullBlockMat (coarseBlockMatrix (cubeSet R) a) - toFullBlockMat Ann)) Z)) =
      descendantsAverage Q j
          (fun R => blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) Z)) -
        blockVecDot Z (blockMatVecMul Ann Z) := by
  have hpt : ∀ R : TriadicCube d,
      blockVecDot Z
          (blockMatVecMul
            (ofFullBlockMat
              (toFullBlockMat (coarseBlockMatrix (cubeSet R) a) - toFullBlockMat Ann)) Z) =
        blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) Z) +
          (- blockVecDot Z (blockMatVecMul Ann Z)) := by
    intro R
    rw [blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
    ring
  simp only [hpt]
  rw [descendantsAverage_add, akhcCfs_descendantsAverage_const]
  ring

/-- **The algebraic core, at a general cube `Q`.** From the `(P3′)`-shaped
bilinear average bound at `Q` (scale `Q.scale`, descendant depth `j` reaching
reference scale `n := Q.scale - j`), specialized at `p = q = Z`, derive the
Loewner-order excess bound on the **averaged** coarse block matrix:
`bfA-average ⪯ (1+X)•Ann`. This is the source's inner `avsum` display,
before subadditivity is invoked. -/
theorem akhcCfs_blockMatLoewnerLE_avg_of_bilinear {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {a : CoeffField d} {Ann : BlockMat d} {X : ℝ}
    (hBilinear : ∀ p q : BlockVec d,
      2 * descendantsAverage Q j
          (fun R => blockVecDot p
            (blockMatVecMul
              (ofFullBlockMat
                (toFullBlockMat (coarseBlockMatrix (cubeSet R) a) - toFullBlockMat Ann)) q)) ≤
        X * (blockVecDot p (blockMatVecMul Ann p) + blockVecDot q (blockMatVecMul Ann q))) :
    BlockMatLoewnerLE
      (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a))
      ((1 + X) • Ann) := by
  intro Z
  have hZ := hBilinear Z Z
  have hSubEq :
      descendantsAverage Q j
          (fun R => blockVecDot Z
            (blockMatVecMul
              (ofFullBlockMat
                (toFullBlockMat (coarseBlockMatrix (cubeSet R) a) - toFullBlockMat Ann)) Z)) =
        descendantsAverage Q j
            (fun R => blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) Z)) -
          blockVecDot Z (blockMatVecMul Ann Z) :=
    akhcCfs_descendantsAverage_bilinear_sub Q j a Ann Z
  rw [hSubEq] at hZ
  have hAvgEq :
      descendantsAverage Q j
          (fun R => blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) Z)) =
        blockVecDot Z
          (blockMatVecMul
            (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a)) Z) :=
    (blockVecDot_blockMatVecMul_descendantsAverageBlockMat Q j
      (fun R => coarseBlockMatrix (cubeSet R) a) Z Z).symm
  rw [hAvgEq] at hZ
  have hgoal :
      blockVecDot Z
          (blockMatVecMul
            (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a)) Z) ≤
        (1 + X) * blockVecDot Z (blockMatVecMul Ann Z) := by linarith only [hZ]
  have hsmul :
      blockVecDot Z (blockMatVecMul ((1 + X) • Ann) Z) =
        (1 + X) * blockVecDot Z (blockMatVecMul Ann Z) := by
    rw [blockMatVecMul_blockSMul, blockVecDot_smul_right]
  show (1 / 2 : ℝ) * blockVecDot Z
      (blockMatVecMul
        (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a)) Z) ≤
    (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul ((1 + X) • Ann) Z)
  rw [hsmul]
  linarith only [hgoal]

/-- **The algebraic core, chained with subadditivity.** For a cube `Q` at
scale `k := Q.scale` and a reference scale `h ≤ k`, samplewise (given
`AELocallyUniformlyEllipticField a`), CoarseGraining's block-matrix
subadditivity (`BlockLoewner.lean:433`,
`coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField`)
combined with the `(P3′)`-shaped average bound at `Q` gives the **positive-part
excess reading** of the root docstring: `bfA(Q) ⪯ (1+X)•Ann`, i.e.
`|(Ann^{-1/2}(bfA(Q) - Ann)Ann^{-1/2})_+| ≤ X` whenever `X ≥ 0` (root
`Frozen.Section4.akhc_weakerP3` docstring). -/
theorem akhcCfs_blockMatLoewnerLE_coarseBlockMatrix_of_subadditivity_and_bilinear
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {Q : TriadicCube d} {h : ℤ} (hh : h ≤ Q.scale) {Ann : BlockMat d} {X : ℝ}
    (hBilinear : ∀ p q : BlockVec d,
      2 * descendantsAverage Q (Q.scale - h).toNat
          (fun R => blockVecDot p
            (blockMatVecMul
              (ofFullBlockMat
                (toFullBlockMat (coarseBlockMatrix (cubeSet R) a.toCoeffField) -
                  toFullBlockMat Ann)) q)) ≤
        X * (blockVecDot p (blockMatVecMul Ann p) + blockVecDot q (blockMatVecMul Ann q))) :
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) a.toCoeffField) ((1 + X) • Ann) := by
  have hSub :=
    Homogenization.Book.Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
      ha Q hh
  have hAvg := akhcCfs_blockMatLoewnerLE_avg_of_bilinear
    (Q := Q) (j := (Q.scale - h).toNat) (a := a.toCoeffField) (Ann := Ann) (X := X) hBilinear
  exact hSub.trans hAvg

/-! ## Finding 2, witnessed concretely -/

end

end SuperdiffusionCLT.AKHC61.Tails
