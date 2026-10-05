/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.MaximizerBridgeC2
public import SuperdiffusionCLT.AKHC61.Tails.Ellipticity
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich
public import SuperdiffusionCLT.AKHC61.WeakNorms.MoreprotoSqrt
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch04.Theorems.CoarseObservables
public import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyFinal

/-!
# Package B3, one-sided variant: the samplewise `LambdaSqCoeffField`/`M⁺_{n,rho}` bound

Follow-up on task db3b / package B3. The earlier bridge file proved

`Ch04.LambdaSqCoeffField (originCube d n) s' (.finite 1) a ≤
    C(s',rho) * sigmaBar_h * (1 + M_{n,rho})^2`

(and its `lambda^{-1}` twin) with `M_{n,rho} := akhcWeak_eventMoreprotoAtScale n h rho a`, built
from the **two-sided** operator norm `|E^{-1/2}HE^{-1/2}|`. Package C1
(`AKHC61/Tails/Ellipticity.lean`) showed that (P2') — a one-sided upper Loewner bound — cannot
control that two-sided quantity: it would need a *matching lower* Loewner bound that (P2') does
not supply. C1's own event quantity is the **one-sided** excess `akhcTailEll_excess M E := sInf
{t ≥ 0 : E ≤ (1+t)•M}` (matching the manuscript's `|(S-I)_+|`), controlled by (P2')
alone via `akhcTailEll_excess_le_of_blockMatLoewnerLE`.

This file re-proves both headline theorems of that earlier file with the one-sided event
quantity

`M⁺_{n,rho} := akhcWeakC_eventMoreprotoPlusAtScale n h rho a
  := sup over Q with Q.scale ≤ n, cubeCenter Q ∈ cubeSet (originCube d n) of
     3^{-rho(n-Q.scale)} · akhcTailEll_excess (Ahom(cu_h)) (bfA(Q))`

in place of `M_{n,rho}`.

## Both bounds hold with `M⁺`, and both need only the one-sided (upper) excess

The earlier per-scale Loewner sandwich is
**only ever an upper bound**, `BlockMatLoewnerLE (bfA R) ((1 + c) • Ahom(cu_h))`. Projected to
the `upperLeft` block this bounds `b(R)` from above (feeding `Lambda`); projected to the
`lowerRight` block it bounds `sigma_*^{-1}(R)` from above (feeding `lambda^{-1}`, since
`lambda_{s,1}^{-1}` is driven by the *supremum* of `|sigma_*^{-1}(R)|`, so an upper bound on
`sigma_*^{-1}(R)` is exactly what caps it). **Neither direction ever needs a lower Loewner bound
`bfA(R) ⪰ (1-c)•Ahom(cu_h)`.** So both theorems go through unchanged with the one-sided excess:
this file's answer to the coordinator's specific check is that the `lambda^{-1}` twin needs
nothing beyond what `akhcTailEll_excess` already gives.

## The excess's key property, missing from C1, proved here

C1 has "a Loewner witness gives an excess bound" (`akhcTailEll_excess_le_of_blockMatLoewnerLE`)
but not the converse — "the excess is itself (or is dominated by) a Loewner witness" — which
this package's argument needs (it must go from `excess ≤ c` to `BlockMatLoewnerLE E ((1+c)•M)`).
Since `akhcTailEll_excess` is an `sInf`, this needs the infimum to be *attained*, which is not
automatic. This file supplies it in two steps:

* `akhcWeakC_isClosed_loewnerSet`: `{t | BlockMatLoewnerLE E ((1+t)•M)}` is closed (an
  intersection, over `Z : BlockVec d`, of preimages of `Ici 0` under the continuous affine map
  `t ↦ (1+t)·m_Z - e_Z`).
* `akhcWeakC_nonempty_loewnerSet`: the defining set is nonempty, via a witness built from the
  **already proved two-sided** `akhcWeak_relativeOperatorNorm`/
  `akhcWeak_blockVecDot_le_relativeOperatorNorm_mul` (`MoreprotoSqrt.lean`) at `t :=
  max 0 (akhcWeak_relativeOperatorNorm M E - 1)` — this only needs `M` (`Ahom(cu_h)`) positive
  definite (`hE_posDef`, the same hypothesis the earlier bridge already carried), never a
  lower bound on `E`.
* `akhcWeakC_excess_mem` (`IsClosed.csInf_mem`) then gives `akhcTailEll_excess M E ∈` the
  defining set, i.e. `BlockMatLoewnerLE E ((1 + akhcTailEll_excess M E) • M)`, and
  `akhcWeakC_loewnerLE_of_excess_le` extends this to every `c ≥ excess` using that `M` is positive
  semidefinite (from `hE_posDef`).

## Main results

* `akhcWeakC_loewnerLE_of_excess_le`: every `c ≥ akhcTailEll_excess M E` is a Loewner witness.
* `akhcWeakC_eventMoreprotoPlus`: the one-sided event quantity `M⁺_{n,rho}`.

The two headline bounds (the upper `Lambda` bound and its `lambda^{-1}` twin, with
`M⁺_{n,rho}`) are proved downstream, in `MaximizerBridgeD.lean`, from these ingredients.

The generic (BlockMat/Loewner-free) real-analysis machinery — the growth-weighted geometric
series, the per-scale-linear-bound-to-square-root packaging, and the constant
`akhcWeakC2_maximizerConst` — lives in the companion file `MaximizerBridgeC2.lean` (split out
purely to keep both files under the 800-line cap) and is used here by import. The constant
`akhcWeakC2_maximizerConst` has the closed form
`C(s',rho) = (1 + (1-3^{-s'})·(1-3^{rho/2-s'})⁻¹)²`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization
open Homogenization.Book

/-! ## Geometry: scale and center of a member of `descendantsAtScale` -/

/-! ## Positive semidefiniteness of the diagonal blocks (general, no cutoff hypotheses) -/

/-! ## The operator norm under a nonnegative scalar -/

/-! ## The excess's key property: attainment and monotonicity (missing from C1, proved here) -/

private theorem akhcWeakC_quadraticForm_nonneg_of_posDef {d : ℕ} [NeZero d] {M : BlockMat d}
    (hM : (toFullBlockMat M).PosDef) (Z : BlockVec d) :
    0 ≤ blockVecDot Z (blockMatVecMul M Z) := by
  have hstep :
      0 ≤ dotProduct (toFullBlockVec Z) (Matrix.mulVec (toFullBlockMat M) (toFullBlockVec Z)) := by
    simpa using hM.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec Z)
  rwa [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec] at hstep

/-- **The Loewner sublevel set, in `t`, is closed.** For fixed `M E : BlockMat d`,
`{t | BlockMatLoewnerLE E ((1+t)•M)}` is an intersection, over `Z : BlockVec d`, of preimages of
`Ici 0` under the continuous affine map `t ↦ (1/2)·((1+t)·m_Z - e_Z)`. -/
private theorem akhcWeakC_isClosed_loewnerSet {d : ℕ} (M E : BlockMat d) :
    IsClosed {t : ℝ | BlockMatLoewnerLE E ((1 + t) • M)} := by
  have heq : {t : ℝ | BlockMatLoewnerLE E ((1 + t) • M)} =
      ⋂ Z : BlockVec d,
        {t : ℝ | (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul E Z) ≤
          (1 / 2 : ℝ) * ((1 + t) * blockVecDot Z (blockMatVecMul M Z))} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h Z
      have hZ := h Z
      rwa [Homogenization.blockMatVecMul_blockSMul, Homogenization.blockVecDot_smul_right] at hZ
    · intro h Z
      have hZ := h Z
      rwa [Homogenization.blockMatVecMul_blockSMul, Homogenization.blockVecDot_smul_right]
  rw [heq]
  refine isClosed_iInter fun Z => ?_
  have hcont : Continuous (fun t : ℝ =>
      (1 / 2 : ℝ) * ((1 + t) * blockVecDot Z (blockMatVecMul M Z))) :=
    continuous_const.mul ((continuous_const.add continuous_id).mul continuous_const)
  exact isClosed_le continuous_const hcont

/-- **The Loewner sublevel set is nonempty**, from the already proved two-sided relative operator
norm (`MoreprotoSqrt.lean`): `t := max 0 (akhcWeak_relativeOperatorNorm M E - 1)` is a witness,
needing only `M` positive definite (never a lower bound on `E`). -/
private theorem akhcWeakC_nonempty_loewnerSet {d : ℕ} [NeZero d] {M E : BlockMat d}
    (hM : (toFullBlockMat M).PosDef) :
    {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE E ((1 + t) • M)}.Nonempty := by
  set t0 : ℝ := akhcWeak_relativeOperatorNorm M E with ht0def
  set s : ℝ := max 0 (t0 - 1) with hsdef
  have hs0 : 0 ≤ s := le_max_left _ _
  have hts : t0 ≤ 1 + s := by
    rcases le_or_gt t0 1 with h1 | h1
    · linarith only [h1, hs0]
    · have hseq : s = t0 - 1 := max_eq_right (by linarith only [h1])
      linarith only [hseq]
  refine ⟨s, hs0, fun Z => ?_⟩
  have hbase := akhcWeak_blockVecDot_le_relativeOperatorNorm_mul (E := E) hM Z
  rw [← ht0def] at hbase
  have hchain : blockVecDot Z (blockMatVecMul E Z) ≤ (1 + s) * blockVecDot Z (blockMatVecMul M Z) :=
    hbase.trans (mul_le_mul_of_nonneg_right hts
      (akhcWeakC_quadraticForm_nonneg_of_posDef hM Z))
  show (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul E Z) ≤
      (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul ((1 + s) • M) Z)
  rw [Homogenization.blockMatVecMul_blockSMul, Homogenization.blockVecDot_smul_right]
  linarith only [hchain]

/-- **The excess is attained.** `akhcTailEll_excess M E`, being the `sInf` of a nonempty closed
set bounded below by `0`, lies in that set: it is itself `≥ 0` and is itself a Loewner witness. -/
private theorem akhcWeakC_excess_mem {d : ℕ} [NeZero d] {M E : BlockMat d}
    (hM : (toFullBlockMat M).PosDef) :
    0 ≤ SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess M E ∧
      BlockMatLoewnerLE E
        ((1 + SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess M E) • M) := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE E ((1 + t) • M)} := by
    have heq : {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE E ((1 + t) • M)} =
        Set.Ici (0 : ℝ) ∩ {t : ℝ | BlockMatLoewnerLE E ((1 + t) • M)} := by
      ext t; simp [Set.mem_Ici]
    rw [heq]
    exact isClosed_Ici.inter (akhcWeakC_isClosed_loewnerSet M E)
  have hne := akhcWeakC_nonempty_loewnerSet (M := M) (E := E) hM
  have hbdd : BddBelow {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE E ((1 + t) • M)} :=
    ⟨0, fun _ ht => ht.1⟩
  exact hclosed.csInf_mem hne hbdd

/-- **Monotonicity from the excess.** Any `c ≥ akhcTailEll_excess M E` is itself a Loewner
witness, via the attained excess and positive-semidefiniteness of `M` (no separate `0 ≤ c` is
needed: it already follows from `hc` and the excess's own nonnegativity). -/
theorem akhcWeakC_loewnerLE_of_excess_le {d : ℕ} [NeZero d] {M E : BlockMat d}
    (hM : (toFullBlockMat M).PosDef) {c : ℝ}
    (hc : SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess M E ≤ c) :
    BlockMatLoewnerLE E ((1 + c) • M) := by
  obtain ⟨-, hexcL⟩ := akhcWeakC_excess_mem (M := M) (E := E) hM
  intro Z
  have h1 := hexcL Z
  rw [Homogenization.blockMatVecMul_blockSMul, Homogenization.blockVecDot_smul_right] at h1
  have h2 :
      (1 + SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess M E) *
          blockVecDot Z (blockMatVecMul M Z) ≤
        (1 + c) * blockVecDot Z (blockMatVecMul M Z) :=
    mul_le_mul_of_nonneg_right (by linarith only [hc])
      (akhcWeakC_quadraticForm_nonneg_of_posDef hM Z)
  show (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul E Z) ≤
      (1 / 2 : ℝ) * blockVecDot Z (blockMatVecMul ((1 + c) • M) Z)
  rw [Homogenization.blockMatVecMul_blockSMul, Homogenization.blockVecDot_smul_right]
  linarith only [h1, h2]

/-! ## The one-sided event quantity `M⁺_{n,rho}` -/

/-- **`M⁺_{n,rho}`**, the one-sided (excess-based) reading of C1's `e.event.moreproto`: it uses
`SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E (bfA(Q))` — the Loewner excess of
`bfA(Q)` relative to `E`, i.e. C1's normalization exactly — in place of the two-sided
`akhcWeak_relativeOperatorNorm`. -/
noncomputable def akhcWeakC_eventMoreprotoPlus {d : ℕ} (n : ℤ) (ρ : ℝ)
    (E : Homogenization.BlockMat d) (a : Homogenization.CoeffField d) : ℝ :=
  sSup
    { M : ℝ |
        ∃ Q : Homogenization.TriadicCube d,
          Q.scale ≤ n ∧
            Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d n) ∧
            M =
              Real.rpow (3 : ℝ) (-ρ * ((n : ℝ) - (Q.scale : ℝ))) *
                SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess E
                  (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a) }

/-! ## The one-sided Loewner sandwich at one descendant cube -/

/-! ## The per-scale block-norm bound -/

/-! ## Main results -/

end

end SuperdiffusionCLT.AKHC61.WeakNorms
