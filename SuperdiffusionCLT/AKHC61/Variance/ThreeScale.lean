/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.BlockAverageBound
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The three-scale variance comparison `e.variance.HC`: deterministic core

The statement `e.variance.HC` of [AK] compares, at three scales
`k ≤ n` and a normalizing scale `m`, the second moment of
`bfAhom_m^{-1/2} bfA(cu_n) bfAhom_m^{-1/2} - I` with the second moment of the
*linear* descendant average
avsum_z bfAhom_m^{-1/2} (bfA(z + cu_k) - bfAhom(cu_k)) bfAhom_m^{-1/2} plus
deterministic comparisons of `bfAhom(cu_j)` (`j ∈ {k, n}`) with bfAhom_m.

This file is the samplewise algebra of that argument. The normalizing matrix
is a positive diagonal `W = diag w` (the reading of bfAhom_m once the
isotropy facts make it diagonal), and the matrix norm is the Frobenius norm of
`W^{-1/2} M W^{-1/2}`, written without square roots as
`akhcRelFrobSq w M = ∑ α β, M α β ^ 2 / (w α * w β)`. The operator norm is
bounded by this Frobenius norm, and the two are comparable up to `2d`.

The printed argument runs samplewise as follows. With
`D := avsum_z bfA(z+cu_k) - bfA(cu_n)`, which is positive semidefinite by
subadditivity, `bfA(cu_n) - W = -D + (avsum_z bfA(z+cu_k) - bfAhom_k) + (bfAhom_k - W)`.
The Frobenius norm of a symmetric positive semidefinite matrix is bounded by
its trace, `X := tr_w D ≥ 0`, and `X ≤ tr_w (avsum_z bfA(z+cu_k))` because
`bfA(cu_n) ⪰ 0`. From `X ≤ c + t` with `c = tr_w bfAhom_k` and `t` the trace
of the linear average one gets `X² ≤ 2 c X + t²` (this replaces the printed
`X² ≤ 2X + 4(X-1)_+²`), and `t² ≤ 2d · |linear average|²`. The expectation
of `X` is the deterministic `tr_w (bfAhom_k - bfAhom_n)`, which is the printed
`E|N| ≤ 2d |E N|` step.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization

noncomputable section

variable {d : ℕ}

/-- The squared Frobenius norm of `W^{-1/2} M W^{-1/2}` for the diagonal
matrix `W = diag w`, written entrywise: `∑ α β, M α β ^ 2 / (w α * w β)`. -/
def akhcRelFrobSq (w : BlockCoord d → ℝ) (M : BlockCoord d → BlockCoord d → ℝ) : ℝ :=
  ∑ α, ∑ β, M α β ^ 2 / (w α * w β)

/-- The trace of `W^{-1/2} M W^{-1/2}` for the diagonal matrix `W = diag w`:
`∑ α, M α α / w α`. -/
def akhcRelTrace (w : BlockCoord d → ℝ) (M : BlockCoord d → BlockCoord d → ℝ) : ℝ :=
  ∑ α, M α α / w α

/-- The entry function of `M - W` for `W = diag w`. -/
def akhcSubDiag (M : BlockMat d) (w : BlockCoord d → ℝ) : BlockCoord d → BlockCoord d → ℝ :=
  fun α β => blockMatEntry M α β - if α = β then w α else 0

theorem akhc_relFrobSq_nonneg {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (M : BlockCoord d → BlockCoord d → ℝ) : 0 ≤ akhcRelFrobSq w M := by
  unfold akhcRelFrobSq
  refine Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun β _ => ?_
  exact div_nonneg (sq_nonneg _) (mul_pos (hw α) (hw β)).le

/-- `card (BlockCoord d) = 2 d`. -/
theorem akhc_card_blockCoord : Fintype.card (BlockCoord d) = 2 * d := by
  simp [BlockCoord, Fintype.card_sum, two_mul]

/-- **The `2 × 2` minor bound** for a symmetric block matrix whose doubled
quadratic form is nonnegative: `M_{αβ}² ≤ M_{αα} M_{ββ}`. -/
theorem akhc_sq_blockMatEntry_le_mul_diag {D : BlockMat d}
    (hsymm : IsSymmetricBlockMat D)
    (hpos : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul D X))
    (α β : BlockCoord d) :
    blockMatEntry D α β ^ 2 ≤ blockMatEntry D α α * blockMatEntry D β β := by
  have hq : ∀ c : ℝ, 0 ≤ blockMatEntry D α α * (c * c) +
      (blockMatEntry D β α + blockMatEntry D α β) * c + blockMatEntry D β β := by
    intro c
    have h := hpos (blockBasis β + c • blockBasis α)
    rw [SuperdiffusionCLT.Section2.Annealed.blockQuadratic_add_smul, blockBasis_pairing,
      blockBasis_pairing, blockBasis_pairing, blockBasis_pairing] at h
    linarith only [h]
  have hdisc := discrim_le_zero hq
  have hsym := hsymm β α
  rw [discrim, hsym] at hdisc
  linarith only [hdisc]

/-- **Frobenius norm is bounded by the trace** for a symmetric positive
semidefinite block matrix, in the `W`-relative form. -/
theorem akhc_relFrobSq_le_relTrace_sq {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    {D : BlockMat d} (hsymm : IsSymmetricBlockMat D)
    (hpos : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul D X)) :
    akhcRelFrobSq w (blockMatEntry D) ≤ akhcRelTrace w (blockMatEntry D) ^ 2 := by
  unfold akhcRelFrobSq akhcRelTrace
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
  have hwαβ : 0 < w α * w β := mul_pos (hw α) (hw β)
  rw [div_mul_div_comm]
  exact div_le_div_of_nonneg_right (akhc_sq_blockMatEntry_le_mul_diag hsymm hpos α β) hwαβ.le

/-- The diagonal entries of a block matrix with nonnegative doubled quadratic
form are nonnegative. -/
theorem akhc_blockMatEntry_diag_nonneg {D : BlockMat d}
    (hpos : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul D X)) (α : BlockCoord d) :
    0 ≤ blockMatEntry D α α := by
  have h := hpos (blockBasis α)
  rwa [blockBasis_pairing] at h

theorem akhc_relTrace_nonneg {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α) {D : BlockMat d}
    (hpos : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul D X)) :
    0 ≤ akhcRelTrace w (blockMatEntry D) :=
  Finset.sum_nonneg fun α _ => div_nonneg (akhc_blockMatEntry_diag_nonneg hpos α) (hw α).le

/-- **Trace by Frobenius**: `(tr_w M)² ≤ 2d · |M|²_w` (Cauchy--Schwarz over the
`2d` diagonal entries). -/
theorem akhc_relTrace_sq_le {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (M : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelTrace w M ^ 2 ≤ (2 * d : ℝ) * akhcRelFrobSq w M := by
  unfold akhcRelTrace akhcRelFrobSq
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (BlockCoord d)))
    (f := fun α => M α α / w α)
  have hcard : ((Finset.univ : Finset (BlockCoord d)).card : ℝ) = 2 * d := by
    rw [Finset.card_univ, akhc_card_blockCoord]
    push_cast
    ring
  rw [hcard] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Finset.sum_le_sum fun α _ => ?_
  have hterm : (M α α / w α) ^ 2 = M α α ^ 2 / (w α * w α) := by
    rw [div_pow, sq (w α)]
  rw [hterm]
  exact Finset.single_le_sum (f := fun β => M α β ^ 2 / (w α * w β))
    (fun β _ => div_nonneg (sq_nonneg _) (mul_pos (hw α) (hw β)).le) (Finset.mem_univ α)

/-- `|x + y + z|²_w ≤ 3 (|x|²_w + |y|²_w + |z|²_w)`. -/
theorem akhc_relFrobSq_add_three_le {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (x y z : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobSq w (fun α β => x α β + y α β + z α β) ≤
      3 * akhcRelFrobSq w x + 3 * akhcRelFrobSq w y + 3 * akhcRelFrobSq w z := by
  unfold akhcRelFrobSq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => ?_
  have hwαβ : 0 < w α * w β := mul_pos (hw α) (hw β)
  have hsq : (x α β + y α β + z α β) ^ 2 ≤ 3 * x α β ^ 2 + 3 * y α β ^ 2 + 3 * z α β ^ 2 := by
    nlinarith only [sq_nonneg (x α β - y α β), sq_nonneg (y α β - z α β),
      sq_nonneg (x α β - z α β)]
  calc (x α β + y α β + z α β) ^ 2 / (w α * w β)
      ≤ (3 * x α β ^ 2 + 3 * y α β ^ 2 + 3 * z α β ^ 2) / (w α * w β) :=
        div_le_div_of_nonneg_right hsq hwαβ.le
    _ = 3 * (x α β ^ 2 / (w α * w β)) + 3 * (y α β ^ 2 / (w α * w β)) +
          3 * (z α β ^ 2 / (w α * w β)) := by ring

/-- **Change of normalization**: if `w' ≤ c w` coordinatewise then
`|M|²_w ≤ c² |M|²_{w'}`. -/
theorem akhc_relFrobSq_le_of_le_mul {w w' : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hw' : ∀ α, 0 < w' α) {c : ℝ} (hle : ∀ α, w' α ≤ c * w α)
    (M : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobSq w M ≤ c ^ 2 * akhcRelFrobSq w' M := by
  unfold akhcRelFrobSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun β _ => ?_
  have hwαβ : 0 < w α * w β := mul_pos (hw α) (hw β)
  have hw'αβ : 0 < w' α * w' β := mul_pos (hw' α) (hw' β)
  have hprod : w' α * w' β ≤ c ^ 2 * (w α * w β) := by
    have h1 := mul_le_mul (hle α) (hle β) (hw' β).le
      ((hw' α).le.trans (hle α))
    linarith only [h1]
  rw [mul_div_assoc', div_le_div_iff₀ hwαβ hw'αβ]
  have hM := sq_nonneg (M α β)
  calc M α β ^ 2 * (w' α * w' β) ≤ M α β ^ 2 * (c ^ 2 * (w α * w β)) :=
        mul_le_mul_of_nonneg_left hprod hM
    _ = c ^ 2 * M α β ^ 2 * (w α * w β) := by ring

/-- **The samplewise three-scale inequality** (the deterministic part of
`e.variance.HC`). For block matrices `An` (the parent
`bfA(cu_n)`), `Avg` (the descendant average `avsum_z bfA(z+cu_k)`) and `Ak`
(any reference, later `bfAhom(cu_k)`), with `An` symmetric positive
semidefinite, `Avg` symmetric and `An ⪯ Avg` (subadditivity),
`|An - W|²_w ≤ (3 + 6d) |Avg - Ak|²_w + 3 |Ak - W|²_w + 6 tr_w(Ak) · tr_w(Avg - An)`. -/
theorem akhc_threeScale_pointwise {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    {An Avg Ak : BlockMat d} (hsymAn : IsSymmetricBlockMat An)
    (hsymAvg : IsSymmetricBlockMat Avg)
    (hposAn : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul An X))
    (hsub : BlockMatLoewnerLE An Avg) :
    akhcRelFrobSq w (akhcSubDiag An w) ≤
      (3 + 6 * d) * akhcRelFrobSq w (fun α β => blockMatEntry Avg α β - blockMatEntry Ak α β) +
        3 * akhcRelFrobSq w (akhcSubDiag Ak w) +
        6 * akhcRelTrace w (blockMatEntry Ak) *
          akhcRelTrace w (fun α β => blockMatEntry Avg α β - blockMatEntry An α β) := by
  set D : BlockMat d := ofFullBlockMat (toFullBlockMat Avg - toFullBlockMat An) with hD
  have hDentry : blockMatEntry D = fun α β => blockMatEntry Avg α β - blockMatEntry An α β := by
    funext α β
    rw [hD, blockMatEntry_ofFullBlockMat]
    cases α <;> cases β <;> rfl
  have hsymD : IsSymmetricBlockMat D := by
    intro α β
    rw [hDentry]
    simp only [hsymAvg α β, hsymAn α β]
  have hposD : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul D X) := by
    intro X
    rw [hD, blockMatVecMul_ofFullBlockMat_sub, blockVecDot_sub_right]
    have h := hsub X
    linarith only [h]
  -- the trace `X := tr_w D` and the comparisons it satisfies
  set E : BlockCoord d → BlockCoord d → ℝ :=
    fun α β => blockMatEntry Avg α β - blockMatEntry Ak α β with hE
  set Xtr : ℝ := akhcRelTrace w (blockMatEntry D) with hXtr
  set c : ℝ := akhcRelTrace w (blockMatEntry Ak) with hc
  set t : ℝ := akhcRelTrace w E with ht
  have hX0 : 0 ≤ Xtr := akhc_relTrace_nonneg hw hposD
  have hAn0 : 0 ≤ akhcRelTrace w (blockMatEntry An) := akhc_relTrace_nonneg hw hposAn
  have hXsplit : Xtr + akhcRelTrace w (blockMatEntry An) = c + t := by
    rw [hXtr, hc, ht, hDentry]
    unfold akhcRelTrace
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hE]
    ring
  have hXle : Xtr ≤ c + t := by linarith only [hXsplit, hAn0]
  have hXsq : Xtr ^ 2 ≤ 2 * c * Xtr + t ^ 2 := by
    have h1 : Xtr * Xtr ≤ Xtr * (c + t) := mul_le_mul_of_nonneg_left hXle hX0
    nlinarith only [h1, sq_nonneg (Xtr - t)]
  have hFD : akhcRelFrobSq w (blockMatEntry D) ≤ Xtr ^ 2 :=
    akhc_relFrobSq_le_relTrace_sq hw hsymD hposD
  have ht2 : t ^ 2 ≤ (2 * d : ℝ) * akhcRelFrobSq w E := akhc_relTrace_sq_le hw E
  -- the entrywise identity `An - W = -D + E + (Ak - W)`
  have hsplit : akhcSubDiag An w =
      fun α β => (-blockMatEntry D α β) + E α β + akhcSubDiag Ak w α β := by
    funext α β
    rw [hDentry, hE]
    unfold akhcSubDiag
    ring
  have hneg : akhcRelFrobSq w (fun α β => -blockMatEntry D α β) =
      akhcRelFrobSq w (blockMatEntry D) := by
    unfold akhcRelFrobSq
    simp only [neg_sq]
  have h3 := akhc_relFrobSq_add_three_le hw (fun α β => -blockMatEntry D α β) E
    (akhcSubDiag Ak w)
  rw [hneg] at h3
  rw [hsplit, ← hDentry]
  have hEnn := akhc_relFrobSq_nonneg hw E
  nlinarith only [h3, hFD, hXsq, ht2, hEnn]

/-- Each normalized diagonal entry is bounded by the `W`-relative Frobenius norm:
if `|M|²_w ≤ ε²` then `|M_{αα} / w_α| ≤ ε`. -/
theorem akhc_abs_diag_div_le {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    {M : BlockCoord d → BlockCoord d → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hM : akhcRelFrobSq w M ≤ ε ^ 2) (α : BlockCoord d) :
    |M α α / w α| ≤ ε := by
  have hterm : M α α ^ 2 / (w α * w α) ≤ akhcRelFrobSq w M := by
    unfold akhcRelFrobSq
    refine le_trans ?_ (Finset.single_le_sum (f := fun γ => ∑ β, M γ β ^ 2 / (w γ * w β))
      (fun γ _ => Finset.sum_nonneg fun β _ =>
        div_nonneg (sq_nonneg _) (mul_pos (hw γ) (hw β)).le) (Finset.mem_univ α))
    exact Finset.single_le_sum (f := fun β => M α β ^ 2 / (w α * w β))
      (fun β _ => div_nonneg (sq_nonneg _) (mul_pos (hw α) (hw β)).le) (Finset.mem_univ α)
  have hsq : (M α α / w α) ^ 2 ≤ ε ^ 2 := by
    rw [div_pow, sq (w α)]
    exact hterm.trans hM
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hε] at h

/-- `|tr_w A - 2d| ≤ 2d ε` whenever `|A - W|²_w ≤ ε²`. -/
theorem akhc_abs_relTrace_sub_le {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    {A : BlockMat d} {ε : ℝ} (hε : 0 ≤ ε) (hA : akhcRelFrobSq w (akhcSubDiag A w) ≤ ε ^ 2) :
    |akhcRelTrace w (blockMatEntry A) - 2 * d| ≤ 2 * d * ε := by
  have hid : akhcRelTrace w (blockMatEntry A) - 2 * d =
      ∑ α, akhcSubDiag A w α α / w α := by
    unfold akhcRelTrace akhcSubDiag
    have hcard : (∑ _α : BlockCoord d, (1 : ℝ)) = 2 * d := by
      rw [Finset.sum_const, Finset.card_univ, akhc_card_blockCoord, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [← hcard, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [ite_true]
    field_simp [(hw α).ne']
  rw [hid]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsum : (∑ _α : BlockCoord d, ε) = 2 * d * ε := by
    rw [Finset.sum_const, Finset.card_univ, akhc_card_blockCoord, nsmul_eq_mul]
    push_cast
    ring
  rw [← hsum]
  exact Finset.sum_le_sum fun α _ => akhc_abs_diag_div_le hw hε hA α

/-- **The deterministic terms of `e.variance.HC` in AK.HC's form**: if
`|bfAhom(cu_j) - W|_w ≤ ε` for `j ∈ {k, n}` then
`3 |Ak - W|²_w + 6 tr_w(Ak) (tr_w(Ak) - tr_w(An)) ≤ 51 d² (ε + ε²)`
(the printed `40d max_j (|·| + |·|²)`, with the Frobenius norm). -/
theorem akhc_threeScale_deterministic_le [NeZero d] {w : BlockCoord d → ℝ}
    (hw : ∀ α, 0 < w α) {Ak An : BlockMat d} {ε : ℝ} (hε : 0 ≤ ε)
    (hk : akhcRelFrobSq w (akhcSubDiag Ak w) ≤ ε ^ 2)
    (hn : akhcRelFrobSq w (akhcSubDiag An w) ≤ ε ^ 2) :
    3 * akhcRelFrobSq w (akhcSubDiag Ak w) +
        6 * akhcRelTrace w (blockMatEntry Ak) *
          (akhcRelTrace w (blockMatEntry Ak) - akhcRelTrace w (blockMatEntry An)) ≤
      51 * (d : ℝ) ^ 2 * (ε + ε ^ 2) := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h1 := akhc_abs_relTrace_sub_le hw hε hk
  have h2 := akhc_abs_relTrace_sub_le hw hε hn
  set ck := akhcRelTrace w (blockMatEntry Ak)
  set cn := akhcRelTrace w (blockMatEntry An)
  have hck : |ck| ≤ 2 * d + 2 * d * ε := by
    have := abs_sub_abs_le_abs_sub ck (2 * d)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * d)] at this
    linarith only [this, h1]
  have hdiff : |ck - cn| ≤ 4 * d * ε := by
    have := abs_sub_le ck (2 * d) cn
    rw [abs_sub_comm (2 * (d : ℝ)) cn] at this
    linarith only [this, h1, h2]
  have hprod : ck * (ck - cn) ≤ (2 * d + 2 * d * ε) * (4 * d * ε) := by
    calc ck * (ck - cn) ≤ |ck * (ck - cn)| := le_abs_self _
      _ = |ck| * |ck - cn| := abs_mul _ _
      _ ≤ (2 * d + 2 * d * ε) * (4 * d * ε) :=
        mul_le_mul hck hdiff (abs_nonneg _) (by positivity)
  have hε2 : ε ^ 2 ≤ (d : ℝ) ^ 2 * ε ^ 2 := by
    have : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd
    nlinarith only [this, sq_nonneg ε]
  have hexp : (2 * d + 2 * d * ε) * (4 * d * ε) = 8 * (d : ℝ) ^ 2 * (ε + ε ^ 2) := by ring
  rw [hexp] at hprod
  have hdε : 0 ≤ (d : ℝ) ^ 2 * ε := by positivity
  rw [mul_assoc 6]
  linarith only [hprod, hk, hε2, hdε]

end

end SuperdiffusionCLT.AKHC61.Variance
