/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.Proto
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `e.variance.proto`, part 1: the matrix algebra

Proof of `e.variance.proto` of [AK]. This file proves the purely
algebraic core of the quenched bound, for abstract symmetric matrices written
entrywise on `BlockCoord d`:

* `akhcProtoC_relFrobSq_le_of_qf_le`: Frobenius monotonicity, `0 ≤ D ≤ Y`
  (as quadratic forms) implies `|D|_w ≤ |Y|_w`;
* `akhcProtoC_relFrobNorm_le_add`: the triangle inequality for `|·|_w`;
* `akhcProtoC_qf_burrito`: the chain `e.big.burrito` and `e.burrito.wrap` of [AK]
  in a form with no matrix inverse. Writing `An = bfA(cu_n)`,
  `Abar = avsum_z bfA(z + cu_k)`, `B = diag b`, the two inputs are
  subadditivity `An ≤ Abar` and the doubled-response positivity
  `2 x·R y ≤ x·An x + y·An y` (which is the ordering `bfA_* ≤ bfA`,
  in the form it is actually used: `bfA_*^{-1} = R bfA R` and
  `[[An, -I], [-I, R An R]] ≥ 0`). Testing the second one against
  `y = B⁻¹ R x` replaces the sample-mean/harmonic-mean identity
  and gives `0 ≤ Abar - An ≤ E + X + (B⁻¹R)ᵀ X (B⁻¹R)` with `X = Abar - B` and
  `E = diag(b - 1/(b∘R))`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The quadratic form `x ↦ ∑ α β, x α M α β x β` of an entrywise matrix. -/
def akhcProtoCQf (M : BlockCoord d → BlockCoord d → ℝ) (x : BlockCoord d → ℝ) : ℝ :=
  ∑ α, ∑ β, x α * M α β * x β

theorem akhcProtoCQf_sub (M N : BlockCoord d → BlockCoord d → ℝ) (x : BlockCoord d → ℝ) :
    akhcProtoCQf (fun α β => M α β - N α β) x = akhcProtoCQf M x - akhcProtoCQf N x := by
  unfold akhcProtoCQf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem akhcProtoCQf_add (M N : BlockCoord d → BlockCoord d → ℝ) (x : BlockCoord d → ℝ) :
    akhcProtoCQf (fun α β => M α β + N α β) x = akhcProtoCQf M x + akhcProtoCQf N x := by
  unfold akhcProtoCQf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

/-- The quadratic form of a diagonal matrix. -/
theorem akhcProtoCQf_diag (e : BlockCoord d → ℝ) (x : BlockCoord d → ℝ) :
    akhcProtoCQf (fun α β => if α = β then e α else 0) x = ∑ α, e α * x α ^ 2 := by
  unfold akhcProtoCQf
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single α (fun β _ hβ => by
      simp only [ite_eq_right (Ne.symm hβ), mul_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ α) h)]
  simp only [ite_true]
  ring

/-! ## Frobenius monotonicity -/

/-- `tr(P M) ≥ 0` for positive semidefinite real matrices. -/
theorem akhcProtoC_trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {P M : Matrix n n ℝ} (hP : P.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ (P * M).trace := by
  have hP0 : (0 : Matrix n n ℝ) ≤ P := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact hP
  set S := CFC.sqrt P with hS
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP0
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hSH : Sᴴ = S := hSpsd.1
  have h1 : (P * M).trace = (Sᴴ * M * S).trace := by
    rw [← hSS, hSH, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h1]
  exact (hM.conjTranspose_mul_mul_same S).trace_nonneg

/-- The `W^{-1/2} M W^{-1/2}` normalization, as a Mathlib matrix. -/
def akhcProtoCNormalize (w : BlockCoord d → ℝ) (M : BlockCoord d → BlockCoord d → ℝ) :
    Matrix (BlockCoord d) (BlockCoord d) ℝ :=
  Matrix.of fun α β => (Real.sqrt (w α))⁻¹ * M α β * (Real.sqrt (w β))⁻¹

theorem akhcProtoC_dotProduct_normalize (w : BlockCoord d → ℝ)
    (M : BlockCoord d → BlockCoord d → ℝ) (x : BlockCoord d → ℝ) :
    x ⬝ᵥ (akhcProtoCNormalize w M *ᵥ x) =
      akhcProtoCQf M (fun α => (Real.sqrt (w α))⁻¹ * x α) := by
  unfold akhcProtoCQf akhcProtoCNormalize
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem akhcProtoC_posSemidef_normalize (w : BlockCoord d → ℝ)
    {M : BlockCoord d → BlockCoord d → ℝ} (hsym : ∀ α β, M α β = M β α)
    (hpos : ∀ x, 0 ≤ akhcProtoCQf M x) :
    (akhcProtoCNormalize w M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun α β => ?_
    simp only [akhcProtoCNormalize, Matrix.of_apply, star_trivial]
    rw [hsym β α]
    ring
  · rw [star_trivial, akhcProtoC_dotProduct_normalize]
    exact hpos _

theorem akhcProtoC_trace_normalize_sq (w : BlockCoord d → ℝ) (hw : ∀ α, 0 < w α)
    {M : BlockCoord d → BlockCoord d → ℝ} (hsym : ∀ α β, M α β = M β α) :
    (akhcProtoCNormalize w M * akhcProtoCNormalize w M).trace = akhcRelFrobSq w M := by
  unfold akhcRelFrobSq
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, akhcProtoCNormalize,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hsym β α]
  have ha : (Real.sqrt (w α))⁻¹ * (Real.sqrt (w α))⁻¹ = (w α)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (hw α).le]
  have hb : (Real.sqrt (w β))⁻¹ * (Real.sqrt (w β))⁻¹ = (w β)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (hw β).le]
  calc (Real.sqrt (w α))⁻¹ * M α β * (Real.sqrt (w β))⁻¹ *
        ((Real.sqrt (w β))⁻¹ * M α β * (Real.sqrt (w α))⁻¹)
      = M α β ^ 2 * ((Real.sqrt (w α))⁻¹ * (Real.sqrt (w α))⁻¹) *
          ((Real.sqrt (w β))⁻¹ * (Real.sqrt (w β))⁻¹) := by ring
    _ = M α β ^ 2 / (w α * w β) := by
        rw [ha, hb, div_eq_mul_inv, mul_inv, mul_assoc]

/-- **Frobenius monotonicity.** If `0 ≤ D ≤ Y` as quadratic forms (both
symmetric), then `|D|_w² ≤ |Y|_w²`: `tr D² ≤ tr DY ≤ tr Y²`. -/
theorem akhcProtoC_relFrobSq_le_of_qf_le {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    {D Y : BlockCoord d → BlockCoord d → ℝ} (hDs : ∀ α β, D α β = D β α)
    (hYs : ∀ α β, Y α β = Y β α) (hD0 : ∀ x, 0 ≤ akhcProtoCQf D x)
    (hDY : ∀ x, akhcProtoCQf D x ≤ akhcProtoCQf Y x) :
    akhcRelFrobSq w D ≤ akhcRelFrobSq w Y := by
  classical
  set ND := akhcProtoCNormalize w D
  set NY := akhcProtoCNormalize w Y
  have hND : ND.PosSemidef := akhcProtoC_posSemidef_normalize w hDs hD0
  have hsub : NY - ND = akhcProtoCNormalize w (fun α β => Y α β - D α β) := by
    ext α β
    simp only [NY, ND, akhcProtoCNormalize, Matrix.sub_apply, Matrix.of_apply]
    ring
  have hE : (NY - ND).PosSemidef := by
    rw [hsub]
    refine akhcProtoC_posSemidef_normalize w (fun α β => by rw [hYs α β, hDs α β])
      fun x => ?_
    rw [akhcProtoCQf_sub]
    exact sub_nonneg.mpr (hDY x)
  have hNY : NY.PosSemidef := by
    have h := hND.add hE
    rwa [add_sub_cancel] at h
  have h1 := akhcProtoC_trace_mul_nonneg hND hE
  have h2 := akhcProtoC_trace_mul_nonneg hNY hE
  rw [Matrix.mul_sub, Matrix.trace_sub, sub_nonneg] at h1 h2
  rw [← akhcProtoC_trace_normalize_sq w hw hDs, ← akhcProtoC_trace_normalize_sq w hw hYs]
  have h3 : (ND * NY).trace = (NY * ND).trace := Matrix.trace_mul_comm ND NY
  linarith only [h1, h2, h3]

/-! ## The triangle inequality for `|·|_w` -/

theorem akhcProtoC_relFrobNorm_eq_norm {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (M : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobNorm w M = ‖(WithLp.toLp 2 (fun p : BlockCoord d × BlockCoord d =>
      M p.1 p.2 / Real.sqrt (w p.1 * w p.2)) :
        EuclideanSpace ℝ (BlockCoord d × BlockCoord d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold akhcRelFrobNorm akhcRelFrobSq
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  simp only [Real.norm_eq_abs, sq_abs]
  rw [div_pow, Real.sq_sqrt (mul_pos (hw α) (hw β)).le]

/-- **Triangle inequality** for the `W`-relative Frobenius norm. -/
theorem akhcProtoC_relFrobNorm_le_add {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    {K M N : BlockCoord d → BlockCoord d → ℝ} (hK : ∀ α β, K α β = M α β + N α β) :
    akhcRelFrobNorm w K ≤ akhcRelFrobNorm w M + akhcRelFrobNorm w N := by
  rw [akhcProtoC_relFrobNorm_eq_norm hw K, akhcProtoC_relFrobNorm_eq_norm hw M,
    akhcProtoC_relFrobNorm_eq_norm hw N]
  refine le_of_eq_of_le ?_ (norm_add_le _ _)
  congr 1
  ext p
  simp only [PiLp.add_apply, hK, add_div]

/-- `|-M|_w = |M|_w`. -/
theorem akhcProtoC_relFrobNorm_neg (w : BlockCoord d → ℝ)
    (M : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobNorm w (fun α β => -M α β) = akhcRelFrobNorm w M := by
  unfold akhcRelFrobNorm akhcRelFrobSq
  simp only [neg_sq]

/-! ## The burrito chain without inverses -/

/-- `(B⁻¹R)ᵀ X (B⁻¹R)` entrywise, for `B = diag b` and `R` the block swap. -/
def akhcProtoCSwapConj (b : BlockCoord d → ℝ) (X : BlockCoord d → BlockCoord d → ℝ) :
    BlockCoord d → BlockCoord d → ℝ :=
  fun α β => X (Sum.swap α) (Sum.swap β) / (b (Sum.swap α) * b (Sum.swap β))

theorem akhcProtoC_sum_swap (f : BlockCoord d → ℝ) :
    ∑ α, f (Sum.swap α) = ∑ α, f α :=
  Equiv.sum_comp (Equiv.sumComm (Fin d) (Fin d)) f

theorem akhcProtoCQf_swapConj (b : BlockCoord d → ℝ) (hb : ∀ α, 0 < b α)
    (X : BlockCoord d → BlockCoord d → ℝ) (v : BlockCoord d → ℝ) :
    akhcProtoCQf (akhcProtoCSwapConj b X) v =
      akhcProtoCQf X (fun β => v (Sum.swap β) / b β) := by
  unfold akhcProtoCQf akhcProtoCSwapConj
  rw [← akhcProtoC_sum_swap]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← akhcProtoC_sum_swap]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [Sum.swap_swap]
  have h1 := (hb (Sum.swap α)).ne'
  have h2 := (hb (Sum.swap β)).ne'
  field_simp

theorem akhcProtoC_relFrobNorm_swapConj_le {w b : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hb : ∀ α, 0 < b α) (hcomp : ∀ α, w α ≤ b α ^ 2 * w (Sum.swap α))
    (X : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobNorm w (akhcProtoCSwapConj b X) ≤ akhcRelFrobNorm w X := by
  unfold akhcRelFrobNorm
  refine Real.sqrt_le_sqrt ?_
  unfold akhcRelFrobSq akhcProtoCSwapConj
  rw [← akhcProtoC_sum_swap]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [← akhcProtoC_sum_swap]
  refine Finset.sum_le_sum fun β _ => ?_
  simp only [Sum.swap_swap]
  have hα := hb α
  have hβ := hb β
  have hwα := hw (Sum.swap α)
  have hwβ := hw (Sum.swap β)
  have heq : (X α β / (b α * b β)) ^ 2 / (w (Sum.swap α) * w (Sum.swap β)) =
      X α β ^ 2 / ((b α ^ 2 * w (Sum.swap α)) * (b β ^ 2 * w (Sum.swap β))) := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (hw α) (hw β))
    (mul_le_mul (hcomp α) (hcomp β) (hw β).le (by positivity))


/-- **The burrito chain, quadratic-form version.** With `D = Abar - An`,
`X = Abar - diag b`, `E = diag(b - 1/(b∘R))`:
`x·D x ≤ x·E x + x·X x + x·((B⁻¹R)ᵀ X (B⁻¹R)) x`. -/
theorem akhcProtoC_qf_burrito {b : BlockCoord d → ℝ} (hb : ∀ α, 0 < b α)
    {An Abar : BlockCoord d → BlockCoord d → ℝ}
    (hsub : ∀ x, akhcProtoCQf An x ≤ akhcProtoCQf Abar x)
    (hstar : ∀ x y, 2 * ∑ α, x α * y (Sum.swap α) ≤ akhcProtoCQf An x + akhcProtoCQf An y)
    (v : BlockCoord d → ℝ) :
    akhcProtoCQf (fun α β => Abar α β - An α β) v ≤
      akhcProtoCQf (fun α β => if α = β then b α - (b (Sum.swap α))⁻¹ else 0) v +
        akhcProtoCQf (fun α β => Abar α β - if α = β then b α else 0) v +
        akhcProtoCQf (akhcProtoCSwapConj b
          (fun α β => Abar α β - if α = β then b α else 0)) v := by
  set X : BlockCoord d → BlockCoord d → ℝ :=
    fun α β => Abar α β - if α = β then b α else 0 with hX
  set u : BlockCoord d → ℝ := fun β => v (Sum.swap β) / b β with hu
  have hAbar : Abar = fun α β => X α β + (if α = β then b α else 0) := by
    funext α β
    simp only [hX, sub_add_cancel]
  have hS : ∑ α, v α * u (Sum.swap α) = ∑ α, (b (Sum.swap α))⁻¹ * v α ^ 2 := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hu, Sum.swap_swap]
    ring
  have hqu : ∑ β, b β * u β ^ 2 = ∑ α, (b (Sum.swap α))⁻¹ * v α ^ 2 := by
    rw [← akhcProtoC_sum_swap (fun β => b β * u β ^ 2)]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hu, Sum.swap_swap]
    have := (hb (Sum.swap α)).ne'
    field_simp
  have hAv : akhcProtoCQf Abar v = akhcProtoCQf X v + ∑ α, b α * v α ^ 2 := by
    rw [hAbar, akhcProtoCQf_add, akhcProtoCQf_diag]
  have hAu : akhcProtoCQf Abar u = akhcProtoCQf X u + ∑ β, b β * u β ^ 2 := by
    rw [hAbar, akhcProtoCQf_add, akhcProtoCQf_diag]
  have hE : akhcProtoCQf (fun α β => if α = β then b α - (b (Sum.swap α))⁻¹ else 0) v =
      ∑ α, b α * v α ^ 2 - ∑ α, (b (Sum.swap α))⁻¹ * v α ^ 2 := by
    rw [akhcProtoCQf_diag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hSC : akhcProtoCQf (akhcProtoCSwapConj b X) v = akhcProtoCQf X u :=
    akhcProtoCQf_swapConj b hb X v
  have h1 := hstar v u
  have h2 := hsub u
  rw [akhcProtoCQf_sub, hE, hSC]
  rw [hS] at h1
  rw [hAu, hqu] at h2
  rw [hAv]
  linarith only [h1, h2]

theorem akhcProtoC_swapConj_symm {b : BlockCoord d → ℝ}
    {X : BlockCoord d → BlockCoord d → ℝ} (hX : ∀ α β, X α β = X β α) (α β : BlockCoord d) :
    akhcProtoCSwapConj b X α β = akhcProtoCSwapConj b X β α := by
  unfold akhcProtoCSwapConj
  rw [hX, mul_comm]

/-- **The abstract quenched bound.** For symmetric `An ≤ Abar` satisfying the
doubled-response inequality, `b > 0`, `w > 0` and `w α ≤ b α² w (Rα)`:
`|An - W|_w ≤ |E|_w + 3|X|_w + |B - W|_w`. -/
theorem akhcProtoC_quenched_abstract {w b : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hb : ∀ α, 0 < b α) (hcomp : ∀ α, w α ≤ b α ^ 2 * w (Sum.swap α))
    {An Abar : BlockCoord d → BlockCoord d → ℝ} (hAnS : ∀ α β, An α β = An β α)
    (hAbarS : ∀ α β, Abar α β = Abar β α)
    (hsub : ∀ x, akhcProtoCQf An x ≤ akhcProtoCQf Abar x)
    (hstar : ∀ x y, 2 * ∑ α, x α * y (Sum.swap α) ≤ akhcProtoCQf An x + akhcProtoCQf An y) :
    akhcRelFrobNorm w (fun α β => An α β - if α = β then w α else 0) ≤
      akhcRelFrobNorm w (fun α β => if α = β then b α - (b (Sum.swap α))⁻¹ else 0) +
        3 * akhcRelFrobNorm w (fun α β => Abar α β - if α = β then b α else 0) +
        akhcRelFrobNorm w (fun α β => (if α = β then b α else 0) - if α = β then w α else 0) := by
  set X : BlockCoord d → BlockCoord d → ℝ :=
    fun α β => Abar α β - if α = β then b α else 0 with hX
  set E : BlockCoord d → BlockCoord d → ℝ :=
    fun α β => if α = β then b α - (b (Sum.swap α))⁻¹ else 0 with hEdef
  set D : BlockCoord d → BlockCoord d → ℝ := fun α β => Abar α β - An α β with hD
  set Y : BlockCoord d → BlockCoord d → ℝ :=
    fun α β => (E α β + X α β) + akhcProtoCSwapConj b X α β with hY
  have hXs : ∀ α β, X α β = X β α := by
    intro α β
    simp only [hX, hAbarS α β]
    by_cases h : α = β
    · subst h; rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  have hEs : ∀ α β, E α β = E β α := by
    intro α β
    simp only [hEdef]
    by_cases h : α = β
    · subst h; rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  have hDs : ∀ α β, D α β = D β α := by
    intro α β
    simp only [hD, hAbarS α β, hAnS α β]
  have hYs : ∀ α β, Y α β = Y β α := by
    intro α β
    simp only [hY, hEs α β, hXs α β, akhcProtoC_swapConj_symm hXs α β]
  have hD0 : ∀ x, 0 ≤ akhcProtoCQf D x := by
    intro x
    rw [hD, akhcProtoCQf_sub]
    exact sub_nonneg.mpr (hsub x)
  have hDY : ∀ x, akhcProtoCQf D x ≤ akhcProtoCQf Y x := by
    intro x
    rw [hY, akhcProtoCQf_add, akhcProtoCQf_add]
    exact akhcProtoC_qf_burrito hb hsub hstar x
  have hDle : akhcRelFrobNorm w D ≤ akhcRelFrobNorm w Y :=
    Real.sqrt_le_sqrt (akhcProtoC_relFrobSq_le_of_qf_le hw hDs hYs hD0 hDY)
  have hY1 : akhcRelFrobNorm w Y ≤
      akhcRelFrobNorm w (fun α β => E α β + X α β) +
        akhcRelFrobNorm w (akhcProtoCSwapConj b X) :=
    akhcProtoC_relFrobNorm_le_add hw fun α β => rfl
  have hY2 : akhcRelFrobNorm w (fun α β => E α β + X α β) ≤
      akhcRelFrobNorm w E + akhcRelFrobNorm w X :=
    akhcProtoC_relFrobNorm_le_add hw fun α β => rfl
  have hSC := akhcProtoC_relFrobNorm_swapConj_le hw hb hcomp X
  -- `An - W = -D + X + (B - W)`
  have hsplit1 : akhcRelFrobNorm w (fun α β => An α β - if α = β then w α else 0) ≤
      akhcRelFrobNorm w (fun α β => -D α β + X α β) +
        akhcRelFrobNorm w
          (fun α β => (if α = β then b α else 0) - if α = β then w α else 0) :=
    akhcProtoC_relFrobNorm_le_add hw fun α β => by simp only [hD, hX]; ring
  have hsplit2 : akhcRelFrobNorm w (fun α β => -D α β + X α β) ≤
      akhcRelFrobNorm w (fun α β => -D α β) + akhcRelFrobNorm w X :=
    akhcProtoC_relFrobNorm_le_add hw fun α β => rfl
  rw [akhcProtoC_relFrobNorm_neg] at hsplit2
  linarith only [hDle, hY1, hY2, hSC, hsplit1, hsplit2]

end

end SuperdiffusionCLT.AKHC61.Variance
