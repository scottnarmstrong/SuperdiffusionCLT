/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Homogenization.Ambient.BlockMatrix

/-!
# A finite-basis polarization bound for block-vector bilinear forms

Pure linear algebra, independent of the localization-average content: if
`Bf : BlockVec d → BlockVec d → ℝ` is bi-additive and bi-homogeneous (i.e.
`ℝ`-bilinear, stated pointwise rather than as a bundled `LinearMap`), and the
diagonal values `Bf (blockBasis α + blockBasis β) (blockBasis α + blockBasis β)`
are bounded by a nonnegative witness `wit (α, β)` for every pair of standard
basis coordinates `α, β : BlockCoord d`, then the quadratic form `x ↦ Bf x x`
is controlled **uniformly in `x`** by `blockVecDot x x` times a `d`-dependent
constant times the total witness mass `∑ p, wit p`.

This is the finite-dimensional fact behind `locAvg_uniform`
(`LocAvgUniformWitness.lean`): `localization_average`
supplies, for each test vector `Pvec` separately, an error witness whose
Orlicz amplitude is `C * ‖Pvec‖² * (...)`; testing it at only the finitely
many vectors `blockBasis α + blockBasis β` (`α, β` ranging over the `2d`
standard coordinates) and combining via polarization recovers a single
witness that works for *every* `Pvec` at once.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization

noncomputable section

/-- The finite basis-coordinate index set has `2 * d` elements. -/
theorem locAvgU_card_blockCoord (d : ℕ) :
    Fintype.card (BlockCoord d) = 2 * d := by
  simp [BlockCoord, Fintype.card_sum, two_mul]

/-- A `Vec d` value is the sum of its coordinates against the standard basis. -/
private theorem locAvgU_vec_eq_sum_single {d : ℕ} (y : Vec d) :
    y = ∑ i : Fin d, y i • (Pi.single i (1 : ℝ) : Vec d) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

/-- `Prod.fst` commutes with a finite sum of `BlockVec d` values. -/
private theorem locAvgU_fst_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → BlockVec d) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Prod.fst_add, ih]

/-- `Prod.snd` commutes with a finite sum of `BlockVec d` values. -/
private theorem locAvgU_snd_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → BlockVec d) :
    (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Prod.snd_add, ih]

/-- `x` decomposes over the standard block-coordinate basis, with coefficients
read off by `toFullBlockVec`. -/
theorem locAvgU_blockVec_eq_sum_basis {d : ℕ} (x : BlockVec d) :
    x = ∑ α : BlockCoord d, (toFullBlockVec x α) • blockBasis α := by
  apply Prod.ext
  · rw [Fintype.sum_sum_type, Prod.fst_add, locAvgU_fst_sum, locAvgU_fst_sum]
    have h1 : ∀ i : Fin d, ((toFullBlockVec x (Sum.inl i)) • blockBasis (Sum.inl i)).1
        = x.1 i • (Pi.single i (1 : ℝ) : Vec d) := by
      intro i; simp [blockBasis, toFullBlockVec]
    have h2 : ∀ i : Fin d, ((toFullBlockVec x (Sum.inr i)) • blockBasis (Sum.inr i)).1
        = (0 : Vec d) := by
      intro i; simp [blockBasis]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i)]
    simp [← locAvgU_vec_eq_sum_single]
  · rw [Fintype.sum_sum_type, Prod.snd_add, locAvgU_snd_sum, locAvgU_snd_sum]
    have h1 : ∀ i : Fin d, ((toFullBlockVec x (Sum.inl i)) • blockBasis (Sum.inl i)).2
        = (0 : Vec d) := by
      intro i; simp [blockBasis]
    have h2 : ∀ i : Fin d, ((toFullBlockVec x (Sum.inr i)) • blockBasis (Sum.inr i)).2
        = x.2 i • (Pi.single i (1 : ℝ) : Vec d) := by
      intro i; simp [blockBasis, toFullBlockVec]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i)]
    simp [← locAvgU_vec_eq_sum_single]

/-- `blockVecDot x x` is the sum of squared basis coefficients. -/
theorem locAvgU_blockVecDot_self_eq_sum_sq {d : ℕ} (x : BlockVec d) :
    blockVecDot x x = ∑ α : BlockCoord d, (toFullBlockVec x α) ^ 2 := by
  rw [← dotProduct_toFullBlockVec x x]
  simp [dotProduct, sq]

/-- Every basis coefficient's square is at most `blockVecDot x x`. -/
theorem locAvgU_sq_coeff_le {d : ℕ} (x : BlockVec d) (α : BlockCoord d) :
    (toFullBlockVec x α) ^ 2 ≤ blockVecDot x x := by
  rw [locAvgU_blockVecDot_self_eq_sum_sq]
  exact Finset.single_le_sum (fun β _ => sq_nonneg _) (Finset.mem_univ α)

/-- Consequently every pairwise product of coefficients is bounded in absolute
value by `blockVecDot x x`. -/
theorem locAvgU_abs_coeff_mul_le {d : ℕ} (x : BlockVec d) (α β : BlockCoord d) :
    |toFullBlockVec x α * toFullBlockVec x β| ≤ blockVecDot x x := by
  have ha := locAvgU_sq_coeff_le x α
  have hb := locAvgU_sq_coeff_le x β
  have hdotnn : (0 : ℝ) ≤ blockVecDot x x := blockVecDot_nonneg x
  have hsq : (toFullBlockVec x α * toFullBlockVec x β) ^ 2 ≤ blockVecDot x x ^ 2 := by
    have hprod : (toFullBlockVec x α) ^ 2 * (toFullBlockVec x β) ^ 2 ≤
        blockVecDot x x * blockVecDot x x :=
      mul_le_mul ha hb (sq_nonneg _) hdotnn
    calc (toFullBlockVec x α * toFullBlockVec x β) ^ 2
        = (toFullBlockVec x α) ^ 2 * (toFullBlockVec x β) ^ 2 := by ring
      _ ≤ blockVecDot x x * blockVecDot x x := hprod
      _ = blockVecDot x x ^ 2 := (sq (blockVecDot x x)).symm
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq hdotnn)

/-- Left-linearity of a bi-additive, bi-homogeneous `Bf` over a finite
weighted sum, for an arbitrary index type. -/
private theorem locAvgU_biform_left_sum {d : ℕ} {Bf : BlockVec d → BlockVec d → ℝ}
    (hadd_l : ∀ x y z, Bf (x + y) z = Bf x z + Bf y z)
    (hsmul_l : ∀ (c : ℝ) x y, Bf (c • x) y = c * Bf x y)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → BlockVec d) (y : BlockVec d) :
    Bf (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * Bf (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h := hsmul_l 0 (0 : BlockVec d) y
      simpa using h
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd_l, hsmul_l, ih]

/-- Right-linearity of a bi-additive, bi-homogeneous `Bf` over a finite
weighted sum, for an arbitrary index type. -/
private theorem locAvgU_biform_right_sum {d : ℕ} {Bf : BlockVec d → BlockVec d → ℝ}
    (hadd_r : ∀ x y z, Bf x (y + z) = Bf x y + Bf x z)
    (hsmul_r : ∀ (c : ℝ) x y, Bf x (c • y) = c * Bf x y)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → BlockVec d) (y : BlockVec d) :
    Bf y (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * Bf y (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h := hsmul_r 0 y (0 : BlockVec d)
      simpa using h
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd_r, hsmul_r, ih]

/-- **The finite-basis polarization bound.** A bi-additive, bi-homogeneous
`Bf : BlockVec d → BlockVec d → ℝ` whose values on the `2d` pairwise sums
`blockBasis α + blockBasis β` of standard basis vectors are dominated by a
nonnegative witness `wit` has its diagonal `Bf x x`, for **every** `x`,
dominated by `blockVecDot x x` times `(d+1)/2` times the total witness mass. -/
theorem locAvgU_biform_bound {d : ℕ} {Bf : BlockVec d → BlockVec d → ℝ}
    (hadd_l : ∀ x y z, Bf (x + y) z = Bf x z + Bf y z)
    (hadd_r : ∀ x y z, Bf x (y + z) = Bf x y + Bf x z)
    (hsmul_l : ∀ (c : ℝ) x y, Bf (c • x) y = c * Bf x y)
    (hsmul_r : ∀ (c : ℝ) x y, Bf x (c • y) = c * Bf x y)
    (wit : BlockCoord d × BlockCoord d → ℝ)
    (hwit_nonneg : ∀ p, 0 ≤ wit p)
    (hwit : ∀ α β : BlockCoord d,
      |Bf (blockBasis α + blockBasis β) (blockBasis α + blockBasis β)| ≤ wit (α, β))
    (x : BlockVec d) :
    |Bf x x| ≤ blockVecDot x x *
      (((4 : ℝ) * d + 1) * ∑ p : BlockCoord d × BlockCoord d, wit p) := by
  set c : BlockCoord d → ℝ := toFullBlockVec x with hc
  -- Step 1: the bilinear double-sum expansion of `Bf x x`.
  have step1 : Bf x x = ∑ α : BlockCoord d, c α * Bf (blockBasis α) x := by
    nth_rewrite 1 [locAvgU_blockVec_eq_sum_basis x]
    exact locAvgU_biform_left_sum hadd_l hsmul_l Finset.univ c blockBasis x
  have step2 : ∀ α : BlockCoord d,
      Bf (blockBasis α) x = ∑ β : BlockCoord d, c β * Bf (blockBasis α) (blockBasis β) := by
    intro α
    nth_rewrite 1 [locAvgU_blockVec_eq_sum_basis x]
    exact locAvgU_biform_right_sum hadd_r hsmul_r Finset.univ c blockBasis (blockBasis α)
  have hexpand : Bf x x = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      c α * c β * Bf (blockBasis α) (blockBasis β) := by
    rw [step1]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [step2 α, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    ring
  -- Step 2: the same expansion with `Bf`'s arguments swapped equals `Bf x x` too.
  have hswap : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      c α * c β * Bf (blockBasis β) (blockBasis α) =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d, c α * c β * Bf (blockBasis α) (blockBasis β) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun β _ => ?_)
    ring
  -- Step 3: `2 * Bf x x` in terms of the symmetrized pair sum `T α β`.
  have h2Bf : 2 * Bf x x = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      c α * c β * (Bf (blockBasis α) (blockBasis β) + Bf (blockBasis β) (blockBasis α)) := by
    have hexpand' : Bf x x = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        c α * c β * Bf (blockBasis β) (blockBasis α) := hexpand.trans hswap.symm
    have hsumadd : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        c α * c β * (Bf (blockBasis α) (blockBasis β) + Bf (blockBasis β) (blockBasis α)) =
        (∑ α : BlockCoord d, ∑ β : BlockCoord d, c α * c β * Bf (blockBasis α) (blockBasis β)) +
          (∑ α : BlockCoord d, ∑ β : BlockCoord d, c α * c β * Bf (blockBasis β) (blockBasis α)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      ring
    rw [hsumadd, ← hexpand, ← hexpand']
    ring
  -- Step 4: diagonal and symmetrized-pair bounds from `wit` (crude, undivided
  -- form: sharper by a factor of `4` on the diagonal, but far simpler to
  -- assemble, and the task only needs a bound up to a `d`-dependent constant).
  have hdiag : ∀ α : BlockCoord d, |Bf (blockBasis α) (blockBasis α)| ≤ wit (α, α) := by
    intro α
    have heq2 : blockBasis α + blockBasis α = (2 : ℝ) • blockBasis α := (two_smul ℝ _).symm
    have h4 : Bf (blockBasis α + blockBasis α) (blockBasis α + blockBasis α) =
        4 * Bf (blockBasis α) (blockBasis α) := by
      rw [heq2, hsmul_l, hsmul_r]; ring
    have hb := hwit α α
    rw [h4, abs_mul] at hb
    have h4abs : |(4 : ℝ)| = 4 := by norm_num
    rw [h4abs] at hb
    have habsnn : (0 : ℝ) ≤ |Bf (blockBasis α) (blockBasis α)| := abs_nonneg _
    linarith only [hb, habsnn]
  have hpair : ∀ α β : BlockCoord d,
      |Bf (blockBasis α) (blockBasis β) + Bf (blockBasis β) (blockBasis α)| ≤
        wit (α, β) + wit (α, α) + wit (β, β) := by
    intro α β
    have hsum4 : Bf (blockBasis α + blockBasis β) (blockBasis α + blockBasis β) =
        Bf (blockBasis α) (blockBasis α) +
          (Bf (blockBasis α) (blockBasis β) + Bf (blockBasis β) (blockBasis α)) +
          Bf (blockBasis β) (blockBasis β) := by
      rw [hadd_l, hadd_r, hadd_r]; ring
    have hb0 := hwit α β
    rw [hsum4] at hb0
    have hb := abs_le.mp hb0
    have hda := abs_le.mp (hdiag α)
    have hdb := abs_le.mp (hdiag β)
    exact abs_le.mpr ⟨by linarith only [hb.1, hda.1, hda.2, hdb.1, hdb.2],
      by linarith only [hb.2, hda.1, hda.2, hdb.1, hdb.2]⟩
  -- Step 5: assemble.
  have hcbound : ∀ α β : BlockCoord d, |c α * c β| ≤ blockVecDot x x := by
    intro α β; rw [hc]; exact locAvgU_abs_coeff_mul_le x α β
  have hdotnn : (0:ℝ) ≤ blockVecDot x x := blockVecDot_nonneg x
  have hbound2 : |2 * Bf x x| ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      blockVecDot x x * (wit (α, β) + wit (α, α) + wit (β, β)) := by
    rw [h2Bf]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun α _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun β _ => ?_)
    calc |c α * c β * (Bf (blockBasis α) (blockBasis β) + Bf (blockBasis β) (blockBasis α))|
        = |c α * c β| * |Bf (blockBasis α) (blockBasis β) + Bf (blockBasis β) (blockBasis α)| :=
          abs_mul _ _
      _ ≤ blockVecDot x x * (wit (α, β) + wit (α, α) + wit (β, β)) :=
          mul_le_mul (hcbound α β) (hpair α β) (abs_nonneg _) hdotnn
  -- Bound the total witness mass over the whole double sum by `(4d+1) * W`.
  have hcard : (Finset.univ : Finset (BlockCoord d)).card = 2 * d := by
    have := locAvgU_card_blockCoord d
    simpa [Finset.card_univ] using this
  set W : ℝ := ∑ p : BlockCoord d × BlockCoord d, wit p with hWdef
  have hWnn : (0 : ℝ) ≤ W := Finset.sum_nonneg (fun p _ => hwit_nonneg p)
  have hWprod : (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (α, β)) = W := by
    rw [hWdef, Fintype.sum_prod_type]
  have hdiagle : (∑ α : BlockCoord d, wit (α, α)) ≤ W := by
    have hstep : (∑ α : BlockCoord d, wit (α, α))
        = ∑ α : BlockCoord d, ∑ β : BlockCoord d, (if β = α then wit (α, β) else 0) := by
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [Finset.sum_ite_eq' Finset.univ α (fun β => wit (α, β))]
      simp
    rw [hstep, ← hWprod]
    refine Finset.sum_le_sum (fun α _ => ?_)
    refine Finset.sum_le_sum (fun β _ => ?_)
    split_ifs with h
    · exact le_refl _
    · exact hwit_nonneg (α, β)
  -- The three pieces of the point-wise total, each controlled by `W`.
  have hclaimB : (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (α, α)) ≤ 2 * (d : ℝ) * W := by
    have hstepB : (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (α, α))
        = 2 * (d : ℝ) * ∑ α : BlockCoord d, wit (α, α) := by
      have : ∀ α : BlockCoord d, (∑ β : BlockCoord d, wit (α, α)) = (2 * (d : ℝ)) * wit (α, α) := by
        intro α
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun α _ => this α), ← Finset.mul_sum]
    rw [hstepB]
    exact mul_le_mul_of_nonneg_left hdiagle (by positivity)
  have hclaimC : (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (β, β)) ≤ 2 * (d : ℝ) * W := by
    have hstepC : (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (β, β))
        = 2 * (d : ℝ) * ∑ β : BlockCoord d, wit (β, β) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast
      ring
    rw [hstepC]
    exact mul_le_mul_of_nonneg_left hdiagle (by positivity)
  have hRHSle : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      blockVecDot x x * (wit (α, β) + wit (α, α) + wit (β, β)) ≤
      blockVecDot x x * (((4 : ℝ) * d + 1) * W) := by
    have hpt : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        (wit (α, β) + wit (α, α) + wit (β, β)) ≤ ((4 : ℝ) * d + 1) * W := by
      have hsplit3 : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          (wit (α, β) + wit (α, α) + wit (β, β)) =
          (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (α, β)) +
            (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (α, α)) +
            (∑ α : BlockCoord d, ∑ β : BlockCoord d, wit (β, β)) := by
        have hinner : ∀ α : BlockCoord d, ∑ β : BlockCoord d,
            (wit (α, β) + wit (α, α) + wit (β, β)) =
            (∑ β : BlockCoord d, wit (α, β)) + (∑ β : BlockCoord d, wit (α, α)) +
              ∑ β : BlockCoord d, wit (β, β) := by
          intro α
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl (fun α _ => hinner α), Finset.sum_add_distrib,
          Finset.sum_add_distrib]
      have hexp : ((4 : ℝ) * d + 1) * W = W + 2 * (d : ℝ) * W + 2 * (d : ℝ) * W := by ring
      rw [hsplit3, hWprod, hexp]
      linarith only [hclaimB, hclaimC]
    calc ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        blockVecDot x x * (wit (α, β) + wit (α, α) + wit (β, β))
        = blockVecDot x x * ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            (wit (α, β) + wit (α, α) + wit (β, β)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ blockVecDot x x * (((4 : ℝ) * d + 1) * W) := mul_le_mul_of_nonneg_left hpt hdotnn
  have hfinal2 : |2 * Bf x x| ≤ blockVecDot x x * (((4 : ℝ) * d + 1) * W) :=
    hbound2.trans hRHSle
  have h2abs : |2 * Bf x x| = 2 * |Bf x x| := by
    rw [abs_mul]; norm_num
  rw [h2abs] at hfinal2
  linarith only [hfinal2, abs_nonneg (Bf x x)]

end

end SuperdiffusionCLT.Section4.NewMixing
