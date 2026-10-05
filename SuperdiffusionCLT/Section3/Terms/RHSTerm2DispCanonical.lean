/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2DispConst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2FinDR
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2IntegrabilityFinal
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RFinite

/-!
# The canonical instantiation of `e.RHS.term2.R.bounds`

## Report first

**`hDispDR` is discharged here.**  `exists_dispDR_canonical` produces a constant
`C₁`, a function of `d` alone, such that the display
`e.RHS.term2.R.bounds` of the paper
holds at every admissible data set, and `term2_finalC_canonical` removes the
`hDispDR` binder from the `l.RHS.term2` conclusion, leaving `hLocMin` as
the only residue.

## The route

The display `e.RHS.term2.R.bounds` reduces to four
annealed amplitudes.  This module supplies them at the canonical witness.

* `KN = ‖k_{L'} − k_ℓ‖`, the operator norm of the finite shell increment.  Its
  amplitude is `knValueAnnealedConst d` (`annealed_L4_increment_le`), its cube
  `L̲⁴` norm is sample-measurable
  (`aemeasurable_cubeLpENorm_four_matrixOperatorNorm_increment`) and its
  annealed fourth moment is finite (`increment_annealed_four_finite`).

* `GN = √d · ∑_{k ∈ (ℓ,L']} ‖∇j_k‖`, the Hilbert–Schmidt density of the product
  rule `canonicalRJacobian_norm_le_finDR`.  Its amplitude is
  `√d · knGradientAnnealedConst`, through `annealed_L4_increment_gradient_le`
  and the fourth-root scaling of a constant multiple
  (`ofReal_const_mul_pow_four_rpow`); its cube norm is sample-measurable
  (`aemeasurable_cubeLpENorm_four_const_mul_gradientSum`) and its annealed
  fourth moment is finite (`gradientSum_const_mul_annealed_four_le`).

* `WG = |∇w|` and `WH = ‖∇²w‖`, the two response densities, with amplitudes
  from the anchor `Frozen.Section3.w_basic_regbounds d hd`, clauses 1
  and 2, both at the same `d`-only constant
  `Cw = 2 · gammaMomentConst 2 · Cwb`.

## Why the pairing is run against the anchor tails

`IsDirichletResponse` carries no measurability in the sample `omega`, so the two
response densities `WG`, `WH` are **not** sample-measurable for an arbitrary
response `w`.  The Hölder/Cauchy–Schwarz pairing of `RHSTerm2RBounds` is
therefore run against the anchor's measurable tail witnesses `Zw`, `Zh` rather
than against `cubeLpENorm 4 WG`, `cubeLpENorm 4 WH`: the cube-norm domination
`cubeLpENorm 4 WG ≤ cubeLpENorm 8 WG ≤ ofReal Zw` holds by the monotonicity of
the cube norm in the exponent, and `ofReal Zw` is measurable by construction, so
`toReal_annealed_le_mul` applies with no measurability hypothesis on the
response.  This is the step that removes the hypotheses `hWGa` and `hWHa`
of the display with four annealed amplitudes.

## The named constants

With `Cwb` the constant of the anchor, `γ₂ = gammaMomentConst 2`, and
`γ_{1/2} = gammaMomentConst (1/2)`:

* `Ck = max (knValueAnnealedConst d) (√d · knGradientAnnealedConst)`;
* `Cw = 2 · γ₂ · Cwb`;
* `C₁ = 3 · Ck · Cw = 3 · max (knValueAnnealedConst d) (√d · knGradientAnnealedConst)
  · (2 · γ₂ · Cwb)`.

Every factor is a function of `d` alone, which is the printed quantifier
`There exists~$C(d)<\infty$` of `l.RHS.term2`.

The anchor used is `w_basic_regbounds`, clauses 1 and 2.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The closing arithmetic of `e.RHS.term2.R.bounds` with the printed
`√(1+h)` Hessian factor -/

/-- **The closing arithmetic of `e.RHS.term2.R.bounds` with the Hessian
amplitude in the printed shape.**

The Hessian amplitude is allowed the printed factor
`(1 + h)^{1/2}`, and the scale arithmetic pays for it with
`(L' − ℓ)^{1/2} (1 + h)^{1/2} ≤ L'` in place of `(L' − ℓ)^{1/2} ≤ L'`.

**Witness of the hypotheses.**  The bound is tight at `Ck = Cw = 1`, `np = 1`,
`IK = (L' − ℓ)^{1/2}`, `IG = 3^{-ℓ}`, `IW = h^{1/2}`,
`IH = (1 + h)^{1/2} 3^{-ℓ'}`: at `S = ScaleSelection.ofBase 4 2 1 0` (so
`n = ℓ = ℓ' = 1`, `L' = 2`, `h = 1`) one has `L' − ℓ = 1`, `3^ℓ 3^{-ℓ'} = 1`,
and both sides of the conclusion equal `3 * 2 * 1 = 6`. -/
private theorem rbounds_arith_shift {S : ScaleSelection} (hSorder : ScalesOrdering S)
    {np IR IDR IK IG IW IH Ck Cw : ℝ}
    (hnp0 : 0 ≤ np) (hCk : 1 ≤ Ck) (hCw : 1 ≤ Cw)
    (hIW0 : 0 ≤ IW) (hIH0 : 0 ≤ IH)
    (hIR : IR ≤ IK * IW) (hIDR : IDR ≤ IG * IW + IK * IH)
    (hKa : IK ≤ Ck * (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2))
    (hGa : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IG ≤ Ck)
    (hWa : IW ≤ Cw * np * ((S.h : ℝ)) ^ ((1 : ℝ) / 2))
    (hHa : IH ≤ Cw * np * Real.sqrt (1 + (S.h : ℝ)) *
      (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ)))) :
    IR + (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IDR ≤
      (3 * Ck * Cw) * ((S.LPrime : ℕ) : ℝ) * np := by
  have hCk0 : (0 : ℝ) ≤ Ck := le_trans zero_le_one hCk
  have hCw0 : (0 : ℝ) ≤ Cw := le_trans zero_le_one hCw
  have hLp0 : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (((S.LPrime - S.ell : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ((S.h : ℝ)) := Nat.cast_nonneg _
  have hh10 : (0 : ℝ) ≤ 1 + (S.h : ℝ) := by linarith only [hh0]
  have hE0 : (0 : ℝ) < (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hEp0 : (0 : ℝ) < (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have htle : (((S.LPrime - S.ell : ℕ) : ℝ)) ≤ ((S.LPrime : ℕ) : ℝ) := by
    exact_mod_cast Nat.cast_le.2 (Nat.sub_le S.LPrime S.ell)
  have hhle : ((S.h : ℝ)) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have hnat : S.h ≤ S.LPrime := by
      have h1 := S.ellPrime_add_h
      have h2 := S.LPrime_eq
      omega
    exact_mod_cast Nat.cast_le.2 hnat
  -- `1 + h ≤ L'`: `h ≤ m < L'`
  have hh1le : 1 + (S.h : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have hnat : S.h + 1 ≤ S.LPrime := by
      have h1 := hSorder.m_lt_LPrime
      have h2 := S.ellPrime_add_h
      omega
    have hcast : ((S.h + 1 : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_add, Nat.cast_one] at hcast
    linarith only [hcast]
  -- `√x ≤ L'` for `0 ≤ x ≤ (L')²`
  have hsq : ∀ x : ℝ, 0 ≤ x → x ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) →
      x ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) := by
    intro x _ hx
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt x ≤ Real.sqrt (((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ)) :=
          Real.sqrt_le_sqrt hx
      _ = ((S.LPrime : ℕ) : ℝ) := Real.sqrt_mul_self hLp0
  -- `(L' − ℓ)^{1/2} h^{1/2} ≤ L'`
  have hprod : (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
      ((S.h : ℝ)) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul ht0]
    calc Real.sqrt ((((S.LPrime - S.ell : ℕ) : ℝ)) * ((S.h : ℝ)))
        ≤ Real.sqrt (((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ)) :=
          Real.sqrt_le_sqrt (mul_le_mul htle hhle hh0 hLp0)
      _ = ((S.LPrime : ℕ) : ℝ) := Real.sqrt_mul_self hLp0
  -- `(L' − ℓ)^{1/2} (1 + h)^{1/2} ≤ L'` — the printed Hessian factor
  have hprod1 : (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
      Real.sqrt (1 + (S.h : ℝ)) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have hle : (((S.LPrime - S.ell : ℕ) : ℝ)) * (1 + (S.h : ℝ)) ≤
        ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) :=
      calc (((S.LPrime - S.ell : ℕ) : ℝ)) * (1 + (S.h : ℝ))
          ≤ ((S.LPrime : ℕ) : ℝ) * (1 + (S.h : ℝ)) :=
            mul_le_mul_of_nonneg_right htle hh10
        _ ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hh1le hLp0
    have hthis : Real.sqrt ((((S.LPrime - S.ell : ℕ) : ℝ)) * (1 + (S.h : ℝ))) ≤
        ((S.LPrime : ℕ) : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact hsq _ (mul_nonneg ht0 hh10) hle
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul ht0]
    exact hthis
  -- `h^{1/2} ≤ L'`
  have hhalf : ((S.h : ℝ)) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) := by
    refine hsq _ hh0 (le_trans hhle ?_)
    have h1 : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
      have : 1 ≤ S.LPrime := by have := hSorder.m_lt_LPrime; omega
      exact_mod_cast this
    calc ((S.LPrime : ℕ) : ℝ) = ((S.LPrime : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hLp0
  -- `3^ℓ 3^{-ℓ'} ≤ 1`
  have hshift : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
      (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))) ≤ 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : ((S.ell : ℕ) : ℝ) ≤ ((S.ellPrime : ℕ) : ℝ) := by
      exact_mod_cast Nat.cast_le.2 (le_of_lt hSorder.ell_lt_ellPrime)
    linarith only [this]
  have hLpsq : ((S.LPrime : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
      have : 1 ≤ S.LPrime := by have := hSorder.m_lt_LPrime; omega
      exact_mod_cast this
    calc ((S.LPrime : ℕ) : ℝ) = ((S.LPrime : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hLp0
  have hthalf : (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) ≤ ((S.LPrime : ℕ) : ℝ) :=
    hsq _ ht0 (le_trans htle hLpsq)
  have hM0 : (0 : ℝ) ≤ Ck * Cw * np := mul_nonneg (mul_nonneg hCk0 hCw0) hnp0
  -- the localization factor `IR`
  have hT1 : IR ≤ Ck * Cw * np * ((S.LPrime : ℕ) : ℝ) := by
    have h1 : IK * IW ≤ (Ck * (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) *
        (Cw * np * ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul hKa hWa hIW0 (mul_nonneg hCk0 (Real.rpow_nonneg ht0 _))
    have h2 : (Ck * (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) *
        (Cw * np * ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) =
        (Ck * Cw * np) * ((((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
          ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) := by ring
    have h3 : (Ck * Cw * np) * ((((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
        ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) ≤ (Ck * Cw * np) * ((S.LPrime : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hprod hM0
    have h4 : (Ck * Cw * np) * ((S.LPrime : ℕ) : ℝ) =
      Ck * Cw * np * ((S.LPrime : ℕ) : ℝ) := by ring
    linarith only [hIR, h1, h2, h3, h4]
  -- the first half of the Jacobian bound
  have hT2a : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IG * IW) ≤
      Ck * Cw * np * ((S.LPrime : ℕ) : ℝ) := by
    have h1 : ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IG) * IW ≤
        Ck * (Cw * np * ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul hGa hWa hIW0 hCk0
    have h2 : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IG * IW) =
      ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IG) * IW := by ring
    have h3 : Ck * (Cw * np * ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) =
      (Ck * Cw * np) * ((S.h : ℝ)) ^ ((1 : ℝ) / 2) := by ring
    have h4 : (Ck * Cw * np) * ((S.h : ℝ)) ^ ((1 : ℝ) / 2) ≤
        (Ck * Cw * np) * ((S.LPrime : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hhalf hM0
    have h5 : (Ck * Cw * np) * ((S.LPrime : ℕ) : ℝ) =
      Ck * Cw * np * ((S.LPrime : ℕ) : ℝ) := by ring
    linarith only [h1, h2, h3, h4, h5]
  -- the second half of the Jacobian bound, at the printed Hessian amplitude
  have hT2b : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IK * IH) ≤
      Ck * Cw * np * ((S.LPrime : ℕ) : ℝ) := by
    have h1 : IK * IH ≤ (Ck * (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) *
        (Cw * np * Real.sqrt (1 + (S.h : ℝ)) *
          (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ)))) :=
      mul_le_mul hKa hHa hIH0 (mul_nonneg hCk0 (Real.rpow_nonneg ht0 _))
    have h2 : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IK * IH) ≤
        (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
          ((Ck * (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) *
            (Cw * np * Real.sqrt (1 + (S.h : ℝ)) *
              (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))))) :=
      mul_le_mul_of_nonneg_left h1 hE0.le
    have h3 : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
        ((Ck * (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2)) *
          (Cw * np * Real.sqrt (1 + (S.h : ℝ)) *
            (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))))) =
        (Ck * Cw * np) * ((((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
          Real.sqrt (1 + (S.h : ℝ)) *
          ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
            (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))))) := by ring
    have h4 : (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
        Real.sqrt (1 + (S.h : ℝ)) *
        ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ)))) ≤ ((S.LPrime : ℕ) : ℝ) := by
      have hstep : (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
          Real.sqrt (1 + (S.h : ℝ)) *
          ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
            (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ)))) ≤
          (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
            Real.sqrt (1 + (S.h : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hshift
          (mul_nonneg (Real.rpow_nonneg ht0 _) (Real.sqrt_nonneg _))
      have hone : (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
        Real.sqrt (1 + (S.h : ℝ)) * 1 =
        (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
          Real.sqrt (1 + (S.h : ℝ)) := mul_one _
      linarith only [hstep, hone, hprod1]
    have h5 : (Ck * Cw * np) * ((((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) *
        Real.sqrt (1 + (S.h : ℝ)) *
        ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))))) ≤
        (Ck * Cw * np) * ((S.LPrime : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h4 hM0
    have h6 : (Ck * Cw * np) * ((S.LPrime : ℕ) : ℝ) =
      Ck * Cw * np * ((S.LPrime : ℕ) : ℝ) := by ring
    linarith only [h2, h3, h5, h6]
  -- assembling
  have hE1 : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IDR ≤
      (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IG * IW + IK * IH) :=
    mul_le_mul_of_nonneg_left hIDR hE0.le
  have hE2 : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IG * IW + IK * IH) =
      (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IG * IW) +
        (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * (IK * IH) := by ring
  have hfin : (3 * Ck * Cw) * ((S.LPrime : ℕ) : ℝ) * np =
    3 * (Ck * Cw * np * ((S.LPrime : ℕ) : ℝ)) := by ring
  linarith only [hT1, hT2a, hT2b, hE1, hE2, hfin]

/-! ## Two elementary identifications -/

/-- The scalar-density norm of the pointwise magnitude of a field equals the
norm of the field. -/
private theorem cubeLpENorm_norm_field_eq (Q : TriadicCube d) (q : ℝ≥0∞)
    {E : Type*} [NormedAddCommGroup E] (g : Vec d → E)
    (hg : MeasureTheory.AEStronglyMeasurable g (normalizedCubeMeasure Q)) :
    cubeLpENorm Q q (fun x => ‖g x‖) = cubeLpENorm Q q g :=
  le_antisymm (cubeLpENorm_mono_enorm (f := fun x => ‖g x‖) hg.norm fun x => by simp)
    (cubeLpENorm_mono_enorm (g := fun x => ‖g x‖) hg fun x => by simp)

/-- The real-valued carrier identity: the normalized cube `L̲⁴` norm of a
continuous nonnegative real field is the `ofReal` of the fourth root of the
normalized average of its fourth power. -/
private theorem cubeLpENorm_four_eq_ofReal_volumeAverage (Q : TriadicCube d)
    (g0 : Vec d → ℝ) (hg0nn : ∀ x : Vec d, 0 ≤ g0 x) (hgc : Continuous g0) :
    cubeLpENorm Q 4 g0 =
      ENNReal.ofReal ((volumeAverage (cubeSet Q)
        (fun x => g0 x ^ (4 : ℝ))) ^ ((4 : ℝ)⁻¹)) := by
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) by norm_num]
  exact eLpNorm_eq_ofReal_rpow_volumeAverage Q (by norm_num) g0
    (fun x => g0 x ^ (4 : ℝ)) hgc.aestronglyMeasurable
    (fun x => by
      show ‖g0 x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (g0 x ^ (4 : ℝ))
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hg0nn x),
        ENNReal.ofReal_rpow_of_nonneg (hg0nn x) (by norm_num : (0 : ℝ) ≤ (4 : ℝ))])
    (fun x => Real.rpow_nonneg (hg0nn x) 4)
    (integrable_rpow_of_continuous_cube Q (by norm_num) g0 hgc hg0nn)

/-! ## The fourth-root scaling of a constant multiple -/

/-- **The fourth root of an annealed constant multiple.**  For `c ≥ 0` and a
finite annealed fourth moment of `F`, the fourth root of the annealed fourth
moment of `ofReal c · F` is at most `c` times the fourth root of that of `F`.
This is the scaling step that absorbs the Hilbert–Schmidt factor `√d` of
`canonicalRJacobian_norm_le_finDR` into the gradient amplitude. -/
private theorem ofReal_const_mul_pow_four_rpow {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {F : Omega → ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (hFfin : (∫⁻ omega, F omega ^ (4 : ℕ) ∂mu) ≠ ⊤) :
    (∫⁻ omega, (ENNReal.ofReal c * F omega) ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) ≤
      c * (∫⁻ omega, F omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) := by
  have hctop : (ENNReal.ofReal c) ^ (4 : ℕ) ≠ ⊤ := by
    rw [← ENNReal.ofReal_pow hc]
    exact ENNReal.ofReal_ne_top
  have hcongr : (fun omega => (ENNReal.ofReal c * F omega) ^ (4 : ℕ)) =
      fun omega => (ENNReal.ofReal c) ^ (4 : ℕ) * F omega ^ (4 : ℕ) := by
    funext omega
    rw [mul_pow]
  rw [hcongr, lintegral_const_mul' _ _ hctop]
  have htop : (ENNReal.ofReal c) ^ (4 : ℕ) * (∫⁻ omega, F omega ^ (4 : ℕ) ∂mu) ≠ ⊤ :=
    ENNReal.mul_ne_top hctop hFfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc]
  rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg]
  have hc4 : ((c : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = c := by
    rw [← Real.rpow_natCast c 4, ← Real.rpow_mul hc ((4 : ℕ) : ℝ) ((1 : ℝ) / 4),
      show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
  rw [hc4]

/-! ## The canonical gradient density: `√d` times the summed one-shell
derivative norms -/

/-- **Sample-measurability of the normalized volume average of the fourth power
of a constant multiple of the summed one-shell derivative norms.**  The family
is continuous in the point for every sample and measurable in the sample for
every point (`measurable_uncurry_matrixDerivativeNorm_sum_shellDeriv`), so its
fourth power is jointly measurable and `measurable_volumeAverage_of_measurable_uncurry`
gives the measurability of the average.  There is no measurability hypothesis on
a response here: the whole content is the joint measurability of the stream
derivatives. -/
private theorem aemeasurable_volumeAverage_rpow_const_mul_gradientSum
    (P : ProbabilityMeasure (ShellSeq d)) (n m : ℕ) (Q : TriadicCube d) (c : ℝ) :
    AEMeasurable (fun omega : ShellSeq d => volumeAverage (cubeSet Q)
      (fun x : Vec d => (c * ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)))
      P.toMeasure :=
  (measurable_volumeAverage_of_measurable_uncurry
    (fun (x : Vec d) (omega : ShellSeq d) => (c * ∑ k ∈ Finset.Ioc n m,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ))
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (4 : ℝ))).measurable.comp
      ((measurable_uncurry_matrixDerivativeNorm_sum_shellDeriv (d := d) n m).const_mul c))
    (cubeSet Q)).aemeasurable

/-- **Sample-measurability of the cube `L̲⁴` norm of a constant multiple of the
summed one-shell derivative norms.**  The carrier identity
`cubeLpENorm_four_eq_ofReal_volumeAverage` writes the cube norm as the `ofReal`
of the fourth root of the normalized volume average, and the average is
sample-measurable by
`aemeasurable_volumeAverage_rpow_const_mul_gradientSum`; the fourth root and the
`ofReal` preserve `AEMeasurable`.  This is the `hGNa` clause for the canonical
Hilbert–Schmidt density `√d · ∑ ‖∇j_k‖`. -/
private theorem aemeasurable_cubeLpENorm_four_const_mul_gradientSum
    (P : ProbabilityMeasure (ShellSeq d)) (n m : ℕ) (Q : TriadicCube d) {c : ℝ}
    (hc : 0 ≤ c) :
    AEMeasurable (fun omega : ShellSeq d => cubeLpENorm Q 4
      (fun x : Vec d => c * ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) P.toMeasure := by
  have hbase := aemeasurable_volumeAverage_rpow_const_mul_gradientSum
    (d := d) P n m Q c
  have hroot : AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal
      ((volumeAverage (cubeSet Q) (fun x : Vec d => (c * ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)))
          ^ (((4 : ℝ))⁻¹))) P.toMeasure :=
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ ((4 : ℝ))⁻¹)).measurable.comp_aemeasurable
      hbase).ennreal_ofReal
  refine hroot.congr (Filter.Eventually.of_forall fun omega => ?_)
  exact (cubeLpENorm_four_eq_ofReal_volumeAverage Q
    (fun x : Vec d => c * ∑ k ∈ Finset.Ioc n m,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
    (fun x => mul_nonneg hc
      (Finset.sum_nonneg fun k _ => ShellField.matrixDerivativeNorm_nonneg _))
    ((continuous_const : Continuous (fun _ : Vec d => c)).mul
      (continuous_matrixDerivativeNorm_sum_shellDeriv omega n m))).symm

/-- **The annealed fourth moment and the fourth-root amplitude of the canonical
gradient density.**  For a nonnegative constant `c` and the density
`GN = c · ∑_{k ∈ (n,m]} ‖∇j_k‖`, the annealed fourth moment of its cube `L̲⁴`
norm is finite and

`3^n · (∫⁻ omega, ‖GN omega‖⁴_{L̲⁴(Q)})^toReal^{1/4} ≤ c · knGradientAnnealedConst`.

The finiteness comes from the `Γ_{1/2}` tail of the summed gradients
(`gradientSum_volumeAverage_isBigOWith`) through the carrier domination and
`lintegral_ofReal_ne_top_of_isBigOWith_gammaSigma`; the amplitude is the
`c = 1` bound `annealed_L4_increment_gradient_le` scaled by `c` through
`ofReal_const_mul_pow_four_rpow`.  Both halves are needed: the first is `hGNfin`
and the second is `hGa` at `c = √d`. -/
private theorem gradientSum_const_mul_annealed_four_le
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ3 : ShellLawJ3 d P) {n m : ℕ} (hnm : n < m) (Q : TriadicCube d) {c : ℝ}
    (hc : 0 ≤ c) :
    (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (fun x : Vec d => c *
        ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
        ∂P.toMeasure) ≠ ⊤ ∧
      ((3 : ℝ) ^ ((n : ℕ) : ℝ)) *
        (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (fun x : Vec d => c *
          ∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
          ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) ≤ c * knGradientAnnealedConst := by
  have hg0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ ∑ k ∈ Finset.Ioc n m,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) :=
    fun _ _ => Finset.sum_nonneg fun k _ => ShellField.matrixDerivativeNorm_nonneg _
  have hsumc : ∀ omega : ShellSeq d, Continuous (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) :=
    fun omega => continuous_matrixDerivativeNorm_sum_shellDeriv omega n m
  have hYnn : ∀ omega : ShellSeq d, 0 ≤ volumeAverage (cubeSet Q)
      (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)) :=
    fun omega =>
      SuperdiffusionCLT.Section2.Norms.volumeAverage_cubeSet_nonneg Q
        (fun x => Real.rpow_nonneg (hg0 omega x) 4)
  have hYm : Measurable (fun omega : ShellSeq d => volumeAverage (cubeSet Q)
      (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ))) :=
    measurable_volumeAverage_of_measurable_uncurry
      (fun (x : Vec d) (omega : ShellSeq d) => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ))
      (measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv (d := d) n m) (cubeSet Q)
  have hKpos : 0 < Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (IndependentSums.gammaTriangleConst 2 * ((3 : ℝ) ^ n)⁻¹) ^ (4 : ℝ)) :=
    mul_pos (Real.exp_pos 1) (mul_pos
      (lt_of_lt_of_le zero_lt_one (one_le_gammaMomentConst ((1 : ℝ) / 2)))
      (Real.rpow_pos_of_pos (mul_pos
        (lt_of_lt_of_le zero_lt_one (one_le_gammaTriangleConst 2))
        (inv_pos.mpr (pow_pos (by norm_num) n))) 4))
  have hYfin : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (volumeAverage (cubeSet Q)
      (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)))
      ∂P.toMeasure) ≠ ⊤ :=
    lintegral_ofReal_ne_top_of_isBigOWith_gammaSigma (mu := P.toMeasure)
      (sigma := ((1 : ℝ) / 2))
      (K := Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        (IndependentSums.gammaTriangleConst 2 * ((3 : ℝ) ^ n)⁻¹) ^ (4 : ℝ)))
      (by norm_num) hKpos hYnn hYm.aemeasurable
      (gradientSum_volumeAverage_isBigOWith P hPrefix hJ3 hnm Q)
  have hFfin : (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (fun x : Vec d =>
      ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hYfin (lintegral_mono fun omega =>
      cubeLpENorm_four_le_ofReal_volumeAverage Q
        (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (hg0 omega) (hsumc omega).aestronglyMeasurable (fun _ => le_rfl) (hg0 omega)
        (hsumc omega))
  have hpoint : ∀ omega : ShellSeq d, cubeLpENorm Q 4 (fun x : Vec d => c *
      ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) =
      ENNReal.ofReal c * cubeLpENorm Q 4 (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) := by
    intro omega
    have hfun : (fun x : Vec d => c * ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) =
        c • (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) := by
      funext x
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun, cubeLpENorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
  have hctop : (ENNReal.ofReal c) ^ (4 : ℕ) ≠ ⊤ := by
    rw [← ENNReal.ofReal_pow hc]
    exact ENNReal.ofReal_ne_top
  have hgoal_eq : (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (fun x : Vec d => c *
        ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
        ∂P.toMeasure) =
      (∫⁻ omega : ShellSeq d, (ENNReal.ofReal c * cubeLpENorm Q 4 (fun x : Vec d =>
        ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) ^ (4 : ℕ)
        ∂P.toMeasure) := by
    refine lintegral_congr fun omega => ?_
    rw [hpoint omega, mul_pow]
  have hcngr : (fun omega : ShellSeq d => (ENNReal.ofReal c * cubeLpENorm Q 4
      (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) ^ (4 : ℕ)) =
      fun omega : ShellSeq d => (ENNReal.ofReal c) ^ (4 : ℕ) * cubeLpENorm Q 4
        (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ) := by
    funext omega
    rw [mul_pow]
  constructor
  · rw [hgoal_eq, hcngr, lintegral_const_mul' _ _ hctop]
    exact ENNReal.mul_ne_top hctop hFfin
  · have hle : (∫⁻ omega : ShellSeq d, (ENNReal.ofReal c * cubeLpENorm Q 4
        (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) ^ (4 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) ≤
        c * (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (fun x : Vec d =>
          ∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
          ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) :=
      ofReal_const_mul_pow_four_rpow (mu := P.toMeasure)
        (F := fun omega : ShellSeq d => cubeLpENorm Q 4 (fun x : Vec d =>
          ∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) hc hFfin
    have hbase := annealed_L4_increment_gradient_le P hPrefix hJ3 hnm
      (fun (omega : ShellSeq d) (x : Vec d) => ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) hg0
      (fun _ _ => le_rfl) Q (fun omega => (hsumc omega).aestronglyMeasurable)
    have h3n : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℕ) : ℝ) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    rw [hgoal_eq]
    calc (3 : ℝ) ^ ((n : ℕ) : ℝ) * (∫⁻ omega : ShellSeq d, (ENNReal.ofReal c *
          cubeLpENorm Q 4 (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) ^ (4 : ℕ)
          ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4)
        ≤ (3 : ℝ) ^ ((n : ℕ) : ℝ) * (c * (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4
            (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
              ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
            ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hle h3n
      _ = c * ((3 : ℝ) ^ ((n : ℕ) : ℝ) * (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4
            (fun x : Vec d => ∑ k ∈ Finset.Ioc n m,
              ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℕ)
            ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4)) := by ring
      _ ≤ c * knGradientAnnealedConst := mul_le_mul_of_nonneg_left hbase hc

/-! ## The canonical instantiation of the display -/

/-- **`hDispDR` is discharged: the display `e.RHS.term2.R.bounds` holds at a
constant that is a function of `d` alone.**

`exists_dispDR_canonical` produces `C₁ = 3 · Ck · Cw` with

* `Ck = max (knValueAnnealedConst d) (√d · knGradientAnnealedConst)`,
* `Cw = 2 · gammaMomentConst 2 · Cwb`, `Cwb` the constant of the anchor
  `Frozen.Section3.w_basic_regbounds d hd`,

and proves the display of the named-witness reduction at that constant,
at the canonical weak Jacobian `canonicalRJacobian` and the test vector
`testVector nu S.LPrime P S.n e`, for every admissible data set.

**The densities.**  `KN = ‖k_{L'} − k_ℓ‖` is the operator norm of the finite
shell increment, `GN = √d · ∑_{k ∈ (ℓ,L']} ‖∇j_k‖` the Hilbert–Schmidt density
of the product rule `canonicalRJacobian_norm_le_finDR`, and `WG = |∇w|`,
`WH = ‖∇²w‖` the two response densities at the weak-Hessian witness
`rfieldHessianWitness`.

**The pairing runs against the anchor tails.**  `IsDirichletResponse` carries no
measurability in `omega`, so `hWGa`/`hWHa` — the sample-measurability of the
cube `L̲⁴` norms of `WG` and `WH` — are not available, and
the display with four annealed amplitudes is therefore *not* applied.  Instead the
Cauchy–Schwarz pairing of `RHSTerm2RBounds` is run against the anchor's
measurable tails: the cube-norm domination
`cubeLpENorm 4 WG ≤ cubeLpENorm 8 WG ≤ ofReal Zw` (monotonicity of the cube norm
in the exponent) replaces the second factor `cubeLpENorm 4 WG` by `ofReal Zw`,
which is measurable by construction, and likewise `ofReal Zh` for `WH`.  This is
the step that removes `hWGa` and `hWHa` from the instantiation.  The two tails
also give exactly the finiteness and amplitude bounds
(`toReal_annealed_four_le_of_isBigO`), so `hWGfin`/`hWHfin` disappear with them.

**Witness of the hypotheses.**  The hypotheses of the two tail bridges are
satisfied by `Zw`, `Zh` themselves (`N := ofReal Zw` in the domination slot of
`toReal_annealed_four_le_of_isBigO`, `le_rfl`); the amplitude positivity
`0 < Cwb · √|p| · h^{1/2}` uses `hp0 : 0 < √(vecNormSq (testVector …))`, proved
from `vecNormSq_testVector`.  A witness of the conclusion is the one disclosed
for that display: `KN = WG ≡ 1`, `GN = WH ≡ 0` realises the
display at `C = 3`.

**Remaining hypotheses of the conclusion:** none beyond the standing data
(`d`, `[NeZero d]`, `2 ≤ d`, and the admissible data set). -/
theorem exists_dispDR_canonical (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection) (hSorder : ScalesOrdering S),
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        (∫⁻ omega : ShellSeq d,
              vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                    (coefficientCutoff nu omega S.ell).toCoeffField y)
                  ((w omega).toH1Function.grad y)) ^
                (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
            (∫⁻ omega : ShellSeq d,
                cubeLpENorm (originCube d (S.m : ℤ)) 2
                  (fun x => HilbertMat.ofMat (fun i j =>
                    canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
                      w hw omega i x j)) ^
                  (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₁ * ((S.LPrime : ℕ) : ℝ) *
            Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) := by
  obtain ⟨Cwb, hCwb, hClauses⟩ :=
    SuperdiffusionCLT.Frozen.Section3.w_basic_regbounds d hd
  have hsqrtd1 : (1 : ℝ) ≤ Real.sqrt d :=
    (Real.one_le_sqrt).mpr
      (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hd))
  have hCkg1 : (1 : ℝ) ≤ Real.sqrt d * knGradientAnnealedConst := by
    have h : (1 : ℝ) * 1 ≤ Real.sqrt d * knGradientAnnealedConst :=
      mul_le_mul hsqrtd1 one_le_knGradientAnnealedConst zero_le_one
        (le_trans zero_le_one hsqrtd1)
    linarith only [h]
  have hCw2g : (1 : ℝ) ≤ 2 * IndependentSums.gammaMomentConst 2 := by
    have h5a : (1 : ℝ) * 2 ≤ IndependentSums.gammaMomentConst 2 * 2 :=
      mul_le_mul_of_nonneg_right (one_le_gammaMomentConst 2) (by norm_num)
    linarith only [h5a]
  have hCwab : (1 : ℝ) ≤ 2 * IndependentSums.gammaMomentConst 2 * Cwb := by
    have h5b : 2 * IndependentSums.gammaMomentConst 2 * 1 ≤
        2 * IndependentSums.gammaMomentConst 2 * Cwb :=
      mul_le_mul_of_nonneg_left hCwb (by linarith only [hCw2g])
    linarith only [hCw2g, h5b]
  have hCkCw : (1 : ℝ) ≤
      max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
        (2 * IndependentSums.gammaMomentConst 2 * Cwb) := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
            (2 * IndependentSums.gammaMomentConst 2 * Cwb) :=
          mul_le_mul (le_trans hCkg1 (le_max_right _ _)) hCwab zero_le_one
            (le_trans zero_le_one (le_trans hCkg1 (le_max_right _ _)))
  have hC₁ : (1 : ℝ) ≤ 3 *
      max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
        (2 * IndependentSums.gammaMomentConst 2 * Cwb) := by
    have hthree : max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
          (2 * IndependentSums.gammaMomentConst 2 * Cwb) ≤
        3 * (max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
          (2 * IndependentSums.gammaMomentConst 2 * Cwb)) := by
      linarith only [hCkCw]
    have hassoc : 3 * (max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
          (2 * IndependentSums.gammaMomentConst 2 * Cwb)) = 3 *
        max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
          (2 * IndependentSums.gammaMomentConst 2 * Cwb) := by ring
    linarith only [hCkCw, hthree, hassoc]
  refine ⟨3 * max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
      (2 * IndependentSums.gammaMomentConst 2 * Cwb), hC₁, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
  -- the scale facts
  have hnm : S.ell < S.LPrime := by
    have h1 := hSorder.ell_lt_ellPrime
    have h2 := hSorder.ellPrime_lt_m
    have h3 : S.LPrime = S.m + 2 * S.a := S.LPrime_eq
    omega
  have hhp : (1 : ℕ) ≤ S.h := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 : S.ellPrime + S.h = S.m := S.ellPrime_add_h
    omega
  have hhp1 : (1 : ℝ) ≤ (S.h : ℝ) := by exact_mod_cast hhp
  have hsqh : (1 : ℝ) ≤ Real.sqrt (1 + (S.h : ℝ)) :=
    (Real.one_le_sqrt).2 (by linarith only [hhp1])
  have hpseq : vecNormSq (testVector nu S.LPrime P S.n e) =
      sigmaBarStarInvSqrt nu S.LPrime P S.n ^ 2 := by
    rw [vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he,
      ← sq_sigmaBarStarInvSqrt hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n]
  have hp0 : 0 < Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) := by
    rw [hpseq]
    exact Real.sqrt_pos.2
      (pow_pos (sigmaBarStarInvSqrt_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n) 2)
  -- the weak-Hessian witness and the two anchor clauses
  let HD : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function :=
    fun omega => hasWeakHessianOnSymm (isOpen_openCubeSet (originCube d (S.m : ℤ)))
      (rfieldHessianWitness d hd S hSorder (testVector nu S.LPrime P S.n e) w hw omega)
  obtain ⟨hGradClause, hHessClause, -⟩ := hClauses nu hnu hnu1 P hPrefix hJ1V2 hJ2
    hJ3 hJ4 S hSorder e he (testVector nu S.LPrime P S.n e) rfl w hw
  obtain ⟨Zw, hZwm, hZwO, hZwdom⟩ := hGradClause
  obtain ⟨Zh, hZhm, hZhO, hZhdom⟩ := hHessClause HD
  -- the four canonical densities
  let KN : ShellSeq d → Vec d → ℝ :=
    fun omega x => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x)
  let GN : ShellSeq d → Vec d → ℝ :=
    fun omega x => Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)
  let WG : ShellSeq d → Vec d → ℝ :=
    fun omega x => vecNorm ((w omega).toH1Function.grad x)
  let WH : ShellSeq d → Vec d → ℝ :=
    fun omega x => ‖HilbertMat.ofMat (fun i j => (HD omega).hess i j x)‖
  have hKN : KN = fun omega x =>
      matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) := rfl
  have hGN : GN = fun omega x => Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) := rfl
  have hWG : WG = fun omega x => vecNorm ((w omega).toH1Function.grad x) := rfl
  have hWH : WH = fun omega x =>
      ‖HilbertMat.ofMat (fun i j => (HD omega).hess i j x)‖ := rfl
  -- nonnegativity and cube measurability
  have hKN0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ KN omega x :=
    fun _ _ => matrixOperatorNorm_nonneg _
  have hGN0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ GN omega x :=
    fun _ _ => mul_nonneg (Real.sqrt_nonneg d)
      (Finset.sum_nonneg fun k _ => ShellField.matrixDerivativeNorm_nonneg _)
  have hWG0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ WG omega x :=
    fun _ _ => vecNorm_nonneg _
  have hWH0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ WH omega x :=
    fun _ _ => norm_nonneg _
  have hKNm : ∀ omega : ShellSeq d, AEStronglyMeasurable (KN omega)
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    change AEStronglyMeasurable
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ)))
    exact (continuous_matrixOperatorNorm_finiteShellIncrement omega S.ell S.LPrime).aestronglyMeasurable
  have hGNm : ∀ omega : ShellSeq d, AEStronglyMeasurable (GN omega)
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    change AEStronglyMeasurable
      (fun x : Vec d => Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ)))
    exact ((continuous_const : Continuous (fun _ : Vec d => Real.sqrt d)).mul
      (continuous_matrixDerivativeNorm_sum_shellDeriv omega S.ell S.LPrime)).aestronglyMeasurable
  have hWGm : ∀ omega : ShellSeq d, AEStronglyMeasurable (WG omega)
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    change AEStronglyMeasurable
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ)))
    have h1 : AEStronglyMeasurable (hilbertifyVecField ((w omega).toH1Function.grad))
        (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
      rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
      exact (memHilbertVectorL2_hilbertifyVecField
        ((w omega).toH1Function.grad_memVectorL2)).aestronglyMeasurable.smul_measure _
    rw [show (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)) =
        (fun x : Vec d => ‖hilbertifyVecField ((w omega).toH1Function.grad) x‖) from
      funext fun x => (norm_hilbertifyVecField_apply _ x).symm]
    exact h1.norm
  have hHm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    have hEnt : ∀ i j : Fin d, MemLp (fun x : Vec d => (HD omega).hess i j x) 2
        (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
      fun i j => (HD omega).hess_memL2 i j
    have hMat : MemLp (fun x : Vec d =>
        (fun i j : Fin d => (HD omega).hess i j x : Mat d)) 2
        (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
      MemLp.of_eval fun i => MemLp.of_eval fun j => hEnt i j
    have hH0 := (HilbertMat.continuousLinearEquivMat d).symm.toContinuousLinearMap.comp_memLp'
      hMat
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact hH0.aestronglyMeasurable.smul_measure _
  have hWHm : ∀ omega : ShellSeq d, AEStronglyMeasurable (WH omega)
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    change AEStronglyMeasurable
      (fun x : Vec d => ‖HilbertMat.ofMat (fun i j => (HD omega).hess i j x)‖)
      (normalizedCubeMeasure (originCube d (S.m : ℤ)))
    exact (hHm omega).norm
  have hgradHm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (hilbertifyVecField ((w omega).toH1Function.grad))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField
      ((w omega).toH1Function.grad_memVectorL2)).aestronglyMeasurable.smul_measure _
  have hRm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (hilbertifyVecField (fun y : Vec d =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
          (coefficientCutoff nu omega S.ell).toCoeffField y)
        ((w omega).toH1Function.grad y)))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    fun omega => aestronglyMeasurable_hilbertifyVecField_matVecMul
      ((continuous_coefficientCutoff_apply nu omega S.LPrime).sub
        (continuous_coefficientCutoff_apply nu omega S.ell)) (hgradHm omega)
  have hDRm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e) w hw omega i x j))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact ((canonicalRJacobian_hasWeakGradientOn d hd nu S hSorder
      (testVector nu S.LPrime P S.n e) w hw).2 omega).aestronglyMeasurable.smul_measure _
  -- the two pointwise product rules of the display `e.RHS.term2.R.bounds`
  have hRpt : ∀ (omega : ShellSeq d) (x : Vec d),
      vecNorm (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
          (coefficientCutoff nu omega S.ell).toCoeffField x)
        ((w omega).toH1Function.grad x)) ≤ KN omega x * WG omega x := by
    intro omega x
    change vecNorm (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
        (coefficientCutoff nu omega S.ell).toCoeffField x)
        ((w omega).toH1Function.grad x)) ≤
      matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) *
        vecNorm ((w omega).toH1Function.grad x)
    rw [coefficientCutoff_toCoeffField_sub_streamCutoff nu omega S.ell S.LPrime x,
      ← finiteShellIncrement_apply_eq_streamCutoff_sub omega (le_of_lt hnm) x]
    exact vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
  have hDRpt : ∀ (omega : ShellSeq d) (x : Vec d),
      ‖HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
          w hw omega i x j)‖ ≤
        GN omega x * WG omega x + KN omega x * WH omega x := by
    intro omega x
    change ‖HilbertMat.ofMat (fun i j => canonicalRJacobian d hd S hSorder
        (testVector nu S.LPrime P S.n e) w hw omega i x j)‖ ≤
      (Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) *
        vecNorm ((w omega).toH1Function.grad x) +
      matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) *
        ‖HilbertMat.ofMat (fun i j => (HD omega).hess i j x)‖
    have hfin := canonicalRJacobian_norm_le_finDR d hd S hSorder
      (testVector nu S.LPrime P S.n e) w hw omega x
    rw [← finiteShellIncrement_apply_eq_streamCutoff_sub omega (le_of_lt hnm) x] at hfin
    have hsumle : ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x) ≤
        ∑ k ∈ Finset.Ioc S.ell S.LPrime,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) :=
      matrixDerivativeNorm_finset_sum_le (Finset.Ioc S.ell S.LPrime)
        (fun k => ShellField.deriv (omega k) x)
    have hsumle' : Real.sqrt d * ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x) *
        vecNorm ((w omega).toH1Function.grad x) ≤
        (Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) *
          vecNorm ((w omega).toH1Function.grad x) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsumle (Real.sqrt_nonneg d)) (vecNorm_nonneg _)
    calc ‖HilbertMat.ofMat (fun i j => canonicalRJacobian d hd S hSorder
          (testVector nu S.LPrime P S.n e) w hw omega i x j)‖
        ≤ matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) *
            ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖ +
            Real.sqrt d * ShellField.matrixDerivativeNorm
              (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x) *
              vecNorm ((w omega).toH1Function.grad x) := hfin
      _ ≤ matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) *
            ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖ +
            (Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
              ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) *
              vecNorm ((w omega).toH1Function.grad x) := add_le_add_right hsumle' _
      _ = (Real.sqrt d * ∑ k ∈ Finset.Ioc S.ell S.LPrime,
              ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) *
              vecNorm ((w omega).toH1Function.grad x) +
            matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) *
            ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖ := by ring
  -- the cube `L̲⁴` dominations of the two response densities by the tails
  have hWGdom : ∀ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4 (WG omega) ≤
      ENNReal.ofReal (Zw omega) := by
    intro omega
    change cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)) ≤ ENNReal.ofReal (Zw omega)
    refine (cubeLpENorm_mono_exponent (originCube d (S.m : ℤ))
      (show (4 : ℝ≥0∞) ≤ 8 by norm_num) (hWGm omega)).trans ?_
    rw [cubeLpENorm_vecNorm_eq_vecCubeLpENorm _ _ _ (hgradHm omega)]
    exact hZwdom omega
  have hWHdom : ∀ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4 (WH omega) ≤
      ENNReal.ofReal (Zh omega) := by
    intro omega
    change cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => ‖HilbertMat.ofMat (fun i j => (HD omega).hess i j x)‖) ≤
      ENNReal.ofReal (Zh omega)
    refine (cubeLpENorm_mono_exponent (originCube d (S.m : ℤ))
      (show (4 : ℝ≥0∞) ≤ 8 by norm_num) (hWHm omega)).trans ?_
    rw [cubeLpENorm_norm_field_eq _ _ _ (hHm omega)]
    exact hZhdom omega
  -- the pointwise cube Hölder pairing with the tails as second factors
  have hNR : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
            (coefficientCutoff nu omega S.ell).toCoeffField y)
          ((w omega).toH1Function.grad y)) ≤
        cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega) *
          ENNReal.ofReal (Zw omega) := by
    intro omega
    rw [SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm]
    exact (cubeLpENorm_two_le_mul_four (hKN0 omega) (hWG0 omega) (hKNm omega)
      (hWGm omega) (hRm omega) (fun x => hRpt omega x)).trans
      (mul_le_mul_of_nonneg_left (hWGdom omega) zero_le)
  have hNDR : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x : Vec d => HilbertMat.ofMat (fun i j =>
          canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
            w hw omega i x j)) ≤
        cubeLpENorm (originCube d (S.m : ℤ)) 4 (GN omega) * ENNReal.ofReal (Zw omega) +
          cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega) * ENNReal.ofReal (Zh omega) := by
    intro omega
    exact (cubeLpENorm_two_le_mul_four_add (hGN0 omega) (hWG0 omega) (hKN0 omega)
      (hWH0 omega) (hGNm omega) (hWGm omega) (hKNm omega) (hWHm omega)
      (hDRm omega) (fun x => hDRpt omega x)).trans (add_le_add
        (mul_le_mul_of_nonneg_left (hWGdom omega) zero_le)
        (mul_le_mul_of_nonneg_left (hWHdom omega) zero_le))
  -- the annealed measurability and finiteness of the four densities
  have hKNa : AEMeasurable (fun omega : ShellSeq d =>
      cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega)) P.toMeasure :=
    aemeasurable_cubeLpENorm_four_matrixOperatorNorm_increment P S.ell S.LPrime
      (originCube d (S.m : ℤ))
  have hGNa : AEMeasurable (fun omega : ShellSeq d =>
      cubeLpENorm (originCube d (S.m : ℤ)) 4 (GN omega)) P.toMeasure :=
    aemeasurable_cubeLpENorm_four_const_mul_gradientSum P S.ell S.LPrime
      (originCube d (S.m : ℤ)) (Real.sqrt_nonneg d)
  have hKNfin : (∫⁻ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega) ^ (4 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    increment_annealed_four_finite P hPrefix hJ2 hJ3 hJ4 hnm (originCube d (S.m : ℤ))
  have hGNfin : (∫⁻ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 4 (GN omega) ^ (4 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    (gradientSum_const_mul_annealed_four_le P hPrefix hJ3 (n := S.ell) (m := S.LPrime)
      hnm (originCube d (S.m : ℤ)) (Real.sqrt_nonneg d)).1
  -- the two tails: finiteness and amplitude
  have hZWmeas : AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal (Zw omega))
      P.toMeasure := hZwm.aemeasurable.ennreal_ofReal
  have hZHmeas : AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal (Zh omega))
      P.toMeasure := hZhm.aemeasurable.ennreal_ofReal
  have hZwA : 0 < Cwb * (Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
      ((S.h : ℝ)) ^ ((1 : ℝ) / 2)) :=
    mul_pos (lt_of_lt_of_le zero_lt_one hCwb) (mul_pos hp0
      (Real.rpow_pos_of_pos (Nat.cast_pos.2 (lt_of_lt_of_le (by norm_num) hhp)) _))
  have hZhA : 0 < Cwb * (Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))))) :=
    mul_pos (lt_of_lt_of_le zero_lt_one hCwb) (mul_pos hp0 (mul_pos
      (Real.sqrt_pos.2 (by linarith only [hhp1]))
      (Real.rpow_pos_of_pos (by norm_num) _)))
  obtain ⟨hZWfin, hZWle⟩ := toReal_annealed_four_le_of_isBigO (mu := P.toMeasure)
    (N := fun omega : ShellSeq d => ENNReal.ofReal (Zw omega)) (Z := Zw)
    (A := Cwb * (Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
      ((S.h : ℝ)) ^ ((1 : ℝ) / 2)))
    hZwA hZwm.aemeasurable hZwO (fun _ => le_rfl)
  obtain ⟨hZHfin, hZHle⟩ := toReal_annealed_four_le_of_isBigO (mu := P.toMeasure)
    (N := fun omega : ShellSeq d => ENNReal.ofReal (Zh omega)) (Z := Zh)
    (A := Cwb * (Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
      (Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))))))
    hZhA hZhm.aemeasurable hZhO (fun _ => le_rfl)
  -- the two Cauchy–Schwarz pairings in the sample
  have hIR : (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y)) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
      (∫⁻ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) *
      (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) :=
    toReal_annealed_le_mul (mu := P.toMeasure) hKNa hZWmeas hNR hKNfin hZWfin
  have hIDR : (∫⁻ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x : Vec d => HilbertMat.ofMat (fun i j =>
            canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
              w hw omega i x j)) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
      (∫⁻ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4 (GN omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) *
        (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (4 : ℕ)
          ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) +
      (∫⁻ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) *
        (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zh omega) ^ (4 : ℕ)
          ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) :=
    toReal_annealed_le_mul_add (mu := P.toMeasure) hGNa hZWmeas hKNa hZHmeas hNDR
      hGNfin hZWfin hKNfin hZHfin
  -- the four amplitudes
  have hIK : (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 4 (KN omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) ≤
      max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) *
        (((S.LPrime - S.ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) :=
    le_trans (annealed_L4_increment_le P hPrefix hJ2 hJ3 hJ4 (n := S.ell) (m := S.LPrime)
      hnm KN hKN0 (fun _ _ => le_rfl) (originCube d (S.m : ℤ)) hKNm)
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg (S.LPrime - S.ell : ℕ)) _))
  have hIG : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
      (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 4 (GN omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) ≤
      max (knValueAnnealedConst d) (Real.sqrt d * knGradientAnnealedConst) :=
    le_trans (gradientSum_const_mul_annealed_four_le P hPrefix hJ3 (n := S.ell)
      (m := S.LPrime) hnm (originCube d (S.m : ℤ)) (Real.sqrt_nonneg d)).2
      (le_max_right _ _)
  have hIW : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) ≤
      (2 * IndependentSums.gammaMomentConst 2 * Cwb) *
        Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
        ((S.h : ℝ)) ^ ((1 : ℝ) / 2) := by
    refine hZWle.trans (le_of_eq ?_)
    ring
  have hIH : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zh omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) ≤
      (2 * IndependentSums.gammaMomentConst 2 * Cwb) *
        Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)) *
        Real.sqrt (1 + (S.h : ℝ)) * (3 : ℝ) ^ (-(((S.ellPrime : ℕ) : ℝ))) := by
    refine hZHle.trans (le_of_eq ?_)
    ring
  have hIW0 : 0 ≤ (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hIH0 : 0 ≤ (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zh omega) ^ (4 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  exact rbounds_arith_shift hSorder (Real.sqrt_nonneg _)
    (le_trans hCkg1 (le_max_right _ _)) hCwab hIW0 hIH0 hIR hIDR hIK hIG hIW hIH

/-! ## The conclusion with `hDispDR` discharged -/

/-- **`l.RHS.term2` with `hDispDR` discharged by the canonical instantiation.**

This is the integrable-witness reduction of `l.RHS.term2` with the binder `hDispDR` — the
display `e.RHS.term2.R.bounds` at the literal constant `C₁ = 1` — *removed*.  It
is supplied by `exists_dispDR_canonical` at its named constant

`C₁ = 3 · max (knValueAnnealedConst d) (√d · knGradientAnnealedConst) · (2 · gammaMomentConst 2 · Cwb)`,

a function of `d` alone, and it is *absorbed* by the chain
`RHSTerm2DispConst.term2_finalC_named_dispConst` at that same `C₁`: the constant
`C(C₁, Cloc, d)` it produces is the terminal constant of the chain
`RHSTerm2Assembly.term2_of_residue`, and no side condition beyond `1 ≤ C₁` and
`1 ≤ Cloc'` is needed to dominate the relaxed display.  The residue of the
conclusion is therefore `hLocMin` **alone**.

`hfinR`, `hFinDR`, `hMeasDR` are discharged inside
`term2_finalC_named_dispConst` exactly as in that reduction, at the
same three named witnesses. -/
theorem term2_finalC_canonical (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cloc : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection) (_hSorder : ScalesOrdering S),
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        -- `hLocMin`: the conjunct-3 clause, at the section constant `Cloc`
        (hLocMin : ∀ U : Book.Ch02.Domain d,
            (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
            ∀ (omega' : ShellSeq d) (p q : Vec d)
              (u : AHarmonicFunction
                (fun x : Vec d =>
                  (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                    volumeAverageMat (U : Set (Vec d))
                      (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                (U : Set (Vec d)))
              (v : AHarmonicFunction
                (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
              (∀ w : AHarmonicFunction
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                  (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q u)) →
              (∀ w : AHarmonicFunction
                  (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
                volumeAverage (U : Set (Vec d))
                    (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
                  Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                      anchorDerivSup S.ell S.LPrime S.n omega' *
                    (ResponseJ (U : Set (Vec d)) p q
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                      ResponseJ (U : Set (Vec d)) p q
                        (coefficientCutoff nu omega' S.ell).toCoeffField +
                      2 * vecDot p q)) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        testVector nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
  obtain ⟨C₁, hC₁, hDisp⟩ := exists_dispDR_canonical d hd
  obtain ⟨C, hC, hmain⟩ := term2_finalC_named_dispConst d hd C₁ hC₁ Cloc
  refine ⟨C, hC, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw hLocMin
  exact hmain nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw hLocMin
    (term2_hfinR_integrability d hd nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4
      S hSorder e he w hw)
    (term2_hFinDR_integrability d hd nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4
      S hSorder e he w hw)
    (term2_hMeasDR_integrability d hd nu P S hSorder e w hw)
    (hDisp nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw)

/-! ## The same, with `hLocMin` replaced by the localization reduction -/

/-- **The `l.RHS.term2` conclusion with no residue beyond the localization
statement.**

The hypothesis `hLocMinEx` is the conclusion of the localization
reduction `RHSTerm2LocMin.term2_hLocMin_of_localization` — the `hLocMin`
family produced from the localization statement of Section 2
(`Frozen/Section2/CutoffLocalization.lean`), with its own existential
constant.  Given it, this theorem is `term2_finalC_canonical` with `hLocMin`
supplied, so term 2 is closed modulo Section 2. -/
theorem term2_finalC_canonical_of_localization (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hLocMinEx : ∃ Cloc : ℝ,
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S),
      ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
        ∀ (omega' : ShellSeq d) (p q : Vec d)
          (u : AHarmonicFunction
            (fun x : Vec d =>
              (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                volumeAverageMat (U : Set (Vec d))
                  (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
            (U : Set (Vec d)))
          (v : AHarmonicFunction
            (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
          (∀ w : AHarmonicFunction
              (fun x : Vec d =>
                (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                  volumeAverageMat (U : Set (Vec d))
                    (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
              (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                    p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                    p q u)) →
          (∀ w : AHarmonicFunction
              (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
            volumeAverage (U : Set (Vec d))
                (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
              Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                  anchorDerivSup S.ell S.LPrime S.n omega' *
                (ResponseJ (U : Set (Vec d)) p q
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                  ResponseJ (U : Set (Vec d)) p q
                    (coefficientCutoff nu omega' S.ell).toCoeffField +
                  2 * vecDot p q)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection) (_hSorder : ScalesOrdering S),
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        testVector nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
  obtain ⟨Cloc, hCloc⟩ := hLocMinEx
  obtain ⟨C, hC, hmain⟩ := term2_finalC_canonical d hd Cloc
  refine ⟨C, hC, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw
  exact hmain nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw
    (hCloc nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder)

end

end SuperdiffusionCLT.Section3.Terms
