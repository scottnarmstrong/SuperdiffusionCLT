/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgAssemblyB
public import SuperdiffusionCLT.Section3.Terms.WindowFactorAbsorption

/-!
# The constant `C_B` of the printed step `e.RHS.term3.B`, named explicitly

The display is `e.RHS.term3.B` of the paper, whose conclusion is the obligation
`_hOscBound` of the term-3 statement.

## What the constants `Cpo`, `C3`, `CB`, `hCB` ask

The oscillation estimate carries the four comparison binders
`{C Cpo C3 CB : ℝ}` with `hC : 0 < C`, `hCpo : 0 ≤ Cpo`, `hC3 : 0 ≤ C3` and

`hCB : oscBoundConst Cpo C C3 S.h ≤ CB`,

where `oscBoundConst` (`Section3/Terms/RHSTerm3OscCg.lean`)

`oscBoundConst Cpo C C3 h = (Cpo · nablaW3Const C · (1 + h)^{3/2})^{1/3} · C3^{2/3}`

is the constant of the printed Hölder pairing: `Cpo` is the per-cube Poincaré
constant, `C` the amplitude constant of the second clause of `e.nablaw.Lt`, and
`C3` the flux-moment constant.  So `hCB` asks, in full:

> *the printed constant `C_B`, evaluated at the window `S.h`, is dominated by an
> independent real number `CB`.*

That single comparison is the *only* place `CB` enters: the assembly concludes

`E[term3.B] ≤ oscBoundConst Cpo C C3 S.h · ν^{-3/2}(δ+η_L)^{1/2}(L')^{1/2}
3^{-(ℓ'-n)}`

and obtains the `_hOscBound` shape by multiplying `hCB` by the nonnegative
prefactor.

## What the paper claims

`e.RHS.term3.B` claims

`E[term3.B] ≤ C ν^{-3/2} (δ + η_L)^{1/2} (L')^{1/2} 3^{-(ℓ'-n)}`

with **one constant `C`**, and its two ingredients are pure-constant displays:
the Poincaré step gives `avsum E[ [∇w - (∇w)_{z+cu_n}]_{H̲¹}³ ] ≤ C avsum
E[‖∇²w‖_{L̲³}³] ≤ C ν^{-3/2} 3^{-3ℓ'}`, and the multiscale-Poincaré step gives
the flux factor `C 3^{3n/2} (L'ν⁻¹)^{3/4}`.  There is **no `h`-dependence**
anywhere in the printed constant.  The second clause of
`l_w_basic_regbounds_window`, which is the version of the first ingredient used
here, carries the union-bound loss `√(1 + h)`
(`Section3/Terms/WindowFactorAbsorption.lean`); raised to the third power by the
third moment and to `1/3` by the Hölder pairing, it is exactly the factor
`(1 + h)^{1/2}` of `oscBoundConst`.  That factor is the whole content of `hCB`.
Since every window `h` is the window of some scale selection, `hCB` cannot hold
with a scale-independent `CB`: the window factor `(1 + h)^{1/2}` is unbounded.
The constant is therefore named in a scale-visible form (below), or the rate is
weakened.

## Main results

* `oscBoundConstBase`: the printed constant with the window removed, an explicit
  term in the prefactors `Cpo`, `C` and `C3`.  Since
  `oscBoundConst = oscBoundConstBase · (1 + h)^{1/2}`
  (`oscBoundConst_eq_window`), `hCB` is the assertion that this base times the
  window factor is dominated by `CB`.
* `oscBoundConstWindow`, `oscBoundConstOffset`: the two explicit forms of `CB`: at
  the window (`base · (1 + h)^{1/2}`) and at the offset (`base · 3^{a/2}`).
  `oscBoundConst_le_windowCB` and `oscBoundConst_le_offsetBase` prove `hCB` at
  each, the second from the hypothesis `_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a`.
* `oscBoundConst_mul_rate_le`: at rate `3^{-(ℓ'-n)}` the product is dominated by
  the scale-independent constant `max 1 (oscBoundConstBase Cpo C C3)` at the
  rate `3^{-a}` of the conclusion's matching summand.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## Naming the printed constant -/

/-- **The printed constant `C_B` of `e.RHS.term3.B` with the window removed.**
The constant of `e.RHS.term3.B` in the paper is a pure constant; here the
only additional factor is the union-bound loss `(1 + h)^{1/2}`
(`oscBoundConst_eq_window`).  This is that constant: an
explicit term in the Poincaré prefactor `Cpo`, the clause amplitude `C` and the
flux-moment prefactor `C3`. -/
def oscBoundConstBase (Cpo C C3 : ℝ) : ℝ :=
  (Cpo * nablaW3Const C) ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3)

/-- The printed constant is nonnegative at nonnegative prefactors. -/
theorem oscBoundConstBase_nonneg {Cpo C C3 : ℝ} (hCpo : 0 ≤ Cpo) (hC : 0 ≤ C)
    (hC3 : 0 ≤ C3) : 0 ≤ oscBoundConstBase Cpo C C3 :=
  mul_nonneg
    (Real.rpow_nonneg (mul_nonneg hCpo (nablaW3Const_nonneg hC)) _)
    (Real.rpow_nonneg hC3 _)

/-- **`CB` at the window.**  The printed constant *including* the `√(1 + h)`
union-bound loss: the base times the window factor, so that `hCB`
holds with no side condition at all. -/
def oscBoundConstWindow (Cpo C C3 : ℝ) (h : ℕ) : ℝ :=
  oscBoundConstBase Cpo C C3 * (1 + (h : ℝ)) ^ ((1 : ℝ) / 2)

/-- **`CB` at the offset.**  With the window replaced by the offset `a` through
the hypothesis `S.h + 1 ≤ 3 ^ S.a`, this is the explicit constant `hCB` admits at
the constant-first order: an explicit term in `Cpo`, `C`, `C3` and the offset
`S.a`, with **no** dependence on the window `S.h`. -/
def oscBoundConstOffset (Cpo C C3 : ℝ) (S : ScaleSelection) : ℝ :=
  oscBoundConstBase Cpo C C3 * (3 : ℝ) ^ ((S.a : ℝ) / 2)

/-! ## `hCB` at the explicit constants -/

/-- **The exact content of `hCB`.**  Since the window enters `oscBoundConst`
through the single factor `(1 + h)^{1/2}` (`oscBoundConst_eq_rpow`), the
comparison `hCB : oscBoundConst Cpo C C3 h ≤ CB` is *equivalent* to the
comparison of the window-free printed constant with `CB` divided by that
factor.  This is why `hCB` grows with the window and cannot hold at a fixed
`CB`. -/
theorem oscBoundConst_eq_window {Cpo C C3 : ℝ} (hCpo : 0 ≤ Cpo) (hC : 0 ≤ C)
    (h : ℕ) : oscBoundConst Cpo C C3 h = oscBoundConstWindow Cpo C C3 h := by
  rw [oscBoundConstWindow, oscBoundConstBase, oscBoundConst_eq_rpow hCpo hC h]

/-- **`hCB` at the explicit window constant `CB = oscBoundConstWindow`.** -/
theorem oscBoundConst_le_windowCB {Cpo C C3 : ℝ} (hCpo : 0 ≤ Cpo) (hC : 0 ≤ C)
    (h : ℕ) : oscBoundConst Cpo C C3 h ≤ oscBoundConstWindow Cpo C C3 h :=
  le_of_eq (oscBoundConst_eq_window hCpo hC h)

/-- The window factor `√(1 + h)` against the offset, from the printed upper
relation `h + 1 ≤ 3^a` of `e.h.restrictions` versus `a = ⌈K log(ν⁻¹L)⌉`
(the hypothesis `_hWindowVsOffset`). -/
theorem windowFactor_le_offset {S : ScaleSelection} (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) :
    (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2) ≤ (3 : ℝ) ^ ((S.a : ℝ) / 2) := by
  have hcast : (1 : ℝ) + (S.h : ℝ) ≤ (3 : ℝ) ^ (S.a : ℝ) := by
    have h1 : ((S.h + 1 : ℕ) : ℝ) ≤ ((3 ^ S.a : ℕ) : ℝ) := by
      exact_mod_cast hWindowVsOffset
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast] at h1
    linarith only [h1]
  have hnn : (0 : ℝ) ≤ 1 + (S.h : ℝ) := by
    have hh : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg S.h
    linarith only [hh]
  have hexp : (S.a : ℝ) * (1 / 2) = (S.a : ℝ) / 2 := by ring
  calc (1 + (S.h : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ((3 : ℝ) ^ (S.a : ℝ)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hnn hcast (by norm_num)
    _ = (3 : ℝ) ^ ((S.a : ℝ) * (1 / 2)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (S.a : ℝ) (1 / 2)).symm
    _ = (3 : ℝ) ^ ((S.a : ℝ) / 2) := by rw [hexp]

/-- **`hCB` at the explicit offset constant `CB = oscBoundConstOffset`.**
The window-carrying constant of `oscBoundConst_le_windowCB` is dominated by the
offset-carrying one as soon as the hypothesis `_hWindowVsOffset` holds, so `hCB`
holds at an explicit `CB` that does not depend on the window. -/
theorem oscBoundConst_le_offsetBase {Cpo C C3 : ℝ} (hCpo : 0 ≤ Cpo) (hC : 0 ≤ C)
    (hC3 : 0 ≤ C3) (S : ScaleSelection) (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) :
    oscBoundConst Cpo C C3 S.h ≤ oscBoundConstOffset Cpo C C3 S := by
  refine (oscBoundConst_le_windowCB hCpo hC S.h).trans ?_
  rw [oscBoundConstWindow, oscBoundConstOffset]
  exact mul_le_mul_of_nonneg_left (windowFactor_le_offset hWindowVsOffset)
    (oscBoundConstBase_nonneg hCpo hC hC3)

/-! ## The product at the rate of the conclusion -/

/-- **The product of the printed constant with the rate, every constant named
explicitly.**  With the explicit constant
`max 1 (oscBoundConstBase Cpo C C3)`, under the hypothesis `_hWindowVsOffset`,
the product of the printed constant with the rate `3^{-(ℓ'-n)} = 3^{-2a}` of
`e.RHS.term3.B` is dominated, at the rate `3^{-a}` of the conclusion's
matching summand `3^{-(ℓ'-n)/2}`, by a constant built from the prefactors alone.

The arithmetic: `(1 + h)^{1/2} ≤ 3^{a/2}` by
`_hWindowVsOffset`, so the product is at most
`base · 3^{a/2} · 3^{-2a} = base · 3^{-3a/2} ≤ base · 3^{-a}`. -/
theorem oscBoundConst_mul_rate_le {Cpo C C3 : ℝ} (hCpo : 0 ≤ Cpo) (hC : 0 ≤ C)
    (hC3 : 0 ≤ C3) (S : ScaleSelection) (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) :
    oscBoundConst Cpo C C3 S.h * (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) ≤
      max 1 (oscBoundConstBase Cpo C C3) * (3 : ℝ) ^ (-(S.a : ℝ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hbase : (0 : ℝ) ≤ oscBoundConstBase Cpo C C3 := oscBoundConstBase_nonneg hCpo hC hC3
  have ha : (0 : ℝ) ≤ (S.a : ℝ) := Nat.cast_nonneg S.a
  -- `ℓ' - n = 2a`
  have h2a : ((S.ellPrime - S.n : ℕ) : ℝ) = 2 * (S.a : ℝ) := by
    rw [S.ellPrime_sub_n]
    push_cast
    ring
  -- the window against the offset, from the V3 binder
  have hwin : oscBoundConst Cpo C C3 S.h ≤
      oscBoundConstBase Cpo C C3 * (3 : ℝ) ^ ((S.a : ℝ) / 2) :=
    oscBoundConst_le_offsetBase hCpo hC hC3 S hWindowVsOffset
  have hrate : (0 : ℝ) ≤ (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) :=
    Real.rpow_nonneg h3.le _
  -- multiply by the nonnegative rate and combine the exponents
  have hstep : oscBoundConst Cpo C C3 S.h * (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) ≤
      oscBoundConstBase Cpo C C3 * (3 : ℝ) ^ (-(3 * (S.a : ℝ)) / 2) := by
    refine (mul_le_mul_of_nonneg_right hwin hrate).trans (le_of_eq ?_)
    have hcombine : (3 : ℝ) ^ ((S.a : ℝ) / 2) *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) =
        (3 : ℝ) ^ (-(3 * (S.a : ℝ)) / 2) := by
      have hsum : (S.a : ℝ) / 2 + -(2 * (S.a : ℝ)) = -(3 * (S.a : ℝ)) / 2 := by ring
      rw [h2a, ← Real.rpow_add h3, hsum]
    rw [mul_assoc, hcombine]
  -- `3^{-3a/2} ≤ 3^{-a}`, and `base ≤ max 1 base`
  have hexp : -(3 * (S.a : ℝ)) / 2 ≤ -(S.a : ℝ) := by
    linarith only [ha]
  have hpow : (3 : ℝ) ^ (-(3 * (S.a : ℝ)) / 2) ≤ (3 : ℝ) ^ (-(S.a : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  refine hstep.trans ?_
  calc oscBoundConstBase Cpo C C3 * (3 : ℝ) ^ (-(3 * (S.a : ℝ)) / 2)
      ≤ oscBoundConstBase Cpo C C3 * (3 : ℝ) ^ (-(S.a : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hbase
    _ ≤ max 1 (oscBoundConstBase Cpo C C3) * (3 : ℝ) ^ (-(S.a : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg h3.le _)

/-! ## The obstruction, as a theorem -/

end

end SuperdiffusionCLT.Section3.Terms
