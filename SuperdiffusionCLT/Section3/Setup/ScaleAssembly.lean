/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.PigeonholeMargin

/-!
# The scale-selection assembly and the crude scale conditions

The proof of Proposition `p.sstar.lower.bound` opens by choosing the window `h`,
running the pigeonhole subargument to get the scale `m`, and defining the four
auxiliary scales `n, ℓ, ℓ', L'`.  The proof then records the *scale
conditions* which the master inequality consumes.  This file assembles the
first half of that: it chooses `h`, produces the
`ScaleSelection`, and proves the three scale conditions `hEta`, `hCrude`,
`hScaleCond` of `Section3/Terms/MasterInequality.master_inequality`.

## The window

The print restricts `h` by `e.h.restrictions` and then
"takes `h` as large as we are permitted", i.e.
`h := ⌊c δ L / log(Cν⁻¹L)⌋`.  `optimalWindow` is that choice (with `c = C⁻¹`),
`windowRestrictions_optimalWindow` verifies both conditions of
`e.h.restrictions` for it, and `optimalWindow_size` is `e.h.optimized.size` with the constant
`optimalWindowConst C c₀ = c₀/(4C)`.

## The threshold

Every step of the print's passage uses `e.L.vs.nu` "with the constant taken
large".  The three places where this file needs
it are isolated as three explicit real hypotheses, each in the shape the proof
consumes:

* `hThresh`, `20 (K log²(ν⁻¹L) + 1) C log(Cν⁻¹L) ≤ δ L` — the largeness that
  makes the printed window `⌊δL/(C log(Cν⁻¹L))⌋` satisfy the first condition of
  `e.h.restrictions`, which the print records parenthetically;
* `hlog`, `11 ≤ log(ν⁻¹L)` — the input of `Setup.hundred_mul_scaleOffset_le`
  and of the comparability of the logarithms over the pigeonhole range;
* `hCT`, a constant `≤ ν⁻¹L` — the "increase the threshold" of the print, which turns the polynomial
  prefactors into a single power of `ν⁻¹L`.

The reduction of these three to the literal printed threshold of `e.L.vs.nu`,
which bounds `m` below by an expression in `ν` and `c⋆` alone, is the paper's
own repeated "after increasing the constant in
`e.L.vs.nu`"; it is not carried out here.

## The scale conditions

* `crudeLowerConst` and `crude_lower_bound` are the crude bound
  `σ̄_{L',*}(cu_n) ≤ Cν^{-2}L`, i.e. `σ̄_{L',*}^{-1}(cu_n) ≥ cν²L^{-1}`.
  The print derives it from `e.CG.bounds.1` and `e.km.Ltwo.size`;
  the route taken here is the annealed envelope, through
  `Section2.Annealed.inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq` and
  `sigmaBarSeq_le_envelopeUpperScalar`, so nothing is assumed.
* `localizationEta` is the print's `η_L = Cν^{-5}L3^{-(L'-m)}` and
  `localizationEta_le` is `η_L ≤ L^{-1000}`.
* `scale_condition_of_selection` is the scale condition of the print, in the form
  `master_inequality` states it (the three polynomial error groups rather than
  the printed common envelope `C(ν⁻¹L)⁹`).

Both of the last two rest on one arithmetic comparison,
`mul_poly_three_le_rpow`: a polynomial in `ν⁻¹L` times `3^{-ca}` is below any
prescribed negative power of `ν⁻¹L`, once `a ≥ K log(ν⁻¹L)` and `cK log 3` is
large.  This is exactly how the print's `a = ⌈K log(ν⁻¹L)⌉` converts a
geometric factor into a polynomial gain, with "`K` sufficiently large" made explicit as
`8056 ≤ K log 3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## The geometric-to-polynomial comparison -/

/-- `3^{-ca} ≤ (ν⁻¹L)^{-cK log 3}` when `a ≥ K log(ν⁻¹L)`: the elementary
content of the print's choice `a = ⌈K log(ν⁻¹L)⌉`, which is what
turns every geometric error `3^{-c(ℓ-n)}` of Section 3 into a power of the
scale `ν⁻¹L`. -/
private theorem three_rpow_neg_le_rpow {T K c : ℝ} {a : ℕ}
    (hT : 0 < T) (hc : 0 < c) (ha : K * Real.log T ≤ (a : ℝ)) :
    (3 : ℝ) ^ (-(c * (a : ℝ))) ≤ T ^ (-(c * K * Real.log 3)) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : (3 : ℝ) ^ (-(c * (a : ℝ))) = Real.exp (Real.log 3 * (-(c * (a : ℝ)))) :=
    Real.rpow_def_of_pos (by norm_num) _
  have h2 : T ^ (-(c * K * Real.log 3)) =
      Real.exp (Real.log T * (-(c * K * Real.log 3))) := Real.rpow_def_of_pos hT _
  rw [h1, h2]
  refine Real.exp_le_exp.2 ?_
  have hstep : c * (K * Real.log T) ≤ c * (a : ℝ) :=
    mul_le_mul_of_nonneg_left ha hc.le
  have hmul := mul_le_mul_of_nonneg_right hstep hlog3.le
  linarith only [hmul]

/-- **The polynomial-times-geometric comparison**: a
constant `A ≤ T` times `T^s 3^{-ca}` is below `T^t`, once `a ≥ K log T` and
`s + 1 - cK log 3 ≤ t`.  Here `T = ν⁻¹L`; the print uses this with `t` a large
negative number, "after increasing the threshold in `e.L.vs.nu`" and with `K`
"sufficiently large, depending only on `d`". -/
private theorem mul_poly_three_le_rpow {T A K c s t : ℝ} {a : ℕ}
    (hT : 1 ≤ T) (hc : 0 < c) (ha : K * Real.log T ≤ (a : ℝ))
    (hA0 : 0 ≤ A) (hA : A ≤ T) (hst : s + 1 - c * K * Real.log 3 ≤ t) :
    A * (T ^ s * (3 : ℝ) ^ (-(c * (a : ℝ)))) ≤ T ^ t := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have h3 := three_rpow_neg_le_rpow (K := K) (c := c) (a := a) hT0 hc ha
  have hTs : (0 : ℝ) ≤ T ^ s := Real.rpow_nonneg hT0.le s
  have heq : T ^ s * T ^ (-(c * K * Real.log 3)) = T ^ (s - c * K * Real.log 3) := by
    rw [← Real.rpow_add hT0]
    ring_nf
  have hstep1 : T ^ s * (3 : ℝ) ^ (-(c * (a : ℝ))) ≤ T ^ (s - c * K * Real.log 3) := by
    calc T ^ s * (3 : ℝ) ^ (-(c * (a : ℝ)))
        ≤ T ^ s * T ^ (-(c * K * Real.log 3)) := mul_le_mul_of_nonneg_left h3 hTs
      _ = T ^ (s - c * K * Real.log 3) := heq
  have hrnn : (0 : ℝ) ≤ T ^ (s - c * K * Real.log 3) := Real.rpow_nonneg hT0.le _
  have hfin : T * T ^ (s - c * K * Real.log 3) = T ^ (1 + (s - c * K * Real.log 3)) := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  calc A * (T ^ s * (3 : ℝ) ^ (-(c * (a : ℝ))))
      ≤ A * T ^ (s - c * K * Real.log 3) := mul_le_mul_of_nonneg_left hstep1 hA0
    _ ≤ T * T ^ (s - c * K * Real.log 3) := mul_le_mul_of_nonneg_right hA hrnn
    _ = T ^ (1 + (s - c * K * Real.log 3)) := hfin
    _ ≤ T ^ t := Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hst])

/-! ## The optimized window `h` -/

/-- **The optimized window**, "we take `h` as large as we are permitted":
by the second condition of `e.h.restrictions` this means
`h = ⌊c δ L / log(Cν⁻¹L)⌋`, here with `c = C⁻¹`. -/
def optimalWindow (C delta nu : ℝ) (L : ℕ) : ℕ :=
  ⌊delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ))))⌋₊

/-- The constant of `e.h.optimized.size` produced by the choice
`optimalWindow`: with `δ = c₀c⋆²` the window satisfies
`h ≥ (c₀/(4C)) c⋆² L / log(ν⁻¹L)`. -/
def optimalWindowConst (C c0 : ℝ) : ℝ := c0 / (4 * C)

theorem optimalWindowConst_pos {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0) :
    0 < optimalWindowConst C c0 := by
  rw [optimalWindowConst]
  exact div_pos hc0 (by linarith only [hC])

/-- `log(Cν⁻¹L) = log C + log(ν⁻¹L)`, the only place the constant inside the
logarithm of `e.h.restrictions` is opened. -/
private theorem log_const_mul {C nu : ℝ} {L : ℕ} (hC : 0 < C) (hnu : 0 < nu)
    (hL : 1 ≤ L) :
    Real.log (C * (nu⁻¹ * (L : ℝ))) = Real.log C + Real.log (nu⁻¹ * (L : ℝ)) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  exact Real.log_mul (ne_of_gt hC) (ne_of_gt (mul_pos (inv_pos.2 hnu) hL0))

/-- `A/B · (B·x/A) = x`, used to read the second condition of
`e.h.restrictions` off the floor bound for `optimalWindow`. -/
private theorem div_mul_div_cancel_aux {A B x : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    A / B * (B * x / A) = x := by
  field_simp

/-- The real-arithmetic core of `optimalWindow_size`: from `X − 1 < h` for
`X = δ LL/(C·LC)`, from `Λ ≤ LC ≤ 2Λ` and from `20 C Λ ≤ δ LL`, one gets
`δ LL/(4C) ≤ h Λ`. -/
private theorem optimalWindow_size_arith {Lam LC C delta LL hh : ℝ}
    (hC0 : 0 < C) (hLampos : 0 < Lam) (hLCge : Lam ≤ LC) (hLCle : LC ≤ 2 * Lam)
    (hLL : 0 ≤ LL) (hdelta : 0 < delta)
    (hXgt : delta * LL / (C * LC) - 1 < hh)
    (hthr2 : 20 * C * Lam ≤ delta * LL) :
    delta * LL / (4 * C) ≤ hh * Lam := by
  have hLamne : Lam ≠ 0 := ne_of_gt hLampos
  have hCne : C ≠ 0 := ne_of_gt hC0
  have hLCpos : (0 : ℝ) < LC := lt_of_lt_of_le hLampos hLCge
  have hCLC : (0 : ℝ) < C * LC := mul_pos hC0 hLCpos
  have hXlow : delta * LL / (C * (2 * Lam)) ≤ delta * LL / (C * LC) :=
    div_le_div_of_nonneg_left (mul_nonneg hdelta.le hLL) hCLC
      (mul_le_mul_of_nonneg_left hLCle hC0.le)
  have hval : delta * LL / (C * (2 * Lam)) * Lam = delta * LL / (2 * C) := by
    field_simp
  have hCLam : (0 : ℝ) ≤ C * Lam := mul_nonneg hC0.le hLampos.le
  have hLamsmall : Lam ≤ delta * LL / (4 * C) := by
    rw [le_div_iff₀ (by linarith only [hC0])]
    linarith only [hthr2, hCLam]
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hXgt) hLampos.le
  have hmul2 := mul_le_mul_of_nonneg_right hXlow hLampos.le
  have hhalf : delta * LL / (2 * C) - delta * LL / (4 * C) = delta * LL / (4 * C) := by
    field_simp
    ring
  linarith only [hmul, hmul2, hval, hLamsmall, hhalf]

/-- **The two conditions of `e.h.restrictions` hold for the
optimized window** `optimalWindow C δ ν L`, under the largeness `hThresh` of
`e.L.vs.nu` (the print's parenthesis, "the lower bound
`h ≥ 10⌈K log²(ν⁻¹L)⌉` is satisfied under `e.L.vs.nu`"). -/
theorem windowRestrictions_optimalWindow {C K nu delta : ℝ} {L : ℕ}
    (hC : 0 < C) (hdelta : 0 < delta)
    (hlogC : 0 < Real.log (C * (nu⁻¹ * (L : ℝ))))
    (hK2 : 0 ≤ K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2)
    (hThresh : 20 * (K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1) *
      (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) ≤ delta * (L : ℝ)) :
    WindowRestrictions C K nu delta L (optimalWindow C delta nu L) := by
  have hCLC : (0 : ℝ) < C * Real.log (C * (nu⁻¹ * (L : ℝ))) := mul_pos hC hlogC
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hXnn : (0 : ℝ) ≤ delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) :=
    div_nonneg (mul_nonneg hdelta.le hL0) hCLC.le
  have hXle : ((optimalWindow C delta nu L : ℕ) : ℝ) ≤
      delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) := Nat.floor_le hXnn
  have hXgt : delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) - 1 <
      ((optimalWindow C delta nu L : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one
      (delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))))
    have hrw : ((optimalWindow C delta nu L : ℕ) : ℝ) =
        (⌊delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ))))⌋₊ : ℝ) := rfl
    linarith only [this, hrw]
  have hXbig : 20 * (K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1) ≤
      delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) :=
    (le_div_iff₀ hCLC).2 hThresh
  refine ⟨hdelta, ?_, ?_⟩
  · have hceil : ((⌈K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2⌉₊ : ℕ) : ℝ) <
        K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1 := Nat.ceil_lt_add_one hK2
    have hgoal : ((10 * ⌈K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2⌉₊ : ℕ) : ℝ) ≤
        ((optimalWindow C delta nu L : ℕ) : ℝ) := by
      have hcast : ((10 * ⌈K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2⌉₊ : ℕ) : ℝ) =
          10 * ((⌈K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2⌉₊ : ℕ) : ℝ) := by
        push_cast
        ring
      linarith only [hcast, hceil, hXgt, hXbig, hK2]
    exact_mod_cast hgoal
  · have hstep : C * Real.log (C * (nu⁻¹ * (L : ℝ))) / delta *
          ((optimalWindow C delta nu L : ℕ) : ℝ) ≤
        C * Real.log (C * (nu⁻¹ * (L : ℝ))) / delta *
          (delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ))))) :=
      mul_le_mul_of_nonneg_left hXle (by positivity)
    have hval : C * Real.log (C * (nu⁻¹ * (L : ℝ))) / delta *
        (delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))))  = (L : ℝ) :=
      div_mul_div_cancel_aux (ne_of_gt hCLC) (ne_of_gt hdelta)
    linarith only [hstep, hval]

/-- **`e.h.optimized.size`**: the optimized window is at least
`(c₀/(4C)) c⋆² L / log(ν⁻¹L)`, in the division-free form the master argument
uses (`hHsize` of `Terms.sstar_lower_bound_of_terms`).  The hypothesis
`hlogCle` is `log C ≤ log(ν⁻¹L)`, one more instance of the threshold
`e.L.vs.nu` taken large. -/
theorem optimalWindow_size {C K nu delta c0 cStar : ℝ} {L : ℕ}
    (hC : 1 ≤ C) (hnu : 0 < nu) (hL : 1 ≤ L) (hdelta : 0 < delta)
    (hdeltaeq : delta = smallnessParameter c0 cStar)
    (hlog1 : 1 ≤ Real.log (nu⁻¹ * (L : ℝ)))
    (hlogCle : Real.log C ≤ Real.log (nu⁻¹ * (L : ℝ)))
    (hK2 : 0 ≤ K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2)
    (hThresh : 20 * (K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1) *
      (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) ≤ delta * (L : ℝ)) :
    optimalWindowConst C c0 * cStar ^ (2 : ℕ) * (L : ℝ) ≤
      ((optimalWindow C delta nu L : ℕ) : ℝ) * Real.log (nu⁻¹ * (L : ℝ)) := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hlogC0 : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC
  have hsplit := log_const_mul (C := C) (nu := nu) (L := L) hC0 hnu hL
  have hLampos : (0 : ℝ) < Real.log (nu⁻¹ * (L : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hlog1
  have hLCge : Real.log (nu⁻¹ * (L : ℝ)) ≤ Real.log (C * (nu⁻¹ * (L : ℝ))) := by
    rw [hsplit]
    linarith only [hlogC0]
  have hLCle : Real.log (C * (nu⁻¹ * (L : ℝ))) ≤ 2 * Real.log (nu⁻¹ * (L : ℝ)) := by
    rw [hsplit]
    linarith only [hlogCle]
  have hlogCpos : (0 : ℝ) < Real.log (C * (nu⁻¹ * (L : ℝ))) :=
    lt_of_lt_of_le hLampos hLCge
  have hCLC : (0 : ℝ) < C * Real.log (C * (nu⁻¹ * (L : ℝ))) := mul_pos hC0 hlogCpos
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hXgt : delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) - 1 <
      ((optimalWindow C delta nu L : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one
      (delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ)))))
    have hrw : ((optimalWindow C delta nu L : ℕ) : ℝ) =
        (⌊delta * (L : ℝ) / (C * Real.log (C * (nu⁻¹ * (L : ℝ))))⌋₊ : ℝ) := rfl
    linarith only [this, hrw]
  have hthr2 : 20 * C * Real.log (nu⁻¹ * (L : ℝ)) ≤ delta * (L : ℝ) := by
    have hA : (1 : ℝ) ≤ K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1 := by linarith only [hK2]
    have hB : (0 : ℝ) < C * Real.log (nu⁻¹ * (L : ℝ)) := mul_pos hC0 hLampos
    have hpos : (0 : ℝ) ≤ 20 * (K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1) := by
      linarith only [hK2]
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 20)) hB.le
    have h2 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hLCge hC0.le) hpos
    linarith only [h1, h2, hThresh]
  have hcore := optimalWindow_size_arith (Lam := Real.log (nu⁻¹ * (L : ℝ)))
    (LC := Real.log (C * (nu⁻¹ * (L : ℝ)))) (C := C) (delta := delta) (LL := (L : ℝ))
    (hh := ((optimalWindow C delta nu L : ℕ) : ℝ)) hC0 hLampos hLCge hLCle hL0 hdelta
    hXgt hthr2
  have hgoal : optimalWindowConst C c0 * cStar ^ (2 : ℕ) * (L : ℝ) =
      delta * (L : ℝ) / (4 * C) := by
    rw [optimalWindowConst, hdeltaeq, smallnessParameter]
    field_simp
  rw [hgoal]
  exact hcore

/-! ## The scale selection -/

section Selection

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The scale selection**, assembled: from the window
restrictions `e.h.restrictions` for the optimized window, the
pigeonhole subargument produces the scale
`m ∈ ℕ ∩ [L/4, L/2]` at which the annealed scalars of the scales `m` and
`m − 2h` are `δ`-comparable, and `e.scale.selection` builds
from it the package `S` of the four auxiliary scales `n, ℓ, ℓ', L'` with the
ordering `e.scales.ordering`, the window comparison
`h ≥ 100a`, and `2h ≤ m`.

The conclusion also records `L/4 < n`, which is what makes the cube scale of
the homogenization comparison `e.bell.vs.starell` large.

The hypotheses `hlog`, `hlogCle` and `hThresh` are the three uses of the
threshold `e.L.vs.nu` isolated in the module docstring. -/
theorem exists_scaleSelection_of_threshold {C K delta : ℝ}
    (hnu1 : nu ≤ 1) (hL : 1 ≤ L) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : (1 : ℝ) ≤ K) (hlog : 11 ≤ Real.log (nu⁻¹ * (L : ℝ)))
    (hC : cutoffEnvelopeConst d ≤ C) (hClarge : 64 ≤ C)
    (hThresh : 20 * (K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 + 1) *
      (C * Real.log (C * (nu⁻¹ * (L : ℝ)))) ≤ delta * (L : ℝ)) :
    ∃ S : ScaleSelection, S.L = L ∧ S.h = optimalWindow C delta nu L ∧
      S.a = scaleOffset K nu L ∧ ScalesOrdering S ∧
      2 * S.h ≤ S.m ∧ 100 * S.a ≤ S.h ∧ 10 ≤ S.h ∧ L / 4 < S.n ∧
      L / 4 + 2 * S.h ≤ S.m ∧ S.m ≤ L / 2 ∧
      sigmaBarSeq nu L P (S.m - 2 * S.h) ≤ (1 + delta) * sigmaBarSeq nu L P S.m ∧
      sigmaBarStarInvSeq nu L P (S.m - 2 * S.h) ≤
        (1 + delta) * sigmaBarStarInvSeq nu L P S.m := by
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hClarge
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hlog1 : (1 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by linarith only [hlog]
  have hlogCpos : (0 : ℝ) < Real.log (C * (nu⁻¹ * (L : ℝ))) := by
    have hsplit := log_const_mul (C := C) (nu := nu) (L := L) hC0 hnu hL
    have hlogC0 : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC1
    rw [hsplit]
    linarith only [hlog1, hlogC0]
  have hK2 : (0 : ℝ) ≤ K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 := by positivity
  have hres : WindowRestrictions C K nu delta L (optimalWindow C delta nu L) :=
    windowRestrictions_optimalWindow hC0 hdelta hlogCpos hK2 hThresh
  obtain ⟨m, hm1, hm2, hm3, -, hup, hlo⟩ :=
    exists_pigeonhole_scale_of_windowRestrictions hnu L hPrefix hJ2 hJ3 hJ4 hnu1 hL
      hdelta hdelta1 hKpos hlog1 hres hC hClarge
  have hah : 2 * scaleOffset K nu L < optimalWindow C delta nu L :=
    two_mul_scaleOffset_lt hKpos hlog1 hres
  have h100 : 100 * scaleOffset K nu L ≤ optimalWindow C delta nu L :=
    hundred_mul_scaleOffset_le hK hlog hres
  have hapos : 0 < scaleOffset K nu L :=
    scaleOffset_pos (mul_pos hKpos (lt_of_lt_of_le zero_lt_one hlog1))
  have hmside : optimalWindow C delta nu L + 2 * scaleOffset K nu L ≤ m :=
    ScaleSelection.ofBase_hm_of_two_mul_h_le hm3 hah
  have h10 : 10 ≤ optimalWindow C delta nu L := by
    have hceilpos : 0 < ⌈K * Real.log (nu⁻¹ * (L : ℝ)) ^ 2⌉₊ :=
      Nat.ceil_pos.2 (mul_pos hKpos (pow_pos (lt_of_lt_of_le zero_lt_one hlog1) 2))
    have := hres.ceil_le
    omega
  refine ⟨ScaleSelection.ofBase L m (optimalWindow C delta nu L)
    (scaleOffset K nu L) hmside, rfl, rfl, rfl, ?_, hm3, h100, h10, ?_, hm1, hm2,
    hup, hlo⟩
  · exact scalesOrdering_of_lt hapos hah
      (scalesOrdering_hL_of_pigeonhole_scale hm3 hah hm2)
  · show L / 4 < m - optimalWindow C delta nu L - 2 * scaleOffset K nu L
    omega

end Selection

/-! ## The crude bound `σ̄_{L',*}(cu_n) ≤ Cν^{-2}L` -/

/-- The constant of the crude lower bound,
`σ̄_{L',*}^{-1}(cu_n) ≥ c ν² L^{-1}`, in the normalization of the
envelope: `c = (1 + 2 C_env(d))^{-1}`. -/
def crudeLowerConst (d : ℕ) : ℝ := (1 + 2 * cutoffEnvelopeConst d)⁻¹

theorem crudeLowerConst_pos (d : ℕ) : 0 < crudeLowerConst d := by
  have h := cutoffEnvelopeConst_pos d
  rw [crudeLowerConst]
  exact inv_pos.2 (by linarith only [h])

section Crude

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (LPrime : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **The crude deterministic bound**,
`σ̄_{L',*}(cu_n) ≤ Cν^{-2}L`, in the inverted form
`σ̄_{L',*}^{-1}(cu_n) ≥ c₀ν²L^{-1}` in which the master inequality uses it
(`hCrude` of `Terms.master_inequality`).  The print obtains it from
`e.CG.bounds.1` and `e.km.Ltwo.size`; the route here is the annealed
envelope of `Section2/Annealed/Envelope.lean`, through the contrast inequality
`inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq` and the upper envelope
`sigmaBarSeq_le_envelopeUpperScalar`, so no further input is used. -/
theorem crude_lower_bound (hnu1 : nu ≤ 1) {L n : ℕ} (hL : 1 ≤ L)
    (hLP : LPrime ≤ L) :
    crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹ ≤
      sigmaBarStarInvSeq nu LPrime P n := by
  have hCe := cutoffEnvelopeConst_pos d
  have hL0 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hnuinvL : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := by
          exact mul_le_mul hnuinv hL0 zero_le_one (by linarith only [hnuinv])
  -- the envelope bound at the base scale
  have henv := sigmaBarSeq_le_envelopeUpperScalar hnu LPrime hPrefix hJ2 hJ3 hJ4 0
  have hmax : max 1 ((LPrime : ℕ) : ℝ) ≤ (L : ℝ) := by
    refine max_le hL0 ?_
    exact_mod_cast hLP
  have henv2 : envelopeUpperScalar d nu LPrime ≤
      (1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)) := by
    have hterm : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 ((LPrime : ℕ) : ℝ) ≤
        2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    have hnusmall : nu ≤ nu⁻¹ * (L : ℝ) := le_trans hnu1 hnuinvL
    rw [envelopeUpperScalar]
    linarith only [hterm, hnusmall]
  have hbtpos := sigmaBarSeq_pos hnu LPrime hPrefix hJ2 hJ3 hJ4 0
  have hApos : (0 : ℝ) < (1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)) := by
    have : (0 : ℝ) < 1 + 2 * cutoffEnvelopeConst d := by linarith only [hCe]
    exact mul_pos this (by linarith only [hnuinvL])
  have hinv : ((1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)))⁻¹ ≤
      (sigmaBarSeq nu LPrime P 0)⁻¹ :=
    (inv_le_inv₀ hApos hbtpos).2 (le_trans henv henv2)
  have hchain := inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq hnu LPrime hPrefix hJ2
    hJ3 hJ4 n
  have hval : ((1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)))⁻¹ =
      crudeLowerConst d * nu * (L : ℝ)⁻¹ := by
    have h1 : (1 + 2 * cutoffEnvelopeConst d) ≠ 0 := by positivity
    have h2 : nu ≠ 0 := ne_of_gt hnu
    have h3 : (L : ℝ) ≠ 0 := by linarith only [hL0]
    rw [crudeLowerConst]
    field_simp
  have hsq : crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹ ≤
      crudeLowerConst d * nu * (L : ℝ)⁻¹ := by
    have hc := crudeLowerConst_pos d
    have hnn : nu ^ (2 : ℕ) ≤ nu := by
      have := mul_le_mul_of_nonneg_left hnu1 hnu.le
      calc nu ^ (2 : ℕ) = nu * nu := by ring
        _ ≤ nu * 1 := this
        _ = nu := mul_one nu
    have hLinv : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnn hc.le) hLinv
    linarith only [this]
  calc crudeLowerConst d * nu ^ (2 : ℕ) * (L : ℝ)⁻¹
      ≤ crudeLowerConst d * nu * (L : ℝ)⁻¹ := hsq
    _ = ((1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)))⁻¹ := hval.symm
    _ ≤ (sigmaBarSeq nu LPrime P 0)⁻¹ := hinv
    _ ≤ sigmaBarStarInvSeq nu LPrime P n := hchain

end Crude

/-! ## Powers of the scale `ν⁻¹L` -/

/-- `ν^{-s} A ≤ (ν⁻¹L)^t` whenever `0 ≤ s ≤ t` and `A ≤ L^t`: the elementary
step by which every polynomial prefactor is absorbed into a
power of the scale `ν⁻¹L`. -/
private theorem nu_rpow_neg_mul_le {nu A s t : ℝ} {L : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hst : s ≤ t)
    (hA0 : 0 ≤ A) (hAL : A ≤ (L : ℝ) ^ t) :
    nu ^ (-s) * A ≤ (nu⁻¹ * (L : ℝ)) ^ t := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hneg : nu ^ (-s) = (nu⁻¹) ^ s := by
    rw [Real.inv_rpow hnu.le, Real.rpow_neg hnu.le]
  have hmono : (nu⁻¹) ^ s ≤ (nu⁻¹) ^ t :=
    Real.rpow_le_rpow_of_exponent_le hinv1 hst
  have hnn : (0 : ℝ) ≤ (nu⁻¹) ^ t := Real.rpow_nonneg (by positivity) t
  have hsplit : (nu⁻¹ * (L : ℝ)) ^ t = (nu⁻¹) ^ t * (L : ℝ) ^ t :=
    Real.mul_rpow (by positivity) hLnn
  rw [hneg, hsplit]
  exact mul_le_mul hmono hAL hA0 hnn

/-- `(ν⁻¹L)^{-r} ≤ L^{-r}` for `r ≥ 0`: the scale `ν⁻¹L` is at least `L`. -/
private theorem scale_rpow_neg_le {nu : ℝ} {L : ℕ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    (nu⁻¹ * (L : ℝ)) ^ (-r) ≤ (L : ℝ) ^ (-r) := by
  have hL0 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hle : (L : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    have := mul_le_mul_of_nonneg_right hinv1 (by linarith only [hL0] : (0:ℝ) ≤ (L:ℝ))
    linarith only [this]
  have hLpos : (0 : ℝ) < (L : ℝ) ^ r := Real.rpow_pos_of_pos (by linarith only [hL0]) r
  have hTpos : (0 : ℝ) < (nu⁻¹ * (L : ℝ)) ^ r :=
    Real.rpow_pos_of_pos (by linarith only [hL0, hle]) r
  have hpow : (L : ℝ) ^ r ≤ (nu⁻¹ * (L : ℝ)) ^ r :=
    Real.rpow_le_rpow (by linarith only [hL0]) hle hr
  rw [Real.rpow_neg (by linarith only [hL0, hle]), Real.rpow_neg (by linarith only [hL0])]
  exact (inv_le_inv₀ hTpos hLpos).2 hpow

/-- `(ν⁻¹L)^{-1002} ≤ ν² L^{-1000}`: the right-hand side of the scale
condition dominates the power of the scale that the left-hand
side is bounded by. -/
private theorem scale_rpow_neg_le_nu_sq {nu : ℝ} {L : ℕ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (hL : 1 ≤ L) :
    (nu⁻¹ * (L : ℝ)) ^ (-(1002 : ℝ)) ≤ nu ^ (2 : ℕ) * (L : ℝ) ^ (-(1000 : ℝ)) := by
  have hL0 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by linarith only [hL0]
  have hsplit : (nu⁻¹ * (L : ℝ)) ^ (-(1002 : ℝ)) =
      (nu⁻¹) ^ (-(1002 : ℝ)) * (L : ℝ) ^ (-(1002 : ℝ)) :=
    Real.mul_rpow (by positivity) hLnn
  have hnuside : (nu⁻¹) ^ (-(1002 : ℝ)) = nu ^ (1002 : ℝ) := by
    rw [Real.inv_rpow hnu.le, Real.rpow_neg hnu.le, inv_inv]
  have hnusq : nu ^ (1002 : ℝ) ≤ nu ^ (2 : ℕ) := by
    have hval : nu ^ (2 : ℝ) = nu ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← hval]
    exact Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hLside : (L : ℝ) ^ (-(1002 : ℝ)) ≤ (L : ℝ) ^ (-(1000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL0 (by norm_num)
  have hnn1 : (0 : ℝ) ≤ (L : ℝ) ^ (-(1002 : ℝ)) := Real.rpow_nonneg hLnn _
  have hnn2 : (0 : ℝ) ≤ nu ^ (2 : ℕ) := by positivity
  rw [hsplit, hnuside]
  exact mul_le_mul hnusq hLside hnn1 hnn2

/-! ## The localization error `η_L` -/

/-- **`η_L = Cν^{-5}L3^{-(L'-m)}`**, the localization error (the
sentence "Set `η_L := Cν^{-5}L3^{-(L'-m)}`"), as a function of the gap
`k = L' − m`. -/
def localizationEta (Ceta nu : ℝ) (L k : ℕ) : ℝ :=
  Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) * (3 : ℝ) ^ (-(k : ℝ))

/-- **`η_L ≤ L^{-1000}`**, the last scale condition, at the
printed gap `L' − m = 2a` with `a ≥ K log(ν⁻¹L)`.  The largeness of `K`
("choose the parameter `K` sufficiently large, depending only on `d`") is
explicit as `8056 ≤ K log 3`, and the largeness of the threshold in
`e.L.vs.nu` as `Ceta ≤ ν⁻¹L`. -/
theorem localizationEta_le {Ceta K nu : ℝ} {L a : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ L)
    (hCeta : 0 ≤ Ceta) (hCT : Ceta ≤ nu⁻¹ * (L : ℝ))
    (hKlog3 : 8056 ≤ K * Real.log 3)
    (ha : K * Real.log (nu⁻¹ * (L : ℝ)) ≤ (a : ℝ)) :
    localizationEta Ceta nu L (2 * a) ≤ (L : ℝ) ^ (-(1000 : ℝ)) := by
  have hL0 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hT1 : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    have := mul_le_mul hinv1 hL0 zero_le_one (by linarith only [hinv1])
    linarith only [this]
  have hLpow : (L : ℝ) ≤ (L : ℝ) ^ (5 : ℝ) := by
    have hnat : (L : ℝ) ^ (1 : ℕ) ≤ (L : ℝ) ^ (5 : ℕ) :=
      pow_le_pow_right₀ hL0 (by norm_num)
    have hval : (L : ℝ) ^ (5 : ℝ) = (L : ℝ) ^ (5 : ℕ) := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hval, pow_one] at *
    exact hnat
  have hP : nu ^ (-(5 : ℝ)) * (L : ℝ) ≤ (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) :=
    nu_rpow_neg_mul_le hnu hnu1 le_rfl (by linarith only [hL0]) hLpow
  have hcast : (((2 * a : ℕ) : ℝ)) = 2 * (a : ℝ) := by push_cast; ring
  have hgnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * (a : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := mul_poly_three_le_rpow (T := nu⁻¹ * (L : ℝ)) (A := Ceta) (K := K)
    (c := 2) (s := 5) (t := -(1000 : ℝ)) (a := a) hT1 (by norm_num) ha hCeta hCT
    (by linarith only [hKlog3])
  have hfinal := scale_rpow_neg_le (nu := nu) (L := L) hnu hnu1 hL
    (r := (1000 : ℝ)) (by norm_num)
  have hstep : localizationEta Ceta nu L (2 * a) ≤
      Ceta * ((nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) * (3 : ℝ) ^ (-(2 * (a : ℝ)))) := by
    rw [localizationEta, hcast]
    have hmul : nu ^ (-(5 : ℝ)) * (L : ℝ) * (3 : ℝ) ^ (-(2 * (a : ℝ))) ≤
        (nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) * (3 : ℝ) ^ (-(2 * (a : ℝ))) :=
      mul_le_mul_of_nonneg_right hP hgnn
    have hrw : Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) * (3 : ℝ) ^ (-(2 * (a : ℝ))) =
        Ceta * (nu ^ (-(5 : ℝ)) * (L : ℝ) * (3 : ℝ) ^ (-(2 * (a : ℝ)))) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hmul hCeta
  calc localizationEta Ceta nu L (2 * a)
      ≤ Ceta * ((nu⁻¹ * (L : ℝ)) ^ (5 : ℝ) * (3 : ℝ) ^ (-(2 * (a : ℝ)))) := hstep
    _ ≤ (nu⁻¹ * (L : ℝ)) ^ (-(1000 : ℝ)) := hkey
    _ ≤ (L : ℝ) ^ (-(1000 : ℝ)) := hfinal

/-! ## The scale condition -/

/-- The real-arithmetic core of the scale condition: three polynomial
prefactors below a common power `T4` of the scale, seven geometric factors
below a common `G`, and the resulting single product below the target. -/
private theorem scale_condition_arith
    {C1 C2 C3 A1 A2 A3 B1 B2 B3 T4 G g1 g2 g3 g4 g5 g6 g7 R : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (h1 : A1 * B1 ≤ T4) (h2 : A2 * B2 ≤ T4) (h3 : A3 * B3 ≤ T4)
    (hT4 : 0 ≤ T4)
    (hg1 : g1 ≤ G) (hg2 : g2 ≤ G) (hg3 : g3 ≤ G) (hg4 : g4 ≤ G)
    (hg5 : g5 ≤ G) (hg6 : g6 ≤ G) (hg7 : g7 ≤ G)
    (hg1n : 0 ≤ g1) (hg2n : 0 ≤ g2) (hg3n : 0 ≤ g3) (hg4n : 0 ≤ g4)
    (hg5n : 0 ≤ g5) (hg6n : 0 ≤ g6) (hg7n : 0 ≤ g7)
    (hfin : (2 * C1 + C2 + 4 * C3) * (T4 * G) ≤ R) :
    C1 * A1 * B1 * (g1 + g2) + C2 * A2 * B2 * g3 +
        C3 * A3 * B3 * (g4 + g5 + g6 + g7) ≤ R := by
  have e1 : C1 * A1 * B1 * (g1 + g2) = C1 * (A1 * B1) * (g1 + g2) := by ring
  have e2 : C2 * A2 * B2 * g3 = C2 * (A2 * B2) * g3 := by ring
  have e3 : C3 * A3 * B3 * (g4 + g5 + g6 + g7) =
      C3 * (A3 * B3) * (g4 + g5 + g6 + g7) := by ring
  have b1 : C1 * (A1 * B1) * (g1 + g2) ≤ C1 * T4 * (2 * G) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 hC1) (by linarith only [hg1, hg2])
      (by linarith only [hg1n, hg2n]) (mul_nonneg hC1 hT4)
  have b2 : C2 * (A2 * B2) * g3 ≤ C2 * T4 * G :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 hC2) hg3 hg3n (mul_nonneg hC2 hT4)
  have b3 : C3 * (A3 * B3) * (g4 + g5 + g6 + g7) ≤ C3 * T4 * (4 * G) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h3 hC3)
      (by linarith only [hg4, hg5, hg6, hg7])
      (by linarith only [hg4n, hg5n, hg6n, hg7n]) (mul_nonneg hC3 hT4)
  have esum : C1 * T4 * (2 * G) + C2 * T4 * G + C3 * T4 * (4 * G) =
      (2 * C1 + C2 + 4 * C3) * (T4 * G) := by ring
  linarith only [e1, e2, e3, b1, b2, b3, esum, hfin]

/-- **The scale condition**, in the form `master_inequality`
consumes it (`hScaleCond`): the three polynomial error groups of
`e.RHS.term1`, `e.RHS.term2` and `e.RHS.term3`, at the scales of
`e.scale.selection`, are together below `ν²L^{-1000}`.

Every geometric factor is at least `3^{-a/8}` with `a = ℓ − n`, because
`ℓ' − ℓ = a`, `ℓ' − n = 2a` and `h ≥ 100a`; every
polynomial prefactor is at most `(ν⁻¹L)^4`; and `a ≥ K log(ν⁻¹L)` converts the
geometric factor into `(ν⁻¹L)^{-K log 3/8}`.  The largeness of `K`
is explicit as `8056 ≤ K log 3` and the largeness of the threshold in
`e.L.vs.nu` as `2C₁ + C₂ + 4C₃ ≤ ν⁻¹L`. -/
theorem scale_condition_of_selection {C1 C2 C3 K nu : ℝ} {S : ScaleSelection}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 1 ≤ S.L)
    (hellL : S.ell ≤ S.L) (hLPL : S.LPrime ≤ S.L) (hhL : S.h ≤ S.L)
    (hah : S.a ≤ S.h) (hKlog3 : 8056 ≤ K * Real.log 3)
    (ha : K * Real.log (nu⁻¹ * (S.L : ℝ)) ≤ (S.a : ℝ))
    (hCT : 2 * C1 + C2 + 4 * C3 ≤ nu⁻¹ * (S.L : ℝ)) :
    C1 * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
          ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
            (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) +
        C2 * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
        C3 * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
          ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
            (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
            (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 8))) ≤
      nu ^ (2 : ℕ) * (S.L : ℝ) ^ (-(1000 : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ (S.L : ℝ) := by exact_mod_cast hL
  have hLnn : (0 : ℝ) ≤ (S.L : ℝ) := by linarith only [hL1]
  have hann : (0 : ℝ) ≤ (S.a : ℝ) := Nat.cast_nonneg _
  have hL4 : (S.L : ℝ) ^ (4 : ℝ) = (S.L : ℝ) ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hellR : (S.ell : ℝ) ≤ (S.L : ℝ) := by exact_mod_cast hellL
  have hLPR : ((S.LPrime : ℕ) : ℝ) ≤ (S.L : ℝ) := by exact_mod_cast hLPL
  have hhR : (S.h : ℝ) ≤ (S.L : ℝ) := by exact_mod_cast hhL
  have hahR : (S.a : ℝ) ≤ (S.h : ℝ) := by exact_mod_cast hah
  -- the three polynomial prefactors, each below `(ν⁻¹L)^4`
  have hb1 : (S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ) ≤ (S.L : ℝ) ^ (4 : ℝ) := by
    rw [hL4]
    calc (S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)
        ≤ (S.L : ℝ) ^ (2 : ℕ) * (S.L : ℝ) :=
          mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hellR 2) hhR
            (Nat.cast_nonneg _) (pow_nonneg hLnn 2)
      _ = (S.L : ℝ) ^ (3 : ℕ) := by ring
      _ ≤ (S.L : ℝ) ^ (4 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
  have hb2 : ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) ≤ (S.L : ℝ) ^ (4 : ℝ) := by
    rw [hL4]
    calc ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) ≤ (S.L : ℝ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hLPR 2
      _ ≤ (S.L : ℝ) ^ (4 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
  have hb3 : ((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ) ≤ (S.L : ℝ) ^ (4 : ℝ) := by
    rw [hL4]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hLPR 4
  have hP1 : nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) ≤
      (nu⁻¹ * (S.L : ℝ)) ^ (4 : ℝ) :=
    nu_rpow_neg_mul_le hnu hnu1 (by norm_num) (by positivity) hb1
  have hP2 : nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      (nu⁻¹ * (S.L : ℝ)) ^ (4 : ℝ) :=
    nu_rpow_neg_mul_le hnu hnu1 (by norm_num) (by positivity) hb2
  have hP3 : nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) ≤
      (nu⁻¹ * (S.L : ℝ)) ^ (4 : ℝ) :=
    nu_rpow_neg_mul_le hnu hnu1 le_rfl (by positivity) hb3
  -- the seven geometric factors, each below `3^{-a/8}`
  have hthree : (1 : ℝ) ≤ 3 := by norm_num
  have hgle : ∀ u : ℝ, (1 : ℝ) / 8 * (S.a : ℝ) ≤ u →
      (3 : ℝ) ^ (-u) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 8 * (S.a : ℝ))) := by
    intro u hu
    exact Real.rpow_le_rpow_of_exponent_le hthree (by linarith only [hu])
  have hgnn : ∀ u : ℝ, (0 : ℝ) ≤ (3 : ℝ) ^ (-u) := fun u =>
    Real.rpow_nonneg (by norm_num) _
  have hen : ((S.ell - S.n : ℕ) : ℝ) = (S.a : ℝ) := by rw [S.ell_sub_n]
  have hpe : ((S.ellPrime - S.ell : ℕ) : ℝ) = (S.a : ℝ) := by rw [S.ellPrime_sub_ell]
  have hpn : ((S.ellPrime - S.n : ℕ) : ℝ) = 2 * (S.a : ℝ) := by
    rw [S.ellPrime_sub_n]; push_cast; ring
  -- the final comparison
  have hT1 : (1 : ℝ) ≤ nu⁻¹ * (S.L : ℝ) := by
    have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have := mul_le_mul hinv1 hL1 zero_le_one (by linarith only [hinv1])
    linarith only [this]
  have hCnn : (0 : ℝ) ≤ 2 * C1 + C2 + 4 * C3 := by linarith only [hC1, hC2, hC3]
  have hkey := mul_poly_three_le_rpow (T := nu⁻¹ * (S.L : ℝ))
    (A := 2 * C1 + C2 + 4 * C3) (K := K) (c := (1 : ℝ) / 8) (s := (4 : ℝ))
    (t := -(1002 : ℝ)) (a := S.a) hT1 (by norm_num) ha hCnn hCT
    (by linarith only [hKlog3])
  have hfin : (2 * C1 + C2 + 4 * C3) *
      ((nu⁻¹ * (S.L : ℝ)) ^ (4 : ℝ) * (3 : ℝ) ^ (-((1 : ℝ) / 8 * (S.a : ℝ)))) ≤
      nu ^ (2 : ℕ) * (S.L : ℝ) ^ (-(1000 : ℝ)) :=
    le_trans hkey (scale_rpow_neg_le_nu_sq hnu hnu1 hL)
  exact scale_condition_arith hC1 hC2 hC3 hP1 hP2 hP3
    (Real.rpow_nonneg (by linarith only [hT1]) _)
    (hgle _ (by rw [hen]; linarith only [hann]))
    (hgle _ (by rw [hpe]; linarith only [hann]))
    (hgle _ (by rw [hen]; linarith only [hann]))
    (hgle _ (by rw [hpn]; linarith only [hann]))
    (hgle _ (by rw [hen]; linarith only [hann]))
    (hgle _ (by rw [hpe]; linarith only [hann]))
    (hgle _ (by linarith only [hahR, hann]))
    (hgnn _) (hgnn _) (hgnn _) (hgnn _) (hgnn _) (hgnn _) (hgnn _) hfin

end

end SuperdiffusionCLT.Section3.Setup
