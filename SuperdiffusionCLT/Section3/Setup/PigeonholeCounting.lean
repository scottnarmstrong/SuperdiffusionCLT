/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Pigeonhole

/-!
# The counting hypothesis of the pigeonhole selection

The paper runs the pigeonhole
subargument underlying [AK, Lemma 3.4]: with `A_k = bfAhom_L(cu_k)` the
determinant ratios telescope, and if the conclusion failed at every scale of
the lattice `⌊L/4⌋ + 2hℕ` then

`(1+δ)^{⌊L/(8h)⌋−2} ≤ det A_{⌊L/4⌋}/det bfAhom_L ≤ (Cν⁻¹L)^{2d}`,

"which contradicts the second condition in `e.h.restrictions`". The
scalar form of this subargument is `exists_pigeonhole_scale`, which takes the counting hypothesis
in the shape `envelopeScalarProduct d nu L < (1 + delta) ^ N` for the number
`N` of available lattice steps.

## The two ingredients

* `pigeonholeStepCount` with its range lemmas: the number of lattice steps
  `N = pigeonholeStepCount L h = ⌊L/(8h)⌋`, together with the remainder bound
  `pigeonholeStepCount_lt_succ_mul` and the range hypothesis
  `pigeonholeStepCount_half_le` that `exists_pigeonhole_scale` needs.
* `envelopeScalarProduct_le`: the polynomial bound. The envelope scalars of
  of `Section2.Annealed` give
  `envelopeUpperScalar = nu + 2 C ν⁻¹ (1 ∨ L)` with `C = cutoffEnvelopeConst d`
  and `envelopeLowerScalar = 2 C ν⁻¹`, so for `1 ≤ L` and `nu ≤ 1` their
  product — the scalar whose `d`-th power is `det bfE_L`, i.e. the printed
  `det bfE_L ≤ (Cν⁻¹L)^{2d}` — is at most `6 (Cν⁻¹L)²`.

## The counting step is exponential, not linear

The print discharges the counting step with the *exponential* estimate
`log(1+δ) ≥ δ/2`: from the second restriction of `e.h.restrictions`
(`(C log(Cν⁻¹L)/δ) h ≤ L`) the step count `⌊L/(8h)⌋` is at least a
constant multiple of `log(Cν⁻¹L)/δ`, so `(1+δ)^N` grows at least like
`(Cν⁻¹L)^{C/16}` — which beats the polynomial `(Cν⁻¹L)^{2d}` as soon as `C` is
large (an explicit uniform choice is `64 ≤ C`). A *linear* comparison of the
shape `6 (Cν⁻¹L)² < 1 + Nδ` cannot hold at all: a polynomial in `L` is never
bounded by a constant multiple of `log(Cν⁻¹L)` for all `L`, and no hypothesis
of that shape is dischargeable under the window restrictions. This module
therefore lands no counting comparison; the exponential route is carried by the
sibling module `PigeonholeMargin.lean`, whose
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions` derives
`envelopeScalarProduct d nu L < (1 + delta) ^ pigeonholeStepCount L h` from
`e.h.restrictions` with the largeness condition `64 ≤ C`, and whose selection
theorem `exists_pigeonhole_scale_of_windowRestrictions` combines it with the
two ingredients above. No restriction of `Parameters.lean` is altered.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## The number of available lattice steps -/

/-- **The number of available lattice steps** of the pigeonhole selection: the
count `N = ⌊L/(8h)⌋` of steps of length `2h` in the printed window, i.e. the
scale from which the printed exponent `⌊L/(8h)⌋−2` is read
off. The two steps of slack are carried by the range hypothesis
`L/4 + 2hN ≤ L/2` of `exists_pigeonhole_scale`, which
`pigeonholeStepCount_half_le` supplies. -/
def pigeonholeStepCount (L h : ℕ) : ℕ := L / (8 * h)

theorem pigeonholeStepCount_eq (L h : ℕ) : pigeonholeStepCount L h = L / (8 * h) := rfl

/-- `8h · N ≤ L` for `N = ⌊L/(8h)⌋`. -/
theorem eight_mul_pigeonholeStepCount_le (L h : ℕ) :
    8 * h * pigeonholeStepCount L h ≤ L := by
  calc 8 * h * pigeonholeStepCount L h = pigeonholeStepCount L h * (8 * h) :=
      Nat.mul_comm _ _
    _ ≤ L := by
      rw [pigeonholeStepCount_eq]
      exact Nat.div_mul_le_self L (8 * h)

/-- `L < 8h · (N + 1)` for `N = ⌊L/(8h)⌋` and `h > 0`: the remainder of the
division by `8h` is bounded by `8h − 1`. -/
theorem pigeonholeStepCount_lt_succ_mul (L h : ℕ) (hh : 0 < h) :
    L < 8 * h * (pigeonholeStepCount L h + 1) := by
  have hmod : L % (8 * h) < 8 * h := Nat.mod_lt L (by positivity)
  have hdiv := Nat.div_add_mod L (8 * h)
  calc L = 8 * h * (L / (8 * h)) + L % (8 * h) := hdiv.symm
    _ < 8 * h * (L / (8 * h)) + 8 * h := Nat.add_lt_add_left hmod _
    _ = 8 * h * (L / (8 * h) + 1) := by ring

/-- **The range hypothesis of `exists_pigeonhole_scale`** for
`N = pigeonholeStepCount L h`: the `N` steps of length `2h` starting at
`⌊L/4⌋` stay inside `[⌊L/4⌋, ⌊L/2⌋]`. -/
theorem pigeonholeStepCount_half_le (L h : ℕ) :
    L / 4 + 2 * h * pigeonholeStepCount L h ≤ L / 2 := by
  have h1 : 4 * (2 * h * pigeonholeStepCount L h) ≤ L :=
    calc 4 * (2 * h * pigeonholeStepCount L h) = 8 * h * pigeonholeStepCount L h := by
          ring
      _ ≤ L := eight_mul_pigeonholeStepCount_le L h
  have h2 : 2 * h * pigeonholeStepCount L h ≤ L / 4 := by
    have h1' : 2 * h * pigeonholeStepCount L h * 4 ≤ L := by
      calc 2 * h * pigeonholeStepCount L h * 4 = 8 * h * pigeonholeStepCount L h := by
            ring
        _ ≤ L := eight_mul_pigeonholeStepCount_le L h
    exact (Nat.le_div_iff_mul_le (k := 4) (by norm_num)).2 h1'
  have h4 : L / 4 + L / 4 ≤ L / 2 := by omega
  exact le_trans (Nat.add_le_add (le_refl (L / 4)) h2) h4

/-! ## The polynomial bound on the envelope scalar product -/

/-- The scale `Cν⁻¹L` of the printed bound `det bfE_L ≤ (Cν⁻¹L)^{2d}`, with
`C = cutoffEnvelopeConst d` the constant of `e.Enaught.mixing`. -/
private theorem nu_le_envelopeScale {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) :
    nu ≤ cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := by
  have hC1 : (1 : ℝ) ≤ cutoffEnvelopeConst d := one_le_cutoffEnvelopeConst d
  have hC0 : 0 ≤ cutoffEnvelopeConst d := le_of_lt (cutoffEnvelopeConst_pos d)
  have hsq : nu * nu ≤ 1 := by
    have h1 : nu * nu ≤ 1 * nu := mul_le_mul_of_nonneg_right hnu1 hnu.le
    have h2 : 1 * nu ≤ 1 * 1 := mul_le_mul_of_nonneg_left hnu1 zero_le_one
    linarith only [h1, h2]
  have e1 : (1 : ℝ) ≤ cutoffEnvelopeConst d * (L : ℝ) :=
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ cutoffEnvelopeConst d * 1 := mul_le_mul_of_nonneg_right hC1 zero_le_one
      _ ≤ cutoffEnvelopeConst d * (L : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.one_le_cast.2 hL) hC0
  have h2 : nu * nu ≤ cutoffEnvelopeConst d * (L : ℝ) := by
    linarith only [hsq, e1]
  have h3 : nu ≤ cutoffEnvelopeConst d * (L : ℝ) / nu := (le_div_iff₀ hnu).2 h2
  calc nu ≤ cutoffEnvelopeConst d * (L : ℝ) / nu := h3
    _ = cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := by ring

/-- The upper-left scalar `nu + 2 C ν⁻¹ (1 ∨ L)` of `bfE_L` is at most
`nu + 2 C ν⁻¹ L`, which for `nu ≤ 1 ≤ L` is at most `3 Cν⁻¹L`. -/
private theorem envelopeUpperScalar_le_three {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) :
    envelopeUpperScalar d nu L ≤ 3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := by
  have hC0 : 0 ≤ cutoffEnvelopeConst d := le_of_lt (cutoffEnvelopeConst_pos d)
  have hmax : max 1 ((L : ℝ)) ≤ (L : ℝ) :=
    max_le (Nat.one_le_cast.2 hL) (le_refl _)
  have hterm : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 ((L : ℝ)) ≤
      2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) :=
    mul_le_mul_of_nonneg_left hmax (by
      have := cutoffEnvelopeConst_pos d
      positivity)
  have hnu := nu_le_envelopeScale (d := d) hnu hnu1 L hL
  unfold envelopeUpperScalar
  calc envelopeUpperScalar d nu L
      = nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 ((L : ℝ)) := rfl
    _ ≤ nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) := add_le_add_right hterm nu
    _ ≤ nu + 2 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := le_of_eq (by ring)
    _ ≤ 3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := by
        linarith only [hnu]

/-- The lower-right scalar `2 C ν⁻¹` of `bfE_L` is at most `2 Cν⁻¹L`. -/
private theorem envelopeLowerScalar_le_two {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (hL : 1 ≤ L) :
    envelopeLowerScalar d nu ≤ 2 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := by
  have hC0 : 0 ≤ cutoffEnvelopeConst d := le_of_lt (cutoffEnvelopeConst_pos d)
  have hnuinv : 0 ≤ nu⁻¹ := inv_nonneg.2 hnu.le
  have hscale : 0 ≤ cutoffEnvelopeConst d * nu⁻¹ := mul_nonneg hC0 hnuinv
  have hform : envelopeLowerScalar d nu = 2 * (cutoffEnvelopeConst d * nu⁻¹) := by
    unfold envelopeLowerScalar
    ring
  have hterm : 1 * (cutoffEnvelopeConst d * nu⁻¹) ≤
      (L : ℝ) * (cutoffEnvelopeConst d * nu⁻¹) :=
    mul_le_mul_of_nonneg_right (Nat.one_le_cast.2 hL) hscale
  have hterm' : 1 * (cutoffEnvelopeConst d * nu⁻¹) = cutoffEnvelopeConst d * nu⁻¹ := by ring
  calc envelopeLowerScalar d nu = 2 * (cutoffEnvelopeConst d * nu⁻¹) := hform
    _ ≤ 2 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) := by
        linarith only [hterm, hterm']

/-- **`det bfE_L ≤ (Cν⁻¹L)^{2d}`**, in the scalar form in which
`exists_pigeonhole_scale` consumes it: the product
`envelopeScalarProduct = envelopeUpperScalar · envelopeLowerScalar` of the two
diagonal scalars of `bfE_L` — whose `d`-th power is `det bfE_L`, since `bfE_L`
is block diagonal with scalar blocks — is at most `6 (Cν⁻¹L)²`.

The factor `6` (against the printed `(Cν⁻¹L)²` with its constant `C`) comes
from the two envelopes `envelopeUpperScalar ≤ 3 Cν⁻¹L` — where `nu ≤ Cν⁻¹L`
follows from `nu ≤ 1 ≤ cutoffEnvelopeConst d · L` — and
`envelopeLowerScalar ≤ 2 Cν⁻¹L`, and is absorbed by taking `C` large. -/
theorem envelopeScalarProduct_le {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) :
    envelopeScalarProduct d nu L ≤
      6 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) ^ 2 := by
  have hU3 := envelopeUpperScalar_le_three (d := d) hnu hnu1 L hL
  have hL2 := envelopeLowerScalar_le_two (d := d) hnu L hL
  have hU0 : 0 ≤ envelopeUpperScalar d nu L :=
    le_of_lt (envelopeUpperScalar_pos hnu d L)
  have hL0 : 0 ≤ envelopeLowerScalar d nu :=
    le_of_lt (envelopeLowerScalar_pos hnu d)
  have hC0 : 0 ≤ cutoffEnvelopeConst d := le_of_lt (cutoffEnvelopeConst_pos d)
  have hA0 : 0 ≤ cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ) :=
    mul_nonneg (mul_nonneg hC0 (inv_nonneg.2 hnu.le)) (Nat.cast_nonneg _)
  have s1 : envelopeScalarProduct d nu L ≤
      (3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ))) * envelopeLowerScalar d nu :=
    mul_le_mul_of_nonneg_right hU3 hL0
  have s2 : (3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ))) * envelopeLowerScalar d nu ≤
      (3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ))) *
        (2 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ))) :=
    mul_le_mul_of_nonneg_left hL2 (by linarith only [hA0])
  calc envelopeScalarProduct d nu L
      = envelopeUpperScalar d nu L * envelopeLowerScalar d nu := rfl
    _ ≤ (3 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ))) *
          (2 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ))) := le_trans s1 s2
    _ = 6 * (cutoffEnvelopeConst d * nu⁻¹ * (L : ℝ)) ^ 2 := by ring

end

end SuperdiffusionCLT.Section3.Setup