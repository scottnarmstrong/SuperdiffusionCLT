/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# The parameters of the proof of the suboptimal lower bound

The paper opens the proof of Proposition `p.sstar.lower.bound` by fixing four
numerical parameters and four auxiliary scales.

* The proof fixes the smallness parameter `δ = c₀ c⋆²`, with `c₀(d) > 0`
  sufficiently small.
* The display `e.h.restrictions` restricts the window `h` by
  `h ≥ 10⌈K log²(ν⁻¹L)⌉` and `(C log(Cν⁻¹L)/δ) h ≤ L`, where `K` is a large
  constant selected later. The sentence after the display records that the
  choice of `c₀` also secures the relative smallness `C δ^{1/2} ≤ ¼c⋆`, and
  adds: "No absolute smallness of `δ` independent of `c⋆` is used."
* It sets `a = ⌈K log(ν⁻¹L)⌉`, and the display `e.scale.selection` sets
  `L' = m + 2a`, `ℓ' = m − h`, `ℓ = ℓ' − a`, `n = ℓ − a` from the pigeonhole
  scale `m`.
* It then records the identities `ℓ − n = a`, `ℓ' − ℓ = a`,
  `ℓ' − n = 2a`, `L' − m = 2a`, `L' − ℓ = h + 3a` and `L' − ℓ' = m − n = h + 2a`.
* The display `e.scales.ordering` records the strict ordering
  `m − 2h < n < ℓ < ℓ' < m < L' < L`.

## The constant `K`

The constant `K` of the display `e.h.restrictions` and of
`a = ⌈K log(ν⁻¹L)⌉` is Section 3's own scale-separation constant,
"a large constant to be selected later", chosen "sufficiently large, depending
only on `d`" in the proof of the proposition. It is a different object from the
`K` bound by the root theorem in `SuperdiffusionCLT.Frozen.Section3`, which
is the J5 nondegeneracy constant of `ShellLawJ5` (the paper's `\nondegconst`);
the two appear side by side in the same display of the proof,
`C(1 + \nondegconst + K log(ν⁻¹L))`.

## Scales are natural numbers

The four auxiliary scales are elements of `ℕ`, and the paper obtains them from
`m` by subtraction. Truncated subtraction on `ℕ` is not faithful to a
subtraction that the paper performs inside its admissible range, so
`ScaleSelection` carries the four scales as fields together with the defining
relations written additively (`ℓ' + h = m`, `ℓ + a = ℓ'`, `n + a = ℓ`,
`L' = m + 2a`). `ScaleSelection.ofBase` builds the package from `L, m, h, a`
under the single arithmetic side condition `h + 2a ≤ m`, and the theorems of
the `Identities` section recover the six printed differences, in truncated
subtraction, from those relations.

The first entry `m − 2h < n` of `e.scales.ordering` is recorded in the
addition-only form `m < n + 2h`, which is what the printed inequality asserts
in `ℤ`; `ScalesOrdering.m_sub_two_mul_h_lt_n` converts it to the printed
truncated form under `2h ≤ m`, which the pigeonhole selection of `m` supplies.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

/-! ## The smallness parameter `δ = c₀ c⋆²` -/

/-- **The smallness parameter `δ = c₀ c⋆²`** of the proof. -/
def smallnessParameter (c0 cStar : ℝ) : ℝ := c0 * cStar ^ 2

theorem smallnessParameter_pos {c0 cStar : ℝ} (hc0 : 0 < c0) (hcStar : 0 < cStar) :
    0 < smallnessParameter c0 cStar := by
  have h : 0 < cStar ^ 2 := by positivity
  exact mul_pos hc0 h

theorem smallnessParameter_nonneg {c0 cStar : ℝ} (hc0 : 0 ≤ c0) :
    0 ≤ smallnessParameter c0 cStar := by
  have h : 0 ≤ cStar ^ 2 := sq_nonneg cStar
  exact mul_nonneg hc0 h

/-- The square root of `δ = c₀c⋆²` factors as `c₀^{1/2} c⋆`. -/
theorem sqrt_smallnessParameter {c0 cStar : ℝ} (hc0 : 0 ≤ c0) (hcStar : 0 ≤ cStar) :
    Real.sqrt (smallnessParameter c0 cStar) = Real.sqrt c0 * cStar := by
  rw [smallnessParameter, Real.sqrt_mul hc0, Real.sqrt_sq hcStar]

/-! ## The scale offset `a` and the window restrictions on `h` -/

/-- **The scale offset `a = ⌈K log(ν⁻¹L)⌉`** of the proof. -/
noncomputable def scaleOffset (K nu : ℝ) (L : ℕ) : ℕ := ⌈K * Real.log (nu⁻¹ * L)⌉₊

theorem le_scaleOffset (K nu : ℝ) (L : ℕ) :
    K * Real.log (nu⁻¹ * L) ≤ (scaleOffset K nu L : ℝ) :=
  Nat.le_ceil _

theorem scaleOffset_lt_add_one {K nu : ℝ} {L : ℕ}
    (h : 0 ≤ K * Real.log (nu⁻¹ * L)) :
    (scaleOffset K nu L : ℝ) < K * Real.log (nu⁻¹ * L) + 1 :=
  Nat.ceil_lt_add_one h

/-- The scale offset is positive as soon as `K log(ν⁻¹L)` is. -/
theorem scaleOffset_pos {K nu : ℝ} {L : ℕ} (h : 0 < K * Real.log (nu⁻¹ * L)) :
    0 < scaleOffset K nu L :=
  Nat.ceil_pos.2 h

/-- **`e.h.restrictions`**: the two conditions restricting the
window `h`, with the constants `C` and `K` of the paper. The positivity
`0 < delta` is part of the print's data (`δ = c₀c⋆²` with `c₀(d) > 0`) and is
carried as a field because the divided form of `window_le`, which is the
display's second line verbatim, reads `0 ≤ L` at `delta = 0` in Lean
(`x / 0 = 0`). -/
structure WindowRestrictions (C K nu delta : ℝ) (L h : ℕ) : Prop where
  /-- The positivity of the print's `δ = c₀c⋆²`. -/
  delta_pos : 0 < delta
  /-- `h ≥ 10⌈K log²(ν⁻¹L)⌉`. -/
  ceil_le : 10 * ⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ ≤ h
  /-- `(C log(Cν⁻¹L)/δ) h ≤ L`, the divided form of the display's second line,
  faithful for `delta > 0`. -/
  window_le : C * Real.log (C * (nu⁻¹ * L)) / delta * h ≤ L

/-- **The window dominates the offset**: `2a < h`. The first condition of
`e.h.restrictions` compares `10⌈K log²(ν⁻¹L)⌉` with `a = ⌈K log(ν⁻¹L)⌉`, and
`log(ν⁻¹L) ≥ 1` makes `K log(ν⁻¹L) ≤ K log²(ν⁻¹L)`, so `h ≥ 10a > 2a`. The
hypothesis `1 ≤ log(ν⁻¹L)` is the threshold condition `e.L.vs.nu` (through
`L ≥ m ≥ C c⋆⁻³(⋯)` with the constant there taken large), not an extra
assumption. This is the arithmetic input of `e.scales.ordering`. -/
theorem two_mul_scaleOffset_lt {C K nu delta : ℝ} {L h : ℕ}
    (hK : 0 < K) (hlog : 1 ≤ Real.log (nu⁻¹ * L))
    (hres : WindowRestrictions C K nu delta L h) :
    2 * scaleOffset K nu L < h := by
  have hsq : K * Real.log (nu⁻¹ * L) ≤ K * Real.log (nu⁻¹ * L) ^ 2 := by
    have hone : Real.log (nu⁻¹ * L) ≤ Real.log (nu⁻¹ * L) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hlog
        (le_trans zero_le_one hlog)
      calc Real.log (nu⁻¹ * L) = Real.log (nu⁻¹ * L) * 1 := (mul_one _).symm
        _ ≤ Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L) := by
              simpa only [mul_one] using this
        _ = Real.log (nu⁻¹ * L) ^ 2 := (sq _).symm
    exact mul_le_mul_of_nonneg_left hone hK.le
  have hceil : scaleOffset K nu L ≤ ⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ :=
    Nat.ceil_le_ceil hsq
  have hpos : 0 < scaleOffset K nu L :=
    scaleOffset_pos (mul_pos hK (lt_of_lt_of_le zero_lt_one hlog))
  have := hres.ceil_le
  omega

/-- **The window dominates the offset by a factor `100`**: `h ≥ 100a`, the
condition `h ≥ 100(ℓ − n) = 100a` of the proof of Proposition
`p.sstar.lower.bound` (used to absorb the contribution
`(L' − ℓ) shom_{L',*}^{-1}(cu_n)` into `h shom_{L',*}^{-1}(cu_n)`). It follows
from the first condition of `e.h.restrictions` by the argument of
`two_mul_scaleOffset_lt`: `a = ⌈K log(ν⁻¹L)⌉₊ < K log(ν⁻¹L) + 1`, while
`h ≥ 10⌈K log²(ν⁻¹L)⌉₊ ≥ 10 K log²(ν⁻¹L)`, and `11 ≤ log(ν⁻¹L)` with `1 ≤ K`
gives `10 K log(ν⁻¹L) + 10 ≤ K log²(ν⁻¹L)`.

The threshold is `11`, not `10`: `10 ≤ log(ν⁻¹L)` is not enough, because
`⌈K log(ν⁻¹L)⌉₊` rounds up — at `log(ν⁻¹L) = 10.0001` and `K = 1` one has
`a = 11` and `100a = 1100 > 10⌈K log²(ν⁻¹L)⌉₊ = 1010`. The paper can
secure `11 ≤ log(ν⁻¹L)` by increasing the constant in `e.L.vs.nu`. -/
theorem hundred_mul_scaleOffset_le {C K nu delta : ℝ} {L h : ℕ}
    (hK : (1 : ℝ) ≤ K) (hlog : 11 ≤ Real.log (nu⁻¹ * L))
    (hres : WindowRestrictions C K nu delta L h) :
    100 * scaleOffset K nu L ≤ h := by
  have hKnn : (0 : ℝ) ≤ K := zero_le_one.trans hK
  have hlog0 : (0 : ℝ) ≤ Real.log (nu⁻¹ * L) := by linarith only [hlog]
  have hKt : (11 : ℝ) ≤ K * Real.log (nu⁻¹ * L) := by
    calc (11 : ℝ) ≤ Real.log (nu⁻¹ * L) := hlog
      _ ≤ K * Real.log (nu⁻¹ * L) := by
          have h1 : (1 : ℝ) * Real.log (nu⁻¹ * L) ≤ K * Real.log (nu⁻¹ * L) :=
            mul_le_mul_of_nonneg_right hK hlog0
          rwa [one_mul] at h1
  have hsq : (10 : ℝ) * (K * Real.log (nu⁻¹ * L)) + 10 ≤
      K * Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L) := by
    have h11 : (11 : ℝ) * Real.log (nu⁻¹ * L) ≤
        Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L) :=
      mul_le_mul_of_nonneg_right hlog hlog0
    have h2 : (11 : ℝ) * (K * Real.log (nu⁻¹ * L)) ≤
        K * (Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L)) := by
      calc (11 : ℝ) * (K * Real.log (nu⁻¹ * L))
          = K * (11 * Real.log (nu⁻¹ * L)) := by ring
        _ ≤ K * (Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L)) :=
          mul_le_mul_of_nonneg_left h11 hKnn
    linarith only [h2, hKt]
  have h1 : (scaleOffset K nu L : ℝ) < K * Real.log (nu⁻¹ * L) + 1 :=
    scaleOffset_lt_add_one (by linarith only [hKt])
  have h2 : (K * Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L) : ℝ) ≤
      ((⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ : ℕ) : ℝ) := by
    have h3 : K * Real.log (nu⁻¹ * L) * Real.log (nu⁻¹ * L)
        = K * Real.log (nu⁻¹ * L) ^ 2 := by ring
    rw [h3]
    exact Nat.le_ceil _
  have h4 : (10 : ℝ) * ((⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ : ℕ) : ℝ) ≤ (h : ℝ) := by
    have h5 : ((10 * ⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ : ℕ) : ℝ)
        = (10 : ℝ) * ((⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ : ℕ) : ℝ) := by
      push_cast
      ring
    have h6 : ((10 * ⌈K * Real.log (nu⁻¹ * L) ^ 2⌉₊ : ℕ) : ℝ) ≤ (h : ℝ) :=
      Nat.cast_le.2 hres.ceil_le
    linarith only [h5, h6]
  have hmain : ((100 * scaleOffset K nu L : ℕ) : ℝ) ≤ (h : ℝ) := by
    have h5 : ((100 * scaleOffset K nu L : ℕ) : ℝ)
        = (100 : ℝ) * ((scaleOffset K nu L : ℕ) : ℝ) := by
      push_cast
      ring
    linarith only [h1, h2, h4, hsq, h5]
  exact Nat.cast_le.mp hmain

/-! ## The scale selection `e.scale.selection` -/

/-- **`e.scale.selection`**: the package of the cutoff scale
`L`, the pigeonhole scale `m`, the window `h`, the offset `a` and the four
auxiliary scales `n, ℓ, ℓ', L'`, carrying the defining relations of the display
in addition-only form. -/
structure ScaleSelection where
  /-- The cutoff scale `L` of Proposition `p.sstar.lower.bound`. -/
  L : ℕ
  /-- The pigeonhole scale `m` of `e.pigeon.matrix`. -/
  m : ℕ
  /-- The window `h` of `e.h.restrictions`. -/
  h : ℕ
  /-- The offset `a = ⌈K log(ν⁻¹L)⌉`. -/
  a : ℕ
  /-- The smallest auxiliary scale `n`. -/
  n : ℕ
  /-- The auxiliary scale `ℓ`. -/
  ell : ℕ
  /-- The auxiliary scale `ℓ'`. -/
  ellPrime : ℕ
  /-- The enlarged cutoff scale `L'`. -/
  LPrime : ℕ
  /-- `ℓ' = m − h`. -/
  ellPrime_add_h : ellPrime + h = m
  /-- `ℓ = ℓ' − a`. -/
  ell_add_a : ell + a = ellPrime
  /-- `n = ℓ − a`. -/
  n_add_a : n + a = ell
  /-- `L' = m + 2a`. -/
  LPrime_eq : LPrime = m + 2 * a

namespace ScaleSelection

/-- The scale selection built from the cutoff `L`, the pigeonhole scale `m`,
the window `h` and the offset `a`, under the condition `h + 2a ≤ m` that makes
the three subtractions of `e.scale.selection` faithful. -/
def ofBase (L m h a : ℕ) (hm : h + 2 * a ≤ m) : ScaleSelection where
  L := L
  m := m
  h := h
  a := a
  n := m - h - 2 * a
  ell := m - h - a
  ellPrime := m - h
  LPrime := m + 2 * a
  ellPrime_add_h := by omega
  ell_add_a := by omega
  n_add_a := by omega
  LPrime_eq := rfl

@[simp] theorem ofBase_L (L m h a : ℕ) (hm : h + 2 * a ≤ m) :
    (ofBase L m h a hm).L = L := rfl

@[simp] theorem ofBase_m (L m h a : ℕ) (hm : h + 2 * a ≤ m) :
    (ofBase L m h a hm).m = m := rfl

@[simp] theorem ofBase_h (L m h a : ℕ) (hm : h + 2 * a ≤ m) :
    (ofBase L m h a hm).h = h := rfl

@[simp] theorem ofBase_a (L m h a : ℕ) (hm : h + 2 * a ≤ m) :
    (ofBase L m h a hm).a = a := rfl

/-- The side condition `h + 2a ≤ m` of `ofBase` from the pigeonhole selection
of `m`: `exists_pigeonhole_scale` produces `2 * h ≤ m`, and `2 * a < h`
(`two_mul_scaleOffset_lt`, the comparison of `e.h.restrictions` with
`a = ⌈K log(ν⁻¹L)⌉`) gives `h + 2 * a < 2 * h`. This is the first bridge
between the pigeonhole scale of `e.pigeon.matrix` and the scale selection
`e.scale.selection`. -/
theorem ofBase_hm_of_two_mul_h_le {h a m : ℕ} (hm : 2 * h ≤ m) (hah : 2 * a < h) :
    h + 2 * a ≤ m := by omega

/-! ### The recorded identities of the proof -/

variable (S : ScaleSelection)

/-- `ℓ − n = a`. -/
theorem ell_sub_n : S.ell - S.n = S.a := by
  have := S.n_add_a; omega

/-- `ℓ' − ℓ = a`. -/
theorem ellPrime_sub_ell : S.ellPrime - S.ell = S.a := by
  have := S.ell_add_a; omega

/-- `ℓ' − n = 2a`. -/
theorem ellPrime_sub_n : S.ellPrime - S.n = 2 * S.a := by
  have := S.ell_add_a; have := S.n_add_a; omega

/-- `L' − m = 2a`. -/
theorem LPrime_sub_m : S.LPrime - S.m = 2 * S.a := by
  have := S.LPrime_eq; omega

/-- `L' − ℓ = h + 3a`. -/
theorem LPrime_sub_ell : S.LPrime - S.ell = S.h + 3 * S.a := by
  have := S.LPrime_eq; have := S.ell_add_a; have := S.ellPrime_add_h; omega

/-- `L' − ℓ' = h + 2a`. -/
theorem LPrime_sub_ellPrime : S.LPrime - S.ellPrime = S.h + 2 * S.a := by
  have := S.LPrime_eq; have := S.ellPrime_add_h; omega

/-- `m − n = h + 2a`, the second half of the printed identity
`L' − ℓ' = m − n = h + 2a`. -/
theorem m_sub_n : S.m - S.n = S.h + 2 * S.a := by
  have := S.ellPrime_add_h; have := S.ell_add_a; have := S.n_add_a; omega

/-- The identity `L' − ℓ' = m − n` in its two-sided form. -/
theorem LPrime_sub_ellPrime_eq_m_sub_n : S.LPrime - S.ellPrime = S.m - S.n := by
  rw [LPrime_sub_ellPrime, m_sub_n]

/-- `m = n + h + 2a`, the addition-only form of `m − n = h + 2a`. -/
theorem m_eq_n_add : S.m = S.n + (S.h + 2 * S.a) := by
  have := S.ellPrime_add_h; have := S.ell_add_a; have := S.n_add_a; omega

end ScaleSelection

/-! ## The ordering `e.scales.ordering` -/

/-- **`e.scales.ordering`**: the strict ordering
`m − 2h < n < ℓ < ℓ' < m < L' < L` of the selected scales. The first entry is
recorded as `m < n + 2h`, the addition-only form of the printed inequality;
`ScalesOrdering.m_sub_two_mul_h_lt_n` recovers the printed form. -/
structure ScalesOrdering (S : ScaleSelection) : Prop where
  /-- `m − 2h < n`. -/
  m_lt : S.m < S.n + 2 * S.h
  /-- `n < ℓ`. -/
  n_lt_ell : S.n < S.ell
  /-- `ℓ < ℓ'`. -/
  ell_lt_ellPrime : S.ell < S.ellPrime
  /-- `ℓ' < m`. -/
  ellPrime_lt_m : S.ellPrime < S.m
  /-- `m < L'`. -/
  m_lt_LPrime : S.m < S.LPrime
  /-- `L' < L`. -/
  LPrime_lt_L : S.LPrime < S.L

namespace ScalesOrdering

variable {S : ScaleSelection}

/-- The printed form `m − 2h < n` of the first entry, under the condition
`2h ≤ m` that the pigeonhole selection of `m` supplies (`m` lies in
`⌊L/4⌋ + 2hℕ` above `⌊L/4⌋ + 2h`). -/
theorem m_sub_two_mul_h_lt_n (hS : ScalesOrdering S) (hm : 2 * S.h ≤ S.m) :
    S.m - 2 * S.h < S.n := by
  have := hS.m_lt; omega

/-- Every one of `n`, `ℓ` and `ℓ'` lies in the range `[m − 2h, m]` over which
`p.sstar.lower.bound#pigeon-range-comparability` compares the
annealed diffusivities, in the addition-only form of the lower endpoint. The
conclusion is the *strict* form `m − 2h < n ≤ m` (and likewise for `ℓ` and
`ℓ'`), which is stronger than the closed `n, ℓ, ℓ' ∈ [m − 2h, m]` that the
paper prints. -/
theorem mem_pigeon_range (hS : ScalesOrdering S) :
    (S.m < S.n + 2 * S.h ∧ S.n ≤ S.m) ∧
      (S.m < S.ell + 2 * S.h ∧ S.ell ≤ S.m) ∧
      (S.m < S.ellPrime + 2 * S.h ∧ S.ellPrime ≤ S.m) := by
  have h1 := hS.m_lt
  have h2 := hS.n_lt_ell
  have h3 := hS.ell_lt_ellPrime
  have h4 := hS.ellPrime_lt_m
  refine ⟨⟨h1, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

end ScalesOrdering

/-- The hypothesis `m + 2a < L` of `scalesOrdering_of_lt` from the range of the
pigeonhole scale: `exists_pigeonhole_scale` produces `m ≤ L / 2` with
`2 * h ≤ m`, and `2 * a < h` (`two_mul_scaleOffset_lt`) gives `m + 2a < 2m ≤ L`.
This is the second bridge between the pigeonhole scale of `e.pigeon.matrix`
and `e.scales.ordering` ("the lower bound on `L` in `e.L.vs.nu`
with its constant taken large relative to `K`"). -/
theorem scalesOrdering_hL_of_pigeonhole_scale {m h a L : ℕ}
    (hm : 2 * h ≤ m) (hah : 2 * a < h) (hmL : m ≤ L / 2) :
    m + 2 * a < L := by omega

/-- **The derivation of `e.scales.ordering`** announced in the paper: the whole
ordering follows from `0 < a`, `2a < h` (the comparison of `e.h.restrictions`
with `a = ⌈K log(ν⁻¹L)⌉`, `two_mul_scaleOffset_lt`) and `m + 2a < L` (the lower
bound on `L` in `e.L.vs.nu` with its constant taken large relative to `K`).
The bridge lemmas `ScaleSelection.ofBase_hm_of_two_mul_h_le` and
`scalesOrdering_hL_of_pigeonhole_scale` supply the side condition of `ofBase`
and this hypothesis `m + 2a < L` from the pigeonhole scale of
`e.pigeon.matrix`. -/
theorem scalesOrdering_of_lt {S : ScaleSelection} (ha : 0 < S.a)
    (hah : 2 * S.a < S.h) (hL : S.m + 2 * S.a < S.L) : ScalesOrdering S where
  m_lt := by have := S.m_eq_n_add; omega
  n_lt_ell := by have := S.n_add_a; omega
  ell_lt_ellPrime := by have := S.ell_add_a; omega
  ellPrime_lt_m := by have := S.ellPrime_add_h; omega
  m_lt_LPrime := by have := S.LPrime_eq; omega
  LPrime_lt_L := by have := S.LPrime_eq; omega

end SuperdiffusionCLT.Section3.Setup
