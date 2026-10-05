/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityRateFree
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeLevelDecay

/-!
# The three-regime split: the ellipticity conclusion from the
# five shell laws alone

This module concerns lemma `l.bfAm.ellip`.  The rate-flexible reduction
`bfAmEllipticity_of_scaleTailAnyRate` (in `BfAmEllipticityRateFree`) produces the conclusion
from the printed per-scale tail at **any** positive rate `c₀`, so the only thing standing
between the five shell laws and the anchor is the per-scale exponent
`c₀ · 3^{γk + (d/2) max ((n-m)-k) 0}` — the printed level improvement
`3^{(d/2) max ((n-m)-k) 0}`.

Two per-scale tails are available.

* The `Γ₁` tail `measureReal_envelopeRatio_gt_two_mul_rpow_le`
  (in `BfAmEllipticityScaleTail`): exponent `2 · 3^{γk}`, no level
  factor.
* The level decay `measureReal_envelopeRatio_gt_le_levelDecay`
  (in `EnvelopeLevelDecay`): exponent
  `(s - 1) / (C_d · levelDecayFactor d m l)` with
  `levelDecayFactor d m l = 3^{-(d/2) max (l - m) 0}` and
  `C_d = envelopeLevelDecayConst d`, at the threshold
  `s ≥ 1 + C_d · levelDecayFactor d m l`.

The second has exactly the printed shape, but at the printed threshold
`s = 2 · 3^{γk} ≥ 2` its threshold hypothesis reads
`1 + C_d · 3^{-(d/2) max (l-m) 0} ≤ 2`, which needs
`3^{(d/2) max (l-m) 0} ≥ C_d` and therefore fails at the boundary `l = m + 1`
where the level factor is `1/3` and `C_d ≥ 18`. The observation this file is
built on is that `levelDecayFactor` **shrinks** in `l - m`, so that threshold
condition becomes free once the level difference reaches

> `L₀(d) := ⌈(2/d) log₃ (envelopeLevelDecayConst d)⌉`,

a constant depending on the dimension alone. Splitting the level difference
`j := max ((n-m)-k) 0` in three therefore closes the anchor.

1. `j = 0` (the cube's scale is at most `m`): the level factor is `1` and the
   honest rate-`2` tail is exactly the required shape.
2. `0 < j ≤ L₀(d)`: finitely many levels, and the level loss `3^{(d/2) j}` is at
   most the `d`-only constant `B(d) := 3^{(d/2) L₀(d)}`. The honest tail still
   gives the required exponent as soon as the rate obeys `c₀ · B(d) ≤ 2`.
3. `j > L₀(d)`: the level factor is at most `C_d⁻¹`, so the level-decay lemma
   applies at the printed threshold and its exponent
   `(2·3^{γk} - 1) · 3^{(d/2)j} / C_d` dominates `c₀ · 3^{γk} · 3^{(d/2)j}` as
   soon as `c₀ ≤ C_d⁻¹`.

The three requirements on `c₀` are simultaneously met at the explicit positive
rate

> `levelRegimeRate d := min (C_d⁻¹) (2 / B(d))`.

Because the reduction accepts any positive rate, this closes
the ellipticity conclusion `bfAmEllipticity_of_regimeSplit` from `d`, `2 ≤ d` and the
five shell laws — no per-scale display is left as a hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

/-! ## The split point and the split factor

`L₀(d) = ⌈(2/d) log₃ (envelopeLevelDecayConst d)⌉` is a natural number depending
on `d` alone: it is the first level difference at which the level decay
`3^{-(d/2)j}` has fallen to `(envelopeLevelDecayConst d)⁻¹`, i.e. at which the
level-decay lemma's threshold `1 + C_d 3^{-(d/2)j}` reaches the printed
threshold `2`. -/

/-- The level split `L₀(d) = ⌈(2/d) log₃ (envelopeLevelDecayConst d)⌉`. -/
def levelSplitPoint (d : ℕ) : ℕ :=
  Nat.ceil ((2 / (d : ℝ)) * Real.logb 3 (envelopeLevelDecayConst d))

/-- The defining property of `L₀(d)`: it is at least `(2/d) log₃ C_d`. -/
theorem levelSplitPoint_spec (d : ℕ) :
    (2 / (d : ℝ)) * Real.logb 3 (envelopeLevelDecayConst d) ≤ (levelSplitPoint d : ℝ) :=
  Nat.le_ceil _

/-- The split factor `B(d) = 3^{(d/2) L₀(d)}`, the level-decay denominator at
the split point. It is a constant depending on `d` alone. -/
def levelSplitFactor (d : ℕ) : ℝ :=
  (3 : ℝ) ^ (((d : ℝ) / 2) * (levelSplitPoint d : ℝ))

theorem levelSplitFactor_pos (d : ℕ) : 0 < levelSplitFactor d :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- **The threshold crossing.** For `d ≥ 1` the level-decay constant is at most
`B(d) = 3^{(d/2) L₀(d)}`: `L₀(d) ≥ (2/d) log₃ C_d` puts `3^{(d/2)L₀(d)}` above
`3^{log₃ C_d} = C_d`. -/
theorem envelopeLevelDecayConst_le_levelSplitFactor (d : ℕ) (hd : 1 ≤ d) :
    envelopeLevelDecayConst d ≤ levelSplitFactor d := by
  have hCpos : 0 < envelopeLevelDecayConst d := envelopeLevelDecayConst_pos d
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hspec := levelSplitPoint_spec d
  have hcoef : ((d : ℝ) / 2) * (2 / (d : ℝ)) = 1 := by
    rw [div_mul_div_comm, show (d : ℝ) * 2 = 2 * (d : ℝ) by ring, div_self (by positivity)]
  have hmul := mul_le_mul_of_nonneg_left hspec (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
  rw [← mul_assoc, hcoef, one_mul] at hmul
  calc envelopeLevelDecayConst d
      = (3 : ℝ) ^ Real.logb 3 (envelopeLevelDecayConst d) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hCpos).symm
    _ ≤ levelSplitFactor d :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hmul

/-! ## The explicit rate -/

/-- The per-scale rate of the three-regime split: the smaller of the rate
`C_d⁻¹` delivered by the level decay and the rate `2 / B(d)` at which the honest
tail absorbs the finite level loss of regime 2. -/
def levelRegimeRate (d : ℕ) : ℝ :=
  min ((envelopeLevelDecayConst d)⁻¹) (2 / levelSplitFactor d)

theorem levelRegimeRate_pos (d : ℕ) : 0 < levelRegimeRate d := by
  rw [levelRegimeRate]
  exact lt_min (inv_pos.2 (envelopeLevelDecayConst_pos d))
    (div_pos (by norm_num) (levelSplitFactor_pos d))

theorem levelRegimeRate_le_levelDecay (d : ℕ) :
    levelRegimeRate d ≤ (envelopeLevelDecayConst d)⁻¹ :=
  min_le_left _ _

theorem levelRegimeRate_le_split (d : ℕ) :
    levelRegimeRate d ≤ 2 / levelSplitFactor d :=
  min_le_right _ _

/-! ## Regimes 1 and 2: the honest tail absorbs the finite level loss

For `j ≤ L₀(d)` the level factor `3^{(d/2)j}` is at most `B(d)`, so the rate
bound `c₀ ≤ 2 / B(d)` makes the required per-scale exponent at most the honest
exponent `2 · 3^{γk}`. Regime 1 is the case `j = 0`, where the level factor is
`1` and the loss is trivial; regime 2 is `0 < j ≤ L₀(d)`, where the loss is at
most the `d`-only constant `B(d)`. -/

/-- **Regimes 1 and 2.** The required per-scale exponent at the rate
`levelRegimeRate d` is at most the honest exponent `2 · 3^{γk}` whenever the
level difference `j` is at most the split point `L₀(d)`. -/
theorem levelRegimeRate_mul_exp_le_of_le_split (d : ℕ) {b j : ℝ} (hb0 : 0 ≤ b)
    (hj : j ≤ (levelSplitPoint d : ℝ)) :
    levelRegimeRate d * (b * (3 : ℝ) ^ (((d : ℝ) / 2) * j)) ≤ 2 * b := by
  have hZle : (3 : ℝ) ^ (((d : ℝ) / 2) * j) ≤ levelSplitFactor d :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hj (by positivity))
  have hBpos : 0 < levelSplitFactor d := levelSplitFactor_pos d
  have hZpos : 0 < (3 : ℝ) ^ (((d : ℝ) / 2) * j) := Real.rpow_pos_of_pos (by norm_num) _
  have hstep : levelRegimeRate d * (3 : ℝ) ^ (((d : ℝ) / 2) * j) ≤ 2 := by
    calc levelRegimeRate d * (3 : ℝ) ^ (((d : ℝ) / 2) * j)
        ≤ (2 / levelSplitFactor d) * (3 : ℝ) ^ (((d : ℝ) / 2) * j) :=
          mul_le_mul_of_nonneg_right (levelRegimeRate_le_split d) hZpos.le
      _ ≤ (2 / levelSplitFactor d) * levelSplitFactor d :=
          mul_le_mul_of_nonneg_left hZle (by positivity)
      _ = 2 := div_mul_cancel₀ 2 hBpos.ne'
  calc levelRegimeRate d * (b * (3 : ℝ) ^ (((d : ℝ) / 2) * j))
      = (levelRegimeRate d * (3 : ℝ) ^ (((d : ℝ) / 2) * j)) * b := by ring
    _ ≤ 2 * b := mul_le_mul_of_nonneg_right hstep hb0

/-! ## Regime 3: the level decay applies at the printed threshold

For `j > L₀(d)` the exponent `(d/2) j` exceeds `log₃ C_d`, so
`Z := 3^{(d/2)j} ≥ C_d`; the level factor `Z⁻¹` is at most `C_d⁻¹` and the
level-decay lemma's threshold holds at the printed `s = 2 · 3^{γk}`. Its
exponent `(2·3^{γk} - 1) Z / C_d` then dominates `c₀ · 3^{γk} · Z` for every
`c₀ ≤ C_d⁻¹`. -/

/-- **Regime 3.** With `Z = 3^{(d/2)j} ≥ C_d`, the level-decay exponent of
`measureReal_envelopeRatio_gt_le_levelDecay` dominates the required exponent at
the rate `levelRegimeRate d`. -/
theorem levelRegimeRate_mul_exp_le_of_gt_split (d : ℕ) {b Z : ℝ} (hb1 : 1 ≤ b)
    (hCZ : envelopeLevelDecayConst d ≤ Z) :
    levelRegimeRate d * (b * Z) ≤
      (2 * 1 * b - 1) / (envelopeLevelDecayConst d * Z⁻¹) := by
  have hCpos : 0 < envelopeLevelDecayConst d := envelopeLevelDecayConst_pos d
  have hZpos : 0 < Z := lt_of_lt_of_le hCpos hCZ
  have h1 : levelRegimeRate d * (b * Z) ≤ (envelopeLevelDecayConst d)⁻¹ * (b * Z) :=
    mul_le_mul_of_nonneg_right (levelRegimeRate_le_levelDecay d) (by positivity)
  have h2 : (envelopeLevelDecayConst d)⁻¹ * (b * Z) = b * Z / envelopeLevelDecayConst d := by
    rw [div_eq_mul_inv]
    ring
  have h3 : (2 * 1 * b - 1) / (envelopeLevelDecayConst d * Z⁻¹) =
      (2 * 1 * b - 1) * Z / envelopeLevelDecayConst d := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have h5 : b ≤ 2 * 1 * b - 1 := by linarith only [hb1]
  have h6 : b * Z ≤ (2 * 1 * b - 1) * Z := mul_le_mul_of_nonneg_right h5 hZpos.le
  calc levelRegimeRate d * (b * Z) ≤ (envelopeLevelDecayConst d)⁻¹ * (b * Z) := h1
    _ = b * Z / envelopeLevelDecayConst d := h2
    _ ≤ (2 * 1 * b - 1) * Z / envelopeLevelDecayConst d :=
        div_le_div_of_nonneg_right h6 hCpos.le
    _ = (2 * 1 * b - 1) / (envelopeLevelDecayConst d * Z⁻¹) := h3.symm

/-! ## The level factor at the cube's own scale -/

/-- The level factor of a cube of scale `l = n - k` is the reciprocal of
`3^{(d/2) max ((n-m)-k) 0}`. -/
theorem levelDecayFactor_eq_inv_rpow (d m n k : ℕ) (hkn : k ≤ n) :
    levelDecayFactor d m (n - k) =
      ((3 : ℝ) ^ (((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0))⁻¹ := by
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
  have harg : ((n : ℝ) - (k : ℝ)) - (m : ℝ) = ((n : ℝ) - (m : ℝ)) - (k : ℝ) := by ring
  rw [levelDecayFactor, hcast, harg, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]

/-! ## The printed per-scale tail by regime -/

/-- **The printed per-scale tail at the split rate.** For every cube `Q` of
scale `n - k`, every `γ ∈ (0,1)` and every `k`, the printed event at `t = 1` has probability
at most `exp (-(levelRegimeRate d · 3^{γk + (d/2) max ((n-m)-k) 0}))`, with the
printed level improvement in the exponent.

The level difference `j = max ((n-m)-k) 0` is split at `L₀(d)`. For `j ≤ L₀(d)`
(which includes every `k > n`, where `j = 0`) the honest `Γ₁` tail
`measureReal_envelopeRatio_gt_two_mul_rpow_le` supplies the exponent, the level
loss `3^{(d/2)j} ≤ B(d)` being absorbed by the rate bound
`levelRegimeRate d ≤ 2 / B(d)`. For `j > L₀(d)` the level decay
`measureReal_envelopeRatio_gt_le_levelDecay` applies at the printed threshold,
since `3^{(d/2)j} ≥ B(d) ≥ C_d` forces the level factor below `C_d⁻¹`. -/
theorem scaleTail_of_regimeSplit (d : ℕ) (hd : 1 ≤ d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {m n : ℕ} {gamma : ℝ} (hg0 : 0 < gamma)
    (k : ℕ) (Q : TriadicCube d) (hQ : Q.scale = (n : ℤ) - (k : ℤ)) :
    P.toMeasure.real {omega : ShellSeq d |
        2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) < envelopeRatio m Q omega} ≤
      Real.exp (-(levelRegimeRate d * (3 : ℝ) ^ (gamma * (k : ℝ) +
        ((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0))) := by
  have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ (gamma * (k : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hg0.le (Nat.cast_nonneg k))
  have hbpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * (k : ℝ)) := lt_of_lt_of_le zero_lt_one hb1
  rcases le_or_gt (max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0) ((levelSplitPoint d : ℕ) : ℝ) with
    hsmall | hbig
  · refine (measureReal_envelopeRatio_gt_two_mul_rpow_le (d := d) (P := P)
      hPrefix hJ2 hJ3 hJ4 m Q hg0 k).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact levelRegimeRate_mul_exp_le_of_le_split d hbpos.le hsmall
  · have hpos : (0 : ℝ) < max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0 :=
      lt_of_le_of_lt (Nat.cast_nonneg (levelSplitPoint d)) hbig
    have hKpos : (0 : ℝ) < ((n : ℝ) - (m : ℝ)) - (k : ℝ) := by
      by_contra h
      rw [max_eq_right (le_of_not_gt h)] at hpos
      exact absurd hpos (lt_irrefl (0 : ℝ))
    have hKgt : (levelSplitPoint d : ℝ) < ((n : ℝ) - (m : ℝ)) - (k : ℝ) :=
      hbig.trans_le (le_of_eq (max_eq_left hKpos.le))
    have hkn : k ≤ n := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hL0 : (0 : ℝ) ≤ (levelSplitPoint d : ℝ) := Nat.cast_nonneg _
      have hlt : (k : ℝ) < (n : ℝ) := by linarith only [hKgt, hL0, hm0]
      exact_mod_cast le_of_lt hlt
    have hCpos : 0 < envelopeLevelDecayConst d := envelopeLevelDecayConst_pos d
    have hCZ : envelopeLevelDecayConst d ≤
        (3 : ℝ) ^ (((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0) :=
      (envelopeLevelDecayConst_le_levelSplitFactor d hd).trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_left hbig.le (by positivity)))
    have hfac : levelDecayFactor d m (n - k) =
        ((3 : ℝ) ^ (((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0))⁻¹ :=
      levelDecayFactor_eq_inv_rpow d m n k hkn
    have hfac_le : levelDecayFactor d m (n - k) ≤ (envelopeLevelDecayConst d)⁻¹ := by
      rw [hfac]
      simpa only [one_div] using one_div_le_one_div_of_le hCpos hCZ
    have hCfac : envelopeLevelDecayConst d * levelDecayFactor d m (n - k) ≤ 1 := by
      calc envelopeLevelDecayConst d * levelDecayFactor d m (n - k)
          ≤ envelopeLevelDecayConst d * (envelopeLevelDecayConst d)⁻¹ :=
            mul_le_mul_of_nonneg_left hfac_le hCpos.le
        _ = 1 := mul_inv_cancel₀ hCpos.ne'
    have hthr : 1 + envelopeLevelDecayConst d * levelDecayFactor d m (n - k) ≤
        2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) := by
      have h2 : (2 : ℝ) ≤ 2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) := by linarith only [hb1]
      linarith only [hCfac, h2]
    have hQ' : Q.scale = ((n - k : ℕ) : ℤ) := by rw [hQ, ← Nat.cast_sub hkn]
    refine (measureReal_envelopeRatio_gt_le_levelDecay (d := d) (P := P)
      hPrefix hJ1 hJ2 hJ3 hJ4 (m := m) (l := n - k) (Q := Q) hQ' hthr).trans
      (Real.exp_le_exp.2 (neg_le_neg ?_))
    rw [hfac, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact levelRegimeRate_mul_exp_le_of_gt_split d hb1 hCZ

/-- **The printed per-scale tail at the split rate, as the reduction's
hypothesis.** The `∀`-closure of `scaleTail_of_regimeSplit`, matching verbatim
the `hScaleTail` slot of `bfAmEllipticity_of_scaleTailAnyRate`
at the rate `levelRegimeRate d`.
Neither `m ≤ n` nor `γ < 1` is used: the split covers every `k`, including
`k > n`. -/
theorem scaleTailHypothesis_of_regimeSplit (d : ℕ) (hd : 1 ≤ d) :
    ∀ (P : ProbabilityMeasure (ShellSeq d)),
      ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
      ShellLawJ4 d P →
      ∀ (m n : ℕ), m ≤ n → ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
        ∀ (k : ℕ) (Q : TriadicCube d), Q.scale = (n : ℤ) - (k : ℤ) →
          P.toMeasure.real {omega : ShellSeq d |
              2 * 1 * (3 : ℝ) ^ (gamma * (k : ℝ)) < envelopeRatio m Q omega} ≤
            Real.exp (-(levelRegimeRate d * (3 : ℝ) ^ (gamma * (k : ℝ) +
              ((d : ℝ) / 2) * max (((n : ℝ) - (m : ℝ)) - (k : ℝ)) 0))) :=
  fun P hPrefix hJ1 hJ2 hJ3 hJ4 m n _hmn gamma hg0 _hg1 k Q hQ =>
    scaleTail_of_regimeSplit (P := P) (m := m) (n := n) (gamma := gamma)
      d hd hPrefix hJ1 hJ2 hJ3 hJ4 hg0 k Q hQ

/-! ## The conclusion -/

/-- **The ellipticity conclusion closes.** The printed conclusion of lemma `l.bfAm.ellip`
holds for every `d ≥ 2` and every `C` produced by
`bfAmEllipticity_of_scaleTailAnyRate` from the printed per-scale tail at the
explicit rate `levelRegimeRate d > 0`, which
`scaleTailHypothesis_of_regimeSplit` discharges outright from the five shell
laws. Nothing is left as a hypothesis beyond the dimension. -/
theorem bfAmEllipticity_of_regimeSplit (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
          ∀ m : ℕ,
            (∀ U : Homogenization.Book.Ch02.Domain d,
                Measurable
                  (fun omega : ShellSeq d =>
                      Carriers.blockMatrixOperatorNorm
                        (envelopeRescale d nu m
                          (Homogenization.coarseBlockMatrix
                            (U : Set (Homogenization.Vec d))
                            (coefficientCutoff nu omega m).toCoeffField))) ∧
                IndependentSums.IsBigOWith P.toMeasure
                  (IndependentSums.gammaSigma 1)
                  (fun omega : ShellSeq d =>
                    Carriers.blockMatrixOperatorNorm
                      (envelopeRescale d nu m
                        (Homogenization.coarseBlockMatrix
                          (U : Set (Homogenization.Vec d))
                          (coefficientCutoff nu omega m).toCoeffField)))
                  1) ∧
              (∀ n : ℕ,
                  BlockMatLoewnerLE
                      (envelopeRescale d nu m (Carriers.annealedBlockMatInfinite nu m P))
                      (envelopeRescale d nu m
                        (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ))))) ∧
                    BlockMatLoewnerLE
                      (envelopeRescale d nu m
                        (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ)))))
                      (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (∀ gamma : ℝ, 0 < gamma → gamma < 1 →
                  ∃ S : ShellSeq d → ℝ,
                    Measurable S ∧
                    IndependentSums.IsBigO P.toMeasure
                        (IndependentSums.gammaSigma gamma) S
                        (C * Real.exp (C * |Real.log gamma| / gamma) * (3 : ℝ) ^ m) ∧
                      ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
                        ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                        ∀ Q : Homogenization.TriadicCube d, Q.scale ≤ (n : ℤ) →
                          cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
                            BlockMatLoewnerLE
                              (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
                                envelopeRescale d nu m
                                  (Homogenization.coarseBlockMatrix
                                    (cubeSet Q)
                                    (coefficientCutoff nu omega m).toCoeffField))
                              ((2 : ℝ) • Homogenization.Book.Ch02.blockIdentity d)) :=
  bfAmEllipticity_of_scaleTailAnyRate d hd (levelRegimeRate d) (levelRegimeRate_pos d)
    (scaleTailHypothesis_of_regimeSplit d (le_trans (by norm_num) hd))

end

end SuperdiffusionCLT.Section2
