/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Section2.Norms.CubeCarrierIdents
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLpLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMomentLargeCube

/-!
# The `L^p` clause of the estimates on the finite shell increment

This module proves clause (b) of the paper's estimates on the increment
`k_m - k_n`, display `e.kmn.Lp`: for `n < m ≤ l` and `p ∈ [1, ∞)` there is a measurable
witness `X` with a `Γ₂` tail at the amplitude
`C p^{1/2} (m-n)^{1/2} 3^{-(d/(2p))(l-m)}` and, pointwise in the sample,

`cubeLpENorm (cu_l) p (k_m - k_n) ≤ ofReal (C (m-n)^{1/2} + X omega)`.

The carrier is `Section2.Norms.cubeLpENorm (originCube d l) (ofReal p)`, the
clause's exact carrier, so this file is the assembly step that turns the
improved moment display `IncrementPthMomentLargeCube` into the shape of the clause.

## The pointwise domination

The carrier is the `p`-th root of the normalized volume average of the `p`-th
power of the pointwise size (`cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm`,
the carrier identification). The display `e.kl.bounds.large`
(`exists_witness_finiteShellIncrementPthMomentLargeCube`) bounds that average
pointwise in the sample by the deterministic leading term
`largeCubePthMomentMeanConst d p (m-n)^{p/2}` plus a witness `Y`; taking the
`p`-th root through the sub-additivity of the `p`-th root at index `1/p ≤ 1`
(`Real.rpow_add_le_add_rpow`) splits the deterministic term off again, giving
the pointwise domination by `D^{1/p} (m-n)^{1/2} + Y^{1/p}`. The witness of the
display need not be nonnegative, so the root is taken of
`max (Y omega) 0`; this only helps the pointwise bound, and the tail is
preserved because `|max (Y omega) 0| ≤ |Y omega|`.

## The `Γ₂` tail through the reverse power rule

`OrliczPower.isBigO_gammaSigma_rpow_rev` is the display `e.powerofGammasigma` in the
direction consumed here: a `Γ_{2/p}` tail of `max (Y omega) 0` at the amplitude `K^p` is a
`Γ₂` tail of `(max (Y omega) 0)^{1/p}` at the amplitude `K`, and the amplitude
`K` is the `p`-th root of the tail amplitude of the display, so the decay
`3^{-(d/2)(l-m)}` becomes the printed clause's `3^{-(d/(2p))(l-m)}`.

## The clause and its constant

The witness is `(max (Y omega) 0)^{1/p}` for the witness `Y` of the display; it is
measurable and its `Γ₂` tail is rescaled to the shape
`C p^{1/2} (m-n)^{1/2} 3^{-(d/(2p))(l-m)}` by `IsBigO.mono_scale` for

`C ≥ lpClauseConst d p`,
`lpClauseConst d p = max (largeCubePthMomentMeanConst d p ^ {1/p})
  (largeCubePthMomentTailConst d p ^ {1/p} / p^{1/2})`,

which dominates both the `p`-th root of the deterministic leading constant and
the `p`-th root of the tail constant divided by the printed factor `p^{1/2}`
(the amplitude carries that factor, so the clause's constant absorbs it
as `K^{1/p} ≤ C p^{1/2}`). The constant depends on `d` and `p` only — not on
`s` — and the quantifier order of
`Frozen/Section2/StreamIncrementScaleEstimatesV3` places `C` after `s` and `p`,
so the dependence is admissible. The printed proof reaches
the same shape by taking the `p`-th root of display `e.kl.bounds.large` and
using the power rule for the `Γ`-indices, which is exactly the route taken here;
the printed constant `C(s,d,p)` is again absorbed into `C`.

## Main results

* `largeCubePthMomentMeanConst_nonneg`, `largeCubePthMomentTailConst_nonneg`:
  the nonnegativity of the constants of the display (needed for the
  `p`-th roots and for the amplitude of the reverse power rule).
* `lpClauseConst`: the explicit constant of the clause.
* `cubeLpENorm_finiteShellIncrement_le`: the pointwise domination.
* `exists_witness_cubeLpENorm_finiteShellIncrement`: the clause.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Nonnegativity of the constants -/

private theorem gammaSigmaIndependentSumConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < Book.Ch04.gammaSigmaIndependentSumConst σ := by
  dsimp [Book.Ch04.gammaSigmaIndependentSumConst]
  by_cases hσ_lt : σ < 1
  · simp only [hσ_lt, ↓reduceIte]
    exact
      (mul_pos
        (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)
        (IndependentSums.gammaSigmaHeavyTailConst_pos hσ))
  · dsimp [Book.Ch04.gammaSigmaExpRegimeEndpointConst]
    by_cases hσ_eq : σ = 1
    · subst σ
      simpa only [lt_self_iff_false, ↓reduceIte, gammaSigmaExpRegimeEndpointConst, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left] using
        (mul_pos (by norm_num : 0 < (2 : ℝ))
          IndependentSums.gammaOneExpRegimeConst_pos)
    · have hExpConst_pos : 0 < IndependentSums.gammaSigmaExpRegimeConst σ := by
        dsimp [IndependentSums.gammaSigmaExpRegimeConst]
        exact lt_of_lt_of_le
          (mul_pos (by positivity) (IndependentSums.gammaMomentConst_pos hσ))
          (le_max_left _ _)
      simpa only [hσ_lt, ↓reduceIte, gammaSigmaExpRegimeEndpointConst, hσ_eq, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left, gt_iff_lt] using
        (mul_pos (by norm_num : 0 < (2 : ℝ)) hExpConst_pos)

/-- The supremum constant of the finite-increment display is
nonnegative in every dimension: its three factors are nonnegative. -/
private theorem streamLinftyConst_nonneg (d : ℕ) : 0 ≤ streamLinftyConst d := by
  rw [streamLinftyConst]
  refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
  exact add_nonneg (le_of_lt (gammaSigmaIndependentSumConst_pos (by norm_num)))
    (div_nonneg (Real.sqrt_nonneg d) (by norm_num))

/-- The amplitude constant of the uniform `p`-th moment display
`e.kmn.bounds` is nonnegative. -/
theorem finiteShellIncrementPthMomentConst_nonneg (d : ℕ) {p : ℝ}
    (hp : (1 : ℝ) ≤ p) : 0 ≤ finiteShellIncrementPthMomentConst d p := by
  have hσ : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  rw [finiteShellIncrementPthMomentConst]
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (streamLinftyConst_nonneg d)
  exact mul_nonneg (Real.exp_pos 1).le (le_of_lt (IndependentSums.gammaMomentConst_pos hσ))

/-- The deterministic leading constant of the improved `p`-th moment
display `e.kl.bounds.large` is nonnegative. -/
theorem largeCubePthMomentMeanConst_nonneg {p : ℝ} (hp : (1 : ℝ) ≤ p) :
    0 ≤ largeCubePthMomentMeanConst d p := by
  have hσ : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  rw [largeCubePthMomentMeanConst]
  exact mul_nonneg (le_of_lt (IndependentSums.gammaMomentConst_pos hσ))
    (Real.rpow_nonneg (finiteShellIncrementPthMomentConst_nonneg d hp) p)

/-- The tail constant of the improved `p`-th moment display
`e.kl.bounds.large` is nonnegative. -/
theorem largeCubePthMomentTailConst_nonneg {p : ℝ} (hp : (1 : ℝ) ≤ p) :
    0 ≤ largeCubePthMomentTailConst d p := by
  have hσ : (0 : ℝ) < 2 / p :=
    div_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp)
  have hGm : 0 ≤ IndependentSums.gammaMomentConst (2 / p) :=
    le_of_lt (IndependentSums.gammaMomentConst_pos hσ)
  have hT : 0 ≤ IndependentSums.gammaTriangleConst (2 / p) :=
    le_of_lt IndependentSums.gammaTriangleConst_pos
  have hG : 0 ≤ Book.Ch04.gammaSigmaIndependentSumConst (2 / p) :=
    le_of_lt (gammaSigmaIndependentSumConst_pos hσ)
  have hF : 0 ≤ finiteShellIncrementPthMomentConst d p :=
    finiteShellIncrementPthMomentConst_nonneg d hp
  rw [largeCubePthMomentTailConst]
  exact mul_nonneg (mul_nonneg hT (mul_nonneg (by positivity) hG))
    (mul_nonneg hT (mul_nonneg (add_nonneg zero_le_one hGm)
      (Real.rpow_nonneg hF p)))

/-! ## Elementary real-exponent identities -/

/-- The `p`-th root is inverse to the `p`-th power at a nonnegative base. -/
private theorem rpow_inv_rpow {x p : ℝ} (hx : 0 ≤ x) (hp : p ≠ 0) :
    (x ^ (p : ℝ)⁻¹) ^ p = x := by
  rw [(Real.rpow_mul hx _ _).symm, inv_mul_cancel₀ hp, Real.rpow_one]

/-! ## The constant of the clause -/

/-- **The constant of the `L^p` clause.** The maximum of the `p`-th root of the
deterministic leading constant of the improved `p`-th moment display
`e.kl.bounds.large` and the `p`-th root of its tail constant divided by the
printed factor `p^{1/2}`: it dominates both the coefficient of the deterministic term
`(m-n)^{1/2}` of the clause and, through the factor
`p^{1/2}` of the amplitude, the `p`-th root of the tail constant.
It depends on `d` and `p` only; the quantifier order of the estimates on
the increment places `C` after `s` and `p`, so the dependence is admissible. -/
def lpClauseConst (d : ℕ) (p : ℝ) : ℝ :=
  max (largeCubePthMomentMeanConst d p ^ ((p : ℝ)⁻¹))
    (largeCubePthMomentTailConst d p ^ ((p : ℝ)⁻¹) / p ^ ((1 : ℝ) / 2))

/-! ## The pointwise domination -/

/-- The spatial variable map of the finite shell increment is continuous: every
shell of the carrier stores a continuous value map. -/
private theorem continuous_finiteShellIncrement (omega : ShellSeq d) (n m : ℕ) :
    Continuous (fun x : Vec d ↦ finiteShellIncrement omega n m x) := by
  have hfun : (fun x : Vec d ↦ finiteShellIncrement omega n m x) =
      fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m, (omega k) x := by
    funext x
    rw [finiteShellIncrement_apply]
    rfl
  rw [hfun]
  exact continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous

/-- **The pointwise domination of the `L^p` carrier by the improved
moment display.** For `p ≥ 1` and a witness `Y` of the display
`e.kl.bounds.large` (the hypothesis `hpt`), the carrier
`cubeLpENorm (cu_l) p (k_m - k_n)` is dominated pointwise in the sample by

`largeCubePthMomentMeanConst d p ^ {1/p} (m-n)^{1/2} + (max (Y omega) 0)^{1/p}`:

the carrier is the `p`-th root of the normalized volume average of the `p`-th
power of the pointwise size (`cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm`),
which the display bounds by `D (m-n)^{p/2} + Y omega`; the root is
monotone, and the sub-additivity of the `p`-th root at the index `1/p ≤ 1`
(`Real.rpow_add_le_add_rpow`) splits the deterministic term `D (m-n)^{p/2}`
into `D^{1/p} (m-n)^{1/2}` and the tail term into `Y^{1/p}`. The witness of the
display need not be nonnegative, so the root is taken of
`max (Y omega) 0`; this only enlarges the bound, and the tail is preserved
because `|max (Y omega) 0| ≤ |Y omega|`. -/
theorem cubeLpENorm_finiteShellIncrement_le
    (omega : ShellSeq d) {p : ℝ} (hp : (1 : ℝ) ≤ p) {n m l : ℕ}
    (Y : ShellSeq d → ℝ)
    (hpt : ∀ omega : ShellSeq d,
      volumeAverage (cubeSet (originCube d (l : ℤ)))
          (fun x : Vec d ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p) ≤
        largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p +
          Y omega) :
    cubeLpENorm (originCube d (l : ℤ)) (ENNReal.ofReal p)
        (fun x : Vec d => finiteShellIncrement omega n m x) ≤
      ENNReal.ofReal (largeCubePthMomentMeanConst d p ^ ((p : ℝ)⁻¹) *
        Real.sqrt ((m - n : ℕ) : ℝ) + (max (Y omega) 0) ^ ((p : ℝ)⁻¹)) := by
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp' : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  have hpne : p ≠ 0 := ne_of_gt hp'
  have hq : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.2 hp0
  have hq1 : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hp').mpr hp
  have hMcont : Continuous (fun x : Vec d ↦ finiteShellIncrement omega n m x) :=
    continuous_finiteShellIncrement omega n m
  have hVnn : 0 ≤ volumeAverage (cubeSet (originCube d (l : ℤ)))
      (fun x : Vec d ↦ ‖finiteShellIncrement omega n m x‖ ^ p) :=
    volumeAverage_cubeSet_nonneg _ fun x ↦ Real.rpow_nonneg (norm_nonneg _) p
  have hVle : volumeAverage (cubeSet (originCube d (l : ℤ)))
      (fun x : Vec d ↦ ‖finiteShellIncrement omega n m x‖ ^ p) ≤
      largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p +
        Y omega := hpt omega
  have hpos : 0 ≤ largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p +
      Y omega := le_trans hVnn hVle
  have hDnn : 0 ≤ largeCubePthMomentMeanConst d p :=
    largeCubePthMomentMeanConst_nonneg hp
  have hsqnn : 0 ≤ Real.sqrt ((m - n : ℕ) : ℝ) :=
    Real.sqrt_nonneg _
  have hstep : volumeAverage (cubeSet (originCube d (l : ℤ)))
        (fun x : Vec d ↦ ‖finiteShellIncrement omega n m x‖ ^ p) ^
        ((p : ℝ)⁻¹) ≤
      largeCubePthMomentMeanConst d p ^ ((p : ℝ)⁻¹) *
        Real.sqrt ((m - n : ℕ) : ℝ) + (max (Y omega) 0) ^ ((p : ℝ)⁻¹) := by
    calc volumeAverage (cubeSet (originCube d (l : ℤ)))
          (fun x : Vec d ↦ ‖finiteShellIncrement omega n m x‖ ^ p) ^ ((p : ℝ)⁻¹)
        ≤ (largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p +
              Y omega) ^ ((p : ℝ)⁻¹) :=
          Real.rpow_le_rpow hVnn hVle hq
      _ ≤ (largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p +
            max (Y omega) 0) ^ ((p : ℝ)⁻¹) :=
          Real.rpow_le_rpow hpos
            (add_le_add_right (le_max_left (Y omega) 0)
              (largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p))
            hq
      _ ≤ (largeCubePthMomentMeanConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p) ^
            ((p : ℝ)⁻¹) + (max (Y omega) 0) ^ ((p : ℝ)⁻¹) :=
          Real.rpow_add_le_add_rpow
            (mul_nonneg hDnn (Real.rpow_nonneg hsqnn p))
            (le_max_right (Y omega) 0) hq hq1
      _ = largeCubePthMomentMeanConst d p ^ ((p : ℝ)⁻¹) *
            Real.sqrt ((m - n : ℕ) : ℝ) + (max (Y omega) 0) ^ ((p : ℝ)⁻¹) := by
          rw [Real.mul_rpow hDnn (Real.rpow_nonneg hsqnn p),
            Real.rpow_rpow_inv hsqnn hpne]
  rw [cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm
    (originCube d (l : ℤ)) hp (fun x : Vec d => finiteShellIncrement omega n m x)
    hMcont]
  exact ENNReal.ofReal_le_ofReal hstep

/-! ## The clause -/

/-- **The `L^p` clause**: for `n < m ≤ l` there is
a measurable witness `X` with a `Γ₂` tail at the amplitude
`C p^{1/2} (m-n)^{1/2} 3^{-(d/(2p))(l-m)}` and, pointwise in the sample,

`cubeLpENorm (cu_l) p (k_m - k_n) ≤ ofReal (C (m-n)^{1/2} + X omega)`.

The witness is `Y^{1/p}` for the witness `Y` of the improved `p`-th
moment display `e.kl.bounds.large`
(`exists_witness_finiteShellIncrementPthMomentLargeCube`, taken of
`max (Y omega) 0` because the witness need not be nonnegative; see
`cubeLpENorm_finiteShellIncrement_le`). The `Γ₂` tail is the reverse power rule of
the display `e.powerofGammasigma` (`OrliczPower.isBigO_gammaSigma_rpow_rev`)
applied to the `Γ_{2/p}` tail at the amplitude
`largeCubePthMomentTailConst d p (m-n)^{p/2} 3^{-(d/2)(l-m)}`, whose `p`-th root
is `largeCubePthMomentTailConst d p^{1/p} (m-n)^{1/2} 3^{-(d/(2p))(l-m)}` — the
printed decay `3^{-(d/2)(l-m)}` becomes the printed clause's
`3^{-(d/(2p))(l-m)}` — and is rescaled to the required shape by `IsBigO.mono_scale`
for `C ≥ lpClauseConst d p` (the factor `p^{1/2}` absorbs the
ratio `largeCubePthMomentTailConst d p^{1/p} / p^{1/2}`). The pointwise bound is
`cubeLpENorm_finiteShellIncrement_le` with the deterministic constant
`largeCubePthMomentMeanConst d p` dominated by `C`. The constant of the clause
is therefore explicit:

`C ≥ lpClauseConst d p`,
`lpClauseConst d p = max (largeCubePthMomentMeanConst d p ^ {1/p})
  (largeCubePthMomentTailConst d p ^ {1/p} / p^{1/2})`,

which depends on `d` and `p` only — not on `s` — and the quantifier order
of the estimates places `C` after `s` and `p`, so the dependence is
admissible. The printed proof reaches the same shape by taking
the `p`-th root of display `e.kl.bounds.large` and applying the power rule
`e.powerofGammasigma`; the printed constant `C(s,d,p)` is again absorbed into
`C`. The Sobolev data `s` is carried in the signature for shape
compatibility with the quantifier structure of the clause; this clause does not depend
on it. -/
theorem exists_witness_cubeLpENorm_finiteShellIncrement
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (s p : ℝ)
    (hs : 0 < s) (hsp : s < 1) (hp : (1 : ℝ) ≤ p) (C : ℝ)
    (hC : lpClauseConst d p ≤ C) {n m l : ℕ} (hnm : n < m) (hml : m ≤ l) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X
        (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        cubeLpENorm (originCube d (l : ℤ)) (ENNReal.ofReal p)
          (fun x : Vec d => finiteShellIncrement omega n m x) ≤
          ENNReal.ofReal
            (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega) := by
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp' : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  have hpne : p ≠ 0 := ne_of_gt hp'
  -- The Sobolev data `s` is referenced here only so that the
  -- signature carries the quantifier shape of the clause.
  have _shapeS := hs
  have _shapeSp := hsp
  obtain ⟨Y, hYmeas, hYtail, hYpt⟩ :=
    exists_witness_finiteShellIncrementPthMomentLargeCube
      hPrefix hJ1 hJ2 hJ3 hJ4 hp hnm hml
  refine ⟨fun omega ↦ (max (Y omega) 0) ^ ((p : ℝ)⁻¹), ?_, ?_, ?_⟩
  · exact (Real.continuous_rpow_const (inv_nonneg.2 hp0)).measurable.comp
      (hYmeas.max measurable_const)
  · have hY'nn : ∀ omega : ShellSeq d, 0 ≤ max (Y omega) 0 :=
      fun _ ↦ le_max_right _ _
    have hY'abs : ∀ omega : ShellSeq d, |max (Y omega) 0| ≤ |Y omega| := by
      intro omega
      by_cases h : 0 ≤ Y omega
      · rw [max_eq_left h, abs_of_nonneg h]
      · have hneg : Y omega < 0 := by linarith only [h]
        rw [max_eq_right (le_of_lt hneg), abs_zero, abs_of_neg hneg]
        exact neg_nonneg.mpr hneg.le
    have hY'tail : IsBigO P.toMeasure (gammaSigma (2 / p))
        (fun omega : ShellSeq d ↦ max (Y omega) 0)
        (largeCubePthMomentTailConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - m : ℕ) : ℝ))) :=
      hYtail.of_abs_le hY'abs
    have hTnn : 0 ≤ largeCubePthMomentTailConst d p :=
      largeCubePthMomentTailConst_nonneg hp
    have hsqnn : 0 ≤ Real.sqrt ((m - n : ℕ) : ℝ) := Real.sqrt_nonneg _
    have h3nn : 0 ≤ (3 : ℝ) := by norm_num
    have hexp : (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ))) * p =
        -((d : ℝ) / 2) * ((l - m : ℕ) : ℝ) := by
      field_simp
    set K : ℝ := largeCubePthMomentTailConst d p ^ ((p : ℝ)⁻¹) *
      Real.sqrt ((m - n : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ))) with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hTnn _) hsqnn)
        (Real.rpow_nonneg h3nn _)
    have hKpow : K ^ p =
        largeCubePthMomentTailConst d p * Real.sqrt ((m - n : ℕ) : ℝ) ^ p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((l - m : ℕ) : ℝ)) := by
      rw [hK, Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hTnn _) hsqnn)
        (Real.rpow_nonneg h3nn _),
        Real.mul_rpow (Real.rpow_nonneg hTnn _) hsqnn,
        rpow_inv_rpow hTnn hpne, ← Real.rpow_mul h3nn, hexp]
    have hKXK : IsBigO P.toMeasure (gammaSigma (2 / p))
        (fun omega : ShellSeq d ↦ ((max (Y omega) 0) ^ ((p : ℝ)⁻¹)) ^ p)
        (K ^ p) := by
      rw [hKpow]
      have hfun : (fun omega : ShellSeq d ↦
            ((max (Y omega) 0) ^ ((p : ℝ)⁻¹)) ^ p) =
          (fun omega : ShellSeq d ↦ max (Y omega) 0) := by
        funext omega
        exact rpow_inv_rpow (le_max_right (Y omega) 0) hpne
      rw [hfun]
      exact hY'tail
    have hrev := Probability.isBigO_gammaSigma_rpow_rev
      (mu := P.toMeasure) (σ := 2) (p := p)
      (X := fun omega : ShellSeq d ↦ (max (Y omega) 0) ^ ((p : ℝ)⁻¹)) (K := K)
      hp' hK0 (fun omega ↦ Real.rpow_nonneg (le_max_right (Y omega) 0) _) hKXK
    refine hrev.mono_scale ?_
    have htailroot : largeCubePthMomentTailConst d p ^ ((p : ℝ)⁻¹) ≤
        C * p ^ ((1 : ℝ) / 2) := by
      have hbranch := le_trans (le_max_right
        (largeCubePthMomentMeanConst d p ^ ((p : ℝ)⁻¹))
        (largeCubePthMomentTailConst d p ^ ((p : ℝ)⁻¹) / p ^ ((1 : ℝ) / 2))) hC
      calc largeCubePthMomentTailConst d p ^ ((p : ℝ)⁻¹)
          = (largeCubePthMomentTailConst d p ^ ((p : ℝ)⁻¹) /
              p ^ ((1 : ℝ) / 2)) * p ^ ((1 : ℝ) / 2) :=
            by rw [div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hp' _))]
        _ ≤ C * p ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hbranch (Real.rpow_nonneg hp0 _)
    rw [hK, Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htailroot
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg h3nn _)
  · intro omega
    refine (cubeLpENorm_finiteShellIncrement_le omega hp Y hYpt).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : largeCubePthMomentMeanConst d p ^ ((p : ℝ)⁻¹) *
        Real.sqrt ((m - n : ℕ) : ℝ) ≤
        C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_left _ _) hC) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    linarith only [h1]

end

end SuperdiffusionCLT.Section2.Estimates.Stream