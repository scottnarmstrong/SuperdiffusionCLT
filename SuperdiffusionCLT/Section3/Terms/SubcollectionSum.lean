/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SublatticeCardinality

/-!
# The concentration comparison, summed over the printed subcollections

The comparison of `Section3/Terms/ConcentrationComparison.lean` is stated
at one block family `blocks` and consumes the pairwise independence `hpair` of the
coordinate block averages over that whole family.  The independence rule
`indepFun_volumeAverage_coord_of_subcollectionAtDepth`
(`Section3/Terms/SublatticeIndependence.lean`) holds only *inside* one printed
subcollection `subcollectionAtDepth R t c`, and it cannot be strengthened to the
whole descendant family, because adjacent blocks touch.  Feeding the comparison
the whole family therefore needs an input that does not exist.

The printed argument never asks for it.  There the whole sum is
split over the `3 ^ d` subcollections,

`∑_{z ∈ 3 ^ n ℤ ^ d ∩ cu_m} X_z = ∑_{y ∈ 3 ^ n ℤ ^ d ∩ cu_{n + 1}} ∑_{z ∈ 3 ^ {n + 1} ℤ ^ d ∩ cu_m} X_{y + z}`,

the concentration input is applied to each *inner* sum, and the results are
summed.  This module restates the comparison in that shape: the family is
decomposed into the printed subcollections, the per-subcollection independence
rule is consumed inside each, and the pieces are reassembled with Cauchy-Schwarz
over the classes.  The `d`-only number of subcollections
`printedSubcollectionCount d = (shellColorPeriod d) ^ d`, equal to the printed
`3 ^ d` at the printed colour period, is named explicitly; it multiplies the
printed decay, exactly as the paper absorbs the bounded sublattice count into the
constant `C`.

## Main results

* `printedSubcollectionCount` — the explicit `d`-only subcollection count
  `(shellColorPeriod d) ^ d`, the number the printed `3 ^ d` becomes;
* `lintegral_ofReal_finsetSum_sq_eq_sum_of_pairwise` — the second moment of a
  *sum* of pairwise independent mean-zero `L²` observables is the sum of the
  second moments; this is the inner sum the paper concentrates;
* `lintegral_ofReal_sq_le_subcollectionSum` — the scalar comparison: an
  observable which is the average of a family tiled by the printed
  subcollections, with independence and centring only *inside* each
  subcollection, obeys the printed decay up to the explicit class count, with no
  cardinality hypothesis on the whole family.

## Hypotheses

The comparison carries only the per-subcollection independence `hpair`, the
per-subcollection `L²` membership `hmem`, the per-subcollection centring
`hmean`, and the whole-family energy tiling `htile`.  The whole-family
cardinality hypothesis `hcard` of the comparison above is not needed: the class
counts only enter through their `d`-only number `printedSubcollectionCount`,
bounded by `card_shellColorSet_le`.  The per-subcollection independence `hpair`
comes from the shell laws by
`indepFun_volumeAverage_coord_of_subcollectionAtDepth` of
`Section3/Terms/SublatticeIndependence.lean`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit `d`-only bound on the number of printed subcollections:
`(shellColorPeriod d) ^ d = (Nat.sqrt d + 2) ^ d`.  At the printed colour period
`3` (that is, `d ≤ 3`) this is exactly the printed `3 ^ d`; in
general it is the cardinality of the colour type `Fin d → Fin (shellColorPeriod d)`
which bounds every shell colour set (`card_shellColorSet_le`).  It is the bounded
number of sublattices the printed argument sums over, and the paper absorbs it
into the constant `C`. -/
def printedSubcollectionCount (d : ℕ) : ℕ := (ShellField.shellColorPeriod d) ^ d

/-- **The second moment of a sum of pairwise independent mean-zero `L²`
observables is the sum of their second moments.**  Unlike the finset-*average*
identity `lintegral_ofReal_sq_finsetAverage_eq_of_pairwise`, this is the identity
for the *inner sum* that the concentration input is applied to: the
inverse-count factor is absent, which is what lets the class counts cancel in the
reassembly. -/
theorem lintegral_ofReal_finsetSum_sq_eq_sum_of_pairwise
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Finset ι} {X : ι → Ω → ℝ}
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hmem : ∀ i ∈ s, MeasureTheory.MemLp (X i) 2 μ)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    (∫⁻ ω, ENNReal.ofReal ((∑ i ∈ s, X i ω) ^ 2) ∂μ) =
      ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal ((X i ω) ^ 2) ∂μ := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
    have hpt : (fun ω => ENNReal.ofReal ((∑ i ∈ s, X i ω) ^ 2)) =
        fun ω => ENNReal.ofReal ((s.card : ℝ) ^ 2) *
          ENNReal.ofReal ((((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2) := by
      funext ω
      rw [← ENNReal.ofReal_mul (sq_nonneg ((s.card : ℝ)))]
      congr 1
      rw [mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hcard, one_pow, one_mul]
    rw [hpt, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_ofReal_sq_finsetAverage_eq_of_pairwise hpair hmem hmean]
    have hone : (s.card : ℝ) ^ 2 * ((s.card : ℝ)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hcard, one_pow]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg ((s.card : ℝ))), hone,
      ENNReal.ofReal_one, one_mul]

/-- **The scalar comparison summed over the printed subcollections.**  An
observable `A` which is the average of a family tiled by the classes
`subcollectionAtDepth R t c`, with pairwise independence (`hpair`), `L²`
membership (`hmem`) and centring (`hmean`) required only *inside* each class, and
with the energy tiling `htile` at the whole family, satisfies the printed decay
`3 ^ {− d t}` multiplied by the explicit `d`-only subcollection count.  The
whole-family cardinality is never assumed. -/
theorem lintegral_ofReal_sq_le_subcollectionSum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {R : TriadicCube d} {t : ℕ} {A : Ω → ℝ} {Y Eb : TriadicCube d → Ω → ℝ} {E : Ω → ℝ}
    (hpart : ∀ ω, A ω = (((descendantsAtDepth R t).card : ℝ))⁻¹ *
      ∑ B ∈ descendantsAtDepth R t, Y B ω)
    (htile : ∀ ω, ∑ B ∈ descendantsAtDepth R t, Eb B ω =
      ((descendantsAtDepth R t).card : ℝ) * E ω)
    (hpair : ∀ c ∈ shellColorSet R t, ∀ B ∈ subcollectionAtDepth R t c,
      ∀ B' ∈ subcollectionAtDepth R t c, B ≠ B' →
      ProbabilityTheory.IndepFun (Y B) (Y B') μ)
    (hmem : ∀ c ∈ shellColorSet R t, ∀ B ∈ subcollectionAtDepth R t c,
      MeasureTheory.MemLp (Y B) 2 μ)
    (hmean : ∀ c ∈ shellColorSet R t, ∀ B ∈ subcollectionAtDepth R t c,
      ∫ ω, Y B ω ∂μ = 0)
    (hEmeas : ∀ B ∈ descendantsAtDepth R t,
      AEMeasurable (fun ω => ENNReal.ofReal (Eb B ω)) μ)
    (hEbnonneg : ∀ B ∈ descendantsAtDepth R t, ∀ ω, 0 ≤ Eb B ω)
    (hjensen : ∀ B ∈ descendantsAtDepth R t,
      (∫⁻ ω, ENNReal.ofReal ((Y B ω) ^ 2) ∂μ) ≤
        ∫⁻ ω, ENNReal.ofReal (Eb B ω) ∂μ) :
    (∫⁻ ω, ENNReal.ofReal ((A ω) ^ 2) ∂μ) ≤
      ENNReal.ofReal (((shellColorSet R t).card : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) * (t : ℝ)))) *
      (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) := by
  classical
  have hNne : (((descendantsAtDepth R t).card : ℝ)) ≠ 0 := by
    rw [descendantsAtDepth_card]
    positivity
  -- The average is the average of the class sums.
  have hA : ∀ ω, A ω = (((descendantsAtDepth R t).card : ℝ))⁻¹ *
      ∑ c ∈ shellColorSet R t, ∑ B ∈ subcollectionAtDepth R t c, Y B ω := by
    intro ω
    rw [hpart ω]
    congr 1
    rw [← biUnion_subcollectionAtDepth R t]
    exact Finset.sum_biUnion
      (fun c₁ _ c₂ _ hne => disjoint_subcollectionAtDepth_of_ne hne)
  -- Each inner sum has second moment the sum of its blocks' second moments.
  have hinner : ∀ c ∈ shellColorSet R t,
      (∫⁻ ω, ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2) ∂μ) =
        ∑ B ∈ subcollectionAtDepth R t c,
          ∫⁻ ω, ENNReal.ofReal ((Y B ω) ^ 2) ∂μ :=
    fun c hc => lintegral_ofReal_finsetSum_sq_eq_sum_of_pairwise
      (fun B hB B' hB' hne => hpair c hc B hB B' hB' hne)
      (fun B hB => hmem c hc B hB) (fun B hB => hmean c hc B hB)
  have hinnermeas : ∀ c ∈ shellColorSet R t, AEMeasurable
      (fun ω => ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2)) μ :=
    fun c hc => by
      have h := ((Finset.aemeasurable_sum (subcollectionAtDepth R t c) fun B hB =>
        (hmem c hc B hB).aemeasurable).pow_const 2).ennreal_ofReal
      simpa only [Finset.sum_apply] using h
  -- The class sums reassemble to the whole-family energy.
  have hsumInner : ∑ c ∈ shellColorSet R t,
      (∫⁻ ω, ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2) ∂μ) ≤
      ENNReal.ofReal (((descendantsAtDepth R t).card : ℝ)) *
        (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) := by
    calc ∑ c ∈ shellColorSet R t,
          (∫⁻ ω, ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2) ∂μ)
        = ∑ c ∈ shellColorSet R t, ∑ B ∈ subcollectionAtDepth R t c,
            ∫⁻ ω, ENNReal.ofReal ((Y B ω) ^ 2) ∂μ := Finset.sum_congr rfl hinner
      _ = ∑ B ∈ descendantsAtDepth R t, ∫⁻ ω, ENNReal.ofReal ((Y B ω) ^ 2) ∂μ := by
          rw [← biUnion_subcollectionAtDepth R t]
          exact (Finset.sum_biUnion
            (fun c₁ _ c₂ _ hne => disjoint_subcollectionAtDepth_of_ne hne)).symm
      _ ≤ ∑ B ∈ descendantsAtDepth R t, ∫⁻ ω, ENNReal.ofReal (Eb B ω) ∂μ :=
          Finset.sum_le_sum fun B hB => hjensen B hB
      _ = ∫⁻ ω, ∑ B ∈ descendantsAtDepth R t, ENNReal.ofReal (Eb B ω) ∂μ :=
          (MeasureTheory.lintegral_finsetSum' _ hEmeas).symm
      _ = ∫⁻ ω, ENNReal.ofReal (∑ B ∈ descendantsAtDepth R t, Eb B ω) ∂μ := by
          rw [lintegral_congr fun ω =>
            (ENNReal.ofReal_sum_of_nonneg fun B hB => hEbnonneg B hB ω).symm]
      _ = ∫⁻ ω, ENNReal.ofReal (((descendantsAtDepth R t).card : ℝ) * E ω) ∂μ := by
          rw [lintegral_congr fun ω => by rw [htile ω]]
      _ = ENNReal.ofReal (((descendantsAtDepth R t).card : ℝ)) *
            ∫⁻ ω, ENNReal.ofReal (E ω) ∂μ := by
          rw [lintegral_congr fun ω => ENNReal.ofReal_mul (Nat.cast_nonneg _),
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Cauchy-Schwarz over the classes.
  have hpt : ∀ ω, ENNReal.ofReal ((A ω) ^ 2) ≤
      ENNReal.ofReal ((((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
        ((shellColorSet R t).card : ℝ)) *
        ∑ c ∈ shellColorSet R t,
          ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2) := by
    intro ω
    have hCS : (A ω) ^ 2 ≤ ((((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
        ((shellColorSet R t).card : ℝ)) *
        ∑ c ∈ shellColorSet R t, (∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2 := by
      rw [hA ω, mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (sq_sum_le_card_mul_sum_sq (s := shellColorSet R t)
          (f := fun c => ∑ B ∈ subcollectionAtDepth R t c, Y B ω)) (sq_nonneg _)
    refine le_trans (ENNReal.ofReal_le_ofReal hCS) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun c _ => sq_nonneg _]
  have hNinv : (((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
      ((descendantsAtDepth R t).card : ℝ) = (((descendantsAtDepth R t).card : ℝ))⁻¹ := by
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hNne, mul_one]
  have halg : (((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
      ((shellColorSet R t).card : ℝ) * ((descendantsAtDepth R t).card : ℝ) =
      ((shellColorSet R t).card : ℝ) * (((descendantsAtDepth R t).card : ℝ))⁻¹ := by
    calc (((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 * ((shellColorSet R t).card : ℝ) *
          ((descendantsAtDepth R t).card : ℝ)
        = ((shellColorSet R t).card : ℝ) *
          ((((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
            ((descendantsAtDepth R t).card : ℝ)) := by ring
      _ = ((shellColorSet R t).card : ℝ) * (((descendantsAtDepth R t).card : ℝ))⁻¹ := by
          rw [hNinv]
  calc (∫⁻ ω, ENNReal.ofReal ((A ω) ^ 2) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal ((((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
            ((shellColorSet R t).card : ℝ)) *
          ∑ c ∈ shellColorSet R t,
            ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
            ((shellColorSet R t).card : ℝ)) *
          ∑ c ∈ shellColorSet R t,
            ∫⁻ ω, ENNReal.ofReal ((∑ B ∈ subcollectionAtDepth R t c, Y B ω) ^ 2) ∂μ := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          MeasureTheory.lintegral_finsetSum' _ hinnermeas]
    _ ≤ ENNReal.ofReal ((((descendantsAtDepth R t).card : ℝ))⁻¹ ^ 2 *
            ((shellColorSet R t).card : ℝ)) *
          (ENNReal.ofReal (((descendantsAtDepth R t).card : ℝ)) *
            ∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) :=
        mul_le_mul' le_rfl hsumInner
    _ = ENNReal.ofReal (((shellColorSet R t).card : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) * (t : ℝ)))) * (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), halg,
          descendantsAtDepth_card_inv_eq_rpow]

end

end SuperdiffusionCLT.Section3.Terms
