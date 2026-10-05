/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE
public import SuperdiffusionCLT.Section2.CutoffApproximationWork

/-!
# Everywhere measurability of the shifted limiting field `srootE_limField`

`srootE_limField nu omega m n k` is `nu • 1 + centeredStreamField omega
(cubeSet (originCube d m)) (shift + ·)`, where `centeredStreamField` is a
`tsum` of shell terms: it is only *a.e.* strongly measurable in general
(`SuperdiffusionCLT.Section2.Cutoff.centeredStreamField_entry_aeStronglyMeasurable`),
since `tsum` is junk off the summability event. `IsEllipticFieldOn`, however,
needs *everywhere* `Measurable`.

Under a *global* (not a.e.) summability hypothesis on the shell-derivative
sup-norms on the recentering cube `cu_m` (available once we are inside a
`filter_upwards` block at a fixed `omega`), `summable_centeredShellTerm` gives
summability at *every* point of `cu_m`, not merely a.e., so the finite partial
sums converge to `centeredStreamField` pointwise everywhere on the shifted
cube `cu_n`. Each partial sum, restricted to `cu_n` and extended by `0`, is
globally measurable (continuous on a measurable piece); the pointwise limit of
globally measurable functions is globally measurable
(`measurable_of_tendsto_metrizable`). This module records that argument.

## Main result

* `srootL4_measurable_srootE_limField_entry`: entrywise everywhere
  measurability of the restriction of `srootE_limField` to `cu_n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory Filter
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers

noncomputable section

private theorem srootL4_tendsto_partialSum_centeredStreamField {d : ℕ}
    (omega : ShellSeq d) (U : Set (Vec d)) (i j : Fin d) {y : Vec d}
    (hsum : Summable fun k : ℕ => centeredShellTerm omega U k y) :
    Filter.Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, centeredShellTerm omega U k y) i j)
      Filter.atTop (nhds (centeredStreamField omega U y i j)) := by
  have hhs : HasSum (fun k : ℕ => centeredShellTerm omega U k y)
      (centeredStreamField omega U y) := by
    rw [centeredStreamField_eq_tsum]
    exact hsum.hasSum
  have hhs_entry := hhs.map (SuperdiffusionCLT.Section2.Cutoff.matEntryCLM d i j)
    (SuperdiffusionCLT.Section2.Cutoff.matEntryCLM d i j).continuous
  have hlim := hhs_entry.tendsto_sum_nat
  have hlim' : Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, centeredShellTerm omega U k y i j)
      Filter.atTop (nhds (centeredStreamField omega U y i j)) := by
    simpa only [Function.comp_apply,
      SuperdiffusionCLT.Section2.Cutoff.matEntryCLM_apply] using hlim
  have heq : (fun N : ℕ => (∑ k ∈ Finset.range N, centeredShellTerm omega U k y) i j) =
      fun N : ℕ => ∑ k ∈ Finset.range N, centeredShellTerm omega U k y i j := by
    funext N
    rw [Matrix.sum_apply]
  rw [heq]
  exact hlim'

open Classical in
/-- **Everywhere measurability, entrywise, of the shifted limiting field
restricted to `cu_n`.** Given a *global* summability hypothesis (not a.e.) on
`cu_m`, the field `srootE_limField` agrees on `cu_n` with the pointwise
(everywhere) limit of its globally measurable finite partial sums. -/
theorem srootL4_measurable_srootE_limField_entry {d : ℕ} (omega : ShellSeq d)
    (m n : ℕ) (k : Fin d → ℤ)
    (hk : (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun j : ℕ =>
      shellDerivLinftyNorm (cubeSet (originCube d (m : ℤ))) (omega j))
    (i j : Fin d) :
    Measurable (fun x : Vec d =>
      if x ∈ cubeSet (originCube d (n : ℤ))
      then centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
        ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) i j
      else 0) := by
  classical
  set Un : Set (Vec d) := cubeSet (originCube d (n : ℤ)) with hUn
  set Um : Set (Vec d) := cubeSet (originCube d (m : ℤ)) with hUm
  set shift : Vec d → Vec d := fun x => (fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x
    with hshift
  have hUb : Bornology.IsBounded Um := isBounded_cubeSet _
  have hUconv : Convex ℝ Um := SuperdiffusionCLT.Section2.Estimates.Stream.convex_cubeSet _
  have hUpos : MeasureTheory.volume Um ≠ 0 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero _
  have hshiftCont : Continuous shift := continuous_const.add continuous_id
  set T : ℕ → Vec d → ℝ := fun N x =>
      if x ∈ Un then (∑ k ∈ Finset.range N, centeredShellTerm omega Um k (shift x)) i j else 0
    with hT
  have hTmeas : ∀ N : ℕ, Measurable (T N) := by
    intro N
    refine Measurable.ite (measurableSet_cubeSet _) ?_ measurable_const
    have hsumN : (fun x : Vec d =>
        (∑ k ∈ Finset.range N, centeredShellTerm omega Um k (shift x)) i j) =
        fun x : Vec d =>
          ∑ k ∈ Finset.range N, centeredShellTerm omega Um k (shift x) i j := by
      funext x
      rw [Matrix.sum_apply]
    rw [hsumN]
    exact (continuous_finsetSum _
      (fun l _ => (centeredShellTerm_entry_continuous omega Um l i j).comp hshiftCont)).measurable
  have hTlim : Filter.Tendsto T Filter.atTop
      (nhds (fun x : Vec d =>
        if x ∈ Un then centeredStreamField omega Um (shift x) i j else 0)) := by
    classical
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : x ∈ Un
    · have hxUm : shift x ∈ Um := hk ⟨x, hx, rfl⟩
      have hsumx : Summable fun k : ℕ => centeredShellTerm omega Um k (shift x) :=
        summable_centeredShellTerm hUb hUconv hUpos omega hsum hxUm
      have := srootL4_tendsto_partialSum_centeredStreamField omega Um i j hsumx
      simpa only [hT, hx, ite_true] using this
    · simpa only [hT, hx, ite_false] using tendsto_const_nhds (x := (0 : ℝ))
  simpa only [hUn, hUm, hshift] using measurable_of_tendsto_metrizable hTmeas hTlim

end

end SuperdiffusionCLT.Section4.MinimalScales
