/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitFieldConvergence

/-!
# Uniform (not merely pointwise) convergence of the cutoff field on `cu_m`

The pointwise convergence of the cutoff field on `cu_m` to the limiting field (almost surely)
rests on the tail of the defining series (see `LimitFieldConvergence.lean`). The termwise-continuity
gap identified in `LimitAssembly.lean` (propagating field convergence through
`coarseBlockMatrix`/`BlockJ`/`normalizedBlockResponseMax`/`scaleResponseAtScale`)
needs a quantitative (Lipschitz-type) estimate, which in turn is driven by a
uniform (`L^∞`-on-the-cube) smallness of the perturbation `k - k_L`, not merely
its pointwise vanishing. This module upgrades the convergence to exactly that:
a single, `x`-independent bound sequence `bound : ℕ → ℝ` that dominates
`‖centeredStreamField omega U x - centeredStreamCutoff omega L U x‖` for every
`x ∈ U` and tends to `0` as `L → ∞`.

The upgrade uses nothing beyond what the pointwise proof already uses: the
same a.s. Borel-Cantelli summability
`SuperdiffusionCLT.Section2.Cutoff.eventually_summable_shellDerivLinftyNorm`
of the shell sup-norms on `cu_{m+1}`, together with the *uniform* termwise bound
`SuperdiffusionCLT.Section2.Carriers.norm_centeredShellTerm_le`
(`‖j_k(x) - (j_k)_U‖ ≤ √d · diam(U) · ‖∇j_k‖_{L∞(U)}`, independent of `x ∈ U`),
which turns the Weierstrass M-test into a uniform tail bound.

## Main result

* `srootL2_tendsto_uniformOn_centeredStreamCutoff_centeredStreamField`: almost
  surely there is a nonnegative `bound : ℕ → ℝ`, tending to `0`, dominating the
  cutoff/limit gap uniformly on `cu_m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Filter Homogenization
open scoped Matrix.Norms.Elementwise
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Frozen.Assumptions

/-- A summable nonnegative real sequence stays summable after a fixed shift.
Isolated as a standalone lemma (no ambient `Mat`/`Vec`/`ShellSeq` clutter) so
that the generic topological-group instance search stays fast. -/
private theorem srootL2_shiftSummable {f : ℕ → ℝ} (hf : Summable f) (c : ℕ) :
    Summable (fun j : ℕ => f (c + j)) := by
  have h := (summable_nat_add_iff c).2 hf
  simpa [add_comm] using h

/-- The tail sums of a real sequence, shifted by a fixed successor offset,
tend to `0` (no summability hypothesis needed: off the summability event both
sides are the junk value `0`). Isolated as a standalone lemma so that the
`congr`/`funext` reindexing stays fast, away from the ambient clutter of the
main proof. -/
private theorem srootL2_tendsto_shift_tsum (f : ℕ → ℝ) :
    Filter.Tendsto (fun L : ℕ => ∑' j : ℕ, f (L + 1 + j)) Filter.atTop (nhds 0) := by
  have htail : Filter.Tendsto (fun i : ℕ => ∑' k : ℕ, f (k + i)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add f
  have hshift : (fun L : ℕ => ∑' j : ℕ, f (L + 1 + j)) =
      (fun i : ℕ => ∑' k : ℕ, f (k + i)) ∘ (fun L : ℕ => L + 1) := by
    funext L
    simp only [Function.comp_apply]
    congr 1
    funext j
    congr 1
    omega
  rw [hshift]
  exact htail.comp (tendsto_add_atTop_nat 1)

/-- **Uniform (`L^∞(cu_m)`) convergence of the cutoff field to the limiting
field.** Almost surely, there is a nonnegative sequence `bound : ℕ → ℝ`,
independent of `x`, with `bound → 0`, such that for every `L` and every
`x ∈ cu_m` the cutoff/limit gap at `x` is at most `bound L`. -/
theorem srootL2_tendsto_uniformOn_centeredStreamCutoff_centeredStreamField {d : ℕ}
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P)
    (m : ℕ) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ bound : ℕ → ℝ, (∀ L : ℕ, 0 ≤ bound L) ∧
        (∀ L : ℕ, ∀ x : Vec d, x ∈ cubeSet (originCube d (m : ℤ)) →
          ‖centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x -
              centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ))) x‖ ≤
            bound L) ∧
        Filter.Tendsto bound Filter.atTop (nhds 0) := by
  set U : Set (Vec d) := cubeSet (originCube d (m : ℤ)) with hU
  have hsum :=
    SuperdiffusionCLT.Section2.Cutoff.eventually_summable_shellDerivLinftyNorm
      (P := P) hJ3 (m := m + 1) (U := U)
      (srootL_cubeSet_subset_openCubeSet_succ m)
  filter_upwards [hsum] with omega homega
  have hUb : Bornology.IsBounded U := isBounded_cubeSet _
  have hUconv : Convex ℝ U :=
    SuperdiffusionCLT.Section2.Estimates.Stream.convex_cubeSet _
  have hUpos : MeasureTheory.volume U ≠ 0 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.volume_cubeSet_ne_zero _
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hUb
  obtain ⟨x0, hx0⟩ := MeasureTheory.nonempty_of_measure_ne_zero hUpos
  have hR0 : 0 ≤ R := le_trans dist_nonneg (hR hx0 hx0)
  set C : ℝ := Real.sqrt d * R with hCdef
  have hCnonneg : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hR0
  refine ⟨fun L => C * ∑' j : ℕ, shellDerivLinftyNorm U (omega (L + 1 + j)), ?_, ?_, ?_⟩
  · intro L
    exact mul_nonneg hCnonneg (tsum_nonneg fun j => shellDerivLinftyNorm_nonneg U _)
  · intro L x hx
    have hsumX : Summable (fun k : ℕ => centeredShellTerm omega U k x) :=
      summable_centeredShellTerm hUb hUconv hUpos omega homega hx
    have hid : centeredStreamField omega U x - centeredStreamCutoff omega L U x =
        ∑' j : ℕ, centeredShellTerm omega U (L + 1 + j) x :=
      centeredStreamField_sub_centeredStreamCutoff hUb omega hsumX L
    rw [hid]
    have hbound_term : ∀ j : ℕ, ‖centeredShellTerm omega U (L + 1 + j) x‖ ≤
        C * shellDerivLinftyNorm U (omega (L + 1 + j)) :=
      fun j => norm_centeredShellTerm_le hUb hUconv hUpos hR omega (L + 1 + j) hx
    have hsummableShift' : Summable (fun j : ℕ => shellDerivLinftyNorm U (omega (L + 1 + j))) :=
      srootL2_shiftSummable homega (L + 1)
    have hsummableC : Summable (fun j : ℕ => C * shellDerivLinftyNorm U (omega (L + 1 + j))) :=
      hsummableShift'.mul_left C
    have hsummableNorm : Summable (fun j : ℕ => ‖centeredShellTerm omega U (L + 1 + j) x‖) :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound_term hsummableC
    calc ‖∑' j : ℕ, centeredShellTerm omega U (L + 1 + j) x‖
        ≤ ∑' j : ℕ, ‖centeredShellTerm omega U (L + 1 + j) x‖ :=
          norm_tsum_le_tsum_norm hsummableNorm
      _ ≤ ∑' j : ℕ, C * shellDerivLinftyNorm U (omega (L + 1 + j)) :=
          hsummableNorm.tsum_le_tsum hbound_term hsummableC
      _ = C * ∑' j : ℕ, shellDerivLinftyNorm U (omega (L + 1 + j)) := tsum_mul_left
  · have htailShift : Filter.Tendsto
        (fun L : ℕ => ∑' j : ℕ, shellDerivLinftyNorm U (omega (L + 1 + j)))
        Filter.atTop (nhds 0) :=
      srootL2_tendsto_shift_tsum (fun r : ℕ => shellDerivLinftyNorm U (omega r))
    simpa using htailShift.const_mul C

end SuperdiffusionCLT.Section4.MinimalScales
