/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyMainB
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyScale
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyT0StrongA
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyT0StrongB
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyRefCompare
public import SuperdiffusionCLT.Section4.NewMixing.RatioBound
public import SuperdiffusionCLT.Section4.NewMixing.Nu4Threshold
public import SuperdiffusionCLT.Section4.NewMixing.T0Refinement

/-!
# The assembly of `l.new.mixing.parameterized`

Lemma `l.new.mixing.parameterized`. The statement is the one recorded in `ParamStatement.lean`.
Its two carried hypotheses are the homogenization-below-cutoff statement `hHomog` and the
cutoff comparison `hComp`.

The proof combines:

* the scale construction with its witnesses identified (`AssemblyScale.lean`);
* the reference comparison from `hHomog` and the cutoff localization
  (`AssemblyRefCompare.lean`), the ratio bound `newMixRatio_bound`;
* the `T_0` refinement uniform in the test direction and sign
  (`AssemblyT0StrongA.lean`, `AssemblyT0StrongB.lean`);
* the energy bound and the passage to the doubled response at fixed parameters
  (`AssemblyMainB.lean`, `AssemblyBridge.lean`);

and one shared constant `C`, to which every threshold is folded with `lNaught_mono_both` and
`newMixAsm_lNaught_le_half`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **Satisfiability of the range hypotheses.** For every constant `C`, every `α, c⋆, ν` and every
`M, K ≥ 1`, the folded threshold, the `m`-scale threshold, the gap condition and the
`|L - r|` condition of the assembled statement hold simultaneously at
`L = m = r = ⌈L₀⌉`. -/
theorem newMixAsm_threshold_witness {C M K alpha cStar nu nondeg : ℝ} (hM : 1 ≤ M)
    (hK : 1 ≤ K) :
    ∃ L m r : ℕ,
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
        (L : ℝ) ∧
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
        (m : ℝ) ∧
      (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) ∧
      |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) := by
  have hLn := Nat.le_ceil
    (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg)
  refine ⟨⌈SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu
    nondeg⌉₊, ⌈SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu
    nondeg⌉₊, ⌈SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu
    nondeg⌉₊, hLn, hLn, ?_, ?_⟩
  · set L : ℕ := ⌈SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu
      nondeg⌉₊ with hLdef
    have h1 : 0 ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg L) _
    have h2 : 0 ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
      Real.rpow_nonneg (Real.log_natCast_nonneg L) _
    have : 0 ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
      mul_nonneg (mul_nonneg (by linarith only [hM]) h1) h2
    linarith only [this]
  · rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith only [hK]) (Real.log_natCast_nonneg _)

/-- The same at the consumer constants `α = 0`, `c⋆ = 2`, `ν = 1`, `M = 1`, `K = 1`,
`nondeg = 1`, for every `C`. -/
example (C : ℝ) :
    ∃ L m r : ℕ,
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (1 + 1)) 0 2 1 1 ≤ (L : ℝ) ∧
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (1 + 1)) 0 2 1 1 ≤ (m : ℝ) ∧
      (L : ℝ) - 1 * (L : ℝ) ^ (0 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) ∧
      |(L : ℝ) - (r : ℝ)| ≤ 1 * Real.log (L : ℝ) :=
  newMixAsm_threshold_witness (C := C) (M := 1) (K := 1) (alpha := 0) (cStar := 2) (nu := 1)
    (nondeg := 1) le_rfl le_rfl

end
end SuperdiffusionCLT.Section4.NewMixing
