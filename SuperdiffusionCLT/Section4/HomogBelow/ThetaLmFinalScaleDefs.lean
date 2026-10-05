/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmMTildeGeM3

/-!
**The scale definitions** `m̃, n, m̃', m₀` of Step 3 in the proof of `p.homog.below`, with
positivity and `max m2 m3 ≤ m̃ / m̃'`.

This file is generic in `m0`: it does not choose between the `m ≤ L²` and `L² ≤ m` branches
of the `m₀`-threshold (`M0ThresholdB.lean` / `M0ThresholdC.lean`) — it only needs the single fact
`homogBelow_mtilde_ge_m3` already supplies for whichever `m0` the caller
plugs in, namely `m3 + 10*m0 + ⌈Cmix·log L⌉₊ + 1 ≤ m`. The caller picks the
concrete `m0` and proves this hypothesis. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **The scale definitions.** Given the natural-number headroom fact
`hmain` (`homogBelow_mtilde_ge_m3`'s conclusion, for whichever `m0` the
caller supplies), together with `m3 ≥ L/2` (`homogBelow_m3_headroom`'s bonus
output) and `4*m2 ≤ L+3` (`homogBelow_P2prime_verified`'s witness `m2 :=
(L+3)/4`), produces `m̃, n, m̃'` satisfying the defining equations of the paper,
the exact relations `m = m̃'+5m0` and `n = m̃+5m0`, positivity,
and `max m2 m3 ≤ m̃` / `max m2 m3 ≤ m̃'`. -/
theorem homogBelow_scaleDefs
    (Cmix : ℝ) (L m m0 m2 m3 : ℕ)
    (hm2 : 4 * m2 ≤ L + 3)
    (hm3half : L / 2 ≤ m3)
    (hmain : m3 + 10 * m0 + ⌈Cmix * Real.log (L : ℝ)⌉₊ + 1 ≤ m) :
    ∃ mtilde n mtilde' : ℕ,
      mtilde + 10 * m0 + ⌈Cmix * Real.log (L : ℝ)⌉₊ = m ∧
      n = mtilde + 5 * m0 ∧
      mtilde' = n + ⌈Cmix * Real.log (L : ℝ)⌉₊ ∧
      m = mtilde' + 5 * m0 ∧
      mtilde + 4 * m0 ≤ n ∧
      mtilde' + 4 * m0 ≤ m ∧
      1 ≤ mtilde ∧ 1 ≤ n ∧ 1 ≤ mtilde' ∧
      m3 + 1 ≤ mtilde ∧ m3 + 1 ≤ mtilde' ∧
      max m2 m3 ≤ mtilde ∧ max m2 m3 ≤ mtilde' := by
  refine ⟨m - 10 * m0 - ⌈Cmix * Real.log (L : ℝ)⌉₊,
    (m - 10 * m0 - ⌈Cmix * Real.log (L : ℝ)⌉₊) + 5 * m0,
    ((m - 10 * m0 - ⌈Cmix * Real.log (L : ℝ)⌉₊) + 5 * m0) + ⌈Cmix * Real.log (L : ℝ)⌉₊,
    ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

end SuperdiffusionCLT.Section4.HomogBelow
