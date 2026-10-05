/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmM0Headroom

/-!
Stage 4 (task `sc3`), item (3) continued: from the headroom fact
(`ThetaLmM0Headroom.lean`) and the two real-valued scale facts every caller
already has (`hThetaLm`'s own `L - M L^α log³L ≤ m`, and the `m₃`-side
headroom `L - m₃ ≥ 2 M L^α log³L` the paper's "`M` replaced by `2M`" move
gives, via `homogBelow_inflateM3` at the
caller), derive the **natural-number** inequality
`m₃ + 10m₀ + ⌈Cmix·log L⌉₊ + 1 ≤ m` that lets the caller conclude
`m̃ := m - 10m₀ - ⌈Cmix·log L⌉₊ ≥ m₃ + 1 > m₃` by `omega`, with no
`ℕ`-subtraction surprises. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **`m₃ + 10m₀ + ⌈Cmix·log L⌉₊ + 1 ≤ m`**, the natural-number form of
Step 3's positivity/headroom claim. -/
theorem homogBelow_mtilde_ge_m3
    (C0 : ℝ) (hC0 : 1 ≤ C0) (Cmix : ℝ) (hCmix : 1 ≤ Cmix) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ C : ℝ, C1 ≤ C →
      ∀ M alpha cStar nu K : ℝ, 1 ≤ M → 0 ≤ alpha → alpha < 1 →
      0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 → 0 ≤ K →
      ∀ L m m3 : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
        (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3 ≤ (m : ℝ) →
        2 * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ 3) ≤ (L : ℝ) - (m3 : ℝ) →
        m3 + 10 * ⌈C0 * Real.log (L : ℝ) ^ 2⌉₊ + ⌈Cmix * Real.log (L : ℝ)⌉₊ + 1 ≤ m := by
  obtain ⟨C1, hC1_1, hheadroom⟩ := homogBelow_m0_headroom C0 hC0 Cmix hCmix
  refine ⟨C1, hC1_1, ?_⟩
  intro C hC M alpha cStar nu K hM halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK L m m3 hL hm_ge hm3_ge
  have hhr := hheadroom C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK L hL
  have hcomb :
      ((m3 + 10 * ⌈C0 * Real.log (L : ℝ) ^ 2⌉₊ + ⌈Cmix * Real.log (L : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
        (m : ℝ) := by
    push_cast
    linarith only [hhr, hm_ge, hm3_ge]
  exact_mod_cast hcomb

end SuperdiffusionCLT.Section4.HomogBelow
