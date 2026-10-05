/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespUniformBound

/-!
# A descendant-uniform bound on `maxDescendantNormalizedBlockResponseAtScale`

Every descendant cube `R ∈ descendantsAtScale Q k` (for `k ≤ Q.scale`) is a
subset of `Q` (`cubeSet_subset_of_mem_descendantsAtScale`), so ellipticity of
`a` on `cubeSet Q` restricts to each `R` (`IsEllipticFieldOn.mono`) with the
SAME constants `(lam, Lam)`; `LimitRespUniformBound.lean`'s explicit,
`R`-independent bound then bounds `normalizedBlockResponseMax R a a0`
uniformly over every `R`, hence bounds their `finsetSsup`.

## Main result

* `srootL3_maxDescendant_le`: an explicit bound on
  `maxDescendantNormalizedBlockResponseAtScale Q k a a0`, uniform in `k ≤
  Q.scale`, from `IsEllipticFieldOn lam Lam (cubeSet Q) a`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory

noncomputable section

/-- **A `k`-uniform bound on `maxDescendantNormalizedBlockResponseAtScale`**,
from a single ellipticity fact on the whole cube `Q`. -/
theorem srootL3_maxDescendant_le {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    maxDescendantNormalizedBlockResponseAtScale Q k a a0 ≤
      (lam / (1 + 2 * Lam ^ 2))⁻¹ *
          fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0) +
        (lam / (1 + 2 * Lam ^ 2))⁻¹ * blockMatrixOfCoeffNormSqBound lam Lam *
          fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0) := by
  unfold maxDescendantNormalizedBlockResponseAtScale finsetSsup
  have hne : (((fun R => normalizedBlockResponseMax R a a0) ''
      (↑(descendantsAtScale Q k) : Set (TriadicCube d)))).Nonempty :=
    Set.Nonempty.image _ (Finset.coe_nonempty.2 (descendantsAtScale_nonempty Q hk))
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hRmem : R ∈ descendantsAtScale Q k := Finset.mem_coe.mp hR
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtScale hk hRmem)
  exact srootL3_normalizedBlockResponseMax_le R a a0 hEllR

end

end SuperdiffusionCLT.Section4.MinimalScales
