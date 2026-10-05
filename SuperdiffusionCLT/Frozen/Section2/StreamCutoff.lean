/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.Finite

@[expose] public section

/-- The infrared cutoff `k_L(x) = ∑_{n=0}^{L} j_n(x)` of the marginal stream
matrix at scale `3 ^ L`. -/
noncomputable def SuperdiffusionCLT.Frozen.Section2.streamCutoff {d : ℕ}
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L : ℕ) :
    Homogenization.RegCoeffField d :=
  ∑ n ∈ Finset.range (L + 1),
    SuperdiffusionCLT.Section2.Cutoff.shellReg omega n
