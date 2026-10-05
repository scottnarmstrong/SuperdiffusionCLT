/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.SlopeStabilityEndpoints
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.SandwichNondegeneracyAttainment
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Window geometry for the iteration lemma: translates, the cap, the normalizers

`l.iteration.lemma` states its window family with **arbitrary real translates** of
the centred triadic cubes,

```
x + □_{j−2} ⊆ U_j ⊆ y + □_j        (for every j ≤ m),
```

which is the paper's own hypothesis: `x` and `y` are unconstrained points of
`ℝ^d`, so `x + □_{j−2}` is in general *not* a triadic cube.  The proved
producers come in two flavours --- `axisCube`-based (arbitrary corner,
arbitrary side) and `TriadicCube`-based --- and only the first applies here.
The translate bridge is proved here: a translate of a centred origin cube *is* an axis cube,
so the anchor's hypothesis yields an `axisCube` sandwich of aspect ratio `1/9` at every scale.

## Main results

* `openCubeSet_originCube_eq_axisCube` — the centred origin cube `□_j` is the axis cube with
  corner `−3^j/2` and side `3^j`.

Nothing here is an estimate: every statement is geometry or measure bookkeeping.

## References

* The paper, `l.iteration.lemma` (the window hypothesis).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open MeasureTheory
open Homogenization (Vec axisCube openCubeSet originCube TriadicCube volumeAverage)
open SuperdiffusionCLT.Section8.Common.Support

noncomputable section

variable {d : ℕ}

/-! ### The translate bridge -/

/-- The centred origin cube `□_j = (−3^j/2, 3^j/2)^d` is the axis cube with corner
`−3^j/2` and side `3^j`. -/
theorem openCubeSet_originCube_eq_axisCube (d : ℕ) (j : ℤ) :
    openCubeSet (originCube d j)
      = axisCube (fun _ => -(1 / 2) * (3 : ℝ) ^ j) ((3 : ℝ) ^ j) := by
  ext z
  simp only [Homogenization.mem_openCubeSet_originCube_iff, axisCube, Set.mem_univ_pi,
    Set.mem_Ioo]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith only [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith only [h2]⟩

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
