/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PigRatioData

/-!
# The largeness `1 <= S.L` from the scale binders

The pigeonhole obligation `_hPigRatio` of the final Term 3 statement was reduced to
one statement about the scale selection with five fields: `delta <= 1`, the largeness
`1 <= S.L`, the threshold `_hCT` (`4 Ceta <= nu^{-1} S.L`), the scale identity
`S.a = scaleOffset pigRatioK nu S.L`, and the pigeonhole scalar conjunct
`hpigL`.  This module addresses the question whether `_hCT` follows from the scale
conditions, or is a side condition to carry.

## The reading of `e.L.vs.nu` in the paper

`_hCT` is **not** arithmetic in the other data.  At the least admissible `Ceta`
it is exactly the largeness `4 gammaMomentConst 1 * CL * (crudeLowerConst d)^{-1}
<= nu^{-1} L` on the prescribed scale, and the scale `nu^{-1} L` is not bounded
below by the scale binders.

The paper is explicit that this is a *standing largeness hypothesis of the
section*.  The label `e.L.vs.nu` is attached to the hypothesis of Proposition
`p.sstar.lower.bound`:

```
  L \geq m \geq \frac12 L
  \quad \mbox{and} \quad
  m \geq C\cstar^{-3} \bigl(
  \log^3 (3+\nu^{-1}) \log \log (3+\nu^{-1})
   + (1+\nondegconst)\log(3+\nu^{-1}+\nondegconst)
  \bigr)
  \,,
```

The proofs then *use* this hypothesis by increasing the constant in it, repeatedly
and by name:

* "by~\eqref{e.h.restrictions} and the lower bound on~$L$ in
  \eqref{e.L.vs.nu} (with the constant there taken large relative to~$K$)";
* "after increasing the constant in~\eqref{e.L.vs.nu} if necessary";
* "after increasing the threshold in~\eqref{e.L.vs.nu}";
* "the lower bound `h >= 10 ceil(K log^2(nu^{-1}L))` is satisfied
  under~\eqref{e.L.vs.nu}";
* "After increasing the lower threshold in~\eqref{e.L.vs.nu}".

So `e.L.vs.nu` is the proposition's own lower-bound-on-`L` hypothesis, and the
"increase the constant" of those places is the paper's uniform way of absorbing a
prescribed constant or log-power into it.  Since `e.L.vs.nu` bounds `m <= L`
below by an expression in `nu` and `cstar` alone, taking its constant large
relative to the fixed constant of `_hCT` (a `d`- and `CL`-expression) yields
`nu^{-1} L >= 4 Ceta`: exactly the datum `_hCT`.  Hence `_hCT` is a legitimate
side condition to carry, of the same kind as the log threshold
`11 <= log(nu^{-1} L)`, and not something the scale conditions imply.

Moreover, `hloc : localizationConst d <= CL` does not bound `CL`, and `hCT` is
false for every sufficiently large `CL`, so no bound on the scale conditions can
discharge `_hCT` while `CL` is a free binder.

## Main results

* `one_le_L_of_scalesOrdering`: the field `1 <= S.L` follows from the binder
  `ScalesOrdering S` alone (`L' < L`), so the residual loses that field.

The scale selection satisfying the five fields is realized from the printed threshold by
`exists_scaleSelection_of_threshold` (`Section3/Setup/ScaleAssembly.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

noncomputable section

/-! ## The largeness `1 <= S.L` is a binder, not a residual -/

/-- **The field `1 <= S.L` of the scale selection is already a binder.**  The final
Term 3 statement carries `_hSorder : ScalesOrdering S`, whose `LPrime_lt_L` is
`S.LPrime < S.L`; hence `S.L >= 1` and the field `hL` of the residual statement costs
nothing beyond the binders of that statement. -/
theorem one_le_L_of_scalesOrdering {S : ScaleSelection} (hS : ScalesOrdering S) :
    1 ≤ S.L := by
  have h := hS.LPrime_lt_L
  omega

end

end SuperdiffusionCLT.Section3.Terms
