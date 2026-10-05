/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-- display `e.Lnaught.def`:

```
L_0(M,alpha,cstar,nu) :=
  ( C(M+1+nondegconst) cstar^{-3} / ((1-alpha)^12 nu^4)
      * log^12( 2 + (M+1+nondegconst) cstar^{-3} / (nu(1-alpha)) )
  )^{1/(1-alpha)}
```

where "the dependence on `nondegconst` is suppressed in the argument list
throughout" and "the universal constant `C` is chosen to be so large that"
a further absorption property holds. `nondegconst` is the
`K` of the marginal nondegeneracy law `a.j.nondeg` / Lean `ShellLawJ5`.

This is a LITERAL definition, not a characterization: `L_0` is exactly the
displayed closed-form real-power expression. Two reading choices:

* **The universal constant `C` is made an explicit argument** (house
  instruction), rather than baked in as an unspecified fixed numeral. Every
  consumer states its own `∃ C(d), ...` and supplies the *same* witness `C`
  both as the proposition's own displayed constant and as this argument (see
  `Section5/Thresholds/HomogBelowAtScales.lean`): the print never distinguishes
  the two `C(d)`s in status (both are "the universal constant, depending
  only on `d`"), and nothing in the print requires them to differ, so a
  single shared witness is the literal, not the strengthened, reading. The
  "chosen so large that ..." absorption property itself is a separate
  existence theorem and is NOT recorded here or anywhere as a hypothesis
  (house instruction).
* **`K` (`nondegconst`) is made an explicit argument**, in the position the
  paper's prose suppresses it from: `lNaught C M alpha cStar nu K`. The
  paper's suppression is cosmetic ("the dependence on `nondegconst` is
  suppressed in the argument list throughout"): the formula itself contains
  `nondegconst` in two places, so it must be a genuine parameter of any
  literal Lean rendering.
* **Every printed power is `Real.rpow`.** `cstar^{-3}`, `(1-alpha)^{12}`,
  `nu^4`, `log^{12}(...)` and the outer `(...)^{1/(1-alpha)}` are all written
  with `Real.rpow`-style `HPow ℝ ℝ ℝ` notation (`^` with a real exponent),
  matching the real-power convention of the formalization (e.g.
  `SstarLowerBound.lean`'s `cStar ^ (-(3:ℝ))`), even where the exponent is
  a positive integer (`12`, `4`), for uniformity and because `alpha` makes
  the outer exponent `1/(1-alpha)` genuinely non-integer in general.
* No positivity/well-definedness side condition is imposed here: this file
  states only the closed-form value, exactly as the print's display does: no
  hypothesis on `M`, `alpha`, `cStar`, `nu`, `K`, or `C` is added (a
  consumer supplies whatever range it needs, e.g. `alpha ∈ [0,1)`,
  `M ∈ [1,∞)`, `cStar > 0`, `nu ∈ (0,1]`, `K > 0`, `1 ≤ C`). -/
noncomputable def SuperdiffusionCLT.Frozen.Section4.lNaught (C M alpha cStar nu K : ℝ) : ℝ :=
  ((C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
        ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ)) ^
    ((1 : ℝ) / (1 - alpha))
