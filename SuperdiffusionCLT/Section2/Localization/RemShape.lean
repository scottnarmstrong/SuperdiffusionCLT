/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.ShiftedRemainderAdopt
public import SuperdiffusionCLT.Section2.Localization.SkewRemainderRepresentation
public import SuperdiffusionCLT.Section2.Localization.Conj3RatioSandwich
public import SuperdiffusionCLT.Section2.Localization.SkewRemainderVariational
public import SuperdiffusionCLT.Section2.Localization.Conj3BridgeIdentity
public import SuperdiffusionCLT.Section2.Localization.TransposeMaximizer
public import Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The shape of the remainder: linear at the difference, quadratic on the skew piece

## What the paper proves

Reading Step 2 of the proof in full, it delivers **two different things**, and
neither of them is a quadratic bound at the whole difference `Z − Z̃`.

**(L1) The linear display at the difference.**  Verbatim:

> Since `Z-\tilde Z` is an admissible zero-boundary variation for both
> minimization problems, the first variations give
> `‖𝐀^{1/2}(Z-\tilde Z)‖² = ⨍_U(𝐀\tilde Z·\tilde Z − 𝐀Z·Z)`

and:

> Combining the two identities with (e.minimizers.pointwise.ratio), we obtain
> `‖𝐀^{1/2}(Z-\tilde Z)‖²_{L²(U)} + ‖\tilde𝐀^{1/2}(Z-\tilde Z)‖²_{L²(U)}
> ≤ Cη(P·𝐀(U;a)P + P·𝐀(U;ã)P)`.

The factor on the loading energy is `Cη` — **linear** in `η`.

**(Q1) The field split and the quadratic bound on the pure-skew piece.**  Verbatim:

> Now write
> `\tilde Z = ½(∇ũ+∇ũ*, ã∇ũ − ãᵗ∇ũ*) + ½(0, h(∇ũ+∇ũ*))`,

the two summands being `\tilde Z_0` and `\tilde Z_1`.  The first slot of
`\tilde Z_1` is literally `0`; and, verbatim,

> By the definition of `η`,
> `‖𝐀^{1/2}\tilde Z_1‖²_{L²(U)} ≤ C‖s^{-1/2}h(∇ũ+∇ũ*)‖²_{L²(U)}
> ≤ Cη²(‖s^{1/2}∇ũ‖² + ‖s^{1/2}∇ũ^*‖²) ≤ Cη² P·𝐀(U;ã)P`.

The factor here is `η²` — **quadratic** — and the field it bounds is the skew
piece `\tilde Z_1`, not the difference.

**The two printed statements differ from a quadratic bound at the whole difference.**  A
quadratic bound at `Z − Z̃` itself is *neither* of them:

* it is strictly **stronger** than (L1): its factor `η²` is below the display's `η(2 + η)`,
  so it implies (L1) but is not implied by it;
* it is a statement about the **wrong field** for (Q1): (Q1) bounds
  `\tilde Z_1`, whose potential slot is `0`, while `Z − Z̃` has a potential slot
  that is a difference of two zero-trace potentials, not `0` pointwise.

## What this module lands

* `PureSkewPiece` / `conj3PureSkewPiece` — the carrier of (Q1) at our carriers, the pure-skew
  piece whose first slot is `0`.
* `conj3SkewRemainderField` — the route's skew remainder field, the paper's `h`.
* `conj3SkewRemainderField_skew` — the route's skew remainder field is pure skew,
  a consequence of the construction (`SkewRemainderRepresentation`).

All dimension-specific statements carry `2 ≤ d`; dimension one is out
of scope, as in the statement.  Names from other namespaces are fully
qualified.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## (Q1): the quadratic bound on the pure-skew piece -/

/-- **(Q1), the pure-skew piece `Z̃₁`.**  Given the skew
remainder `H` and the vector field `r` that plays the role of `∇ũ + ∇ũ*`, this is
the field `½ (0, H r)`: its first slot is the zero vector, which is what makes the
quadratic shape applicable to it and inapplicable to the whole difference. -/
noncomputable def PureSkewPiece {d : ℕ} (H : Vec d → Mat d) (r : Vec d → Vec d) :
    Vec d → BlockVec d :=
  fun x => ((0 : Vec d), matVecMul (H x) (r x))

/-- **The skew remainder field of the cutoff pair.**  The paper's `h`,
`h = κ_L − κ_m − (κ_L − κ_m)_U`, read at our carriers: the difference of
the perturbed field `centeredPairField` and the base field `coefficientCutoff`.
This is the field the quadratic bound (Q1) is stated for. -/
noncomputable def conj3SkewRemainderField {d : ℕ} (nu : ℝ) (omega : ShellSeq d)
    (m L : ℕ) (U : Set (Vec d)) : Vec d → Mat d :=
  fun x => centeredPairField nu omega m L U x -
    (coefficientCutoff nu omega m).toCoeffField x

/-- **(Q1) at the cutoff pair.**  The pure-skew piece is built from the
route's skew remainder field and the potential slot of the route's perturbed
doubled field `Zt = routeDoubledFieldL`; the loading is `(−p, q)`. -/
abbrev conj3PureSkewPiece {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) : Vec d → BlockVec d :=
  PureSkewPiece (conj3SkewRemainderField nu omega m L (U : Set (Vec d)))
    (fun x => (routeDoubledFieldL U nu hnu omega m L hmL p q u).potential x)

/-- **The route's skew remainder field is pure skew.**  A consequence of the
construction, not an extra hypothesis: both coefficient fields have symmetric part
`ν Id`, so their difference is pointwise anti-symmetric
(`SkewRemainderRepresentation.remainder_centeredPairField_skew`). -/
theorem conj3SkewRemainderField_skew (nu : ℝ) (omega : ShellSeq d) (m L : ℕ)
    (U : Set (Vec d)) (x : Vec d) :
    matTranspose (conj3SkewRemainderField nu omega m L U x) =
      -(conj3SkewRemainderField nu omega m L U x) :=
  remainder_centeredPairField_skew nu omega m L U x

end

end SuperdiffusionCLT.Section2.Localization
