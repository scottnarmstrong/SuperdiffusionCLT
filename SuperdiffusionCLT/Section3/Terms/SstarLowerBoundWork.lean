/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# The suboptimal lower bound `p.sstar.lower.bound`: the statement and the first conjunct

## The statement

The paper's `p.sstar.lower.bound` ("Suboptimal lower bound estimate") reads: there exist
`C(d) ∈ [1,∞)` and `c(d) ∈ (0,1/2]` such that, for every `L, m ∈ ℕ` satisfying `e.L.vs.nu`,

```
L >= m >= 1/2 L and m >= C cStar^{-3} ( log^3 (3 + nu^{-1}) log log (3 + nu^{-1})
                                          + (1 + nondegconst) log(3 + nu^{-1} + nondegconst) )
```

with `sigmaBar_L = lim_{r→∞} sigmaBar_{L,*}(cu_r)`, we have `e.sstar.lower.bound`,

```
sigmaBar_L >= sigmaBar_{L,*}(cu_m) >= c cStar^{3/2} nu^2 m^{1/2} log^{-9/2}(nu^{-1} m),
```

and moreover the quenched estimate `e.sstar.lower.bound.quenched` holds:

```
sigmaStar_{L,*}^{-1}(cu_m) <= C nu^{-2} cStar^{-3/2} m^{-1/2} log^{9/2}(nu^{-1} m) Id
                              + O_{Gamma_2}(C nu^{-2} 3^{-m/8}) Id.
```

The standing assumptions are `nu ∈ (0,1]` (the molecular diffusivity) and the multiscale stream
assumption `a.multiscale.stream` (the stream matrix `k(x) = sum_{n>=0} j_n(x)` with the clauses
J1 (range of dependence `3^n sqrt d`), J2 (independence of disjoint subcollections), J3 (local
regularity), J4 (dihedral symmetry) and J5 (non-degeneracy, with constants `cStar, nondegconst`)).
They are rendered as `ShellLawPrefix/J1V2/J2/J3/J4` and `ShellLawJ5`.

## Proof outline

If the running diffusivity does not grow fast enough in `m`, then by its monotonicity in the
spatial scale there is a range of scales across which it barely changes, the maximizers at the two
ends of that range are comparable, and the maximizer at the largest scale is nearly affine; an
almost-affine maximizer forces either no advection (excluded by `a.j.nondeg`, J5) or a large
diffusivity.  Concretely:

* fix `delta = c_0 cStar^2` and select the window `h` subject to `e.h.restrictions`; set
  `A_k := bfAhom_L(cu_k)`, use the subadditivity chain `bfAhom_L <= A_k <= bfE_L` together with
  `det bfAhom_L = 1` and `det bfE_L <= (C nu^{-1} L)^{2d}` to pigeonhole a scale with
  `|A_m A_{m-2h}^{-1} - 1| <= delta` (`e.pigeon.matrix` / `e.pigeon.scalar`);
* choose the scale-separation constant `K` and the window, then the three scale conditions,
  including the absorption `cStar h > C(1 + nondegconst + K log(nu^{-1}L))` (this is the step that
  forces the correction of the threshold, see below);
* the **master inequality** `cStar h sigmaBar_{L',*}^{-1}(cu_n) <= ...`;
* absorb, insert the homogenization comparison `e.bell.vs.starell`, the two balanced localization
  comparisons, the optimized window size `e.h.optimized.size` and the comparability of
  logarithms, then take a square root to reach `e.sstar.lower.bound` at the pigeonhole scale;
  monotonicity in the spatial scale removes the pigeonhole scale;
* the quenched estimate, from the deterministic bound at cutoff `R = 2 floor(m/2)` and spatial
  scale `n_0 = floor(m/2)`, the balanced transfer from cutoff `R` to cutoff `L`, and the mixing
  estimate `e.sstarL.quenched.lb` (`l.mixing.minscale`), whose `O_{Gamma_2}` amplitude is
  `3^{-(m-n_0)/4} <= 3^{-m/8}`.

The matrix-valued Orlicz error `O_{Gamma_2}(.) Id` is read as in the paper: in one-sided matrix
inequalities the displayed scalar random variable multiplies `Id`, i.e. a measurable scalar `X`
with `X = O_{Gamma_2}(.)` multiplies the identity in the Loewner order.

## `e.L.vs.nu` is the standing largeness hypothesis

The display `e.L.vs.nu` **is** the standing largeness hypothesis of the proposition: the threshold
on the prescribed scale `m` together with the range condition `L >= m >= L/2`.  It is not a local
arithmetic fact, and carrying it as an input is faithful: the formal statement carries it as the
hypotheses `m <= L`, `L <= 2 * m` (range) and
`C * cStar ^ (-3) * (log(3 + nu^{-1} + cStar^{-1}) ^ 3 *
  log(log(3 + nu^{-1} + cStar^{-1})) + (1 + K) * log(3 + nu^{-1} + K)) <= m`
(largeness), where the binder `K` is the J5 constant `nondegconst`.

Two readings differ from the print.

* The printed `3 + nu^{-1}` in the two iterated logarithms is replaced by
  `3 + nu^{-1} + cStar^{-1}`, so that the absorption step is available for every `cStar > 0`
  (a correction of the printed text; see `ERRATA.md`).
* The range-of-dependence clause is `ShellLawJ1Restriction` (pointwise restriction sigma-fields) in place of
  `ShellLawJ1` (integral-generated local sigma-fields).  `ShellLawJ1Restriction` implies `ShellLawJ1`, so
  the statement is weaker than the one with `ShellLawJ1`.

## What this file contains

* `sigmaBarStarScalar_originCube_le_sigmaBarInfinite_frozen` — the **first conjunct**
  `sigmaBar_{L,*}(cu_m) <= sigmaBar_L` of `e.sstar.lower.bound`, in the exact shape and hypothesis
  list of the printed statement `p.sstar.lower.bound`, with **no residual hypothesis**.  It is
  `Section2.Annealed.sigmaBarStarScalar_originCube_le_sigmaBarInfinite`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The first conjunct of `e.sstar.lower.bound`**,
`sigmaBar_{L,*}(cu_m) <= sigmaBar_L`, in the exact shape and hypothesis list of
the printed statement `p.sstar.lower.bound`: standing data
`0 < nu`, `ShellLawPrefix/J2/J3/J4`, spatial scale `m`, cutoff `L`.  **No residual
hypothesis.**  This is
`Section2.Annealed.sigmaBarStarScalar_originCube_le_sigmaBarInfinite`, restated
with `L` the cutoff and `m` the spatial scale. -/
theorem sigmaBarStarScalar_originCube_le_sigmaBarInfinite_frozen [NeZero d]
    {nu : ℝ} {P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hnu : 0 < nu)
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (L m : ℕ) :
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu L P :=
  SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_originCube_le_sigmaBarInfinite
    hnu L hPrefix hJ2 hJ3 hJ4 m

end

end SuperdiffusionCLT.Section3.Terms
