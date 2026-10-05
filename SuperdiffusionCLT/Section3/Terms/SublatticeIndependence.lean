/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparison
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import Homogenization.Sobolev.Fractional.PairCapture
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The sublattice independence rule `hpair`/`hmem`

`SuperdiffusionCLT.Section3.Terms.ConcentrationComparison` proves the printed analytic
comparison at the printed block family.  Two of its hypotheses are the *sublattice independence
rule*: the pairwise independence `hpair` of the block averages and the `L²` membership `hmem` of
the same averages.  This module reads the printed rule, which follows Proposition
`p.concentration` in the paper:

> We often apply Proposition `p.concentration` in the case of sequences
> which have a finite range of dependence.  For instance, we may have random
> variables `{ X_z }_{z ∈ 3^n ℤ^d ∩ cu_m}` for some `m, n ∈ ℕ` with `n < m`,
> which have the property that `X_z` and `X_{z'}` are independent provided that
> the corresponding subcubes do not touch: that is, if `dist(z + cu_n, z' + cu_n)
> ≠ 0`.  In this case, we can simply break into `3^d` many subcollections which
> are independent:
> `∑_{z ∈ 3^n ℤ^d ∩ cu_m} X_z = ∑_{y ∈ 3^n ℤ^d ∩ cu_{n+1}}
> ∑_{z ∈ 3^{n+1} ℤ^d ∩ cu_m} X_{y+z}`;
> applying the concentration inequality to each inner sum, under
> `X_z = O_{Γ_σ}(1)` and `E[X_z] = 0`, gives `O_{Γ_σ}(C_σ 3^{d/2 (m-n-1)})`;
> summing over `y` and the triangle inequality give
> `O_{Γ_σ}(C_σ 3^{d/2 (m-n)})`.

## Main results

* `subcollectionAtDepth` is one printed subcollection: one colour class of
  `ShellField.cubeShellColor` inside the depth-`t` descendants of a parent `R`.
  `indepFun_volumeAverage_coord_of_subcollectionAtDepth` restates `hpair` there and
  discharges it from the lane independence engine
  (`indepFun_volumeAverage_coord_of_laneSeparated`); the engine's separation hypothesis is
  *supplied* by the colouring (`areShellSeparated_cubeSet_of_cubeShellColor_eq`).
* `indepFun_volumeAverage_coord_of_colorClass` is the same statement on a family of triadic cubes
  at one scale and one colour.
* The colouring (period `Nat.sqrt d + 2`) is the size-bounded realisation of the printed step:
  for `d ≥ 5` the literal period-three reading `3^{n+1} ℤ^d` gives index offset `3`, set gap
  `2 · 3^ell < √d · 3^ell`, so it satisfies the printed non-touching condition yet fails the
  engine's separation hypothesis at its own shell.

## Hypotheses

At a printed subcollection, `hpair` rests on the shell laws `ShellLawJ1Restriction`, `ShellLawJ2` and lane
measurability of the block averages; no separation hypothesis remains.  A consumer stating
`hpair` over the whole descendant family must therefore apply it per colour class and sum over
the at most `K^d` classes, with the class count in place of `(3^d)^(m-j-ell)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## `hpair` and `hmem` from the restriction-lane independence engine -/

/-- **`hpair` from the restriction-lane independence engine.**  For a finite
family of pairwise shell-separated blocks whose coordinate block averages are
observables of the joined restriction lanes of their own cubes, the block
averages are pairwise independent.  This is the shape of the hypothesis `hpair`
of the comparison at `Ω = ShellSeq d`, `μ = P.toMeasure`, with the lane
measurability of the averages as the only input beyond the shell laws. -/
theorem indepFun_volumeAverage_coord_of_laneSeparated
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {ell : ℕ} {blocks : Finset (TriadicCube d)}
    (hsep : ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' →
      ShellField.AreShellSeparated ell (cubeSet B) (cubeSet B'))
    {F : ShellSeq d → Vec d → Vec d} (i : Fin d)
    (hlane : ∀ B ∈ blocks, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))) :
    ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' →
      ProbabilityTheory.IndepFun
        (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))
        (fun ω => volumeAverage (cubeSet B') (fun x => F ω x i)) P.toMeasure := by
  classical
  intro B hB B' hB' hne
  have hIndep : ProbabilityTheory.iIndepFun
      (fun (R : {R : TriadicCube d // R ∈ blocks}) (ω : ShellSeq d) =>
        volumeAverage (cubeSet (R : TriadicCube d)) (fun x => F ω x i)) P.toMeasure := by
    refine iIndepFun_of_blockLane_shellRestrictionSigma hJ1 hJ2 ell
      (U := fun R : {R : TriadicCube d // R ∈ blocks} => cubeSet (R : TriadicCube d))
      (fun R => measurableSet_cubeSet (R : TriadicCube d)) ?_ ?_
    · intro R
      exact hlane (R : TriadicCube d) R.2
    · intro R R' hne'
      exact hsep (R : TriadicCube d) R.2 (R' : TriadicCube d) R'.2
        (fun h => hne' (Subtype.ext h))
  exact hIndep.indepFun (i := ⟨B, hB⟩) (j := ⟨B', hB'⟩)
    (fun h => hne (Subtype.ext_iff.mp h))

/-! ## The printed sublattice: one colour class -/

/-- **The printed "break into `3^d` subcollections".**  On a family of triadic
cubes at one scale and one `ShellField.cubeShellColor`, the separation is
supplied by the colouring (`areShellSeparated_cubeSet_of_cubeShellColor_eq`): the
engine returns pairwise independence with no separation hypothesis. -/
theorem indepFun_volumeAverage_coord_of_colorClass [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {ell : ℕ} {blocks : Finset (TriadicCube d)}
    (hscale : ∀ B ∈ blocks, B.scale = (ell : ℤ))
    {c : ShellField.ShellCubeColor d}
    (hcolor : ∀ B ∈ blocks, ShellField.cubeShellColor B = c)
    {F : ShellSeq d → Vec d → Vec d} (i : Fin d)
    (hlane : ∀ B ∈ blocks, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))) :
    ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' →
      ProbabilityTheory.IndepFun
        (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))
        (fun ω => volumeAverage (cubeSet B') (fun x => F ω x i)) P.toMeasure := by
  classical
  refine indepFun_volumeAverage_coord_of_laneSeparated P hJ1 hJ2 ?_ i hlane
  intro B hB B' hB' hne
  exact ShellField.areShellSeparated_cubeSet_of_cubeShellColor_eq
    (hscale B hB) (hscale B' hB') ((hcolor B hB).trans (hcolor B' hB').symm) hne

/-! ## The printed subcollections

The printed rule does *not* assert independence over the whole
block family.  It partitions that family into `3^d` subcollections and asserts
independence only inside each one, with the printed separation condition that
the corresponding subcubes do not touch (a condition on the cubes *as sets*).
The lemmas below restate `hpair` and `hmem` at one such subcollection and
discharge them from the lane engine; the separation input is *supplied* by the
colouring geometry, so it is not a residual. -/

/-- **A printed subcollection of the descendant family.**  The colour class `c`
inside the depth-`t` descendants of `R`.  This is the family of one of the
printed inner sums, whose members share a common triadic-index residue. -/
noncomputable def subcollectionAtDepth (R : TriadicCube d) (t : ℕ)
    (c : ShellField.ShellCubeColor d) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth R t).filter fun B => ShellField.cubeShellColor B = c

theorem mem_subcollectionAtDepth {R : TriadicCube d} {t : ℕ}
    {c : ShellField.ShellCubeColor d} {B : TriadicCube d} :
    B ∈ subcollectionAtDepth R t c ↔
      B ∈ descendantsAtDepth R t ∧ ShellField.cubeShellColor B = c := by
  classical
  simp only [subcollectionAtDepth, Finset.mem_filter]

theorem subcollectionAtDepth_scale {R : TriadicCube d} {t : ℕ}
    {c : ShellField.ShellCubeColor d} {B : TriadicCube d}
    (hB : B ∈ subcollectionAtDepth R t c) :
    B.scale = R.scale - (t : ℤ) :=
  scale_eq_sub_of_mem_descendantsAtDepth (mem_subcollectionAtDepth.mp hB).1

theorem subcollectionAtDepth_color {R : TriadicCube d} {t : ℕ}
    {c : ShellField.ShellCubeColor d} {B : TriadicCube d}
    (hB : B ∈ subcollectionAtDepth R t c) :
    ShellField.cubeShellColor B = c :=
  (mem_subcollectionAtDepth.mp hB).2

/-- **`hpair` at one printed subcollection, discharged from the lane engine.**
On a single colour class of the depth-`t` descendants the coordinate block
averages are pairwise independent with *no separation hypothesis*: distinct
members of one colour class are shell-separated at their own scale.  The hypotheses
are the shell laws `hJ1`, `hJ2` and the lane measurability of the averages. -/
theorem indepFun_volumeAverage_coord_of_subcollectionAtDepth [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {R : TriadicCube d} {t ell : ℕ} {c : ShellField.ShellCubeColor d}
    (hscaleR : R.scale - (t : ℤ) = (ell : ℤ))
    {F : ShellSeq d → Vec d → Vec d} (i : Fin d)
    (hlane : ∀ B ∈ subcollectionAtDepth R t c, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))) :
    ∀ B ∈ subcollectionAtDepth R t c, ∀ B' ∈ subcollectionAtDepth R t c, B ≠ B' →
      ProbabilityTheory.IndepFun
        (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))
        (fun ω => volumeAverage (cubeSet B') (fun x => F ω x i)) P.toMeasure := by
  classical
  refine indepFun_volumeAverage_coord_of_colorClass
    (blocks := subcollectionAtDepth R t c) (c := c) P hJ1 hJ2 ?_ ?_ i hlane
  · intro B hB
    rw [subcollectionAtDepth_scale hB, hscaleR]
  · intro B hB
    exact subcollectionAtDepth_color hB

end

end SuperdiffusionCLT.Section3.Terms
