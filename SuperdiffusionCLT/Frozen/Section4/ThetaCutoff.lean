/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

@[expose] public section

/-- **The renormalized ellipticity ratio `Θ_{L,n}` of the infrared cutoff field on
`cu_n`**, [AK] `e.Theta.n.def`, in the
isotropic reduction of the proof of `t.weaker.P3`, for the law of
the cutoff field `a_L` (`coefficientCutoff nu omega L`) under the shell law `P`.
This is the object that the paper names in the proof of `p.homog.below`
("`Θ_{L,n}` denotes the renormalized ellipticity ratio from [AK, Theorem 6.1]
for the coefficient field `bfA_L` on `cu_n`"), bounds at scale `0`, and
evaluates as `Θ_{L,m} = a_m b_m`:

`Θ_{L,n} := σ̄_L(cu_n) · σ̄_{L,*}^{-1}(cu_n)`.

Readings.

* **The printed definition.** [AK] defines, for each `n ∈ ℕ`,
  `Θ_n := min_{h ∈ ℝ^{d×d}_skew} |(shom_*^{-1/2} bhom_h shom_*^{-1/2})(cu_n)|`,
  with `bhom_h = shom + (khom - h)^t shom_*^{-1} (khom - h)`
  (the pattern of `e.Theta`), where `shom_*`,
  `khom`, `shom`, `bhom` are read off from `bfAhom(U) = E[bfA(U)]` by
  `e.meet.the.homs`.
* **The isotropic reduction.** Under (P4), `khom(cu_n) = 0` and `shom(cu_n)`,
  `shom_*(cu_n)` are scalar multiples of `Id`. Then
  `h^t shom_*^{-1} h ⪰ 0` for every skew `h`, so the minimum is attained at `h = 0`
  and `Θ_n = |(shom_*^{-1/2} shom shom_*^{-1/2})(cu_n)|`; with
  `shom = σ̄ Id` and `shom_*^{-1} = σ̄_*^{-1} Id`, `σ̄, σ̄_*^{-1} > 0`, the operator
  norm is the real number `σ̄ · σ̄_*^{-1}`. The definition below is that value.
* **The carriers are exactly these objects.** In
  `Section2/Annealed/Blocks.lean`, `sigmaBarStarInv` is the lower-right block of
  `annealedBlockMatrix` (`E[s_*^{-1}]`, first line of `e.meet.the.homs`),
  `kappaBar = sigmaBarStar * sigmaBarStarInvKappaMean` (second line), and
  `sigmaBar = bBar - kappaBar^t sigmaBarStarInv kappaBar` (third line);
  `sigmaBarSeq` and `sigmaBarStarInvSeq` are their `(0,0)` entries on
  `cubeSet (originCube d n)`.
* **Where the reduction is proved (not assumed here).** Under
  `0 < nu` and `ShellLawJ4` (which gives (P4) of [AK] for the cutoff law):
  `sigmaBarStarInvKappaMean_originCube_eq_zero`, `sigmaBar_originCube_eq_smul_one` and
  `sigmaBarStarInv_originCube_eq_smul_one` (`Section2/Annealed/Symmetry.lean`);
  positivity `sigmaBarSeq_pos`, `sigmaBarStarInvSeq_pos`
  (`Section2/Annealed/InfiniteVolume.lean`, under the prefix and J2--J4). The
  general min-over-skew formula is not formalized: every consumer (the statements
  `t.weaker.P3` and `p.homog.below`) carries `ShellLawJ4`, where the two agree.
* **Product, not quotient.** The lower-right annealed block `E[s_*^{-1}]` is the
  primitive object (`sigmaBarStar` is defined as its inverse), so the ratio is
  the product with `sigmaBarStarInvSeq`, the `a_m b_m` of the paper,
  rather than a division by the derived `sigmaBarStarScalar`.
* **Scale index `n : ℕ`** (every printed use,
  including `Θ_0`, is at a natural scale).
* **No hypothesis.** A literal, total definition with no side condition. -/
noncomputable def SuperdiffusionCLT.Frozen.Section4.thetaCutoff
    {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure
      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (n : ℕ) : ℝ :=
  SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n *
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n
