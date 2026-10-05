/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section4.Ellipticity.Union
public import SuperdiffusionCLT.Section2.BfAmEllipticityRegimeSplit
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-- **Proposition `p.ellipticity.Ptwoprime`** (The renormalized ellipticity
bound), Section 4:

> There exists `C(d) < ∞` such that, for every `γ ∈ (0,1)` and `m,L ∈ ℕ`
> with `L ≥ 1` and `m ≥ (1/4)L`, we have the estimate (`e.ellipticity.
> Ptwoprime`)
> `sup_{k∈ℤ∩(-∞,m]} 3^{γ(k-m)} max_{z∈3^kℤ^d∩cu_m}`
> `|bfAhom_L^{-1/2}(cu_m) bfA_L(z+cu_k) bfAhom_L^{-1/2}(cu_m)|`
> `≤ O_{Γ1}(C γ^{-1} ν^{-2} L)`.

## Reading choices

* **`z + cu_k`, including negative `k`, via `TriadicCube`.** Exactly as
  the third assertion of `BfAmEllipticity` (`e.Smgamma.integ`/
  `e.bfAm.ellip`, "for every `l ∈ ℤ ∩ (-∞, n]` and every
  `z ∈ 3^l ℤ^d ∩ cu_n`"), the index `k ∈ ℤ ∩ (-∞,m]` and the lattice point
  `z ∈ 3^kℤ^d ∩ cu_m` are realized together as a `Homogenization.TriadicCube
  d` binder `Q` with `Q.scale = k` (an arbitrary integer, no lower bound —
  `TriadicCube.scale : ℤ` and `descendantsAtScale`/the cube geometry are
  total for negative scales) and `Homogenization.cubeCenter Q ∈
  Homogenization.cubeSet (Homogenization.originCube d (m:ℤ))` reading
  "`z ∈ cu_m`" (this same convention already reduces `z ∈
  3^kℤ^d ∩ cu_m` to "the cube's own center lies in `cu_m`"); `z + cu_k` itself is
  `Homogenization.cubeSet Q`.
* **The sup/max, as a uniform bound over every applicable `(k,Q)` pair.**
  `sup_k (3^{γ(k-m)} max_z f(k,z)) ≤ B` (for a `B` not depending on `k,z`,
  as here — the `O_{Γ1}` amplitude depends only on `γ,ν,L,d`) is logically
  *equivalent* to "`∀ k, ∀ z, 3^{γ(k-m)} f(k,z) ≤ B`" — not a strengthening:
  `sup S ≤ B ↔ ∀ x ∈ S, x ≤ B` is the defining property of `sup` for a
  bounded-above-by-`B` set, and taking the `max_z` inside a fixed `k` first
  changes nothing since `B` does not depend on `z` either. So the statement
  binds one measurable witness `X` (depending on `γ,m,L` but not on `k,Q`)
  and asserts the bound for every `(k,Q)` pair; this is the literal
  translation, matching the shape of the third assertion of `BfAmEllipticity`
  (`∀ n, S ω ≤ 3^n → ∀ Q, Q.scale ≤ n → cubeCenter Q ∈ cu_n → bound`).
* **The `A^{-1/2} H A^{-1/2}` sandwich, sqrt-free**, per
  the sandwich forms of the formalization, clause (i) (see
  `MixingBelowCutoff` for the same reading): `A = bfAhom_L(cu_m)`
  (`annealedBlockMatrix nu L P (cubeSet
  (originCube d m))`, same matrix both sides), `H = bfA_L(z+cu_k)`
  (`coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).
  toCoeffField`, generally unsymmetric since `z+cu_k` is not the origin
  cube). `‖A^{-1/2}HA^{-1/2}‖ ≤ t` reads as `2p·Hq ≤ t(p·Ap+q·Aq)` for all
  `p,q : BlockVec d`. Combined with the `3^{γ(k-m)}` factor: the printed
  `3^{γ(k-m)}|A^{-1/2}HA^{-1/2}| ≤ X` becomes, for every `p q`,
  `2p·Hq ≤ 3^{-γ(k-m)} X (p·Ap+q·Aq)` (multiplying both sides of the
  sandwich bound by the positive scalar `3^{-γ(k-m)}`).
* **No new matrix square root is constructed** (unlike a naïve reading that
  would need `bfAhom_L(cu_m)^{-1/2}` as an explicit `BlockMat`): the
  sqrt-free sandwich form makes this unnecessary, and no
  supporting `def` is introduced beyond the printed objects.
* **`γ ∈ (0,1)` is the open interval**, matching the print exactly (not
  `[0,1)` or `(0,1]`).
* **The J-binders.** `ShellLawPrefix`, `ShellLawJ1Restriction`, `J2`, `J3`, `J4`:
  `a.multiscale.stream`. `c⋆`/`nondegconst`/`J5` occur in neither the
  printed statement nor its printed proof (the proof's only external input
  is the crude comparison `e.Enaught.vs.Ahom.L.crude`, itself `c⋆`-free), so
  `J5` is absent. -/
theorem SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
            ∀ m L : ℕ, 1 ≤ L → (L : ℝ) ≤ 4 * (m : ℝ) →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X
                    (C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (L : ℝ)) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (k : ℤ), k ≤ (m : ℤ) →
                    ∀ Q : Homogenization.TriadicCube d, Q.scale = k →
                      Homogenization.cubeCenter Q ∈
                          Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                        ∀ p q : Homogenization.BlockVec d,
                          2 *
                              Homogenization.blockVecDot p
                                (Homogenization.blockMatVecMul
                                  (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                        omega L).toCoeffField)
                                  q) ≤
                            (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega *
                              (Homogenization.blockVecDot p
                                  (Homogenization.blockMatVecMul
                                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                      nu L P
                                      (Homogenization.cubeSet
                                        (Homogenization.originCube d (m : ℤ))))
                                    p) +
                                Homogenization.blockVecDot q
                                  (Homogenization.blockMatVecMul
                                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                      nu L P
                                      (Homogenization.cubeSet
                                        (Homogenization.originCube d (m : ℤ))))
                                    q))
    := by
  exact SuperdiffusionCLT.Section4.Ellipticity.ellipBelow_main d hd
