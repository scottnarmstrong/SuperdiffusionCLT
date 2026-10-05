/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssembly
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-- **Proposition `p.mixing.P.three.prime`** (Mixing below the infrared cutoff), Section 4.

The statement carries the gap binder
`n ≤ m - ⌈C log(ν⁻¹n)⌉`, directly after `⌈C log(ν⁻¹L)⌉ ≤ n`. When `n ≤ L` it
follows from `n ≤ m - ⌈C log(ν⁻¹L)⌉` (so nothing changes there, including all of
the first clause, whose guard forces `n ≤ L`); when `n > L` the large-gap
clause without this binder would demand a quenched single-cube homogenization rate for the
cutoff field above scale `L` that the paper proves only through
`p.homog.below`, which consumes this statement. The reading of the paper: the third
condition of `e.mixing.gaps` with `log(ν⁻¹(L∨n))`, and the large-gap display
with `3^{-(d/2)(m-L∨n)}`.

> There exists a constant `C(d) < ∞` such that, for every `m,n ∈ ℕ` and
> `L ∈ ℕ` with `L ≥ 1` satisfying (`e.mixing.gaps`)
> `L - n ≤ C^{-1} shom_{L,*}^2(cu_n)`, `m < 2n`,
> `n ≤ m - ⌈C log(ν^{-1}L)⌉`, `n ≥ ⌈C log(ν^{-1}L)⌉`,
> we have, guarded by `m ≤ L + C log(ν^{-1}L)` (`e.main.mixing.estimate`),
> `|bfAhom_L^{-1/2}(cu_n) avsum_{z∈3^nℤ^d∩cu_m}(bfA_L(z+cu_n)-bfAhom_L(cu_n)) bfAhom_L^{-1/2}(cu_n)|`
> `≤ O_{Γ2}(C(L-n)_+^{1/2}shom_{L,*}^{-1}(cu_n)) + O_{Γ1}(C(L-n)_+shom_{L,*}^{-2}(cu_n)) + O_{Γ1/3}(Cm^{-3000})`,
> and, guarded oppositely by `m > L + C log(ν^{-1}L)`, the same left side is
> `≤ O_{Γ1}(Cm^{-3000})`.

## Reading choices

* **The `A^{-1/2} H A^{-1/2}` sandwich, sqrt-free.** Following
  the sandwich forms of the formalization, clause (i) — which apply to
  every inverse-square-root sandwich — a printed
  `‖A^{-1/2} H A^{-1/2}‖ ≤ t` with `A ≻ 0` symmetric and `H` a (possibly
  unsymmetric) block is read as the relative bilinear bound
  `2 p·Hq ≤ t (p·Ap + q·Aq)` for every `p, q`. Here `A = bfAhom_L(cu_n)`
  (`annealedBlockMatrix nu L P (cubeSet (originCube d n))`, the *same*
  matrix on both sides, so the case `A = B`) and `H` is the
  (`z`-averaged) block difference `bfA_L(z+cu_n) - bfAhom_L(cu_n)`. This
  avoids constructing any new matrix square root and is the
  standing convention for exactly this shape, as in the statement of
  `e.refined.localization.twoo` (same "sum of
  Orlicz terms" idiom reused below).
* **The average, real-valued.** `BlockMat d`
  has no `Sub`/averaging structure, so (as in
  `l.localization.average`) the block *difference* inside one cube is formed
  through `ofFullBlockMat (toFullBlockMat · - toFullBlockMat ·)`, and the
  lattice average `avsum_{z∈3^nℤ^d∩cu_m}` of the whole sandwiched quadratic
  form is realized directly as the real-number average `(card)⁻¹ • ∑` over
  `Homogenization.descendantsAtDepth (originCube d m) (m-n)` (the aligned
  lattice `3^nℤ^d ∩ cu_m`, exactly as in that statement); linearity of
  `blockVecDot`/`blockMatVecMul` in the matrix argument makes "bilinear form
  of the averaged matrix" and "average of the bilinear forms" the same real
  number, so no `BlockMat`-valued average object is needed.
* **The sum of three (resp. one) Orlicz terms**, as in
  `e.refined.localization.twoo`: independent measurable witnesses `X1, X2,
  X3` (one per summand, its own index `Γ_σ` and its own amplitude), the
  bound asserted at the coefficient `X1 + X2 + X3`. This is the literal
  reading of a sum of `O` terms, not a bound by their max or a single
  witness of a blended index.
* **The two indicator-guarded displays are implications**, not a literal
  indicator function multiplying an unconditional bound: `m ≤ L + C
  log(ν^{-1}L) → (3-term bound)` and `L + C log(ν^{-1}L) < m → (1-term
  bound)`. When a guard's hypothesis fails, the printed inequality
  `|·| · 0 ≤ (nonnegative RHS)` carries no information, exactly matching an
  implication with a false antecedent; when the hypothesis holds, the two
  readings coincide with the real inequality. Neither guard's threshold
  needs a `≤`/`<` split beyond a case split at the same point the print
  itself uses (`≤` in the first indicator, `>` in the second — jointly
  exhaustive and disjoint, so no scale `m` is doubly or never covered).
* **`(L-n)_+`, `(L-n)_+^{1/2}`.** Cast from the `ℕ`-truncated subtraction
  `((L - n : ℕ) : ℝ)`, which equals `max 0 ((L:ℝ) - (n:ℝ))` unconditionally
  for `L, n : ℕ` — the standing convention of the formalization.
* **`shom_{L,*}^{-1}(cu_n)`, `shom_{L,*}^{-2}(cu_n)`.** Written as negative
  `Real.rpow` powers of the positive scalar `sigmaBarStarScalar nu L P
  (cubeSet (originCube d n))` directly, rather than through a separately
  named inverse carrier, matching the `cStar ^ (-(3:ℝ))`-style
  convention and avoiding an extra import.
* **`⌈C log(ν^{-1}L)⌉`** is `Int.ceil`, as in the statement of the stream
  increment scale estimates (`⌈A * Real.log (B * (m:ℝ))⌉`; there too a real ceiling
  compared against a cast `ℕ` via `ℤ`), not
  `Nat.ceil`: the surrounding inequalities (`n ≤ m - ⌈·⌉`, `n ≥ ⌈·⌉`) are
  read in `ℤ`, so that `n ≤ m - ⌈·⌉` is never distorted by `ℕ`-truncation
  when the ceiling exceeds `m`.
* **The J-binders.** `a.multiscale.stream` is carried by the prefix and
  `J1`-`J4` (`ShellLawJ1Restriction` for the restriction lane); `c⋆`/`nondegconst`/`J5` occur in
  neither the printed statement nor its printed proof for this proposition, so they are absent.
* **Hypothesis discipline.** Only the printed ranges (`L ≥ 1`, `e.mixing.
  gaps`) and the standing shell laws are hypotheses; no side condition from
  the proof (`m_3`, the AK.HC parameter translation, `K(d)`, etc.) is
  carried. -/
theorem SuperdiffusionCLT.Frozen.Section4.mixing_below_cutoff (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m n L : ℕ, 1 ≤ L →
            (L : ℝ) - (n : ℝ) ≤
              C⁻¹ *
                (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                  (2 : ℝ) →
            m < 2 * n →
            (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ →
            ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ ≤ (n : ℤ) →
            (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ →
            ((m : ℝ) ≤ (L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) →
              ∃ X1 X2 X3 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X1
                    (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                        (-(1 : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X2
                    (C * ((L - n : ℕ) : ℝ) *
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                        (-(2 : ℝ))) ∧
                Measurable X3 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X3
                    (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.BlockVec d),
                    2 *
                        (((Homogenization.descendantsAtDepth
                                (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ Homogenization.descendantsAtDepth
                              (Homogenization.originCube d (m : ℤ)) (m - n),
                            Homogenization.blockVecDot p
                              (Homogenization.blockMatVecMul
                                (Homogenization.ofFullBlockMat
                                  (Homogenization.toFullBlockMat
                                      (Homogenization.coarseBlockMatrix
                                        (Homogenization.cubeSet R)
                                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                            nu omega L).toCoeffField) -
                                    Homogenization.toFullBlockMat
                                      (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                        nu L P
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (n : ℤ))))))
                                q)) ≤
                      (X1 omega + X2 omega + X3 omega) *
                        (Homogenization.blockVecDot p
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              p) +
                          Homogenization.blockVecDot q
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              q))) ∧
            ((L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) < (m : ℝ) →
              ∃ X4 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X4 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X4
                    (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.BlockVec d),
                    2 *
                        (((Homogenization.descendantsAtDepth
                                (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ Homogenization.descendantsAtDepth
                              (Homogenization.originCube d (m : ℤ)) (m - n),
                            Homogenization.blockVecDot p
                              (Homogenization.blockMatVecMul
                                (Homogenization.ofFullBlockMat
                                  (Homogenization.toFullBlockMat
                                      (Homogenization.coarseBlockMatrix
                                        (Homogenization.cubeSet R)
                                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                            nu omega L).toCoeffField) -
                                    Homogenization.toFullBlockMat
                                      (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                        nu L P
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (n : ℤ))))))
                                q)) ≤
                      X4 omega *
                        (Homogenization.blockVecDot p
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              p) +
                          Homogenization.blockVecDot q
                            (Homogenization.blockMatVecMul
                              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                              q)))
    := by
  exact SuperdiffusionCLT.Section4.Mixing.mixMain_main_closed d hd
