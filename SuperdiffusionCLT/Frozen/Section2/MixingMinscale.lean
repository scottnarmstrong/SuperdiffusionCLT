/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorFinal
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction

@[expose] public section

/-- **Lemma `l.mixing.minscale`**, under the standing molecular-diffusivity range
`nu ∈ (0,1]` and the standing multiscale stream assumption
`a.multiscale.stream` of the paper, with the matrix-valued Orlicz
convention of the paper (operator norm; in a one-sided matrix inequality
the displayed scalar random variable multiplies `Id`).

There is `C(d) < ∞` such that:

* `e.sstarL.quenched.lb`, for every `h, n, L ∈ ℕ` with `h < n ≤ L`,
  `s_{L,*}^{-1}(cu_n) ≤ σ̄_{L,*}^{-1}(cu_h) + O_{Γ₂}(C ν^{-2} 3^{-(n-h)/4} Id)`;
* `e.refined.localization.twoo`, for every `h, n, ℓ, L ∈ ℕ` with
  `h < n < ℓ < L`,
  `|s_{L,*}^{-1/2}(cu_n) (k_L - k_ℓ)_{cu_n} s_{L,*}^{-1/2}(cu_n)|
   ≤ O_{Γ₂}(C (L-ℓ)^{1/2} σ̄_{L,*}^{-1}(cu_h))
     + O_{Γ₁}(C ν^{-2} (L-ℓ)^{1/2} 3^{-(n-h)/4})`.

Readings this text fixes.

* **The sandwich norm.** The printed
  inverse-square-root norm of `e.refined.localization.twoo` is written
  square-root free: with `A = B = s_{L,*}(cu_n)` positive symmetric and
  `H = (k_L - k_ℓ)_{cu_n}`, `|A^{-1/2} H A^{-1/2}| ≤ t` is the relative
  bilinear bound `2 p·H q ≤ t (p·A p + q·A q)` for all `p, q`; the two are
  equivalent by the substitution `u = A^{1/2}p`, `v = A^{1/2}q`. No sign
  hypothesis on `t` is needed: the printed norm is nonnegative, so a negative
  value falsifies both sides at once.
* **The sum of two Orlicz terms.** The print adds an `O_{Γ₂}` and an `O_{Γ₁}`
  term with different amplitudes, so two measurable witnesses `X₁`, `X₂` are
  bound, each with its own index and amplitude, and the relative bound is
  asserted at the coefficient `X₁ + X₂`. This is the literal reading of a sum
  of two `O` terms.
* **`σ̄_{L,*}^{-1}(cu_h)`, matrix and scalar.** In `e.sstarL.quenched.lb` the
  print writes a matrix inequality whose right side is the matrix
  `σ̄_{L,*}^{-1}(cu_h) = E[s_{L,*}^{-1}(cu_h)]` plus a scalar random variable
  times `Id`, so `sigmaBarStarInv` is used there. In
  `e.refined.localization.twoo` the same symbol multiplies a scalar Orlicz
  amplitude and is read as the scalar of the paper ("by abusing notation
  slightly we allow `shom_{L,*}^{-1}(cu_m)` to also denote a scalar"), the
  `(0,0)` entry `sigmaBarStarInvScalar`, which is what forces the `[NeZero d]`
  binder. The scalar and the operator-norm readings agree through the
  `a.j.iso` scalarization, which is a theorem derivable from the `J4` binder of
  this statement and not a premise of it.
* **The cubes.** `cu_n` and `cu_h` occur only as domains of a coarse or an
  annealed matrix, so they are the half-open `Homogenization.cubeSet`, the
  usual convention; the open and half-open cubes differ by a
  Lebesgue-null set and the cube bridges transfer every coarse and
  annealed identity between them.
* **Scale differences.** `(n - h)` and `(L - ℓ)` are natural-number differences
  cast to `ℝ`; under the printed strict inequalities the truncation never
  fires.
* **The J-binders.** `a.multiscale.stream` is carried by the prefix and
  `J1`--`J4`, the range-of-dependence assumption being the restriction version
  `ShellLawJ1Restriction`. `J5`,
  `c⋆` and the nondegeneracy constant occur neither in the printed lemma nor in
  its printed proof, so they are absent. -/
theorem SuperdiffusionCLT.Frozen.Section2.sigmaStarInv_mixing_minscale
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          (∀ h n L : ℕ, h < n → n ≤ L →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X
                    (C * nu ^ (-(2 : ℝ)) *
                      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    Homogenization.MatLoewnerLE
                      (Homogenization.sigmaStarInvCoarse
                        (Homogenization.cubeSet
                          (Homogenization.originCube d (n : ℤ)))
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                            nu omega L).toCoeffField)
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInv
                          nu L P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (h : ℤ))) +
                        X omega • (1 : Homogenization.Mat d))) ∧
            ∀ h n l L : ℕ, h < n → n < l → l < L →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X1
                    (C * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar
                        nu L P
                        (Homogenization.cubeSet
                          (Homogenization.originCube d (h : ℤ)))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X2
                    (C * nu ^ (-(2 : ℝ)) * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.Vec d),
                    2 * Homogenization.vecDot p
                        (Homogenization.matVecMul
                          (Homogenization.volumeAverageMat
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (n : ℤ)))
                            (fun y =>
                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega l L y))
                          q) ≤
                      (X1 omega + X2 omega) *
                        (Homogenization.vecDot p
                            (Homogenization.matVecMul
                              (Homogenization.sigmaStarCoarse
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega L).toCoeffField) p) +
                          Homogenization.vecDot q
                            (Homogenization.matVecMul
                              (Homogenization.sigmaStarCoarse
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega L).toCoeffField) q))
    := by
  exact SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d
