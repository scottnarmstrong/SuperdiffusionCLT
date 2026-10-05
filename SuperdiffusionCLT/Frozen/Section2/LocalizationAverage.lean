/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Section2.Localization.LocalizationAveragePrintedClose
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction

@[expose] public section

/-- **Lemma `l.localization.average` (Averaged gauged comparison)**,
under the standing molecular-diffusivity range `nu ∈ (0,1]` and the standing
multiscale stream assumption `a.multiscale.stream` of the paper.

There is `C(d) < ∞` such that, for every `m, n, ℓ, L ∈ ℕ` with `n ≤ ℓ ≤ m` and
`L ≥ ℓ`, writing `h_z := (k_L - k_ℓ)_{z+cu_n}` for `z ∈ 3^n ℤ^d ∩ cu_m`, one has
for every `P ∈ ℝ^{2d}` the estimate `e.localization.average.oneshot`

`| ⨍_{z ∈ 3^n ℤ^d ∩ cu_m} P·(bfA_L(z+cu_n) - G_{-h_z}^t bfAhom_ℓ(cu_n) G_{-h_z}) P |
 ≤ O_{Γ_{1/3}}( C ν^{-3} |P|² ( 1_{L>ℓ} L 3^{-(ℓ-n)}
     + (1∨ℓ)(1∨L)(1∨(m-n)) 3^{-(d/2)(m-ℓ)} ) )`.

Readings this text fixes.

* **The lattice average.** The printed sum runs over `3^n ℤ^d ∩ cu_m`, the centres of the scale-`n`
  triadic cubes tiling `cu_m`; since `3^{m-n}` is odd no lattice point meets the boundary of `cu_m`,
  so the open and half-open cubes carry the same lattice and the index set is unambiguous. It is
  realized as `Homogenization.descendantsAtDepth (originCube d m) (m - n)`, a `Finset` of
  cardinality `(3^d)^{m-n} > 0`, and `⨍` is `(card)⁻¹ • ∑`. The cubes `z + cu_n` are their half-open
  realizations `cubeSet R`, which differ from the open cubes by a Lebesgue-null set.
* **The gauge.** `G_h` is the triangular gauge `blockG` of `e.G`,
  and `h_z = (k_L - k_ℓ)_{z+cu_n}` is inlined as the volume average of the
  finite shell increment on `cubeSet R`; `BlockMat d` carries no `Sub`
  instance, so the printed matrix difference is written through
  `ofFullBlockMat (toFullBlockMat · - toFullBlockMat ·)`, as in
  `l.localization.A`.
* **The annealed matrix.** `bfAhom_ℓ(cu_n)` is `E[bfA_ℓ(cu_n)]`
  (`e.homs.defs.U.0`), namely `annealedBlockMatrix`; the
  vanishing of its off-diagonal block is a consequence of `a.j.iso` and is not
  assumed here.
* **The constant.** It is printed after the display ("for a constant
  `C(d) < ∞`"), and its argument list `C(d)` forces the uniform reading: `C` is
  bound outermost, before `nu`, the law, the scales and `P`. All consumers
  in the paper need it uniform in the scales.
* **The Orlicz witness.** The print bounds an absolute value by an
  `O_{Γ_{1/3}}` quantity; the statement binds a measurable witness `X` with
  `X = O_{Γ_{1/3}}(·)` and asserts the pointwise bound by `X`, with
  `Measurable X` as the first conjunct, the usual form of such statements.
* **The J-binders.** `a.multiscale.stream` is carried by the prefix and
  `J1`--`J4`, the range-of-dependence assumption being the restriction version
  `ShellLawJ1Restriction`. `J5`,
  `c⋆` and the nondegeneracy constant occur neither in the printed lemma nor in
  its printed proof, so they are absent. -/
theorem SuperdiffusionCLT.Frozen.Section2.localization_average
    (d : ℕ) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m n l L : ℕ, n ≤ l → l ≤ m → l ≤ L →
            ∀ Pvec : Homogenization.BlockVec d,
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X
                    (C * nu ^ (-(3 : ℝ)) *
                      Homogenization.blockVecDot Pvec Pvec *
                      ((if l < L then
                            (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))
                          else 0) +
                        max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
                          (3 : ℝ) ^
                            (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))))) ∧
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    |((Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (m : ℤ))
                            (m - n)).card : ℝ)⁻¹ *
                        ∑ R ∈ Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (m : ℤ)) (m - n),
                          Homogenization.blockVecDot Pvec
                            (Homogenization.blockMatVecMul
                              (Homogenization.ofFullBlockMat
                                (Homogenization.toFullBlockMat
                                    (Homogenization.coarseBlockMatrix
                                      (Homogenization.cubeSet R)
                                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                          nu omega L).toCoeffField) -
                                  Homogenization.toFullBlockMat
                                    (Homogenization.Book.Ch02.blockMatMul
                                      (Homogenization.Book.Ch02.blockMatTranspose
                                        (Homogenization.Book.Ch02.blockG
                                          (-Homogenization.volumeAverageMat
                                            (Homogenization.cubeSet R)
                                            (fun y =>
                                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                                omega l L y))))
                                      (Homogenization.Book.Ch02.blockMatMul
                                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                          nu l P
                                          (Homogenization.cubeSet
                                            (Homogenization.originCube d (n : ℤ))))
                                        (Homogenization.Book.Ch02.blockG
                                          (-Homogenization.volumeAverageMat
                                            (Homogenization.cubeSet R)
                                            (fun y =>
                                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                                omega l L y)))))))
                              Pvec)| ≤
                      X omega
    := by
  exact SuperdiffusionCLT.Section2.Localization.localization_average_of_printedT2 d
