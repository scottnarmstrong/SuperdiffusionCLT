/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.BfAmEllipticityRegimeSplit
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm
public import SuperdiffusionCLT.Section2.Carriers.AnnealedBlockInfinite
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction

@[expose] public section

/-- **Lemma `l.bfAm.ellip` (Ellipticity bounds for `bfA_m`)**, under the standing
molecular-diffusivity range `nu ∈ (0,1]` and the standing multiscale stream assumption
`a.multiscale.stream` of the paper.

There is `C(d)` such that, for every `m ∈ ℕ`:

* `e.Enaught.vs.A.and.Ahom`: for every bounded domain `U`,
  `|bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}| ≤ O_{Γ₁}(1)`;
* for every `n ∈ ℕ`,
  `bfE_m^{-1/2} bfAhom_m bfE_m^{-1/2} ≤ bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2}
  ≤ I_{2d}`;
* `e.Smgamma.integ` and `e.bfAm.ellip`: for every
  `γ ∈ (0,1)` there is a random minimal scale `S_{m,γ}` with
  `S_{m,γ} = O_{Γ_γ}(C exp(C |log γ| / γ) 3^m)` such that, for every `n ∈ ℕ`,
  `3^n ≥ S_{m,γ}` implies
  `3^{-γ(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≤ 2 I_{2d}` for every
  `l ∈ ℤ ∩ (-∞, n]` and every `z ∈ 3^l ℤ^d ∩ cu_n`.

Readings this text fixes.

* **The envelope and its constant.** `bfE_m` of `e.Enaught.mixing` is
  `SuperdiffusionCLT.Section2.Annealed.envelopeBlockMat`, and
  the normalization `bfE_m^{-1/2} · bfE_m^{-1/2}` is
  `envelopeRescale`; the printed constant `C_{(e.km.Ltwo.size)}` is read as
  `SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d` (the printed
  constant enlarged by the `Γ₁` moment constant and truncated below at `1`).
* **The domain.** `Homogenization.Book.Ch02.Domain d` (bounded open convex)
  where the paper prints a bounded Lipschitz domain; the triadic sub-cubes `z + cu_l` are
  the exact members of `Homogenization.TriadicCube d` with `l = Q.scale ≤ n`
  and `z = cubeCenter Q ∈ cu_n`, so the printed index set `l ∈ ℤ ∩ (-∞, n]`,
  `z ∈ 3^l ℤ^d ∩ cu_n` is quantified literally, including negative `l`.
* **The first assertion.** The printed `|·| ≤ O_{Γ₁}(1)` is stated directly on
  the nonnegative random variable `blockMatrixOperatorNorm (envelopeRescale …)`
  through `IsBigOWith` at amplitude `1`, with no witness variable: for a
  nonnegative quantity the upper-tail relation is the printed relation, and a
  witness `X` with `|·| ≤ X` and `X = O_{Γ₁}(1)` exists exactly when this holds.
* **bfAhom_m (`e.homs.defs`).**
  `SuperdiffusionCLT.Section2.Carriers.annealedBlockMatInfinite`, the
  entrywise infimum over `n` of `bfAhom_m(cu_n)`; the printed sequence is
  nonincreasing, so the infimum is the printed limit wherever the
  print's own presupposition holds, and it is total and choice-free elsewhere.
* **The J-binders.** `a.multiscale.stream` is carried by the prefix and
  `J1`--`J4`; the range-of-dependence assumption is the restriction version
  `ShellLawJ1Restriction`. `J5`,
  `c⋆` and the nondegeneracy constant occur neither in the printed lemma nor in
  its printed proof, so they are absent.

The sub-cube clause of
the third assertion is quantified almost surely in the sample, as the printed
random scale is almost surely finite; the print's pathwise phrasing is read with
the standing "almost surely" convention.

The statement assumes `[NeZero d]` and `hd : 2 <= d`, as the paper treats `d ≥ 2`
throughout (Theorem A is stated for all dimensions `d ≥ 2`, and the log-correlated field of
the running example is defined only for `d ≥ 2`). The hypothesis is used at
exactly one place in the proof: the level sum compares `γ k + (d/2) max(K-k, 0)`
with `γ K`, which needs `γ ≤ d/2`, and `γ` ranges over `(0,1)`. -/
theorem SuperdiffusionCLT.Frozen.Section2.envelopeRescale_ellipticity
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m : ℕ,
            (∀ U : Homogenization.Book.Ch02.Domain d,
                Measurable
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                        (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                          (Homogenization.coarseBlockMatrix
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                omega m).toCoeffField))) ∧
                Homogenization.IndependentSums.IsBigOWith P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 1)
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                    SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (Homogenization.coarseBlockMatrix
                          (U : Set (Homogenization.Vec d))
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                              omega m).toCoeffField)))
                  1) ∧
              (∀ n : ℕ,
                  Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Carriers.annealedBlockMatInfinite
                          nu m P))
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ))))) ∧
                    Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ)))))
                      (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (∀ gamma : ℝ, 0 < gamma → gamma < 1 →
                  ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable S ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma gamma) S
                        (C * Real.exp (C * |Real.log gamma| / gamma) *
                          (3 : ℝ) ^ m) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                        ∀ Q : Homogenization.TriadicCube d, Q.scale ≤ (n : ℤ) →
                          Homogenization.cubeCenter Q ∈
                              Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ)) →
                            Homogenization.BlockMatLoewnerLE
                              (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
                                SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                                  (Homogenization.coarseBlockMatrix
                                    (Homogenization.cubeSet Q)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                        omega m).toCoeffField))
                              ((2 : ℝ) • Homogenization.Book.Ch02.blockIdentity d))
    := by
  exact SuperdiffusionCLT.Section2.bfAmEllipticity_of_regimeSplit d hd
