/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Section2.Estimates.Stream.StreamIncrementScaleEstimatesBridge

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-- **Estimates on `k_m - k_n`** (`l.ellip.k.scales.estimates`).

The readings this statement fixes are recorded here.

* **The matrix norm.** `open scoped Matrix.Norms.L2Operator` supplies the
  only `NormedAddCommGroup (Mat d)` instance in scope, whose norm is the
  CoarseGraining library's `Homogenization.Book.Ch02.matrixOperatorNorm`; without the scoped open
  the statement does not elaborate at all, so the size used by `cubeLpENorm`,
  `cubeHsENorm` and the Gagliardo seminorm cannot silently change.
* **The pairing.** `matHatNegENorm` pairs against the rank-one gradient class `p ⊗ ∇g`:
  the density is `fderiv ℝ g x (v ᵥ* M x)`,
  that is `∇g(x) · (M(x)ᵀ v)`. The supremum runs over
  `|v| ≤ 1` and over smooth potentials `g` with `(g)_Q = 0` whose gradient
  field `∇g` has normalized full `W̲^{s,p'}(Q)` norm at most one, and the
  `Ĥ^{-s}` of the third "Moreover" term is the volume-normalized order-`s`
  hatted negative norm `matHatNegENorm` as well. The constraint is on the field `∇g`,
  not on the potential `g`. Every field this
  statement quantifies over is skew — `ShellField` stores
  `p x i j = -p x j i`, and `finiteShellIncrement` and `centeredStreamField`
  inherit it — so `Mᵀ = -M`, and since the index set `{v : |v| ≤ 1}` is
  symmetric under `v ↦ -v` the supremum coincides with the paper's own
  contraction `⨍ ∇w · (M p)`.
* **The cube realization.** One convention per object:
  `Homogenization.openCubeSet` wherever a pointwise supremum of a continuous
  field is taken (the shell derivative norms `shellDerivLinftyNorm`, in the
  derivative tail and in the summability guard), and `Homogenization.cubeSet`
  for volume averages and for the domains of the matrix norms (the centring
  domain of `centeredStreamField`, `volumeAverageMat`, and the membership test
  `cubeCenter Q ∈ cubeSet cu_m`). The two differ by
  a Lebesgue-null set, so no norm is affected; the membership test at scale `n`
  is the half-open one.
* **The `H̲^s` norm.** The printed two-piece bound is a definitional identity of
  `cubeHsENorm`; the lemma `cubeHsENorm_le_add` is the direction used where the
  shells are summed.
* **The "Moreover" block.** `centeredStreamField` is a `tsum`, equal
  to `0` off its summability event, so the block is quantified almost surely
  and stated under the guard that on every natural cube the series of shell
  derivative norms converges. That guard is exactly the event which
  `Section2.Cutoff.eventually_summable_shellDerivLinftyNorm` derives from J3
  (the remark following `l.cutoff.approximation`),
  a countable intersection of full-measure events; on it the series defining
  `k - (k)_{cu_m}` converges at every point of every cube and at every
  `x ∈ ℝ^d`, so no clause of the block can be discharged by the `tsum` junk
  value. This is the paper's own reading: its `k` is the almost surely defined
  field of `e.good.k`.
* **`K_σ ≥ 27`** is the paper's own construction (`e.mathcal.K.int`); it is
  conclusion-side and cannot smuggle a premise.
* **Range of `p`.** The exponent range is `1 < p`: at `p = 1` the test class of
  the hatted negative norm is unconstrained at the conjugate exponent `∞`, so
  that norm is `⊤` and the clause is false; the paper uses the clause only for
  `1 < p < ∞`.
* **The Gagliardo supremum.** It runs over the infinitely many `M > n` and is
  read almost surely: its pathwise form is refuted by a constant shell sequence,
  for which the seminorm of `k_M - k_n` equals `M - n` times a fixed nonzero
  seminorm.
* **The third term of the "Moreover" block** is the volume-normalized
  `matHatNegENorm` (the `Ŵ̲^{-s,2}` of `e.apply.multiscale.Poincare`, which
  carries no volume factor), not its un-normalized counterpart: in the
  un-normalized carrier the pairing of an order-one field against a normalized
  test gradient is of size `3^{dm/2}`, so the term
  `3^{-sm}[k - (k)_{cu_m}]_{Ĥ^{-s}(cu_m)}` would grow like `3^{dm/2}` and no
  random scale could make it `≤ δ m^σ`.
* **The J-binder.** The restriction version of the range-of-dependence
  assumption (`ShellLawJ1Restriction`) is bound, which the concentration step of the
  `L^p` clause consumes.
* **The amplitude of `log K_σ`.** The `Γ_{2σ}` tail of `log K_σ` has amplitude
  `C₀ · (C₁ δ⁻¹ √(σ⁻¹ log(e + C₂ δ⁻¹ σ⁻¹)))^{1/σ}`, with a free constant `C₀`
  **outside** the `1/σ` power, quantified together with `C₁` after `s`, and the
  logarithm regularized so that its argument is at least `e`. This differs from
  the printed `C₁(C₂δ⁻¹σ⁻¹)^{1/σ}`. The union bound over the bad scales is
  saturated when they are disjoint, which the hypotheses permit, and then forces a
  `√log(1/δ)` factor that no constants in `d, s` alone can absorb; and the free
  constant must sit outside the `1/σ` power, since otherwise the whole amplitude
  tends to `1` as `σ → ∞`, while the floor `K_σ ≥ 27` forces
  `log K_σ ≥ log 27` and hence an amplitude at least `3 log 3`; moreover whenever
  `|C₂δ⁻¹σ⁻¹| ≤ 1` the logarithm of the unregularized shape is nonpositive and the
  amplitude would be exactly `0`, which no probability law admits.
  This shape dominates the amplitude `2(log 3)(4 + (2Aδ⁻¹√Θ)^{1/σ})` of the
  geometric summation, with `Θ = 3 + σ⁻¹ + (3/(2σ)) max(0, log(6A²δ⁻²σ⁻¹))` and
  `A` the uniform `Γ₂` amplitude of the envelope family `X_m`. -/
theorem SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates
    (d : ℕ) :
    ∃ C₂ : ℝ,
      ∀ s : ℝ, 0 < s → s < 1 →
        ∃ C₀ C₁ : ℝ,
          ∀ p : ℝ, 1 < p →
            ∃ C : ℝ,
              ∀ P : MeasureTheory.ProbabilityMeasure
                  (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                (∀ l m n : ℕ, n < m → m ≤ l →
                    (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable X ∧
                        Homogenization.IndependentSums.IsBigO P.toMeasure
                          (Homogenization.IndependentSums.gammaSigma 2) X
                          (C * (3 : ℝ) ^ (s * (m : ℝ))) ∧
                        ∀ omega,
                          SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                              (Homogenization.originCube d (l : ℤ)) s
                              (ENNReal.ofReal p)
                              (fun x =>
                                SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                  omega n m x) ≤
                            ENNReal.ofReal (X omega)) ∧
                      (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧
                          Homogenization.IndependentSums.IsBigO P.toMeasure
                            (Homogenization.IndependentSums.gammaSigma 2) X
                            (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                              (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
                          ∀ omega,
                            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                (Homogenization.originCube d (l : ℤ))
                                (ENNReal.ofReal p)
                                (fun x =>
                                  SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                    omega n m x) ≤
                              ENNReal.ofReal
                                (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) ∧
                      (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧
                          Homogenization.IndependentSums.IsBigO P.toMeasure
                            (Homogenization.IndependentSums.gammaSigma 2) X
                            (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                              ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
                          ∀ omega,
                            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                (Homogenization.originCube d (l : ℤ)) ∞
                                (fun x =>
                                  SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                    omega n m x) ≤
                              ENNReal.ofReal (X omega)) ∧
                      (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧
                          Homogenization.IndependentSums.IsBigO P.toMeasure
                            (Homogenization.IndependentSums.gammaSigma 2) X
                            (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                          ∀ omega,
                            SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                                (Homogenization.originCube d (l : ℤ)) s
                                (fun x =>
                                  SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                    omega n m x) ≤
                              ENNReal.ofReal (X omega))) ∧
                  (∀ l n : ℕ,
                      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧
                          Homogenization.IndependentSums.IsBigO P.toMeasure
                            (Homogenization.IndependentSums.gammaSigma 2) X
                            (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                          ∀ᵐ omega ∂P.toMeasure,
                            (⨆ M : {M : ℕ // n < M},
                              SuperdiffusionCLT.Section2.Norms.cubeEuclideanGagliardoESeminorm
                                (Homogenization.originCube d (l : ℤ)) s 2
                                (fun x =>
                                  SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                    omega n M.1 x)) ≤
                              ENNReal.ofReal (X omega)) ∧
                  (∀ delta : ℝ, 0 < delta → delta < 1 →
                      ∀ sigma : ℝ, 0 < sigma →
                        ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                          Measurable Kfun ∧
                            (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
                            Homogenization.IndependentSums.IsBigO P.toMeasure
                              (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                              (fun omega => Real.log (Kfun omega))
                              (C₀ *
                                (C₁ * delta⁻¹ *
                                    Real.sqrt (sigma⁻¹ *
                                      Real.log (Real.exp 1 + C₂ * delta⁻¹ * sigma⁻¹))) ^
                                  sigma⁻¹) ∧
                            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                                ∂P.toMeasure,
                              (∀ i : ℕ,
                                  Summable fun k : ℕ =>
                                    SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                      (Homogenization.openCubeSet
                                        (Homogenization.originCube d (i : ℤ)))
                                      (omega k)) →
                                ((∀ m : ℕ,
                                    Kfun omega ≤ (3 : ℝ) ^ m →
                                (ENNReal.ofReal ((m : ℝ)⁻¹) *
                                      SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                        (Homogenization.originCube d (m : ℤ)) ∞
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                          omega
                                          (Homogenization.cubeSet
                                            (Homogenization.originCube d (m : ℤ)))) +
                                    ENNReal.ofReal ((3 : ℝ) ^ m) *
                                      (∑' k : ℕ,
                                        ENNReal.ofReal
                                          (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                            (Homogenization.openCubeSet
                                              (Homogenization.originCube d (m : ℤ)))
                                            (omega (m + 1 + k)))) +
                                    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                                      SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                        (Homogenization.originCube d (m : ℤ)) s 2
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                          omega
                                          (Homogenization.cubeSet
                                            (Homogenization.originCube d (m : ℤ)))) ≤
                                  ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                                  ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                                    ∀ n : ℕ,
                                      (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                                        n ≤ m →
                                          ∀ Q : Homogenization.TriadicCube d,
                                            Q.scale = (n : ℤ) →
                                              Homogenization.cubeCenter Q ∈
                                                  Homogenization.cubeSet
                                                    (Homogenization.originCube d (m : ℤ)) →
                                                Homogenization.Book.Ch02.matrixOperatorNorm
                                                    (Homogenization.volumeAverageMat
                                                      (Homogenization.cubeSet Q)
                                                      (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                                        omega
                                                        (Homogenization.cubeSet
                                                          (Homogenization.originCube d (m : ℤ))))) ≤
                                                  A * Real.log (B * (m : ℝ)) * delta *
                                                    (m : ℝ) ^ sigma) ∧
                                  ∀ x : Homogenization.Vec d,
                              Homogenization.Book.Ch02.matrixOperatorNorm
                                    (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                        omega
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (0 : ℤ))) x -
                                      SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                        omega
                                        (Homogenization.cubeSet
                                          (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                                C *
                                  Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                                    (2 * (1 + sigma)))) 
    :=
  SuperdiffusionCLT.Section2.Estimates.Stream.streamIncrement_scale_estimates_of_clauses d
    (SuperdiffusionCLT.Section2.Estimates.Stream.lpClause_input d)
