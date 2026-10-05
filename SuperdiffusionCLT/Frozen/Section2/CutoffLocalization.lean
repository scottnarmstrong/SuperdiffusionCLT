/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02.Setup
public import SuperdiffusionCLT.Section2.Localization.LocalizationUnconditional
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable
public import SuperdiffusionCLT.Section2.Cutoff.Finite
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4

@[expose] public section

/-- **Lemma `l.localization` (Localization)**, under the standing molecular-diffusivity
range `nu ∈ (0,1]` and the standing multiscale stream assumption `a.multiscale.stream`
of the paper.

There is `C(d) < ∞` such that for every `m, n, L ∈ ℕ` with `n ≤ m ≤ L` and
every Lipschitz domain `U ⊆ cu_n`:

* `e.localization.s.star` :
  `|s_L^{-1/2}(U) s_m(U) s_L^{-1/2}(U) - Id| +
   |s_{m,*}^{1/2}(U) s_{L,*}^{-1}(U) s_{m,*}^{1/2}(U) - Id|
   ≤ O_{Γ₁}(C ν^{-2} 3^{-(m-n)})`;
* `e.skbounds` :
  `|s_{L,*}^{-1/2}(U)(kcg_L(U) - kcg_m(U) - (k_L - k_m)_U) s_L^{-1/2}(U)|
   ≤ O_{Γ₁}(C ν^{-2} 3^{-(m-n)/2})`;
* `e.localization.minimizers`, for every `p, q ∈ ℝ^d` :
  `‖∇v(·,U,p,q; a_L - (k_L-k_m)_U) - ∇v(·,U,p,q; a_m)‖²_{L̲²(U)}
   ≤ C ν^{-2} 3^n ‖∇(k_m - k_L)‖_{L^∞(cu_n)}
     (J(U,p,q; a_L-(k_L-k_m)_U) + J(U,p,q; a_m) + 2 p·q)`.

Readings this text fixes.

* **The symmetric sandwich.** Each summand of `e.localization.s.star` is written
  square-root free as a two-sided Loewner comparison: for `A ≻ 0` symmetric and
  `M` symmetric, `|A^{-1/2} M A^{-1/2} - Id| ≤ t` is equivalent to
  `(1-t) A ≤ M ≤ (1+t) A`, because congruence by `A^{±1/2}` preserves the
  Loewner order in both directions. The first summand is the instance
  `A = s_L(U)`, `M = s_m(U)`; the second is the instance
  `A = s_{m,*}^{-1}(U)`, `M = s_{L,*}^{-1}(U)`, whose `A^{-1/2} = s_{m,*}^{1/2}`
  reproduces the printed norm and which is stated on `sigmaStarInvCoarse`, the
  primitive carrier, so that no matrix inversion enters the statement. A
  negative value of the witness falsifies both sides at once (`-2 t A ≤ 0` is
  impossible for `A ≻ 0`), so no sign hypothesis is needed.
* **The unsymmetric sandwich.**
  `e.skbounds` is written
  `2 p·H q ≤ t (p·A p + q·B q)` for all `p, q`, with `A = s_{L,*}(U)`,
  `B = s_L(U)` and `H = kcg_L(U) - kcg_m(U) - (k_L - k_m)_U`; the substitution
  `u = A^{1/2}p`, `v = B^{1/2}q` shows this is exactly `|A^{-1/2}HB^{-1/2}| ≤ t`.
* **The printed sum of two norms.** `e.localization.s.star` bounds the sum of
  the two norms by one `O_{Γ₁}` quantity; this statement bounds each of them by
  the same witness. The readings are equivalent because both norms are
  nonnegative and `C` is bound outermost (`N₁+N₂ ≤ X ⟹ N_i ≤ X`, and
  `N_i ≤ X ⟹ N₁+N₂ ≤ 2X`, with `2C` admissible). Every Section 3 consumer uses
  one summand at a time.
* **The maximizers.**
  `v(·,U,p,q;a)` of `e.J.def` is quantified **universally**
  over every `a`-harmonic function attaining the variational supremum; the
  maximizing property is written out literally as
  `∀ w, ⨍_U (integrand at w) ≤ ⨍_U (integrand at u)`, the defining property of
  the supremum `ResponseJ`. Neither existence nor uniqueness is assumed, and
  the existence and uniqueness-modulo-constants asserted in the paper remain a
  separate obligation, never a premise. The clause is therefore vacuous at any
  `(omega, p, q)` admitting no maximizer, and asserts no existence.
* **The `L^∞` window (`e.nabla.kmn.Linfty`).**
  `‖∇(k_m - k_L)‖_{L^∞(cu_n)}` is the pointwise supremum over the open cube
  `cu_n` of the exact Euclidean induced norm of the derivative of the finite
  shell increment, that derivative being the finite sum of the stored shell
  derivatives on `(m, L]`; zero is adjoined to the defining range explicitly,
  the pattern of `shellDerivLinftyNorm`. This is the norm of
  the sum, not the sum of shellwise norms. Because `ShellField` stores a
  continuous derivative and `cu_n` is open and nonempty, the pointwise
  supremum coincides with the essential supremum of the printed `L^∞` norm as
  read in the proof of `l.localization`.
* **The cubes and the domain.** `cu_n` is the **open** cube, used
  here only as the container of `U` and as the window of the `L^∞` norm, so it
  is `Homogenization.openCubeSet`; the paper's Lipschitz domain is
  `Homogenization.Book.Ch02.Domain d` (bounded open convex), and its bundled
  boundedness is implied by the printed inclusion `U ⊆ cu_n`.
* **The coarse layer.** The coarse matrices and `J` are the raw
  `Homogenization.sigmaCoarse`, `sigmaStarInvCoarse`, `sigmaStarCoarse`,
  `kappaCoarse` and `ResponseJ` on `Set (Vec d)` and `CoeffField d`, so that
  no `Book.Ch02.CoeffOn` bundle and hence no ellipticity constant or entry bound enters the
  statement.
* **The J-binders.** `a.multiscale.stream` is carried by the prefix and
  `J1`--`J4`, the range-of-dependence assumption being the restriction version
  `ShellLawJ1Restriction`. `J5`,
  `c⋆` and the nondegeneracy constant occur neither in the printed lemma nor in
  its printed proof, so they are absent.

The statement assumes the dimension hypothesis `(d : ℕ) [NeZero d] (hd : 2 ≤ d)`, as the
paper assumes `d ≥ 2` throughout. -/
theorem SuperdiffusionCLT.Frozen.Section2.cutoff_localization
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
          ∀ m n L : ℕ, n ≤ m → m ≤ L →
            ∀ U : Homogenization.Book.Ch02.Domain d,
              (U : Set (Homogenization.Vec d)) ⊆
                  Homogenization.openCubeSet
                    (Homogenization.originCube d (n : ℤ)) →
              (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧
                  Homogenization.IndependentSums.IsBigO P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma 1) X
                      (C * nu ^ (-(2 : ℝ)) *
                        (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ∧
                    ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                      Homogenization.MatLoewnerLE
                          ((1 - X omega) •
                            Homogenization.sigmaCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField)
                          (Homogenization.sigmaCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega m).toCoeffField) ∧
                        Homogenization.MatLoewnerLE
                          (Homogenization.sigmaCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega m).toCoeffField)
                          ((1 + X omega) •
                            Homogenization.sigmaCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField) ∧
                        Homogenization.MatLoewnerLE
                          ((1 - X omega) •
                            Homogenization.sigmaStarInvCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega m).toCoeffField)
                          (Homogenization.sigmaStarInvCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega L).toCoeffField) ∧
                        Homogenization.MatLoewnerLE
                          (Homogenization.sigmaStarInvCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega L).toCoeffField)
                          ((1 + X omega) •
                            Homogenization.sigmaStarInvCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega m).toCoeffField)) ∧
                (∃ Y : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable Y ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma 1) Y
                        (C * nu ^ (-(2 : ℝ)) *
                          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2))) ∧
                      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                        (p q : Homogenization.Vec d),
                        2 * Homogenization.vecDot p
                            (Homogenization.matVecMul
                              (Homogenization.kappaCoarse
                                  (U : Set (Homogenization.Vec d))
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField -
                                Homogenization.kappaCoarse
                                  (U : Set (Homogenization.Vec d))
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega m).toCoeffField -
                                Homogenization.volumeAverageMat
                                  (U : Set (Homogenization.Vec d))
                                  (fun y =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega m L y))
                              q) ≤
                          Y omega *
                            (Homogenization.vecDot p
                                (Homogenization.matVecMul
                                  (Homogenization.sigmaStarCoarse
                                    (U : Set (Homogenization.Vec d))
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L).toCoeffField) p) +
                              Homogenization.vecDot q
                                (Homogenization.matVecMul
                                  (Homogenization.sigmaCoarse
                                    (U : Set (Homogenization.Vec d))
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L).toCoeffField) q))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.Vec d)
                    (u : Homogenization.AHarmonicFunction
                      (fun x : Homogenization.Vec d =>
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                              nu omega L).toCoeffField x -
                          Homogenization.volumeAverageMat
                            (U : Set (Homogenization.Vec d))
                            (fun y =>
                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega m L y))
                      (U : Set (Homogenization.Vec d)))
                    (v : Homogenization.AHarmonicFunction
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                          nu omega m).toCoeffField
                      (U : Set (Homogenization.Vec d))),
                    (∀ w : Homogenization.AHarmonicFunction
                        (fun x : Homogenization.Vec d =>
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega L).toCoeffField x -
                            Homogenization.volumeAverageMat
                              (U : Set (Homogenization.Vec d))
                              (fun y =>
                                SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                  omega m L y))
                        (U : Set (Homogenization.Vec d)),
                        Homogenization.volumeAverage
                            (U : Set (Homogenization.Vec d))
                            (Homogenization.scalarResponseIntegrand
                              (U : Set (Homogenization.Vec d))
                              (fun x : Homogenization.Vec d =>
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField x -
                                  Homogenization.volumeAverageMat
                                    (U : Set (Homogenization.Vec d))
                                    (fun y =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega m L y))
                              p q w) ≤
                          Homogenization.volumeAverage
                            (U : Set (Homogenization.Vec d))
                            (Homogenization.scalarResponseIntegrand
                              (U : Set (Homogenization.Vec d))
                              (fun x : Homogenization.Vec d =>
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField x -
                                  Homogenization.volumeAverageMat
                                    (U : Set (Homogenization.Vec d))
                                    (fun y =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega m L y))
                              p q u)) →
                      (∀ w : Homogenization.AHarmonicFunction
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                              nu omega m).toCoeffField
                          (U : Set (Homogenization.Vec d)),
                          Homogenization.volumeAverage
                              (U : Set (Homogenization.Vec d))
                              (Homogenization.scalarResponseIntegrand
                                (U : Set (Homogenization.Vec d))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega m).toCoeffField p q w) ≤
                            Homogenization.volumeAverage
                              (U : Set (Homogenization.Vec d))
                              (Homogenization.scalarResponseIntegrand
                                (U : Set (Homogenization.Vec d))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega m).toCoeffField p q v)) →
                        Homogenization.volumeAverage
                            (U : Set (Homogenization.Vec d))
                            (fun x =>
                              Homogenization.vecNormSq
                                (u.toH1.grad x - v.toH1.grad x)) ≤
                          C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
                              sSup
                                (Set.range fun o :
                                    Option {x : Homogenization.Vec d //
                                      x ∈ Homogenization.openCubeSet
                                        (Homogenization.originCube d (n : ℤ))} =>
                                  match o with
                                  | none => 0
                                  | some x =>
                                      SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
                                        (∑ k ∈ Finset.Ioc m L,
                                          SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
                                            (omega k) x.1)) *
                            (Homogenization.ResponseJ
                                (U : Set (Homogenization.Vec d)) p q
                                (fun x : Homogenization.Vec d =>
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L).toCoeffField x -
                                    Homogenization.volumeAverageMat
                                      (U : Set (Homogenization.Vec d))
                                      (fun y =>
                                        SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                          omega m L y)) +
                              Homogenization.ResponseJ
                                (U : Set (Homogenization.Vec d)) p q
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega m).toCoeffField +
                              2 * Homogenization.vecDot p q)
    := by
  exact SuperdiffusionCLT.Section2.Localization.cutoff_localization_unconditional d hd
