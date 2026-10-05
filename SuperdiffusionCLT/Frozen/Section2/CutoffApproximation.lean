/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.CutoffApproximationWork
public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Localization.CutoffComparison

@[expose] public section

/-- **Lemma `l.cutoff.approximation` (Cutoff approximation on bounded
domains)**, under the standing molecular-diffusivity range `nu ∈ (0,1]`.

Let `U` be a bounded domain and suppose `∑_{k=0}^∞ ‖∇ j_k‖_{L∞(U)} < ∞`.  With
`k^U = k - (k)_U = ∑_{k=0}^∞ (j_k - (j_k)_U)` and `a^U = ν Id + k^U`, the field
`a^U` is uniformly elliptic in `U`, and for every `L ∈ ℕ` and every
`u ∈ A(U; a^U) ∩ H¹(U)` there is `u_L ∈ u + H¹₀(U)` with `u_L ∈ A(U; a_L)` and

`‖∇u - ∇u_L‖_{L²(U)} ≤ C(U) ν^{-1} (∑_{k=L+1}^∞ ‖∇ j_k‖_{L∞(U)}) ‖∇u‖_{L²(U)}`.

The domain carrier is `Homogenization.Book.Ch02.Domain d` (bounded open convex)
where the paper prints a bounded Lipschitz domain.  The lemma is pathwise: it carries no
law and no `J1`--`J5` hypothesis, its only probabilistic input being the
summability hypothesis, which the accompanying remark in the paper
supplies almost surely from `a.j.reg` and Borel--Cantelli. -/
theorem SuperdiffusionCLT.Frozen.Section2.cutoff_approximation
    (d : ℕ) (U : Homogenization.Book.Ch02.Domain d) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
          Summable (fun k : ℕ =>
              SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                (U : Set (Homogenization.Vec d)) (omega k)) →
            (∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
                ∀ x ∈ (U : Set (Homogenization.Vec d)),
                  Homogenization.IsEllipticMatrix lam Lam
                    (nu • (1 : Homogenization.Mat d) +
                      SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                        omega (U : Set (Homogenization.Vec d)) x)) ∧
              ∀ (L : ℕ) (u : Homogenization.H1Function
                  (U : Set (Homogenization.Vec d))),
                Homogenization.IsAHarmonicGradient
                    (fun x : Homogenization.Vec d =>
                      nu • (1 : Homogenization.Mat d) +
                        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                          omega (U : Set (Homogenization.Vec d)) x)
                    (U : Set (Homogenization.Vec d)) u.grad →
                  ∃ uL : Homogenization.H1Function
                      (U : Set (Homogenization.Vec d)),
                    (∃ w : Homogenization.H10Function
                        (U : Set (Homogenization.Vec d)),
                      uL = u + w.toH1Function) ∧
                      Homogenization.IsAHarmonicGradient
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                            omega L).toCoeffField
                        (U : Set (Homogenization.Vec d)) uL.grad ∧
                      Real.sqrt (∫ x in (U : Set (Homogenization.Vec d)),
                          Homogenization.vecNormSq (u.grad x - uL.grad x)
                          ∂MeasureTheory.volume) ≤
                        C * nu⁻¹ *
                            (∑' k : ℕ,
                              SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                (U : Set (Homogenization.Vec d))
                                (omega (L + 1 + k))) *
                          Real.sqrt (∫ x in (U : Set (Homogenization.Vec d)),
                            Homogenization.vecNormSq (u.grad x)
                            ∂MeasureTheory.volume)
    := by
  exact SuperdiffusionCLT.Section2.Cutoff.cutoff_approximation d U
