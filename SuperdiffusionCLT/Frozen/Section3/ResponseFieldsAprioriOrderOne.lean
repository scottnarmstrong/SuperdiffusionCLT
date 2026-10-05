/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section2.Norms.NegativeHatOrderOne
public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyOrderOne
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

/-- **Lemma `l.abstract.response.fields`, the deterministic half**: the four estimates the
paper introduces as "the following deterministic estimates, which
do not use stationarity, hold with a constant `C(d) < ∞`".

For every `M ∈ ℕ`, every flux field `F` and every pair of response fields
`w_D ∈ H¹₀(cu_M)`, `w_N ∈ H¹(cu_M)` of `e.abstract.response.equations`:

* `e.abstract.response.L8`,
  `‖∇w_D‖_{L̲⁸} + ‖∇w_N‖_{L̲⁸} ≤ C ‖F‖_{L̲⁸}`;
* `e.abstract.response.W28`,
  `‖∇²w_D‖_{L̲⁸} + ‖∇²w_N‖_{L̲⁸} ≤ C ‖∇F‖_{L̲⁸}`;
* `e.abstract.response.Hhalf`,
  `‖∇w_D‖_{H̲^{1/2}} + ‖∇w_N‖_{H̲^{1/2}} ≤ C ‖F‖_{H̲^{1/2}}`; and
* `e.abstract.response.ND.weak`, introduced by "Finally,"
  under the same constant,
  `‖∇w_N − ∇w_D‖_{L̲²} ≤ C ‖F − (F)_{cu_M}‖_{Ĥ̲^{-1}}^{1/5}
  ‖F − (F)_{cu_M}‖_{L̲⁴}^{4/5} + C |(F)_{cu_M}|`.

The stationary energy comparison of the paper is the companion statement
`responseFields_stationary`. There is no probability space, no measure and no
group action here: every binder is a deterministic datum of one cube and one
flux field, and the one constant is quantified before all of them
and shared by all four estimates.

Readings: `e.abstract.response.W28` is read universally over weak-Hessian
witnesses, so the clause bounds every witness and asserts neither existence nor
regularity; `2 ≤ d` is standing, the `L^p` endpoint needing it; the function spaces are on the
open cube while the normalized norms and averages are on the half-open cube,
the two being interchangeable by
`SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet`
and
`SuperdiffusionCLT.Section3.ResponseFields.volumeAverageVec_cubeSet_eq_openCubeSet`;
the `H̲^{1/2}` norm is `cubeHsENorm`; the pointwise size of the weak
Hessian `∇²w` and of `∇F` in `e.abstract.response.W28` is the Frobenius norm
of `HilbertMat`, which differs from the operator norm by a factor
between `1` and `√d`, absorbed by the constant `C(d)`.

The Hessian clause (`e.abstract.response.W28`) and the `H̲^{1/2}`
clause (`e.abstract.response.Hhalf`) are stated for the Dirichlet response
only. The paper proves them "by reflection"; for the Neumann
response the reflected flux is discontinuous across every face on which the
normal component does not vanish, so its divergence carries a surface term and
the reflected problem is not a Poisson problem with `L^p` data: the sketch does
not reach the Neumann Hessian, and the `H^{1/2}` interpolation needs that
`W^{2,2}` endpoint. Section 3 consumes these two clauses only for the Dirichlet
response; the Neumann versions are used later in the paper. The `L̲^8` gradient clause and the
weak Neumann–Dirichlet comparison hold for both responses.

The hatted negative norm of `e.abstract.response.ND.weak` is the
order-one vector norm `SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne`,
in the scaled normalization, and not the order-zero
`Section3.ResponseFields.vecHatNegENorm`. The test class of the
supremum defining `‖F‖_{Ĥ̲^{-1}(U)}` constrains the test *gradient field* in
`H̲¹(U)`, that is `‖∇g‖_{L̲²(U)} + |U|^{1/d}‖∇²g‖_{L̲²(U)} ≤ 1`; the printed
"for instance" sentence `‖∇g‖_{L̲²(U)} ≤ 1` is a correction of the printed text (see
`ERRATA.md`): it defines an order-zero quantity, under which the scaling of the
proof is not the printed one. The order-one norm is
the smaller of the two
(`SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne_le_vecHatNegENorm`), so
the fourth clause here is stronger than with the order-zero norm. -/
theorem SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
          (originCube d (M : ℤ)) F wD →
        SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
          (originCube d (M : ℤ)) F wN →
        (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
            C * SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
              (originCube d (M : ℤ)) 8 F) ∧
        (∀ (DF : Fin d → Vec d → Vec d)
            (HD : HasWeakHessianOn (openCubeSet (originCube d (M : ℤ)))
              wD.toH1Function),
            (∀ i, HasWeakGradientOn (openCubeSet (originCube d (M : ℤ)))
              (fun x => F x i) (DF i)) →
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
            C * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => DF i x j))) ∧
        (SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField wD.toH1Function.grad) ≤
            C * SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField F)) ∧
        (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
              (originCube d (M : ℤ)) 2
              (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
            C * (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne
                  (originCube d (M : ℤ))
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
                (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (M : ℤ)) 4
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
              C * ‖HilbertVec.ofVec (volumeAverageVec
                  (cubeSet (originCube d (M : ℤ))) F)‖ₑ)
    :=
  SuperdiffusionCLT.Section3.ResponseFields.responseFields_apriori_orderOne_of_clauses d hd
