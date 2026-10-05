/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyOrderOneJunk

/-!
# The a priori response estimates with the order-one hatted negative norm

The four estimates of `l.abstract.response.fields` in the paper are its
deterministic half.  `AprioriAssemblyE.lean` assembles them with the order-zero
hatted negative norm and no hypothesis beyond `2 ≤ d`; this module does the same
for the reading in which the hatted negative norm of `e.abstract.response.ND.weak`
is the order-one vector norm `Section2.Norms.vecHatNegENormOrderOne`.

Only the fourth clause changes.  The four clauses are supplied by

* clause 1, `e.abstract.response.L8`: `exists_responseGradientL8Clause` with the
  junk branch `junkL8_bridge`;
* clause 2, `e.abstract.response.W28`: `exists_dirichletHessianL8Clause'`, the
  repaired case split of `AprioriAssemblyE.lean`, which has no junk binder;
* clause 3, `e.abstract.response.Hhalf`: `exists_dirichletHsClause` with
  `dirichlet_hhalf_bridge` at the constant `hhalfEndpointConst d hd`, the
  differentiated endpoint `hhalf_endpoint_bridge` and the junk branch
  `junkHalf_bridge`;
* clause 4, `e.abstract.response.ND.weak`: `exists_responseDifferenceL2Clause_orderOne`
  with the Step 3 bridge `harmonic_interpolation_bridge`, the order-one
  `Ĥ̲^{-1}` estimate
  `hminusOne_response_difference_bridge` at the constant
  `hminusOneResponseConst d`, and the order-one junk branch
  `junkND_bridge_orderOne` of `AprioriAssemblyOrderOneJunk.lean`.

The constant bookkeeping is the one of `responseFields_apriori_orderZero_of_clauses`:
the four clause constants are added, and each clause is monotone in its own
constant.

-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## The a priori response estimates at order one -/

/-- **The a priori response estimates with the order-one hatted negative norm.**
The conclusion is the statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne` verbatim: it
is `responseFields_apriori_orderZero_of_clauses` with the hatted negative norm of the
fourth clause read at order one.

There is no hypothesis beyond `2 ≤ d`.  The junk binders of the bridge chain
are discharged by `junkL8_bridge`, `junkHalf_bridge` and `junkND_bridge_orderOne`; the junk binder
of the Hessian clause is gone, replaced by the repaired case split of
`exists_dirichletHessianL8Clause'`; and
the order-one `Ĥ̲^{-1}` binder `hHm1` is discharged by
`hminusOne_response_difference_bridge`. -/
theorem responseFields_apriori_orderOne_of_clauses (d : ℕ) (hd : 2 ≤ d) :
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
    := by
  obtain ⟨C1, hC1top, hC1⟩ := exists_responseGradientL8Clause hd junkL8_bridge
  obtain ⟨C2, hC2top, hC2⟩ := exists_dirichletHessianL8Clause' hd
  obtain ⟨C3, hC3top, hC3⟩ := exists_dirichletHsClause
    (dirichletHhalfConst d hd (hhalfEndpointConst d hd))
    (dirichletHhalfConst_lt_top d hd (hhalfEndpointConst d hd))
    (dirichlet_hhalf_bridge d hd (hhalfEndpointConst d hd)
      (hhalfEndpointConst_nonneg d hd) (hhalf_endpoint_bridge d hd) junkHalf_bridge)
  obtain ⟨C4, hC4top, hC4⟩ := exists_responseDifferenceL2Clause_orderOne hd
    (harmonicInterpolationConst d) (harmonicInterpolationConst_lt_top d)
    (hminusOneResponseConst d) (hminusOneResponseConst_lt_top d)
    (harmonic_interpolation_bridge d) (hminusOne_response_difference_bridge hd)
    junkND_bridge_orderOne
  refine ⟨C1 + C2 + C3 + C4, ?_, ?_⟩
  · exact ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hC1top, hC2top⟩, hC3top⟩, hC4top⟩
  have hle1 : C1 ≤ C1 + C2 + C3 + C4 :=
    le_trans (le_trans le_self_add le_self_add) le_self_add
  have hle2 : C2 ≤ C1 + C2 + C3 + C4 :=
    le_trans (le_trans le_add_self le_self_add) le_self_add
  have hle3 : C3 ≤ C1 + C2 + C3 + C4 := le_trans le_add_self le_self_add
  have hle4 : C4 ≤ C1 + C2 + C3 + C4 := le_add_self
  intro M F wD wN hD hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (hC1 M F wD wN hD hN) ?_
    gcongr
  · intro DF HD hweak
    refine le_trans (hC2 M F wD hD DF HD hweak) ?_
    gcongr
  · refine le_trans (hC3 M F wD hD) ?_
    gcongr
  · refine le_trans (hC4 M F wD wN hD hN) ?_
    exact add_le_add (mul_le_mul' (mul_le_mul' hle4 le_rfl) le_rfl)
      (mul_le_mul' hle4 le_rfl)

end

end ResponseFields
end Section3
end SuperdiffusionCLT
