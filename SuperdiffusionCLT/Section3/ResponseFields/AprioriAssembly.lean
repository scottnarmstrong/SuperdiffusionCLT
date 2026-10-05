/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Section3.ResponseFields.ResponseLinearity
public import SuperdiffusionCLT.Section3.ResponseFields.HminusOneDuality
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Sobolev.DirichletW2pDivergence

/-!
# The gradient and Hessian clauses of the a priori response estimates

The paper states the first two of
the four deterministic estimates of `l.abstract.response.fields`:

* `e.abstract.response.L8`,
  `‖∇w_D‖_{L̲⁸} + ‖∇w_N‖_{L̲⁸} ≤ C ‖F‖_{L̲⁸}`;
* `e.abstract.response.W28`, read for the
  Dirichlet summand alone, `‖∇²w_D‖_{L̲⁸} ≤ C ‖∇F‖_{L̲⁸}`, read universally
  over weak-Hessian witnesses.

The gradient clause is assembled here, and the Hessian clause in `AprioriAssemblyE.lean`, in
exactly the shape the two conjuncts have in the statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero`: one constant
`C < ⊤` quantified before the scale, the flux and the two response fields.

## The two analytic inputs

* `exists_cubeResponseGradientL8Estimate` (`LpEstimates.lean`), Step 2 of the
  proof at the exponent `8`, for both branches at once. It is the `p = 8` case
  of `exists_cubeResponseGradientLpEstimate`, whose exponent range is
  `1 < p < ∞`, so `p = 8` is covered with room to spare.
* The Dirichlet Hessian endpoint of `Sobolev/DirichletW2pDivergence.lean`, at
  `p = 8`, already stated universally over the weak-Hessian witness `HD`: the
  a.e. uniqueness of weak derivatives (`hess_ae_eq` there) turns the witness
  produced by the Calderón-Zygmund endpoint into a bound for every witness.

## The integrability side conditions

The conjuncts carry no integrability hypothesis on the flux, while both
inputs need one: the gradient endpoint needs `F ∈ L̲⁸(cu_M)` and the Hessian
endpoint needs the `L̲²` data `F`, `∇F ∈ L̲²(cu_M)`. On a cube of finite
volume the only gap is the *junk branch* of the statement, where the
datum is not measurable and every pairing in the two response equations
evaluates against Bochner's `0`. The theorem below quantifies that branch as a
single explicit hypothesis, guarded so that the branch where the corresponding
right-hand side is `⊤` — where the estimate is empty — is discharged here and
not assumed.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Measure bookkeeping on a triadic cube -/

/-- The normalized cube measure is a probability measure. -/
theorem isProbabilityMeasure_normalizedCubeMeasure (Q : TriadicCube d) :
    IsProbabilityMeasure (normalizedCubeMeasure Q) :=
  ⟨normalizedCubeMeasure_apply_univ Q⟩

/-- `L̲^q(Q)` membership descends along exponents on a cube, the measure being a
probability measure. -/
theorem memLp_normalizedCubeMeasure_mono {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} {q r : ℝ≥0∞} {f : Vec d → E} (hqr : q ≤ r)
    (hf : MemLp f r (normalizedCubeMeasure Q)) : MemLp f q (normalizedCubeMeasure Q) := by
  have := isProbabilityMeasure_normalizedCubeMeasure Q
  exact hf.mono_exponent hqr

/-- An `L̲²(Q)` field is an `L²` field of the open cube: the two measures differ
by the positive finite factor `(cubeVolume Q)⁻¹`. -/
theorem memVectorL2_of_memLp_two_normalizedCubeMeasure {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) : MemVectorL2 (openCubeSet Q) F := by
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 (cubeVolume_pos Q))
  have h := hF.smul_measure (c := (ENNReal.ofReal ((cubeVolume Q)⁻¹))⁻¹) (by simp [hc])
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, smul_smul,
    ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul] at h
  exact h

/-- A sum with `1` never vanishes. -/
private theorem add_one_ne_zero (C : ℝ≥0∞) : C + 1 ≠ 0 := by
  intro h
  rw [add_eq_zero] at h
  exact one_ne_zero h.2

/-! ## `e.abstract.response.L8` -/

/-- **The `L̲⁸` gradient clause of `l.abstract.response.fields`**
(`e.abstract.response.L8`), in the shape of the first conjunct
of the statement `responseFields_apriori_orderZero`.

The single hypothesis `hjunk` is the junk branch of that conjunct: a flux of
finite `L̲⁸(cu_M)` size which is not `L̲⁸(cu_M)`-measurable, so that Step 2 of
the proof does not apply to it. The branch of infinite `L̲⁸(cu_M)` size, where
the right-hand side is `⊤`, is discharged in the proof. -/
theorem exists_responseGradientL8Clause (hd : 2 ≤ d)
    (hjunk : ∀ (M : ℕ) (F : Vec d → Vec d)
      (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
      (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
      IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
      vecCubeLpENorm (originCube d (M : ℤ)) 8 F < ⊤ →
      ¬ MemLp (hilbertifyVecField F) 8
          (normalizedCubeMeasure (originCube d (M : ℤ))) →
      vecCubeLpENorm (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
          vecCubeLpENorm (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
        vecCubeLpENorm (originCube d (M : ℤ)) 8 F) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
        vecCubeLpENorm (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
            vecCubeLpENorm (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
          C * vecCubeLpENorm (originCube d (M : ℤ)) 8 F := by
  obtain ⟨C, hCtop, hC⟩ := exists_cubeResponseGradientL8Estimate hd
  refine ⟨C + 1, ENNReal.add_lt_top.2 ⟨hCtop, ENNReal.one_lt_top⟩, ?_⟩
  intro M F wD wN hD hN
  by_cases hmem : MemLp (hilbertifyVecField F) 8
      (normalizedCubeMeasure (originCube d (M : ℤ)))
  · refine le_trans (hC _ F hmem wD wN hD hN) ?_
    gcongr
    exact le_self_add
  · by_cases htop : vecCubeLpENorm (originCube d (M : ℤ)) 8 F = ⊤
    · rw [htop, ENNReal.mul_top (add_one_ne_zero C)]
      exact le_top
    · refine le_trans (hjunk M F wD wN hD hN (lt_top_iff_ne_top.2 htop) hmem) ?_
      calc vecCubeLpENorm (originCube d (M : ℤ)) 8 F
          = 1 * vecCubeLpENorm (originCube d (M : ℤ)) 8 F := (one_mul _).symm
        _ ≤ (C + 1) * vecCubeLpENorm (originCube d (M : ℤ)) 8 F := by
            gcongr
            exact le_add_self

/-! ## `e.abstract.response.W28`, the Dirichlet summand -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
