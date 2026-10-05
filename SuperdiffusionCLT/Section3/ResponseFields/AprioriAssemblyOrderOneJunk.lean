/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyE
public import SuperdiffusionCLT.Section3.ResponseFields.HminusOneOrderOneB

/-!
# The junk branch of `e.abstract.response.ND.weak` in the order-one carrier

`e.abstract.response.ND.weak` is the fourth clause of the deterministic half of
`l.abstract.response.fields` in the paper. Its hatted negative norm is the order-one
vector norm `Section2.Norms.vecHatNegENormOrderOne`, and the clause is assembled by
`exists_responseDifferenceL2Clause_orderOne` from three inputs, the last of which is the
branch on which Step 4 does not run.

`JunkBranchB.junkND_bridge` is that branch in the order-zero carrier
`vecHatNegENorm`. It is not the hypothesis the order-one clause asks for: its
second guard reads `‖F₀‖_{Ĥ̲^{-1}(cu_M)} = 0` at order zero, whereas the
order-one guard is the weaker `‖F₀‖ = 0` for the *smaller* norm, and its
conclusion is stated in the order-zero norm as well.

This module supplies the missing step and the order-one branch.

## The two norms vanish together

The order-one test class constrains
`‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)} ≤ 1`, the order-zero class
only `‖∇g‖_{L̲²(Q)} ≤ 1`, so the order-one supremum is the smaller of the
two. The converse implication *at the value zero* is pure homogeneity and needs
no density: a smooth potential has a finite order-one test quantity
(`vecHatTestH1ENorm_lt_top`, because `∇g` and `∇²g` are continuous and the cube
is bounded), so a positive multiple of any order-zero test potential is
order-one admissible, and the duality
`ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul` transports the
vanishing of the order-one supremum to every order-zero test potential. That is
`vecHatNegENorm_eq_zero_of_vecHatNegENormOrderOne_eq_zero`.

## The branch

With that, `junkND_bridge_orderOne` is the order-one branch: on the guard
`‖F₀‖_{L̲⁴(cu_M)} < ⊤` the centred flux is not measurable and both response
gradients vanish almost everywhere, exactly as at order zero; on the guard
`‖F₀‖_{Ĥ̲^{-1}(cu_M)} = 0` at order one the order-zero norm of `F₀` vanishes
too, and the order-zero branch of `JunkBranchB.lean` applies verbatim, paying
for the centring with the printed constant term `|(F)_{cu_M}|`.

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

/-! ## A continuous field is `L^q` for the normalized cube measure -/

/-- Every continuous field is `L^q` for the normalized measure of a triadic
cube: the cube is bounded, so the field is bounded on its compact closure. -/
private theorem memLp_normalizedCubeMeasure_of_continuous' {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {q : ℝ≥0∞} {f : Vec d → E}
    (hf : Continuous f) : MemLp f q (normalizedCubeMeasure Q) := by
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn
    hf.norm.continuousOn
  have hae : ∀ᵐ x ∂(normalizedCubeMeasure Q), ‖f x‖ ≤ C := by
    rw [normalizedCubeMeasure]
    refine Measure.ae_smul_measure ?_ _
    rw [cubeMeasure]
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    simpa only [Real.norm_eq_abs, abs_norm] using hC x (subset_closure hx)
  exact MemLp.of_bound hf.aestronglyMeasurable C hae

/-! ## The order-one test quantity of a smooth potential is finite -/

private theorem contDiff_euclideanGradient_apply'' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => euclideanGradient g y i) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fderiv ℝ g y) :=
    hg.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

private theorem continuous_hilbertifyVecField_euclideanGradient' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (fun x : Vec d => hilbertifyVecField (euclideanGradient g) x) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  have hcont : Continuous (fun x : Vec d => euclideanGradient g x) :=
    continuous_pi fun _ => hfd.clm_apply continuous_const
  exact (HilbertVec.ofVecL d).continuous.comp hcont

private theorem continuous_hilbertMat_euclideanGradientJacobian' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (fun x : Vec d =>
      HilbertMat.ofMat (Section2.Norms.euclideanGradientJacobian g x)) := by
  have hcont : Continuous
      (fun x : Vec d => (Section2.Norms.euclideanGradientJacobian g x : Mat d)) := by
    refine continuous_pi fun i => continuous_pi fun _ => ?_
    have h : Continuous (fun x : Vec d =>
        fderiv ℝ (fun y : Vec d => euclideanGradient g y i) x) :=
      (contDiff_euclideanGradient_apply'' hg i).continuous_fderiv
        (by simp)
    exact h.clm_apply continuous_const
  exact ((HilbertMat.continuousLinearEquivMat d).symm).continuous.comp hcont

/-- **A smooth potential has a finite order-one test quantity.** Both `∇g` and
`∇²g` are continuous, hence bounded on the compact closure of the cube, so both
summands of `vecHatTestH1ENorm` are finite. -/
theorem vecHatTestH1ENorm_lt_top {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Section2.Norms.vecHatTestH1ENorm Q g < ⊤ := by
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
  · exact (memLp_normalizedCubeMeasure_of_continuous' Q
      (continuous_hilbertifyVecField_euclideanGradient' hg)).eLpNorm_lt_top
  · exact (memLp_normalizedCubeMeasure_of_continuous' Q
      (continuous_hilbertMat_euclideanGradientJacobian' hg)).eLpNorm_lt_top

/-! ## The two hatted negative norms vanish together -/

/-- **The order-zero hatted negative norm vanishes with the order-one one.**
The order-one norm is the smaller of the two
(`Section2.Norms.vecHatNegENormOrderOne_le_vecHatNegENorm`); at the value zero the
reverse implication holds as well, by homogeneity of the supremum in the test
potential. Given an order-zero test potential `g`, the order-one test quantity
`vecHatTestH1ENorm Q g` is finite, so `c⁻¹ g` is order-one admissible for
`c = (vecHatTestH1ENorm Q g).toReal + 1`, and the duality
`ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul` bounds the pairing of
`F` against `g` by `c · 0 = 0`. No density statement is used. -/
theorem vecHatNegENorm_eq_zero_of_vecHatNegENormOrderOne_eq_zero {Q : TriadicCube d}
    {F : Vec d → Vec d} (h : Section2.Norms.vecHatNegENormOrderOne Q F = 0) :
    vecHatNegENorm Q F = 0 := by
  refine le_antisymm (vecHatNegENorm_le fun g hg => ?_) (zero_le)
  set c : ℝ := (Section2.Norms.vecHatTestH1ENorm Q g).toReal + 1 with hcdef
  have hcpos : 0 < c := by
    have : (0 : ℝ) ≤ (Section2.Norms.vecHatTestH1ENorm Q g).toReal :=
      ENNReal.toReal_nonneg
    rw [hcdef]
    linarith only [this]
  have hnorm : Section2.Norms.vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c := by
    have hofReal : ENNReal.ofReal c = Section2.Norms.vecHatTestH1ENorm Q g + 1 := by
      rw [hcdef, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
        ENNReal.ofReal_toReal (vecHatTestH1ENorm_lt_top hg.contDiff).ne,
        ENNReal.ofReal_one]
    rw [hofReal]
    exact le_self_add
  have hpair := Section2.Norms.ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul
    F hcpos hg.contDiff hg.meanZero hnorm
  rw [h, mul_zero, le_zero_iff, ENNReal.ofReal_eq_zero] at hpair
  have hzero : volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) = 0 :=
    abs_eq_zero.1 (le_antisymm hpair (abs_nonneg _))
  rw [hzero, ENNReal.ofReal_zero]

/-! ## The junk branch of `e.abstract.response.ND.weak` at order one -/

/-- **The junk branch of the fourth conjunct of the version-3 a priori
statement**, in the exact shape of the hypothesis `hjunk` of
`AprioriAssemblyC.exists_responseDifferenceL2Clause_orderOne`.

This is `JunkBranchB.junkND_bridge` with the hatted negative norm read at order
one. On the first guard the centred flux has finite `L̲⁴(cu_M)` size, so failing
to be an `L̲⁴(cu_M)` field means it is not measurable on the cube; the flux
itself is then not measurable either, both response gradients vanish almost
everywhere and the left-hand side is `0`. On the second guard the order-one
hatted negative norm of the centred flux vanishes, hence so does the order-zero
one, and the duality bound `vecCubeLpENorm_grad_sub_le_vecHatNegENorm`
together with `vecHatNegENorm_le_add_const` pays for the centring with exactly
the printed constant term `|(F)_{cu_M}|`. -/
theorem junkND_bridge_orderOne (M : ℕ) (F : Vec d → Vec d)
    (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (hD : IsCubeDirichletResponse (originCube d (M : ℤ)) F wD)
    (hN : IsCubeNeumannResponse (originCube d (M : ℤ)) F wN)
    (hmem : ¬ MemLp (hilbertifyVecField (fun x => F x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) 4
        (normalizedCubeMeasure (originCube d (M : ℤ))))
    (hguard : vecCubeLpENorm (originCube d (M : ℤ)) 4
          (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) < ⊤ ∨
        Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
          (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0) :
    vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      (Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm (originCube d (M : ℤ)) 4
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
        ‖HilbertVec.ofVec (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ := by
  rcases hguard with hfin | hhat
  · have hF0 := not_aestronglyMeasurable_of_not_memLp hfin hmem
    have hF : ¬ AEStronglyMeasurable F
        (volume.restrict (openCubeSet (originCube d (M : ℤ)))) := fun h =>
      hF0 (h.sub aestronglyMeasurable_const)
    have hzero : vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) = 0 := by
      refine vecCubeLpENorm_eq_zero_of_ae_eq_zero ?_
      filter_upwards [grad_ae_eq_zero_of_isCubeDirichletResponse hF hD,
        grad_ae_eq_zero_of_isCubeNeumannResponse hF hN] with x hxD hxN
      simp [hxD, hxN]
    rw [hzero]
    exact zero_le
  · have hhat0 : vecHatNegENorm (originCube d (M : ℤ))
        (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0 :=
      vecHatNegENorm_eq_zero_of_vecHatNegENormOrderOne_eq_zero hhat
    have hbound : vecHatNegENorm (originCube d (M : ℤ)) F ≤
        ‖HilbertVec.ofVec (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ := by
      refine le_trans (vecHatNegENorm_le_add_const F
        (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ?_
      rw [hhat0, zero_add]
      exact vecHatNegENorm_const_le _
    rw [hhat, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_add]
    exact le_trans (vecCubeLpENorm_grad_sub_le_vecHatNegENorm hN hD) hbound

end

end ResponseFields
end Section3
end SuperdiffusionCLT
