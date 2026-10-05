/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliD
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryB

/-!
# The weak test on one grid cube for an arbitrary `H¹` vector field

`ca2_cube_pair`: for a grid cube `R` inside an open set `W` on which `u` solves `-∇·(A∇u) = f`,
the average over `R` of `(A∇u)·ξ` for any `H¹(R)` vector field `ξ` is bounded by the two weak
bounds of the right-hand-side lemma times `‖ξ‖ + 2 K ℓ ‖∇ξ‖` (the ambient-frame version of
`ca1_cube_ambient` for a general field `ξ`, needed for the boundary datum `Φ ∇γ - (u - γ) ∇Φ`).
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_exists_shift_h1 (R : TriadicCube d) (ξ : H1Function (openCubeSet R)) :
    ∃ ξ' : H1Function (openCubeSet (originCube d R.scale)),
      (∀ x, ξ'.toFun x = ξ.toFun (x + triadicCubeShift R)) ∧
      (∀ x, ξ'.grad x = ξ.grad (x + triadicCubeShift R)) := by
  refine ⟨(ξ.translate (-triadicCubeShift R)).restrict (isOpen_openCubeSet _)
    (ca1_openCube_subset_translate R), fun x => ?_, fun x => ?_⟩
  · simp [H1Function.restrict, H1Function.translate_toFun, sub_neg_eq_add]
  · simp [H1Function.restrict, H1Function.translate_grad, sub_neg_eq_add]

theorem ca2_cube_pair [NeZero d] (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    {lam Lam : ℝ} {A : CoeffField d} (hEll : IsEllipticFieldOn lam Lam W A)
    {S α1 β1 α2 β2 : ℝ} (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function W) {f : Vec d → ℝ} (hf2 : MemLp f 2 (normalizedCubeMeasure R))
    (hfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm R
      (ENNReal.ofReal (sobStar d)).conjExponent f ≠ ⊤)
    (hu : IsWeakSolutionOn A W u f (fun _ => 0))
    (hBB : ∀ (u' : H1Function (openCubeSet (originCube d R.scale))) (f' : Vec d → ℝ),
      IsWeakSolutionOn (fun x => A (x + triadicCubeShift R)) (openCubeSet (originCube d R.scale)) u' f'
        (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) (fun x => matVecMul (A (x + triadicCubeShift R) - S • (1 : Mat d)) (u'.grad x))) ≤
        ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f')
    (ξ : Fin d → H1Function (openCubeSet R)) {Λ : ℝ}
    (hΛ : ∀ i, cubeLpNorm R (2 : ℝ≥0∞) (ξ i).toFun +
      2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤ Λ) :
    |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x)) (fun i => (ξ i).toFun x))| ≤
      (S * (α2 * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β2 * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f) +
          (α1 * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β1 * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f)) * Λ := by
  classical
  obtain ⟨u', hu'f, hu'g, hsol⟩ := ca1_exists_shift R hRW u hu
  obtain ⟨hflux, hgrad⟩ := hBB u' (fun x => f (x + (triadicCubeShift R))) hsol
  have hellS := ca1_elliptic_shift R hRW hEll
  have hmeasf : AEStronglyMeasurable f (normalizedCubeMeasure R) := hf2.aestronglyMeasurable
  have hfin' : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
      (ENNReal.ofReal (sobStar d)).conjExponent (fun x => f (x + (triadicCubeShift R))) ≠ ⊤ := by
    rw [ca1_cubeLpENorm_shift R _ hmeasf]; exact hfin
  choose ξ' hξ'f hξ'g using fun i => ca2_exists_shift_h1 R (ξ i)
  have hΛ' : ∀ i, cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (ξ' i).toFun +
      2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor (originCube d R.scale) *
        cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ' i).grad x)) ≤ Λ := by
    intro i
    have n1 : cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (ξ' i).toFun =
        cubeLpNorm R (2 : ℝ≥0∞) (ξ i).toFun := by
      have := ca1_cubeLpNorm_shift R (2 : ℝ≥0∞) (ξ i).memL2_normalizedCubeMeasure.aestronglyMeasurable
      rw [← this]
      congr 1
      funext x
      exact hξ'f i x
    have n2 : cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ' i).grad x)) =
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) := by
      refine Eq.trans ?_ (ca1_cubeLpNorm_shift R (2 : ℝ≥0∞)
        (G := fun x => euclideanNorm ((ξ i).grad x))
        (r1_memLp_grad_eucNorm R (ξ i)).aestronglyMeasurable)
      congr 1
      funext x
      simp only [hξ'g i x]
    have n4 : cubeScaleFactor (originCube d R.scale) = cubeScaleFactor R := by
      simp [cubeScaleFactor, originCube]
    rw [n1, n2, n4]
    exact hΛ i
  have key := ca1_cube_weak_test (originCube d R.scale) hellS hS hα1 hβ1 hα2 hβ2 u'
    (fun x => f (x + (triadicCubeShift R))) hfin' ξ' hflux hgrad hΛ'
  have hT : (fun x => vecDot (matVecMul ((fun x => A (x + (triadicCubeShift R))) x) (u'.grad x))
      (fun i => (ξ' i).toFun x)) =
      fun x => (fun y => vecDot (matVecMul (A y) (u.grad y)) (fun i => (ξ i).toFun y))
        (x + (triadicCubeShift R)) := by
    funext x
    simp only [hu'g, hξ'f]
  have hav := cubeAverage_originCube_comp_addRight_eq R (fun y => vecDot (matVecMul (A y) (u.grad y))
    (fun i => (ξ i).toFun y))
  rw [hT, hav] at key
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRW
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have n1 : cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u'.grad x))) =
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) := by
    have := ca1_cubeLpNorm_shift R (2 : ℝ≥0∞) hG.aestronglyMeasurable
    rw [← this]
    congr 1
    funext x
    simp only [hu'g]
  have n3 : cubeLpNorm (originCube d R.scale) (ENNReal.ofReal (sobStar d)).conjExponent
      (fun x => f (x + (triadicCubeShift R))) = cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f :=
    ca1_cubeLpNorm_shift R _ hmeasf
  rw [n1, n3] at key
  exact key

/-- Witness for the non-law hypotheses of `ca2_cube_pair`: the identity field on the origin cube of
`ℝ²` at scale `3`, the zero solution, the zero vector field, `ν = S = 1`. -/
example : True := by
  obtain ⟨K, hK, hD⟩ := r1_ofReal_dual_le 2
  have hBB : ∀ (u' : H1Function (openCubeSet (originCube 2 (originCube 2 3).scale))) (f' : Vec 2 → ℝ),
      IsWeakSolutionOn (fun x => (fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift (originCube 2 3)))
        (openCubeSet (originCube 2 (originCube 2 3).scale)) u' f' (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube 2 (originCube 2 3).scale) (1 / 4 : ℝ)
          (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift (originCube 2 3)) -
            (1 : ℝ) • (1 : Mat 2)) (u'.grad x))) ≤
        ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube 2 (originCube 2 3).scale) 2 (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube 2 (originCube 2 3).scale) (ENNReal.ofReal (sobStar 2)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube 2 (originCube 2 3).scale) (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube 2 (originCube 2 3).scale) 2 (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube 2 (originCube 2 3).scale) (ENNReal.ofReal (sobStar 2)).conjExponent f' := by
    intro u' f' _
    refine ⟨?_, ?_⟩
    · have e : (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift (originCube 2 3)) -
          (1 : ℝ) • (1 : Mat 2)) (u'.grad x)) = fun _ => (0 : Vec 2) := by
        funext x i; simp [matVecMul]
      rw [e]
      refine le_trans (hD _ (fun _ => (0 : Vec 2)) (fun i => memLp_const 0)
        (by simp [vecNormSq, vecDot])) ?_
      simp [SuperdiffusionCLT.Section2.Norms.cubeLpENorm, vecNormSq, vecDot]
    · refine le_trans (hD _ u'.grad (r1_memLp_grad_comp _ u') (r1_memLp_grad_eucNorm _ u')) ?_
      simp
  have := ca2_cube_pair (d := 2) (originCube 2 3) (W := openCubeSet (originCube 2 3)) le_rfl
    (A := fun _ => (1 : Mat 2)) (lam := 1) (Lam := 1)
    (Section6.ew1_ellip _ (measurableSet_openCubeSet _)) (S := 1) (α1 := 0) (β1 := 0) (α2 := K)
    (β2 := 0) zero_le_one le_rfl le_rfl hK le_rfl (0 : H1Function (openCubeSet (originCube 2 3)))
    (f := fun _ => 0) (memLp_const 0) (by simp [SuperdiffusionCLT.Section2.Norms.cubeLpENorm])
    (fun φ => by simp [matVecMul, vecDot]) hBB
    (fun _ => (0 : H1Function (openCubeSet (originCube 2 3)))) (Λ := 0) (fun i => by
      simp [cubeLpNorm])
  trivial

end SuperdiffusionCLT.Section7
