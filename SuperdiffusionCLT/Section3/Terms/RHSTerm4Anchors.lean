/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Section3.Terms.RHSTerm4ConstFirst
public import SuperdiffusionCLT.Section3.Terms.EllsepEquation
public import SuperdiffusionCLT.Sobolev.CubeSmoothDensityH2B
public import SuperdiffusionCLT.Sobolev.DirichletW2pDivergence

/-!
# `l.RHS.term4` with its fractional duality discharged

Lemma `l.RHS.term4`, with display `e.RHS.term4`.

The constant-first form of `l.RHS.term4` (see `Section3/Terms/RHSTerm4ConstFirst.lean`
and `Section3/Terms/RHSTerm4Join.lean`) has three inputs: the two `Γ₂` witnesses
`hKminussp` and `hWhalf`, and the pointwise fractional duality `hDual` of the proof.
This module discharges the third one.

## What discharges the duality

`SuperdiffusionCLT.Sobolev.pairing_le_of_hasWeakHessianOn`
(`Sobolev/CubeSmoothDensityH2B.lean`) concludes exactly the `hDual` shape for a
gradient field `∇w` of an `H¹` function `w` carrying a weak Hessian, and asks
for five things: the weak-Hessian witness itself, the `L̲²(cu_m)` rows of the
matrix field, the `L̲²(cu_m)` membership of `∇w`, and the finiteness of the two
half norms.  All five are available here.

* **The weak-Hessian witness.** It is *constructed*, not assumed: the response
  `w` of `e.def.w` is the Dirichlet response on `cu_m` of the flux
  `F = (k_{L'} − k_{ℓ'})p`, that flux is `C¹` with the classical Jacobian
  `streamFluxWeakGradient` of `Section3/ResponseFields/RegboundsInputsB.lean`,
  and both are bounded on the cube, so the Calderón-Zygmund endpoint
  `Sobolev.exists_cubeDirichletResponseHessianLpEstimate` at the exponent `2`
  produces a `HasWeakHessianOn` witness for `w`.  This is
  `exists_hasWeakHessianOn_of_isDirichletResponse` below.
* **The two `L̲²` memberships.** The matrix field `k_{ℓ'} − k_ℓ` is continuous
  and the cube is bounded, so every row of it is `L̲²(cu_m)`; and `∇w` is
  `L̲²(cu_m)` because it is the gradient field bundled in the `H¹` structure of
  `w`.
* **The two finiteness conditions.** They are read off the pointwise clauses of
  `hKminussp` and `hWhalf` themselves: both bound the corresponding half norm by
  an `ENNReal.ofReal`, which is never `⊤`.

## On the a priori response anchor

The Hessian clause `e.abstract.response.W28` of the a priori estimate
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero` is **not**
consumed here, and cannot be: it is an `L̲⁸` *bound*, read universally over
weak-Hessian witnesses, and asserts no existence, while the duality needs a
witness and no bound at all.  The estimate enters the term-4
chain one step earlier instead, through `l.w.basic.regbounds`
(`Section3/ResponseFields/RegboundsB.lean`), whose third conclusion is the
`H̲^{1/2}` clause `hWhalf`.

## Main results

* `memLp_hilbertifyVecField_vecMul_streamCutoff_sub`: the row hypothesis.
* `exists_hasWeakHessianOn_of_isDirichletResponse`: the weak-Hessian witness.
* `hDual_of_hasWeakHessianOn`: the `hDual` binder from a given witness.
* `hDual_of_isDirichletResponse`: the `hDual` binder with no witness assumed.
* `exists_kmnWminussp_of_gate`: the `W^{-1/2,2}` witness `e.kmn.Wminussp` in the
  shape the term-4 chain (`l_RHS_term4_of_anchors_ae`) consumes, from clause (a) of
  the gate `streamIncrement_scale_estimates`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Sobolev
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L^q` data from continuity on a cube -/

/-- A continuous field of any normed carrier lies in every `L^q` of an open
triadic cube: the cube sits in a compact ball on which the field is bounded and
has finite measure.  This is the vector-valued form of
`Section3/Terms/EllsepEquation.memL2On_openCubeSet_of_continuous`. -/
private theorem memLp_openCubeSet_of_continuous {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {q : ℝ≥0∞} {f : Vec d → E} (hf : Continuous f) :
    MemLp f q (volume.restrict (openCubeSet Q)) := by
  have hsub : openCubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    ProperSpace.isCompact_closedBall _ _
  have hbdd : BddAbove ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    hK.bddAbove_image hf.norm.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable
    (sSup ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q))) ?_
  filter_upwards
    [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with y hy
  exact le_csSup hbdd (Set.mem_image_of_mem _ (hsub hy))

/-- The same against the normalized cube measure, which differs from the
restricted volume by one finite factor. -/
private theorem memLp_normalizedCubeMeasure_of_continuous {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {q : ℝ≥0∞} {f : Vec d → E}
    (hf : Continuous f) : MemLp f q (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memLp_openCubeSet_of_continuous Q hf).smul_measure ENNReal.ofReal_ne_top

/-! ## The row hypothesis of the fractional duality -/

/-- **The row hypothesis of the fractional duality, for the cutoff increment.**
Every row `u ↦ u ᵥ* (k_b − k_a)` of the matrix field `k_b − k_a` is an
`L̲²(Q)` field: the field is continuous and the cube is bounded. -/
theorem memLp_hilbertifyVecField_vecMul_streamCutoff_sub (omega : ShellSeq d)
    {a b : ℕ} (hab : a ≤ b) (Q : TriadicCube d) (u : Vec d) :
    MemLp (hilbertifyVecField (fun x => Matrix.vecMul u
        (streamCutoff omega b x - streamCutoff omega a x))) 2
      (normalizedCubeMeasure Q) := by
  have hcont : Continuous (fun x : Vec d => Matrix.vecMul u
      (streamCutoff omega b x - streamCutoff omega a x)) := by
    refine continuous_pi fun j => ?_
    have hcoord : (fun x : Vec d => Matrix.vecMul u
        (streamCutoff omega b x - streamCutoff omega a x) j)
        = fun x : Vec d => ∑ i : Fin d, u i *
          (streamCutoff omega b x - streamCutoff omega a x) i j := by
      funext x
      rfl
    rw [hcoord]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((continuous_apply j).comp
        ((continuous_apply i).comp (continuous_streamCutoff_sub omega hab)))
  refine Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 ?_
  exact memLp_openCubeSet_of_continuous Q hcont

/-! ## The weak Hessian of the Dirichlet response -/

/-- The classical Jacobian of the upper-shell flux, in the Euclidean matrix
carrier, is continuous. -/
private theorem continuous_jacobianHilbertMat_streamFluxWeakGradient
    (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b) (p : Vec d) :
    Continuous (fun x : Vec d =>
      jacobianHilbertMat (streamFluxWeakGradient omega a b p) x) := by
  have hbase : Continuous (fun x : Vec d =>
      ((fun i j => streamFluxWeakGradient omega a b p i x j) : Mat d)) :=
    continuous_pi fun i => continuous_pi fun j =>
      continuous_streamFluxWeakGradient omega hab p i j
  exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp hbase

/-- **The Dirichlet response of `e.def.w` carries a weak Hessian.** The flux
`F = (k_{L'} − k_{ℓ'})p` is `C¹` with the classical Jacobian
`streamFluxWeakGradient`, and both are bounded on the cube, so the
divergence-form Calderón-Zygmund endpoint of
`Sobolev/DirichletW2pDivergence.lean` at the exponent `2` produces a
`HasWeakHessianOn` witness for `w`.  Nothing is assumed beyond the response
equation and the ordering `ℓ' ≤ L'` of `e.scales.ordering`. -/
theorem exists_hasWeakHessianOn_of_isDirichletResponse (hd : 2 ≤ d)
    (omega : ShellSeq d) {LPrime ellPrime m : ℕ} (hab : ellPrime ≤ LPrime)
    (p : Vec d) (w : H10Function (openCubeSet (originCube d (m : ℤ))))
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    Nonempty (HasWeakHessianOn (openCubeSet (originCube d (m : ℤ)))
      w.toH1Function) := by
  obtain ⟨_C, _hCtop, hC⟩ :=
    exists_cubeDirichletResponseHessianLpEstimate hd 2 (by norm_num) (by norm_num)
  have hflux : Continuous (fun x : Vec d =>
      matVecMul (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) p) :=
    continuous_pi fun i => continuous_streamFlux_apply omega hab p i
  obtain ⟨H, _, _⟩ := hC (m : ℤ)
    (fun x => matVecMul (streamCutoff omega LPrime x -
      streamCutoff omega ellPrime x) p)
    (streamFluxWeakGradient omega ellPrime LPrime p)
    (memLp_normalizedCubeMeasure_of_continuous _ hflux)
    (fun i => hasWeakGradientOn_streamFluxWeakGradient omega hab p i _)
    (memLp_normalizedCubeMeasure_of_continuous _
      (continuous_jacobianHilbertMat_streamFluxWeakGradient omega hab p))
    (memLp_normalizedCubeMeasure_of_continuous _
      (continuous_jacobianHilbertMat_streamFluxWeakGradient omega hab p))
    w hw
  exact ⟨H⟩

/-! ## The fractional duality -/

/-- **The `hDual` binder of the constant-first form of `l.RHS.term4`, from a
weak-Hessian witness.** This is `Sobolev.pairing_le_of_hasWeakHessianOn` at `s = 1/2` with
the matrix field `k_{ℓ'} − k_ℓ` and the response gradient `∇w`, its two
`L̲²(cu_m)` binders discharged. -/
theorem hDual_of_hasWeakHessianOn (hd : 2 ≤ d) (omega : ShellSeq d)
    {ell ellPrime m : ℕ} (hlow : ell ≤ ellPrime) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (m : ℤ))))
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) w.toH1Function)
    (hMfin : Section2.Norms.matHatNegENorm (originCube d (m : ℤ))
        ((1 : ℝ) / 2) (2 : ℝ≥0∞)
        (fun x => streamCutoff omega ellPrime x - streamCutoff omega ell x) ≠ ⊤)
    (hGfin : Section2.Norms.cubeHsENorm (originCube d (m : ℤ)) ((1 : ℝ) / 2)
        (hilbertifyVecField w.toH1Function.grad) ≠ ⊤) :
    |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun y => vecDot p (matVecMul (streamCutoff omega ellPrime y -
          streamCutoff omega ell y) (w.toH1Function.grad y)))| ≤
      (Section2.Norms.matHatNegENorm (originCube d (m : ℤ))
            ((1 : ℝ) / 2) (2 : ℝ≥0∞)
            (fun x => streamCutoff omega ellPrime x -
              streamCutoff omega ell x)).toReal *
        (Section2.Norms.cubeHsENorm (originCube d (m : ℤ)) ((1 : ℝ) / 2)
            (hilbertifyVecField w.toH1Function.grad)).toReal * vecNorm p :=
  pairing_le_of_hasWeakHessianOn (by norm_num) (by norm_num) (by omega) p H
    (fun u => memLp_hilbertifyVecField_vecMul_streamCutoff_sub omega hlow _ u)
    (Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
      w.toH1Function.grad_memVectorL2)
    hMfin hGfin

/-- **The `hDual` binder of the constant-first form of `l.RHS.term4`, with no witness
assumed.**  The weak-Hessian witness is the one of
`exists_hasWeakHessianOn_of_isDirichletResponse`, and the two half norms are
finite because the pointwise clauses of the two `Γ₂` witnesses bound them by
real numbers. -/
theorem hDual_of_isDirichletResponse (hd : 2 ≤ d) (omega : ShellSeq d)
    {LPrime ellPrime ell m : ℕ} (hlow : ell ≤ ellPrime)
    (hhigh : ellPrime ≤ LPrime) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (m : ℤ))))
    (hw : IsDirichletResponse omega LPrime ellPrime m p w)
    (hMfin : Section2.Norms.matHatNegENorm (originCube d (m : ℤ))
        ((1 : ℝ) / 2) (2 : ℝ≥0∞)
        (fun x => streamCutoff omega ellPrime x - streamCutoff omega ell x) ≠ ⊤)
    (hGfin : Section2.Norms.cubeHsENorm (originCube d (m : ℤ)) ((1 : ℝ) / 2)
        (hilbertifyVecField w.toH1Function.grad) ≠ ⊤) :
    |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun y => vecDot p (matVecMul (streamCutoff omega ellPrime y -
          streamCutoff omega ell y) (w.toH1Function.grad y)))| ≤
      (Section2.Norms.matHatNegENorm (originCube d (m : ℤ))
            ((1 : ℝ) / 2) (2 : ℝ≥0∞)
            (fun x => streamCutoff omega ellPrime x -
              streamCutoff omega ell x)).toReal *
        (Section2.Norms.cubeHsENorm (originCube d (m : ℤ)) ((1 : ℝ) / 2)
            (hilbertifyVecField w.toH1Function.grad)).toReal * vecNorm p := by
  obtain ⟨H⟩ :=
    exists_hasWeakHessianOn_of_isDirichletResponse hd omega hhigh p w hw
  exact hDual_of_hasWeakHessianOn hd omega hlow p w H hMfin hGfin

/-! ## `e.RHS.term4` on the two `Γ₂` witnesses alone -/

/-! ## The `W^{-1/2,2}` witness from the shell-increment gate -/

/-- **`e.kmn.Wminussp` in the shape `l.RHS.term4` consumes**, from clause (a) of
the gate `streamIncrement_scale_estimates` at `s = 1/2`, `p = 2`.
Three reshapings separate the two texts and are done here: the gate's exponent
slot is `ENNReal.ofReal 2` where the term-4 hypothesis writes `(2 : ℝ≥0∞)`; the
gate's carrier is the finite increment `k_m − k_n` where the term-4 hypothesis
writes the difference of two cutoffs; and the gate's amplitude exponent is
`s · m` where the term-4 hypothesis writes `m / 2`.  The gate's clause constant
is a bare `∃ C : ℝ` with no sign, while `l_RHS_term4_constFirst_ae` asks for
`1 ≤ C₁`, so the amplitude is raised from `C` to `|C| + 1`. -/
theorem exists_kmnWminussp_of_gate {P : ProbabilityMeasure (ShellSeq d)} {C : ℝ}
    {l m n : ℕ} (hnm : n ≤ m)
    (hgate : ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X
        (C * (3 : ℝ) ^ (((1 : ℝ) / 2) * ((m : ℕ) : ℝ))) ∧
      ∀ omega : ShellSeq d,
        Section2.Norms.matHatNegENorm (originCube d (l : ℤ)) ((1 : ℝ) / 2)
            (ENNReal.ofReal (2 : ℝ))
            (fun x => (finiteShellIncrement omega n m x : Mat d)) ≤
          ENNReal.ofReal (X omega)) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X
        ((|C| + 1) * (3 : ℝ) ^ (((m : ℕ) : ℝ) / 2)) ∧
      ∀ omega : ShellSeq d,
        Section2.Norms.matHatNegENorm (originCube d (l : ℤ)) ((1 : ℝ) / 2)
            (2 : ℝ≥0∞)
            (fun x => streamCutoff omega m x - streamCutoff omega n x) ≤
          ENNReal.ofReal (X omega) := by
  obtain ⟨X, hXm, hXO, hXle⟩ := hgate
  have hexp : ((1 : ℝ) / 2) * ((m : ℕ) : ℝ) = ((m : ℕ) : ℝ) / 2 := by ring
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℝ≥0∞).toReal) from by norm_num,
      ENNReal.ofReal_toReal (by norm_num)]
  have hcar : ∀ omega : ShellSeq d,
      (fun x => (finiteShellIncrement omega n m x : Mat d))
        = fun x : Vec d => streamCutoff omega m x - streamCutoff omega n x := by
    intro omega
    funext x
    exact finiteShellIncrement_apply_eq_streamCutoff_sub omega hnm x
  refine ⟨X, hXm, ?_, ?_⟩
  · rw [hexp] at hXO
    refine hXO.mono_scale ?_
    have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (((m : ℕ) : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hle : C ≤ |C| + 1 := by
      have hself := le_abs_self C
      linarith only [hself]
    exact mul_le_mul_of_nonneg_right hle hbase
  · intro omega
    have h := hXle omega
    rwa [htwo, hcar omega] at h

/-! ## `e.RHS.term4` on the `H̲^{1/2}` response estimate alone -/

end

end SuperdiffusionCLT.Section3.Terms
