/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section2.Cutoff.Size
public import Homogenization.Geometry.ConvexDomain
public import Homogenization.Sobolev.PotentialSolenoidalL2OriginCubeBridge

/-!
# The Dirichlet response `w`

The paper defines the Dirichlet response `w ∈ H²(cu_m)` of `e.def.w` as the
solution of

`−Δw = (f_{L'} − f_{ℓ'})·p = ∇·((k_{L'} − k_{ℓ'}) p)` in `cu_m`,
`w = 0` on `∂cu_m`,

with `f_j = ∇·k_j` the row divergence, and `F = (k_{L'} − k_{ℓ'}) p`.

The predicate `IsDirichletResponse` renders this as
`IsCubeDirichletResponse` for the
flux field `(k_{L'} − k_{ℓ'}) p` on `openCubeSet (originCube d m)`, i.e. as the
zero-trace weak Dirichlet problem of `Homogenization.PDE.DirichletRHS` for the
coefficient `Id` and the forcing `−F` (the weak form
`∫ ∇w·∇φ = −∫ F·∇φ` of `−Δw = ∇·F`). This module wires the solvability and
uniqueness theory of that problem to the cube.

## Main results

* `isEllipticFieldOn_one`: the identity matrix field is elliptic on every open
  cube, with constants `lam = Lam = 1`; this is the ellipticity witness that the
  identity coefficient needs.
* `dirichletRhsField`: the flux field `F = (k_{L'} − k_{ℓ'}) p` whose divergence
  is the right-hand side of `e.def.w`.
* `isDirichletResponse_iff_isCubeDirichletResponse`: the identification of
  `IsDirichletResponse` with the sibling predicate
  `IsCubeDirichletResponse`, by `Iff.rfl`.
* `continuous_dirichletRhsField`: the flux field `(k_{L'} − k_{ℓ'}) p` is
  continuous in the point, because each shell of the carrier stores a
  continuous value map (`continuous_streamCutoff_apply`).
* `exists_isDirichletResponse`: a zero-trace weak solution exists. The flux
  field is square-integrable on the open cube because it is continuous and
  bounded on the cube (the cube sits in the closed ball of center `cubeCenter`
  and radius `cubeRadius`, on which the field is bounded); no summability
  hypothesis is needed.
* `dirichletResponse`, `isDirichletResponse_dirichletResponse`: the response
  defined by choice, with its defining property.
* `isDirichletResponse_gradToVectorL2_eq` and
  `isDirichletResponse_grad_ae_eq`: the a.e.-uniqueness of the gradient. Two
  responses have the same weak-gradient `L²` class, hence the same weak
  gradient almost everywhere.

## What is not claimed

The `H²(cu_m)` regularity the paper asserts for `w` on a cube with corners is
not claimed here; it is a separate statement.  The response is produced and its gradient is
unique at the level of the weak zero-trace problem only.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The identity coefficient field -/

/-- `Id · ξ = ξ` for the Euclidean carrier's matrix action. -/
private theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The identity matrix is elliptic with constants `lam = Lam = 1`. -/
private theorem isEllipticMatrix_one : IsEllipticMatrix 1 1 (1 : Mat d) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro ξ
    rw [matVecMul_one ξ, vecNormSq]
    simp only [one_mul]
    exact le_of_eq rfl
  · intro ξ
    rw [show ((1 : Mat d))⁻¹ = (1 : Mat d) from inv_one] at *
    rw [matVecMul_one ξ, vecNormSq]
    simp only [inv_one, one_mul]
    exact le_of_eq rfl

/-- The identity coefficient field `a ≡ Id` is elliptic on every open triadic
cube, with constants `lam = Lam = 1`. This is the ellipticity witness that the
zero-trace Dirichlet problem of `e.def.w` needs. -/
theorem isEllipticFieldOn_one (n : ℤ) :
    IsEllipticFieldOn 1 1 (openCubeSet (originCube d n)) (fun _ => (1 : Mat d)) := by
  classical
  refine ⟨?_, fun x _hx => isEllipticMatrix_one⟩
  refine measurable_matrix_of_entries fun i j => ?_
  exact Measurable.ite (isOpen_openCubeSet (originCube d n)).measurableSet
    (measurable_const : Measurable fun _ : Vec d => ((1 : Mat d) i j))
    (measurable_const : Measurable fun _ : Vec d => (0 : ℝ))

/-! ## The right-hand side field on the cube -/

/-- The flux field of `e.def.w`: `F = (k_{L'} − k_{ℓ'}) p`,
whose divergence `∇·F = (f_{L'} − f_{ℓ'})·p` is the right-hand side of
`−Δw = ∇·F`, with `f_j = ∇·k_j` the row divergence. -/
def dirichletRhsField (omega : ShellSeq d) (LPrime ellPrime : ℕ) (p : Vec d) :
    Vec d → Vec d :=
  fun x => matVecMul (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) p

/-- A continuous `Vec d`-valued field is bounded on an open triadic cube: the
cube sits in the closed ball of center `cubeCenter` and radius `cubeRadius`,
which is compact, and the Euclidean norm of the field is continuous. -/
private theorem exists_normBound_of_continuous (n : ℤ) {f : Vec d → Vec d}
    (hf : Continuous f) :
    ∃ C : ℝ, ∀ x ∈ openCubeSet (originCube d n), ‖f x‖ ≤ C := by
  have hsub : openCubeSet (originCube d n) ⊆
      Metric.closedBall (cubeCenter (originCube d n)) (cubeRadius (originCube d n)) := by
    rw [← ball_cubeCenter_eq_openCubeSet (originCube d n)]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact
      (Metric.closedBall (cubeCenter (originCube d n)) (cubeRadius (originCube d n))) :=
    ProperSpace.isCompact_closedBall _ _
  have hne : Set.Nonempty
      (Metric.closedBall (cubeCenter (originCube d n)) (cubeRadius (originCube d n))) :=
    ⟨cubeCenter (originCube d n), by simp [cubeRadius_nonneg (originCube d n)]⟩
  have hbdd : BddAbove
      ((fun y : Vec d => ‖f y‖) '' Metric.closedBall
        (cubeCenter (originCube d n)) (cubeRadius (originCube d n))) :=
    hK.bddAbove_image (hf.norm.continuousOn)
  refine ⟨sSup ((fun y : Vec d => ‖f y‖) '' Metric.closedBall
    (cubeCenter (originCube d n)) (cubeRadius (originCube d n))), fun y hy => ?_⟩
  exact le_csSup hbdd (Set.mem_image_of_mem _ (hsub hy))

/-- A continuous `Vec d`-valued field is square-integrable on an open triadic
cube, because the cube has finite measure and the field is bounded there. -/
theorem memVectorL2_of_continuous (n : ℤ) {f : Vec d → Vec d} (hf : Continuous f) :
    MemVectorL2 (openCubeSet (originCube d n)) f := by
  rw [MemVectorL2]
  obtain ⟨C, hC⟩ := exists_normBound_of_continuous n hf
  refine MeasureTheory.MemLp.of_bound
    (hf.stronglyMeasurable.aestronglyMeasurable) C ?_
  filter_upwards
    [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet (originCube d n)).measurableSet]
    with x hx
  exact hC x hx

/-- The flux field of `e.def.w` is continuous in the point: each
shell of the carrier stores a continuous value map. -/
theorem continuous_dirichletRhsField (omega : ShellSeq d) (LPrime ellPrime : ℕ) (p : Vec d) :
    Continuous (dirichletRhsField omega LPrime ellPrime p) := by
  have hentry : ∀ i j : Fin d, Continuous
      (fun x : Vec d => streamCutoff omega LPrime x i j -
        streamCutoff omega ellPrime x i j) := by
    intro i j
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_streamCutoff_apply omega LPrime))).sub
      ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_streamCutoff_apply omega ellPrime)))
  refine continuous_pi fun i => ?_
  show Continuous fun x : Vec d => ∑ j, (streamCutoff omega LPrime x -
    streamCutoff omega ellPrime x) i j * p j
  refine continuous_finsetSum _ fun j _ => ?_
  have hrw : (fun x : Vec d => (streamCutoff omega LPrime x -
      streamCutoff omega ellPrime x) i j * p j)
      = fun x : Vec d => (streamCutoff omega LPrime x i j -
          streamCutoff omega ellPrime x i j) * p j := by
    funext x
    rfl
  rw [hrw]
  exact (hentry i j).mul (continuous_const : Continuous fun _ : Vec d => p j)

/-- The flux field of `e.def.w` is square-integrable on the open
cube, being continuous there. -/
theorem memVectorL2_dirichletRhsField (omega : ShellSeq d) (LPrime ellPrime : ℕ) (m : ℕ)
    (p : Vec d) :
    MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (dirichletRhsField omega LPrime ellPrime p) :=
  memVectorL2_of_continuous (m : ℤ) (continuous_dirichletRhsField omega LPrime ellPrime p)

/-- An open triadic cube is nonempty. -/
private theorem nonempty_openCubeSet (n : ℤ) :
    Set.Nonempty (openCubeSet (originCube d n)) := by
  refine ⟨cubeCenter (originCube d n), ?_⟩
  rw [← ball_cubeCenter_eq_openCubeSet, Metric.mem_ball, dist_self]
  exact cubeRadius_pos (originCube d n)

/-! ## The identification with the sibling predicate -/

/-- **`IsDirichletResponse` is `IsCubeDirichletResponse`**: the predicate of
`e.def.w` is definitionally the Dirichlet response of the flux field
`dirichletRhsField omega LPrime ellPrime p` on the open cube
`openCubeSet (originCube d m)`, i.e. the first problem of
`e.abstract.response.equations` at
`F = (k_{L'} − k_{ℓ'}) p`, rendered as the zero-trace weak problem
`∫ ∇w·∇φ = −∫ F·∇φ`. -/
theorem isDirichletResponse_iff_isCubeDirichletResponse (omega : ShellSeq d)
    (LPrime ellPrime : ℕ) (m : ℕ) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (m : ℤ)))) :
    IsDirichletResponse omega LPrime ellPrime m p w ↔
      SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
        (originCube d (m : ℤ)) (dirichletRhsField omega LPrime ellPrime p) w :=
  Iff.rfl

/-! ## Existence and uniqueness of the response -/

/-- **Existence of the Dirichlet response of `e.def.w`**: for
every shell sequence, every pair of cutoff levels, every cube index `m` and
every vector `p`, the zero-trace weak Dirichlet problem
`−Δw = ∇·((k_{L'} − k_{ℓ'}) p)` in `cu_m` with `w = 0` on `∂cu_m` has a
solution `w ∈ H¹₀(cu_m)`.

The flux field `(k_{L'} − k_{ℓ'}) p` is square-integrable on the
open cube (`memVectorL2_dirichletRhsField`), the identity coefficient field is
elliptic there (`isEllipticFieldOn_one`), and the abstract zero-trace-potential
closure of CoarseGraining is realized on the bounded open convex cube; no
summability hypothesis is needed beyond these facts. -/
theorem exists_isDirichletResponse [NeZero d] (omega : ShellSeq d) (LPrime ellPrime : ℕ)
    (m : ℕ) (p : Vec d) :
    ∃ w : H10Function (openCubeSet (originCube d (m : ℤ))),
      IsDirichletResponse omega LPrime ellPrime m p w := by
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet (originCube d (m : ℤ))) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ)))
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := fun _ => (1 : Mat d)) (U := openCubeSet (originCube d (m : ℤ)))
      (g := fun x => -dirichletRhsField omega LPrime ellPrime p x) (lam := 1) (Lam := 1)
      (memVectorL2_dirichletRhsField omega LPrime ellPrime m p).neg hRealize
      (nonempty_openCubeSet (m : ℤ)) (isEllipticFieldOn_one (d := d) (m : ℤ))
  exact ⟨w, (isDirichletResponse_iff_isZeroTraceDirichletRhsWeakSolution omega LPrime ellPrime m p
    w).2 hw⟩

/-- Two responses have the same weak-gradient `L²` class. This form needs
neither the Poincaré inequality nor the dimension hypothesis. -/
theorem isDirichletResponse_gradToVectorL2_eq (omega : ShellSeq d) (LPrime ellPrime : ℕ)
    (m : ℕ) (p : Vec d) {w₁ w₂ : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (h₁ : IsDirichletResponse omega LPrime ellPrime m p w₁)
    (h₂ : IsDirichletResponse omega LPrime ellPrime m p w₂) :
    w₁.toH1Function.gradToVectorL2 = w₂.toH1Function.gradToVectorL2 := by
  have hu := (isDirichletResponse_iff_isZeroTraceDirichletRhsWeakSolution omega LPrime ellPrime m
    p w₁).1 h₁
  have hv := (isDirichletResponse_iff_isZeroTraceDirichletRhsWeakSolution omega LPrime ellPrime m
    p w₂).1 h₂
  exact IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
    (nonempty_openCubeSet (m : ℤ)) hu hv
    (isEllipticFieldOn_one (d := d) (m : ℤ))

/-! ## The Dirichlet response defined by choice -/

/-- **The Dirichlet response of `e.def.w`**: the zero-trace
weak solution of `−Δw = ∇·((k_{L'} − k_{ℓ'}) p)` on `cu_m` chosen by
`Classical.choice` among the solutions of `exists_isDirichletResponse`. Two
such choices agree in weak gradient, as `L²` classes and almost everywhere, by
`isDirichletResponse_gradToVectorL2_eq` and `isDirichletResponse_grad_ae_eq`.

The `H²(cu_m)` regularity that the paper asserts for `w` is not part of this definition. -/
noncomputable def dirichletResponse [NeZero d] (omega : ShellSeq d) (LPrime ellPrime : ℕ)
    (m : ℕ) (p : Vec d) : H10Function (openCubeSet (originCube d (m : ℤ))) :=
  Classical.choose (exists_isDirichletResponse omega LPrime ellPrime m p)

/-- The defining property of `dirichletResponse`. -/
theorem isDirichletResponse_dirichletResponse [NeZero d] (omega : ShellSeq d)
    (LPrime ellPrime : ℕ) (m : ℕ) (p : Vec d) :
    IsDirichletResponse omega LPrime ellPrime m p (dirichletResponse omega LPrime ellPrime m p) :=
  Classical.choose_spec (exists_isDirichletResponse omega LPrime ellPrime m p)

/-- Two responses agree in weak gradient almost everywhere, the pointwise form
of `isDirichletResponse_gradToVectorL2_eq`. -/
theorem isDirichletResponse_grad_ae_eq (omega : ShellSeq d) (LPrime ellPrime : ℕ) (m : ℕ)
    (p : Vec d) {w₁ w₂ : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (h₁ : IsDirichletResponse omega LPrime ellPrime m p w₁)
    (h₂ : IsDirichletResponse omega LPrime ellPrime m p w₂) :
    w₁.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))]
      w₂.toH1Function.grad := by
  have h := isDirichletResponse_gradToVectorL2_eq omega LPrime ellPrime m p h₁ h₂
  filter_upwards [H1Function.coeFn_gradToVectorL2 w₁.toH1Function,
    H1Function.coeFn_gradToVectorL2 w₂.toH1Function] with x hx₁ hx₂
  rw [← hx₁, ← hx₂, h]

end

end SuperdiffusionCLT.Section3.Setup