/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Pigeonhole
public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import Homogenization.PDE.DirichletRHS

/-!
# The test vectors, the maximizers and the Dirichlet response

The paper introduces the objects on which the proof of Proposition
`p.sstar.lower.bound` is run, after the scales of `Parameters.lean` and the
pigeonhole scale of `Pigeonhole.lean` are fixed.

* A unit vector `e ∈ ℝ^d` is fixed.
* `e.u.k.y.def` sets
  `u_{k,y} = v_{L'}(·, y+cu_k, 0, shom_{L',*}^{1/2}(cu_n) e)`, the maximizer of
  the variational problem `e.J.def` formed with the cutoff coefficient `a_{L'}`
  on the translated cube `y + cu_k`, in the pure-flux slot `(p, q) = (0, Q)`
  with `Q = shom_{L',*}^{1/2}(cu_n) e`.
* `e.Sec3.p.q.def` sets `p = shom_{L',*}^{-1/2}(cu_n) e` and
  `q = E[(a_ℓ ∇u_n)_{cu_ℓ}]`.
* `e.p-bound-crude` records `|p| ≤ nu^{-1/2}`.
* `e.average.of.vn` records `E[(∇u_n)_{z+cu_n}] = p`.
* `e.v.ky.energy` records the energy normalization
  `‖∇u_k‖²_{L̲²(z+cu_k)} = 2 nu⁻¹ J_{L'}(z+cu_k, 0, Q)`
  `= nu⁻¹ Q · s_{L',*}^{-1}(z+cu_k) Q ≤ nu⁻² shom_{L',*}(cu_n)`.
* `e.def.w` defines the Dirichlet response `w ∈ H²(cu_m)` by
  `−Δw = (f_{L'} − f_{ℓ'})·p = ∇·((k_{L'} − k_{ℓ'}) p)` in `cu_m`,
  `w = 0` on `∂cu_m` (here `F = (k_{L'} − k_{ℓ'})p`).

## The scalar square roots

Under J4 the annealed lower-right block on an origin cube is the scalar matrix
`shom_{L',*}^{-1}(cu_n) Id` (`sigmaBarStarInv_originCube_eq_smul_one`), so both
`shom_{L',*}^{-1/2}(cu_n)` and `shom_{L',*}^{1/2}(cu_n)` are scalars: the former
is `Real.sqrt (sigmaBarStarInvSeq nu L' P n)` and the latter its inverse. The
two source vectors are therefore scalar multiples of `e`, and the identity
`|p|² = shom_{L',*}^{-1}(cu_n)` used throughout the proof is
`vecNormSq_testVector` below.

## What is a definition and what is a source input

`setupMaximizer` is the Chapter 2 canonical maximizer of `CoarseGraining`, whose
existence theory `Book.Ch02.responseExistenceTheory` is a proved theorem there;
the characterization theorems of the `Maximizer` section are the properties the
source uses (`IsResponseMaximizer`, the mean-zero gauge, the averaged gradient
and flux of `e.v.spatial.averages`, and the response value of `e.J.mat`).

`IsDirichletResponse` renders `e.def.w` as the Dirichlet response of the flux
field `F = (k_{L'} − k_{ℓ'}) p` on the open cube, i.e. as
`IsCubeDirichletResponse` of `Section3/ResponseFields/Definitions.lean`: the
print poses `−Δw = ∇·F` (with `f_j = ∇·k_j` the row divergence of the stream
matrix, no transpose), whose weak form is
`∫ ∇w·∇φ = −∫ F·∇φ`, i.e. the zero-trace Dirichlet problem of
`Homogenization.PDE.DirichletRHS` for the coefficient `Id` and forcing `−F`.
None of the following is assumed below: the existence of a solution, its
uniqueness, and the `H²(cu_m)` regularity that the paper asserts on a cube
with corners.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The scalar square roots of the annealed lower block -/

section Scalars

variable [NeZero d]

/-- `shom_{L',*}^{-1/2}(cu_n)`, the scalar square root of the annealed
lower-right block on the cube `cu_n` at cutoff `L'`. -/
def sigmaBarStarInvSqrt (nu : ℝ) (LPrime : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) : ℝ :=
  Real.sqrt (sigmaBarStarInvSeq nu LPrime P n)

/-- **`p = shom_{L',*}^{-1/2}(cu_n) e`**, the first half of `e.Sec3.p.q.def`. -/
def testVector (nu : ℝ) (LPrime : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℕ) (e : Vec d) : Vec d :=
  sigmaBarStarInvSqrt nu LPrime P n • e

/-- **`Q = shom_{L',*}^{1/2}(cu_n) e`**, the flux slot of `e.u.k.y.def`. -/
def fluxSlot (nu : ℝ) (LPrime : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℕ) (e : Vec d) : Vec d :=
  (sigmaBarStarInvSqrt nu LPrime P n)⁻¹ • e

omit [NeZero d] in
private theorem vecNormSqSmulS (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  show vecDot (c • x) (c • x) = c ^ 2 * vecDot x x
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

variable {nu : ℝ} (hnu : 0 < nu) (LPrime : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

theorem sigmaBarStarInvSqrt_pos (n : ℕ) : 0 < sigmaBarStarInvSqrt nu LPrime P n :=
  Real.sqrt_pos.2 (sigmaBarStarInvSeq_pos hnu LPrime hPrefix hJ2 hJ3 hJ4 n)

theorem sq_sigmaBarStarInvSqrt (n : ℕ) :
    sigmaBarStarInvSqrt nu LPrime P n ^ 2 = sigmaBarStarInvSeq nu LPrime P n :=
  Real.sq_sqrt (sigmaBarStarInvSeq_pos hnu LPrime hPrefix hJ2 hJ3 hJ4 n).le

/-- **`|p|² = shom_{L',*}^{-1}(cu_n)`** for a unit vector `e`, the identity the
source uses repeatedly. -/
theorem vecNormSq_testVector (n : ℕ) {e : Vec d} (he : vecNormSq e = 1) :
    vecNormSq (testVector nu LPrime P n e) = sigmaBarStarInvSeq nu LPrime P n := by
  rw [testVector, vecNormSqSmulS, he, mul_one,
    sq_sigmaBarStarInvSqrt hnu LPrime hPrefix hJ2 hJ3 hJ4 n]

/-- **`|Q|² = shom_{L',*}(cu_n)`** for a unit vector `e`: the flux slot of
`e.u.k.y.def` has squared length the annealed running diffusivity at `cu_n`. -/
theorem vecNormSq_fluxSlot (n : ℕ) {e : Vec d} (he : vecNormSq e = 1) :
    vecNormSq (fluxSlot nu LPrime P n e) = (sigmaBarStarInvSeq nu LPrime P n)⁻¹ := by
  have hpos := sigmaBarStarInvSqrt_pos hnu LPrime hPrefix hJ2 hJ3 hJ4 n
  rw [fluxSlot, vecNormSqSmulS, he, mul_one, inv_pow,
    sq_sigmaBarStarInvSqrt hnu LPrime hPrefix hJ2 hJ3 hJ4 n]

end Scalars

/-! ## The maximizers `u_{k,y}` -/

section Maximizer

/-- **`e.u.k.y.def`**: the maximizer of the variational
problem `J(U, 0, Q; a)` in the pure-flux slot, taken in the mean-zero gauge of
the Chapter 2 canonical maximizer. With `U = y + cu_k`, `a = a_{L'}` and
`Q = shom_{L',*}^{1/2}(cu_n) e` this is `u_{k,y}`. -/
def setupMaximizer (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (Q : Vec d) :
    Book.Ch02.CanonicalMaximizer U a 0 Q :=
  Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) 0 Q

variable (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (Q : Vec d)

/-- The defining property of `u_{k,y}`: it maximizes the response functional in
the slot `(0, Q)`. -/
theorem isResponseMaximizer_setupMaximizer :
    Book.Ch02.IsResponseMaximizer U a 0 Q (setupMaximizer U a Q).toSolution :=
  (setupMaximizer U a Q).isMaximizer

/-- **`e.v.spatial.averages` in the pure-flux slot**, the quenched precursor of
`e.average.of.vn`: the averaged gradient of `u_{k,y}` over the
cube is `s_{L',*}^{-1}(U) Q`. -/
theorem averageGradient_setupMaximizer :
    Book.Ch02.averageGradient U a (setupMaximizer U a Q).toSolution =
      matVecMul (Book.Ch02.sigmaStarInvCoarse U a) Q := by
  rw [setupMaximizer, Book.Ch02.averageGradient_canonicalMaximizer_eq,
    matVecMul_zero, add_zero, neg_zero, zero_add]

/-- The averaged flux of `u_{k,y}` over the cube, the second line of
`e.solution.avg.grad.flux.identity` in the pure-flux slot. -/
theorem averageFlux_setupMaximizer :
    Book.Ch02.averageFlux U a (setupMaximizer U a Q).toSolution =
      Q - matVecMul (matTranspose (Book.Ch02.kappaCoarse U a))
        (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) Q) := by
  rw [setupMaximizer, Book.Ch02.averageFlux_canonicalMaximizer_eq, matVecMul_zero,
    sub_zero]

/-- **The second equality of `e.v.ky.energy`**: the response
value of the pure-flux problem is `J(U, 0, Q) = (1/2) Q · s_*^{-1}(U) Q`. -/
theorem responseJ_setupMaximizer :
    Book.Ch02.responseJ U a 0 Q =
      (1 / 2 : ℝ) * vecDot Q (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) Q) :=
  Book.Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse U a Q

/-- **The last inequality of `e.v.ky.energy`**: the crude ellipticity
bound `s_{L',*}^{-1}(U) ≤ nu⁻¹ Id` of `e.CG.bounds.1`, valid in every domain `U`,
turns the response value into `2 nu⁻¹ J(U, 0, Q) ≤ nu⁻² |Q|²`. With
`Q = shom_{L',*}^{1/2}(cu_n) e` and `|e| = 1` the right side is
`nu⁻² shom_{L',*}(cu_n)`, the printed bound. -/
theorem two_mul_inv_mul_responseJ_le {nu : ℝ} (hnu : 0 < nu)
    (hcrude : MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse U a) (nu⁻¹ • (1 : Mat d))) :
    2 * nu⁻¹ * Book.Ch02.responseJ U a 0 Q ≤ nu⁻¹ * nu⁻¹ * vecNormSq Q := by
  have hQ := hcrude Q
  have hone : vecDot Q (matVecMul (nu⁻¹ • (1 : Mat d)) Q) = nu⁻¹ * vecNormSq Q := by
    have hmv : matVecMul (1 : Mat d) Q = Q := by
      funext i
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [smul_matVecMul, vecDot_smul_right, hmv]
    rfl
  rw [hone] at hQ
  rw [responseJ_setupMaximizer U a Q]
  have hinv : 0 < nu⁻¹ := inv_pos.2 hnu
  have hmul := mul_le_mul_of_nonneg_left hQ hinv.le
  have hexp : 2 * nu⁻¹ * ((1 / 2 : ℝ) *
      vecDot Q (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) Q)) =
      nu⁻¹ * ((1 / 2 : ℝ) *
        vecDot Q (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) Q)) * 2 := by ring
  rw [hexp]
  have hgoal : nu⁻¹ * ((1 / 2 : ℝ) * (nu⁻¹ * vecNormSq Q)) * 2 =
      nu⁻¹ * nu⁻¹ * vecNormSq Q := by ring
  rw [← hgoal]
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  exact mul_le_mul_of_nonneg_right hmul h2

end Maximizer

/-! ## The Dirichlet response `w` -/

section DirichletResponse

open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields

/-- `Id · ξ = ξ` for the Euclidean carrier's matrix action. -/
private theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem setIntegral_vecDot_neg {F G : Vec d → Vec d} (U : Set (Vec d)) :
    ∫ x in U, vecDot (-F x) (G x) ∂MeasureTheory.volume
      = -∫ x in U, vecDot (F x) (G x) ∂MeasureTheory.volume := by
  rw [← integral_neg]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp [vecDot, Finset.sum_neg_distrib]

private theorem setIntegral_vecDot_matVecMul_one (U : Set (Vec d)) (u phi : H10Function U) :
    ∫ x in U, vecDot (matVecMul (1 : Mat d) (u.toH1Function.grad x))
        (phi.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x)
        ∂MeasureTheory.volume := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  exact congrArg (fun v => vecDot v (phi.toH1Function.grad x)) (matVecMul_one _)

/-- **`e.def.w`**: `w ∈ H¹₀(cu_m)` solves
`−Δw = (f_{L'} − f_{ℓ'})·p = ∇·((k_{L'} − k_{ℓ'}) p)` in `cu_m` with zero
boundary values.

Here `f_j = ∇·k_j` is the row divergence of the stream matrix,
so `(f_{L'} − f_{ℓ'})·p = ∇·((k_{L'} − k_{ℓ'}) p)` with **no transpose**.
The distributional reading of `−Δw = ∇·F` at
`F = (k_{L'} − k_{ℓ'}) p` tests against `φ ∈ H¹₀(cu_m)` as
`∫_{cu_m} ∇w·∇φ = −∫_{cu_m} F·∇φ`, i.e. the zero-trace Dirichlet problem of
`Homogenization.PDE.DirichletRHS` with coefficient `Id` and forcing `−F`, which
is exactly `IsCubeDirichletResponse` of `Section3/ResponseFields/Definitions.lean`
for the flux field `F` on the open cube; the predicate below *is* that
predicate, definitionally.

Existence of such a `w`, its uniqueness, and the `H²(cu_m)` regularity that the
source asserts on a cube with corners are not assumed by this predicate. -/
def IsDirichletResponse (omega : ShellSeq d) (LPrime ellPrime m : ℕ) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (m : ℤ)))) : Prop :=
  IsCubeDirichletResponse (originCube d (m : ℤ))
    (fun x => matVecMul (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) p) w

/-- The weak formulation of `e.def.w` written out: the defining identity that
`IsDirichletResponse` asserts for every zero-trace test function,
`∫_{cu_m} ∇w·∇φ = −∫_{cu_m} ((k_{L'} − k_{ℓ'}) p)·∇φ`. -/
theorem isDirichletResponse_iff (omega : ShellSeq d) (LPrime ellPrime m : ℕ)
    (p : Vec d) (w : H10Function (openCubeSet (originCube d (m : ℤ)))) :
    IsDirichletResponse omega LPrime ellPrime m p w ↔
      ∀ phi : H10Function (openCubeSet (originCube d (m : ℤ))),
        ∫ x in openCubeSet (originCube d (m : ℤ)),
            vecDot (w.toH1Function.grad x)
              (phi.toH1Function.grad x) ∂MeasureTheory.volume =
          -∫ x in openCubeSet (originCube d (m : ℤ)),
            vecDot
              (matVecMul (streamCutoff omega LPrime x -
                streamCutoff omega ellPrime x) p)
              (phi.toH1Function.grad x) ∂MeasureTheory.volume :=
  Iff.rfl

/-- `IsDirichletResponse` is CoarseGraining's zero-trace weak solution of
`-div(a ∇w) = div g` at `a = Id` and forcing `−F`, `F = (k_{L'} − k_{ℓ'}) p`:
this is the rendering of the weak form `∫ ∇w·∇φ = −∫ F·∇φ` of `e.def.w` in
`Homogenization.PDE.DirichletRHS`. -/
theorem isDirichletResponse_iff_isZeroTraceDirichletRhsWeakSolution (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (m : ℤ)))) :
    IsDirichletResponse omega LPrime ellPrime m p w ↔
      IsZeroTraceDirichletRhsWeakSolution (fun _ => (1 : Mat d))
        (openCubeSet (originCube d (m : ℤ))) w
        (fun x => -matVecMul (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) p) := by
  constructor
  · intro h phi
    refine Eq.trans ?_ (Eq.trans (h phi)
      (setIntegral_vecDot_neg
        (F := fun x => matVecMul (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) p)
        (G := phi.toH1Function.grad) (U := openCubeSet (originCube d (m : ℤ)))).symm)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    exact congrArg (fun v => vecDot v (phi.toH1Function.grad x)) (matVecMul_one _)
  · intro h phi
    exact Eq.trans (setIntegral_vecDot_matVecMul_one
      (U := openCubeSet (originCube d (m : ℤ))) w phi).symm
      (Eq.trans (h phi)
        (setIntegral_vecDot_neg
          (F := fun x => matVecMul (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) p)
          (G := phi.toH1Function.grad) (U := openCubeSet (originCube d (m : ℤ)))))

end DirichletResponse

end

end SuperdiffusionCLT.Section3.Setup
