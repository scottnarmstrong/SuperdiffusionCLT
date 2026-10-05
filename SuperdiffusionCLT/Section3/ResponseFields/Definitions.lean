/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.PDE.DirichletRHS
public import Homogenization.PDE.NeumannRHS
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PublicTheorems

/-!
# The Dirichlet and prescribed-flux Neumann responses of a flux field on a cube

The display `e.abstract.response.equations` of the paper poses on the cube `cu_M`
the two problems

> `-Δ w_D = ∇·F` in `cu_M`, `w_D = 0` on `∂cu_M`,

> `-Δ w_N = ∇·F` in `cu_M`, `n·(∇w_N + F) = 0` on `∂cu_M`,

with `w_D ∈ H¹₀(cu_M)` and `w_N ∈ H¹(cu_M)` of zero average. This file supplies
the two weak formulations and their basic theory.

## The weak formulations

Both problems are the same identity against different test classes: the
distributional reading of `-Δ w = ∇·F` is

> `∫ ∇w·∇φ = -∫ F·∇φ`,

taken over `φ ∈ H¹₀(cu_M)` for the Dirichlet problem and over all of
`H¹(cu_M)` for the Neumann problem, where the enlarged test class is exactly
what encodes the natural boundary condition `n·(∇w_N + F) = 0`. The
zero-average normalization is carried by the type
`H1MeanZeroFunction`, and testing against mean-zero functions loses nothing
because only `∇φ` appears.

This is the same reading as CoarseGraining's
`Homogenization.IsZeroTraceDirichletRhsWeakSolution` and
`Homogenization.IsMeanZeroNeumannRhsWeakSolution` at the identity coefficient
field and forcing `-F`; the two bridge theorems below record the
identification, and existence and uniqueness are imported through them.

## The domain

The boundary-value problems are posed on the *open* cube `openCubeSet Q`,
because `IsOpenBoundedConvexDomain` — the hypothesis of every solvability and
Poincaré input in CoarseGraining — fails for the half-open `cubeSet Q`. The
volume-normalized norms of `Section3/ResponseFields/Norms.lean` are taken
against `cubeSet Q`; the two restrictions of Lebesgue measure agree
(`Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet`), so
no analytic content is lost, but the two set-level presentations are not
definitionally equal and a consumer must transport explicitly.

## Main definitions

* `IsCubeDirichletResponse`: the first problem of `e.abstract.response.equations`.
* `IsCubeNeumannResponse`: the second one, with the zero-average normalization.

## Main results

* `isCubeDirichletResponse_iff`, `isCubeNeumannResponse_iff`: the bridges to
  the CoarseGraining weak formulations at the identity coefficient field.
* `exists_isCubeDirichletResponse`, `exists_isCubeNeumannResponse`: solvability
  on every triadic cube for every `L²` flux.
* `gradToVectorL2_eq_of_isCubeDirichletResponse`,
  `gradToVectorL2_eq_of_isCubeNeumannResponse`: uniqueness of the response
  gradient in `L²`.
* `setIntegral_vecDot_grad_neumann_dirichlet`: the mixed term of Step 1 of the
  proof, `∫ ∇w_N·∇w_D = ∫ |∇w_D|²`.
* `setIntegral_energy_gap`, `volumeAverage_energy_gap`: the exact gap identity
  `e.energy.quadratic.N.D` (`#pythagoras`), in the plain and
  volume-normalized forms.
* `isCubeDirichletResponse_sub_const`: the Dirichlet half of
  `#centered-flux-responses`: constants disappear under the
  divergence.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- `IsFiniteMeasure` on an open triadic cube, the instance every mean-zero and
Poincaré input of CoarseGraining requires. -/
instance instIsFiniteMeasureVolumeMeasureOnOpenCubeSet (Q : TriadicCube d) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  simpa [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-! ## The two weak formulations -/

/-- **The Dirichlet response** of the flux field `F` on the cube `Q`, the first
problem of `e.abstract.response.equations`: `w ∈ H¹₀(Q)` with
`∫_Q ∇w·∇φ = -∫_Q F·∇φ` for every `φ ∈ H¹₀(Q)`. The zero boundary value is
carried by the type of `w`. -/
def IsCubeDirichletResponse (Q : TriadicCube d) (F : Vec d → Vec d)
    (w : H10Function (openCubeSet Q)) : Prop :=
  ∀ φ : H10Function (openCubeSet Q),
    ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) =
      -∫ x in openCubeSet Q, vecDot (F x) (φ.toH1Function.grad x)

/-- **The prescribed-flux Neumann response** of the flux field `F` on the cube
`Q`, the second problem of `e.abstract.response.equations`:
`w ∈ H¹(Q)` of zero average with `∫_Q ∇w·∇φ = -∫_Q F·∇φ` for every
`φ ∈ H¹(Q)`. The enlarged test class is the natural boundary condition
`n·(∇w + F) = 0`, and the zero-average normalization is carried by
the type of `w`. -/
def IsCubeNeumannResponse (Q : TriadicCube d) (F : Vec d → Vec d)
    (w : H1MeanZeroFunction (openCubeSet Q)) : Prop :=
  ∀ φ : H1MeanZeroFunction (openCubeSet Q),
    ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) =
      -∫ x in openCubeSet Q, vecDot (F x) (φ.toH1Function.grad x)

/-! ## The bridges to the CoarseGraining weak formulations -/

private theorem setIntegral_vecDot_neg (Q : TriadicCube d) (F G : Vec d → Vec d) :
    ∫ x in openCubeSet Q, vecDot (-F x) (G x) =
      -∫ x in openCubeSet Q, vecDot (F x) (G x) := by
  rw [← integral_neg]
  refine setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => ?_)
  simp [vecDot, Finset.sum_neg_distrib]

/-- The Dirichlet response is CoarseGraining's zero-trace weak solution of
`-div(a ∇w) = div g` at `a = I` and `g = -F`. -/
theorem isCubeDirichletResponse_iff (Q : TriadicCube d) (F : Vec d → Vec d)
    (w : H10Function (openCubeSet Q)) :
    IsCubeDirichletResponse Q F w ↔
      IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
        (openCubeSet Q) w (fun x => -F x) := by
  constructor
  · intro h φ
    rw [show (fun x => vecDot
        (matVecMul (identityCoeffField d x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x)) =
      fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) from
        funext fun x => by rw [matVecMul_identityCoeffField]]
    rw [setIntegral_vecDot_neg]
    exact h φ
  · intro h φ
    have hφ := h φ
    rw [show (fun x => vecDot
        (matVecMul (identityCoeffField d x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x)) =
      fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) from
        funext fun x => by rw [matVecMul_identityCoeffField]] at hφ
    rw [setIntegral_vecDot_neg] at hφ
    exact hφ

/-- The Neumann response is CoarseGraining's mean-zero weak solution of
`-div(a ∇w) = div g` at `a = I` and `g = -F`. -/
theorem isCubeNeumannResponse_iff (Q : TriadicCube d) (F : Vec d → Vec d)
    (w : H1MeanZeroFunction (openCubeSet Q)) :
    IsCubeNeumannResponse Q F w ↔
      IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
        (openCubeSet Q) w (fun x => -F x) := by
  constructor
  · intro h φ
    rw [show (fun x => vecDot
        (matVecMul (identityCoeffField d x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x)) =
      fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) from
        funext fun x => by rw [matVecMul_identityCoeffField]]
    rw [setIntegral_vecDot_neg]
    exact h φ
  · intro h φ
    have hφ := h φ
    rw [show (fun x => vecDot
        (matVecMul (identityCoeffField d x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x)) =
      fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) from
        funext fun x => by rw [matVecMul_identityCoeffField]] at hφ
    rw [setIntegral_vecDot_neg] at hφ
    exact hφ

/-! ## Solvability -/

private theorem isEllipticFieldOn_identity_openCubeSet (Q : TriadicCube d) :
    IsEllipticFieldOn 1 1 (openCubeSet Q) (identityCoeffField d) :=
  isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)

/-- **Solvability of the Dirichlet problem on a cube.** Every `L²` flux field on
`openCubeSet Q` has a Dirichlet response, by CoarseGraining's Lax-Milgram
construction together with the realization of the potential zero-trace closure
on a bounded open convex domain. -/
theorem exists_isCubeDirichletResponse [NeZero d] (Q : TriadicCube d)
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    ∃ w : H10Function (openCubeSet Q), IsCubeDirichletResponse Q F w := by
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := identityCoeffField d) (U := openCubeSet Q) (g := fun x => -F x)
      (lam := 1) (Lam := 1) hF.neg hRealize (openCubeSet_nonempty_internal Q)
      (isEllipticFieldOn_identity_openCubeSet Q)
  exact ⟨w, (isCubeDirichletResponse_iff Q F w).2 hw⟩

/-- **Solvability of the prescribed-flux Neumann problem on a cube.** Every `L²`
flux field on `openCubeSet Q` has a zero-average Neumann response, by
CoarseGraining's mean-zero Lax-Milgram construction together with the
scale-correct cube Poincaré-Wirtinger estimate. -/
theorem exists_isCubeNeumannResponse (Q : TriadicCube d)
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    ∃ w : H1MeanZeroFunction (openCubeSet Q), IsCubeNeumannResponse Q F w := by
  obtain ⟨w, hw⟩ :=
    exists_isMeanZeroNeumannRhsWeakSolution_of_h1CoerciveEstimate
      (a := identityCoeffField d) (U := openCubeSet Q) (g := fun x => -F x)
      (lam := 1) (Lam := 1) hF.neg (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q) (isEllipticFieldOn_identity_openCubeSet Q)
  exact ⟨w, (isCubeNeumannResponse_iff Q F w).2 hw⟩

/-! ## Uniqueness of the response gradient -/

/-- Two Dirichlet responses of the same flux have the same gradient in `L²`. -/
theorem gradToVectorL2_eq_of_isCubeDirichletResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {u v : H10Function (openCubeSet Q)}
    (hu : IsCubeDirichletResponse Q F u) (hv : IsCubeDirichletResponse Q F v) :
    u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 :=
  IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
    (openCubeSet_nonempty_internal Q)
    ((isCubeDirichletResponse_iff Q F u).1 hu)
    ((isCubeDirichletResponse_iff Q F v).1 hv)
    (isEllipticFieldOn_identity_openCubeSet Q)

/-- Two Neumann responses of the same flux have the same gradient in `L²`. -/
theorem gradToVectorL2_eq_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {u v : H1MeanZeroFunction (openCubeSet Q)}
    (hu : IsCubeNeumannResponse Q F u) (hv : IsCubeNeumannResponse Q F v) :
    u.toH1Function.gradToVectorL2 = v.toH1Function.gradToVectorL2 :=
  IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
    (openCubeSet_nonempty_internal Q)
    ((isCubeNeumannResponse_iff Q F u).1 hu)
    ((isCubeNeumannResponse_iff Q F v).1 hv)
    (isEllipticFieldOn_identity_openCubeSet Q)

/-! ## The exact energy gap identity -/

/-- **The mixed term of Step 1**: testing the Neumann equation
with the Dirichlet response, which is admissible after subtracting its average,
and then using the Dirichlet equation, gives
`∫ ∇w_N·∇w_D = ∫ ∇w_D·∇w_D`. -/
theorem setIntegral_vecDot_grad_neumann_dirichlet {Q : TriadicCube d}
    {F : Vec d → Vec d} {wN : H1MeanZeroFunction (openCubeSet Q)}
    {wD : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q F wN) (hD : IsCubeDirichletResponse Q F wD) :
    ∫ x in openCubeSet Q,
        vecDot (wN.toH1Function.grad x) (wD.toH1Function.grad x) =
      ∫ x in openCubeSet Q,
        vecDot (wD.toH1Function.grad x) (wD.toH1Function.grad x) := by
  have hgrad :
      (H1Function.toMeanZero wD.toH1Function).toH1Function.grad =
        wD.toH1Function.grad := by
    funext x
    exact H1Function.grad_subAverage wD.toH1Function x
  have hNtest := hN (H1Function.toMeanZero wD.toH1Function)
  rw [hgrad] at hNtest
  rw [hNtest, hD wD]

/-- **The exact Dirichlet-Neumann gap identity** `e.energy.quadratic.N.D`,
in the plain integral form:
`∫|∇w_N − ∇w_D|² = ∫|∇w_N|² − ∫|∇w_D|²`. -/
theorem setIntegral_energy_gap {Q : TriadicCube d} {F : Vec d → Vec d}
    {wN : H1MeanZeroFunction (openCubeSet Q)} {wD : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q F wN) (hD : IsCubeDirichletResponse Q F wD) :
    ∫ x in openCubeSet Q,
        vecNormSq (wN.toH1Function.grad x - wD.toH1Function.grad x) =
      (∫ x in openCubeSet Q, vecNormSq (wN.toH1Function.grad x)) -
        ∫ x in openCubeSet Q, vecNormSq (wD.toH1Function.grad x) := by
  have hNN : IntegrableOn
      (fun x => vecDot (wN.toH1Function.grad x) (wN.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 wN.toH1Function.grad_memVectorL2
      wN.toH1Function.grad_memVectorL2
  have hND : IntegrableOn
      (fun x => vecDot (wN.toH1Function.grad x) (wD.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 wN.toH1Function.grad_memVectorL2
      wD.toH1Function.grad_memVectorL2
  have hDD : IntegrableOn
      (fun x => vecDot (wD.toH1Function.grad x) (wD.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 wD.toH1Function.grad_memVectorL2
      wD.toH1Function.grad_memVectorL2
  have hpt : ∀ x : Vec d,
      vecNormSq (wN.toH1Function.grad x - wD.toH1Function.grad x) =
        vecDot (wN.toH1Function.grad x) (wN.toH1Function.grad x) -
          2 * vecDot (wN.toH1Function.grad x) (wD.toH1Function.grad x) +
          vecDot (wD.toH1Function.grad x) (wD.toH1Function.grad x) := by
    intro x
    simp only [vecNormSq, vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmix : IntegrableOn
      (fun x => vecDot (wN.toH1Function.grad x) (wN.toH1Function.grad x) -
        2 * vecDot (wN.toH1Function.grad x) (wD.toH1Function.grad x))
      (openCubeSet Q) := hNN.sub (hND.const_mul 2)
  rw [setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => hpt x),
    integral_add hmix hDD, integral_sub hNN (hND.const_mul 2),
    integral_const_mul, setIntegral_vecDot_grad_neumann_dirichlet hN hD]
  simp only [vecNormSq]
  ring

/-- **The exact Dirichlet-Neumann gap identity** `e.energy.quadratic.N.D`
in the volume-normalized form:
`‖∇w_N − ∇w_D‖²_{L̲²} = ‖∇w_N‖²_{L̲²} − ‖∇w_D‖²_{L̲²}`. -/
theorem volumeAverage_energy_gap {Q : TriadicCube d} {F : Vec d → Vec d}
    {wN : H1MeanZeroFunction (openCubeSet Q)} {wD : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q F wN) (hD : IsCubeDirichletResponse Q F wD) :
    volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (wN.toH1Function.grad x - wD.toH1Function.grad x)) =
      volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (wN.toH1Function.grad x)) -
        volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (wD.toH1Function.grad x)) := by
  simp only [volumeAverage]
  rw [setIntegral_energy_gap hN hD, mul_sub]

/-! ## The centered flux -/

/-- **The Dirichlet half of `#centered-flux-responses`**:
constants disappear under the divergence, so the Dirichlet response of `F` is
also the Dirichlet response of `F − c` for every constant vector `c`. -/
theorem isCubeDirichletResponse_sub_const {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H10Function (openCubeSet Q)}
    (hF : MemVectorL2 (openCubeSet Q) F)
    (h : IsCubeDirichletResponse Q F w) (c : Vec d) :
    IsCubeDirichletResponse Q (fun x => F x - c) w := by
  intro φ
  have hzero : ∫ x in openCubeSet Q, vecDot c (φ.toH1Function.grad x) = 0 :=
    integral_vecDot_const_zeroTraceGrad_eq_zero φ c
  have hcL2 : MemVectorL2 (openCubeSet Q) (fun _ : Vec d => c) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q)) (c := c)
  have hFint : IntegrableOn
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hcint : IntegrableOn
      (fun x => vecDot c (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hcL2 φ.toH1Function.grad_memVectorL2
  have hsplit : ∀ x : Vec d,
      vecDot (F x - c) (φ.toH1Function.grad x) =
        vecDot (F x) (φ.toH1Function.grad x) -
          vecDot c (φ.toH1Function.grad x) := by
    intro x
    simp only [vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => hsplit x),
    integral_sub hFint hcint, hzero, sub_zero]
  exact h φ

end

end ResponseFields
end Section3
end SuperdiffusionCLT
