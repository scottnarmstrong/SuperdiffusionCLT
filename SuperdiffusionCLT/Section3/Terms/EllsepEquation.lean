/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.MasterIdentity
public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Sobolev.DirichletW2pDivergence
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB

/-!
# The equation `e.ellsep` and the integration by parts leading to `e.ellsep.testing`

The paper writes the equation `e.ellsep` satisfied by
the maximizer `u_m = u_{m,0}` of `e.u.k.y.def` as

`−∇·a_ℓ∇u_m = (f_{L'} − f_ℓ)·∇u_m` in `cu_m`.

This is not an extra assumption on `u_m`: the maximizer of `e.J.def` ranges over
the set `A(U)` of solutions of `∇·a_{L'}∇u = 0` in `U`,
so `u_m` solves that equation by construction, and `e.ellsep` is what the same
equation reads after `a_{L'} = a_ℓ + (k_{L'} − k_ℓ)` is substituted and the
divergence is moved off the stream increment.

## What is proved here

* `isSolenoidalOn_coefficientCutoff_cubeMaximizerGradient` — the weak form
  `∫_{cu_m} ∇φ·a_{L'}∇u_m = 0`, for every zero-trace test `φ`, of the maximizer
  `cubeMaximizer` of `GluedField.lean`.  It is the solenoidality half of the
  Chapter 2 carrier `Book.Ch02.Solution U a = AHarmonicFunction a U`, so the
  equation `e.ellsep` *is* exposed by the maximizer's characterization
  and needs no hypothesis.
* `volumeAverage_vecDot_coefficientCutoff_of_isSolenoidalOn` — the same identity after the
  substitution `a_{L'} = a_ℓ + (k_{L'} − k_ℓ)`:
  `⨍_{cu_m} ∇φ·a_ℓ∇u_m = −⨍_{cu_m} ∇φ·(k_{L'} − k_ℓ)∇u_m`.
* `memL2On_openCubeSet_of_continuous`, `weakDivergence_streamFluxWeakGradient` —
  `∇·((k_b − k_a)p) = (f_b − f_a)·p`
  for the classical Jacobian of the upper-shell flux, the identity that reads
  the drift `f = ∇·k` of `Drift.lean` off the weak Jacobian of
  `RegboundsInputsB.lean`.
* `volumeAverage_zeroTrace_mul_drift_sub` — **the integration by parts** leading
  to `e.ellsep.testing`, in the general form
  `⨍_U w (f_b − f_a)·V = −⨍_U ((k_b − k_a)V)·∇w` for `w ∈ H¹₀(U)`, given a
  weak Jacobian of the field `(k_b − k_a)V` whose divergence is `(f_b − f_a)·V`.
* `volumeAverage_zeroTrace_mul_drift_sub_const` — the same identity for a
  constant vector `V ≡ p`, where the weak Jacobian is the classical one
  and no hypothesis remains.

## What is carried

For a *non-constant* `V` the divergence datum is a hypothesis.  With
`V = ∇u_m` the paper's integration by parts asserts

`∇·((k_{L'} − k_ℓ)∇u_m) = (f_{L'} − f_ℓ)·∇u_m`,

i.e. that the contraction of the antisymmetric matrix `k_{L'} − k_ℓ` with the
Hessian of `u_m` vanishes.  Two inputs are needed for it: `∇u_m ∈ H¹(cu_m)` (an `H²` bound for the
maximizer, which the Chapter 2 response theory of `CoarseGraining` does not produce — the carrier
`Book.Ch02.Solution` stores `toH1 : H1Function U` and nothing above it), and a
product rule for the weak derivative of `K·V` with `K` of class `C¹` and
`V ∈ H¹` (`Homogenization.HasWeakPartialDerivOn` tests against smooth compactly
supported functions only, and no such product rule is available there).  So the
datum is taken as the explicit hypotheses `hJac`, `hDiv` in the exact shape of
`DirichletW2pDivergence.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Sobolev

noncomputable section

variable {d : ℕ}

/-! ## The weak form of `e.ellsep` -/

/-- **`e.ellsep`** in weak form
for the maximizer: the cube maximizer `u_{k,z}` of `e.u.k.y.def` is a
Chapter 2 solution for the coefficient `a_L`, so its flux is solenoidal against
every zero-trace test function,

`∫_{z} (a_L ∇u_{k,z})·∇φ = 0`.

This is the solenoidality half of `Book.Ch02.Solution U a`, which is
`AHarmonicFunction a.toCoeffField U`; the constraint set `A(U)` of `e.J.def`
is exactly this predicate, so the equation is part of
the maximizer's characterization and no hypothesis is needed. -/
theorem isSolenoidalOn_coefficientCutoff_cubeMaximizerGradient {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    IsSolenoidalOn (openCubeSet z)
      (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
        (cubeMaximizerGradient hnu omega L F z x)) :=
  (cubeMaximizer hnu omega L F z).toSolution.isHarmonic.2

/-! ## `L²` data from continuity on a cube -/

/-- A continuous scalar field is square-integrable on an open triadic cube: the
cube sits in a compact ball on which the field is bounded, and the cube has
finite measure. -/
theorem memL2On_openCubeSet_of_continuous (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : Continuous f) : MemL2On (openCubeSet Q) f := by
  have hsub : openCubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    ProperSpace.isCompact_closedBall _ _
  have hbdd : BddAbove ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    hK.bddAbove_image hf.norm.continuousOn
  refine MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable
    (sSup ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q))) ?_
  filter_upwards
    [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with y hy
  exact le_csSup hbdd (Set.mem_image_of_mem _ (hsub hy))

/-! ## The divergence of the upper-shell flux is the drift -/

/-- The increment of the stored cutoff derivative over `(a, b]`. -/
private theorem streamCutoffDerivSub (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (x : Vec d) :
    streamCutoffDeriv omega b x - streamCutoffDeriv omega a x
      = ∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x := by
  have hdisj : Disjoint (Finset.range (a + 1)) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ioc] at hk'
    omega
  have hunion : Finset.range (a + 1) ∪ Finset.Ioc a b = Finset.range (b + 1) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hsplit : ∑ n ∈ Finset.range (b + 1), ShellField.deriv (omega n) x
      = ∑ n ∈ Finset.range (a + 1), ShellField.deriv (omega n) x
        + ∑ n ∈ Finset.Ioc a b, ShellField.deriv (omega n) x := by
    rw [← hunion, Finset.sum_union hdisj]
  show (∑ n ∈ Finset.range (b + 1), ShellField.deriv (omega n) x)
      - (∑ n ∈ Finset.range (a + 1), ShellField.deriv (omega n) x) = _
  rw [hsplit]
  abel

/-- The coordinate reading of the drift increment: `(f_b − f_a)_k` is the trace
of the derivative increment against the coordinate directions. -/
private theorem driftCutoffSubApply (omega : ShellSeq d) (a b : ℕ) (x : Vec d)
    (k : Fin d) :
    driftCutoff omega b x k - driftCutoff omega a x k
      = ∑ i : Fin d,
          ((streamCutoffDeriv omega b x - streamCutoffDeriv omega a x)
            (basisVec i)) i k := by
  show (∑ i : Fin d, streamCutoffDeriv omega b x (Pi.single i 1) i k)
      - (∑ i : Fin d, streamCutoffDeriv omega a x (Pi.single i 1) i k) = _
  rw [← Finset.sum_sub_distrib]
  rfl

/-- **`∇·((k_b − k_a)p) = (f_b − f_a)·p`**: the divergence of the classical
Jacobian of the upper-shell flux is the drift increment paired with `p`.  This
is the identity of the paper's drift computation read backwards, with the
row-divergence convention `(∇·A)_j = ∑_i ∂_i A_{ij}` that `Drift.lean` fixes. -/
theorem weakDivergence_streamFluxWeakGradient (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p : Vec d) (x : Vec d) :
    weakDivergence (streamFluxWeakGradient omega a b p) x
      = vecDot (driftCutoff omega b x - driftCutoff omega a x) p := by
  have hleft : weakDivergence (streamFluxWeakGradient omega a b p) x
      = ∑ i : Fin d, ∑ k : Fin d,
          ((streamCutoffDeriv omega b x - streamCutoffDeriv omega a x)
            (basisVec i)) i k * p k := by
    simp only [weakDivergence]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [streamFluxWeakGradient_apply omega hab p i x i, streamCutoffDerivSub omega hab x]
    rfl
  have hright : vecDot (driftCutoff omega b x - driftCutoff omega a x) p
      = ∑ k : Fin d, ∑ i : Fin d,
          ((streamCutoffDeriv omega b x - streamCutoffDeriv omega a x)
            (basisVec i)) i k * p k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    show (driftCutoff omega b x k - driftCutoff omega a x k) * p k = _
    rw [driftCutoffSubApply omega a b x k, Finset.sum_mul]
  rw [hleft, hright, Finset.sum_comm]

/-! ## Continuity and `L²` data of the upper-shell flux and its Jacobian -/

/-- The classical Jacobian of the upper-shell flux is continuous: the flux is of
class `C¹`. -/
theorem continuous_streamFluxWeakGradient (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p : Vec d) (i j : Fin d) :
    Continuous (fun x : Vec d => streamFluxWeakGradient omega a b p i x j) :=
  (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).continuous.comp
    ((contDiff_streamFlux_apply omega hab p i).continuous_fderiv (by simp))

/-- The drift increment paired with a constant vector is continuous, because it
is the trace of the continuous Jacobian of the upper-shell flux. -/
theorem continuous_driftCutoff_sub_vecDot (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p : Vec d) :
    Continuous (fun x : Vec d =>
      vecDot (driftCutoff omega b x - driftCutoff omega a x) p) := by
  have hrw : (fun x : Vec d => vecDot (driftCutoff omega b x - driftCutoff omega a x) p)
      = fun x : Vec d => ∑ i : Fin d, streamFluxWeakGradient omega a b p i x i := by
    funext x
    rw [← weakDivergence_streamFluxWeakGradient omega hab p x]
    rfl
  rw [hrw]
  exact continuous_finsetSum _ fun i _ => continuous_streamFluxWeakGradient omega hab p i i

/-- The coordinates of the drift increment are continuous. -/
theorem continuous_driftCutoff_sub_apply (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (k : Fin d) :
    Continuous (fun x : Vec d =>
      driftCutoff omega b x k - driftCutoff omega a x k) := by
  have hrw : (fun x : Vec d => driftCutoff omega b x k - driftCutoff omega a x k)
      = fun x : Vec d =>
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (basisVec k) := by
    funext x
    rw [vecDot_basisVec_right]
    rfl
  rw [hrw]
  exact continuous_driftCutoff_sub_vecDot omega hab (basisVec k)

/-! ## The integration by parts leading to `e.ellsep.testing` -/

/-- **The integration by parts leading to `e.ellsep.testing`**, at the level of
the set integral: for `w ∈ H¹₀(Q)`,

`∫_Q w (f_b − f_a)·V = −∫_Q ((k_b − k_a)V)·∇w`,

given a weak Jacobian `DG` of the field `(k_b − k_a)V` whose divergence is the
drift pairing `(f_b − f_a)·V`.  The hypotheses `hJac` and `hDiv` are the two
halves of the print's sentence: that the skew field `(k_b − k_a)V` has a weak
Jacobian, and that its divergence loses the Hessian contraction because
`k_b − k_a` is antisymmetric.  For a constant `V` they are discharged in
`volumeAverage_zeroTrace_mul_drift_sub_const` below. -/
theorem setIntegral_zeroTrace_mul_drift_sub {Q : TriadicCube d} (omega : ShellSeq d)
    (a b : ℕ) (V : Vec d → Vec d) (DG : Fin d → Vec d → Vec d)
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x) i))
    (hDG : ∀ i : Fin d, GradMemL2On (openCubeSet Q) (DG i))
    (hJac : HasWeakJacobianOn (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x)) DG)
    (hDiv : ∀ x ∈ openCubeSet Q, weakDivergence DG x
      = vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x))
    (w : H10Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q, w.toH1Function x *
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x) ∂volume =
      -∫ x in openCubeSet Q, vecDot
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x))
        (w.toH1Function.grad x) ∂volume := by
  have hbase := setIntegral_vecDot_zeroTrace_grad_eq_neg hFlux hDG hJac w
  have hcongr : ∫ x in openCubeSet Q, weakDivergence DG x * w.toH1Function x ∂volume
      = ∫ x in openCubeSet Q, w.toH1Function x *
          vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x) ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    rw [hDiv x hx, mul_comm]
  rw [← hcongr, hbase, neg_neg]

/-- The normalized-average form of `setIntegral_zeroTrace_mul_drift_sub`:
`⨍_Q w (f_b − f_a)·V = −⨍_Q ((k_b − k_a)V)·∇w`. -/
theorem volumeAverage_zeroTrace_mul_drift_sub {Q : TriadicCube d} (omega : ShellSeq d)
    (a b : ℕ) (V : Vec d → Vec d) (DG : Fin d → Vec d → Vec d)
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x) i))
    (hDG : ∀ i : Fin d, GradMemL2On (openCubeSet Q) (DG i))
    (hJac : HasWeakJacobianOn (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x)) DG)
    (hDiv : ∀ x ∈ openCubeSet Q, weakDivergence DG x
      = vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x))
    (w : H10Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x => w.toH1Function x *
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x)) =
      -volumeAverage (openCubeSet Q) (fun x => vecDot
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x))
        (w.toH1Function.grad x)) := by
  simp only [volumeAverage]
  rw [setIntegral_zeroTrace_mul_drift_sub omega a b V DG hFlux hDG hJac hDiv w]
  ring

/-- The `L²` data of the upper-shell flux paired with a constant vector. -/
private theorem fluxConstMemL2 (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (p : Vec d) (i : Fin d) :
    MemL2On (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) p i) :=
  memL2On_openCubeSet_of_continuous Q (continuous_streamFlux_apply omega hab p i)

/-- The `L²` data of the classical Jacobian of the upper-shell flux. -/
private theorem fluxJacobianMemL2 (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (p : Vec d) (i : Fin d) :
    GradMemL2On (openCubeSet Q) (streamFluxWeakGradient omega a b p i) :=
  fun j => memL2On_openCubeSet_of_continuous Q (continuous_streamFluxWeakGradient omega hab p i j)

/-- **The integration by parts for a constant vector**, with no
hypothesis left: for `w ∈ H¹₀(Q)` and `p ∈ ℝ^d`,

`⨍_Q w (f_b − f_a)·p = −⨍_Q ((k_b − k_a)p)·∇w`.

The weak Jacobian is the classical one of
`RegboundsInputsB.lean` and its divergence is the drift
by `weakDivergence_streamFluxWeakGradient`. -/
theorem volumeAverage_zeroTrace_mul_drift_sub_const (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (p : Vec d)
    (w : H10Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x => w.toH1Function x *
        vecDot (driftCutoff omega b x - driftCutoff omega a x) p) =
      -volumeAverage (openCubeSet Q) (fun x => vecDot
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x) p)
        (w.toH1Function.grad x)) :=
  volumeAverage_zeroTrace_mul_drift_sub omega a b (fun _ => p)
    (streamFluxWeakGradient omega a b p)
    (fluxConstMemL2 omega hab Q p) (fluxJacobianMemL2 omega hab Q p)
    (fun i => hasWeakGradientOn_streamFluxWeakGradient omega hab p i (openCubeSet Q))
    (fun x _hx => weakDivergence_streamFluxWeakGradient omega hab p x) w

/-! ## `e.ellsep` after the substitution `a_{L'} = a_ℓ + (k_{L'} − k_ℓ)` -/

private theorem matVecMulAddMatE (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  show ∑ j, (A i j + B i j) * x j = (∑ j, A i j * x j) + ∑ j, B i j * x j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`e.ellsep` in the form the master identity tests**: the
solenoidality of the flux `a_{L'} V` against zero-trace tests, rewritten with
`a_{L'} = a_ℓ + (k_{L'} − k_ℓ)`, reads

`⨍_U ∇φ·a_ℓ V = −⨍_U ∇φ·(k_{L'} − k_ℓ)V`.

The two integrability hypotheses are the side conditions of splitting the cube
integral of the sum; the substitution itself is
`coefficientCutoff_toCoeffField_add_streamCutoff_sub`. -/
theorem volumeAverage_vecDot_coefficientCutoff_of_isSolenoidalOn (nu : ℝ)
    (omega : ShellSeq d) (LPrime ell : ℕ) {U : Set (Vec d)} (V : Vec d → Vec d)
    (phi : H10Function U)
    (hEll : IsSolenoidalOn U
      (fun x => matVecMul ((coefficientCutoff nu omega LPrime).toCoeffField x) (V x)))
    (hIntA : IntegrableOn (fun x => vecDot (phi.toH1Function.grad x)
      (matVecMul ((coefficientCutoff nu omega ell).toCoeffField x) (V x))) U volume)
    (hIntK : IntegrableOn (fun x => vecDot (phi.toH1Function.grad x)
      (matVecMul (streamCutoff omega LPrime x - streamCutoff omega ell x) (V x)))
      U volume) :
    volumeAverage U (fun x => vecDot (phi.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega ell).toCoeffField x) (V x))) =
      -volumeAverage U (fun x => vecDot (phi.toH1Function.grad x)
        (matVecMul (streamCutoff omega LPrime x - streamCutoff omega ell x) (V x))) := by
  have hpt : (fun x => vecDot (matVecMul
        ((coefficientCutoff nu omega LPrime).toCoeffField x) (V x))
          (phi.toH1Function.grad x))
      = fun x => vecDot (phi.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega ell).toCoeffField x) (V x))
        + vecDot (phi.toH1Function.grad x)
          (matVecMul (streamCutoff omega LPrime x - streamCutoff omega ell x) (V x)) := by
    funext x
    rw [vecDot_comm, ← coefficientCutoff_toCoeffField_add_streamCutoff_sub nu omega
      LPrime ell x, matVecMulAddMatE, vecDot_add_right]
  have hzero := hEll phi
  rw [hpt, MeasureTheory.integral_add hIntA hIntK] at hzero
  simp only [volumeAverage]
  have hsplit : ∫ x in U, vecDot (phi.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega ell).toCoeffField x) (V x)) ∂volume
      = -∫ x in U, vecDot (phi.toH1Function.grad x)
        (matVecMul (streamCutoff omega LPrime x - streamCutoff omega ell x) (V x))
        ∂volume := by linarith only [hzero]
  rw [hsplit]
  ring

/-! ## `e.ellsep` in the drift form -/

/-- The pairing of `∇w` with the skew flux `(k_b − k_a)V` is integrable on the
cube when the flux is square-integrable coordinatewise. -/
theorem integrableOn_vecDot_grad_streamFlux {Q : TriadicCube d} (omega : ShellSeq d)
    {a b : ℕ} (V : Vec d → Vec d) (w : H10Function (openCubeSet Q))
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x) i)) :
    IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
      (matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x)))
      (openCubeSet Q) volume := by
  have hrw : (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x)))
      = fun x => ∑ i : Fin d, w.toH1Function.grad x i *
        matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x) i := rfl
  rw [hrw]
  exact MeasureTheory.integrable_finsetSum _ fun i _ =>
    (w.toH1Function.gradMemL2 i).integrable_mul (hFlux i)

end

end SuperdiffusionCLT.Section3.Terms
