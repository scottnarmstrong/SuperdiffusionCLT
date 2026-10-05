/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.EllsepEquation
public import SuperdiffusionCLT.Section3.Setup.DirichletResponse

/-!
# The four testing displays of the master identity

The paper tests the equation `e.ellsep` and the Dirichlet problem `e.def.w`
against `w` and integrates by parts.  `Section3/Terms/MasterIdentity.lean`
carries the four resulting displays as the explicit hypotheses `hTestEllsep`,
`hTestW`, `hParts`, `hPartsP` of `ellsep_testing` and
`ellsep_testing_decomposition`.  This module proves the two displays below that have no
analytic hypothesis, in exactly those shapes.

## The displays proved

* `w_testing_formula` — `e.w.testing.formula`.  Proved from
  the weak form of `e.def.w` (`Setup.IsDirichletResponse`) and the integration
  by parts of `Section3/Terms/EllsepEquation.lean` for the constant vector `p`;
  no analytic hypothesis remains, only the additivity side conditions.
* `parts_constant_term` — the integration by parts of the paper applied to the
  term carrying the constant `p`, using the antisymmetry of `k_{ℓ'}` and
  `k_ℓ`.  No analytic hypothesis remains.

## What is not proved here

The remaining two displays (`e.ellsep` tested against `w` and split at `p`, and the integration
by parts applied to the term carrying `∇u_m − p`) put a derivative on the field
`(k_{L'} − k_ℓ)∇u_m`, whose weak Jacobian is not available: it needs `∇u_m ∈ H¹(cu_m)` and a
weak product rule (see the module docstring of `Section3/Terms/EllsepEquation.lean`).  The weak
form of `e.ellsep` itself is supplied by the maximizer through
`Section3/Terms/EllsepEquation.isSolenoidalOn_coefficientCutoff_cubeMaximizerGradient`.

All other side conditions are integrability of the cube integrands.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Sobolev

noncomputable section

variable {d : ℕ}

/-! ## Algebra of the normalized cube average -/

private theorem volumeAverageAddT {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun x => f x + g x) = volumeAverage U f + volumeAverage U g := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_add hf hg]
  ring

private theorem volumeAverageNegT {U : Set (Vec d)} (f : Vec d → ℝ) :
    volumeAverage U (fun x => -f x) = -volumeAverage U f := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_neg]
  ring

/-- `p · (G)_U = ⨍_U p·G`: a constant vector passes through the normalized
vector average. -/
private theorem vecDotVolumeAverageVec {U : Set (Vec d)} (p : Vec d)
    (G : Vec d → Vec d)
    (hint : ∀ i : Fin d, IntegrableOn (fun x => G x i) U volume) :
    vecDot p (volumeAverageVec U G) = volumeAverage U (fun x => vecDot p (G x)) := by
  have hleft : vecDot p (volumeAverageVec U G)
      = ∑ i : Fin d, p i *
          ((volume U).toReal⁻¹ * ∫ x in U, G x i ∂volume) := rfl
  have hpt : (fun x => vecDot p (G x))
      = fun x => ∑ i : Fin d, p i * G x i := rfl
  have hsum : ∫ x in U, (∑ i : Fin d, p i * G x i) ∂volume
      = ∑ i : Fin d, p i * ∫ x in U, G x i ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hint i).const_mul (p i))]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  rw [hleft, show volumeAverage U (fun x => vecDot p (G x))
      = (volume U).toReal⁻¹ * ∫ x in U, vecDot p (G x) ∂volume from rfl,
    hpt, hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Antisymmetry of the stream increment -/

private theorem matVecMulNegMatT (A : Mat d) (x : Vec d) :
    matVecMul (-A) x = -matVecMul A x := by
  funext i
  show ∑ j, (-A i j) * x j = -∑ j, A i j * x j
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The stream increment is antisymmetric, being a difference of antisymmetric
matrices. -/
private theorem streamCutoffSubSkew (omega : ShellSeq d) (a b : ℕ) (x : Vec d) :
    matTranspose (streamCutoff omega b x - streamCutoff omega a x)
      = -(streamCutoff omega b x - streamCutoff omega a x) := by
  funext i k
  show streamCutoff omega b x k i - streamCutoff omega a x k i
      = -(streamCutoff omega b x i k - streamCutoff omega a x i k)
  rw [streamCutoff_skew_entry omega b x k i, streamCutoff_skew_entry omega a x k i]
  ring

/-- **The transposition identity for an antisymmetric matrix**:
`x·(K y) = −(K x)·y`.  This is the algebraic half of the integrations by parts
of the paper. -/
private theorem vecDotMatVecMulSkew {K : Mat d} (hK : matTranspose K = -K)
    (x y : Vec d) : vecDot x (matVecMul K y) = -vecDot (matVecMul K x) y := by
  have h := Homogenization.vecDot_matVecMul_transpose x y K
  rw [hK, matVecMulNegMatT, vecDot_neg_right] at h
  linarith only [h]

/-! ## `L²` data and integrability on the cube -/

private theorem memL2StreamEntry (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (i j : Fin d) :
    MemL2On (openCubeSet Q)
      (fun x => (streamCutoff omega b x - streamCutoff omega a x) i j) :=
  memL2On_openCubeSet_of_continuous Q
    ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_streamCutoff_sub omega hab)))

/-- Each coordinate of `(k_b − k_a)∇w` is integrable on the cube. -/
private theorem integrableStreamGrad (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (i : Fin d) :
    IntegrableOn (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x)
      (w.toH1Function.grad x) i) (openCubeSet Q) volume := by
  have hterm : ∀ j : Fin d, IntegrableOn
      (fun x => (streamCutoff omega b x - streamCutoff omega a x) i j *
        w.toH1Function.grad x j) (openCubeSet Q) volume := fun j =>
    (memL2StreamEntry omega hab Q i j).integrable_mul (w.toH1Function.gradMemL2 j)
  have hrw : (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x)
        (w.toH1Function.grad x) i)
      = fun x => ∑ j : Fin d, (streamCutoff omega b x - streamCutoff omega a x) i j *
        w.toH1Function.grad x j := rfl
  rw [hrw]
  exact MeasureTheory.integrable_finsetSum _ fun j _ => hterm j

/-- Each coordinate of `w (f_b − f_a)` is integrable on the cube. -/
private theorem integrableZeroTraceDrift (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (i : Fin d) :
    IntegrableOn (fun x => (w.toH1Function.toFun x •
      (driftCutoff omega b x - driftCutoff omega a x)) i) (openCubeSet Q) volume :=
  w.toH1Function.memL2.integrable_mul
    (memL2On_openCubeSet_of_continuous Q (continuous_driftCutoff_sub_apply omega hab i))

/-- The reversed drift increment is square-integrable on the cube. -/
private theorem memL2DriftApplyRev (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (i : Fin d) :
    MemL2On (openCubeSet Q)
      (fun x => driftCutoff omega a x i - driftCutoff omega b x i) := by
  have h := (continuous_driftCutoff_sub_apply omega hab i).neg
  have hrw : (fun x : Vec d => -(driftCutoff omega b x i - driftCutoff omega a x i))
      = fun x : Vec d => driftCutoff omega a x i - driftCutoff omega b x i := by
    funext x
    ring
  exact memL2On_openCubeSet_of_continuous Q (hrw ▸ h)

/-- Each coordinate of `w (f_a − f_b)` is integrable on the cube. -/
private theorem integrableZeroTraceDriftRev (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (i : Fin d) :
    IntegrableOn (fun x => (w.toH1Function.toFun x •
      (driftCutoff omega a x - driftCutoff omega b x)) i) (openCubeSet Q) volume :=
  w.toH1Function.memL2.integrable_mul (memL2DriftApplyRev omega hab Q i)

/-- `p·(f_b − f_a)` is square-integrable on the cube. -/
private theorem memL2DriftVecDot (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (p : Vec d) :
    MemL2On (openCubeSet Q)
      (fun x => vecDot p (driftCutoff omega b x - driftCutoff omega a x)) := by
  have h := continuous_driftCutoff_sub_vecDot omega hab p
  have hrw : (fun x : Vec d => vecDot (driftCutoff omega b x - driftCutoff omega a x) p)
      = fun x : Vec d => vecDot p (driftCutoff omega b x - driftCutoff omega a x) := by
    funext x
    exact vecDot_comm _ _
  rw [hrw] at h
  exact memL2On_openCubeSet_of_continuous Q h

/-- `p·(f_a − f_b)` is square-integrable on the cube. -/
private theorem memL2DriftVecDotRev (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (p : Vec d) :
    MemL2On (openCubeSet Q)
      (fun x => vecDot p (driftCutoff omega a x - driftCutoff omega b x)) := by
  have h := (memL2DriftVecDot omega hab Q p).neg
  have hrw : (-fun x : Vec d => vecDot p (driftCutoff omega b x - driftCutoff omega a x))
      = fun x : Vec d => vecDot p (driftCutoff omega a x - driftCutoff omega b x) := by
    funext x
    show -vecDot p (driftCutoff omega b x - driftCutoff omega a x) = _
    rw [show driftCutoff omega b x - driftCutoff omega a x
        = -(driftCutoff omega a x - driftCutoff omega b x) from (neg_sub _ _).symm,
      vecDot_neg_right, neg_neg]
  rw [hrw] at h
  exact h

/-- `w p·(f_b − f_a)` is integrable on the cube. -/
private theorem integrableZeroTraceDriftVecDot (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (p : Vec d) :
    IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot p (driftCutoff omega b x - driftCutoff omega a x)) (openCubeSet Q) volume :=
  w.toH1Function.memL2.integrable_mul (memL2DriftVecDot omega hab Q p)

/-- `w p·(f_a − f_b)` is integrable on the cube. -/
private theorem integrableZeroTraceDriftVecDotRev (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (p : Vec d) :
    IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot p (driftCutoff omega a x - driftCutoff omega b x)) (openCubeSet Q) volume :=
  w.toH1Function.memL2.integrable_mul (memL2DriftVecDotRev omega hab Q p)

/-! ## The scale ordering of `e.scale.selection` -/

private theorem ellLeEllPrime (S : ScaleSelection) : S.ell ≤ S.ellPrime := by
  have h := S.ell_add_a
  omega

private theorem ellPrimeLeLPrime (S : ScaleSelection) : S.ellPrime ≤ S.LPrime := by
  have h1 := S.ellPrime_add_h
  have h2 := S.LPrime_eq
  omega

private theorem ellLeLPrime (S : ScaleSelection) : S.ell ≤ S.LPrime :=
  le_trans (ellLeEllPrime S) (ellPrimeLeLPrime S)

/-! ## `hPartsP`: the integration by parts of the paper at the constant `p` -/

/-- **The integration by parts of the paper
applied to the constant `p`**, in the exact shape of the hypothesis `hPartsP`
of `Section3/Terms/MasterIdentity.ellsep_testing`:

`p·⨍_{cu_m} w (f_ℓ − f_{ℓ'}) = −p·⨍_{cu_m} (k_{ℓ'} − k_ℓ)∇w`.

Both halves are proved: the derivative is moved off `f_{ℓ'} − f_ℓ = ∇·(k_{ℓ'} −
k_ℓ)` by `volumeAverage_zeroTrace_mul_drift_sub_const`, and the resulting
pairing is flipped by the antisymmetry of `k_{ℓ'} − k_ℓ`.  No hypothesis
remains. -/
theorem parts_constant_term (omega : ShellSeq d) (S : ScaleSelection) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ)))) :
    vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x •
          (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))) =
      -vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          (w.toH1Function.grad x))) := by
  have hle : S.ell ≤ S.ellPrime := ellLeEllPrime S
  have hbridgeL : vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x •
          (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x)))
      = volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot p (w.toH1Function.toFun x •
          (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))) :=
    vecDotVolumeAverageVec p _ (fun i => integrableZeroTraceDriftRev omega hle w i)
  have hptL : (fun x : Vec d => vecDot p (w.toH1Function.toFun x •
        (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x)))
      = fun x : Vec d => -(w.toH1Function.toFun x *
        vecDot (driftCutoff omega S.ellPrime x - driftCutoff omega S.ell x) p) := by
    funext x
    rw [vecDot_smul_right, show driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x
        = -(driftCutoff omega S.ellPrime x - driftCutoff omega S.ell x) from
      (neg_sub _ _).symm, vecDot_neg_right, vecDot_comm]
    ring
  have hIbp : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.ellPrime x - driftCutoff omega S.ell x) p) =
      -volumeAverage (openCubeSet (originCube d (S.m : ℤ))) (fun x => vecDot
        (matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x) p)
        (w.toH1Function.grad x)) :=
    volumeAverage_zeroTrace_mul_drift_sub_const omega hle p w
  have hbridgeR : vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          (w.toH1Function.grad x)))
      = volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot p (matVecMul
          (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          (w.toH1Function.grad x))) :=
    vecDotVolumeAverageVec p _ (fun i => integrableStreamGrad omega hle w i)
  have hptR : (fun x : Vec d => vecDot p (matVecMul
        (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
        (w.toH1Function.grad x)))
      = fun x : Vec d => -vecDot
        (matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x) p)
        (w.toH1Function.grad x) := by
    funext x
    exact vecDotMatVecMulSkew (streamCutoffSubSkew omega S.ell S.ellPrime x) p _
  rw [hbridgeL, hptL, volumeAverageNegT, hIbp, hbridgeR, hptR, volumeAverageNegT]

/-! ## `hTestW`: `e.w.testing.formula` -/

/-- **`e.w.testing.formula`**, in the exact shape of the hypothesis `hTestW` of
`Section3/Terms/MasterIdentity.ellsep_testing`:

`⨍_{cu_m}|∇w|² = p·⨍_{cu_m} w (f_{L'} − f_ℓ) + p·⨍_{cu_m} w (f_ℓ − f_{ℓ'})`.

The single hypothesis is `e.def.w` itself: `w` is the Dirichlet response of the
flux `(k_{L'} − k_{ℓ'})p` on `cu_m` (`Setup.IsDirichletResponse`).  Testing that weak form
against `w` gives
`⨍|∇w|² = −⨍ ((k_{L'} − k_{ℓ'})p)·∇w`, and the integration by parts of the paper
for the constant `p` turns the right side into `p·⨍ w (f_{L'} − f_{ℓ'})`,
which splits at the shell `ℓ`. -/
theorem w_testing_formula (omega : ShellSeq d) (S : ScaleSelection) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : IsDirichletResponse omega S.LPrime S.ellPrime S.m p w) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x •
            (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))) +
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x •
            (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))) := by
  have hle1 : S.ellPrime ≤ S.LPrime := ellPrimeLeLPrime S
  have hle2 : S.ell ≤ S.LPrime := ellLeLPrime S
  have hle3 : S.ell ≤ S.ellPrime := ellLeEllPrime S
  have hweak := (isDirichletResponse_iff omega S.LPrime S.ellPrime S.m p w).1 hw w
  have hLHS : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      -volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (matVecMul
          (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
          (w.toH1Function.grad x)) := by
    show (volume (openCubeSet (originCube d (S.m : ℤ)))).toReal⁻¹ *
        ∫ x in openCubeSet (originCube d (S.m : ℤ)),
          vecNormSq (w.toH1Function.grad x) ∂volume = _
    rw [show (∫ x in openCubeSet (originCube d (S.m : ℤ)),
        vecNormSq (w.toH1Function.grad x) ∂volume)
      = ∫ x in openCubeSet (originCube d (S.m : ℤ)),
        vecDot (w.toH1Function.grad x) (w.toH1Function.grad x) ∂volume from rfl, hweak]
    simp only [volumeAverage]
    ring
  have hIbp : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ellPrime x) p) =
      -volumeAverage (openCubeSet (originCube d (S.m : ℤ))) (fun x => vecDot
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
        (w.toH1Function.grad x)) :=
    volumeAverage_zeroTrace_mul_drift_sub_const omega hle1 p w
  have hsplit : (fun x : Vec d => w.toH1Function.toFun x *
        vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ellPrime x) p)
      = fun x : Vec d => w.toH1Function.toFun x *
          vecDot p (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        + w.toH1Function.toFun x *
          vecDot p (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x) := by
    funext x
    rw [vecDot_comm, show driftCutoff omega S.LPrime x - driftCutoff omega S.ellPrime x
        = (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
          + (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x) by abel,
      vecDot_add_right]
    ring
  have hint1 : IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot p (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    integrableZeroTraceDriftVecDot omega hle2 w p
  have hint2 : IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot p (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    integrableZeroTraceDriftVecDotRev omega hle3 w p
  have hbr1 : vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x •
          (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)))
      = volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x *
          vecDot p (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)) := by
    rw [vecDotVolumeAverageVec p _ (fun i => integrableZeroTraceDrift omega hle2 w i)]
    exact congrArg (volumeAverage (openCubeSet (originCube d (S.m : ℤ))))
      (funext fun x => vecDot_smul_right _ _ _)
  have hbr2 : vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x •
          (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x)))
      = volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x *
          vecDot p (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x)) := by
    rw [vecDotVolumeAverageVec p _ (fun i => integrableZeroTraceDriftRev omega hle3 w i)]
    exact congrArg (volumeAverage (openCubeSet (originCube d (S.m : ℤ))))
      (funext fun x => vecDot_smul_right _ _ _)
  rw [hLHS, hbr1, hbr2, ← hIbp, hsplit, volumeAverageAddT hint1 hint2]

/-! ## `hTestEllsep`: `e.ellsep` tested against `w` -/

/-! ## `hParts`: the integration by parts of the paper at `∇u_m − p` -/

/-! ## `e.ellsep.testing` with the four displays discharged -/

end

end SuperdiffusionCLT.Section3.Terms
