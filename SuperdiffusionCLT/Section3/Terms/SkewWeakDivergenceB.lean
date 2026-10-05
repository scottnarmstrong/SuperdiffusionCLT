/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SkewWeakDivergence

/-!
# The divergence identity at the stream cutoff, and the separation display

The paper asserts

`∇·((k_{L'} − k_ℓ)∇u_m) = (f_{L'} − f_ℓ)·∇u_m`,

"because the matrix is antisymmetric".  The route to that identity through
`Section3/Terms/EllsepDriftB.weakDivergence_streamGradJacobian` produces the
whole weak *Jacobian* of `K ∇u` and therefore consumes a weak Hessian of `u`,
which is not available for
the cube maximizer.  `Section3/Terms/SkewWeakDivergence.lean` proves the divergence
identity for an abstract antisymmetric `C²` matrix field and an `H¹` function, with no second
derivative of `u` at all.  This module instantiates it at the stream increment —
the stream cutoff is `C²` because the shell carrier stores two
derivatives (`ShellField.contDiff_two`), and its divergence is the drift
increment by `weakDivergence_streamFluxWeakGradient` read at the basis vectors —
and then carries the resulting datum through the separation display.

`Section3/Terms/EllsepTesting.ellsep_testing_of_carriers` cannot be reused
directly: its three open carriers `hDG`, `hJac`, `hDiv` are consumed inside
`Sobolev/DirichletW2pDivergence.setIntegral_vecDot_zeroTrace_grad_eq_neg`, whose
*proof* packages each component `F i` with the whole Jacobian row `DF i` as an
`H1Function`, even though its *statement* mentions only `weakDivergence DF`.  The
restatement that would let the existing chain be reused verbatim is exactly
`SkewWeakDivergence.setIntegral_vecDot_zeroTrace_grad_eq_neg_of_hasWeakDivergenceOn`:
replace `(hDF, hweak)` by `(hG : MemL2On U G, hdiv : HasWeakDivergenceOn U F G)`
and `weakDivergence DF` by `G`.  Here the display is rebuilt directly from
`ellsep_testing_decomposition` with the two Jacobian-consuming inputs replaced.

## Main results

* `hasWeakDivergenceOn_streamGrad` — `∇·((k_b − k_a)∇u) = (f_b − f_a)·∇u` for
  `u ∈ H¹`.
* `ellsep_testing_of_hasWeakDivergenceOn`, `ellsep_testing_of_h1_field` — the
  separation display with the weak-Jacobian carriers
  removed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Sobolev
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The stream increment -/

private theorem matVecMulBasisVecEntry (A : Mat d) (i j : Fin d) :
    matVecMul A (basisVec j) i = A i j := by
  show ∑ k : Fin d, A i k * basisVec j k = A i j
  rw [Finset.sum_eq_single j]
  · simp [basisVec]
  · intro k _ hk
    simp [basisVec, hk]
  · intro hj
    simp at hj

/-- A single stream cutoff is `C²`: each shell of the carrier is. -/
private theorem contDiffTwoStreamCutoff (omega : ShellSeq d) (L : ℕ) :
    ContDiff ℝ 2 (fun x : Vec d => streamCutoff omega L x) := by
  rw [show (fun x : Vec d => streamCutoff omega L x)
      = fun x : Vec d => ∑ k ∈ Finset.range (L + 1), (omega k : Vec d → Mat d) x from
    funext fun x => streamCutoff_apply omega L x]
  exact ContDiff.sum fun k _ => ShellField.contDiff_two (omega k)

/-- The entries of a stream increment are `C²`. -/
private theorem contDiffTwoStreamSubEntry (omega : ShellSeq d) (a b : ℕ)
    (i j : Fin d) :
    ContDiff ℝ 2
      (fun x : Vec d => (streamCutoff omega b x - streamCutoff omega a x) i j) := by
  have h : ContDiff ℝ 2 (fun x : Vec d => fluxEntryCLM (basisVec j) i
      (streamCutoff omega b x - streamCutoff omega a x)) :=
    (fluxEntryCLM (basisVec j) i).contDiff.comp
      ((contDiffTwoStreamCutoff omega b).sub (contDiffTwoStreamCutoff omega a))
  rwa [show (fun x : Vec d => fluxEntryCLM (basisVec j) i
        (streamCutoff omega b x - streamCutoff omega a x))
      = fun x : Vec d => (streamCutoff omega b x - streamCutoff omega a x) i j from
    funext fun x => by rw [fluxEntryCLM_apply, matVecMulBasisVecEntry]] at h

/-- A stream increment is antisymmetric entrywise. -/
private theorem streamSubSkewEntry (omega : ShellSeq d) (a b : ℕ) (x : Vec d)
    (i j : Fin d) :
    (streamCutoff omega b x - streamCutoff omega a x) i j =
      -(streamCutoff omega b x - streamCutoff omega a x) j i := by
  show streamCutoff omega b x i j - streamCutoff omega a x i j =
    -(streamCutoff omega b x j i - streamCutoff omega a x j i)
  rw [streamCutoff_skew_entry omega b x i j, streamCutoff_skew_entry omega a x i j]
  ring

/-- **The divergence of the stream increment is the drift increment.**  It is
`weakDivergence_streamFluxWeakGradient` read at the basis vectors. -/
private theorem matFieldDivergenceStream (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (x : Vec d) (j : Fin d) :
    matFieldDivergence
        (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y) x j =
      driftCutoff omega b x j - driftCutoff omega a x j := by
  have hsum : matFieldDivergence
        (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y) x j =
      weakDivergence (streamFluxWeakGradient omega a b (basisVec j)) x := by
    show ∑ i : Fin d, (fderiv ℝ (fun y : Vec d =>
        (streamCutoff omega b y - streamCutoff omega a y) i j) x) (basisVec i) =
      ∑ i : Fin d, streamFluxWeakGradient omega a b (basisVec j) i x i
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (fun y : Vec d => (streamCutoff omega b y - streamCutoff omega a y) i j)
        = fun y : Vec d =>
          matVecMul (streamCutoff omega b y - streamCutoff omega a y) (basisVec j) i
      from funext fun y => (matVecMulBasisVecEntry _ i j).symm]
    rfl
  rw [hsum, weakDivergence_streamFluxWeakGradient omega hab (basisVec j) x,
    vecDot_basisVec_right]
  rfl

/-- **`∇·((k_b − k_a)∇u) = (f_b − f_a)·∇u` for `u` merely in `H¹`**, with no weak Hessian of `u`
anywhere.  This is the datum the separation display needs in place of the weak
Jacobian `hJac` and its `L²` rows `hDG`. -/
theorem hasWeakDivergenceOn_streamGrad (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    HasWeakDivergenceOn (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (u.grad x))
      (fun x => vecDot (driftCutoff omega b x - driftCutoff omega a x) (u.grad x)) := by
  have hbase := hasWeakDivergenceOn_matVecMul_of_skew Q
    (K := fun x : Vec d => streamCutoff omega b x - streamCutoff omega a x)
    (contDiffTwoStreamSubEntry omega a b) (streamSubSkewEntry omega a b) u
  rwa [show (fun x : Vec d => vecDot (matFieldDivergence
        (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y) x)
        (u.grad x))
      = fun x : Vec d =>
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (u.grad x) from
    funext fun x => congrArg (fun v : Vec d => vecDot v (u.grad x))
      (funext fun j => matFieldDivergenceStream omega hab x j)] at hbase

/-! ## The integration by parts, with no open carrier -/

/-- **`hFlux` with no hypothesis on `u` beyond `u ∈ H¹`**: the skew flux
`(k_b − k_a)∇u` is square-integrable coordinatewise on the cube. -/
theorem memL2On_streamSubGrad (omega : ShellSeq d) (a b : ℕ) (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (i : Fin d) :
    MemL2On (openCubeSet Q) (fun x =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) (u.grad x) i) := by
  show MemL2On (openCubeSet Q) (fun x => ∑ j : Fin d,
    (streamCutoff omega b x - streamCutoff omega a x) i j * u.grad x j)
  exact MeasureTheory.memLp_finsetSum _ fun j _ =>
    memL2On_entry_mul_gradCoord Q (contDiffTwoStreamSubEntry omega a b) u i j

/-- **The drift pairing is square-integrable with no weak-Jacobian datum**: the
drift increment is continuous, hence bounded on the cube, and `∇u ∈ L²`.  This
replaces the use of `Section3/Terms/EllsepEquation.memL2On_drift_sub_vecDot`,
which reads the pairing off the trace of a weak Jacobian. -/
theorem memL2On_driftSubGrad (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    MemL2On (openCubeSet Q) (fun x =>
      vecDot (driftCutoff omega b x - driftCutoff omega a x) (u.grad x)) := by
  show MemL2On (openCubeSet Q) (fun x => ∑ k : Fin d,
    (driftCutoff omega b x - driftCutoff omega a x) k * u.grad x k)
  refine MeasureTheory.memLp_finsetSum _ fun k _ => ?_
  exact (memLpOn_openCubeSet_of_continuous (p := ⊤) Q
    (continuous_driftCutoff_sub_apply omega hab k)).fun_mul (u.gradMemL2 k)

/-- **The integration by parts from a weak divergence.**
This is the exact conclusion of
`Section3/Terms/EllsepEquation.setIntegral_zeroTrace_mul_drift_sub`, with its
weak-Jacobian datum `hDG`, `hJac`, `hDiv` replaced by the weak divergence and the
`L²` datum of the drift pairing. -/
theorem setIntegral_zeroTrace_mul_drift_sub_of_hasWeakDivergenceOn
    {Q : TriadicCube d} (omega : ShellSeq d) (a b : ℕ) (V : Vec d → Vec d)
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet Q) (fun x =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x) i))
    (hG : MemL2On (openCubeSet Q) (fun x =>
      vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x)))
    (hdiv : HasWeakDivergenceOn (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x))
      (fun x => vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x)))
    (w : H10Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q, w.toH1Function x *
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x) ∂volume =
      -∫ x in openCubeSet Q, vecDot
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x))
        (w.toH1Function.grad x) ∂volume := by
  have hbase :=
    setIntegral_vecDot_zeroTrace_grad_eq_neg_of_hasWeakDivergenceOn hFlux hG hdiv w
  have hcomm : ∫ x in openCubeSet Q, w.toH1Function x *
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x) *
          w.toH1Function x ∂volume :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hcomm]
  linarith only [hbase]

/-- The normalized-average form: the exact conclusion of
`Section3/Terms/EllsepEquation.volumeAverage_zeroTrace_mul_drift_sub` from a weak
divergence. -/
theorem volumeAverage_zeroTrace_mul_drift_sub_of_hasWeakDivergenceOn
    {Q : TriadicCube d} (omega : ShellSeq d) (a b : ℕ) (V : Vec d → Vec d)
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet Q) (fun x =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x) i))
    (hG : MemL2On (openCubeSet Q) (fun x =>
      vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x)))
    (hdiv : HasWeakDivergenceOn (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x))
      (fun x => vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x)))
    (w : H10Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x => w.toH1Function x *
        vecDot (driftCutoff omega b x - driftCutoff omega a x) (V x)) =
      -volumeAverage (openCubeSet Q) (fun x => vecDot
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x) (V x))
        (w.toH1Function.grad x)) := by
  simp only [volumeAverage]
  rw [setIntegral_zeroTrace_mul_drift_sub_of_hasWeakDivergenceOn omega a b V
    hFlux hG hdiv w]
  ring

/-! ## The separation display with the weak-Jacobian carriers removed -/

private theorem volumeAverageSubE {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun x => f x - g x) = volumeAverage U f - volumeAverage U g := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_sub hf hg]
  ring

private theorem vecDotVolumeAverageVecE {U : Set (Vec d)} (p : Vec d)
    (G : Vec d → Vec d)
    (hint : ∀ i : Fin d, IntegrableOn (fun x => G x i) U volume) :
    vecDot p (volumeAverageVec U G) = volumeAverage U (fun x => vecDot p (G x)) := by
  have hleft : vecDot p (volumeAverageVec U G)
      = ∑ i : Fin d, p i *
          ((volume U).toReal⁻¹ * ∫ x in U, G x i ∂volume) := rfl
  have hpt : (fun x => vecDot p (G x)) = fun x => ∑ i : Fin d, p i * G x i := rfl
  have hsum : ∫ x in U, (∑ i : Fin d, p i * G x i) ∂volume
      = ∑ i : Fin d, p i * ∫ x in U, G x i ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hint i).const_mul (p i))]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  rw [hleft, show volumeAverage U (fun x => vecDot p (G x))
      = (volume U).toReal⁻¹ * ∫ x in U, vecDot p (G x) ∂volume from rfl,
    hpt, hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem matVecMulSubE (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

private theorem matVecMulNegMatE (A : Mat d) (x : Vec d) :
    matVecMul (-A) x = -matVecMul A x := by
  funext i
  show ∑ j, (-A i j) * x j = -∑ j, A i j * x j
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem integrableStreamConstGradE (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (p : Vec d)
    (w : H10Function (openCubeSet Q)) :
    IntegrableOn (fun x => vecDot
      (matVecMul (streamCutoff omega b x - streamCutoff omega a x) p)
      (w.toH1Function.grad x)) (openCubeSet Q) volume := by
  show IntegrableOn (fun x => ∑ i : Fin d,
    matVecMul (streamCutoff omega b x - streamCutoff omega a x) p i *
      w.toH1Function.grad x i) (openCubeSet Q) volume
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  exact (memL2On_openCubeSet_of_continuous Q
    (continuous_streamFlux_apply omega hab p i)).integrable_mul
    (w.toH1Function.gradMemL2 i)

private theorem integrableZeroTraceDriftE (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (i : Fin d) :
    IntegrableOn (fun x => (w.toH1Function.toFun x •
      (driftCutoff omega b x - driftCutoff omega a x)) i) (openCubeSet Q) volume :=
  w.toH1Function.memL2.integrable_mul
    (memL2On_openCubeSet_of_continuous Q
      (continuous_driftCutoff_sub_apply omega hab i))

private theorem memL2DriftVecDotE (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (Q : TriadicCube d) (p : Vec d) :
    MemL2On (openCubeSet Q)
      (fun x => vecDot p (driftCutoff omega b x - driftCutoff omega a x)) := by
  have h := continuous_driftCutoff_sub_vecDot omega hab p
  rw [show (fun x : Vec d => vecDot (driftCutoff omega b x - driftCutoff omega a x) p)
      = fun x : Vec d => vecDot p (driftCutoff omega b x - driftCutoff omega a x) from
    funext fun x => vecDot_comm _ _] at h
  exact memL2On_openCubeSet_of_continuous Q h

private theorem integrableZeroTraceDriftVecDotE (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) (p : Vec d) :
    IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot p (driftCutoff omega b x - driftCutoff omega a x))
      (openCubeSet Q) volume :=
  w.toH1Function.memL2.integrable_mul (memL2DriftVecDotE omega hab Q p)

private theorem ellLeLPrimeE (S : ScaleSelection) : S.ell ≤ S.LPrime := by
  have h1 := S.ell_add_a
  have h2 := S.ellPrime_add_h
  have h3 := S.LPrime_eq
  omega

/-- **`e.ellsep` tested against the response, with no weak Jacobian.**  This is
`Section3/Terms/EllsepTesting.ellsep_tested_against_response` with its
`hDG`, `hJac`, `hDiv` replaced by the weak divergence `hdiv` and the `L²` datum
`hG` of the drift pairing. -/
theorem ellsep_tested_against_response_of_hasWeakDivergenceOn (nu : ℝ)
    (omega : ShellSeq d) (S : ScaleSelection) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ)))) (V : Vec d → Vec d)
    (hEll : IsSolenoidalOn (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
        (V x)))
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (V x) i))
    (hG : MemL2On (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        (V x)))
    (hdiv : HasWeakDivergenceOn (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (V x))
      (fun x => vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        (V x)))
    (hIntA : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
      (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (V x)))
      (openCubeSet (originCube d (S.m : ℤ))) volume) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (V x))) =
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x •
            (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x *
            vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
              (V x - p)) := by
  have hle2 : S.ell ≤ S.LPrime := ellLeLPrimeE S
  have hIntK := integrableOn_vecDot_grad_streamFlux omega V w hFlux
  have hstep1 := volumeAverage_vecDot_coefficientCutoff_of_isSolenoidalOn nu omega
    S.LPrime S.ell V w hEll hIntA hIntK
  have hstep2 := volumeAverage_zeroTrace_mul_drift_sub_of_hasWeakDivergenceOn omega
    S.ell S.LPrime V hFlux hG hdiv w
  have hcomm : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (V x)))
      = volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (V x)) (w.toH1Function.grad x)) :=
    congrArg (volumeAverage (openCubeSet (originCube d (S.m : ℤ))))
      (funext fun x => vecDot_comm _ _)
  have hintV : IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) (V x))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    w.toH1Function.memL2.integrable_mul hG
  have hintP : IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p)
      (openCubeSet (originCube d (S.m : ℤ))) volume := by
    have h := integrableZeroTraceDriftVecDotE omega hle2 w p
    rwa [show (fun x : Vec d => w.toH1Function.toFun x *
          vecDot p (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))
        = fun x : Vec d => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p from
      funext fun x => by rw [vecDot_comm]] at h
  have hptSub : (fun x : Vec d => w.toH1Function.toFun x *
        vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) (V x - p))
      = fun x : Vec d => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) (V x)
        - w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p := by
    funext x
    rw [show V x - p = V x + -p from sub_eq_add_neg _ _, vecDot_add_right,
      vecDot_neg_right]
    ring
  have hbr : vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x •
          (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)))
      = volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p) := by
    rw [vecDotVolumeAverageVecE p _ (fun i => integrableZeroTraceDriftE omega hle2 w i)]
    refine congrArg (volumeAverage (openCubeSet (originCube d (S.m : ℤ))))
      (funext fun x => ?_)
    rw [vecDot_smul_right, vecDot_comm]
  rw [hstep1, hcomm, hbr, hptSub, volumeAverageSubE hintV hintP, ← hstep2]
  ring

/-- **The integration by parts applied to the gradient term,
with no weak Jacobian.**  This is
`Section3/Terms/EllsepTesting.parts_gradient_term` with its `hDG`, `hJac`,
`hDiv` replaced by the weak divergence `hdiv` and the `L²` datum `hG`. -/
theorem parts_gradient_term_of_hasWeakDivergenceOn (omega : ShellSeq d)
    (S : ScaleSelection) (p : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ)))) (V : Vec d → Vec d)
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (V x) i))
    (hG : MemL2On (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        (V x)))
    (hdiv : HasWeakDivergenceOn (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (V x))
      (fun x => vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        (V x))) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
            (V x - p)) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
            (V x - p))) := by
  have hle2 : S.ell ≤ S.LPrime := ellLeLPrimeE S
  have hstep2 := volumeAverage_zeroTrace_mul_drift_sub_of_hasWeakDivergenceOn omega
    S.ell S.LPrime V hFlux hG hdiv w
  have hconst := volumeAverage_zeroTrace_mul_drift_sub_const omega hle2 p w
  have hintV : IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) (V x))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    w.toH1Function.memL2.integrable_mul hG
  have hintP : IntegrableOn (fun x => w.toH1Function.toFun x *
      vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p)
      (openCubeSet (originCube d (S.m : ℤ))) volume := by
    have h := integrableZeroTraceDriftVecDotE omega hle2 w p
    rwa [show (fun x : Vec d => w.toH1Function.toFun x *
          vecDot p (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))
        = fun x : Vec d => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p from
      funext fun x => by rw [vecDot_comm]] at h
  have hptSub : (fun x : Vec d => w.toH1Function.toFun x *
        vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) (V x - p))
      = fun x : Vec d => w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) (V x)
        - w.toH1Function.toFun x *
          vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x) p := by
    funext x
    rw [show V x - p = V x + -p from sub_eq_add_neg _ _, vecDot_add_right,
      vecDot_neg_right]
    ring
  have hintKcomm : IntegrableOn (fun x => vecDot
      (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) (V x))
      (w.toH1Function.grad x)) (openCubeSet (originCube d (S.m : ℤ))) volume := by
    have h := integrableOn_vecDot_grad_streamFlux omega V w hFlux
    rwa [show (fun x : Vec d => vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (V x)))
        = fun x : Vec d => vecDot
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (V x)) (w.toH1Function.grad x) from
      funext fun x => vecDot_comm _ _] at h
  have hptR : (fun x : Vec d => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
          (V x - p)))
      = fun x : Vec d => vecDot
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) p)
          (w.toH1Function.grad x)
        - vecDot
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (V x)) (w.toH1Function.grad x) := by
    funext x
    have h1 : vecDot (w.toH1Function.grad x) (matVecMul
        (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) (V x))
        = vecDot (matVecMul
          (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) (V x))
          (w.toH1Function.grad x) := vecDot_comm _ _
    have h2 : vecDot (w.toH1Function.grad x) (matVecMul
        (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) p)
        = vecDot (matVecMul
          (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) p)
          (w.toH1Function.grad x) := vecDot_comm _ _
    have h3 : vecDot (w.toH1Function.grad x) (matVecMul
          (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x) (V x - p))
        = -vecDot (w.toH1Function.grad x) (matVecMul
            (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) (V x))
          + vecDot (w.toH1Function.grad x) (matVecMul
            (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) p) := by
      rw [show streamCutoff omega S.ell x - streamCutoff omega S.LPrime x
          = -(streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) from
        (neg_sub _ _).symm, matVecMulNegMatE, vecDot_neg_right, matVecMulSubE,
        sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
      ring
    linarith only [h1, h2, h3]
  rw [hptSub, volumeAverageSubE hintV hintP, hptR,
    volumeAverageSubE (integrableStreamConstGradE omega hle2 p w) hintKcomm,
    hstep2, hconst]
  ring

/-- **`e.ellsep.testing` with the weak-Jacobian carriers replaced by a weak
divergence**.  The
conclusion is exactly that of
`Section3/Terms/EllsepTesting.ellsep_testing_of_carriers`; what has changed is
the datum for the skew field `(k_{L'} − k_ℓ)V`: its weak Jacobian `hJac` and the
`L²` rows `hDG` are gone, and in their place stand the weak divergence `hdiv`
and the `L²` datum `hG` of the drift pairing. -/
theorem ellsep_testing_of_hasWeakDivergenceOn (nu : ℝ) (omega : ShellSeq d)
    (S : ScaleSelection) (p q : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (V uNGlued : Vec d → Vec d)
    (hw : IsDirichletResponse omega S.LPrime S.ellPrime S.m p w)
    (hEll : IsSolenoidalOn (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
        (V x)))
    (hFlux : ∀ i : Fin d, MemL2On (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (V x) i))
    (hG : MemL2On (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        (V x)))
    (hdiv : HasWeakDivergenceOn (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
        (V x))
      (fun x => vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
        (V x)))
    (hIntFlux : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (V x)))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hIntK : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          (V x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt1 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt2 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          (uNGlued x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt3 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (V x - uNGlued x))) (openCubeSet (originCube d (S.m : ℤ))) volume) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued x) - q)) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uNGlued x - p))) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (V x - uNGlued x))) -
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            (w.toH1Function.grad x))) :=
  ellsep_testing_decomposition nu omega S p q w V uNGlued hIntFlux hIntK hInt1
    hInt2 hInt3
    (ellsep_tested_against_response_of_hasWeakDivergenceOn nu omega S p w V hEll
      hFlux hG hdiv hIntFlux)
    (w_testing_formula omega S p w hw)
    (parts_gradient_term_of_hasWeakDivergenceOn omega S p w V hFlux hG hdiv)
    (parts_constant_term omega S p w)

/-- **`e.ellsep.testing` at an `H¹` field, with every skew-flux carrier
discharged.**  Taking `V = ∇u` for an `H¹` function `u` on the cube — in
particular for the cube maximizer, whose weak Hessian
is unavailable — the
three carriers `hFlux`, `hG`, `hdiv` are supplied by `memL2On_streamSubGrad`,
`memL2On_driftSubGrad` and `hasWeakDivergenceOn_streamGrad`.  What remains open
is exactly `hw`, `hEll` and the five integrability side conditions of the
display. -/
theorem ellsep_testing_of_h1_field (nu : ℝ) (omega : ShellSeq d)
    (S : ScaleSelection) (p q : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (u : H1Function (openCubeSet (originCube d (S.m : ℤ))))
    (uNGlued : Vec d → Vec d)
    (hw : IsDirichletResponse omega S.LPrime S.ellPrime S.m p w)
    (hEll : IsSolenoidalOn (openCubeSet (originCube d (S.m : ℤ)))
      (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
        (u.grad x)))
    (hIntFlux : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (u.grad x)))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hIntK : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          (u.grad x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt1 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt2 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          (uNGlued x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt3 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (u.grad x - uNGlued x))) (openCubeSet (originCube d (S.m : ℤ))) volume) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued x) - q)) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uNGlued x - p))) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (u.grad x - uNGlued x))) -
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            (w.toH1Function.grad x))) :=
  ellsep_testing_of_hasWeakDivergenceOn nu omega S p q w u.grad uNGlued hw hEll
    (memL2On_streamSubGrad omega S.ell S.LPrime (originCube d (S.m : ℤ)) u)
    (memL2On_driftSubGrad omega (ellLeLPrimeE S) (originCube d (S.m : ℤ)) u)
    (hasWeakDivergenceOn_streamGrad omega (ellLeLPrimeE S)
      (originCube d (S.m : ℤ)) u)
    hIntFlux hIntK hInt1 hInt2 hInt3

end

end SuperdiffusionCLT.Section3.Terms
