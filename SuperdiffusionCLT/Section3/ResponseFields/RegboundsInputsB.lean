/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import SuperdiffusionCLT.Section3.Setup.Parameters

/-!
# The upper-shell flux in the three response norms, and the centering step

This module completes `Section3/ResponseFields/RegboundsInputs.lean` with the
three readings of the upper-shell flux `(k_b − k_a)p` that the a priori
response estimates consume — the cube-average centering, the `L̲²` half of the
`H̲^{1/2}` norm, and the Jacobian that enters the `W̲^{2,8}` clause — together
with the two auxiliaries of the centering step of `l.w.basic.regbounds` and the
scale identity `m − ℓ' = h` of `e.scale.selection`.

## Which centering the a priori estimates see

The Dirichlet response of `F` is the Dirichlet response of `F − c` for every
constant vector `c` (`isCubeDirichletResponse_sub_const`): constants
disappear under the divergence.  `isCubeDirichletResponse_sub_const_iff`
records the equivalence, which is what makes the printed replacement of `F` by
`F − (F)_{cu_m}` in the estimates legitimate in both directions.  The
quantitative half of the step is `vecNorm_volumeAverageVec_sub_const_le` of the
companion module: the cube average is within `√d` of any other centering, so
the centered flux is controlled by the value at the cube centre with the extra
factor `1 + √d`.

## The Jacobian

The `W̲^{2,8}` clause of the a priori estimates quantifies over a weak gradient
`DF` of the components of `F`.  A consumer instantiates it, so this module
supplies the canonical choice — the classical Jacobian of the upper-shell
flux, which is a weak gradient because the flux is `C^1` — and the bound on
the carrier `HilbertMat.ofMat` of the resulting matrix, whose norm is the
Frobenius norm, hence at most `√d` times the exact induced derivative norm.

## Main results

* `exists_witness_vecCubeLpENorm_streamFlux_sub_volumeAverage`.
* `isCubeDirichletResponse_sub_const_iff`.
* `scalesOrdering_one_le_h`, `scaleSelection_pred_m_sub_ellPrime_le_h`.

## References

* The paper: `#centered-flux-responses`, `l.w.basic.regbounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The cube-average centering of the upper-shell flux -/

/-- **The upper shell in `L̲^q(cu_n)`, centered at its own cube average.**
This is the shape in which the a priori response estimates are applied in
the proof of `l.w.basic.regbounds`: the flux is replaced by `F − (F)_{cu_m}`, where the
average is the one the statement writes, over the half-open cube.

The amplitude is the one for centering at the cube centre, multiplied by `1 + √d`,
the price of moving the centering from the cube centre to the cube average. -/
theorem exists_witness_vecCubeLpENorm_streamFlux_sub_volumeAverage
    (hJ3 : ShellLawJ3 d P) (p : Vec d) {n a b : ℕ} (hna : n ≤ a + 1)
    (hab : a < b) :
    ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        ((1 + Real.sqrt d) *
          (upperShellFluxConst d * (3 : ℝ) ^ n * vecNorm p *
            (gammaTriangleConst 2 * ((3 : ℝ) ^ a)⁻¹))) ∧
      ∀ (q : ℝ≥0∞) (omega : ShellSeq d),
        vecCubeLpENorm (originCube d (n : ℤ)) q
            (fun x =>
              matVecMul (streamCutoff omega b x - streamCutoff omega a x) p -
                volumeAverageVec (cubeSet (originCube d (n : ℤ)))
                  (fun y =>
                    matVecMul
                      (streamCutoff omega b y - streamCutoff omega a y) p)) ≤
          ENNReal.ofReal (Z omega) := by
  have hfac : (0 : ℝ) ≤ 1 + Real.sqrt d := by positivity
  refine ⟨fun omega => (1 + Real.sqrt d) * upperShellFluxSupBound n a b p omega,
    (measurable_upperShellFluxSupBound n a b p).const_mul _, ?_, ?_⟩
  · have hconst : (0 : ℝ) ≤ upperShellFluxConst d * (3 : ℝ) ^ n * vecNorm p := by
      have h1 := upperShellFluxConst_nonneg d
      have h2 := vecNorm_nonneg p
      positivity
    have hwith :=
      ((isBigOWith_gammaSigma_upperShellDerivGauge hJ3 hna hab).const_mul
        hconst).const_mul hfac
    exact
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := gammaSigma 2)
        (X := fun omega : ShellSeq d =>
          (1 + Real.sqrt d) * upperShellFluxSupBound n a b p omega)
        (A := (1 + Real.sqrt d) *
          (upperShellFluxConst d * (3 : ℝ) ^ n * vecNorm p *
            (gammaTriangleConst 2 * ((3 : ℝ) ^ a)⁻¹)))
        (fun omega =>
          mul_nonneg hfac (upperShellFluxSupBound_nonneg n a b p omega))).1
        hwith
  · intro q omega
    refine vecCubeLpENorm_le_of_forall_mem_openCubeSet ?_ fun x hx => ?_
    · have hc : Continuous fun x : Vec d =>
          matVecMul (streamCutoff omega b x - streamCutoff omega a x) p :=
        continuous_matVecMul_comp
          ((continuous_streamCutoff_apply omega b).sub
            (continuous_streamCutoff_apply omega a)) p
      exact ((HilbertVec.ofVecL d).continuous.comp
        (hc.sub continuous_const)).aestronglyMeasurable
    set F : Vec d → Vec d := fun y =>
      matVecMul (streamCutoff omega b y - streamCutoff omega a y) p with hF
    set c : Vec d :=
      matVecMul (streamCutoff omega b 0 - streamCutoff omega a 0) p with hc
    have hcenter : ∀ y ∈ openCubeSet (originCube d (n : ℤ)),
        vecNorm (F y - c) ≤ upperShellFluxSupBound n a b p omega := fun y hy =>
      vecNorm_streamFlux_sub_center_le omega n a b p hy hab.le
    have havg : vecNorm (volumeAverageVec (openCubeSet (originCube d (n : ℤ))) F - c)
        ≤ Real.sqrt d * upperShellFluxSupBound n a b p omega :=
      vecNorm_volumeAverageVec_sub_const_le
        (fun i => integrableOn_streamFlux_apply omega hab.le p _ i)
        (upperShellFluxSupBound_nonneg n a b p omega) hcenter
    rw [volumeAverageVec_cubeSet_eq_openCubeSet]
    have hsplit : F x - volumeAverageVec (openCubeSet (originCube d (n : ℤ))) F =
        (F x - c) - (volumeAverageVec (openCubeSet (originCube d (n : ℤ))) F - c) := by
      abel
    rw [hsplit]
    refine (vecNorm_sub_le_add _ _).trans ?_
    refine (add_le_add (hcenter x hx) havg).trans_eq ?_
    ring

/-! ## The `L̲²` half of the `H̲^{1/2}` norm -/

/-! ## The Jacobian of the upper-shell flux -/

def matEntryCLMB (i l : Fin d) : Mat d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) l).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin d → ℝ) i)

@[simp] private theorem matEntryCLMB_apply (i l : Fin d) (A : Mat d) :
    matEntryCLMB i l A = A i l := rfl

/-- `M ↦ (M p)_i`, the `i`-th component of the flux read as a continuous linear
functional of the stream matrix. -/
def fluxEntryCLM (p : Vec d) (i : Fin d) : Mat d →L[ℝ] ℝ :=
  ∑ l : Fin d, p l • matEntryCLMB i l

@[simp] theorem fluxEntryCLM_apply (p : Vec d) (i : Fin d) (A : Mat d) :
    fluxEntryCLM p i A = matVecMul A p i := by
  rw [fluxEntryCLM, sum_apply]
  simp only [smul_apply, matEntryCLMB_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]

/-- The finite shell increment is `C^1`: each shell of the carrier is
`C^2`. -/
theorem contDiff_finiteShellIncrement (omega : ShellSeq d) (a b : ℕ) :
    ContDiff ℝ 1 (finiteShellIncrement omega a b : Vec d → Mat d) := by
  have hfun : (finiteShellIncrement omega a b : Vec d → Mat d) =
      fun x => ∑ k ∈ Finset.Ioc a b, (omega k : Vec d → Mat d) x := by
    funext x
    rw [finiteShellIncrement_apply]
    rfl
  rw [hfun]
  exact ContDiff.sum fun k _ =>
    (ShellField.contDiff_two (omega k)).of_le (by norm_num)

theorem contDiff_streamFlux_apply (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (p : Vec d) (i : Fin d) :
    ContDiff ℝ 1 (fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p i) := by
  have hfun : (fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p i) =
      fun x : Vec d =>
        fluxEntryCLM p i
          ((finiteShellIncrement omega a b : Vec d → Mat d) x) := by
    funext x
    rw [fluxEntryCLM_apply,
      ← finiteShellIncrement_apply_eq_streamCutoff_sub omega hab x]
  rw [hfun]
  exact (fluxEntryCLM p i).contDiff.comp
    (contDiff_finiteShellIncrement omega a b)

/-- **The classical Jacobian row of the upper-shell flux**, in the exact shape
`fun x i => fderiv ℝ f x (basisVec i)` produced by
`HasWeakGradientOn.of_contDiff`, so that it is *the* weak gradient a consumer
of the a priori `W̲^{2,8}` estimate supplies for the `i`-th component. -/
def streamFluxWeakGradient (omega : ShellSeq d) (a b : ℕ) (p : Vec d)
    (i : Fin d) : Vec d → Vec d :=
  fun x j => fderiv ℝ (fun y : Vec d =>
    matVecMul (streamCutoff omega b y - streamCutoff omega a y) p i) x
    (basisVec j)

theorem hasWeakGradientOn_streamFluxWeakGradient (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p : Vec d) (i : Fin d) (U : Set (Vec d)) :
    HasWeakGradientOn U
      (fun y : Vec d =>
        matVecMul (streamCutoff omega b y - streamCutoff omega a y) p i)
      (streamFluxWeakGradient omega a b p i) :=
  HasWeakGradientOn.of_contDiff (contDiff_streamFlux_apply omega hab p i)

theorem streamFluxWeakGradient_apply (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p : Vec d) (i : Fin d) (x : Vec d) (j : Fin d) :
    streamFluxWeakGradient omega a b p i x j =
      matVecMul ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x)
        (basisVec j)) p i := by
  have hcomp : HasFDerivAt
      (fun y : Vec d =>
        matVecMul (streamCutoff omega b y - streamCutoff omega a y) p i)
      ((fluxEntryCLM p i).comp
        (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x)) x := by
    have hK := hasFDerivAt_streamCutoff_sub omega hab x
    have h := (fluxEntryCLM p i).hasFDerivAt.comp x hK
    simp only [Function.comp_def, fluxEntryCLM_apply] at h
    exact h
  rw [streamFluxWeakGradient, hcomp.fderiv]
  exact fluxEntryCLM_apply p i _

theorem vecNorm_basisVec (i : Fin d) : vecNorm (basisVec i) = 1 := by
  have h : vecNorm (basisVec i) ^ 2 = 1 ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, vecNormSq_basisVec, one_pow]
  have h1 := Real.sqrt_le_sqrt h.le
  have h2 := Real.sqrt_le_sqrt h.ge
  rw [Real.sqrt_sq (vecNorm_nonneg _),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1)] at h1 h2
  exact le_antisymm h1 h2

/-- The norm of the `HilbertMat` carrier is the Frobenius norm. -/
theorem norm_sq_hilbertMat_ofMat (A : Mat d) :
    ‖HilbertMat.ofMat A‖ ^ 2 = ∑ i, ∑ j, A i j * A i j := by
  rw [← real_inner_self_eq_norm_sq, HilbertMat.inner_def]

/-- **The pointwise Jacobian bound of the upper shell.** On `cu_n` the
Frobenius norm of the Jacobian of `(k_b − k_a)p` is at most
`√d |p| ∑_{k ∈ (a,b]} ‖∇ j_k‖_{L^∞(cu_n)}`: each column is the image of a unit
vector under the exact induced derivative norm, and there are `d` columns. -/
theorem norm_hilbertMat_streamFluxWeakGradient_le (omega : ShellSeq d)
    (n a b : ℕ) (hab : a ≤ b) (p : Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ‖HilbertMat.ofMat
        (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ≤
      Real.sqrt d * vecNorm p * upperShellDerivGauge n a b omega := by
  set D := ∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x with hD
  set G := upperShellDerivGauge n a b omega with hG
  have hGnonneg : 0 ≤ G := upperShellDerivGauge_nonneg n a b omega
  have hDG : ShellField.matrixDerivativeNorm D ≤ G :=
    matrixDerivativeNorm_sum_shellDeriv_le_upperShellDerivGauge omega n a b hx
  have hcol : ∀ j : Fin d, matrixOperatorNorm (D (basisVec j)) ≤ G := by
    intro j
    refine le_trans ?_ hDG
    have h := matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm D
      (basisVec j)
    rwa [vecNorm_basisVec, mul_one] at h
  have hsum : ∑ i : Fin d, ∑ j : Fin d,
      streamFluxWeakGradient omega a b p i x j *
        streamFluxWeakGradient omega a b p i x j ≤
      (d : ℝ) * (G ^ 2 * vecNormSq p) := by
    have hswap : ∑ i : Fin d, ∑ j : Fin d,
        streamFluxWeakGradient omega a b p i x j *
          streamFluxWeakGradient omega a b p i x j =
        ∑ j : Fin d, vecNormSq (matVecMul (D (basisVec j)) p) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [streamFluxWeakGradient_apply omega hab p i x j]
    rw [hswap]
    calc
      ∑ j : Fin d, vecNormSq (matVecMul (D (basisVec j)) p) ≤
          ∑ _j : Fin d, G ^ 2 * vecNormSq p := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine
          (vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq _ _).trans ?_
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) (hcol j) 2)
          (vecNormSq_nonneg p)
      _ = (d : ℝ) * (G ^ 2 * vecNormSq p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ Real.sqrt d * vecNorm p * G :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)) hGnonneg
  have hsq : ‖HilbertMat.ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ^ 2 ≤
      (Real.sqrt d * vecNorm p * G) ^ 2 := by
    refine ((norm_sq_hilbertMat_ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)).trans_le hsum).trans_eq ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d),
      vecNorm_sq_eq_vecNormSq]
    ring
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB] at hfin

/-- **The upper shell's Jacobian in `L̲^q(cu_n)`**, in the `∃ Z` shape of the
response estimates.  This is the second parenthesized term of
`l.w.basic.regbounds` **restricted to the shells `k ≥ n`**; the
shells below the cube scale are not covered here — on them the paper uses
stationarity over the `3^{d(n-k)}` sub-cubes of `cu_n`, which is the technique
of the large-cube clauses, not of the display `e.nabla.kmn.Linfty`. -/
theorem exists_witness_cubeLpENorm_streamFluxWeakGradient
    (hJ3 : ShellLawJ3 d P) (p : Vec d) {n a b : ℕ} (hna : n ≤ a + 1)
    (hab : a < b) :
    ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (Real.sqrt d * vecNorm p *
          (gammaTriangleConst 2 * ((3 : ℝ) ^ a)⁻¹)) ∧
      ∀ (q : ℝ≥0∞) (omega : ShellSeq d),
        Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) q
            (fun x => HilbertMat.ofMat
              (fun i j => streamFluxWeakGradient omega a b p i x j)) ≤
          ENNReal.ofReal (Z omega) := by
  have hconst : (0 : ℝ) ≤ Real.sqrt d * vecNorm p :=
    mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)
  refine ⟨fun omega =>
      Real.sqrt d * vecNorm p * upperShellDerivGauge n a b omega,
    (measurable_upperShellDerivGauge n a b).const_mul _, ?_, ?_⟩
  · exact
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := gammaSigma 2)
        (X := fun omega : ShellSeq d =>
          Real.sqrt d * vecNorm p * upperShellDerivGauge n a b omega)
        (A := Real.sqrt d * vecNorm p *
          (gammaTriangleConst 2 * ((3 : ℝ) ^ a)⁻¹))
        (fun omega =>
          mul_nonneg hconst (upperShellDerivGauge_nonneg n a b omega))).1
        ((isBigOWith_gammaSigma_upperShellDerivGauge hJ3 hna hab).const_mul
          hconst)
  · intro q omega
    have hentry : ∀ i j : Fin d, Measurable
        (fun x : Vec d => streamFluxWeakGradient omega a b p i x j) := fun i j =>
      measurable_fderiv_apply_const ℝ (fun y : Vec d =>
        matVecMul (streamCutoff omega b y - streamCutoff omega a y) p i) (basisVec j)
    have hmat : AEStronglyMeasurable
        (fun x : Vec d => (fun i j => streamFluxWeakGradient omega a b p i x j : Mat d))
        (normalizedCubeMeasure (originCube d (n : ℤ))) := by
      rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
      intro i
      rw [aemeasurable_pi_iff]
      intro j
      exact (hentry i j).aemeasurable
    exact cubeLpENorm_le_of_forall_mem_openCubeSet
      ((HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable
        hmat)
      (fun x hx =>
        norm_hilbertMat_streamFluxWeakGradient_le omega n a b hab.le p hx)

/-! ## The centering equivalence -/

/-- **`#centered-flux-responses` as an equivalence**: `w` is
the Dirichlet response of `F` if and only if it is the Dirichlet response of
`F − c`, for every constant vector `c`.  The forward direction is
`isCubeDirichletResponse_sub_const`; the converse is the forward direction at
`−c`, and it is what lets the printed proof read the a priori estimates for
`F − (F)_{cu_m}` as estimates for the response of `F` itself. -/
theorem isCubeDirichletResponse_sub_const_iff {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H10Function (openCubeSet Q)}
    (hF : MemVectorL2 (openCubeSet Q) F) (c : Vec d) :
    IsCubeDirichletResponse Q F w ↔
      IsCubeDirichletResponse Q (fun x => F x - c) w := by
  constructor
  · intro h
    exact isCubeDirichletResponse_sub_const hF h c
  · intro h
    have hFc : MemVectorL2 (openCubeSet Q) (fun x => F x - c) :=
      hF.sub (MeasureTheory.memLp_const
        (μ := volumeMeasureOn (openCubeSet Q)) (c := c))
    have h2 := isCubeDirichletResponse_sub_const hFc h (-c)
    have hfun : (fun x => (F x - c) - -c) = F := by
      funext x
      abel
    rwa [hfun] at h2

/-! ## The scale identity `m − ℓ' = h` -/

/-- Under the scale ordering the window has at least one scale. -/
theorem scalesOrdering_one_le_h {S : ScaleSelection} (hS : ScalesOrdering S) :
    1 ≤ S.h := by
  have h1 := hS.ellPrime_lt_m
  have h2 := S.ellPrime_add_h
  omega

/-- The lower shell of the split at `m − 1` has at most `h` scales; this is the
comparison the printed proof uses to absorb the anchor's `(m − 1 − ℓ')^{1/2}`
into the `h^{1/2}` of `e.nablaw.Lt`. -/
theorem scaleSelection_pred_m_sub_ellPrime_le_h (S : ScaleSelection) :
    S.m - 1 - S.ellPrime ≤ S.h := by
  have := S.ellPrime_add_h
  omega

/-- The upper shell of the split at `m − 1` is nonempty. -/
theorem scalesOrdering_pred_m_lt_LPrime {S : ScaleSelection}
    (hS : ScalesOrdering S) : S.m - 1 < S.LPrime := by
  have := hS.m_lt_LPrime
  omega

/-- The cube index `m` is admissible for the upper shell split at `m − 1`. -/
theorem scaleSelection_m_le_pred_m_add_one (S : ScaleSelection) :
    S.m ≤ S.m - 1 + 1 := by
  omega

/-- The real form of `scaleSelection_pred_m_sub_ellPrime_le_h` used by the `Γ₂`
amplitudes. -/
theorem scaleSelection_rpow_pred_m_sub_ellPrime_le (S : ScaleSelection) {t : ℝ}
    (ht : 0 ≤ t) :
    ((S.m - 1 - S.ellPrime : ℕ) : ℝ) ^ t ≤ ((S.h : ℕ) : ℝ) ^ t := by
  refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ ht
  exact_mod_cast scaleSelection_pred_m_sub_ellPrime_le_h S

end

end SuperdiffusionCLT.Section3.ResponseFields
