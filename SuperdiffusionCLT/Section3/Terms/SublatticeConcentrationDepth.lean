/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section3.Terms.MaximizerGradientL2
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section3.ResponseFields.StationaryComparison
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing
public import SuperdiffusionCLT.Section2.Annealed.CutoffRealizationPackage
public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Probability.OrliczMoments
public import Homogenization.Book.Ch04.Theorems.Concentration

/-!
# The sublattice concentration of the term-1 observable `a_ℓ ∇ũ_n − q̃`

The sublattice clause of the proof of `l.RHS.term1` reads: "For `k ≥ ell`, each `3^k`-cube is
decomposed into aligned `3^ell`-blocks. After splitting these blocks into a bounded number of
sublattices, the `O(3^ell)` range of dependence allows us to apply Proposition
`p.concentration`, and the definition of `q̃` centers every such block by stationarity."  This
module adapts to the term-1 observable two of the inputs of that step, in the template of the
mixing anchor of `Section2/Annealed/MixingStepEnvelope.lean`:

* the **per-variable envelope** (`abs_fluxBlockAverageVec_entry_le`, with its family and centred
  instances): for every triadic cube `Q` with `openCubeSet Q ⊆ cubeSet cu_m`, every coordinate
  `i` and every shell sequence, the cube average `(a_ℓ ∇ũ_n)_{cubeSet Q} i` is bounded by
  `‖a_ℓ‖_{L^∞(cu_m)} * nu⁻¹ * |F|`: the pointwise operator bound
  `‖a_ℓ(x)‖ ≤ ‖a_ℓ‖_{L^∞(cu_m)}` (`matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound`)
  paired with Cauchy–Schwarz on the cube (`Section2.Norms.abs_volumeAverage_vecDot_le_mul`), the
  `L²` transport of the flux field (`memVectorL2_matVecMul_coefficientCutoff` of
  `RHSTerm1.lean`) and the energy bound `‖∇ũ‖²_{L̲²(Q)} ≤ nu⁻² |F|²`, carried as the explicit
  hypothesis `hn` in the shape `vecCubeLpENorm_gluedGradientField_translate`;
* the **centering** (`integral_fluxBlockAverageVec_eq_qVector`): at the centred cube `cu_ℓ` the
  expectation of the cube average of the flux is exactly the proxy
  `q̃ = qVector hnu P L ell k m F` — this is the definition of `q̃`, the cheap instance of "the
  definition of `q̃` centers every such block".

The term-1 observable is `fluxBlockObservable`, the cube average of the flux at a block,
centered at `q̃`.  It is `a_ℓ ∇ũ_n`, i.e.
`fun omega x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
  (gluedGradientField hnu L k m F omega x)`, with the data
`L = S.ell`, `k = S.n`, `m = S.m`, `F = fluxSlot nu S.LPrime P S.n e`, and the proxy
`q̃ = qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Small helpers -/

/-- The cube norm of a constant field is the Euclidean magnitude of the
constant: the Euclidean magnitude of a constant vector field on the cube. -/
theorem vecCubeLpENorm_const_eq {Q : TriadicCube d} {q : ℝ≥0∞} (hq : q ≠ 0)
    (c : Vec d) :
    vecCubeLpENorm Q q (fun _ : Vec d => c) = ENNReal.ofReal (vecNorm c) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hμ0 : normalizedCubeMeasure Q ≠ 0 := fun h =>
    absurd (normalizedCubeMeasure_apply_univ Q) (by rw [h]; simp)
  show eLpNorm (fun _ : Vec d => HilbertVec.ofVec c) q (normalizedCubeMeasure Q) = _
  rw [eLpNorm_const _ hq hμ0, measure_univ, ENNReal.one_rpow, mul_one,
    ← ofReal_norm]
  exact congrArg ENNReal.ofReal
    (norm_hilbertifyVecField_apply (fun _ : Vec d => c) c)

/-- The `ℝ` reading of a squared cube-norm bound. -/
theorem vecCubeLpENorm_toReal_le_of_sq_le {Q : TriadicCube d} {G : Vec d → Vec d}
    {c : ℝ} (hc : 0 ≤ c)
    (h : vecCubeLpENorm Q 2 G ^ (2 : ℕ) ≤ ENNReal.ofReal c) :
    (vecCubeLpENorm Q 2 G).toReal ≤ Real.sqrt c := by
  have hne : vecCubeLpENorm Q 2 G ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_pow (show (2 : ℕ) ≠ 0 by norm_num)] at h
    exact absurd h (not_le.2 ENNReal.ofReal_lt_top)
  have h1 := (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hne)
    ENNReal.ofReal_ne_top).2 h
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hc] at h1
  exact Real.le_sqrt_of_sq_le h1

/-- The coordinate pairing of a vector field with the unit vector `e_i` is the
`i`-th coordinate. -/
private theorem vecDot_single (v : Vec d) (i : Fin d) :
    vecDot v (Pi.single i 1) = v i := by
  simp [vecDot, Pi.single_apply]

/-- The Euclidean magnitude of the unit coordinate vector is one. -/
private theorem vecNorm_single (i : Fin d) : vecNorm (Pi.single i (1 : ℝ)) = 1 := by
  have hv0 : 0 ≤ vecNorm (Pi.single i (1 : ℝ)) := vecNorm_nonneg _
  have hsq : vecNorm (Pi.single i (1 : ℝ)) ^ 2 = 1 := by
    rw [vecNorm_sq_eq_vecNormSq]
    show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
    simp [vecDot, Pi.single_apply]
  rw [show vecNorm (Pi.single i (1 : ℝ)) = Real.sqrt (vecNorm (Pi.single i (1 : ℝ)) ^ 2) from
    by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hv0], hsq, Real.sqrt_one]

/-- The square root of the squared energy factor `nu⁻¹ * nu⁻¹ * vecNormSq F` is
the linear energy factor `nu⁻¹ * Real.sqrt (vecNormSq F)`. -/
private theorem sqrt_invSq_mul_vecNormSq {nu : ℝ} (hnu : 0 < nu) (F : Vec d) :
    Real.sqrt (nu⁻¹ * nu⁻¹ * vecNormSq F) = nu⁻¹ * Real.sqrt (vecNormSq F) := by
  rw [Real.sqrt_mul (x := nu⁻¹ * nu⁻¹)
      (mul_nonneg (inv_pos.2 hnu).le (inv_pos.2 hnu).le) (vecNormSq F),
    Real.sqrt_mul_self_eq_abs, abs_of_nonneg (inv_pos.2 hnu).le]

/-! ## The per-variable envelope of the flux observable -/

/-- **The per-variable envelope of the term-1 flux observable** (the pointwise
half of the sublattice clause): for every triadic cube `Q` whose open
realization sits in the large cube `cu_m`, every coordinate `i` and every shell
sequence, the cube average of the flux `a_ℓ ∇ũ_n` at `Q` is bounded by

> `‖a_ℓ‖_{L^∞(cu_m)} * nu⁻¹ * |F|`,

with `‖a_ℓ‖_{L^∞(cu_m)}` the carrier `coeffLinftySupBound nu L m` and
the `nu⁻¹ |F|` factor the cube norm of the glued field read from the energy
bound.  The proof is the pointwise operator bound
`matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound` on `cubeSet cu_m`
paired with Cauchy–Schwarz on the cube
(`Section2.Norms.abs_volumeAverage_vecDot_le_mul`); the `L²` membership of the
flux field is `memVectorL2_matVecMul_coefficientCutoff` of
`RHSTerm1.lean` transported to the normalized cube measure, and the energy of
the glued field enters through the hypothesis `hn`. -/
theorem abs_fluxBlockAverageVec_entry_le {Q : TriadicCube d} {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {L k m : ℕ} {F : Vec d} (i : Fin d)
    (hsub : openCubeSet Q ⊆ cubeSet (originCube d (m : ℤ)))
    (hn : (vecCubeLpENorm Q 2 (gluedGradientField hnu L k m F omega)).toReal ≤
      nu⁻¹ * Real.sqrt (vecNormSq F)) :
    |volumeAverageVec (cubeSet Q)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i| ≤
      coeffLinftySupBound nu L m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by
  classical
  set G : Vec d → Vec d := gluedGradientField hnu L k m F omega
  set A : Vec d → Mat d := (coefficientCutoff nu omega L).toCoeffField
  have hB0 : 0 ≤ coeffLinftySupBound nu L m omega :=
    coeffLinftySupBound_nonneg nu (le_of_lt hnu) L m omega
  have hGV : MemVectorL2 (openCubeSet Q) G :=
    memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega Q
  have hmemHf : MemLp (hilbertifyVecField fun x => matVecMul (A x) (G x)) 2
      (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_matVecMul_coefficientCutoff hnu omega L Q hGV)
  have hmemHG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memVectorL2 hGV
  have hmemHb : MemLp (hilbertifyVecField fun _ : Vec d => Pi.single i (1 : ℝ)) 2
      (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (HilbertVec.ofVec (Pi.single i (1 : ℝ)))
  have hcs := Section2.Norms.abs_volumeAverage_vecDot_le_mul
    (Q := Q) (a := fun x => matVecMul (A x) (G x))
    (b := fun _ : Vec d => Pi.single i (1 : ℝ)) hmemHf hmemHb
  have havg : volumeAverageVec (cubeSet Q) (fun x => matVecMul (A x) (G x)) i
      = volumeAverage (cubeSet Q)
          (fun x => vecDot (matVecMul (A x) (G x)) (Pi.single i (1 : ℝ))) := by
    show volumeAverage (cubeSet Q) (fun x => matVecMul (A x) (G x) i) = _
    exact congrArg (volumeAverage (cubeSet Q))
      (funext fun x => (vecDot_single (matVecMul (A x) (G x)) i).symm)
  rw [← havg] at hcs
  -- the single vector carries norm one
  have hq0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hone : (vecCubeLpENorm Q 2 fun _ : Vec d => Pi.single i (1 : ℝ)).toReal = 1 := by
    rw [vecCubeLpENorm_const_eq hq0, vecNorm_single]
    exact ENNReal.toReal_ofReal one_pos.le
  rw [hone, mul_one] at hcs
  -- the dominated field is bounded by `‖a_ℓ‖_∞` times the glued field norm
  have hftop : vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (G x)) ≠ ⊤ :=
    ne_of_lt hmemHf.eLpNorm_lt_top
  have hprod : ENNReal.ofReal (coeffLinftySupBound nu L m omega) * vecCubeLpENorm Q 2 G < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmemHG.eLpNorm_lt_top
  -- the a.e. operator envelope of the cutoff on the cube
  have hOp : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
        coeffLinftySupBound nu L m omega := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact Measure.ae_smul_measure
      ((MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)).mono
        fun x hx =>
          matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu hnu.le omega
            (hsub hx))
      (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hscale : (vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (G x))).toReal ≤
      coeffLinftySupBound nu L m omega * (vecCubeLpENorm Q 2 G).toReal := by
    have hprod' := vecCubeLpENorm_matVecMul_le 2 A G hB0 hmemHf.aestronglyMeasurable hOp
    exact (ENNReal.toReal_le_toReal hftop hprod.ne).2 hprod' |>.trans
      (by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0])
  calc |volumeAverageVec (cubeSet Q)
        (fun x => matVecMul (A x) (G x)) i| ≤
      (vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (G x))).toReal := hcs
    _ ≤ coeffLinftySupBound nu L m omega * (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
      le_trans hscale (mul_le_mul_of_nonneg_left hn hB0)
    _ = coeffLinftySupBound nu L m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by ring

/-- The energy of the glued field on a sub-cube of the family, at the `ℝ`
level: the translation covariance `vecCubeLpENorm_gluedGradientField_translate`
reduces the cube to the centred maximizer of the translated shell sequence,
whose energy is the hypothesis-free bound
`volumeAverage_vecNormSq_cubeMaximizerGradient_le`. -/
theorem vecCubeLpENorm_gluedGradientField_family {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {L k m : ℕ} (hkm : k ≤ m) {F : Vec d}
    {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d k m) :
    (vecCubeLpENorm Q 2 (gluedGradientField hnu L k m F omega)).toReal ≤
      nu⁻¹ * Real.sqrt (vecNormSq F) := by
  rw [vecCubeLpENorm_gluedGradientField_translate hnu omega L hkm F hQ]
  refine le_trans (vecCubeLpENorm_toReal_le_of_sq_le (c := nu⁻¹ * nu⁻¹ * vecNormSq F)
    (mul_nonneg (mul_nonneg (inv_pos.2 hnu).le (inv_pos.2 hnu).le) (vecNormSq_nonneg F))
    (vecCubeLpENorm_two_sq_le_of_volumeAverage_le
      (memVectorL2_cubeMaximizerGradient hnu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L F
        (originCube d (k : ℤ)))
      (volumeAverage_vecNormSq_cubeMaximizerGradient_le hnu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L F
        (originCube d (k : ℤ))))) ?_
  rw [sqrt_invSq_mul_vecNormSq hnu F]

/-- **The per-variable envelope at a sub-cube of the family** (the shape the
sublattice clause reads): for every scale-`k` sub-cube
`Q` of `cu_m`, every coordinate and every shell sequence,
`(a_ℓ ∇ũ_n)_{cubeSet Q} i` is bounded by `‖a_ℓ‖_{L^∞(cu_m)} * nu⁻¹ * |F|`. -/
theorem abs_fluxBlockAverageVec_entry_le_family {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {L k m : ℕ} (hkm : k ≤ m) {F : Vec d} (i : Fin d)
    {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d k m) :
    |volumeAverageVec (cubeSet Q)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i| ≤
      coeffLinftySupBound nu L m omega * nu⁻¹ * Real.sqrt (vecNormSq F) :=
  abs_fluxBlockAverageVec_entry_le hnu omega i
    (Set.Subset.trans (openCubeSet_subset_cubeSet Q)
      (cubeSet_subset_of_mem_largeCubeSubcubes hQ))
    (vecCubeLpENorm_gluedGradientField_family hnu omega hkm hQ)

/-- **The per-variable envelope at the centred cube `cu_r`** for
`k ≤ r ≤ m`: the energy of the glued field on the intermediate cube is
bounded by `vecCubeLpENorm_two_sq_gluedGradientField_le`. -/
theorem abs_fluxBlockAverageVec_entry_le_centered {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {L k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) {F : Vec d}
    (i : Fin d) :
    |volumeAverageVec (cubeSet (originCube d (r : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i| ≤
      coeffLinftySupBound nu L m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by
  refine abs_fluxBlockAverageVec_entry_le hnu omega i
    (Set.Subset.trans (openCubeSet_subset_cubeSet (originCube d (r : ℤ)))
      (cubeSet_subset_of_mem_largeCubeSubcubes (originCube_mem_largeCubeSubcubes hrm))) ?_
  refine le_trans (vecCubeLpENorm_toReal_le_of_sq_le (c := nu⁻¹ * nu⁻¹ * vecNormSq F)
    (mul_nonneg (mul_nonneg (inv_pos.2 hnu).le (inv_pos.2 hnu).le) (vecNormSq_nonneg F))
    (vecCubeLpENorm_two_sq_gluedGradientField_le hnu hkr hrm L F omega)) ?_
  rw [sqrt_invSq_mul_vecNormSq hnu F]

/-! ## The centering: the definition of the proxy `q̃` -/

/-- **The expectation of the block average at the centred cube `cu_ℓ` is the
proxy `q̃`** ("the definition of `q̃` centers every such block"):
the proxy is by definition the annealed cube average
`qVector hnu P L ell k m F`, so the centering is
`qVector_apply` read coordinatewise.  For the term-1 data this is the
pinned instance `L = ell = S.ell`, `k = S.n`, `m = S.m`,
`F = fluxSlot nu S.LPrime P S.n e`. -/
theorem integral_fluxBlockAverageVec_eq_qVector {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (L ell k m : ℕ) (F : Vec d)
    (hq : ∀ i : Fin d, MeasureTheory.Integrable
      (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (ell : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
            (gluedGradientField hnu L k m F omega x) i)) P.toMeasure) (i : Fin d) :
    ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet (originCube d (ell : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
            (gluedGradientField hnu L k m F omega x)) i
      ∂P.toMeasure = qVector hnu P L ell k m F i :=
  (qVector_apply hnu P L ell k m F hq i).symm

/-- The term-1 block observable: the cube average of the flux at the block
`R`, centered at the proxy `q̃`.  With the data
`ell = S.ell`, `k = S.n`, `m = S.m`, `F = fluxSlot nu S.LPrime P S.n e` this is
the observable whose sublattice averages the printed clause concentrates. -/
def fluxBlockObservable {nu : ℝ} (_hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (ell k m : ℕ) (F : Vec d) (i : Fin d) (R : TriadicCube d) (omega : ShellSeq d) : ℝ :=
  volumeAverageVec (cubeSet R)
    (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
      (gluedGradientField _hnu ell k m F omega x)) i - qVector _hnu P ell ell k m F i

end

end SuperdiffusionCLT.Section3.Terms