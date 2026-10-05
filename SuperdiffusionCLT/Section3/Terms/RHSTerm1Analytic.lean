/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1FinalB
public import SuperdiffusionCLT.Section3.Terms.SublatticeConcentrationDepth
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# The two analytic residues of the statement of `l.RHS.term1`

The reduction of `l.RHS.term1` leaves the localization clause `_hLocMin` plus the two
analytic obligations `_hJensen` and `_hConcDepth`.  This module proves the analytic half:

* **`_hJensen`**, whose primitive content is the pair of integrability inputs
  `_hInt1` and `_hInt2` — the componentwise
  `P`-integrability of the annealed `cu_ℓ`-average of `a_ℓ ∇ũ_n` and of
  `a_ℓ ∇ũ_{L'}`.  These are proved unconditionally, from the premises the
  statement already carries:
  * the general bound `abs_volumeAverageVec_cutoff_gluedGradient_le_centered`
    (pointwise operator dominance of the cutoff on `cu_m` against the `L²`
    energy of the glued field on `cu_r`, in the shape of
    `SublatticeConcentrationDepth.abs_fluxBlockAverageVec_entry_le` with the
    cutoff level and the glued level separated);
  * the measurability `measurable_volumeAverageVec_cutoff_gluedGradient` of the
    average in the sample (the cube mean is the inner product of the cut-off row
    class with the glued class, both measurable in the sample);
  * the domination by the integrable envelope `coeffLinftySupBound nu Lc m`
    (`integrable_coeffLinftySupBound`, the `Γ₂` first moment of
    `CoefficientLinftyMoments`).
* **`_hConcDepth`**, reduced to a *numeric* gate on its constant:
  the printed depth-moment clause holds at every
  `Cc` dominating `3^{d (m - ℓ)}`, because the descendant Jensen bound
  `vecDepthSqMoment_le_vecSqAvg_of_memVectorL2` (the `L²` tiling
  plus the cube Jensen on each descendant) makes the depth weight
  `3^{-d (m - j - ℓ)} ≤ 1` absorb the loss.
  The residue of `_hConcDepth` is thus exactly the *pin* of `Cc`, not the shape
  of the display.

The `l.RHS.term1` conclusion then follows from the localization clause (in the
abbreviation `LocMinClause`), the numeric gate on `Cc`, and the pigeonhole side
condition — with `_hJensen`, `_hInt1`, `_hInt2` and `_hConcDepth` all gone.
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

/-! ## The integrable envelope of the cutoff coefficient -/

/-- **The annealed first moment of the `L^∞(cu_m)` envelope of the cutoff
coefficient is finite**: `coeffLinftySupBound nu L m` is `P`-integrable for
`L ≤ m`.  This is the `Γ₂` tail of
`isBigO_gammaSigma_coeffLinftySupBound` read at `k = 1`
(`Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two`), the envelope being
nonnegative by `coeffLinftySupBound_nonneg`. -/
theorem integrable_coeffLinftySupBound {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {L m : ℕ} (hLm : L ≤ m) :
    MeasureTheory.Integrable (fun omega : ShellSeq d => coeffLinftySupBound nu L m omega)
      P.toMeasure := by
  have hB0 : ∀ omega : ShellSeq d, 0 ≤ coeffLinftySupBound nu L m omega :=
    coeffLinftySupBound_nonneg nu hnu.le L m
  have hAmp : 0 < coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m := by
    rw [coeffLinftyGammaTwoAmplitude, streamCutoffLinftyGammaTwoAmplitude]
    refine add_pos_of_nonneg_of_pos (le_of_lt hnu) (mul_pos gammaTriangleConst_pos ?_)
    exact add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_shellValueLargeCubeConst d))
        (Real.sqrt_pos.2 (by
          have hmc : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le m
          linarith only [hmc])))
      (mul_nonneg (largeCubeLinftyConst_pos hPrefix).le
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have hint := Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
    (mu := P.toMeasure)
    (X := fun omega : ShellSeq d => coeffLinftySupBound nu L m omega)
    (A := coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m)
    hAmp (measurable_coeffLinftySupBound nu L m).aemeasurable
    (isBigO_gammaSigma_coeffLinftySupBound hPrefix hJ2 hJ3 hJ4
      (hnu := hnu.le) hLm) 1
  exact (MeasureTheory.integrable_congr
    (Filter.Eventually.of_forall fun omega => by
      show |coeffLinftySupBound nu L m omega| ^ ((1 : ℕ) : ℝ) =
        coeffLinftySupBound nu L m omega
      rw [abs_of_nonneg (hB0 omega), Nat.cast_one, Real.rpow_one])).1 hint

/-! ## The per-cube envelope with the cutoff level and the glued level separated -/

/-- The coordinate pairing of a vector field with the unit vector `e_i` is the
`i`-th coordinate. -/
private theorem vecDot_unit (v : Vec d) (i : Fin d) :
    vecDot v (Pi.single i 1) = v i := by
  simp [vecDot, Pi.single_apply]

/-- The Euclidean magnitude of the unit coordinate vector is one. -/
private theorem vecNorm_unit (i : Fin d) : vecNorm (Pi.single i (1 : ℝ)) = 1 := by
  have hv0 : 0 ≤ vecNorm (Pi.single i (1 : ℝ)) := vecNorm_nonneg _
  have hsq : vecNorm (Pi.single i (1 : ℝ)) ^ 2 = 1 := by
    rw [Setup.vecNorm_sq_eq_vecNormSq]
    show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
    simp [vecDot, Pi.single_apply]
  rw [show vecNorm (Pi.single i (1 : ℝ)) =
      Real.sqrt (vecNorm (Pi.single i (1 : ℝ)) ^ 2) from
    by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hv0], hsq, Real.sqrt_one]

/-- The square root of the squared energy factor `nu⁻¹ * nu⁻¹ * vecNormSq F` is
the linear energy factor `nu⁻¹ * Real.sqrt (vecNormSq F)`. -/
private theorem sqrt_invSq_mul_vecNormSq_aux {nu : ℝ} (hnu : 0 < nu) (F : Vec d) :
    Real.sqrt (nu⁻¹ * nu⁻¹ * vecNormSq F) = nu⁻¹ * Real.sqrt (vecNormSq F) := by
  rw [Real.sqrt_mul (x := nu⁻¹ * nu⁻¹)
      (mul_nonneg (inv_pos.2 hnu).le (inv_pos.2 hnu).le) (vecNormSq F),
    Real.sqrt_mul_self_eq_abs, abs_of_nonneg (inv_pos.2 hnu).le]

/-- **The per-variable envelope of the cutoff flux at a general cube**, with the
cutoff level `Lc` and the glued level `Lg` separated: for every triadic cube `Q`
whose open realization sits in the large cube `cu_m`,

> `|(a_{Lc} ∇ũ)_{cubeSet Q, i}| ≤ ‖a_{Lc}‖_{L^∞(cu_m)} * nu⁻¹ * |F|`,

the energy of the glued field entering through the hypothesis `hn` in the shape
the energy lemmas supply on the scales they cover.  This is
`SublatticeConcentrationDepth.abs_fluxBlockAverageVec_entry_le` with the two
levels separated, which the term-1 pair `(Lc, Lg) = (ℓ, ℓ)` and `(ℓ, L')`
requires. -/
theorem abs_volumeAverageVec_cutoff_gluedGradient_le {Q : TriadicCube d} {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) {Lc Lg k m : ℕ} {F : Vec d} (i : Fin d)
    (hsub : openCubeSet Q ⊆ cubeSet (originCube d (m : ℤ)))
    (hn : (vecCubeLpENorm Q 2 (gluedGradientField hnu Lg k m F omega)).toReal ≤
      nu⁻¹ * Real.sqrt (vecNormSq F)) :
    |volumeAverageVec (cubeSet Q)
        (fun x => matVecMul ((coefficientCutoff nu omega Lc).toCoeffField x)
          (gluedGradientField hnu Lg k m F omega x)) i| ≤
      coeffLinftySupBound nu Lc m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by
  classical
  set G : Vec d → Vec d := gluedGradientField hnu Lg k m F omega
  set A : Vec d → Mat d := (coefficientCutoff nu omega Lc).toCoeffField
  have hB0 : 0 ≤ coeffLinftySupBound nu Lc m omega :=
    coeffLinftySupBound_nonneg nu (le_of_lt hnu) Lc m omega
  have hGV : MemVectorL2 (openCubeSet Q) G :=
    memVectorL2_openCubeSet_gluedGradientField hnu Lg k m F omega Q
  have hmemHf : MemLp (hilbertifyVecField fun x => matVecMul (A x) (G x)) 2
      (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_matVecMul_coefficientCutoff hnu omega Lc Q hGV)
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
      (funext fun x => (vecDot_unit (matVecMul (A x) (G x)) i).symm)
  rw [← havg] at hcs
  have hq0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hone : (vecCubeLpENorm Q 2 fun _ : Vec d => Pi.single i (1 : ℝ)).toReal = 1 := by
    rw [vecCubeLpENorm_const_eq hq0, vecNorm_unit]
    exact ENNReal.toReal_ofReal one_pos.le
  rw [hone, mul_one] at hcs
  have hftop : vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (G x)) ≠ ⊤ :=
    ne_of_lt hmemHf.eLpNorm_lt_top
  have hprod : ENNReal.ofReal (coeffLinftySupBound nu Lc m omega) * vecCubeLpENorm Q 2 G
      < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmemHG.eLpNorm_lt_top
  have hOp : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      matrixOperatorNorm ((coefficientCutoff nu omega Lc).toCoeffField x) ≤
        coeffLinftySupBound nu Lc m omega := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact Measure.ae_smul_measure
      ((MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)).mono
        fun x hx =>
          matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu hnu.le omega
            (hsub hx))
      (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hscale : (vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (G x))).toReal ≤
      coeffLinftySupBound nu Lc m omega * (vecCubeLpENorm Q 2 G).toReal := by
    have hprod' := vecCubeLpENorm_matVecMul_le 2 A G hB0 hmemHf.aestronglyMeasurable hOp
    exact (ENNReal.toReal_le_toReal hftop hprod.ne).2 hprod' |>.trans
      (by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0])
  calc |volumeAverageVec (cubeSet Q)
        (fun x => matVecMul (A x) (G x)) i| ≤
      (vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (G x))).toReal := hcs
    _ ≤ coeffLinftySupBound nu Lc m omega * (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
      le_trans hscale (mul_le_mul_of_nonneg_left hn hB0)
    _ = coeffLinftySupBound nu Lc m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by ring

/-- **The per-variable envelope at the centred cube `cu_r`**, for `k ≤ r ≤ m` and
with the cutoff level and the glued level separated: the energy hypothesis is
`vecCubeLpENorm_two_sq_gluedGradientField_le` at the glued level. -/
theorem abs_volumeAverageVec_cutoff_gluedGradient_le_centered {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {Lc Lg k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) {F : Vec d}
    (i : Fin d) :
    |volumeAverageVec (openCubeSet (originCube d (r : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega Lc).toCoeffField x)
          (gluedGradientField hnu Lg k m F omega x)) i| ≤
      coeffLinftySupBound nu Lc m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by
  rw [← volumeAverageVec_cubeSet_eq_openCubeSet]
  refine abs_volumeAverageVec_cutoff_gluedGradient_le hnu omega i
    (Set.Subset.trans (openCubeSet_originCube_subset hrm)
      (openCubeSet_subset_cubeSet (originCube d (m : ℤ)))) ?_
  refine le_trans (vecCubeLpENorm_toReal_le_of_sq_le (c := nu⁻¹ * nu⁻¹ * vecNormSq F)
    (mul_nonneg (mul_nonneg (inv_pos.2 hnu).le (inv_pos.2 hnu).le) (vecNormSq_nonneg F))
    (vecCubeLpENorm_two_sq_gluedGradientField_le hnu hkr hrm Lg F omega)) ?_
  rw [sqrt_invSq_mul_vecNormSq_aux hnu F]

/-! ## Measurability of the average in the sample -/

/-- **The annealed `cu_r`-average of the cutoff flux is measurable in the
sample.**  The cube mean is the inner product of the cut-off coefficient row
class with the `L²(cu_m)` class of the glued field
(`volumeAverageVec_matVecMul_eq_inner`); the row class is measurable in the
sample (`measurable_cutOffRowClass`, the coefficient being Caratheodory) and the
glued class is too (`measurable_gluedGradientClass`).  The cutoff level `Lc` and
the glued level `Lg` are independent, and the only geometric input is
`r ≤ m`. -/
theorem measurable_volumeAverageVec_cutoff_gluedGradient [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {Lc Lg k r m : ℕ} (hr : r ≤ m) (F : Vec d) (i : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (r : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega Lc).toCoeffField x)
          (gluedGradientField hnu Lg k m F omega x)) i) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hVU : openCubeSet (originCube d (r : ℤ)) ⊆ openCubeSet (originCube d (m : ℤ)) :=
    openCubeSet_originCube_subset hr
  have hVmeas : MeasurableSet (openCubeSet (originCube d (r : ℤ))) :=
    (isOpen_openCubeSet (originCube d (r : ℤ))).measurableSet
  have hrow : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (Set.indicator (openCubeSet (originCube d (r : ℤ)))
        (fun y => (fun j => (coefficientCutoff nu omega Lc).toCoeffField y i j : Vec d))) :=
    fun omega => (memVectorL2_of_continuous (m : ℤ)
      (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega Lc i j)).indicator
      hVmeas
  have hglued := measurable_gluedGradientClass (d := d) hnu Lg k m F
  have hEq : (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet (originCube d (r : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega Lc).toCoeffField x)
            (gluedGradientField hnu Lg k m F omega x)) i) =
      fun omega : ShellSeq d => (MeasureTheory.volume (openCubeSet (originCube d (r : ℤ)))).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hrow omega))
          (toHilbertVectorL2OfVecField
            (memVectorL2_gluedGradientField hnu Lg k m F omega (originCube d (m : ℤ)))) := by
    funext omega
    exact volumeAverageVec_matVecMul_eq_inner hVU hVmeas
      (fun y => (coefficientCutoff nu omega Lc).toCoeffField y)
      (memVectorL2_gluedGradientField hnu Lg k m F omega (originCube d (m : ℤ))) i (hrow omega)
  rw [hEq]
  exact measurable_const.mul (continuous_inner.measurable.comp
    ((measurable_cutOffRowClass Lc m (originCube d (r : ℤ)) hVmeas i hrow).prodMk hglued))

/-! ## The two integrability inputs `_hInt1` and `_hInt2` of `_hJensen` -/

/-- **The componentwise integrability of the annealed `cu_r`-average of the
cutoff flux.**  The average is measurable in the sample
(`measurable_volumeAverageVec_cutoff_gluedGradient`) and bounded pointwise by the
integrable envelope `coeffLinftySupBound nu Lc m` times the energy factor
(`abs_volumeAverageVec_cutoff_gluedGradient_le_centered`,
`integrable_coeffLinftySupBound`), so `Integrable.mono'` closes it.  The
hypotheses are exactly the ones the statement already carries: `Lc ≤ m`
for the envelope, and `k ≤ r ≤ m` for the energy of the glued field. -/
theorem integrable_volumeAverageVec_cutoff_gluedGradient [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {Lc Lg k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) (hLcm : Lc ≤ m) (F : Vec d)
    (i : Fin d) :
    MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (r : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega Lc).toCoeffField x)
          (gluedGradientField hnu Lg k m F omega x)) i) P.toMeasure := by
  have hB := integrable_coeffLinftySupBound (d := d) hnu hPrefix hJ2 hJ3 hJ4 hLcm
  refine Integrable.mono' (hB.mul_const (nu⁻¹ * Real.sqrt (vecNormSq F)))
    (measurable_volumeAverageVec_cutoff_gluedGradient (d := d) hnu hrm F i).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, ← mul_assoc]
  exact abs_volumeAverageVec_cutoff_gluedGradient_le_centered (Lc := Lc) (Lg := Lg) (k := k)
    hnu omega hkr hrm (F := F) i

/-- **`_hInt1` of the `l.RHS.term1` reduction.**  The
componentwise `P`-integrability of the annealed `cu_ℓ`-average of
`a_ℓ ∇ũ_n` with `F = fluxSlot nu S.LPrime P S.n e`; the scale facts are
`S.n < S.ell < S.m` of `e.scales.ordering`. -/
theorem term1_hInt1 (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) :
    ∀ i : Fin d, MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x)) i) P.toMeasure :=
  fun i => integrable_volumeAverageVec_cutoff_gluedGradient (d := d) hnu hPrefix hJ2 hJ3 hJ4
    (Lc := S.ell) (Lg := S.ell) (k := S.n) (r := S.ell) (m := S.m)
    (le_of_lt hSorder.n_lt_ell)
    (le_of_lt (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m))
    (le_of_lt (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m))
    (fluxSlot nu S.LPrime P S.n e) i

/-- **`_hInt2` of the `l.RHS.term1` reduction.**  The
componentwise `P`-integrability of the annealed `cu_ℓ`-average of
`a_ℓ ∇ũ_{L'}`, the cutoff level `S.ell` and the glued level `S.LPrime` being
independent in the envelope. -/
theorem term1_hInt2 (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) :
    ∀ i : Fin d, MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x)) i) P.toMeasure :=
  fun i => integrable_volumeAverageVec_cutoff_gluedGradient (d := d) hnu hPrefix hJ2 hJ3 hJ4
    (Lc := S.ell) (Lg := S.LPrime) (k := S.n) (r := S.ell) (m := S.m)
    (le_of_lt hSorder.n_lt_ell)
    (le_of_lt (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m))
    (le_of_lt (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m))
    (fluxSlot nu S.LPrime P S.n e) i

/-! ## The depth-moment residue `_hConcDepth`

The printed clause `_hConcDepth` of `term1_finalB` is a moment bound: the
annealed `∫⁻` of the depth-`j` moment of the pairing field at `cu_m` is
controlled by the annealed `∫⁻` of its `L̲²(cu_m)` norm, with the depth weight
`3^{-d (m - j - ℓ)}`.  The depth weight is at most one, so the clause is
*weaker* than the unweighted bound; that is what is proved here: the descendant
Jensen bound `vecDepthSqMoment_le_vecSqAvg_of_memVectorL2` (the `L²` tiling
`vecSqAvg_eq_descendantsAverage_memLp` plus cube Jensen on each descendant, no
continuity of the field) gives the clause at every constant dominating
`3^{d (m - ℓ)}`, which is therefore the only content of `Cc` that the display
carries. -/

/-- **Cube Jensen for an `L²` field**: the squared magnitude of the cube average
of an `L²` vector field is at most its squared normalized `L̲²` norm.  This is
`ofReal_vecNormSq_volumeAverageVec_le` read through
`toReal_cubeLpENorm_two_sq`, and it needs no continuity of the field. -/
theorem vecNormSq_volumeAverageVec_le_vecSqAvg_of_memVectorL2 {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    vecNormSq (volumeAverageVec (cubeSet Q) F) ≤ vecSqAvg Q F := by
  have hsq : vecSqAvg Q F = (vecCubeLpENorm Q 2 F).toReal ^ 2 := by
    simpa only [vecSqAvg, vecCubeLpENorm] using
      (toReal_cubeLpENorm_two_sq Q (memLp_hilbertifyVecField_of_memVectorL2 hF)).symm
  rw [hsq, volumeAverageVec_cubeSet_eq_openCubeSet]
  have hfin : vecCubeLpENorm Q 2 F ≠ ⊤ :=
    (memLp_hilbertifyVecField_of_memVectorL2 hF).eLpNorm_lt_top.ne
  have h2 : vecCubeLpENorm Q 2 F ^ (2 : ℕ) =
      ENNReal.ofReal ((vecCubeLpENorm Q 2 F).toReal ^ 2) :=
    calc vecCubeLpENorm Q 2 F ^ (2 : ℕ)
        = (ENNReal.ofReal (vecCubeLpENorm Q 2 F).toReal) ^ (2 : ℕ) := by
          rw [ENNReal.ofReal_toReal hfin]
      _ = ENNReal.ofReal ((vecCubeLpENorm Q 2 F).toReal ^ 2) :=
          (ENNReal.ofReal_pow ENNReal.toReal_nonneg 2).symm
  have h := ofReal_vecNormSq_volumeAverageVec_le hF
  rw [h2] at h
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 h

/-- An `L²` field on a cube is `L²` on every descendant cube: the open
descendants are contained in the closed parent, and the closed parent is
a.e. equal to the open one. -/
theorem memVectorL2_openCubeSet_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) : MemVectorL2 (openCubeSet R) F := by
  have hBig : MemVectorL2 (cubeSet Q) F := by
    show MemLp F 2 (volumeMeasureOn (cubeSet Q))
    rw [show volumeMeasureOn (cubeSet Q) = volumeMeasureOn (openCubeSet Q) from
      MeasureTheory.Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)]
    exact hF
  exact memVectorL2_mono
    ((openCubeSet_subset_cubeSet R).trans (cubeSet_subset_of_mem_descendantsAtDepth hR))
    hBig

/-- **The descendant Jensen bound**: for an `L²` field on `Q`, the depth-`j`
moment of its cube averages is at most its squared normalized `L̲²` norm on `Q`.
This holds without any continuity hypothesis. -/
theorem vecDepthSqMoment_le_vecSqAvg_of_memVectorL2 (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    vecDepthSqMoment Q j F ≤ vecSqAvg Q F := by
  rw [vecDepthSqMoment,
    vecSqAvg_eq_descendantsAverage_memLp (Q := Q) (F := F) j
      (memLp_hilbertifyVecField_of_memVectorL2 hF)]
  exact descendantsAverage_le_descendantsAverage Q j fun R hR =>
    vecNormSq_volumeAverageVec_le_vecSqAvg_of_memVectorL2
      (memVectorL2_openCubeSet_of_mem_descendantsAtDepth hR hF)

end

end SuperdiffusionCLT.Section3.Terms
