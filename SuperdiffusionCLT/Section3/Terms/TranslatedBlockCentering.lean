/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthC

/-!
# Translated-block centering off the centred cube `cu_ℓ`

The centring of the glued flux pairing is transported from the centred cube `cu_ℓ` to every
aligned block: the glued field is constant on its scale-`n` descendants, so on a block of scale at
least `n` the average of the glued pairing is the `descendantsAverage` of the single-block
maximizer pairings over the scale-`n` descendants, and each of those has the same annealed value as
`cu_n` by stationarity of the gluing at scale `n`.
`SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector` identifies the `cu_ℓ` value
with the proxy `q̃` of the printed argument, modulo the integrability `hq`.  This module supplies
the ambient sample measurability and the integrability inputs and composes the statements,
producing the per-block centring needed downstream as `hmean`:

`∀ R ∈ s, ∫ ω, fluxBlockObservable hnu P ℓ n m F i R ω = 0`.

## Two block families, and the printed relation `n ≤ ℓ`

The printed argument centres the aligned scale-`ℓ` blocks (in the proof of `l.RHS.term1`, each
`3^k`-cube is decomposed into aligned `3^ℓ`-blocks), with the glued field glued at scale
`n ≤ ℓ`.  The analytic consumer states its blocks through the *gluing* family
`largeCubeSubcubes d k m`, where the same letter `k` is the gluing scale of
`gluedGradientField hnu ell k m F`.  There the centring rests on the mosaic
`⟨a_ℓ ∇u_k⟩_R = ⟨descendantsAverage of the scale-`k` pairings⟩` and on stationarity at the gluing
scale, both of which require `k ≤ ell` — the printed `n ≤ ℓ`, with `k` here playing the role of
`n`.  This relation is not implied by `hkm : k ≤ m` and `hℓm : ell ≤ m`, so it has to be a
hypothesis.  For `ell < k` the reference object `⟨a_ell ∇u_k⟩_{cu_ell}` is an average of a
`k`-scale field over a strictly smaller cube, which stationarity of the `k`-scale gluing does not
identify with the `k`-block average `⟨a_ell ∇u_k⟩_{cu_k}`.

## Main results

* `maximizerFluxPairing_eq_volumeAverageVec_gluedGradientField` — on a block of the gluing scale
  the single-cube maximizer pairing is the glued cube mean.
* `measurable_maximizerFluxPairing`, `measurable_gluedFluxPairing_originCube` — the ambient
  sample measurability, discharged from the flux cube-mean identity
  `measurable_volumeAverage_flux_gluedGradientField`.
* `integrable_maximizerFluxPairing_originCube`, `integrable_maximizerFluxPairing_of_mem`,
  `integrable_gluedFluxPairing_of_mem` — the integrability inputs, discharged from the annealed
  envelope `integrable_coeffLinftySupBound`.
* `integral_maximizerFluxPairing_eq_originCube_of_mem` — stationarity: the single-block pairing
  has the same expectation on every block of the gluing family.
* `integral_gluedFluxPairing_originCube_eq_qVector`, `integral_gluedFluxPairing_of_mem_eq_qVector`
  — the glued pairing has expectation `q̃` at `cu_ℓ` and on every aligned block of scale at least
  `n`.
* `integral_fluxBlockObservable_eq_zero_of_mem_le_scale` — the per-block centring, with no
  hypothesis beyond the printed `n ≤ ℓ`, the scale ranges and the shell-law data.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-! ## Two functions equal on an open cube have equal cube averages -/

/-- Two functions that agree on the open cube have the same normalized average
there.  This is the congruence for the `openCubeSet` realization used by the
maximizer pairing. -/
private theorem volumeAverage_congr_on_openCubeSet {Q : TriadicCube d} {f g : Vec d → ℝ}
    (h : ∀ x ∈ openCubeSet Q, f x = g x) :
    volumeAverage (openCubeSet Q) f = volumeAverage (openCubeSet Q) g := by
  rw [volumeAverage, volumeAverage,
    MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) h]

/-! ## The single-block maximizer pairing on a block of the gluing scale -/

/-- **The single-cube maximizer pairing is the glued cube mean on a block of the
gluing scale.**  On a scale-`k` sub-cube `z` of the large cube the glued field
`∇u_k` of `e.u.k.def` is the maximizer gradient of `z`
(`gluedGradientField_apply_of_mem_openCubeSet`), so the glued cube mean of the
pairing is `maximizerFluxPairing` of `z`. -/
theorem maximizerFluxPairing_eq_volumeAverageVec_gluedGradientField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L k m : ℕ) (F : Vec d) (i : Fin d) (omega : ShellSeq d)
    {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d k m) :
    maximizerFluxPairing hnu L F i omega z =
      volumeAverageVec (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i := by
  simp only [maximizerFluxPairing, volumeAverageVec]
  exact volumeAverage_congr_on_openCubeSet fun x hx => by
    rw [gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hz hx]

/-- **The single-cube maximizer pairing is measurable in the sample.**  It is the
glued cube mean on a block of the gluing scale, which the flux cube-mean
identity makes measurable. -/
theorem measurable_maximizerFluxPairing [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ)
    (F : Vec d) (i : Fin d) {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d k m) :
    Measurable (fun omega : ShellSeq d => maximizerFluxPairing hnu L F i omega z) := by
  have hfun : (fun omega : ShellSeq d => maximizerFluxPairing hnu L F i omega z) =
      fun omega : ShellSeq d => volumeAverageVec (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i :=
    funext fun omega =>
      maximizerFluxPairing_eq_volumeAverageVec_gluedGradientField hnu L k m F i omega hz
  rw [hfun]
  exact measurable_volumeAverage_flux_gluedGradientField hnu L k m F hz i

/-! ## The sample measurability of the centring input at `cu_ℓ` -/

/-- **The glued flux pairing at the centred cube `cu_ℓ` is measurable in the
sample.**  It is the `descendantsAverage` of the single-block maximizer pairings
over the `3^{d(ℓ-n)}` aligned scale-`n` blocks of `cu_ℓ`, a finite sum of
measurable functions.  This discharges the hypothesis `hmeas` of
the centring identity for the glued flux pairing. -/
theorem measurable_gluedFluxPairing_originCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {n ℓ m : ℕ} (hnℓ : n ≤ ℓ) (hℓm : ℓ ≤ m) (F : Vec d) (i : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      gluedFluxPairing hnu ℓ n m F i omega (originCube d (ℓ : ℤ))) := by
  have hQ0 : originCube d (ℓ : ℤ) ∈
      descendantsAtDepth (originCube d (m : ℤ)) (m - ℓ) := by
    rw [← largeCubeSubcubes_eq_descendantsAtDepth]
    exact originCube_mem_largeCubeSubcubes hℓm
  have hdecomp : (fun omega : ShellSeq d =>
      gluedFluxPairing hnu ℓ n m F i omega (originCube d (ℓ : ℤ))) =
      fun omega : ShellSeq d => descendantsAverage (originCube d (ℓ : ℤ)) (ℓ - n)
        (fun z => maximizerFluxPairing hnu ℓ F i omega z) :=
    funext fun omega =>
      volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer
        hnu hnℓ hℓm F omega hQ0 i
  rw [hdecomp]
  simp only [descendantsAverage]
  have hsum : Measurable (fun omega : ShellSeq d =>
      ∑ z ∈ descendantsAtDepth (originCube d (ℓ : ℤ)) (ℓ - n),
        maximizerFluxPairing hnu ℓ F i omega z) :=
    Finset.measurable_sum _ fun z hz => by
      have hzmem : z ∈ largeCubeSubcubes d n m := by
        rw [largeCubeSubcubes_eq_descendantsAtDepth]
        have h := mem_descendantsAtDepth_trans (Q := originCube d (m : ℤ))
          (R := originCube d (ℓ : ℤ)) hQ0 hz
        rwa [show m - ℓ + (ℓ - n) = m - n from by omega] at h
      exact measurable_maximizerFluxPairing hnu ℓ n m F i hzmem
  exact (measurable_const : Measurable fun _ : ShellSeq d =>
    ((descendantsAtDepth (originCube d (ℓ : ℤ)) (ℓ - n)).card : ℝ)⁻¹).mul hsum

/-! ## The integrability of the two centring inputs

Both integrability inputs of the composition are read off the same
quenched envelope: the pointwise bound `abs_fluxBlockAverageVec_entry_le_centered`
of the glued pairing at the reference scale, whose annealed first moment is
finite by `integrable_coeffLinftySupBound`.  The glued scale `k` plays two roles
below and the pointwise bound is available precisely because the block being
averaged is at least as large as the glued blocks: `k ≤ ell` for the reference
cube `cu_ℓ`, and `k ≤ k` (reflexivity) for a single gluing block. -/

/-- **The `cu_ℓ` block average of the glued pairing is integrable.**  This is
the input `hq` of
`SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector` at the
pinned glued scale: for `k ≤ ℓ`, the glued field is a mosaic of scale-`k`
blocks, so the `cu_ℓ` average is the average of `3^{d(ℓ-k)}` single-block
pairings, each bounded by the quenched envelope of `a_ℓ` on `cu_m`. -/
theorem integrable_volumeAverageVec_gluedGradientField_centredCube [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {ell k m : ℕ} (hkℓ : k ≤ ell) (hℓm : ell ≤ m) (F : Vec d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    ∀ i : Fin d, Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (gluedGradientField hnu ell k m F omega x) i)) P.toMeasure := by
  intro i
  have hmeas : Measurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (gluedGradientField hnu ell k m F omega x) i)) := by
    have hbridge : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (ell : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
            (gluedGradientField hnu ell k m F omega x) i)) =
        fun omega : ShellSeq d =>
          gluedFluxPairing hnu ell k m F i omega (originCube d (ell : ℤ)) := by
      funext omega
      simp only [gluedFluxPairing, volumeAverageVec]
      exact (volumeAverage_cubeSet_eq_openCubeSet (originCube d (ell : ℤ)) _).symm
    rw [hbridge]
    exact measurable_gluedFluxPairing_originCube hnu hkℓ hℓm F i
  refine Integrable.mono'
    ((integrable_coeffLinftySupBound hnu hPrefix hJ2 hJ3 hJ4 hℓm).mul_const
      (nu⁻¹ * Real.sqrt (vecNormSq F)))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs]
  rw [(volumeAverage_cubeSet_eq_openCubeSet (originCube d (ell : ℤ))
      (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
        (gluedGradientField hnu ell k m F omega x) i)).symm]
  simpa only [volumeAverageVec, mul_assoc] using
    abs_fluxBlockAverageVec_entry_le_centered hnu omega (L := ell) (k := k) (r := ell)
      (m := m) hkℓ hℓm (F := F) i

/-- **The single block pairing at the centred cube `cu_k` is integrable.**  This
is the reference value the stationarity transfer produces on every scale-`k`
block: on the gluing block `cu_k` the glued field is the maximizer gradient of
`cu_k`, so the pairing is bounded by the same quenched envelope. -/
theorem integrable_maximizerFluxPairing_originCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell k m : ℕ} (hkm : k ≤ m) (hℓm : ell ≤ m) (F : Vec d) (i : Fin d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    Integrable (fun omega : ShellSeq d =>
      maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ))) P.toMeasure := by
  have hz : originCube d (k : ℤ) ∈ largeCubeSubcubes d k m :=
    originCube_mem_largeCubeSubcubes hkm
  have hbridge : (fun omega : ShellSeq d =>
      maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ))) =
      fun omega : ShellSeq d => volumeAverageVec (openCubeSet (originCube d (k : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (gluedGradientField hnu ell k m F omega x)) i :=
    funext fun omega =>
      maximizerFluxPairing_eq_volumeAverageVec_gluedGradientField hnu ell k m F i omega hz
  rw [hbridge]
  have hmeas : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (k : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (gluedGradientField hnu ell k m F omega x)) i) :=
    measurable_volumeAverage_flux_gluedGradientField hnu ell k m F hz i
  refine Integrable.mono'
    ((integrable_coeffLinftySupBound hnu hPrefix hJ2 hJ3 hJ4 hℓm).mul_const
      (nu⁻¹ * Real.sqrt (vecNormSq F)))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs]
  rw [(volumeAverageVec_cubeSet_eq_openCubeSet (originCube d (k : ℤ))
      (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
        (gluedGradientField hnu ell k m F omega x))).symm]
  exact (abs_fluxBlockAverageVec_entry_le_centered hnu omega (L := ell) (k := k) (r := k)
      (m := m) le_rfl hkm (F := F) i).trans_eq (by rw [mul_assoc])

/-! ## Stationarity: the pairing has the same expectation on every scale-`k`
block -/

/-- The scale of a block of the gluing family is the gluing scale. -/
theorem scale_eq_of_mem_largeCubeSubcubes {k m : ℕ} (hkm : k ≤ m) {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) : z.scale = (k : ℤ) := by
  have hz' : z ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - k) := by
    rwa [largeCubeSubcubes_eq_descendantsAtDepth] at hz
  have hle : (m : ℤ) - ((m - k : ℕ) : ℤ) = (k : ℤ) := by omega
  rw [scale_eq_sub_of_mem_descendantsAtDepth hz']
  simpa only [originCube] using hle

/-- **Stationarity of the single block pairing over the scale-`k` blocks of
`cu_m`.**  The expectation of `maximizerFluxPairing` on any block of the gluing
family equals its expectation on the centred block `cu_k`: the pairing is
translation covariant (`maximizerFluxPairing_translate`) and the shell law is
invariant under the lattice translation `triadicCubeShift z` (by `ShellLawPrefix` and
`ShellLawJ2`), which is `TranslatedBlocks.integral_of_translationCovariant`. -/
theorem integral_maximizerFluxPairing_eq_originCube_of_mem [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell k m : ℕ} (hkm : k ≤ m) (F : Vec d) (i : Fin d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d k m) :
    ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure =
      ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ))
        ∂P.toMeasure := by
  have hscale := scale_eq_of_mem_largeCubeSubcubes (d := d) hkm hz
  have hmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
      maximizerFluxPairing hnu ell F i omega (originCube d z.scale)) P.toMeasure := by
    rw [hscale]
    exact (measurable_maximizerFluxPairing hnu ell k m F i
      (originCube_mem_largeCubeSubcubes hkm)).aestronglyMeasurable
  have h := integral_of_translationCovariant (P := P) hPrefix hJ2
    (F := fun (omega : ShellSeq d) (Q : TriadicCube d) => maximizerFluxPairing hnu ell F i omega Q)
    (fun omega => maximizerFluxPairing_translate hnu ell F i omega z) hmeas
  rw [hscale] at h
  exact h

/-- **The pairing is integrable on every block of the gluing family.**  The
stationarity transfer of the centred reference value `cu_k`. -/
theorem integrable_maximizerFluxPairing_of_mem [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell k m : ℕ} (hkm : k ≤ m) (hℓm : ell ≤ m) (F : Vec d) (i : Fin d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d k m) :
    Integrable (fun omega : ShellSeq d => maximizerFluxPairing hnu ell F i omega z)
      P.toMeasure := by
  have hscale := scale_eq_of_mem_largeCubeSubcubes (d := d) hkm hz
  have heq : (fun omega : ShellSeq d => maximizerFluxPairing hnu ell F i omega z) =
      translateObservable (fun omega : ShellSeq d =>
        maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ))) z := by
    funext omega
    rw [maximizerFluxPairing_translate hnu ell F i omega z, hscale]
    rfl
  rw [heq]
  exact integrable_translateObservable hPrefix hJ2
    (integrable_maximizerFluxPairing_originCube hnu hkm hℓm F i hPrefix hJ2 hJ3 hJ4) z

/-! ## The composition: the per-block centring carried downstream as `hmean`

The reference value `q̃` of
`SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector` is the
expectation of the glued pairing on `cu_ℓ`.  On a block `R` of the gluing family
`largeCubeSubcubes d k m` the glued pairing is the single block pairing
(`k = R.scale`), whose expectation is the `cu_k` value by stationarity, and the
`cu_ℓ` reference value is the average of those same `cu_k` values over the
`3^{d(ℓ-k)}` aligned scale-`k` blocks of `cu_ℓ`.  The two coincide, so the
centred observable `fluxBlockObservable` has mean zero on every block of the
family — the statement carried downstream as `hmean`. -/

/-- **The `cu_ℓ` reference value is the `cu_k` block value.**  For `k ≤ ℓ` the
glued pairing on the reference cube `cu_ℓ` is the `descendantsAverage` of the
single block pairings over its `3^{d(ℓ-k)}` aligned scale-`k` blocks; each has
the expectation of `cu_k` by stationarity, so the `cu_ℓ` expectation is the
`cu_k` expectation. -/
theorem integral_gluedFluxPairing_originCube_eq_maximizerFluxPairing [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {ell k m : ℕ} (hkℓ : k ≤ ell) (hℓm : ell ≤ m) (F : Vec d) (i : Fin d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    ∫ omega : ShellSeq d, gluedFluxPairing hnu ell k m F i omega (originCube d (ell : ℤ))
        ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ)) ∂P.toMeasure := by
  have hkm : k ≤ m := le_trans hkℓ hℓm
  have hQ0 : originCube d (ell : ℤ) ∈
      descendantsAtDepth (originCube d (m : ℤ)) (m - ell) := by
    rw [← largeCubeSubcubes_eq_descendantsAtDepth]
    exact originCube_mem_largeCubeSubcubes hℓm
  have hmem : ∀ z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
      z ∈ largeCubeSubcubes d k m := by
    intro z hz
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans (Q := originCube d (m : ℤ))
      (R := originCube d (ell : ℤ)) hQ0 hz
    rwa [show m - ell + (ell - k) = m - k from by omega] at h
  have hpt : ∀ omega : ShellSeq d,
      gluedFluxPairing hnu ell k m F i omega (originCube d (ell : ℤ)) =
        descendantsAverage (originCube d (ell : ℤ)) (ell - k)
          (fun z => maximizerFluxPairing hnu ell F i omega z) :=
    fun omega => volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer
      hnu hkℓ hℓm F omega hQ0 i
  have hcard : ((descendantsAtDepth (originCube d (ell : ℤ)) (ell - k)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
      (descendantsAtDepth_nonempty (originCube d (ell : ℤ)) (ell - k)))
  have hsum : ∫ omega : ShellSeq d,
        (∑ z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
          maximizerFluxPairing hnu ell F i omega z) ∂P.toMeasure =
      ∑ z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
        ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure :=
    MeasureTheory.integral_finsetSum _
      (fun z hz => integrable_maximizerFluxPairing_of_mem hnu hkm hℓm F i hPrefix hJ2 hJ3 hJ4
        (hmem z hz))
  have hcongr_sum : (∑ z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
        ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure) =
      ∑ _z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
        ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ))
          ∂P.toMeasure :=
    Finset.sum_congr rfl fun z hz =>
      integral_maximizerFluxPairing_eq_originCube_of_mem hnu hkm F i hPrefix hJ2 (hmem z hz)
  calc ∫ omega : ShellSeq d, gluedFluxPairing hnu ell k m F i omega (originCube d (ell : ℤ))
        ∂P.toMeasure
      = ∫ omega : ShellSeq d, descendantsAverage (originCube d (ell : ℤ)) (ell - k)
          (fun z => maximizerFluxPairing hnu ell F i omega z) ∂P.toMeasure := by
        rw [funext hpt]
    _ = ((descendantsAtDepth (originCube d (ell : ℤ)) (ell - k)).card : ℝ)⁻¹ *
          ∫ omega : ShellSeq d,
            (∑ z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
              maximizerFluxPairing hnu ell F i omega z) ∂P.toMeasure := by
        simp only [descendantsAverage]
        rw [MeasureTheory.integral_const_mul]
    _ = ((descendantsAtDepth (originCube d (ell : ℤ)) (ell - k)).card : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
            ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure := by
        rw [hsum]
    _ = ((descendantsAtDepth (originCube d (ell : ℤ)) (ell - k)).card : ℝ)⁻¹ *
          ∑ _z ∈ descendantsAtDepth (originCube d (ell : ℤ)) (ell - k),
            ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ))
              ∂P.toMeasure := by
        rw [hcongr_sum]
    _ = ((descendantsAtDepth (originCube d (ell : ℤ)) (ell - k)).card : ℝ)⁻¹ *
          (((descendantsAtDepth (originCube d (ell : ℤ)) (ell - k)).card : ℝ) *
            ∫ omega : ShellSeq d,
              maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ)) ∂P.toMeasure) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∫ omega : ShellSeq d,
          maximizerFluxPairing hnu ell F i omega (originCube d (k : ℤ)) ∂P.toMeasure :=
        inv_mul_cancel_left₀ hcard _

/-- **The reference value is the proxy**: `∫ gluedFluxPairing(cu_ℓ) = q̃`. -/
theorem integral_gluedFluxPairing_originCube_eq_qVector [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell n m : ℕ} (hnℓ : n ≤ ell) (hℓm : ell ≤ m) (F : Vec d) (i : Fin d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    ∫ omega : ShellSeq d, gluedFluxPairing hnu ell n m F i omega (originCube d (ell : ℤ))
      ∂P.toMeasure = qVector hnu P ell ell n m F i := by
  have hq := integrable_volumeAverageVec_gluedGradientField_centredCube hnu hnℓ hℓm F
    hPrefix hJ2 hJ3 hJ4
  have hb : (fun omega : ShellSeq d =>
      gluedFluxPairing hnu ell n m F i omega (originCube d (ell : ℤ))) =
      fun omega : ShellSeq d => volumeAverageVec (openCubeSet (originCube d (ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (gluedGradientField hnu ell n m F omega x)) i := by
    funext omega
    simp only [gluedFluxPairing, volumeAverageVec]
    exact volumeAverage_cubeSet_eq_openCubeSet (originCube d (ell : ℤ)) _
  rw [hb]
  exact integral_fluxBlockAverageVec_eq_qVector hnu P ell ell n m F hq i

/-! ## The centring on every aligned block of scale at least the gluing scale

The printed argument centers *every* aligned block whose scale is at least the
reference scale `ℓ` (the `3^k`-blocks of the decomposition, `k ≥ ℓ`), with the
glued field glued at scale `n ≤ ℓ` (where `n := ℓ - a`).  The transfers below decouple the
*block* scale `q` from the *coefficient* scale `ell`: the glued field is constant on its scale-`n`
descendants, so the mosaic identity holds at the block's own depth `q - n`, and
each descendant has the expectation of `cu_n` by stationarity.  Hence the
centred observable has mean zero on every aligned block of scale `q ≥ n`, which
covers both the gluing family `q = n` (the blocks of the analytic consumer) and
the printed decomposition blocks (`q ≥ ℓ ≥ n`). -/

/-- **The mosaic on an arbitrary aligned block.**  For an aligned block `Q` of
scale `q ≥ n` the glued pairing is the `descendantsAverage` of the single block
pairings over the `3^{d (q - n)}` aligned scale-`n` blocks inside it.  This is
`RHSTerm1ConcDepthC.volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer`
with the block scale `q` decoupled from the coefficient scale `ell`. -/
theorem gluedFluxPairing_eq_descendantsAverage_of_mem [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell n q m : ℕ} (hnq : n ≤ q) (hqm : q ≤ m) (F : Vec d) (i : Fin d) (omega : ShellSeq d)
    {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d q m) :
    gluedFluxPairing hnu ell n m F i omega Q =
      descendantsAverage Q (q - n) (fun z => maximizerFluxPairing hnu ell F i omega z) := by
  rw [gluedFluxPairing]
  have hG : MemVectorL2 (openCubeSet Q) (gluedGradientField hnu ell n m F omega) :=
    memVectorL2_openCubeSet_gluedGradientField hnu ell n m F omega Q
  have hA : MemVectorL2 (openCubeSet Q) (fun x => matVecMul
      ((coefficientCutoff nu omega ell).toCoeffField x)
      (gluedGradientField hnu ell n m F omega x)) :=
    memVectorL2_matVecMul_coefficientCutoff hnu omega ell Q hG
  have hF : MemLp (hilbertifyVecField (fun x => matVecMul
      ((coefficientCutoff nu omega ell).toCoeffField x)
      (gluedGradientField hnu ell n m F omega x))) 2 (normalizedCubeMeasure Q) :=
    Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hA
  rw [volumeAverageVec_eq_descendantsAverage_memLp Q (q - n) hF i]
  rw [descendantsAverage, descendantsAverage]
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  have hQd : Q ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - q) := by
    rwa [largeCubeSubcubes_eq_descendantsAtDepth] at hQ
  have hzlarge : z ∈ largeCubeSubcubes d n m := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hQd hz
    rwa [show (m - q) + (q - n) = m - n from by omega] at h
  have hmax : maximizerFluxPairing hnu ell F i omega z =
      volumeAverage (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega ell).toCoeffField x)
        (cubeMaximizerGradient hnu omega ell F z x) i) := by
    simp only [maximizerFluxPairing, volumeAverageVec]
  have hstep : volumeAverageVec (cubeSet z) (fun x => matVecMul
      ((coefficientCutoff nu omega ell).toCoeffField x)
      (gluedGradientField hnu ell n m F omega x)) i =
      volumeAverage (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega ell).toCoeffField x)
        (cubeMaximizerGradient hnu omega ell F z x) i) := by
    show volumeAverage (cubeSet z) (fun x => matVecMul
      ((coefficientCutoff nu omega ell).toCoeffField x)
      (gluedGradientField hnu ell n m F omega x) i) = _
    rw [volumeAverage_cubeSet_eq_openCubeSet z, volumeAverage, volumeAverage,
      MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet z) (fun x hx => by
        show matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (gluedGradientField hnu ell n m F omega x) i = matVecMul
          ((coefficientCutoff nu omega ell).toCoeffField x)
          (cubeMaximizerGradient hnu omega ell F z x) i
        rw [gluedGradientField_apply_of_mem_openCubeSet hnu ell n m F omega hzlarge hx])]
  exact hstep.trans hmax.symm

/-- **The glued pairing is integrable on every aligned block of scale `≥ n`.** -/
theorem integrable_gluedFluxPairing_of_mem [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell n q m : ℕ} (hnq : n ≤ q) (hqm : q ≤ m) (hℓm : ell ≤ m) (F : Vec d) (i : Fin d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {Q : TriadicCube d}
    (hQ : Q ∈ largeCubeSubcubes d q m) :
    Integrable (fun omega : ShellSeq d => gluedFluxPairing hnu ell n m F i omega Q)
      P.toMeasure := by
  have hnm : n ≤ m := le_trans hnq hqm
  have hQd : Q ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - q) := by
    rwa [largeCubeSubcubes_eq_descendantsAtDepth] at hQ
  have hpt : (fun omega : ShellSeq d => gluedFluxPairing hnu ell n m F i omega Q) =
      fun omega : ShellSeq d => descendantsAverage Q (q - n)
        (fun z => maximizerFluxPairing hnu ell F i omega z) :=
    funext fun omega => gluedFluxPairing_eq_descendantsAverage_of_mem hnu hnq hqm F i omega hQ
  rw [hpt]
  simp only [descendantsAverage]
  refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
  intro z hz
  have hzlarge : z ∈ largeCubeSubcubes d n m := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hQd hz
    rwa [show (m - q) + (q - n) = m - n from by omega] at h
  exact integrable_maximizerFluxPairing_of_mem hnu hnm hℓm F i hPrefix hJ2 hJ3 hJ4 hzlarge

/-- **The expectation on an arbitrary aligned block of scale `≥ n` is the
`cu_n` block value.** -/
theorem integral_gluedFluxPairing_of_mem_eq_maximizerFluxPairing [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {ell n q m : ℕ} (hnq : n ≤ q) (hqm : q ≤ m) (hℓm : ell ≤ m)
    (F : Vec d) (i : Fin d) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d q m) :
    ∫ omega : ShellSeq d, gluedFluxPairing hnu ell n m F i omega Q ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        maximizerFluxPairing hnu ell F i omega (originCube d (n : ℤ)) ∂P.toMeasure := by
  have hnm : n ≤ m := le_trans hnq hqm
  have hQd : Q ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - q) := by
    rwa [largeCubeSubcubes_eq_descendantsAtDepth] at hQ
  have hmem : ∀ z ∈ descendantsAtDepth Q (q - n), z ∈ largeCubeSubcubes d n m := by
    intro z hz
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hQd hz
    rwa [show (m - q) + (q - n) = m - n from by omega] at h
  have hpt : ∀ omega : ShellSeq d,
      gluedFluxPairing hnu ell n m F i omega Q =
        descendantsAverage Q (q - n) (fun z => maximizerFluxPairing hnu ell F i omega z) :=
    fun omega => gluedFluxPairing_eq_descendantsAverage_of_mem hnu hnq hqm F i omega hQ
  have hcard : ((descendantsAtDepth Q (q - n)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q (q - n)))
  have hsum : ∫ omega : ShellSeq d,
        (∑ z ∈ descendantsAtDepth Q (q - n), maximizerFluxPairing hnu ell F i omega z)
        ∂P.toMeasure =
      ∑ z ∈ descendantsAtDepth Q (q - n),
        ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure :=
    MeasureTheory.integral_finsetSum _
      (fun z hz => integrable_maximizerFluxPairing_of_mem hnu hnm hℓm F i hPrefix hJ2 hJ3 hJ4
        (hmem z hz))
  have hcongr_sum : (∑ z ∈ descendantsAtDepth Q (q - n),
        ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure) =
      ∑ _z ∈ descendantsAtDepth Q (q - n),
        ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega (originCube d (n : ℤ))
          ∂P.toMeasure :=
    Finset.sum_congr rfl fun z hz =>
      integral_maximizerFluxPairing_eq_originCube_of_mem hnu hnm F i hPrefix hJ2 (hmem z hz)
  calc ∫ omega : ShellSeq d, gluedFluxPairing hnu ell n m F i omega Q ∂P.toMeasure
      = ∫ omega : ShellSeq d, descendantsAverage Q (q - n)
          (fun z => maximizerFluxPairing hnu ell F i omega z) ∂P.toMeasure := by
        rw [funext hpt]
    _ = ((descendantsAtDepth Q (q - n)).card : ℝ)⁻¹ *
          ∫ omega : ShellSeq d,
            (∑ z ∈ descendantsAtDepth Q (q - n),
              maximizerFluxPairing hnu ell F i omega z) ∂P.toMeasure := by
        simp only [descendantsAverage]
        rw [MeasureTheory.integral_const_mul]
    _ = ((descendantsAtDepth Q (q - n)).card : ℝ)⁻¹ *
          ∑ z ∈ descendantsAtDepth Q (q - n),
            ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega z ∂P.toMeasure := by
        rw [hsum]
    _ = ((descendantsAtDepth Q (q - n)).card : ℝ)⁻¹ *
          ∑ _z ∈ descendantsAtDepth Q (q - n),
            ∫ omega : ShellSeq d, maximizerFluxPairing hnu ell F i omega (originCube d (n : ℤ))
              ∂P.toMeasure := by
        rw [hcongr_sum]
    _ = ((descendantsAtDepth Q (q - n)).card : ℝ)⁻¹ *
          (((descendantsAtDepth Q (q - n)).card : ℝ) *
            ∫ omega : ShellSeq d,
              maximizerFluxPairing hnu ell F i omega (originCube d (n : ℤ)) ∂P.toMeasure) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∫ omega : ShellSeq d,
          maximizerFluxPairing hnu ell F i omega (originCube d (n : ℤ)) ∂P.toMeasure :=
        inv_mul_cancel_left₀ hcard _

/-- **The glued pairing on every aligned block of scale `≥ n` has expectation
`q̃`** — the printed centring, with the block scale `q` decoupled from both the
coefficient scale `ell` and the gluing scale `n`. -/
theorem integral_gluedFluxPairing_of_mem_eq_qVector [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {ell n q m : ℕ} (hnℓ : n ≤ ell) (hℓm : ell ≤ m) (hnq : n ≤ q) (hqm : q ≤ m)
    (F : Vec d) (i : Fin d) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d q m) :
    ∫ omega : ShellSeq d, gluedFluxPairing hnu ell n m F i omega Q ∂P.toMeasure =
      qVector hnu P ell ell n m F i := by
  calc ∫ omega : ShellSeq d, gluedFluxPairing hnu ell n m F i omega Q ∂P.toMeasure
      = ∫ omega : ShellSeq d,
          maximizerFluxPairing hnu ell F i omega (originCube d (n : ℤ)) ∂P.toMeasure :=
        integral_gluedFluxPairing_of_mem_eq_maximizerFluxPairing hnu hnq hqm hℓm F i
          hPrefix hJ2 hJ3 hJ4 hQ
    _ = ∫ omega : ShellSeq d, gluedFluxPairing hnu ell n m F i omega (originCube d (ell : ℤ))
          ∂P.toMeasure :=
        (integral_gluedFluxPairing_originCube_eq_maximizerFluxPairing hnu hnℓ hℓm F i
          hPrefix hJ2 hJ3 hJ4).symm
    _ = qVector hnu P ell ell n m F i :=
        integral_gluedFluxPairing_originCube_eq_qVector hnu hnℓ hℓm F i hPrefix hJ2 hJ3 hJ4

/-- **The per-block centring on every aligned block of scale `≥ n`** — the
printed *"the definition of `q̃` centers every such block by stationarity"*, with
no hypothesis beyond the printed `n ≤ ℓ`. -/
theorem integral_fluxBlockObservable_eq_zero_of_mem_le_scale [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {ell n q m : ℕ} (hnℓ : n ≤ ell) (hℓm : ell ≤ m) (hnq : n ≤ q) (hqm : q ≤ m)
    (F : Vec d) (i : Fin d) {Q : TriadicCube d} (hQ : Q ∈ largeCubeSubcubes d q m) :
    ∫ omega : ShellSeq d, fluxBlockObservable hnu P ell n m F i Q omega ∂P.toMeasure = 0 := by
  have hobs : (fun omega : ShellSeq d => fluxBlockObservable hnu P ell n m F i Q omega) =
      fun omega : ShellSeq d =>
        gluedFluxPairing hnu ell n m F i omega Q - qVector hnu P ell ell n m F i :=
    funext fun omega => fluxBlockObservable_eq_gluedFluxPairing_sub hnu P ell n m F i Q omega
  rw [hobs, integral_sub
      (integrable_gluedFluxPairing_of_mem hnu hnq hqm hℓm F i hPrefix hJ2 hJ3 hJ4 hQ)
      (integrable_const _),
    integral_gluedFluxPairing_of_mem_eq_qVector hnu hnℓ hℓm hnq hqm F i hPrefix hJ2 hJ3 hJ4 hQ]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

end

end SuperdiffusionCLT.Section3.Terms
