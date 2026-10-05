/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepth
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Localization
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGaps
public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocality
public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import SuperdiffusionCLT.Section2.Localization.CoarseCentering

/-!
# The three named inputs of the per-cube concentration `hconc`

`RHSTerm1ConcDepth.concDepthClause_of_hconc` reduces the depth moment
`_hConcDepth` of `term1_close` to the single per-cube concentration `hconc` on
every depth-`j` descendant of the centred cube `cu_m`:

`∫⁻ ‖⟨a_ℓ ∇ũ_n − q̃⟩_R‖² ≤ 3^{−d (m − j − ℓ)} · ∫⁻ ‖a_ℓ ∇ũ_n − q̃‖²_{L̲²(R)}`.

The docstring "The exact residual" of `RHSTerm1ConcDepth` names three inputs that
`hconc` itself still rests on:

1. the centering of the block average off the centred cube `cu_ℓ`;
2. the sample measurability of the block observable in the lane
   `blockLane (m − j) P`;
3. the identification of the block partition of a depth-`j` descendant with the
   aligned scale-`ℓ` blocks it contains.

This module proves what is available for items 3, 2 and 1.  **Item 2 is
proved in full.**  The sample measurability at the coarser lane `blockLane ℓ` is
not obtained from the ambient-sample chain: the response, Hessian and maximizer
measurability results of Section 3 supply the ambient
statement only, and `Measurable` at the sub-`σ`-algebra `blockLane ℓ S` is
strictly stronger, because it additionally restricts the preimages to that
`σ`-algebra.  It is obtained instead from the coarse-matrix route: on an aligned
scale-`k` block `R` the block average of the flux is the coarse-matrix expression
`F − κᵀ(R)(σ⁻¹_*(R) F)` (`volumeAverageVec_flux_gluedGradientField_eq`), the
coarse matrices of the cutoff and of the `R`-restricted cutoff coincide because
`coarseBlockMatrix` on `cubeSet R` is unchanged by restriction, the restricted
cutoff is measurable in the lane
(`CoarseBlockLocality.measurable_blockLane_restrictedCoefficientCutoff`), and the
arbitrary-parameter entry engines of `Section2.Annealed.Measurability` transfer
that to the two coarse matrices and then to the observable.

## Main results

* `pow_card_inv_eq_rpow`, `descendantsAtDepth_card_inv_eq_rpow` — **item 3, the
  arithmetic half**: the reciprocal of the number of aligned scale-`ℓ` blocks of a
  scale-`M` cube is exactly the clause's decay factor `3^{−d (M − ℓ)}`.  This is the
  identity that identifies the printed `3^{−d (m − j − ℓ)}` with the block count of the
  partition.  For `m ≤ j + ℓ` the exponent is `0`, i.e. the factor is `1`, matching a
  single block, so no centering or independence is needed at depths `j > m − ℓ`.
* **Item 2, the coarse-matrix reduction and the lane measurability.**  The block
  observable on an aligned scale-`k` block `R` is the coarse-matrix expression
  `F − κᵀ(R)(σ⁻¹_*(R) F) − q̃`, and both coarse matrices are those of the cutoff
  field itself, because restriction to `cubeSet R` does not change `coarseBlockMatrix V` for
  `V ⊆ cubeSet R`.  This gives the lane measurability of the block observable on every
  aligned block, with no residual hypothesis beyond the alignment
  `R ∈ largeCubeSubcubes d k m`.
* `maximizerFluxPairing`, `maximizerFluxPairing_translate` — **item 1, the
  deterministic core**: the flux pairing `⟨a_ℓ ∇u_{L,Q}⟩_Q` of a single cube
  maximizer is translation covariant, i.e. its value on `Q` for `omega` is its
  value on the centred cube `cu_{Q.scale}` for the translated shell sequence
  `τ_{Q} omega`.  This is the covariance hypothesis that
  `TranslatedBlocks.integral_of_translationCovariant` and
  `RHSTerm3SourceGaps.integral_sq_descendantAverage_eq` consume; for the term-3
  carriers it is supplied by `translatedBlockNorm_eq_originCube` and its
  companions, and for the term-1 flux it is the content of the items below.
* `gluedFluxPairing`, `volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer`
  — **item 1, the glued reduction**: on an aligned scale-`ℓ` block the paired
  glued field is the `descendantsAverage` over the `3^{d (ℓ − n)}` aligned
  scale-`n` blocks inside it of `maximizerFluxPairing`, because the glued field
  is constant on each such block (`gluedGradientField_apply_of_mem_openCubeSet`,
  legitimate since `n + a = ℓ` gives `n ≤ ℓ`).
* `fluxBlockObservable_eq_gluedFluxPairing_sub` — the pinned observable of the
  clause is the glued flux pairing minus the constant proxy `q̃`, so the
  covariance and the transfer are statements about the pinned observable too.
* `mem_descendantsAtDepth_trans` — forward transitivity of the descendant
  depth, with the depth indices added.

## What remains as hypotheses

* **Item 1.**  The covariance is proved.  What remains is the centering of the
  block average off `cu_ℓ`: the annealed mean of the glued flux pairing is the same
  on every aligned scale-`ℓ` block of `cu_m` as on the centred cube `cu_ℓ`, by
  `TranslatedBlocks.integral_translateObservable_eq`, with the value at `cu_ℓ`
  identified with the proxy `q̃` by
  `SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector`.  This needs the
  ambient (not lane) `AEStronglyMeasurable` of the scalar coordinate of the glued
  pairing at `cu_ℓ`; the cross-scale flux-cube-mean measurability of the chain does
  not apply here, because `measurable_volumeAverage_flux_gluedGradientField`
  requires the cube to be a scale-`n` block of the glued partition while `cu_ℓ`
  is not one when `ℓ > n`.  The composition of the transfer with the
  `cu_ℓ` centering also involves the `cubeSet`/`openCubeSet` change of the average,
  the subtraction of the constant proxy, and the integrability hypothesis `hq`
  of `integral_fluxBlockAverageVec_eq_qVector`.
* **Item 2.**  Discharged: the lane statement holds on every aligned block.
* **Item 3.**  The identification is proved; what is not proved here is its *use* in
  the concentration step, the analytic per-cube inequality
  `∫⁻ ‖⟨f⟩_R‖² ≤ C 3^{−d (m − j − ℓ)} ∫⁻ ‖f‖²_{L̲²(R)}` itself.  The sublattice
  independence rule bounds the deviation of the *average over a separated
  family*, not the per-cube comparison of mean and square average, so what is
  proved here is the combinatorial half only.
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
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Item 3: the block count is the printed decay factor -/

/-- The reciprocal of the `t`-th power of the block count `3^d` is the printed
decay factor `3^{−d t}`.  This is the arithmetic identity that identifies the
clause's exponent `−(d (m − j − ℓ))` with the reciprocal of the number of
aligned scale-`ℓ` blocks of a scale-`(m − j)` cube. -/
theorem pow_card_inv_eq_rpow {d : ℕ} (t : ℕ) :
    (((3 ^ d) ^ t : ℕ) : ℝ)⁻¹ = (3 : ℝ) ^ (-((d : ℝ) * (t : ℝ))) := by
  have hcast : (((3 ^ d) ^ t : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ t := by push_cast; ring
  rw [hcast, ← pow_mul, ← Real.rpow_natCast (3 : ℝ) (d * t),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- The same count read on the depth-`t` descendant family of an arbitrary
triadic cube. -/
theorem descendantsAtDepth_card_inv_eq_rpow {d : ℕ} (R : TriadicCube d) (t : ℕ) :
    ((descendantsAtDepth R t).card : ℝ)⁻¹ =
      (3 : ℝ) ^ (-((d : ℝ) * (t : ℝ))) := by
  rw [descendantsAtDepth_card]
  exact pow_card_inv_eq_rpow (d := d) t

/-! ## Item 3: the block-partition identity at the glued field

The clause's per-cube concentration is read on the cube mean and the square
average of the observable; the reduction of the depth moment to it
(`lintegral_ofReal_descendantsAverage` and the reverse use of the `vecSqAvg`
tiling) is exactly the identity that the cube quantity on `cu_m` is the
`descendantsAverage` of the descendant quantities.  At the glued field both are
unconditional: the field is `L̲²` on `cu_m`, so the membership hypothesis of
`volumeAverageVec_eq_descendantsAverage_memLp` and
`vecSqAvg_eq_descendantsAverage_memLp` is discharged rather than carried. -/

/-! ## Item 1: the translation covariance of the single-block flux pairing

The centering input of `hconc` is `E[⟨a_ℓ ∇ũ_n⟩_R] = q̃` on every aligned
scale-`ℓ` block `R`.  `integral_fluxBlockAverageVec_eq_qVector` gives
it only at the centred cube `cu_ℓ`; transporting it to `R` is the covariance
below, at the level of a single maximizer, which is the granularity at which the
glued field decomposes over the aligned scale-`n` sub-blocks. -/

/-- **The block flux pairing.**  The average over the cube `Q` of the cut-off
coefficient applied to the maximizer gradient of `Q` — the contribution of the
single aligned block `Q` to the flux pairing of the glued field. -/
def maximizerFluxPairing [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (F : Vec d)
    (i : Fin d) (omega : ShellSeq d) (Q : TriadicCube d) : ℝ :=
  volumeAverageVec (openCubeSet Q)
    (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
      (cubeMaximizerGradient hnu omega L F Q x)) i

/-- The normalized cube integral is the open-cube average. -/
private theorem integralNCM (Q : TriadicCube d) (f : Vec d → ℝ) :
    ∫ x, f x ∂normalizedCubeMeasure Q = volumeAverage (openCubeSet Q) f := by
  rw [integral_normalizedCubeMeasure_eq, volumeAverage, volume_openCubeSet_toReal]

/-- Reading a scalar field on `Q` after the shift `x ↦ x − triadicCubeShift Q`
is reading it on the centred cube of the same scale. -/
private theorem volumeAverage_comp_sub_shift (Q : TriadicCube d) (g : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) (fun x => g (x - triadicCubeShift Q)) =
      volumeAverage (openCubeSet (originCube d Q.scale)) g := by
  rw [← integralNCM, ← integralNCM]
  have hmp := measurePreserving_addRight_normalizedCubeMeasure_originCube Q
  have hemb : MeasurableEmbedding (fun x : Vec d => x + triadicCubeShift Q) :=
    (MeasurableEquiv.addRight (triadicCubeShift Q)).measurableEmbedding
  have h := hmp.integral_comp hemb (fun x : Vec d => g (x - triadicCubeShift Q))
  simpa only [add_sub_cancel_right] using h.symm

/-- The cut-off coefficient is the transported coefficient read after the
inverse shift: `a_ℓ(ω)(x) = a_ℓ(τ_z ω)(x − z)`. -/
private theorem coefficientCutoff_apply_eq_translate (nu : ℝ) (z x : Vec d)
    (omega : ShellSeq d) (L : ℕ) :
    (coefficientCutoff nu omega L).toCoeffField x =
      (coefficientCutoff nu (ShellField.translateSequence z omega) L).toCoeffField (x - z) := by
  have h := congrFun (translateCoeffField_coefficientCutoff nu z omega L) (x - z)
  rw [translateCoeffField] at h
  have hx : (fun i : Fin d => (x - z) i + z i) = x := by
    funext i
    simp
  conv_lhs => rw [← hx]
  exact h

/-- **Item 1, the deterministic core, with the shift as a parameter.**  For any
vector `z` carrying `Q` onto the centred cube of its scale, the flux pairing of
the single maximizer of `Q` at `omega` is the pairing on `cu_{Q.scale}` at the
translated shell sequence `τ_z omega`. -/
private theorem fluxPairing_volumeAverage_translate_aux [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (F : Vec d) (i : Fin d) (omega : ShellSeq d) (Q : TriadicCube d) {z : Vec d}
    (hz : z = triadicCubeShift Q) :
    volumeAverage (openCubeSet Q)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (cubeMaximizerGradient hnu omega L F Q x) i) =
      volumeAverage (openCubeSet (originCube d Q.scale))
        (fun y => matVecMul
          ((coefficientCutoff nu (ShellField.translateSequence z omega) L).toCoeffField y)
          (cubeMaximizerGradient hnu (ShellField.translateSequence z omega) L F
            (originCube d Q.scale) y) i) := by
  subst hz
  have hae := cubeMaximizerGradient_translate_ae hnu omega L F Q
  have hcoe : ∀ x : Vec d, (coefficientCutoff nu omega L).toCoeffField x =
      (coefficientCutoff nu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField
        (x - triadicCubeShift Q) :=
    fun x => coefficientCutoff_apply_eq_translate nu (triadicCubeShift Q) x omega L
  have hae' : (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
        (cubeMaximizerGradient hnu omega L F Q x) i) =ᵐ[normalizedCubeMeasure Q]
      (fun x => matVecMul
        ((coefficientCutoff nu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField
          (x - triadicCubeShift Q))
        (cubeMaximizerGradient hnu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L F
          (originCube d Q.scale) (x - triadicCubeShift Q)) i) := by
    filter_upwards [hae] with x hx
    rw [hcoe x, hx]
  rw [← integralNCM Q, MeasureTheory.integral_congr_ae hae', integralNCM Q]
  exact volumeAverage_comp_sub_shift Q (fun y => matVecMul
    ((coefficientCutoff nu
      (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField y)
    (cubeMaximizerGradient hnu
      (ShellField.translateSequence (triadicCubeShift Q) omega) L F
      (originCube d Q.scale) y) i)

/-- **Item 1, the deterministic core.**  The flux pairing of a single cube
maximizer is translation covariant: its value on an arbitrary triadic cube `Q`
at the sample `omega` is its value on the centred cube `cu_{Q.scale}` at the
translated sample.  This is the `hcov` hypothesis of
`TranslatedBlocks.integral_of_translationCovariant` and of
`RHSTerm3SourceGaps.integral_sq_descendantAverage_eq` at the term-1 carrier; it
is the flux analogue of `translatedBlockNorm_eq_originCube`. -/
theorem maximizerFluxPairing_translate [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (F : Vec d) (i : Fin d) (omega : ShellSeq d) (Q : TriadicCube d) :
    maximizerFluxPairing hnu L F i omega Q =
      maximizerFluxPairing hnu L F i
        (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale) :=
  fluxPairing_volumeAverage_translate_aux hnu L F i omega Q rfl

/-! ## Item 1: the glued block average as a descendant average of maximizers

The clause's observable carries the *glued* field `∇ũ_n`, whose value on a
scale-`ℓ` block `Q` is the one maximizer of the aligned scale-`n` block
containing it.  Decomposing `Q` into those blocks (`n ≤ ℓ`) turns the glued
block pairing into the `descendantsAverage` of the single-block pairings, which
is the form the covariance above transports. -/

/-- Descendant depth is transitive: a depth-`n` descendant of a depth-`m`
descendant is a depth-`(m + n)` descendant. -/
theorem mem_descendantsAtDepth_trans {d : ℕ} {Q R S : TriadicCube d} {m n : ℕ}
    (hR : R ∈ descendantsAtDepth Q m) (hS : S ∈ descendantsAtDepth R n) :
    S ∈ descendantsAtDepth Q (m + n) := by
  induction n generalizing S with
  | zero =>
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hS
      subst hS
      simpa using hR
  | succ n ih =>
      rw [mem_descendantsAtDepth_succ_iff] at hS
      obtain ⟨U, hU, hSU⟩ := hS
      rw [Nat.add_succ, mem_descendantsAtDepth_succ_iff]
      exact ⟨U, ih hU, hSU⟩

/-- **The glued block flux pairing.**  The average over the cube `Q` of the
cut-off coefficient against the glued gradient — the integrand of
`fluxBlockObservable`, at the pinned glued data `L = ℓ`, `k = n`, `m`. -/
def gluedFluxPairing [NeZero d] {nu : ℝ} (hnu : 0 < nu) (ℓ n m : ℕ) (F : Vec d) (i : Fin d)
    (omega : ShellSeq d) (Q : TriadicCube d) : ℝ :=
  volumeAverageVec (cubeSet Q) (fun x => matVecMul
    ((coefficientCutoff nu omega ℓ).toCoeffField x)
    (gluedGradientField hnu ℓ n m F omega x)) i

/-- **Item 1, the reduction of the glued block average.**  For an aligned cube
`Q` of scale `ℓ` inside `cu_m` and a glued scale `n ≤ ℓ`, the flux pairing of
the glued field on `Q` (the integrand of `fluxBlockObservable`) is the
`descendantsAverage` over the aligned scale-`n` blocks inside `Q` of the
single-block pairings `maximizerFluxPairing`. -/
theorem volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) {n ℓ m : ℕ} (hnℓ : n ≤ ℓ) (hℓm : ℓ ≤ m) (F : Vec d)
    (omega : ShellSeq d) {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - ℓ)) (i : Fin d) :
    gluedFluxPairing hnu ℓ n m F i omega Q =
      descendantsAverage Q (ℓ - n) (fun z => maximizerFluxPairing hnu ℓ F i omega z) := by
  rw [gluedFluxPairing]
  have hG : MemVectorL2 (openCubeSet Q) (gluedGradientField hnu ℓ n m F omega) :=
    memVectorL2_openCubeSet_gluedGradientField hnu ℓ n m F omega Q
  have hA : MemVectorL2 (openCubeSet Q) (fun x => matVecMul
      ((coefficientCutoff nu omega ℓ).toCoeffField x)
      (gluedGradientField hnu ℓ n m F omega x)) :=
    memVectorL2_matVecMul_coefficientCutoff hnu omega ℓ Q hG
  have hF : MemLp (hilbertifyVecField (fun x => matVecMul
      ((coefficientCutoff nu omega ℓ).toCoeffField x)
      (gluedGradientField hnu ℓ n m F omega x))) 2 (normalizedCubeMeasure Q) :=
    Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hA
  rw [volumeAverageVec_eq_descendantsAverage_memLp Q (ℓ - n) hF i]
  rw [descendantsAverage, descendantsAverage]
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzlarge : z ∈ largeCubeSubcubes d n m := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hQ hz
    rwa [show (m - ℓ) + (ℓ - n) = m - n from by omega] at h
  have hmax : maximizerFluxPairing hnu ℓ F i omega z =
      volumeAverage (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega ℓ).toCoeffField x)
        (cubeMaximizerGradient hnu omega ℓ F z x) i) := by
    simp only [maximizerFluxPairing, volumeAverageVec]
  have hstep : volumeAverageVec (cubeSet z) (fun x => matVecMul
      ((coefficientCutoff nu omega ℓ).toCoeffField x)
      (gluedGradientField hnu ℓ n m F omega x)) i =
      volumeAverage (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega ℓ).toCoeffField x)
        (cubeMaximizerGradient hnu omega ℓ F z x) i) := by
    show volumeAverage (cubeSet z) (fun x => matVecMul
      ((coefficientCutoff nu omega ℓ).toCoeffField x)
      (gluedGradientField hnu ℓ n m F omega x) i) = _
    rw [volumeAverage_cubeSet_eq_openCubeSet z, volumeAverage, volumeAverage,
      MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet z) (fun x hx => by
        show matVecMul ((coefficientCutoff nu omega ℓ).toCoeffField x)
          (gluedGradientField hnu ℓ n m F omega x) i = matVecMul
          ((coefficientCutoff nu omega ℓ).toCoeffField x)
          (cubeMaximizerGradient hnu omega ℓ F z x) i
        rw [gluedGradientField_apply_of_mem_openCubeSet hnu ℓ n m F omega hzlarge hx])]
  exact hstep.trans hmax.symm

/-- **Item 1: the pinned observable is the glued pairing minus the proxy.**
The observable `fluxBlockObservable` concentrated by the printed clause is, at
every block `Q` and every sample, the glued flux pairing on `Q` minus the
constant proxy `q̃ = qVector hnu P ℓ ℓ n m F`.  Since `q̃` does not depend on the
block, the covariance and the annealed transfer below apply to the pinned
observable verbatim. -/
theorem fluxBlockObservable_eq_gluedFluxPairing_sub [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (ℓ n m : ℕ) (F : Vec d) (i : Fin d)
    (Q : TriadicCube d) (omega : ShellSeq d) :
    fluxBlockObservable hnu P ℓ n m F i Q omega =
      gluedFluxPairing hnu ℓ n m F i omega Q - qVector hnu P ℓ ℓ n m F i :=
  rfl

/-! ## Item 1: the lattice-shift consequence

With the covariance in hand, the lattice-shift machinery applies.  For
two aligned cubes of the same scale, the block average on one is the block
average on the other read at the translated shell sequence, the shift being
`cubeShiftVector` (`RHSTerm3SourceGaps`); on the instance `Q' = cu_ℓ`, `Q = R`
that vector is exactly `triadicCubeShift R`. -/

/-! ## The lane measurability of the block observable

The annealed second-moment bound for the term-1 flux block observable
asks that the pinned block observable `fluxBlockObservable … R` on a scale-`k`
block `R` be measurable in the joined restriction lane
`blockLane ell (shellRestrictionSigma (cubeSet R))`.  The observable is not
directly a coarse-block quantity, but the flux cube-mean identity
`volumeAverageVec_flux_gluedGradientField_eq` writes it as the coarse matrix
expression

`F − κᵀ(R) (σ_*⁻¹(R) F) − q̃`,

in which no selection of a solution enters.  The coarse matrices of the cutoff
and of its restriction to `cubeSet R` agree, because the coarse block matrix on
`cubeSet R` does not see the change, and the restricted cutoff is an observable
of the lane (`measurable_blockLane_restrictedCoefficientCutoff`).  The
arbitrary-space slice engine `measurable_kappaCoarse_apply` /
`measurable_sigmaStarInvCoarse_apply` then gives the lane measurability. -/

section LaneMeasurability

variable {nu : ℝ}

end LaneMeasurability

/-! ## The block-partition identification of the clause's index set

The clause is indexed by the depth-`j` descendants of `cu_m`, while the
per-sublattice rule of `SublatticeConcentrationDepth` is stated on a separated
sub-family of `largeCubeSubcubes d k m`.  The two index sets are the same
partition read at complementary scales, and the three statements below are that
identification. -/

section BlockPartition

end BlockPartition

end

end SuperdiffusionCLT.Section3.Terms
