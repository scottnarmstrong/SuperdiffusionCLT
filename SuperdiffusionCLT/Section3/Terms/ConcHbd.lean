/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.ConcLaneBundle
public import SuperdiffusionCLT.Section3.Terms.SublatticeConcentrationDepth
public import SuperdiffusionCLT.Section3.Terms.ConcXIntegrated
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Close
public import SuperdiffusionCLT.Section2.Estimates.Stream.CoefficientLinftyMoments
public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# Term 1's amplitude slot: the printed envelope

The printed hypothesis of the concentration step is the *envelope* `X_z = O_{Γ_σ}(1)`
together with `E[X_z] = 0` — a sample-dependent, a.s.-finite, `Γ`-measurable
carrier with a finite second moment.  This module makes that envelope explicit and discharges
the amplitude slot of the depth clause from it.

## What the chain consumes

The amplitude enters only through the `L²`-membership `hmem` of the comparison,
by `MeasureTheory.MemLp.mono'`.  What that step needs is a *dominating `L²`
function*, not a sample-uniform constant: the printed envelope.  The amplitude slot is
therefore carried here as

* `HbdConcOn hnu P S e C` — a bound by a sample-dependent envelope `C`,
  on the printed range `j + ℓ ≤ m` (the range in which the blocks of
  `subcollectionAtDepth R (m - j - ℓ) c` are the scale-`ℓ` blocks of the printed
  rule);
* together with the printed second moment `MemLp C 2 P.toMeasure`.

## Main results

* `concBlockEnvelope` — the printed envelope made explicit:
  `‖a_ℓ‖_{L^∞(cu_m)}(ω) · ν⁻¹ |F| + ‖q̃‖`, the per-variable envelope
  `abs_fluxBlockAverageVec_entry_le_family` plus the constant proxy;
* `concEnvelopeAmplitude` — the named `Γ₂` amplitude of the carrier at the
  envelope's own scales, `coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d)
  d ℓ m`, and `abs_moment_coeffLinftySupBound_le`: the explicit second moment
  `E[‖a_ℓ‖²_{L^∞(cu_m)}] ≤ A² (1 + Γ(2))` at that named amplitude;
* `abs_volumeAverage_concDepthField_le_envelope` — the pointwise bound, at every
  printed depth, class, coordinate and block.  The route is the valuation of the
  glued block pairing as the `descendantsAverage` of the single aligned
  scale-`n` maximizer pairings
  (`volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer`), each of
  which carries the per-variable envelope; no energy hypothesis on the scale-`ℓ`
  block itself is needed, so no residual remains;
* `memLp_concBlockEnvelope` and `concEnvelopeMemLp_envelope_holds` — the printed
  second moment of the envelope, from the `Γ₂` tail of `coeffLinftySupBound`
  (`isBigO_gammaSigma_coeffLinftySupBound`);
* `hbdConcOn_envelope_holds` — `HbdConcOn` at that envelope, **no hypotheses**;
* `memLp_volumeAverage_coord_of_envelope`,
  `memLp_volumeAverage_coord_of_subcollectionAtDepth_envelope` and
  `hpair_and_hmem_of_subcollectionAtDepth_envelope` — the chain's `hmem` step
  consumed with a dominating `L²` function rather than a constant
  (`MemLp.mono'`);
* `hpair_and_hmem_concDepthField_of_envelope`, `hconc_concDepthField_of_envelope`
  and `concDepthClause_of_envelope` — the wiring from the envelope
  `{C, hC, hon}` to the depth clause;
* `concDepthClause_of_shellLaws` — `ConcDepthClause d nu hnu S P e
  (concDepthConstant d)` from the shell laws alone.  The amplitude slot is
  discharged, and term 1 carries no residual beyond those laws;
* `term1_close_of_shellLaws` — the `l.RHS.term1` conclusion
  (`RHSTerm1Close.term1_close`) with the concentration binder `_hConcDepth`
  **removed**: it is the clause above, at the chain's own constant.  Term 1
  therefore carries, beyond the standing data, only the localization clause
  `_hLocMin` at `Cloc` and the pigeonhole side condition `_hPigeon`.
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
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.HighContrast
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The printed envelope of the block observable -/

/-- **The printed envelope of the coordinate block averages of the depth
observable.**  The per-variable envelope
`abs_fluxBlockAverageVec_entry_le_family` bounds the flux `a_ℓ ∇ũ_n` on every
aligned scale-`n` block by `‖a_ℓ‖_{L^∞(cu_m)}(ω) · ν⁻¹ |F|`; the observable is
that flux minus the constant proxy `q̃`, so the printed `O_{Γ_σ}(1)` carrier of
the block averages is `‖a_ℓ‖_{L^∞(cu_m)}(ω) · ν⁻¹ |F| + |q̃|`.  It is
sample-dependent: the carrier `coeffLinftySupBound` of `Frozen/Assumptions` has
no sup bound. -/
def concBlockEnvelope [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d) (omega : ShellSeq d) : ℝ :=
  coeffLinftySupBound nu S.ell S.m omega * nu⁻¹ *
      Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)) +
    vecNorm (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))

/-! ## The single-block envelope, from the maximizer pairing -/

/-- **The per-variable envelope of the single-block maximizer pairing.**  On an
aligned scale-`n` block `z`, the glued field is the maximizer of `z`
(`gluedGradientField_apply_of_mem_openCubeSet`), so the single-block flux pairing
`maximizerFluxPairing` is the flux average to which
`abs_fluxBlockAverageVec_entry_le_family` applies. -/
theorem abs_maximizerFluxPairing_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    {L k m : ℕ} (hkm : k ≤ m) {F : Vec d} (i : Fin d) {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) :
    |maximizerFluxPairing hnu L F i omega z| ≤
      coeffLinftySupBound nu L m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by
  have hstep : volumeAverageVec (cubeSet z) (fun x => matVecMul
      ((coefficientCutoff nu omega L).toCoeffField x)
      (gluedGradientField hnu L k m F omega x)) i =
      volumeAverage (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega L).toCoeffField x)
        (cubeMaximizerGradient hnu omega L F z x) i) := by
    show volumeAverage (cubeSet z) (fun x => matVecMul
      ((coefficientCutoff nu omega L).toCoeffField x)
      (gluedGradientField hnu L k m F omega x) i) = _
    rw [volumeAverage_cubeSet_eq_openCubeSet z, volumeAverage, volumeAverage,
      MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet z) (fun x hx => by
        show matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x) i = matVecMul
          ((coefficientCutoff nu omega L).toCoeffField x)
          (cubeMaximizerGradient hnu omega L F z x) i
        rw [gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hz hx])]
  have hmax : maximizerFluxPairing hnu L F i omega z =
      volumeAverage (openCubeSet z) (fun x => matVecMul
        ((coefficientCutoff nu omega L).toCoeffField x)
        (cubeMaximizerGradient hnu omega L F z x) i) := rfl
  rw [hmax, ← hstep]
  exact abs_fluxBlockAverageVec_entry_le_family hnu omega hkm (F := F) i hz

/-- **The per-variable envelope of the glued block pairing.**  On an aligned
scale-`ℓ` block `Q` of `cu_m` with glued scale `n ≤ ℓ`, the glued block pairing
is the `descendantsAverage` of the single aligned scale-`n` maximizer pairings
(`volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer`); each
carries `abs_maximizerFluxPairing_le`, and an average of terms bounded by `c` is
bounded by `c`. -/
theorem abs_gluedFluxPairing_le_of_mem_largeCubeSubcubes [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {ℓ n m : ℕ} (hnℓ : n ≤ ℓ) (hℓm : ℓ ≤ m) (F : Vec d)
    (i : Fin d) (omega : ShellSeq d) {Q : TriadicCube d}
    (hQ : Q ∈ largeCubeSubcubes d ℓ m) :
    |gluedFluxPairing hnu ℓ n m F i omega Q| ≤
      coeffLinftySupBound nu ℓ m omega * nu⁻¹ * Real.sqrt (vecNormSq F) := by
  have hQdesc : Q ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - ℓ) := by
    rwa [largeCubeSubcubes_eq_descendantsAtDepth] at hQ
  have hnm : n ≤ m := le_trans hnℓ hℓm
  rw [volumeAverageVec_fluxPairing_glued_eq_descendantsAverage_maximizer hnu hnℓ hℓm F omega
      hQdesc i]
  refine le_trans
    (SuperdiffusionCLT.Section2.Estimates.Stream.abs_descendantsAverage_le Q (ℓ - n) _) ?_
  refine le_trans (Homogenization.descendantsAverage_le_descendantsAverage Q (ℓ - n)
    (fun z hz => ?_)) (le_of_eq (Homogenization.descendantsAverage_const Q (ℓ - n) _))
  have hzlarge : z ∈ largeCubeSubcubes d n m := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hQdesc hz
    rwa [show (m - ℓ) + (ℓ - n) = m - n from by omega] at h
  exact abs_maximizerFluxPairing_le hnu omega hnm (F := F) i hzlarge

/-- **The printed pointwise envelope of the coordinate block average of the
depth observable**, at every printed depth and block.  The block average is the
glued block pairing minus the constant proxy
(`volumeAverage_coord_concDepthField_eq_fluxBlockObservable`,
`fluxBlockObservable_eq_gluedFluxPairing_sub`); the pairing carries
`abs_gluedFluxPairing_le_of_mem_largeCubeSubcubes` and the proxy contributes the
constant `|q̃_i| ≤ ‖q̃‖`.  No residual hypothesis. -/
theorem abs_volumeAverage_concDepthField_le_envelope [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (hjell : j + S.ell ≤ S.m)
    {c : ShellField.ShellCubeColor d} (_hc : c ∈ shellColorSet R (S.m - j - S.ell))
    (i : Fin d) {B : TriadicCube d} (hB : B ∈ subcollectionAtDepth R (S.m - j - S.ell) c)
    (omega : ShellSeq d) :
    |volumeAverage (cubeSet B) (fun x => concDepthField hnu P S e omega x i)| ≤
      concBlockEnvelope hnu P S e omega := by
  have hBdesc : B ∈ descendantsAtDepth R (S.m - j - S.ell) := (mem_subcollectionAtDepth.mp hB).1
  have hBmem : B ∈ largeCubeSubcubes d S.ell S.m := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth]
    have h := mem_descendantsAtDepth_trans hR hBdesc
    rwa [show j + (S.m - j - S.ell) = S.m - S.ell from by omega] at h
  have hnℓ : S.n ≤ S.ell := by have := S.n_add_a; omega
  have hℓm : S.ell ≤ S.m := by have := S.ell_add_a; have := S.ellPrime_add_h; omega
  have hflux : |gluedFluxPairing hnu S.ell S.n S.m
      (fluxSlot nu S.LPrime P S.n e) i omega B| ≤
      coeffLinftySupBound nu S.ell S.m omega * nu⁻¹ *
        Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)) :=
    abs_gluedFluxPairing_le_of_mem_largeCubeSubcubes hnu hnℓ hℓm _ i omega hBmem
  have hcarrier : volumeAverage (cubeSet B)
      (fun x => concDepthField hnu P S e omega x i) =
      gluedFluxPairing hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i omega B -
        qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i :=
    (volumeAverage_coord_concDepthField_eq_fluxBlockObservable hnu P S e omega i B).trans
      (fluxBlockObservable_eq_gluedFluxPairing_sub hnu P S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e) i B omega)
  rw [hcarrier, concBlockEnvelope]
  have h1 : |gluedFluxPairing hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i omega B -
        qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i| ≤
      |gluedFluxPairing hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i omega B| +
        |qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (gluedFluxPairing hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i omega B)
        (-(qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i))
  have h2 : |qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) i| ≤
      vecNorm (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) :=
    abs_apply_le_vecNorm _ i
  exact le_trans h1 (add_le_add hflux h2)

/-! ## The named amplitude of the envelope, and its printed second moment -/

/-- **The `Γ₂` amplitude of the carrier at the envelope's own scales**, named
explicitly: the `coeffLinftyGammaTwoAmplitude` at `C = largeCubeLinftyConst
d`, `L = ℓ`, `m = m`.  It is `ν + γ₂ (‖k₀‖-amplitude + C₀ √ℓ √m)` with
`γ₂ = gammaTriangleConst 2`. -/
def concEnvelopeAmplitude (nu : ℝ) (d ell m : ℕ) : ℝ :=
  coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d ell m

/-- **The named amplitude is positive.**  It is `ν > 0` plus a nonnegative
`γ₂`-multiple, so it is positive at every `ℓ ≤ m`; no moment hypothesis is
needed for positivity. -/
theorem concEnvelopeAmplitude_pos (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) {nu : ℝ} (hnu : 0 < nu) (ell m : ℕ) :
    0 < concEnvelopeAmplitude nu d ell m := by
  rw [concEnvelopeAmplitude, coeffLinftyGammaTwoAmplitude, streamCutoffLinftyGammaTwoAmplitude]
  refine add_pos_of_nonneg_of_pos (le_of_lt hnu)
    (mul_pos gammaTriangleConst_pos ?_)
  exact add_pos_of_pos_of_nonneg
    (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_shellValueLargeCubeConst d))
      (Real.sqrt_pos.2 (by
        have hmc : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le m
        linarith only [hmc])))
    (mul_nonneg (largeCubeLinftyConst_pos hPrefix).le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- **The carrier `coeffLinftySupBound nu L m` is square-integrable.**  Its `Γ₂`
tail (`isBigO_gammaSigma_coeffLinftySupBound`) makes every polynomial
moment finite (`integrable_abs_rpow_of_isBigO_gammaSigma_two`), in particular the
second. -/
theorem memLp_coeffLinftySupBound (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {nu : ℝ} (hnu : 0 < nu) {L m : ℕ} (hLm : L ≤ m) :
    MemLp (fun omega : ShellSeq d => coeffLinftySupBound nu L m omega) 2 P.toMeasure := by
  have hXm : Measurable (fun omega : ShellSeq d => coeffLinftySupBound nu L m omega) :=
    measurable_coeffLinftySupBound nu L m
  have hint : Integrable (fun omega : ShellSeq d => |coeffLinftySupBound nu L m omega| ^ (2 : ℝ))
      P.toMeasure := by
    have hX : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => coeffLinftySupBound nu L m omega)
        (concEnvelopeAmplitude nu d L m) := by
      rw [concEnvelopeAmplitude]
      exact isBigO_gammaSigma_coeffLinftySupBound hPrefix hJ2 hJ3 hJ4 hnu.le hLm
    exact Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      (concEnvelopeAmplitude_pos P hPrefix hnu L m) hXm.aemeasurable hX 2
  rw [memLp_two_iff_integrable_sq hXm.aestronglyMeasurable]
  refine hint.congr (Filter.Eventually.of_forall fun omega => ?_)
  show |coeffLinftySupBound nu L m omega| ^ (2 : ℝ) = coeffLinftySupBound nu L m omega ^ 2
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]

/-- **The printed second moment of the envelope.**  The envelope is the carrier
times the constant `ν⁻¹ |F|` plus the constant `‖q̃‖`, so its `L²`-membership is
that of the carrier. -/
theorem memLp_concBlockEnvelope [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) :
    MemLp (concBlockEnvelope hnu P S e) 2 P.toMeasure := by
  have hℓm : S.ell ≤ S.m := by have := S.ell_add_a; have := S.ellPrime_add_h; omega
  have hX := memLp_coeffLinftySupBound P hPrefix hJ2 hJ3 hJ4 hnu hℓm
  have h1 : MemLp (fun omega : ShellSeq d => coeffLinftySupBound nu S.ell S.m omega * nu⁻¹ *
      Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e))) 2 P.toMeasure :=
    (hX.mul_const nu⁻¹).mul_const _
  have h2 : MemLp (fun _ : ShellSeq d => vecNorm
      (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))) 2 P.toMeasure :=
    MeasureTheory.memLp_const _
  have h3 := h1.add h2
  unfold concBlockEnvelope
  exact h3

/-! ## The amplitude slot

The printed hypothesis is the envelope.  The slot below carries the envelope itself,
on the printed range `j + ℓ ≤ m`. -/

/-- **The amplitude slot narrowed to a sample-dependent envelope** `C`: the
sample-by-sample bound on the block averages by `C`, on the printed
range `j + ℓ ≤ m`. -/
def HbdConcOn [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d) (C : ShellSeq d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j, j + S.ell ≤ S.m →
    ∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
    ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c, ∀ omega : ShellSeq d,
      |volumeAverage (cubeSet B) (fun x => concDepthField hnu P S e omega x i)| ≤ C omega

/-- **The printed second moment of the envelope.**  The chain's `hmem` step
consumes the envelope through its `L²`-membership, which is what this records. -/
def ConcEnvelopeMemLp (P : ProbabilityMeasure (ShellSeq d)) (C : ShellSeq d → ℝ) : Prop :=
  MemLp C 2 P.toMeasure

/-- **The narrowed amplitude slot holds, with no hypotheses**, at the printed
envelope: the pointwise bound `abs_volumeAverage_concDepthField_le_envelope` at
every printed depth, class, coordinate and block. -/
theorem hbdConcOn_envelope_holds [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d) :
    HbdConcOn hnu P S e (concBlockEnvelope hnu P S e) :=
  fun _ _ hR hjell _ hc i _B hB omega =>
    abs_volumeAverage_concDepthField_le_envelope hnu P S e hR hjell hc i hB omega

/-- **The printed second moment of the envelope holds**, from the shell
laws: the `Γ₂` tail of the carrier plus the constant proxy. -/
theorem concEnvelopeMemLp_envelope_holds [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) :
    ConcEnvelopeMemLp P (concBlockEnvelope hnu P S e) :=
  memLp_concBlockEnvelope hnu P S e hPrefix hJ2 hJ3 hJ4

/-! ## The chain consumed with the envelope: `hmem` from a dominating `L²` function -/

/-- **`hmem` from a dominating `L²` envelope.**  A *constant*
bound with `MemLp.of_bound` is not what the chain needs; it needs a
dominating `L²` function, and `MemLp.mono'` supplies it. -/
theorem memLp_volumeAverage_coord_of_envelope
    (P : ProbabilityMeasure (ShellSeq d)) {ell : ℕ} {blocks : Finset (TriadicCube d)}
    {F : ShellSeq d → Vec d → Vec d} (i : Fin d)
    (hlane : ∀ B ∈ blocks, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i)))
    (C : ShellSeq d → ℝ) (hC : MemLp C 2 P.toMeasure)
    (hbd : ∀ B ∈ blocks, ∀ omega : ShellSeq d,
      |volumeAverage (cubeSet B) (fun x => F omega x i)| ≤ C omega) :
    ∀ B ∈ blocks, MeasureTheory.MemLp
      (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i)) 2 P.toMeasure := by
  intro B hB
  refine hC.mono'
    ((hlane B hB).mono
      (SuperdiffusionCLT.Section3.HighContrast.blockLane_le
        (ShellField.shellRestrictionSigma_le (cubeSet B) (measurableSet_cubeSet B)))
      le_rfl).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun omega => by
    simpa only [Real.norm_eq_abs] using hbd B hB omega

/-- **`hmem` at one printed subcollection, from a dominating `L²` envelope.** -/
theorem memLp_volumeAverage_coord_of_subcollectionAtDepth_envelope
    (P : ProbabilityMeasure (ShellSeq d)) {R : TriadicCube d} {t ell : ℕ}
    {c : ShellField.ShellCubeColor d} {F : ShellSeq d → Vec d → Vec d} (i : Fin d)
    (hlane : ∀ B ∈ subcollectionAtDepth R t c, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i)))
    (C : ShellSeq d → ℝ) (hC : MemLp C 2 P.toMeasure)
    (hbd : ∀ B ∈ subcollectionAtDepth R t c, ∀ omega : ShellSeq d,
      |volumeAverage (cubeSet B) (fun x => F omega x i)| ≤ C omega) :
    ∀ B ∈ subcollectionAtDepth R t c, MeasureTheory.MemLp
      (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i)) 2 P.toMeasure :=
  memLp_volumeAverage_coord_of_envelope P (blocks := subcollectionAtDepth R t c) i hlane C hC hbd

/-- **`hpair` and `hmem` together at one printed subcollection, from the
envelope.**  The amplitude is the printed envelope and its second moment. -/
theorem hpair_and_hmem_of_subcollectionAtDepth_envelope [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {R : TriadicCube d} {t ell : ℕ} {c : ShellField.ShellCubeColor d}
    (hscaleR : R.scale - (t : ℤ) = (ell : ℤ))
    {F : ShellSeq d → Vec d → Vec d}
    (hlane : ∀ i : Fin d, ∀ B ∈ subcollectionAtDepth R t c, @Measurable (ShellSeq d) ℝ
      (SuperdiffusionCLT.Section3.HighContrast.blockLane ell
        (ShellField.shellRestrictionSigma (cubeSet B) (measurableSet_cubeSet B)))
      inferInstance (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i)))
    (C : ShellSeq d → ℝ) (hC : MemLp C 2 P.toMeasure)
    (hbd : ∀ i : Fin d, ∀ B ∈ subcollectionAtDepth R t c, ∀ omega : ShellSeq d,
      |volumeAverage (cubeSet B) (fun x => F omega x i)| ≤ C omega) :
    (∀ i : Fin d, ∀ B ∈ subcollectionAtDepth R t c, ∀ B' ∈ subcollectionAtDepth R t c,
        B ≠ B' → ProbabilityTheory.IndepFun
          (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i))
          (fun omega => volumeAverage (cubeSet B') (fun x => F omega x i)) P.toMeasure) ∧
      (∀ i : Fin d, ∀ B ∈ subcollectionAtDepth R t c, MeasureTheory.MemLp
        (fun omega => volumeAverage (cubeSet B) (fun x => F omega x i)) 2 P.toMeasure) :=
  ⟨fun i => indepFun_volumeAverage_coord_of_subcollectionAtDepth
      P hJ1 hJ2 hscaleR i (hlane i),
    fun i => memLp_volumeAverage_coord_of_subcollectionAtDepth_envelope P i (hlane i) C hC (hbd i)⟩

/-! ## The depth clause from the shell laws alone -/

/-- **`hpair` and `hmem` at the observable field, from the envelope.**  The amplitude slot
is the envelope `{C, hC, hon}`. -/
theorem hpair_and_hmem_concDepthField_of_envelope [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (e : Vec d)
    (hlaneOn : HlaneConcOn hnu P S e) (C : ShellSeq d → ℝ) (hC : MemLp C 2 P.toMeasure)
    (hon : HbdConcOn hnu P S e C)
    {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (hpos : 0 < S.m - j - S.ell) :
    (∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
        ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c,
        ∀ B' ∈ subcollectionAtDepth R (S.m - j - S.ell) c, B ≠ B' →
        ProbabilityTheory.IndepFun
          (fun omega : ShellSeq d => volumeAverage (cubeSet B)
            (fun x => concDepthField hnu P S e omega x i))
          (fun omega : ShellSeq d => volumeAverage (cubeSet B')
            (fun x => concDepthField hnu P S e omega x i)) P.toMeasure) ∧
      (∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
        ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c,
        MeasureTheory.MemLp (fun omega : ShellSeq d => volumeAverage (cubeSet B)
          (fun x => concDepthField hnu P S e omega x i)) 2 P.toMeasure) := by
  have hjm : j ≤ S.m := by omega
  have hjell : j + S.ell ≤ S.m := by omega
  have hscaleR : R.scale - ((S.m - j - S.ell : ℕ) : ℤ) = (S.ell : ℤ) := by
    have hRs : R.scale = (S.m : ℤ) - (j : ℤ) := by
      have h := scale_eq_sub_of_mem_descendantsAtDepth hR
      exact h
    have hcast : ((S.m - j - S.ell : ℕ) : ℤ) = (S.m : ℤ) - (j : ℤ) - (S.ell : ℤ) := by
      rw [Nat.cast_sub (m := S.ell) (n := S.m - j) (by omega),
        Nat.cast_sub (m := j) (n := S.m) hjm]
    rw [hRs, hcast]
    ring
  constructor
  · intro c hc i B hB B' hB' hne
    exact (hpair_and_hmem_of_subcollectionAtDepth_envelope (R := R) (t := S.m - j - S.ell)
      (ell := S.ell) (c := c) P hJ1 hJ2 hscaleR (hlaneOn j R hR hjell c hc) C hC
      (fun i B hB omega => hon j R hR hjell c hc i B hB omega)).1 i B hB B' hB' hne
  · intro c hc i B hB
    exact (hpair_and_hmem_of_subcollectionAtDepth_envelope (R := R) (t := S.m - j - S.ell)
      (ell := S.ell) (c := c) P hJ1 hJ2 hscaleR (hlaneOn j R hR hjell c hc) C hC
      (fun i B hB omega => hon j R hR hjell c hc i B hB omega)).2 i B hB

/-- **The per-cube concentration at the observable field from the envelope
alone.**  The amplitude slot is the envelope.  Residuals carried: `P, hJ1, hJ2, hnu, S, e,
hPrefix, hJ3, hJ4, hlaneOn, C, hC, hon`. -/
theorem hconc_concDepthField_of_envelope [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (hlaneOn : HlaneConcOn hnu P S e) (C : ShellSeq d → ℝ) (hC : MemLp C 2 P.toMeasure)
    (hon : HbdConcOn hnu P S e C) :
    ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      (∫⁻ omega, ENNReal.ofReal
          (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField hnu P S e omega)))
          ∂P.toMeasure) ≤
        ENNReal.ofReal (concDepthConstant d *
            (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega, ENNReal.ofReal
            (vecSqAvg R (concDepthField hnu P S e omega)) ∂P.toMeasure) := by
  intro j R hR
  by_cases hcase : 0 < S.m - j - S.ell
  · have hjm : j ≤ S.m := by omega
    have hnj : S.n ≤ S.m - j := by
      have hnl : S.n ≤ S.ell := Nat.le.intro S.n_add_a
      omega
    obtain ⟨hpair, hmem⟩ :=
      hpair_and_hmem_concDepthField_of_envelope P hJ1 hJ2 hnu S e hlaneOn C hC hon hR hcase
    refine le_trans (lintegral_concDepthField_le_decay_subcollections_of_xIntegrated hnu P S e
      hPrefix hJ2 hJ3 hJ4 hjm hR hnj hpair hmem) ?_
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (printedSubcollectionCount d : ℝ)),
      ENNReal.ofReal_mul (le_trans zero_le_one (one_le_concDepthConstant d))]
    exact mul_le_mul'
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (printedSubcollectionCount_le_concDepthConstant d))
        le_rfl) le_rfl
  · exact hconc_concDepthField_truncated hnu P S e (one_le_concDepthConstant d) j
      (by omega) R hR

/-- **`_hConcDepth` from the envelope.** -/
theorem concDepthClause_of_envelope [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (hlaneOn : HlaneConcOn hnu P S e) (C : ShellSeq d → ℝ)
    (hC : ConcEnvelopeMemLp P C) (hon : HbdConcOn hnu P S e C) :
    ConcDepthClause d nu hnu S P e (concDepthConstant d) :=
  concDepthClause_of_hconc hnu S P e
    (hconc_concDepthField_of_envelope P hJ1 hJ2 hnu S e hPrefix hJ3 hJ4 hlaneOn C hC hon)

/-- **`_hConcDepth` from the shell laws alone.  The amplitude slot
is discharged.**  No sample-uniform bound remains: the lane slot is
`hlaneConcOn_holds`, the envelope is `concBlockEnvelope`, its second moment is
`concEnvelopeMemLp_envelope_holds`, and the envelope bound is
`hbdConcOn_envelope_holds`.  The clause's constant is
`concDepthConstant d = max 1 (printedSubcollectionCount d)`. -/
theorem concDepthClause_of_shellLaws [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d)) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    ConcDepthClause d nu hnu S P e (concDepthConstant d) :=
  concDepthClause_of_envelope P hJ1 hJ2 hnu S e hPrefix hJ3 hJ4
    (hlaneConcOn_holds hnu P S e) (concBlockEnvelope hnu P S e)
    (concEnvelopeMemLp_envelope_holds hnu P S e hPrefix hJ2 hJ3 hJ4)
    (hbdConcOn_envelope_holds hnu P S e)

/-! ## Term 1 with the localization clause as its only obligation -/

/-- **The `l.RHS.term1` conclusion with the concentration binder gone.**
This is `RHSTerm1Close.term1_close` with `_hConcDepth` removed from the binders:
it is supplied at `Cc = concDepthConstant d` by `concDepthClause_of_shellLaws`,
from the shell laws alone.  Every surviving binder is a standing assumption or the
localization clause `_hLocMin`; the pigeonhole side condition `_hPigeon` and the
two section constants `Cloc` (localization) and `concDepthConstant d` remain. -/
theorem term1_close_of_shellLaws (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cloc : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hLocMin : ∀ U : Book.Ch02.Domain d,
            (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
            ∀ (omega' : ShellSeq d) (p q : Vec d)
              (u : AHarmonicFunction
                (fun x : Vec d =>
                  (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                    volumeAverageMat (U : Set (Vec d))
                      (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                (U : Set (Vec d)))
              (v : AHarmonicFunction
                (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
              (∀ w : AHarmonicFunction
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                  (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q u)) →
              (∀ w : AHarmonicFunction
                  (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
                volumeAverage (U : Set (Vec d))
                    (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
                  Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                      anchorDerivSup S.ell S.LPrime S.n omega' *
                    (ResponseJ (U : Set (Vec d)) p q
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                      ResponseJ (U : Set (Vec d)) p q
                        (coefficientCutoff nu omega' S.ell).toCoeffField +
                      2 * vecDot p q))
        (_hPigeon : 2 * S.h ≤ S.m),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                  qVector hnu P S.LPrime S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  obtain ⟨C, hC1, hmain⟩ := term1_close d hd Cloc (concDepthConstant d)
  exact ⟨C, hC1, fun nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw hLocMin
      hPigeon =>
    hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw hLocMin
      (concDepthClause_of_shellLaws P hJ1V2 hJ2 hnu S e hPrefix hJ3 hJ4) hPigeon⟩

end

end SuperdiffusionCLT.Section3.Terms
