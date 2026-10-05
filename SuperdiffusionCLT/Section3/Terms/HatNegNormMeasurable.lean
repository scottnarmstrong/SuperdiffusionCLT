/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Final
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC

/-!
# Measurability of the order-one hatted negative norm

`SuperdiffusionCLT.Section3.Terms.term1_final` carries the obligation
`_hMeasHminus`: the `ω`-measurability of

`ω ↦ ‖a_ℓ ∇ũ_n − q̃‖_{Ĥ̲^{-1}(cu_m)}`,

whose carrier is `Section2.Norms.vecHatNegENormOrderOne`, an **uncountable** supremum
over the order-one test class (`IsVecHatTestFieldOrderOne`):

`vecHatNegENormOrderOne Q F = ⨆ g, ⨆ _ : IsVecHatTestFieldOrderOne Q g,
  ofReal (⨍_Q F·∇g)`.

No earlier result reaches that supremum directly, because a supremum over an
uncountable index of measurable functions need not be measurable.  This module
discharges the obligation by a route that needs **no** countability or density of
the test class at all.

## The route

Every test field of the class has a finite `L̲²(Q)` gradient, so
`∇g ∈ L²(openCubeSet Q)` and the potential class
`c_g := [∇g] ∈ HilbertVectorL2 (openCubeSet Q)` is well defined
(`memVectorL2_euclideanGradient_of_testField`).  The pairing is a value identity
in that class (`volumeAverage_vecDot_eq_inv_mul_inner`):

`⍍_Q (F·∇g) = (cubeVolume Q)⁻¹ ⟪[F], c_g⟫`.

Consequently the functional `Φ v := vecHatNegENormOrderOne Q (hilbertClassField v)` is
one-sided Lipschitz in the `L²` class norm,

`Φ v ≤ Φ w + (cubeVolume Q)^{-1/2} ‖v − w‖`   (`vecHatNegENormOrderOne_le_add_classDist`),

because for each test field `g` the real triangle inequality for the inner
product splits `⟪v, c_g⟫` into `⟪w, c_g⟫` and `⟪v − w, c_g⟫`, and the second
term is bounded by Cauchy–Schwarz and the test-class constraint.  This is a
**value** identity, so it needs no splitting of a Bochner integral and hence no
integrability hypothesis: in particular it does not depend on the total-integral
convention under which the hatted norm itself is only subadditive on `L²` fields.

Swapping `v` and `w` gives the two-sided bound, so `Φ` is Lipschitz, hence
measurable, and composing with an almost-everywhere measurable class map gives
the obligation.  The countability of the test class — real, and available from
`Lp.SecondCountableTopology` since the class space is second countable — is not
needed: the Lipschitz bound above is uniform over the whole uncountable test
class, which is the sense in which the supremum may be replaced by a countable
dense subfamily.

## Main results

* `memVectorL2_euclideanGradient_of_testField`: the gradient of a test field is
  an `L²` field of the open cube.
* `volumeAverage_vecDot_eq_inv_mul_inner`: the pairing, read in the class.
* `vecHatNegENormOrderOne_congr_ae`: the carrier only sees the `L²` class.
* `vecHatNegENormOrderOne_le_add_classDist`, `vecHatNegENormOrderOne_classDist_le_add`: the
  two one-sided Lipschitz bounds.
* `measurable_vecHatNegENormOrderOne_hilbertClassField`: the functional is measurable.
* `aemeasurable_vecHatNegENormOrderOne_of_classMeasurable`: the class-level obligation.
* `aemeasurable_vecHatNegENormOrderOne_pairingField`,
  `aemeasurable_vecHatNegENormOrderOne_term1Hminus`: the obligation `_hMeasHminus`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Test fields have `L²` gradients on the open cube -/

/-- **The gradient of an order-one test field is an `L²` field of the open
cube.**  The test constraint bounds `‖∇g‖_{L̲²(Q)}` by one, which is finite, and
the two measures `normalizedCubeMeasure Q` and `volume.restrict (openCubeSet Q)`
differ by the positive finite factor `(cubeVolume Q)⁻¹`. -/
theorem memVectorL2_euclideanGradient_of_testField {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : SuperdiffusionCLT.Section2.Norms.IsVecHatTestFieldOrderOne Q g) :
    MemVectorL2 (openCubeSet Q) (euclideanGradient g) := by
  have hfin : ResponseFields.vecCubeLpENorm Q 2 (euclideanGradient g) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans
        (SuperdiffusionCLT.Section2.Norms.vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm
          Q g)
        hg.h1_le_one)
  have hmem :=
    ResponseFields.memLp_hilbertifyVecField_iff.1
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_euclideanGradient
        hg.contDiff hfin)
  have h2 := memLp_two_volume_restrict_of_memLp Q hmem
  rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h2

/-! ## The pairing, read in the `L²` class -/

/-- **The normalized cube pairing of two `L²` vector fields is the scaled `L²`
inner product of their classes.**  This is the value identity that turns every
statement about the hatted negative norm into class-level algebra, with no
Bochner-integral splitting anywhere. -/
theorem volumeAverage_vecDot_eq_inv_mul_inner {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G) :
    volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x)) =
      (cubeVolume Q)⁻¹ * (inner ℝ (toHilbertVectorL2OfVecField hF)
        (toHilbertVectorL2OfVecField hG) : ℝ) := by
  rw [volumeAverage, volume_cubeSet_toReal,
    MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q),
    ← inner_toHilbertVectorL2OfVecField_eq_integral hF hG]

/-- The `ResponseFields` pairing density is the `vecDot` integrand, so the two
readings of the normalized average coincide. -/
theorem volumeAverage_vecGradientPairingDensity_eq_vecDot (Q : TriadicCube d)
    (F : Vec d → Vec d) (g : Vec d → ℝ) :
    volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) =
      volumeAverage (cubeSet Q) (fun x => vecDot (F x) (euclideanGradient g x)) := by
  rw [funext fun x => vecGradientPairingDensity_eq_vecDot F g x]

/-- **The pairing of a class with a test field is the scaled inner product of
the class with the test gradient class.**  The representative is the canonical
`hilbertClassField`, so the left side is class-level. -/
theorem volumeAverage_vecDot_hilbertClassField_eq_inv_mul_inner {Q : TriadicCube d}
    {g : Vec d → ℝ} (hG : MemVectorL2 (openCubeSet Q) (euclideanGradient g))
    (v : HilbertVectorL2 (openCubeSet Q)) :
    volumeAverage (cubeSet Q) (fun x => vecDot (hilbertClassField v x)
        (euclideanGradient g x)) =
      (cubeVolume Q)⁻¹ * inner ℝ v (toHilbertVectorL2OfVecField hG) := by
  rw [volumeAverage_vecDot_eq_inv_mul_inner (memVectorL2_hilbertClassField v) hG,
    toHilbertVectorL2OfVecField_hilbertClassField]

/-! ## The carrier only sees the `L²` class -/

/-- **The order-one hatted negative norm is blind to null sets of the open
cube.**  Every test field of the class has a gradient in `L²(openCubeSet Q)`, so
the pairing with it is determined by the class of the field. -/
theorem vecHatNegENormOrderOne_congr_ae {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q F =
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q G := by
  have hpair : ∀ g : Vec d → ℝ,
      volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) =
        volumeAverage (cubeSet Q) (vecGradientPairingDensity G g) := by
    intro g
    have hae : vecGradientPairingDensity F g
        =ᵐ[volumeMeasureOn (openCubeSet Q)] vecGradientPairingDensity G g := by
      filter_upwards [hFG] with x hx
      simp only [vecGradientPairingDensity_eq_vecDot, hx]
    have h : ∫ x in cubeSet Q, vecGradientPairingDensity F g x ∂volume =
        ∫ x in cubeSet Q, vecGradientPairingDensity G g x ∂volume := by
      rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q),
        MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]
      exact MeasureTheory.integral_congr_ae hae
    rw [volumeAverage, volumeAverage, h]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun g => iSup_le fun hg => ?_
    rw [hpair g]
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  · refine iSup_le fun g => iSup_le fun hg => ?_
    rw [← hpair g]
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

/-! ## The functional is Lipschitz in the class -/

/-- **One-sided Lipschitz bound.**  For each order-one test field `g`, the
pairing against a class is the scaled inner product with the test gradient class
(`volumeAverage_vecDot_hilbertClassField_eq_inv_mul_inner`).  The real triangle
inequality in the inner product then splits `⟪v, ∇g⟫` into the `w`-term and the
`(v − w)`-term; the second is bounded by Cauchy–Schwarz and the test-class
constraint `‖∇g‖_{L̲²(Q)} ≤ 1`.  Since the bound is uniform over the whole test
class, it holds for the supremum. -/
theorem vecHatNegENormOrderOne_le_add_classDist {Q : TriadicCube d}
    (v w : HilbertVectorL2 (openCubeSet Q)) :
    SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField v) ≤
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField w) +
        ENNReal.ofReal
          (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField (v - w))).toReal := by
  refine SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne_le fun g hg => ?_
  have hgfin : ResponseFields.vecCubeLpENorm Q 2 (euclideanGradient g) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans
        (SuperdiffusionCLT.Section2.Norms.vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm
          Q g)
        hg.h1_le_one)
  have hGmem : MemVectorL2 (openCubeSet Q) (euclideanGradient g) :=
    memVectorL2_euclideanGradient_of_testField hg
  have hvalV := volumeAverage_vecDot_hilbertClassField_eq_inv_mul_inner (Q := Q) hGmem v
  have hvalW := volumeAverage_vecDot_hilbertClassField_eq_inv_mul_inner (Q := Q) hGmem w
  have hvalD := volumeAverage_vecDot_hilbertClassField_eq_inv_mul_inner (Q := Q) hGmem
    (v - w)
  have hm1 : (ResponseFields.vecCubeLpENorm Q 2 (euclideanGradient g)).toReal ≤ 1 := by
    have hle : ResponseFields.vecCubeLpENorm Q 2 (euclideanGradient g) ≤ 1 :=
      le_trans
        (SuperdiffusionCLT.Section2.Norms.vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm
          Q g)
        hg.h1_le_one
    simpa using (ENNReal.toReal_le_toReal hgfin ENNReal.one_ne_top).2 hle
  have hboundD : |(cubeVolume Q)⁻¹ *
      inner ℝ (v - w) (toHilbertVectorL2OfVecField hGmem)| ≤
      (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField (v - w))).toReal := by
    rw [← hvalD]
    refine le_trans
      (SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
        (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
          (memVectorL2_hilbertClassField (v - w)))
        (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_euclideanGradient
          hg.contDiff hgfin)) ?_
    calc (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField (v - w))).toReal *
          (ResponseFields.vecCubeLpENorm Q 2 (euclideanGradient g)).toReal
        ≤ (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField (v - w))).toReal * 1 :=
          mul_le_mul_of_nonneg_left hm1 ENNReal.toReal_nonneg
      _ = (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField (v - w))).toReal :=
          mul_one _
  have hadd : inner ℝ v (toHilbertVectorL2OfVecField hGmem) =
      inner ℝ w (toHilbertVectorL2OfVecField hGmem) +
        inner ℝ (v - w) (toHilbertVectorL2OfVecField hGmem) := by
    conv_lhs => rw [show v = w + (v - w) from by abel]
    rw [inner_add_left]
  have hstep : |volumeAverage (cubeSet Q) (fun x => vecDot (hilbertClassField v x)
        (euclideanGradient g x))| ≤
      |volumeAverage (cubeSet Q) (fun x => vecDot (hilbertClassField w x)
        (euclideanGradient g x))| +
        (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField (v - w))).toReal := by
    rw [hvalV, hvalW,
      show (cubeVolume Q)⁻¹ * inner ℝ v (toHilbertVectorL2OfVecField hGmem) =
        (cubeVolume Q)⁻¹ * inner ℝ w (toHilbertVectorL2OfVecField hGmem) +
          (cubeVolume Q)⁻¹ * inner ℝ (v - w) (toHilbertVectorL2OfVecField hGmem) from by
        rw [hadd, mul_add]]
    exact le_trans (abs_add_le _ _) (add_le_add_right hboundD _)
  rw [volumeAverage_vecGradientPairingDensity_eq_vecDot]
  refine le_trans (le_trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
    (ENNReal.ofReal_le_ofReal hstep)) ?_
  rw [ENNReal.ofReal_add (abs_nonneg _) ENNReal.toReal_nonneg]
  refine add_le_add ?_ le_rfl
  rw [← volumeAverage_vecGradientPairingDensity_eq_vecDot]
  exact SuperdiffusionCLT.Section2.Norms.ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne
    (hilbertClassField w) hg

/-! ## The Lipschitz constant, and the functional is finite -/

/-- The normalized-to-unnormalized `L²` conversion factor of the cube: the
constant that turns the class norm into the normalized cube norm. -/
noncomputable def hatNegClassLipschitzConst (Q : TriadicCube d) : ℝ :=
  (ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ ((1 : ENNReal) / 2).toReal).toReal

theorem hatNegClassLipschitzConst_nonneg (Q : TriadicCube d) :
    0 ≤ hatNegClassLipschitzConst Q :=
  ENNReal.toReal_nonneg

/-- **The class distance in the normalized cube norm.**  The normalized `L̲²(Q)`
norm of the canonical representative of a class is the Lipschitz constant times
the class norm. -/
theorem toReal_vecCubeLpENorm_hilbertClassField (Q : TriadicCube d)
    (v : HilbertVectorL2 (openCubeSet Q)) :
    (ResponseFields.vecCubeLpENorm Q 2 (hilbertClassField v)).toReal =
      hatNegClassLipschitzConst Q * ‖v‖ := by
  rw [hatNegClassLipschitzConst,
    SuperdiffusionCLT.Section3.Setup.vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField
      (memVectorL2_hilbertClassField v),
    toHilbertVectorL2OfVecField_hilbertClassField, ENNReal.toReal_mul, toReal_enorm]

/-- **The class functional is finite**, being dominated by the `L̲²(Q)` norm of
the canonical representative. -/
theorem vecHatNegENormOrderOne_hilbertClassField_ne_top (Q : TriadicCube d)
    (v : HilbertVectorL2 (openCubeSet Q)) :
    SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField v) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_
    (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne_le_vecCubeLpENorm
      (SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
        (memVectorL2_hilbertClassField v)))
  rw [SuperdiffusionCLT.Section3.Setup.vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField
      (memVectorL2_hilbertClassField v),
    toHilbertVectorL2OfVecField_hilbertClassField]
  exact ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
    enorm_ne_top

/-- The one-sided Lipschitz bound with the explicit constant. -/
theorem vecHatNegENormOrderOne_classDist_le_add (Q : TriadicCube d)
    (v w : HilbertVectorL2 (openCubeSet Q)) :
    SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField v) ≤
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField w) +
        ENNReal.ofReal (hatNegClassLipschitzConst Q * ‖v - w‖) := by
  rw [← toReal_vecCubeLpENorm_hilbertClassField (Q := Q) (v - w)]
  exact vecHatNegENormOrderOne_le_add_classDist v w

/-- The one-sided Lipschitz bound, in the real reading of the functional. -/
theorem toReal_vecHatNegENormOrderOne_le_add_classDist (Q : TriadicCube d)
    (v w : HilbertVectorL2 (openCubeSet Q)) :
    (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
        (hilbertClassField v)).toReal ≤
      (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
        (hilbertClassField w)).toReal +
        hatNegClassLipschitzConst Q * ‖v - w‖ := by
  have hW : SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
      (hilbertClassField w) ≠ ⊤ :=
    vecHatNegENormOrderOne_hilbertClassField_ne_top Q w
  have hc : 0 ≤ hatNegClassLipschitzConst Q * ‖v - w‖ :=
    mul_nonneg (hatNegClassLipschitzConst_nonneg Q) (norm_nonneg _)
  calc (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
        (hilbertClassField v)).toReal
      ≤ (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField w) +
          ENNReal.ofReal (hatNegClassLipschitzConst Q * ‖v - w‖)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hW, ENNReal.ofReal_ne_top⟩)
          (vecHatNegENormOrderOne_classDist_le_add Q v w)
    _ = (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
          (hilbertClassField w)).toReal +
          hatNegClassLipschitzConst Q * ‖v - w‖ := by
        rw [ENNReal.toReal_add hW ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc]

/-- **The class functional is Lipschitz**, hence continuous and measurable. -/
theorem lipschitzWith_vecHatNegENormOrderOne_classToReal (Q : TriadicCube d) :
    LipschitzWith ⟨hatNegClassLipschitzConst Q, hatNegClassLipschitzConst_nonneg Q⟩
      (fun v : HilbertVectorL2 (openCubeSet Q) =>
        (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
          (hilbertClassField v)).toReal) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [Real.dist_eq, dist_eq_norm]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · have h := toReal_vecHatNegENormOrderOne_le_add_classDist Q v w
    show _ ≤ hatNegClassLipschitzConst Q * _
    linarith only [h]
  · have h := toReal_vecHatNegENormOrderOne_le_add_classDist Q w v
    rw [norm_sub_rev w v] at h
    show _ ≤ hatNegClassLipschitzConst Q * _
    linarith only [h]

/-- **The order-one hatted negative norm of a class is measurable in the
class.**  It is the real Lipschitz functional read through `ENNReal.ofReal`,
which is finite everywhere. -/
theorem measurable_vecHatNegENormOrderOne_hilbertClassField (Q : TriadicCube d) :
    Measurable fun v : HilbertVectorL2 (openCubeSet Q) =>
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField v) := by
  have hmeas : Measurable fun v : HilbertVectorL2 (openCubeSet Q) =>
      (SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
        (hilbertClassField v)).toReal :=
    (lipschitzWith_vecHatNegENormOrderOne_classToReal Q).continuous.measurable
  have heq : (fun v : HilbertVectorL2 (openCubeSet Q) =>
        SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField v)) =
      fun v => ENNReal.ofReal
        ((SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q
          (hilbertClassField v)).toReal) := by
    funext v
    exact (ENNReal.ofReal_toReal (vecHatNegENormOrderOne_hilbertClassField_ne_top Q v)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.measurable.comp hmeas

/-! ## The obligation, at the class and at the field -/

/-- **The obligation from an almost-everywhere measurable class.**  No
countability of the test class is used: the functional is Lipschitz in the class
norm, and the Lipschitz bound is uniform over the whole uncountable test class. -/
theorem aemeasurable_vecHatNegENormOrderOne_hilbertClassField {α : Type*} [MeasurableSpace α]
    {Q : TriadicCube d} {mu : MeasureTheory.Measure α}
    {V : α → HilbertVectorL2 (openCubeSet Q)} (hV : AEMeasurable V mu) :
    AEMeasurable (fun a : α =>
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (hilbertClassField (V a)))
      mu :=
  (measurable_vecHatNegENormOrderOne_hilbertClassField Q).comp_aemeasurable hV

/-- **The obligation from an almost-everywhere measurable `L²` class of a vector
field.**  The canonical representative of the class agrees with the field almost
everywhere, and the carrier only sees the class. -/
theorem aemeasurable_vecHatNegENormOrderOne_of_classMeasurable {α : Type*} [MeasurableSpace α]
    {Q : TriadicCube d} {mu : MeasureTheory.Measure α} {F : α → Vec d → Vec d}
    (hF : ∀ a : α, MemVectorL2 (openCubeSet Q) (F a))
    (hclass : AEMeasurable (fun a : α => toHilbertVectorL2OfVecField (hF a)) mu) :
    AEMeasurable (fun a : α =>
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne Q (F a)) mu := by
  have h1 := aemeasurable_vecHatNegENormOrderOne_hilbertClassField (Q := Q)
    (V := fun a : α => toHilbertVectorL2OfVecField (hF a)) hclass
  refine h1.congr ?_
  filter_upwards with a
  exact vecHatNegENormOrderOne_congr_ae
    (hilbertClassField_toHilbertVectorL2OfVecField (U := openCubeSet Q) (hF a))

/-- **The obligation `_hMeasHminus` of `term1_final`, for the pairing field.**
The `L²(cu_m)` class of the pairing field is measurable in the sample by the
`measurable_gluedGradientClass` route, and the carrier only sees that
class. -/
theorem aemeasurable_vecHatNegENormOrderOne_pairingField [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (F qTilde : Vec d) {mu : MeasureTheory.Measure (ShellSeq d)} :
    AEMeasurable (fun omega : ShellSeq d =>
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne (originCube d (m : ℤ))
        (pairingField hnu L k m F qTilde omega)) mu :=
  aemeasurable_vecHatNegENormOrderOne_of_classMeasurable
    (Q := originCube d (m : ℤ))
    (F := fun omega : ShellSeq d => pairingField hnu L k m F qTilde omega)
    (fun omega => memVectorL2_pairingField hnu L k m F qTilde omega (originCube d (m : ℤ)))
    (aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass hnu L k m F qTilde
      (measurable_gluedGradientClass hnu L k m F).aemeasurable)

/-- **The obligation `_hMeasHminus` in the shape of `term1_final`.**  The integrand is the
glued field `a_ℓ ∇ũ_n − q̃` exactly as it appears among the binders of
`term1_final`. -/
theorem aemeasurable_vecHatNegENormOrderOne_term1Hminus [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) :
    AEMeasurable (fun omega : ShellSeq d =>
      SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne (originCube d (S.m : ℤ))
        (fun x : Vec d =>
          matVecMul ((SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
            nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x) -
              qVector hnu P S.ell S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e))) P.toMeasure :=
  aemeasurable_vecHatNegENormOrderOne_pairingField hnu S.ell S.n S.m
    (fluxSlot nu S.LPrime P S.n e)
    (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))

end

end SuperdiffusionCLT.Section3.Terms
