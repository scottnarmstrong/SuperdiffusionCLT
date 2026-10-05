/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pF

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Half cube: the reflection in the flat face

The open half cube `flatHalfCube e m = {x ∈ (-3^m/2, 3^m/2)^d : 0 < x e}` has the hyperplane
`x e = 0` as its flat face and doubles, under the reflection `hcFlip e`, to the whole cube
`openCubeSet (originCube d m)`.  This file sets up the reflection, the decomposition of the
cube into the half cube, its reflected copy and a null set, the extensions of functions and vector
fields by parity (`hcExt`, `hcExtVec`), and the exact `L^p` norm of an extension.

The parity of the flux datum of an odd response is the parity of the gradient of an odd function:
the tangential components are odd and the normal component is even (`hcSgn`).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The reflection in the hyperplane `x e = 0`. -/
def hcFlip (e : Fin d) (x : Vec d) : Vec d := fun i => if i = e then -x i else x i

theorem hcFlip_flip (e : Fin d) (x : Vec d) : hcFlip e (hcFlip e x) = x := by
  funext i; by_cases h : i = e <;> simp [hcFlip, h]

theorem hcFlip_apply_e (e : Fin d) (x : Vec d) : hcFlip e x e = - x e := by simp [hcFlip]

theorem hcFlip_apply_ne {e i : Fin d} (h : i ≠ e) (x : Vec d) : hcFlip e x i = x i := by
  simp [hcFlip, h]

theorem measurePreserving_hcFlip (e : Fin d) :
    MeasurePreserving (hcFlip e) volume volume := by
  have := volume_preserving_pi (α' := fun _ : Fin d => ℝ) (β' := fun _ : Fin d => ℝ)
    (f := fun i (t : ℝ) => if i = e then -t else t) (fun i => by
      by_cases h : i = e
      · simp only [h, ite_true]; exact Measure.measurePreserving_neg _
      · simp only [h, ite_false]; exact MeasurePreserving.id _)
  exact this

theorem continuous_hcFlip (e : Fin d) : Continuous (hcFlip e) := by
  refine continuous_pi fun i => ?_
  by_cases h : i = e
  · simp only [hcFlip, h, ite_true]; exact (continuous_apply e).neg
  · simp only [hcFlip, h, ite_false]; exact continuous_apply i

/-- The reflection as a homeomorphism. -/
def hcFlipHomeo (e : Fin d) : Vec d ≃ₜ Vec d where
  toFun := hcFlip e
  invFun := hcFlip e
  left_inv := hcFlip_flip e
  right_inv := hcFlip_flip e
  continuous_toFun := continuous_hcFlip e
  continuous_invFun := continuous_hcFlip e

theorem measurableEmbedding_hcFlip (e : Fin d) : MeasurableEmbedding (hcFlip e) :=
  (hcFlipHomeo e).measurableEmbedding

/-- The open half cube above the hyperplane `x e = 0`: the open centred cube of side `3^m`
cut by `0 < x e`. -/
def flatHalfCube (e : Fin d) (m : ℤ) : Set (Vec d) :=
  openCubeSet (originCube d m) ∩ {x | 0 < x e}

theorem hc_mem_openCubeSet_originCube_iff (m : ℤ) (x : Vec d) :
    x ∈ openCubeSet (originCube d m) ↔ ∀ i, -((3 : ℝ) ^ m / 2) < x i ∧ x i < (3 : ℝ) ^ m / 2 := by
  simp only [openCubeSet, originCube, Set.mem_ofPred_eq, cubeScaleFactor]
  refine forall_congr' fun i => ?_
  simp only [Pi.zero_apply, Int.cast_zero, zero_sub, zero_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

theorem hcFlip_mem_openCubeSet_iff (e : Fin d) (m : ℤ) (x : Vec d) :
    hcFlip e x ∈ openCubeSet (originCube d m) ↔ x ∈ openCubeSet (originCube d m) := by
  rw [hc_mem_openCubeSet_originCube_iff, hc_mem_openCubeSet_originCube_iff]
  refine forall_congr' fun i => ?_
  by_cases h : i = e
  · subst h
    rw [hcFlip_apply_e]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]
  · rw [hcFlip_apply_ne h]

theorem flatHalfCube_subset (e : Fin d) (m : ℤ) : flatHalfCube e m ⊆ openCubeSet (originCube d m) :=
  Set.inter_subset_left

theorem isOpen_flatHalfCube (e : Fin d) (m : ℤ) : IsOpen (flatHalfCube e m) :=
  (isOpen_openCubeSet _).inter (isOpen_lt continuous_const (continuous_apply e))

theorem measurableSet_flatHalfCube (e : Fin d) (m : ℤ) : MeasurableSet (flatHalfCube e m) :=
  (isOpen_flatHalfCube e m).measurableSet

theorem preimage_hcFlip_flatHalfCube (e : Fin d) (m : ℤ) :
    hcFlip e ⁻¹' flatHalfCube e m = openCubeSet (originCube d m) ∩ {x | x e < 0} := by
  ext x
  simp only [flatHalfCube, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
    hcFlip_mem_openCubeSet_iff, hcFlip_apply_e]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith only [h2]⟩

theorem disjoint_flatHalfCube_preimage (e : Fin d) (m : ℤ) :
    Disjoint (flatHalfCube e m) (hcFlip e ⁻¹' flatHalfCube e m) := by
  rw [preimage_hcFlip_flatHalfCube]
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 : 0 < x e := hx.2
  have h2 : x e < 0 := hx'.2
  linarith only [h1, h2]

theorem hc_volume_hyperplane (e : Fin d) : volume {x : Vec d | x e = 0} = 0 := by
  have h : {x : Vec d | x e = 0} = (LinearMap.ker (LinearMap.proj e : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
      Set (Vec d)) := by
    ext x; simp
  rw [h]
  refine Measure.addHaar_submodule volume _ ?_
  intro htop
  have : (Pi.single e (1 : ℝ) : Vec d) ∈ LinearMap.ker (LinearMap.proj e : (Fin d → ℝ) →ₗ[ℝ] ℝ) := by
    rw [htop]; trivial
  simp at this

theorem hc_openCubeSet_ae_eq_union (e : Fin d) (m : ℤ) :
    openCubeSet (originCube d m) =ᵐ[volume]
      (flatHalfCube e m ∪ hcFlip e ⁻¹' flatHalfCube e m : Set (Vec d)) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (t := {x : Vec d | x e = 0}) (fun x hx => ?_) (hc_volume_hyperplane e)
    obtain ⟨hxQ, hxn⟩ := hx
    by_contra hne
    rcases lt_trichotomy (x e) 0 with h | h | h
    · exact hxn (Or.inr (by rw [preimage_hcFlip_flatHalfCube]; exact ⟨hxQ, h⟩))
    · exact hne h
    · exact hxn (Or.inl ⟨hxQ, h⟩)
  · have : (flatHalfCube e m ∪ hcFlip e ⁻¹' flatHalfCube e m) \ openCubeSet (originCube d m) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := hx
      rcases hx1 with h | h
      · exact hx2 (flatHalfCube_subset e m h)
      · rw [preimage_hcFlip_flatHalfCube] at h; exact hx2 h.1
    rw [this]; exact measure_empty

theorem hc_restrict_openCubeSet_eq (e : Fin d) (m : ℤ) :
    volume.restrict (openCubeSet (originCube d m)) =
      volume.restrict (flatHalfCube e m) + volume.restrict (hcFlip e ⁻¹' flatHalfCube e m) := by
  rw [Measure.restrict_congr_set (hc_openCubeSet_ae_eq_union e m),
    Measure.restrict_union (disjoint_flatHalfCube_preimage e m)
      ((measurableEmbedding_hcFlip e).measurable (measurableSet_flatHalfCube e m))]

/-- The reflection as a continuous linear map. -/
def hcFlipL (e : Fin d) : Vec d →L[ℝ] Vec d :=
  ContinuousLinearMap.pi fun i => if i = e then -(ContinuousLinearMap.proj i) else
    ContinuousLinearMap.proj i

theorem hcFlipL_apply (e : Fin d) (x : Vec d) : hcFlipL e x = hcFlip e x := by
  funext i
  by_cases h : i = e <;> simp [hcFlipL, hcFlip, h]

/-- The sign picked up by the `i`-th partial derivative under the reflection. -/
def hcSgn (e i : Fin d) : ℝ := if i = e then 1 else -1

theorem hcFlip_basisVec (e i : Fin d) : hcFlip e (basisVec i) = -hcSgn e i • basisVec i := by
  funext j
  by_cases hj : j = e <;> by_cases hi : i = e <;> by_cases hji : j = i <;>
    simp_all [hcFlip, hcSgn, basisVec]

theorem fderiv_comp_hcFlip {φ : Vec d → ℝ} (hφ : Differentiable ℝ φ) (e : Fin d) (x : Vec d)
    (i : Fin d) :
    fderiv ℝ (fun y => φ (hcFlip e y)) x (basisVec i) =
      -hcSgn e i * fderiv ℝ φ (hcFlip e x) (basisVec i) := by
  have h1 : HasFDerivAt (fun y => φ (hcFlip e y))
      ((fderiv ℝ φ (hcFlip e x)).comp (hcFlipL e)) x := by
    have h2 : HasFDerivAt φ (fderiv ℝ φ (hcFlipL e x)) (hcFlipL e x) :=
      (hφ (hcFlipL e x)).hasFDerivAt
    have := h2.comp x (hcFlipL e).hasFDerivAt
    simpa only [Function.comp_def, hcFlipL_apply] using this
  rw [h1.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hcFlipL_apply, hcFlip_basisVec, map_smul,
    smul_eq_mul, neg_mul]

theorem hcFlip_zero_of_mem {e : Fin d} {x : Vec d} (hx : x e = 0) : hcFlip e x = x := by
  funext i
  by_cases h : i = e
  · subst h; simp [hcFlip, hx]
  · simp [hcFlip, h]

theorem hc_integral_openCubeSet_split (e : Fin d) (m : ℤ) {a : Vec d → ℝ}
    (ha : IntegrableOn a (openCubeSet (originCube d m))) :
    ∫ x in openCubeSet (originCube d m), a x =
      (∫ x in flatHalfCube e m, a x) + ∫ x in flatHalfCube e m, a (hcFlip e x) := by
  have h1 : Integrable a (volume.restrict (flatHalfCube e m)) :=
    Integrable.mono_measure ha (by rw [hc_restrict_openCubeSet_eq e m]; exact Measure.le_add_right le_rfl)
  have h2 : Integrable a (volume.restrict (hcFlip e ⁻¹' flatHalfCube e m)) :=
    Integrable.mono_measure ha (by rw [hc_restrict_openCubeSet_eq e m]; exact Measure.le_add_left le_rfl)
  rw [hc_restrict_openCubeSet_eq e m, integral_add_measure h1 h2]
  congr 1
  have := (measurePreserving_hcFlip e).setIntegral_preimage_emb (measurableEmbedding_hcFlip e)
    (fun y => a (hcFlip e y)) (flatHalfCube e m)
  simp only [hcFlip_flip] at this
  exact this

/-- Extension of a function on the half cube to the cube by the reflection, with the sign `σ`. -/
noncomputable def hcExt (σ : ℝ) (e : Fin d) (F : Vec d → ℝ) (x : Vec d) : ℝ :=
  if 0 < x e then F x else σ * F (hcFlip e x)

/-- The extension of a vector field: component `i` is extended with the sign `hcSgn e i`.
This is the parity of the gradient of an odd function, and the parity of the flux datum of an
odd response. -/
noncomputable def hcExtVec (e : Fin d) (G : Vec d → Vec d) (x : Vec d) : Vec d :=
  fun i => hcExt (hcSgn e i) e (fun y => G y i) x

theorem hcExt_of_pos {σ : ℝ} {e : Fin d} {F : Vec d → ℝ} {x : Vec d} (hx : 0 < x e) :
    hcExt σ e F x = F x := by simp [hcExt, hx]

theorem hcExt_of_neg {σ : ℝ} {e : Fin d} {F : Vec d → ℝ} {x : Vec d} (hx : x e < 0) :
    hcExt σ e F x = σ * F (hcFlip e x) := by
  simp [hcExt, not_lt.2 hx.le]

theorem hcExt_comp_flip {σ : ℝ} {e : Fin d} {F : Vec d → ℝ} {x : Vec d} (hx : 0 < x e) :
    hcExt σ e F (hcFlip e x) = σ * F x := by
  have : hcFlip e x e < 0 := by rw [hcFlip_apply_e]; linarith only [hx]
  rw [hcExt_of_neg this, hcFlip_flip]

theorem hcExt_sub (σ : ℝ) (e : Fin d) (F F' : Vec d → ℝ) :
    hcExt σ e (fun x => F x - F' x) = fun x => hcExt σ e F x - hcExt σ e F' x := by
  funext x; unfold hcExt; split_ifs <;> ring

theorem lintegral_openCubeSet_hcExt (e : Fin d) (m : ℤ) {σ : ℝ} (hσ : |σ| = 1)
    (F : Vec d → ℝ) (q : ℝ) :
    ∫⁻ x in openCubeSet (originCube d m), ‖hcExt σ e F x‖ₑ ^ q =
      2 * ∫⁻ x in flatHalfCube e m, ‖F x‖ₑ ^ q := by
  rw [hc_restrict_openCubeSet_eq e m, lintegral_add_measure]
  have h1 : ∫⁻ x in flatHalfCube e m, ‖hcExt σ e F x‖ₑ ^ q =
      ∫⁻ x in flatHalfCube e m, ‖F x‖ₑ ^ q := by
    refine setLIntegral_congr_fun (measurableSet_flatHalfCube e m) fun x hx => ?_
    rw [hcExt_of_pos hx.2]
  have h2 : ∫⁻ x in hcFlip e ⁻¹' flatHalfCube e m, ‖hcExt σ e F x‖ₑ ^ q =
      ∫⁻ x in flatHalfCube e m, ‖F x‖ₑ ^ q := by
    have := (measurePreserving_hcFlip e).setLIntegral_comp_preimage_emb
      (measurableEmbedding_hcFlip e) (fun y => ‖hcExt σ e F (hcFlip e y)‖ₑ ^ q)
      (flatHalfCube e m)
    simp only [hcFlip_flip] at this
    rw [this]
    refine setLIntegral_congr_fun (measurableSet_flatHalfCube e m) fun x hx => ?_
    rw [hcExt_comp_flip hx.2, enorm_mul]
    have : ‖σ‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs, hσ]; simp
    rw [this, one_mul]
  rw [h1, h2, two_mul]

theorem aestronglyMeasurable_hcExt (e : Fin d) (m : ℤ) (σ : ℝ) {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (flatHalfCube e m))) :
    AEStronglyMeasurable (hcExt σ e F) (volume.restrict (openCubeSet (originCube d m))) := by
  rw [hc_restrict_openCubeSet_eq e m]
  refine AEStronglyMeasurable.add_measure ?_ ?_
  · refine hF.congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_flatHalfCube e m)] with x hx
    rw [hcExt_of_pos hx.2]
  · have hmp := (measurePreserving_hcFlip e).restrict_preimage_emb (measurableEmbedding_hcFlip e)
      (flatHalfCube e m)
    have h1 : AEStronglyMeasurable (fun x => σ * F (hcFlip e x))
        (volume.restrict (hcFlip e ⁻¹' flatHalfCube e m)) :=
      aestronglyMeasurable_const.mul (hF.comp_measurePreserving hmp)
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem ((measurableEmbedding_hcFlip e).measurable
      (measurableSet_flatHalfCube e m))] with x hx
    rw [preimage_hcFlip_flatHalfCube] at hx
    rw [hcExt_of_neg hx.2]

theorem eLpNorm_hcExt_volume (e : Fin d) (m : ℤ) {σ : ℝ} (hσ : |σ| = 1) {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict (flatHalfCube e m)))
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (hcExt σ e F) p (volume.restrict (openCubeSet (originCube d m))) =
      2 ^ (1 / p.toReal) * eLpNorm F p (volume.restrict (flatHalfCube e m)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (aestronglyMeasurable_hcExt e m σ hF),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hF,
    lintegral_openCubeSet_hcExt e m hσ, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

/-- The normalized measure on the half cube. -/
noncomputable def flatHalfMeasure (e : Fin d) (m : ℤ) : Measure (Vec d) :=
  (normalizedCubeMeasure (originCube d m)).restrict (flatHalfCube e m)

theorem flatHalfMeasure_eq (e : Fin d) (m : ℤ) :
    flatHalfMeasure e m = ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ •
      volume.restrict (flatHalfCube e m) := by
  rw [flatHalfMeasure, normalizedCubeMeasure_eq_smul, Measure.restrict_smul,
    Measure.restrict_restrict (measurableSet_flatHalfCube e m),
    Set.inter_eq_left.2 (flatHalfCube_subset e m)]

theorem aestronglyMeasurable_flatHalfMeasure_iff (e : Fin d) (m : ℤ) {F : Vec d → ℝ} :
    AEStronglyMeasurable F (flatHalfMeasure e m) ↔
      AEStronglyMeasurable F (volume.restrict (flatHalfCube e m)) := by
  have hv : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  have h1 : ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ ≠ 0 := by
    simpa using hv
  have h2 : ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro hF
    have : volume.restrict (flatHalfCube e m) = (ENNReal.ofReal (cubeVolume (originCube d m))⁻¹)⁻¹ •
        flatHalfMeasure e m := by
      rw [flatHalfMeasure_eq, smul_smul, ENNReal.inv_mul_cancel h1 h2, one_smul]
    rw [this]
    exact hF.smul_measure _
  · intro hF
    rw [flatHalfMeasure_eq]
    exact hF.smul_measure _

theorem aestronglyMeasurable_hcExt_normalized (e : Fin d) (m : ℤ) (σ : ℝ) {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (flatHalfMeasure e m)) :
    AEStronglyMeasurable (hcExt σ e F) (normalizedCubeMeasure (originCube d m)) := by
  rw [normalizedCubeMeasure_eq_smul]
  exact (aestronglyMeasurable_hcExt e m σ
    ((aestronglyMeasurable_flatHalfMeasure_iff e m).1 hF)).smul_measure _

theorem eLpNorm_hcExt_normalized (e : Fin d) (m : ℤ) {σ : ℝ} (hσ : |σ| = 1) {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (flatHalfMeasure e m))
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (hcExt σ e F) p (normalizedCubeMeasure (originCube d m)) =
      2 ^ (1 / p.toReal) * eLpNorm F p (flatHalfMeasure e m) := by
  have hF' : AEStronglyMeasurable F (volume.restrict (flatHalfCube e m)) :=
    (aestronglyMeasurable_flatHalfMeasure_iff e m).1 hF
  have hE' := aestronglyMeasurable_hcExt e m σ hF'
  have hexp : (1 / p).toReal = 1 / p.toReal := by simp [ENNReal.toReal_inv]
  rw [flatHalfMeasure_eq, normalizedCubeMeasure_eq_smul,
    eLpNorm_smul_measure_of_ne_top hpt _ _ hF', eLpNorm_smul_measure_of_ne_top hpt _ _ hE',
    eLpNorm_hcExt_volume e m hσ hF' hp0 hpt, smul_eq_mul, smul_eq_mul, hexp]
  ring

theorem memLp_hcExt_normalized (e : Fin d) (m : ℤ) {σ : ℝ} (hσ : |σ| = 1) {F : Vec d → ℝ}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hF : MemLp F p (flatHalfMeasure e m)) :
    MemLp (hcExt σ e F) p (normalizedCubeMeasure (originCube d m)) := by
  rw [memLp_iff, eLpNorm_hcExt_normalized e m hσ hF.aestronglyMeasurable hp0 hpt]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
    hF.eLpNorm_lt_top

theorem norm_hcExtVec (e : Fin d) (G : Vec d → Vec d) (x : Vec d) :
    ‖hcExtVec e G x‖ = hcExt 1 e (fun y => ‖G y‖) x := by
  unfold hcExtVec hcExt
  split_ifs with h
  · rfl
  · rw [one_mul]
    refine le_antisymm ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simp only [Real.norm_eq_abs, abs_mul]
      have : |hcSgn e i| = 1 := by by_cases hi : i = e <;> simp [hcSgn, hi]
      rw [this, one_mul]
      simpa using norm_le_pi_norm (G (hcFlip e x)) i
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      have h1 : |hcSgn e i| = 1 := by by_cases hi : i = e <;> simp [hcSgn, hi]
      have h2 := norm_le_pi_norm (fun j => hcSgn e j * G (hcFlip e x) j) i
      simp only [Real.norm_eq_abs, abs_mul, h1, one_mul] at h2 ⊢
      exact h2

theorem aestronglyMeasurable_hcExtVec_normalized (e : Fin d) (m : ℤ) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (flatHalfMeasure e m)) :
    AEStronglyMeasurable (hcExtVec e G) (normalizedCubeMeasure (originCube d m)) := by
  refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun i => ?_)
  exact (aestronglyMeasurable_hcExt_normalized e m (hcSgn e i)
    ((continuous_apply i).comp_aestronglyMeasurable hG)).aemeasurable

theorem eLpNorm_hcExtVec_normalized (e : Fin d) (m : ℤ) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (flatHalfMeasure e m)) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (hcExtVec e G) p (normalizedCubeMeasure (originCube d m)) =
      2 ^ (1 / p.toReal) * eLpNorm G p (flatHalfMeasure e m) := by
  have h1 : eLpNorm (hcExtVec e G) p (normalizedCubeMeasure (originCube d m)) =
      eLpNorm (fun x => ‖hcExtVec e G x‖) p (normalizedCubeMeasure (originCube d m)) :=
    (eLpNorm_norm _ (aestronglyMeasurable_hcExtVec_normalized e m hG)).symm
  have h2 : eLpNorm G p (flatHalfMeasure e m) = eLpNorm (fun x => ‖G x‖) p (flatHalfMeasure e m) :=
    (eLpNorm_norm _ hG).symm
  rw [h1, h2]
  simp only [norm_hcExtVec]
  exact eLpNorm_hcExt_normalized e m (by simp) hG.norm hp0 hpt

theorem memLp_hcExtVec_normalized (e : Fin d) (m : ℤ) {G : Vec d → Vec d}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hG : MemLp G p (flatHalfMeasure e m)) :
    MemLp (hcExtVec e G) p (normalizedCubeMeasure (originCube d m)) := by
  rw [memLp_iff, eLpNorm_hcExtVec_normalized e m hG.aestronglyMeasurable hp0 hpt]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
    hG.eLpNorm_lt_top

end SuperdiffusionCLT.Section7
