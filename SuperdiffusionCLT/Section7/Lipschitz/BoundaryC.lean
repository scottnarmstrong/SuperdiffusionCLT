/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InteriorB
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryApprox
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlargeB
public import SuperdiffusionCLT.Section7.Analytic.ElementaryB
public import Homogenization.Sobolev.H1.LocalizedZeroTrace

/-!
# The boundary estimate on the grid: translation and norm helpers

The translation of a localized zero trace, pointwise bounds from essential suprema of continuous
functions on an open set, the derivatives of a translated datum, and the translation of the
oscillation about the average.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- A localized zero trace is transported by a translation of the three sets. -/
theorem lip_fine_loc_translate {Ω V : Set (Vec d)} {w : Vec d → ℝ} (z : Vec d)
    (h : LocalizedZeroTraceFunctionOn Ω V w) :
    LocalizedZeroTraceFunctionOn (translateSet (-z) Ω) (translateSet (-z) V)
      (fun x => w (x + z)) := by
  intro η' hη' hc hsub
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun y => η' (y - z)) :=
    hη'.comp (contDiff_id.sub contDiff_const)
  have hcη : HasCompactSupport (fun y => η' (y - z)) := by
    have := hc.comp_homeomorph (Homeomorph.subRight z)
    exact this
  have hsubη : tsupport (fun y => η' (y - z)) ⊆ V := by
    intro x hx
    have hx' : x - z ∈ tsupport η' := by
      rw [show (fun y => η' (y - z)) = η' ∘ Homeomorph.subRight z by rfl,
        tsupport_comp_eq_preimage η' (Homeomorph.subRight z)] at hx
      exact hx
    have := hsub hx'
    rw [mem_translateSet_iff_sub_mem] at this
    simpa using this
  obtain ⟨φ, hφ⟩ := h _ hη hcη hsubη
  refine ⟨φ.translate (-z), ?_⟩
  funext x
  have h1 : (φ.translate (-z)).toH1Function.toFun x = φ.toH1Function.toFun (x - -z) := by
    rw [H10Function.translate_toH1Function, H1Function.translate_toFun]
  rw [h1, hφ]
  simp [sub_neg_eq_add]

/-- A bound that holds almost everywhere on an open set for a continuous function holds
everywhere on it. -/
theorem lip_fine_le_of_ae_le {Q : Set (Vec d)} (hQ : IsOpen Q) {h : Vec d → ℝ}
    (hc : Continuous h) {G : ℝ} (hae : ∀ᵐ x ∂volume.restrict Q, h x ≤ G) :
    ∀ x ∈ Q, h x ≤ G := by
  intro x hx
  by_contra hcon
  push Not at hcon
  have hopen : IsOpen ({y | G < h y} ∩ Q) := (isOpen_lt continuous_const hc).inter hQ
  have hpos : 0 < volume ({y | G < h y} ∩ Q) := hopen.measure_pos volume ⟨x, hcon, hx⟩
  rw [ae_restrict_iff' hQ.measurableSet] at hae
  have hnull : volume {y | ¬ (y ∈ Q → h y ≤ G)} = 0 := by
    rw [ae_iff] at hae
    exact hae
  have hsub : ({y | G < h y} ∩ Q) ⊆ {y | ¬ (y ∈ Q → h y ≤ G)} := by
    rintro y ⟨hy1, hy2⟩ hy3
    exact absurd (hy3 hy2) (not_le.2 hy1)
  exact absurd (measure_mono_null hsub hnull) hpos.ne'

/-- A finite essential supremum bounds the function almost everywhere. -/
theorem lip_fine_ae_abs_le {μ : Measure (Vec d)} {h : Vec d → ℝ} (htop : eLpNorm h ⊤ μ ≠ ⊤) :
    ∀ᵐ x ∂μ, |h x| ≤ (eLpNorm h ⊤ μ).toReal := by
  have hm : AEStronglyMeasurable h μ := by
    by_contra hn
    exact htop (eLpNorm_of_not_aestronglyMeasurable hn)
  have hF0 : 0 ≤ (eLpNorm h ⊤ μ).toReal := ENNReal.toReal_nonneg
  filter_upwards [enorm_ae_le_eLpNormEssSup h μ] with x hx
  rw [← eLpNorm_exponent_top hm, ← ENNReal.ofReal_toReal htop, ← ofReal_norm,
    ENNReal.ofReal_le_ofReal_iff hF0, Real.norm_eq_abs] at hx
  exact hx

/-- The finiteness of the essential supremum forces measurability. -/
theorem lip_fine_aesm_of_ne_top {μ : Measure (Vec d)} {h : Vec d → ℝ} (htop : eLpNorm h ⊤ μ ≠ ⊤) :
    AEStronglyMeasurable h μ := by
  by_contra hn
  exact htop (eLpNorm_of_not_aestronglyMeasurable hn)

/-- The derivatives of a translated datum. -/
theorem lip_fine_fderiv_translate {g : Vec d → ℝ} (hg : ContDiff ℝ 2 g) (z : Vec d) :
    ContDiff ℝ 2 (fun x => g (x + z)) ∧
      (∀ x, fderiv ℝ (fun x => g (x + z)) x = fderiv ℝ g (x + z)) ∧
      (∀ x, fderiv ℝ (fderiv ℝ (fun x => g (x + z))) x = fderiv ℝ (fderiv ℝ g) (x + z)) := by
  have h1 : ∀ x, fderiv ℝ (fun x => g (x + z)) x = fderiv ℝ g (x + z) := fun x => by
    simpa using fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := x) z
  refine ⟨hg.comp (contDiff_id.add contDiff_const), h1, fun x => ?_⟩
  have e : fderiv ℝ (fun x => g (x + z)) = fun x => fderiv ℝ g (x + z) := funext h1
  rw [e]
  simpa using fderiv_comp_add_right (𝕜 := ℝ) (f := fderiv ℝ g) (x := x) z

/-- The cube about `z` meets `t • U`, seen from `z`. -/
theorem lip_fine_translate_inter (z : Vec d) (j : ℕ) (S : Set (Vec d)) :
    translateSet (-z) (shiftCube z (j : ℤ) ∩ S) =
      shiftCube (0 : Vec d) (j : ℤ) ∩ translateSet (-z) S := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Set.mem_inter_iff, Set.mem_inter_iff,
    mem_translateSet_iff_sub_mem, ← lip_interior_translate_shiftCube z j,
    mem_translateSet_iff_sub_mem]


/-- The oscillation about the average, translated. -/
theorem lip_fine_lpBar_osc (z : Vec d) (S : Set (Vec d)) (hS : MeasurableSet S) (w : Vec d → ℝ) :
    lpBar (translateSet (-z) S) 2 (fun x => w (x + z) - ⨍ y in translateSet (-z) S, w (y + z)) =
      lpBar S 2 (fun x => w x - ⨍ y in S, w y) := by
  rw [lip_interior_average_translate z S hS w]
  exact lpBar_translateSet z S 2 (fun x => w x - ⨍ y in S, w y)

/-- The gradient norm, translated. -/
theorem lip_fine_lpBar_grad (z : Vec d) (S : Set (Vec d)) (F : Vec d → Vec d) :
    lpBar (translateSet (-z) S) 2 (fun x => eucNorm (F (x + z))) =
      lpBar S 2 (fun x => eucNorm (F x)) :=
  lpBar_translateSet z S 2 (fun x => eucNorm (F x))


/-- The `L²` norm of the oscillation, translated. -/
theorem lip_fine_lipL2_osc (z : Vec d) (S : Set (Vec d)) (hS : MeasurableSet S) (w : Vec d → ℝ) :
    lipL2 (translateSet (-z) S) (fun x => w (x + z) - ⨍ y in translateSet (-z) S, w (y + z)) =
      lipL2 S (fun x => w x - ⨍ y in S, w y) := by
  unfold lipL2
  rw [lip_fine_lpBar_osc z S hS w]

/-- The `L²` norm of a difference, translated. -/
theorem lip_fine_lipL2_diff (z : Vec d) (S : Set (Vec d)) (w g : Vec d → ℝ) :
    lipL2 (translateSet (-z) S) (fun x => w (x + z) - g (x + z)) =
      lipL2 S (fun x => w x - g x) := by
  unfold lipL2
  rw [lpBar_translateSet z S 2 (fun x => w x - g x)]

/-- The `L²` norm of the gradient, translated. -/
theorem lip_fine_lipGradL2 (z : Vec d) (S : Set (Vec d)) (F : Vec d → Vec d) :
    lipGradL2 (translateSet (-z) S) (fun x => F (x + z)) = lipGradL2 S F := by
  unfold lipGradL2
  rw [lip_fine_lpBar_grad z S F]


/-- The logarithm is dominated by half the scale. -/
theorem lip_fine_log_le {B x : ℝ} (hB : 0 ≤ B) (hx : 16 * B ^ 2 + 1 ≤ x) :
    B * Real.log x ≤ x / 2 := by
  have hx0 : 0 < x := by nlinarith only [hx, sq_nonneg B]
  have h1 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have h3 : 4 * B ≤ Real.sqrt x := by
    rw [show 4 * B = Real.sqrt ((4 * B) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith only [hx, sq_nonneg B])
  have h4 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  rw [← h2] at h1
  have h5 : Real.log x ≤ 2 * Real.sqrt x := by
    have : Real.sqrt x / (1 / 2) = 2 * Real.sqrt x := by ring
    linarith only [h1, this]
  have h6 : B * Real.log x ≤ B * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left h5 hB
  nlinarith only [h6, h3, h4, Real.sqrt_nonneg x]

/-- The size of the box `n` against the ambient scale. -/
theorem lip_fine_numeric {B E : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E) {A m' m n : ℕ} (hm'm : m' ≤ m)
    (hmA : m ≤ m' + A) (hAm : A ≤ m') (hBm : 16 * B ^ 2 + 1 ≤ (m' : ℝ))
    (hE4 : (4 : ℝ) ^ (E + 1) ≤ (m' : ℝ)) (hwin : (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ)) :
    (n : ℝ) ^ (-(E + 1)) ≤ (m : ℝ) ^ (-E) := by
  have hm'0 : 0 < (m' : ℝ) := by nlinarith only [hBm, sq_nonneg B]
  have hm'm' : (m' : ℝ) ≤ m := by exact_mod_cast hm'm
  have hm0 : 0 < (m : ℝ) := by linarith only [hm'm', hm'0]
  have hlog := lip_fine_log_le hB hBm
  have hm2 : (m : ℝ) ≤ 2 * m' := by
    have : (m : ℝ) ≤ m' + A := by exact_mod_cast hmA
    have h2 : (A : ℝ) ≤ m' := by exact_mod_cast hAm
    linarith only [this, h2]
  have hnq : (m : ℝ) / 4 ≤ n := by linarith only [hwin, hlog, hm2]
  have hE1 : -(E + 1) ≤ 0 := by linarith only [hE]
  have h1 : (n : ℝ) ^ (-(E + 1)) ≤ ((m : ℝ) / 4) ^ (-(E + 1)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnq hE1
  have h2 : ((m : ℝ) / 4) ^ (-(E + 1)) = (m : ℝ) ^ (-(E + 1)) * (4 : ℝ) ^ (E + 1) := by
    rw [Real.div_rpow hm0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      div_inv_eq_mul]
  have h3 : (m : ℝ) ^ (-(E + 1)) = (m : ℝ) ^ (-E) * (m : ℝ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hm0]; ring_nf
  have h4 : (m : ℝ) ^ (-1 : ℝ) * (4 : ℝ) ^ (E + 1) ≤ 1 := by
    rw [Real.rpow_neg_one]
    have : (4 : ℝ) ^ (E + 1) ≤ m := le_trans hE4 hm'm'
    calc (m : ℝ)⁻¹ * (4 : ℝ) ^ (E + 1) ≤ (m : ℝ)⁻¹ * m :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hm0.le)
      _ = 1 := inv_mul_cancel₀ hm0.ne'
  have hmE : 0 ≤ (m : ℝ) ^ (-E) := Real.rpow_nonneg hm0.le _
  calc (n : ℝ) ^ (-(E + 1)) ≤ (m : ℝ) ^ (-(E + 1)) * (4 : ℝ) ^ (E + 1) := h1.trans h2.le
    _ = (m : ℝ) ^ (-E) * ((m : ℝ) ^ (-1 : ℝ) * (4 : ℝ) ^ (E + 1)) := by rw [h3]; ring
    _ ≤ (m : ℝ) ^ (-E) * 1 := mul_le_mul_of_nonneg_left h4 hmE
    _ = (m : ℝ) ^ (-E) := mul_one _

/-- The scale of the coarsest grid, against the bottom scale. -/
theorem lip_fine_nK_le {B : ℝ} (hB : 0 ≤ B) (s : ℕ) {m' n : ℕ} (hn0 : b2c_n0 (B + s) ≤ m')
    (hwin : (m' : ℝ) - B * Real.log (m' : ℝ) ≤ (n : ℝ)) :
    (nK (B + s) m' : ℝ) ≤ (n : ℝ) - s := by
  have hN : 0 ≤ B + (s : ℝ) := by positivity
  have hm := b2c_n0_spec hn0
  have hm4 : (4 : ℝ) ≤ m' := by nlinarith only [hm, hN]
  have hK : (4 * (B + (s : ℝ)) + 2) ^ 2 ≤ (m' : ℝ) := by nlinarith only [hm, hN]
  rw [nK_cast hN hK]
  have hl := a23_one_le_log hm4
  have hc := Nat.le_ceil ((B + (s : ℝ)) * Real.log (m' : ℝ))
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith only [hwin, hl, hc, hs0]

end SuperdiffusionCLT.Section7
