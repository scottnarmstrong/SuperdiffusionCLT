/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayK
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The slope of an affine function from its size on a cube

An affine function `α + ⟨γ, x - z⟩` which is bounded by `E` (almost everywhere, or in the mean
square) on a cube of side `s` has slope `|γ_i| ≤ 2E / s` (resp. `√32 (s^{-d-2} ∫ g²)^{1/2}`).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_isOpen_axisCube (c : Vec d) (s : ℝ) : IsOpen (axisCube c s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem r3e_measurableSet_axisCube (c : Vec d) (s : ℝ) : MeasurableSet (axisCube c s) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem r3e_continuous_affine (α : ℝ) (γ z : Vec d) :
    Continuous (fun x : Vec d => α + vecDot γ (x - z)) := by
  unfold vecDot
  fun_prop

theorem r3e_pointwise_of_ae {c : Vec d} {s : ℝ} {g : Vec d → ℝ} (hg : Continuous g) {E : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (axisCube c s)), |g x| ≤ E) :
    ∀ x ∈ axisCube c s, |g x| ≤ E := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hxE⟩ := hcon
  have hW : IsOpen (axisCube c s ∩ {y | E < |g y|}) :=
    (r3e_isOpen_axisCube c s).inter (isOpen_lt continuous_const hg.abs)
  have hpos := hW.measure_pos volume ⟨x, hx, hxE⟩
  have hae : ∀ᵐ y ∂(volume : Measure (Vec d)), y ∈ axisCube c s → |g y| ≤ E :=
    (ae_restrict_iff' (r3e_measurableSet_axisCube c s)).1 h
  have h0 : volume {y | ¬ (y ∈ axisCube c s → |g y| ≤ E)} = 0 := ae_iff.1 hae
  refine absurd (measure_mono_null (fun y hy => ?_) h0) hpos.ne'
  exact fun hh => absurd (hh hy.1) (not_le.2 hy.2)

/-- The slope of an affine function bounded by `E` on a cube. -/
theorem r3e_slope_sup {c z γ : Vec d} {α s E : ℝ} (hs : 0 < s)
    (h : ∀ᵐ x ∂(volume.restrict (axisCube c s)), |α + vecDot γ (x - z)| ≤ E) (i : Fin d) :
    |γ i| * s ≤ 2 * E := by
  have hpt := r3e_pointwise_of_ae (r3e_continuous_affine α γ z).abs.abs
    (h.mono fun x hx => by simpa using hx)
  have hpt' : ∀ x ∈ axisCube c s, |α + vecDot γ (x - z)| ≤ E := fun x hx => by
    simpa using hpt x hx
  have hmem : ∀ η : ℝ, 0 < η → η < s / 2 →
      (fun j => c j + η) ∈ axisCube c s ∧
        (fun j => c j + η + (s - 2 * η) * (basisVec i : Vec d) j) ∈ axisCube c s := by
    intro η hη hηs
    constructor
    · intro j _
      simp only [Set.mem_Ioo]
      constructor <;> linarith only [hη, hηs]
    · intro j _
      simp only [Set.mem_Ioo, basisVec, Pi.single_apply]
      by_cases hj : j = i
      · simp only [hj, ite_true]
        constructor <;> linarith only [hη, hηs]
      · simp only [hj, ite_false]
        constructor <;> linarith only [hη, hηs]
  have hE : 0 ≤ E := by
    have := hmem (s / 4) (by positivity) (by linarith only [hs])
    exact (abs_nonneg _).trans (hpt' _ this.1)
  by_contra hlt
  rw [not_le] at hlt
  have ha : 0 < |γ i| := by
    rcases (abs_nonneg (γ i)).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hlt; linarith only [hlt, hE]
    · exact h0
  set a : ℝ := |γ i| with hadef
  set η : ℝ := min (s / 4) ((a * s - 2 * E) / (4 * a)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (div_pos (by linarith only [hlt]) (by positivity))
  have hη1 : η ≤ s / 4 := min_le_left _ _
  have hη2 : η ≤ (a * s - 2 * E) / (4 * a) := min_le_right _ _
  have hη3 : 4 * a * η ≤ a * s - 2 * E := by
    rw [le_div_iff₀ (by positivity)] at hη2
    linarith only [hη2]
  obtain ⟨hlo, hhi⟩ := hmem η hη0 (by linarith only [hη1, hs])
  have hdiff : (α + vecDot γ ((fun j => c j + η + (s - 2 * η) * (basisVec i : Vec d) j) - z)) -
      (α + vecDot γ ((fun j => c j + η) - z)) = (s - 2 * η) * γ i := by
    have : (fun j => c j + η + (s - 2 * η) * (basisVec i : Vec d) j) - z =
        ((fun j => c j + η) - z) + (s - 2 * η) • basisVec i := by
      ext j; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    unfold vecDot at *
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have h2 : ∑ x, γ x * ((s - 2 * η) * (basisVec i : Vec d) x) = (s - 2 * η) * γ i := by
      simp [basisVec, Pi.single_apply, mul_comm]
    rw [h2]
    ring
  have h1 := hpt' _ hlo
  have h2 := hpt' _ hhi
  have h3 : |(s - 2 * η) * γ i| ≤ 2 * E := by
    rw [← hdiff]
    calc _ ≤ |α + vecDot γ ((fun j => c j + η + (s - 2 * η) * (basisVec i : Vec d) j) - z)| +
          |α + vecDot γ ((fun j => c j + η) - z)| := abs_sub _ _
      _ ≤ 2 * E := by linarith only [h1, h2]
  rw [abs_mul, abs_of_pos (by linarith only [hη1, hs] : 0 < s - 2 * η)] at h3
  nlinarith only [h3, hη3, hlt, ha, hη0]

/-- The half cube `{x ∈ □(c, s) | x_i < c_i + s/2}`. -/
def r3e_halfBox (c : Vec d) (s : ℝ) (i : Fin d) : Set (Vec d) :=
  Set.pi Set.univ fun j => Set.Ioo (c j) (c j + if j = i then s / 2 else s)

theorem r3e_halfBox_subset (c : Vec d) {s : ℝ} (hs : 0 < s) (i : Fin d) :
    r3e_halfBox c s i ⊆ axisCube c s := by
  intro x hx j hj
  have h := hx j hj
  simp only [Set.mem_Ioo] at h ⊢
  refine ⟨h.1, lt_of_lt_of_le h.2 ?_⟩
  by_cases hji : j = i
  · simp only [hji, ite_true]; linarith only [hs]
  · simp only [hji, ite_false]; exact le_rfl

theorem r3e_halfBox_shift (c : Vec d) {s : ℝ} (i : Fin d) {x : Vec d}
    (hx : x ∈ r3e_halfBox c s i) : x + (s / 2) • basisVec i ∈ axisCube c s := by
  intro j hj
  have h := hx j hj
  simp only [Set.mem_Ioo, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec, Pi.single_apply] at h ⊢
  by_cases hji : j = i
  · simp only [hji, ite_true, mul_one] at h ⊢
    constructor <;> linarith only [h.1, h.2]
  · simp only [hji, ite_false, mul_zero, add_zero] at h ⊢
    exact h

theorem r3e_volume_halfBox (c : Vec d) {s : ℝ} (hs : 0 < s) (i : Fin d) :
    (volume (r3e_halfBox c s i)).toReal = s ^ d / 2 := by
  have hle : c ≤ fun j => c j + if j = i then s / 2 else s := fun j => by
    simp only [le_add_iff_nonneg_right]
    split_ifs <;> linarith only [hs]
  have h : (volume (r3e_halfBox c s i)).toReal =
      ∏ j : Fin d, (s * if j = i then (1 / 2 : ℝ) else 1) := by
    rw [r3e_halfBox, Real.volume_pi_Ioo_toReal hle]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · simp only [hji, ite_true]; ring
    · simp only [hji, ite_false]; ring
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp
  ring

theorem r3e_integrableOn_axisCube {c : Vec d} {s : ℝ} {h : Vec d → ℝ} (hh : Continuous h)
    {S : Set (Vec d)} (hS : S ⊆ axisCube c s) : IntegrableOn h S := by
  have hsub : axisCube c s ⊆ Set.Icc c (fun j => c j + s) := fun x hx =>
    ⟨fun j => (hx j (Set.mem_univ j)).1.le, fun j => (hx j (Set.mem_univ j)).2.le⟩
  exact (hh.integrableOn_Icc).mono_set (hS.trans hsub)

/-- The slope of an affine function in the mean square over a cube. -/
theorem r3e_slope_L2 {c z γ : Vec d} {α s : ℝ} (hs : 0 < s) (i : Fin d) :
    |γ i| ^ 2 * s ^ (d + 2) ≤ 32 * (∫ x in axisCube c s, (α + vecDot γ (x - z)) ^ 2) := by
  set g : Vec d → ℝ := fun x => α + vecDot γ (x - z) with hg
  have hgc : Continuous g := r3e_continuous_affine α γ z
  set F : Set (Vec d) := axisCube c s with hF
  set H : Set (Vec d) := r3e_halfBox c s i with hH
  set t : Vec d := (s / 2) • basisVec i with ht
  have hHm : MeasurableSet H := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hHF : H ⊆ F := r3e_halfBox_subset c hs i
  have hshift : ∀ x, g (x + t) - g x = (s / 2) * γ i := by
    intro x
    simp only [hg, add_sub_add_left_eq_sub]
    have : x + t - z = (x - z) + t := by abel
    rw [this]
    unfold vecDot
    simp only [Pi.add_apply, ht, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have h2 : ∑ x, γ x * ((s / 2) * (basisVec i : Vec d) x) = (s / 2) * γ i := by
      simp [basisVec, Pi.single_apply, mul_comm]
    rw [h2]
    ring
  have hg2 : Continuous fun x => g x ^ 2 := hgc.pow 2
  have hg2s : Continuous fun x => g (x + t) ^ 2 := (hgc.comp (continuous_id.add continuous_const)).pow 2
  have hI1 : IntegrableOn (fun x => g x ^ 2) F := r3e_integrableOn_axisCube hg2 le_rfl
  have hI2 : IntegrableOn (fun x => g x ^ 2) H := r3e_integrableOn_axisCube hg2 hHF
  have hI3 : IntegrableOn (fun x => g (x + t) ^ 2) H := r3e_integrableOn_axisCube hg2s hHF
  have hshiftInt : ∫ x in H, g (x + t) ^ 2 ≤ ∫ x in F, g x ^ 2 := by
    have hmp : MeasurePreserving (fun x : Vec d => x + t) volume volume :=
      measurePreserving_add_right volume t
    have hemb : MeasurableEmbedding (fun x : Vec d => x + t) := measurableEmbedding_addRight t
    have h1 := hmp.setIntegral_preimage_emb hemb (fun y => g y ^ 2) F
    have hHsub : H ⊆ (fun x : Vec d => x + t) ⁻¹' F := fun x hx =>
      r3e_halfBox_shift c i hx
    have hI4 : IntegrableOn (fun x => g (x + t) ^ 2) ((fun x : Vec d => x + t) ⁻¹' F) := by
      have hsubI : (fun x : Vec d => x + t) ⁻¹' F ⊆ Set.Icc (c - t) (fun j => c j - t j + s) :=
        fun x hx => ⟨fun j => by
          have := (hx j (Set.mem_univ j)).1
          simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
          linarith only [this.le], fun j => by
          have := (hx j (Set.mem_univ j)).2
          simp only [Pi.add_apply] at this
          linarith only [this.le]⟩
      exact hg2s.integrableOn_Icc.mono_set hsubI
    rw [← h1]
    exact setIntegral_mono_set hI4 (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall hHsub)
  have hplain : ∫ x in H, g x ^ 2 ≤ ∫ x in F, g x ^ 2 :=
    setIntegral_mono_set hI1 (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall hHF)
  have hpt : ∀ x ∈ H, ((s / 2) * γ i) ^ 2 ≤ 2 * g (x + t) ^ 2 + 2 * g x ^ 2 := by
    intro x _
    have := hshift x
    rw [← this]
    nlinarith only [sq_nonneg (g (x + t) + g x)]
  have hvol : volume H ≠ ⊤ := by
    intro htop
    have := r3e_volume_halfBox c hs i
    rw [← hH, htop, ENNReal.toReal_top] at this
    have hp : 0 < s ^ d / 2 := by positivity
    linarith only [this, hp]
  have hint : ∫ x in H, ((s / 2) * γ i) ^ 2 ≤
      ∫ x in H, (2 * g (x + t) ^ 2 + 2 * g x ^ 2) :=
    setIntegral_mono_on (integrableOn_const hvol) ((hI3.const_mul 2).add (hI2.const_mul 2)) hHm hpt
  have hconst : ∫ x in H, ((s / 2) * γ i) ^ 2 = ((s / 2) * γ i) ^ 2 * (s ^ d / 2) := by
    rw [setIntegral_const, measureReal_def, r3e_volume_halfBox c hs i, smul_eq_mul, mul_comm]
  have hsplit : ∫ x in H, (2 * g (x + t) ^ 2 + 2 * g x ^ 2) =
      2 * (∫ x in H, g (x + t) ^ 2) + 2 * (∫ x in H, g x ^ 2) := by
    have h1 := integral_add (hI3.const_mul 2) (hI2.const_mul 2)
    rw [integral_const_mul, integral_const_mul] at h1
    exact h1
  have hpow : |γ i| ^ 2 * s ^ (d + 2) = 8 * (((s / 2) * γ i) ^ 2 * (s ^ d / 2)) := by
    rw [sq_abs]; ring
  rw [hpow, ← hconst]
  linarith only [hint, hsplit, hshiftInt, hplain]

end SuperdiffusionCLT.Section7
