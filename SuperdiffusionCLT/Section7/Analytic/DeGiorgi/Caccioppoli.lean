/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.CaccioppoliB
public import Homogenization.Sobolev.MatchedPair.Core
public import Homogenization.CoarseGraining.CoarseBounds.AeBridge

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem levelTest_eq {U : Set (Vec d)} (u : H1Function U) (k : ℝ) (η : Vec d → ℝ) (W : Vec d)
    (x : Vec d) (hW : W = {y | k < u.toFun y}.indicator u.grad x) :
    levelTest u k η x = η x ^ 2 • W + (2 * max (u.toFun x - k) 0 * η x) • cutoffGrad η x := by
  unfold levelTest
  by_cases h : k < u.toFun x
  · have hx : x ∈ {y | k < u.toFun y} := h
    rw [Set.indicator_of_mem hx] at hW ⊢
    rw [hW]
  · have hx : x ∉ {y | k < u.toFun y} := h
    have hm : max (u.toFun x - k) 0 = 0 := max_eq_right (by linarith only [not_lt.mp h])
    rw [Set.indicator_of_notMem hx] at hW ⊢
    rw [hW, hm]
    simp

theorem cutoffGrad_continuous {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d) :
    Continuous (fun x => cutoffGrad η x i) :=
  (hη.continuous_fderiv (by simp)).clm_apply continuous_const

theorem caccioppoli_truncation {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (axisCube z L) a)
    (u : H1Function (axisCube z L)) (k : ℝ) (f : Vec d → ℝ) (g : Vec d → Vec d) {Fb Gb : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (axisCube z L)))
    (hgm : AEStronglyMeasurable g (volume.restrict (axisCube z L)))
    (hf : ∀ᵐ x ∂(volume.restrict (axisCube z L)), |f x| ≤ Fb)
    (hg : ∀ᵐ x ∂(volume.restrict (axisCube z L)), eucNorm (g x) ≤ Gb)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηsupp : tsupport η ⊆ axisCube z L)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ}
    (hG : ∀ x, eucNorm (cutoffGrad η x) ≤ G)
    (hlevel : ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
      (∫ x in axisCube z L, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
        ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x)) :
    ∫ x in axisCube z L, η x ^ 2 * vecNormSq ({y | k < u.toFun y}.indicator u.grad x) ≤
      (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * G ^ 2 *
          (∫ x in axisCube z L, max (u.toFun x - k) 0 ^ 2) +
        (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) *
          (volume ({x | k < u.toFun x} ∩ tsupport η)).toReal) := by
  have hQo : IsOpen (axisCube z L) := isOpen_axisCube z L
  have hQm : MeasurableSet (axisCube z L) := hQo.measurableSet
  have hconv := isOpenBoundedConvexDomain_axisCube z L
  have : IsFiniteMeasure (volume.restrict (axisCube z L)) := hconv.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hRHS : 0 ≤ (8 * (d : ℝ) ^ 2 + 4) * ((Lam / lam) ^ 2 * G ^ 2 *
          (∫ x in axisCube z L, max (u.toFun x - k) 0 ^ 2) +
        (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) *
          (volume ({x | k < u.toFun x} ∩ tsupport η)).toReal) := by
    have : 0 ≤ ∫ x in axisCube z L, max (u.toFun x - k) 0 ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    positivity
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have : IsEmpty (Fin d) := by rw [hd]; infer_instance
    have h0 : ∀ x, η x ^ 2 * vecNormSq ({y | k < u.toFun y}.indicator u.grad x) = 0 := by
      intro x; simp [vecNormSq, vecDot]
    exact le_of_eq_of_le (integral_eq_zero_of_ae (Filter.Eventually.of_forall h0)) hRHS
  by_cases hQne : (axisCube z L).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hQne
    have hμ0 : volume.restrict (axisCube z L) = 0 := by rw [hQne]; exact Measure.restrict_empty
    simp only [hμ0, integral_zero_measure]
    positivity
  obtain ⟨x0, hx0⟩ := hQne
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 x0 hx0
  set μ : Measure (Vec d) := volume.restrict (axisCube z L) with hμ
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => a x i j) μ := by
    intro i j
    have hm : Measurable (fun x => if x ∈ axisCube z L then a x i j else 0) := by
      have := hEll.1
      exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    simp [hx]
  have hAb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ Lam := by
    filter_upwards [ae_restrict_mem hQm] with x hx i j
    exact abs_apply_le_of_isEllipticFieldOn hEll hx i j
  obtain ⟨w', hw'f, hw'g⟩ := exists_h1_max_sub_const hconv u k
  set w : Vec d → ℝ := fun x => max (u.toFun x - k) 0 with hw
  have hwL2 : MemLp w 2 μ := by rw [← hw'f]; exact w'.memL2
  set W : Vec d → Vec d := w'.grad with hWdef
  have hWi : ∀ i, MemLp (fun x => W x i) 2 μ := w'.gradMemL2
  have hNc := cutoffGrad_continuous hη
  have hNb : ∀ i x, |cutoffGrad η x i| ≤ G := fun i x =>
    (abs_apply_le_eucNorm _ i).trans (hG x)
  have hηc : Continuous η := hη.continuous
  have hηb : ∀ x, |η x| ≤ 1 := fun x => by rw [abs_of_nonneg (hη0 x)]; exact hη1 x
  have hη2b : ∀ x, |η x ^ 2| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (hη0 x) (hη1 x)
  set T : Vec d → Vec d := fun x => η x ^ 2 • W x + (2 * w x * η x) • cutoffGrad η x with hT
  have hTi : ∀ i, MemLp (fun x => T x i) 2 μ := by
    intro i
    have h1 := memLp_two_mul_bdd (μ := μ) (φ := fun x => η x ^ 2) (C := 1)
      (hηc.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall hη2b) (hWi i)
    have h2 := memLp_two_mul_bdd (μ := μ) (φ := fun x => cutoffGrad η x i) (C := G)
      (hNc i).aestronglyMeasurable (Filter.Eventually.of_forall fun x => hNb i x) hwL2
    have h3 := memLp_two_mul_bdd (μ := μ) (φ := fun x => 2 * η x) (C := 2)
      ((continuous_const.mul hηc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [abs_mul, abs_of_nonneg (hη0 x)]
        have := hη1 x
        simp only [abs_two]; linarith only [this]) h2
    refine (h1.add h3).ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp only [hT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgi : ∀ i, MemLp (fun x => g x i) 2 μ := fun i =>
    MemLp.of_bound ((continuous_apply i).comp_aestronglyMeasurable hgm) Gb
      (hg.mono fun x hx => by
        rw [Real.norm_eq_abs]; exact (abs_apply_le_eucNorm (g x) i).trans hx)
  have I1 : Integrable (fun x => vecDot (matVecMul (a x) (W x)) (T x)) μ :=
    caccioppoli_integrable_vecDot_of_memLp (memLp_matVecMul hAm hAb hWi) hTi
  have I2 : Integrable (fun x => f x * (η x ^ 2 * w x)) μ :=
    (memLp_two_mul_bdd hfm hf (memLp_two_mul_bdd (hηc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall hη2b) hwL2)).integrable one_le_two
  have I3 : Integrable (fun x => vecDot (g x) (T x)) μ := caccioppoli_integrable_vecDot_of_memLp hgi hTi
  have I4 : Integrable (fun x => η x ^ 2 * vecNormSq (W x)) μ := by
    have hc : ∀ i, MemLp (fun x => (η x • W x) i) 2 μ := fun i => by
      simpa using memLp_two_mul_bdd hηc.aestronglyMeasurable
        (Filter.Eventually.of_forall hηb) (hWi i)
    refine (caccioppoli_integrable_vecDot_of_memLp (F := fun x => η x • W x) (G := fun x => η x • W x)
      hc hc).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot_smul_left, vecDot_smul_right, vecNormSq]
    ring
  have hu_m : AEStronglyMeasurable u.toFun μ := u.memL2.aestronglyMeasurable
  have hũ : Measurable (hu_m.mk u.toFun) := hu_m.stronglyMeasurable_mk.measurable
  have hũae : ∀ᵐ x ∂μ, u.toFun x = hu_m.mk u.toFun x := hu_m.ae_eq_mk
  set S : Set (Vec d) := {x | k < hu_m.mk u.toFun x} ∩ tsupport η with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const hũ).inter (isClosed_tsupport η).measurableSet
  set s : Vec d → ℝ := S.indicator (fun _ => (1 : ℝ)) with hsdef
  have I5 : Integrable (fun x => w x ^ 2) μ := hwL2.integrable_sq
  have I6 : Integrable s μ := (integrable_const (1 : ℝ)).indicator hSm
  set Cw : ℝ := 4 * (d * Lam) ^ 2 * G ^ 2 / lam + 3 / 2 * lam * G ^ 2 with hCw
  set Cs : ℝ := L ^ 2 * Fb ^ 2 / (2 * lam) + 2 * Gb ^ 2 / lam with hCs
  have hpt : ∀ᵐ x ∂μ, lam / 2 * (η x ^ 2 * vecNormSq (W x)) ≤
      (vecDot (matVecMul (a x) (W x)) (T x) - f x * (η x ^ 2 * w x) - vecDot (g x) (T x)) +
        (Cw * w x ^ 2 + Cs * s x) := by
    filter_upwards [ae_restrict_mem hQm, hf, hg, hũae, hw'g] with x hxQ hfx hgx hux hWx
    have hηG : η x ≤ G * L := (le_abs_self _).trans (abs_cutoff_le hd hη hηsupp hG hxQ)
    have hs : η x ≠ 0 → ¬(w x = 0 ∧ W x = 0) → s x = 1 := by
      intro hη' hz
      have hk : k < u.toFun x := by
        by_contra h
        apply hz
        have h' : u.toFun x ≤ k := not_lt.mp h
        refine ⟨max_eq_right (by linarith only [h']), ?_⟩
        rw [hWx, Set.indicator_of_notMem (show x ∉ {y | k < u.toFun y} from h)]
      have hxS : x ∈ S := ⟨by simp only [Set.mem_ofPred_eq]; rw [← hux]; exact hk,
        subset_tsupport η (Function.mem_support.2 hη')⟩
      simp [hsdef, Set.indicator_of_mem hxS]
    exact pointwise_caccioppoli (G := G) (L := L) (Fb := Fb) (Gb := Gb) (hEll.2 x hxQ)
      (fun i j => abs_apply_le_of_isEllipticFieldOn hEll hxQ i j) (W x) (cutoffGrad η x) (g x)
      (f x) (w x) (η x) (s x) (le_max_right _ _) (hη0 x) (hη1 x) hηG (hG x) hfx hgx
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _) hs
  have hLT : ∀ᵐ x ∂μ, levelTest u k η x = T x := by
    filter_upwards [hw'g] with x hWx
    exact levelTest_eq u k η (W x) x hWx
  have hlev2 : ∫ x, vecDot (matVecMul (a x) (W x)) (T x) ∂μ =
      ∫ x, f x * (η x ^ 2 * w x) ∂μ + ∫ x, vecDot (g x) (T x) ∂μ := by
    have e1 : ∫ x, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) ∂μ =
        ∫ x, vecDot (matVecMul (a x) (W x)) (T x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hLT, hw'g] with x h1 hWx
      rw [h1]
      by_cases hk : k < u.toFun x
      · have : W x = u.grad x := by
          rw [hWx, Set.indicator_of_mem (show x ∈ {y | k < u.toFun y} from hk)]
        rw [this]
      · have hW0 : W x = 0 := by
          rw [hWx, Set.indicator_of_notMem (show x ∉ {y | k < u.toFun y} from hk)]
        have hw0 : w x = 0 := max_eq_right (by linarith only [not_lt.mp hk])
        simp [hT, hW0, hw0, vecDot]
    have e2 : ∫ x, vecDot (g x) (levelTest u k η x) ∂μ = ∫ x, vecDot (g x) (T x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hLT] with x h1
      rw [h1]
    rw [← e1, ← e2]
    exact hlevel
  have I12 : Integrable (fun x => vecDot (matVecMul (a x) (W x)) (T x) -
      f x * (η x ^ 2 * w x)) μ := I1.sub I2
  have I123 : Integrable (fun x => vecDot (matVecMul (a x) (W x)) (T x) -
      f x * (η x ^ 2 * w x) - vecDot (g x) (T x)) μ := I12.sub I3
  have I56 : Integrable (fun x => Cw * w x ^ 2 + Cs * s x) μ :=
    (I5.const_mul Cw).add (I6.const_mul Cs)
  have Isum : Integrable (fun x => (vecDot (matVecMul (a x) (W x)) (T x) -
      f x * (η x ^ 2 * w x) - vecDot (g x) (T x)) + (Cw * w x ^ 2 + Cs * s x)) μ :=
    I123.add I56
  have hH : ∫ x, (vecDot (matVecMul (a x) (W x)) (T x) - f x * (η x ^ 2 * w x) -
      vecDot (g x) (T x)) ∂μ = 0 := by
    rw [integral_sub I12 I3, integral_sub I1 I2]
    linarith only [hlev2]
  have hsint : ∫ x, s x ∂μ = (μ S).toReal := by
    rw [hsdef]
    exact integral_indicator_one hSm
  have hR : ∫ x, (Cw * w x ^ 2 + Cs * s x) ∂μ = Cw * ∫ x, w x ^ 2 ∂μ + Cs * (μ S).toReal := by
    rw [integral_add (I5.const_mul _) (I6.const_mul _), integral_const_mul, integral_const_mul,
      hsint]
  have hJ : lam / 2 * ∫ x, η x ^ 2 * vecNormSq (W x) ∂μ ≤
      Cw * ∫ x, w x ^ 2 ∂μ + Cs * (μ S).toReal := by
    have := integral_mono_ae (I4.const_mul (lam / 2))
      Isum hpt
    rw [integral_const_mul, integral_add I123 I56, hH,
      integral_add (I5.const_mul _) (I6.const_mul _), integral_const_mul, integral_const_mul,
      hsint] at this
    linarith only [this]
  have hLHS : ∫ x in axisCube z L, η x ^ 2 * vecNormSq ({y | k < u.toFun y}.indicator u.grad x) =
      ∫ x, η x ^ 2 * vecNormSq (W x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hw'g] with x hWx
    rw [hWx]
  have hmeas : (μ S).toReal =
      (volume ({x | k < u.toFun x} ∩ tsupport η)).toReal := by
    have hsub : {x | k < u.toFun x} ∩ tsupport η ⊆ axisCube z L :=
      Set.inter_subset_right.trans hηsupp
    have h1 : μ S = μ ({x | k < u.toFun x} ∩ tsupport η) := by
      refine measure_congr ?_
      filter_upwards [hũae] with x hx
      simp only [hS, Set.mem_inter_iff, Set.mem_ofPred_eq, hx]
    have h2 : μ ({x | k < u.toFun x} ∩ tsupport η) =
        volume ({x | k < u.toFun x} ∩ tsupport η) := by
      rw [hμ, Measure.restrict_apply' hQm, Set.inter_eq_left.2 hsub]
    rw [h1, h2]
  have hIw : 0 ≤ ∫ x, w x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hm0 : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  have ha : 1 ≤ Lam / lam := (one_le_div hlam).2 hlamLam
  have hc1 : 2 / lam * Cw ≤ (8 * (d : ℝ) ^ 2 + 4) * ((Lam / lam) ^ 2 * G ^ 2) := by
    have e : 2 / lam * Cw = 8 * (d : ℝ) ^ 2 * ((Lam / lam) ^ 2 * G ^ 2) + 3 * G ^ 2 := by
      rw [hCw]; field_simp; ring
    have h : G ^ 2 ≤ (Lam / lam) ^ 2 * G ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg G) (one_le_pow₀ ha)
    linarith only [e, h, sq_nonneg G]
  have hc2 : 2 / lam * Cs ≤ (8 * (d : ℝ) ^ 2 + 4) * ((1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2)) := by
    have e : 2 / lam * Cs = (1 / lam) ^ 2 * (L ^ 2 * Fb ^ 2 + 4 * Gb ^ 2) := by
      rw [hCs]; field_simp; ring
    have e' : (8 * (d : ℝ) ^ 2 + 4) * ((1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2)) -
        (1 / lam) ^ 2 * (L ^ 2 * Fb ^ 2 + 4 * Gb ^ 2) =
        (1 / lam) ^ 2 * (8 * (d : ℝ) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) + 3 * (L ^ 2 * Fb ^ 2)) := by
      ring
    have : 0 ≤ (1 / lam) ^ 2 *
        (8 * (d : ℝ) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) + 3 * (L ^ 2 * Fb ^ 2)) := by positivity
    linarith only [e, e', this]
  rw [hLHS]
  have hJ2 : ∫ x, η x ^ 2 * vecNormSq (W x) ∂μ ≤
      2 / lam * (Cw * ∫ x, w x ^ 2 ∂μ + Cs * (μ S).toReal) := by
    have := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 2 / lam)
    have e : 2 / lam * (lam / 2 * ∫ x, η x ^ 2 * vecNormSq (W x) ∂μ) =
        ∫ x, η x ^ 2 * vecNormSq (W x) ∂μ := by field_simp
    linarith only [this, e]
  have h3 := mul_le_mul_of_nonneg_right hc1 hIw
  have h4 := mul_le_mul_of_nonneg_right hc2 hm0
  rw [hmeas] at hJ2
  rw [hmeas] at h4
  have e5 : 2 / lam * (Cw * ∫ x, w x ^ 2 ∂μ + Cs * (volume ({x | k < u.toFun x} ∩ tsupport η)).toReal) =
      2 / lam * Cw * ∫ x, w x ^ 2 ∂μ + 2 / lam * Cs * (volume ({x | k < u.toFun x} ∩ tsupport η)).toReal := by
    ring
  linarith only [hJ2, e5, h3, h4]

/-- The level inequality: an `H¹` weak solution tested with `(u - k)₊ η²`, for a smooth cutoff `η`
with compact support in the cube. -/
theorem level_inequality_of_isWeakSolutionOn {a : CoeffField d} (z : Vec d) {L : ℝ}
    (u : H1Function (axisCube z L)) (f : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : IsWeakSolutionOn a (axisCube z L) u f g) (k : ℝ) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηsupp : tsupport η ⊆ axisCube z L) :
    ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
      (∫ x in axisCube z L, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
        ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x) := by
  classical
  have hQo : IsOpen (axisCube z L) := isOpen_axisCube z L
  have hconv := isOpenBoundedConvexDomain_axisCube z L
  obtain ⟨w', hw'f, hw'g⟩ := exists_h1_max_sub_const hconv u k
  have hη2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * η x) := hη.mul hη
  have hc2 : HasCompactSupport (fun x => η x * η x) := hηc.mul_right
  set φ1 : H1Function (axisCube z L) := w'.mulContDiffHasCompactSupport hη2 hc2 with hφ1
  have hφ1f : φ1.toFun = fun x => η x * η x * w'.toFun x := by
    rw [hφ1]; exact H1Function.mulContDiffHasCompactSupport_toFun w' hη2 hc2
  have hφ1g : φ1.grad = fun x i => η x * η x * w'.grad x i +
      w'.toFun x * (fderiv ℝ (fun x => η x * η x) x) (basisVec i) := by
    rw [hφ1]; exact H1Function.mulContDiffHasCompactSupport_grad w' hη2 hc2
  have hmem : MemH10 (axisCube z L) φ1.toFun := by
    refine memH10_of_compactSupport hconv φ1 (K := tsupport η) hηc hηsupp ?_
    intro x hx
    rw [hφ1f]
    simp [image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨φ, hφ⟩ := hmem
  have hweak := hu φ
  have hgrad : ∀ᵐ x ∂(volume.restrict (axisCube z L)),
      φ.toH1Function.grad x = levelTest u k η x := by
    have hall : ∀ᵐ x ∂(volume.restrict (axisCube z L)), ∀ i,
        φ.toH1Function.grad x i = φ1.grad x i :=
      ae_all_iff.2 fun i => gradCoord_ae_eq_of_toFun_eq hQo φ.toH1Function φ1 hφ i
    filter_upwards [hall, hw'g] with x hx hWx
    funext i
    rw [hx i, hφ1g]
    dsimp only
    have hd : (fderiv ℝ (fun x => η x * η x) x) (basisVec i) =
        2 * η x * cutoffGrad η x i := by
      have h1 : HasFDerivAt (fun x => η x * η x)
          (η x • fderiv ℝ η x + η x • fderiv ℝ η x) x :=
        ((hη.differentiable (by simp)) x).hasFDerivAt.mul
          ((hη.differentiable (by simp)) x).hasFDerivAt
      rw [h1.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul,
        cutoffGrad]
      ring
    rw [hd]
    unfold levelTest
    by_cases hk : k < u.toFun x
    · have hx' : x ∈ {y | k < u.toFun y} := hk
      have hw : w'.toFun x = max (u.toFun x - k) 0 := by rw [hw'f]
      rw [hWx, Set.indicator_of_mem hx'] at *
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hx', hw]
      ring
    · have hx' : x ∉ {y | k < u.toFun y} := hk
      have hw : w'.toFun x = 0 := by
        rw [hw'f]; exact max_eq_right (by linarith only [not_lt.mp hk])
      have hm : max (u.toFun x - k) 0 = 0 := max_eq_right (by linarith only [not_lt.mp hk])
      rw [Set.indicator_of_notMem hx'] at hWx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hx', hw, hm,
        hWx]
      simp
  have hφf : φ.toH1Function.toFun = fun x => η x ^ 2 * max (u.toFun x - k) 0 := by
    rw [hφ, hφ1f, hw'f]
    funext x
    ring
  have e1 : ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) =
      ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  have e2 : ∫ x in axisCube z L, vecDot (g x) (φ.toH1Function.grad x) =
      ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x) := by
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]
  rw [← e1, ← e2, hweak]
  simp only [hφf]

/-- Witness: identity coefficients on the unit square, the zero solution, zero data and the zero
cutoff meet all hypotheses of `caccioppoli_truncation`; the level inequality is the one derived
from the weak form. -/
example : True := by
  have hQm : MeasurableSet (axisCube (0 : Vec 2) 1) := (isOpen_axisCube _ _).measurableSet
  have hEll : IsEllipticFieldOn (1 : ℝ) 1 (axisCube (0 : Vec 2) 1) (fun _ => (1 : Mat 2)) :=
    ⟨measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
        Measurable.ite hQm measurable_const measurable_const,
      fun _ _ => Homogenization.isEllipticMatrix_one_one le_rfl⟩
  have hu : IsWeakSolutionOn (fun _ => (1 : Mat 2)) (axisCube (0 : Vec 2) 1)
      (0 : H1Function (axisCube (0 : Vec 2) 1)) (fun _ => 0) (fun _ => 0) := by
    intro φ
    simp [vecDot, matVecMul]
  have hlev := level_inequality_of_isWeakSolutionOn (a := fun _ => (1 : Mat 2)) (0 : Vec 2)
    (L := 1) (0 : H1Function (axisCube (0 : Vec 2) 1)) (fun _ => 0) (fun _ => 0) hu 0
    (η := fun _ => 0) contDiff_const (by simp [HasCompactSupport, tsupport]) (by simp [tsupport])
  have := caccioppoli_truncation (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) (0 : Vec 2)
    (L := 1) hEll (0 : H1Function (axisCube (0 : Vec 2) 1)) 0 (fun _ => 0) (fun _ => 0)
    (Fb := 0) (Gb := 0) aestronglyMeasurable_const aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => by simp) (Filter.Eventually.of_forall fun _ => by simp [eucNorm, vecNormSq, vecDot])
    (η := fun _ => 0) contDiff_const (by simp [tsupport]) (fun _ => le_rfl) (fun _ => zero_le_one)
    (G := 0) (fun x => by simp [cutoffGrad, eucNorm, vecNormSq, vecDot]) hlev
  trivial

end SuperdiffusionCLT.Section7
