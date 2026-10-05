/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryG
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryE
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The edge-and-layer term of the boundary Caccioppoli inequality

On the set `B` of small measure left uncovered by the good grid cubes, the pairing
`∫_B (A∇u)·(Φ∇γ - (u - γ)∇Φ)` is bounded by Young's inequality, the pointwise bound of the
datum, and the Sobolev inequality on a small set (`ca2_sob_layer`) for the `H¹₀(D)` functions
`E_i (u - γ)`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_eLpNorm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) : (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have h := lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hf
  rw [← toReal_eLpNorm] at h
  rw [h]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hnn : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

theorem ca2_lipGradient_le {a : ℝ} {Kη : ℝ≥0} (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i))
    (i j : Fin d) (x : Vec d) : |lipGradient (ca1_E a i) x j| ≤ Kη := by
  have h1 : ‖fderiv ℝ (ca1_E a i) x‖ ≤ Kη := norm_fderiv_le_of_lipschitz ℝ (hKη i)
  have h3 : ‖fderiv ℝ (ca1_E a i) x (basisVec j)‖ ≤ Kη := by
    calc ‖fderiv ℝ (ca1_E a i) x (basisVec j)‖ ≤ ‖fderiv ℝ (ca1_E a i) x‖ * ‖basisVec (d := d) j‖ :=
          (fderiv ℝ (ca1_E a i) x).le_opNorm _
      _ ≤ Kη := by rw [ca2_basis_norm, mul_one]; exact h1
  simpa [lipGradient] using h3

theorem ca2_tsupport_E_subset {a : ℝ} (ha : 0 < a) (i : Fin d) :
    tsupport (ca1_E (d := d) a i) ⊆ Metric.closedBall 0 a := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  by_contra hxn
  have h0 : ca1_phi a x = 0 := ca1_phi_eq_zero_of_not_mem ha hxn
  have := ca1_E_abs_le ha i x
  rw [h0, mul_zero] at this
  exact hx (abs_nonpos_iff.1 this)

/-- The `H¹₀(D)` function `E_i (u - γ)` with its gradient. -/
theorem ca2_phi_i {D V : Set (Vec d)} (hD : IsOpen D) (hV : IsOpen V) (u : H1Function D)
    {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn D V (fun x => u.toFun x - γ x)) {a : ℝ} (ha : 0 < a)
    (haV : Metric.closedBall (0 : Vec d) a ⊆ V) (i : Fin d) :
    ∃ φ : H10Function D, (∀ x, φ.toH1Function.toFun x = ca1_E a i x * (u.toFun x - γ x)) ∧
      ∀ᵐ x ∂(volume.restrict D), ∀ j, φ.toH1Function.grad x j =
        ca1_E a i x * (u.grad x j - p12_grad γ x j) +
          (u.toFun x - γ x) * lipGradient (ca1_E a i) x j := by
  obtain ⟨φ, hφf, hφg⟩ := ca2_test_fn hD hV u hγ hZ (ca2_contDiff_E a i)
    (ca1_hasCompactSupport_E ha i) ((ca2_tsupport_E_subset ha i).trans haV)
  refine ⟨φ, hφf, ?_⟩
  filter_upwards [hφg] with x hx j
  rw [hx]
  simp [lipGradient, p12_grad]

theorem ca2_sq3 (p q r : ℝ) : (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
  nlinarith only [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]

/-- The `L²(D)` energy of the coordinate derivatives of `E_i (u - γ)`. -/
theorem ca2_dphi_sq_le [NeZero d] {D : Set (Vec d)} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (u : H1Function D) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {a : ℝ} (ha : 0 < a) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) {G1 : ℝ}
    (hb1 : ∀ x ∈ D, ‖fderiv ℝ γ x‖ ≤ G1) (i j : Fin d) (g : Vec d → ℝ)
    (hg : ∀ᵐ x ∂(volume.restrict D), g x =
        ca1_E a i x * (u.grad x j - p12_grad γ x j) +
          (u.toFun x - γ x) * lipGradient (ca1_E a i) x j) :
    ∫ x in D, g x ^ 2 ≤
      3 * (144 * a⁻¹ ^ 2 * (∫ x in D, ca1_Phi a x * vecNormSq (u.grad x)) +
        144 * a⁻¹ ^ 2 * (G1 ^ 2 * (volume D).toReal) +
        (Kη : ℝ) ^ 2 * ∫ x in D, (u.toFun x - γ x) ^ 2) := by
  classical
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hfin : IsFiniteMeasure (volume.restrict D) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hDb.measure_lt_top⟩
  have hγL : MemLp γ 2 (volume.restrict D) := lip_witness_bdry_memLp_cont hD hDb hγ1.continuous
  have hwL : MemLp (fun x => u.toFun x - γ x) 2 (volume.restrict D) := u.memL2.sub hγL
  have I1 : Integrable (fun x => ca1_Phi a x * vecNormSq (u.grad x)) (volume.restrict D) :=
    ca2_integrable_energy u (ca2_contDiff_Phi a) (ca1_hasCompactSupport_Phi ha)
  have I2 : Integrable (fun _ : Vec d => G1 ^ 2) (volume.restrict D) := integrable_const _
  have I3 : Integrable (fun x => (u.toFun x - γ x) ^ 2) (volume.restrict D) := hwL.integrable_sq
  have hR : Integrable (fun x => 3 * (144 * a⁻¹ ^ 2 * (ca1_Phi a x * vecNormSq (u.grad x)) +
      144 * a⁻¹ ^ 2 * G1 ^ 2 + (Kη : ℝ) ^ 2 * (u.toFun x - γ x) ^ 2)) (volume.restrict D) :=
    ((((I1.const_mul _).add (I2.const_mul _)).add (I3.const_mul _))).const_mul _
  have hmono : ∫ x in D, g x ^ 2 ≤ ∫ x in D, 3 * (144 * a⁻¹ ^ 2 * (ca1_Phi a x * vecNormSq (u.grad x)) +
      144 * a⁻¹ ^ 2 * G1 ^ 2 + (Kη : ℝ) ^ 2 * (u.toFun x - γ x) ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hR ?_
    filter_upwards [hg, ae_restrict_mem hD.measurableSet] with x hx hxD
    rw [hx]
    have hφ0 := ca1_phi_nonneg a x
    have hφ1 := ca1_phi_le_one a x
    have hE : |ca1_E a i x| ≤ 12 * a⁻¹ * ca1_phi a x := ca1_E_abs_le ha i x
    have hu1 : |u.grad x j| ≤ Real.sqrt (vecNormSq (u.grad x)) := abs_le_eucNorm _ _
    have hγj : |p12_grad γ x j| ≤ G1 := (ca2_abs_partial_le x j).trans (hb1 x hxD)
    have hl := ca2_lipGradient_le hKη i j x
    set p : ℝ := 12 * a⁻¹ * ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)) with hp
    set q : ℝ := 12 * a⁻¹ * ca1_phi a x * G1 with hq
    set r : ℝ := Kη * |u.toFun x - γ x| with hr
    have h1 : |ca1_E a i x * (u.grad x j - p12_grad γ x j) +
        (u.toFun x - γ x) * lipGradient (ca1_E a i) x j| ≤ p + q + r := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        have : |u.grad x j - p12_grad γ x j| ≤ Real.sqrt (vecNormSq (u.grad x)) + G1 :=
          (abs_sub _ _).trans (add_le_add hu1 hγj)
        calc |ca1_E a i x| * |u.grad x j - p12_grad γ x j|
            ≤ (12 * a⁻¹ * ca1_phi a x) * (Real.sqrt (vecNormSq (u.grad x)) + G1) :=
              mul_le_mul hE this (abs_nonneg _) (by positivity)
          _ = p + q := by rw [hp, hq]; ring
      · rw [abs_mul]
        calc |u.toFun x - γ x| * |lipGradient (ca1_E a i) x j| ≤ |u.toFun x - γ x| * Kη :=
              mul_le_mul_of_nonneg_left hl (abs_nonneg _)
          _ = r := by rw [hr]; ring
    have h2 : (ca1_E a i x * (u.grad x j - p12_grad γ x j) +
        (u.toFun x - γ x) * lipGradient (ca1_E a i) x j) ^ 2 ≤ (p + q + r) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ((ca2_sq3 p q r).trans ?_)
    have e1 : p ^ 2 = 144 * a⁻¹ ^ 2 * (ca1_Phi a x * vecNormSq (u.grad x)) := by
      rw [hp, mul_pow, Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _),
        ca1_Phi_eq]
      ring
    have e2 : q ^ 2 ≤ 144 * a⁻¹ ^ 2 * G1 ^ 2 := by
      rw [hq]
      have : (ca1_phi a x) ^ 2 ≤ 1 := by nlinarith only [hφ0, hφ1]
      have e : (12 * a⁻¹ * ca1_phi a x * G1) ^ 2 = 144 * a⁻¹ ^ 2 * G1 ^ 2 * (ca1_phi a x) ^ 2 := by ring
      rw [e]
      exact mul_le_of_le_one_right (by positivity) this
    have e3 : r ^ 2 = (Kη : ℝ) ^ 2 * (u.toFun x - γ x) ^ 2 := by
      rw [hr, mul_pow, sq_abs]
    rw [e1, e3]
    nlinarith only [e2]
  refine hmono.trans (le_of_eq ?_)
  have hAB : Integrable (fun x => 144 * a⁻¹ ^ 2 * (ca1_Phi a x * vecNormSq (u.grad x)) +
      144 * a⁻¹ ^ 2 * G1 ^ 2) (volume.restrict D) := (I1.const_mul _).add (I2.const_mul _)
  have hC : Integrable (fun x => (Kη : ℝ) ^ 2 * (u.toFun x - γ x) ^ 2) (volume.restrict D) :=
    I3.const_mul _
  rw [integral_const_mul, integral_add hAB hC, integral_add (I1.const_mul _) (I2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp only [Measure.restrict_apply_univ, smul_eq_mul, Measure.real]
  ring

/-- **The Sobolev bound for `E_i (u - γ)` on a small set `B ⊆ D`.** -/
theorem ca2_phi_B_bound [NeZero d] (hd : 2 ≤ d) {D V : Set (Vec d)} (hD : IsOpen D) (hV : IsOpen V)
    (hDb : Bornology.IsBounded D) (u : H1Function D) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn D V (fun x => u.toFun x - γ x)) {a : ℝ} (ha : 0 < a)
    (haV : Metric.closedBall (0 : Vec d) a ⊆ V) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) {G1 : ℝ}
    (hb1 : ∀ x ∈ D, ‖fderiv ℝ γ x‖ ≤ G1) {B : Set (Vec d)} (hBD : B ⊆ D) (i : Fin d) :
    ∫ x in B, (ca1_E a i x * (u.toFun x - γ x)) ^ 2 ≤
      (ca2_CS d : ℝ) ^ 2 * (d : ℝ) ^ 2 * (((volume B).toReal * (volume D).toReal) ^ (1 / (d : ℝ))) *
        (3 * (144 * a⁻¹ ^ 2 * (∫ x in D, ca1_Phi a x * vecNormSq (u.grad x)) +
          144 * a⁻¹ ^ 2 * (G1 ^ 2 * (volume D).toReal) +
          (Kη : ℝ) ^ 2 * ∫ x in D, (u.toFun x - γ x) ^ 2)) := by
  classical
  obtain ⟨φ, hφf, hφg⟩ := ca2_phi_i hD hV u hγ hZ ha haV i
  have hvD : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hvB : volume B ≠ ⊤ := ((measure_mono hBD).trans_lt hDb.measure_lt_top).ne
  have hS := ca2_sob_layer hd hDb hBD φ
  set θ : ℝ := 1 / (2 * (d : ℝ)) with hθ
  set Θ : ℝ := 3 * (144 * a⁻¹ ^ 2 * (∫ x in D, ca1_Phi a x * vecNormSq (u.grad x)) +
          144 * a⁻¹ ^ 2 * (G1 ^ 2 * (volume D).toReal) +
          (Kη : ℝ) ^ 2 * ∫ x in D, (u.toFun x - γ x) ^ 2) with hΘ
  have hy : ∀ j, ((eLpNorm (fun x => φ.toH1Function.grad x j) 2 (volume.restrict D)).toReal) ^ 2 ≤ Θ := by
    intro j
    rw [ca2_eLpNorm_sq (φ.toH1Function.gradMemL2 j).aestronglyMeasurable]
    exact ca2_dphi_sq_le hD hDb u hγ ha hKη hb1 i j (fun x => φ.toH1Function.grad x j)
      (by filter_upwards [hφg] with x hx; exact hx j)
  have hyfin : ∀ j, eLpNorm (fun x => φ.toH1Function.grad x j) 2 (volume.restrict D) ≠ ⊤ :=
    fun j => (φ.toH1Function.gradMemL2 j).eLpNorm_ne_top
  have hRHS : (ca2_CS d : ℝ≥0∞) * (volume B) ^ θ * (volume D) ^ θ *
      ∑ j : Fin d, eLpNorm (fun x => φ.toH1Function.grad x j) 2 (volume.restrict D) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ?_) ?_) ?_
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hvB
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hvD
    · exact (ENNReal.sum_lt_top.2 fun j _ => (hyfin j).lt_top).ne
  have hT := ENNReal.toReal_mono hRHS hS
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_sum (fun j _ => hyfin j)] at hT
  simp only [ENNReal.coe_toReal] at hT
  set eB := (eLpNorm φ.toH1Function.toFun 2 (volume.restrict B)).toReal with heB
  set vB := (volume B).toReal with hvBdef
  set vD := (volume D).toReal with hvDdef
  set ys : Fin d → ℝ := fun j => (eLpNorm (fun x => φ.toH1Function.grad x j) 2 (volume.restrict D)).toReal
    with hys
  have hys0 : ∀ j, 0 ≤ ys j := fun j => ENNReal.toReal_nonneg
  have hCS0 : 0 ≤ (ca2_CS d : ℝ) := NNReal.coe_nonneg _
  have hsum : (∑ j, ys j) ^ 2 ≤ d * ∑ j, ys j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := ys)
    simpa using this
  have hsum2 : ∑ j, ys j ^ 2 ≤ d * Θ := by
    calc ∑ j, ys j ^ 2 ≤ ∑ _j : Fin d, Θ := Finset.sum_le_sum fun j _ => hy j
      _ = d * Θ := by simp
  have heB0 : 0 ≤ eB := ENNReal.toReal_nonneg
  have hsq : eB ^ 2 ≤ ((ca2_CS d : ℝ) * vB ^ θ * vD ^ θ * ∑ j, ys j) ^ 2 :=
    pow_le_pow_left₀ heB0 hT 2
  have hpow : (vB ^ θ * vD ^ θ) ^ 2 = (vB * vD) ^ (1 / (d : ℝ)) := by
    have hB0 : 0 ≤ vB := ENNReal.toReal_nonneg
    have hD0 : 0 ≤ vD := ENNReal.toReal_nonneg
    rw [← Real.mul_rpow hB0 hD0, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [hθ]
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  have hφB : ∫ x in B, (ca1_E a i x * (u.toFun x - γ x)) ^ 2 = eB ^ 2 := by
    rw [heB, ca2_eLpNorm_sq (φ.toH1Function.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hBD le_rfl))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hφf x]
  rw [hφB]
  refine hsq.trans ?_
  have e : ((ca2_CS d : ℝ) * vB ^ θ * vD ^ θ * ∑ j, ys j) ^ 2 =
      (ca2_CS d : ℝ) ^ 2 * (vB ^ θ * vD ^ θ) ^ 2 * (∑ j, ys j) ^ 2 := by ring
  rw [e, hpow]
  have hbase : 0 ≤ (ca2_CS d : ℝ) ^ 2 * (vB * vD) ^ (1 / (d : ℝ)) := by positivity
  calc (ca2_CS d : ℝ) ^ 2 * (vB * vD) ^ (1 / (d : ℝ)) * (∑ j, ys j) ^ 2
      ≤ (ca2_CS d : ℝ) ^ 2 * (vB * vD) ^ (1 / (d : ℝ)) * (d * (d * Θ)) :=
        mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hsum2 (Nat.cast_nonneg _))) hbase
    _ = _ := by ring

theorem ca2_vecNormSq_eq (v : Vec d) : vecNormSq v = ∑ i, v i ^ 2 := by
  unfold vecNormSq vecDot
  exact Finset.sum_congr rfl fun i _ => (sq (v i)).symm

theorem ca2_vecNormSq_G_le {a : ℝ} (x : Vec d) {γ : Vec d → ℝ} {G1 : ℝ}
    (hb : ‖fderiv ℝ γ x‖ ≤ G1) (w : ℝ) :
    vecNormSq (ca2_G (ca1_Phi a) γ (fun _ => w) x) ≤
      2 * (d * G1 ^ 2) + 2 * ∑ i, (ca1_E a i x * w) ^ 2 := by
  have hΦ0 : 0 ≤ ca1_Phi a x := by rw [ca1_Phi_eq]; exact sq_nonneg _
  have hΦ1 : ca1_Phi a x ≤ 1 := (abs_le.1 (ca1_Phi_abs_le a x)).2
  rw [ca2_vecNormSq_eq]
  have h1 : ∀ i, ca2_G (ca1_Phi a) γ (fun _ => w) x i ^ 2 ≤
      2 * G1 ^ 2 + 2 * (ca1_E a i x * w) ^ 2 := by
    intro i
    have e : ca2_G (ca1_Phi a) γ (fun _ => w) x i = ca1_Phi a x * p12_grad γ x i - ca1_E a i x * w := by
      simp only [ca2_G, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show p12_grad (ca1_Phi (d := d) a) x i = ca1_E a i x from ca1_Phi_fderiv a i x]
      ring
    rw [e]
    have hγi : |p12_grad γ x i| ≤ G1 := (ca2_abs_partial_le x i).trans hb
    have h2 : (ca1_Phi a x * p12_grad γ x i) ^ 2 ≤ G1 ^ 2 := by
      rw [mul_pow]
      have : ca1_Phi a x ^ 2 ≤ 1 := by nlinarith only [hΦ0, hΦ1]
      have h3 : p12_grad γ x i ^ 2 ≤ G1 ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hγi 2
      nlinarith only [this, h3, sq_nonneg (p12_grad γ x i), sq_nonneg (ca1_Phi a x)]
    nlinarith only [h2, sq_nonneg (ca1_Phi a x * p12_grad γ x i + ca1_E a i x * w)]
  calc ∑ i, ca2_G (ca1_Phi a) γ (fun _ => w) x i ^ 2 ≤ ∑ i : Fin d, (2 * G1 ^ 2 + 2 * (ca1_E a i x * w) ^ 2) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = _ := by
        rw [Finset.sum_add_distrib]
        have h2 : ∑ i : Fin d, 2 * (ca1_E a i x * w) ^ 2 = 2 * ∑ i : Fin d, (ca1_E a i x * w) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
        rw [h2]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The edge-and-layer term**: for every `s > 0`,
`|∫_B (A∇u)·G| ≤ Λ ((s/2) ∫_B |∇u|² + s⁻¹ (d G1² |B| + d Ψ))` with the Sobolev quantity `Ψ`. -/
theorem ca2_Bterm [NeZero d] (hd : 2 ≤ d) {D V : Set (Vec d)} (hD : IsOpen D) (hV : IsOpen V)
    (hDb : Bornology.IsBounded D) {A : CoeffField d} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hop : ∀ x ∈ D, ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function D) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn D V (fun x => u.toFun x - γ x)) {a : ℝ} (ha : 0 < a)
    (haV : Metric.closedBall (0 : Vec d) a ⊆ V) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) {G1 : ℝ}
    (hb1 : ∀ x ∈ D, ‖fderiv ℝ γ x‖ ≤ G1) {B : Set (Vec d)} (hBD : B ⊆ D) (hBm : MeasurableSet B)
    {s : ℝ} (hs : 0 < s) :
    |∫ x in B, vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| ≤
      Λ * (s / 2 * (∫ x in B, vecNormSq (u.grad x)) +
        s⁻¹ * (d * G1 ^ 2 * (volume B).toReal +
          d * ((ca2_CS d : ℝ) ^ 2 * (d : ℝ) ^ 2 * (((volume B).toReal * (volume D).toReal) ^ (1 / (d : ℝ))) *
            (3 * (144 * a⁻¹ ^ 2 * (∫ x in D, ca1_Phi a x * vecNormSq (u.grad x)) +
              144 * a⁻¹ ^ 2 * (G1 ^ 2 * (volume D).toReal) +
              (Kη : ℝ) ^ 2 * ∫ x in D, (u.toFun x - γ x) ^ 2))))) := by
  classical
  have hvB : volume B ≠ ⊤ := ((measure_mono hBD).trans_lt hDb.measure_lt_top).ne
  have hfinB : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hvB⟩
  set Ψ : ℝ := (ca2_CS d : ℝ) ^ 2 * (d : ℝ) ^ 2 * (((volume B).toReal * (volume D).toReal) ^ (1 / (d : ℝ))) *
            (3 * (144 * a⁻¹ ^ 2 * (∫ x in D, ca1_Phi a x * vecNormSq (u.grad x)) +
              144 * a⁻¹ ^ 2 * (G1 ^ 2 * (volume D).toReal) +
              (Kη : ℝ) ^ 2 * ∫ x in D, (u.toFun x - γ x) ^ 2)) with hΨ
  have hΛ' := hΛ
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hγL : MemLp γ 2 (volume.restrict D) := lip_witness_bdry_memLp_cont hD hDb hγ1.continuous
  have hwL : MemLp (fun x => u.toFun x - γ x) 2 (volume.restrict D) := u.memL2.sub hγL
  -- integrability on `B`
  have J1 : Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict B) := by
    have h1 : Integrable (fun x => eucNorm (u.grad x) ^ 2) (volume.restrict D) :=
      (memLp_eucNorm_grad u).integrable_sq
    have h2 : (fun x => eucNorm (u.grad x) ^ 2) = fun x => vecNormSq (u.grad x) := by
      funext x
      unfold eucNorm
      exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    rw [h2] at h1
    exact h1.mono_measure (Measure.restrict_mono hBD le_rfl)
  have J2 : ∀ i, Integrable (fun x => (ca1_E a i x * (u.toFun x - γ x)) ^ 2) (volume.restrict B) := by
    intro i
    obtain ⟨φ, hφf, -⟩ := ca2_phi_i hD hV u hγ hZ ha haV i
    have := φ.toH1Function.memL2.integrable_sq
    refine (this.congr (Filter.Eventually.of_forall fun x => ?_)).mono_measure
      (Measure.restrict_mono hBD le_rfl)
    simp only [hφf x]
  have J3 : Integrable (fun _ : Vec d => G1 ^ 2) (volume.restrict B) := integrable_const _
  have hRint : Integrable (fun x => Λ * (s / 2 * vecNormSq (u.grad x) +
      s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2))) (volume.restrict B) := by
    refine Integrable.const_mul ?_ _
    refine (J1.const_mul _).add (Integrable.const_mul ?_ _)
    exact (J3.const_mul _).add (integrable_finsetSum _ fun i _ => J2 i)
  have hpt : ∀ x ∈ D, |vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| ≤
      Λ * (s / 2 * vecNormSq (u.grad x) +
        s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2)) := by
    intro x hxD
    have h1 := ca1_abs_vecDot_le (matVecMul (A x) (u.grad x))
      (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)
    have h2 : eucNorm (matVecMul (A x) (u.grad x)) ≤ Λ * eucNorm (u.grad x) := hop x hxD _
    have hG := ca2_vecNormSq_G_le (a := a) x (γ := γ) (G1 := G1) (hb1 x hxD) (u.toFun x - γ x)
    have hy := ca1_young (r := s) (p := eucNorm (u.grad x))
      (q := eucNorm (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) hs
    have hn : eucNorm (u.grad x) ^ 2 = vecNormSq (u.grad x) := by
      unfold eucNorm
      exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    have hn2 : eucNorm (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) ^ 2 =
        vecNormSq (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) := by
      unfold eucNorm
      exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    rw [hn, hn2] at hy
    have hG' : vecNormSq (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) ≤
        2 * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) := by
      have e2 : 2 * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) =
          2 * (d * G1 ^ 2) + 2 * ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2 := by ring
      rw [e2]
      exact hG
    have h3 : eucNorm (u.grad x) * eucNorm (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) ≤
        s / 2 * vecNormSq (u.grad x) + s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) := by
      have e : vecNormSq (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) / (2 * s) ≤
          s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        have : s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) * (2 * s) =
            2 * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) := by
          rw [show s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) * (2 * s) =
            2 * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) * (s⁻¹ * s) by ring,
            inv_mul_cancel₀ hs.ne', mul_one]
        rw [this]; exact hG'
      linarith only [hy, e]
    calc _ ≤ eucNorm (matVecMul (A x) (u.grad x)) *
          eucNorm (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) := h1
      _ ≤ (Λ * eucNorm (u.grad x)) * eucNorm (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x) :=
          mul_le_mul_of_nonneg_right h2 (ca1_eucNorm_nonneg _)
      _ = Λ * (eucNorm (u.grad x) * eucNorm (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hΛ
  have hmono : |∫ x in B, vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| ≤
      ∫ x in B, Λ * (s / 2 * vecNormSq (u.grad x) +
        s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2)) := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hRint ?_
    filter_upwards [ae_restrict_mem hBm] with x hx
    exact hpt x (hBD hx)
  refine hmono.trans ?_
  have hI1 : Integrable (fun x => s / 2 * vecNormSq (u.grad x)) (volume.restrict B) := J1.const_mul _
  have hI2 : Integrable (fun x => s⁻¹ * (d * G1 ^ 2 + ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2))
      (volume.restrict B) := Integrable.const_mul ((J3.const_mul _).add (integrable_finsetSum _ fun i _ => J2 i)) _
  have hI3 : Integrable (fun x => (d : ℝ) * G1 ^ 2) (volume.restrict B) := integrable_const _
  have hI4 : Integrable (fun x => ∑ i, (ca1_E a i x * (u.toFun x - γ x)) ^ 2) (volume.restrict B) :=
    integrable_finsetSum _ fun i _ => J2 i
  rw [integral_const_mul, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    integral_add hI3 hI4, integral_const, integral_finsetSum _ fun i _ => J2 i]
  simp only [Measure.restrict_apply_univ, smul_eq_mul, Measure.real]
  have hΨi : ∀ i, ∫ x in B, (ca1_E a i x * (u.toFun x - γ x)) ^ 2 ≤ Ψ := fun i =>
    ca2_phi_B_bound hd hD hV hDb u hγ hZ ha haV hKη hb1 hBD i
  have hsum : ∑ i, ∫ x in B, (ca1_E a i x * (u.toFun x - γ x)) ^ 2 ≤ d * Ψ := by
    calc _ ≤ ∑ _i : Fin d, Ψ := Finset.sum_le_sum fun i _ => hΨi i
      _ = d * Ψ := by simp
  refine mul_le_mul_of_nonneg_left ?_ hΛ
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hh : (volume B).toReal * (d * G1 ^ 2) + ∑ i, ∫ x in B, (ca1_E a i x * (u.toFun x - γ x)) ^ 2 ≤
      d * G1 ^ 2 * (volume B).toReal + d * Ψ := by
    have e : (volume B).toReal * (d * G1 ^ 2) = d * G1 ^ 2 * (volume B).toReal := by ring
    linarith only [hsum, e]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hs0)

end SuperdiffusionCLT.Section7
