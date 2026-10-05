/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryH

/-!
# The crude Caccioppoli inequality with a boundary datum

The cutoff-weighted energy of a solution with the localized trace of a `C²` datum `γ` is bounded by
`Λ²/ν` times the `L²` norms of `u - γ`, with the pointwise bound `G1` of `∇γ`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_vecDot_split (X : Vec d) (w : ℝ) (Γ N : Vec d) (c : ℝ) :
    vecDot X (c • Γ - w • N) = c * vecDot X Γ - w * vecDot X N := by
  unfold vecDot
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine congrArg₂ _ (Finset.sum_congr rfl fun i _ => by ring) (Finset.sum_congr rfl fun i _ => by ring)

/-- Pointwise bound of the integrand of the energy identity. -/
theorem ca2_pt_crude [NeZero d] {ν Λ a G1 : ℝ} (hν : 0 < ν) (ha : 0 < a) (hΛ : 0 ≤ Λ) (hG1 : 0 ≤ G1)
    (A : Mat d) (v : Vec d) (hop : ∀ v : Vec d, eucNorm (matVecMul A v) ≤ Λ * eucNorm v) (x : Vec d)
    {γ : Vec d → ℝ} (hb : ‖fderiv ℝ γ x‖ ≤ G1) (w : ℝ) :
    vecDot (matVecMul A v) (ca2_G (ca1_Phi a) γ (fun _ => w) x) ≤
      ν / 2 * (ca1_Phi a x * vecNormSq v) + Λ ^ 2 * d * G1 ^ 2 / ν +
        144 * d * Λ ^ 2 * a⁻¹ ^ 2 / ν * w ^ 2 := by
  have hΦ0 : 0 ≤ ca1_Phi a x := by rw [ca1_Phi_eq]; exact sq_nonneg _
  have hφ0 := ca1_phi_nonneg a x
  have hφ1 := ca1_phi_le_one a x
  have hG : ca2_G (ca1_Phi a) γ (fun _ => w) x =
      ca1_Phi a x • p12_grad γ x - w • (fun i => ca1_E a i x) := by
    funext i
    simp only [ca2_G, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show p12_grad (ca1_Phi (d := d) a) x i = ca1_E a i x from ca1_Phi_fderiv a i x]
  rw [hG, ca2_vecDot_split]
  -- the cross term
  have hc := ca1_cross_pointwise (ν := ν / 2) (Λ := Λ) (a := a) (by positivity) ha hΛ A v hop x w
  have hc' : -(w * vecDot (matVecMul A v) (fun i => ca1_E a i x)) ≤
      ν / 2 / 2 * (ca1_Phi a x * vecNormSq v) + (144 * d * Λ ^ 2 * a⁻¹ ^ 2) / (2 * (ν / 2)) * w ^ 2 := by
    have h1 : vecDot (matVecMul A v) (w • fun i => ca1_E a i x) = w * vecDot (matVecMul A v) (fun i => ca1_E a i x) := by
      unfold vecDot
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 := neg_abs_le (vecDot (matVecMul A v) (w • fun i => ca1_E a i x))
    rw [h1] at h2 hc
    linarith only [hc, h2]
  -- the datum term
  have hd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hn : eucNorm v ^ 2 = vecNormSq v := by
    unfold eucNorm
    exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have h4 : ca1_Phi a x * vecDot (matVecMul A v) (p12_grad γ x) ≤
      ν / 2 / 2 * (ca1_Phi a x * vecNormSq v) + Λ ^ 2 * d * G1 ^ 2 / ν := by
    have e1 := ca1_abs_vecDot_le (matVecMul A v) (p12_grad γ x)
    have hv0 := ca1_eucNorm_nonneg v
    have e2 : eucNorm (matVecMul A v) * eucNorm (p12_grad γ x) ≤
        (Λ * eucNorm v) * (Real.sqrt d * G1) :=
      mul_le_mul (hop v) ((ca2_eucNorm_grad_le x).trans (mul_le_mul_of_nonneg_left hb hd0))
        (ca1_eucNorm_nonneg _) (by positivity)
    have hΦφ : ca1_Phi a x ≤ ca1_phi a x := by
      rw [ca1_Phi_eq]; nlinarith only [hφ0, hφ1]
    have e3 : ca1_Phi a x * vecDot (matVecMul A v) (p12_grad γ x) ≤
        ca1_phi a x * eucNorm v * (Λ * Real.sqrt d * G1) := by
      calc ca1_Phi a x * vecDot (matVecMul A v) (p12_grad γ x)
          ≤ ca1_Phi a x * |vecDot (matVecMul A v) (p12_grad γ x)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hΦ0
        _ ≤ ca1_Phi a x * ((Λ * eucNorm v) * (Real.sqrt d * G1)) :=
            mul_le_mul_of_nonneg_left (e1.trans e2) hΦ0
        _ ≤ ca1_phi a x * ((Λ * eucNorm v) * (Real.sqrt d * G1)) :=
            mul_le_mul_of_nonneg_right hΦφ (by have := ca1_eucNorm_nonneg v; positivity)
        _ = _ := by ring
    have hy := ca1_young (r := ν / 2) (p := ca1_phi a x * eucNorm v) (q := Λ * Real.sqrt d * G1) (by positivity)
    have e4 : (ca1_phi a x * eucNorm v) ^ 2 = ca1_Phi a x * vecNormSq v := by
      rw [mul_pow, hn, ← ca1_Phi_eq]
    have e5 : (Λ * Real.sqrt d * G1) ^ 2 = Λ ^ 2 * d * G1 ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    rw [e4, e5] at hy
    have e6 : Λ ^ 2 * d * G1 ^ 2 / (2 * (ν / 2)) = Λ ^ 2 * d * G1 ^ 2 / ν := by field_simp
    rw [e6] at hy
    linarith only [e3, hy]
  have e7 : (144 * d * Λ ^ 2 * a⁻¹ ^ 2) / (2 * (ν / 2)) = 144 * d * Λ ^ 2 * a⁻¹ ^ 2 / ν := by field_simp
  rw [e7] at hc'
  have e8 : ν / 2 / 2 * (ca1_Phi a x * vecNormSq v) + ν / 2 / 2 * (ca1_Phi a x * vecNormSq v) =
      ν / 2 * (ca1_Phi a x * vecNormSq v) := by ring
  linarith only [h4, hc', e8]

/-- **The crude Caccioppoli inequality with a boundary datum.** -/
theorem ca2_crude [NeZero d] {D V : Set (Vec d)} (hD : IsOpen D) (hV : IsOpen V)
    (hDb : Bornology.IsBounded D) {lam Lam ν Λ : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam D A) (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ D, symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ D, ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function D) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict D))
    (hu : IsWeakSolutionOn A D u f (fun _ => 0)) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn D V (fun x => u.toFun x - γ x)) {a : ℝ} (ha : 0 < a)
    (haV : Metric.closedBall (0 : Vec d) a ⊆ V) {G1 : ℝ} (hG1 : 0 ≤ G1)
    (hb1 : ∀ x ∈ D, ‖fderiv ℝ γ x‖ ≤ G1) :
    ν * ∫ x in D, ca1_Phi a x * vecNormSq (u.grad x) ≤
      a ^ 2 / ν * (∫ x in D, f x ^ 2) +
        (ν / a ^ 2 + 288 * d * Λ ^ 2 / (ν * a ^ 2)) * (∫ x in D, (u.toFun x - γ x) ^ 2) +
          2 * (Λ ^ 2 * d * G1 ^ 2 / ν) * (volume D).toReal := by
  classical
  have hDm : MeasurableSet D := hD.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict D) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hDb.measure_lt_top⟩
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hγL : MemLp γ 2 (volume.restrict D) := lip_witness_bdry_memLp_cont hD hDb hγ1.continuous
  have hw : MemLp (fun x => u.toFun x - γ x) 2 (volume.restrict D) := u.memL2.sub hγL
  have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict D) := hf.integrable_sq
  have hw2 : Integrable (fun x => (u.toFun x - γ x) ^ 2) (volume.restrict D) := hw.integrable_sq
  have hΦc := ca1_hasCompactSupport_Phi (d := d) ha
  have hΦ1 := ca2_contDiff_Phi (d := d) a
  have hΦT : tsupport (ca1_Phi (d := d) a) ⊆ V := (ca1_tsupport_Phi_subset ha).trans haV
  have hX := ca2_integrable_energy u hΦ1 hΦc
  have hid := ca2_energy_identity hD hV hEll hsym u hu hγ hZ hΦ1 hΦc hΦT
  set X := ∫ x in D, ca1_Phi a x * vecNormSq (u.grad x) with hXdef
  set F2 := ∫ x in D, f x ^ 2 with hF2
  set W2 := ∫ x in D, (u.toFun x - γ x) ^ 2 with hW2
  set r : ℝ := a ^ 2 / ν with hr
  have hr0 : 0 < r := by positivity
  -- the right-hand-side term
  have hIf : (∫ x in D, f x * (ca1_Phi a x * (u.toFun x - γ x))) ≤ r / 2 * F2 + 1 / (2 * r) * W2 := by
    have hle : ∀ x ∈ D, f x * (ca1_Phi a x * (u.toFun x - γ x)) ≤
        r / 2 * f x ^ 2 + 1 / (2 * r) * (u.toFun x - γ x) ^ 2 := by
      intro x _
      have h1 := ca1_young (r := r) (p := f x) (q := ca1_Phi a x * (u.toFun x - γ x)) hr0
      have hΦ0 : 0 ≤ ca1_Phi a x := by rw [ca1_Phi_eq]; exact sq_nonneg _
      have hΦ1' : ca1_Phi a x ≤ 1 := (abs_le.1 (ca1_Phi_abs_le a x)).2
      have h2 : (ca1_Phi a x * (u.toFun x - γ x)) ^ 2 ≤ (u.toFun x - γ x) ^ 2 := by
        rw [mul_pow]
        have : ca1_Phi a x ^ 2 ≤ 1 := by nlinarith only [hΦ0, hΦ1']
        nlinarith only [this, sq_nonneg (u.toFun x - γ x)]
      have h3 : (ca1_Phi a x * (u.toFun x - γ x)) ^ 2 / (2 * r) ≤ 1 / (2 * r) * (u.toFun x - γ x) ^ 2 := by
        rw [div_eq_mul_inv, mul_comm, one_div]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith only [h1, h3]
    have hint := ca2_integrable_rhs hDb hD u hγ hΦ1 hΦc hf
    have hg : IntegrableOn (fun x => r / 2 * f x ^ 2 + 1 / (2 * r) * (u.toFun x - γ x) ^ 2) D volume :=
      (hf2.const_mul (r / 2)).add (hw2.const_mul (1 / (2 * r)))
    have := setIntegral_mono_on hint hg hDm hle
    rw [integral_add (hf2.const_mul (r / 2)) (hw2.const_mul (1 / (2 * r))), integral_const_mul,
      integral_const_mul] at this
    exact this
  -- the cross term
  have hIG : (∫ x in D, vecDot (matVecMul (A x) (u.grad x))
      (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)) ≤
      ν / 2 * X + Λ ^ 2 * d * G1 ^ 2 / ν * (volume D).toReal + 144 * d * Λ ^ 2 * a⁻¹ ^ 2 / ν * W2 := by
    have hconst : Integrable (fun _ : Vec d => Λ ^ 2 * d * G1 ^ 2 / ν) (volume.restrict D) := integrable_const _
    have hg : IntegrableOn (fun x => ν / 2 * (ca1_Phi a x * vecNormSq (u.grad x)) +
        Λ ^ 2 * d * G1 ^ 2 / ν + 144 * d * Λ ^ 2 * a⁻¹ ^ 2 / ν * (u.toFun x - γ x) ^ 2) D volume :=
      ((hX.const_mul (ν / 2)).add hconst).add (hw2.const_mul _)
    have := setIntegral_mono_on (ca2_integrable_cross hEll u hγ hΦ1 hΦc) hg hDm (fun x hx =>
      ca2_pt_crude hν ha hΛ hG1 (A x) (u.grad x) (hop x hx) x (hb1 x hx) (u.toFun x - γ x))
    have hAB : Integrable (fun x => ν / 2 * (ca1_Phi a x * vecNormSq (u.grad x)) +
        Λ ^ 2 * d * G1 ^ 2 / ν) (volume.restrict D) := (hX.const_mul (ν / 2)).add hconst
    have hC : Integrable (fun x => 144 * d * Λ ^ 2 * a⁻¹ ^ 2 / ν * (u.toFun x - γ x) ^ 2)
        (volume.restrict D) := hw2.const_mul _
    rw [integral_add hAB hC, integral_add (hX.const_mul (ν / 2)) hconst, integral_const_mul,
      integral_const_mul, integral_const] at this
    simp only [Measure.restrict_apply_univ, smul_eq_mul, Measure.real] at this
    linarith only [this]
  have hpos : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  have e1 : 1 / (2 * r) * W2 = ν / (2 * a ^ 2) * W2 := by rw [hr]; field_simp
  have e2 : 144 * d * Λ ^ 2 * a⁻¹ ^ 2 / ν * W2 = 144 * d * Λ ^ 2 / (ν * a ^ 2) * W2 := by
    field_simp
  have e3 : (ν / a ^ 2 + 288 * d * Λ ^ 2 / (ν * a ^ 2)) * W2 =
      2 * (ν / (2 * a ^ 2) * W2) + 2 * (144 * d * Λ ^ 2 / (ν * a ^ 2) * W2) := by
    field_simp; ring
  rw [e1] at hIf
  rw [e2] at hIG
  have e4 : a ^ 2 / ν * F2 = 2 * (r / 2 * F2) := by rw [hr]; ring
  rw [e3, e4]
  have e5 : 2 * (Λ ^ 2 * d * G1 ^ 2 / ν) * (volume D).toReal =
      2 * (Λ ^ 2 * d * G1 ^ 2 / ν * (volume D).toReal) := by ring
  rw [e5]
  linarith only [hid, hIf, hIG]

end SuperdiffusionCLT.Section7
