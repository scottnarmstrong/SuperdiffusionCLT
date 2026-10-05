/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB
public import Homogenization.Geometry.TriadicCubeTranslation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A polynomial cutoff on a cube, with Harnack inequality (interior Caccioppoli, step 2)

For the weak-norm test of the superdiffusive Caccioppoli inequality the
cutoff has to satisfy the Harnack inequality `sup_{z+□_n} φ ≤ C inf_{z+□_n} φ` on every grid cube
whose triple lies in `{φ > 0}`.  A flat `C^∞` cutoff cannot, so we use the explicit profile
`g(t) = (1 - t²)₊³` and `φ_a(x) = ∏ g(x_k / a)`.  The weight `Φ_a = φ_a²` is `C¹` with compact
support in the cube of half-side `a`, and its partial derivatives have the closed form
`E_a i = a⁻¹ G'(x_i / a) ∏_{k ≠ i} G(x_k / a)` with `G = g²`.

## Main results

* `Section7.ca1_Phi_fderiv`: the partial derivatives of `Φ_a`.
* `Section7.ca1_lipschitz`: `Φ_a` and `E_a i` are Lipschitz with constants `K a⁻¹`, `K a⁻²`.
* `Section7.ca1_E_abs_le`: `|E_a i| ≤ 12 a⁻¹ φ_a`.
* `Section7.ca1_E_layer`: near the edge of the cube `|E_a i|` is tiny (fifth power of the distance).
* `Section7.ca1_phi_harnack`, `Section7.ca1_phi_lower`: Harnack inequality and lower bound.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

/-- The truncated power `y ↦ (max y 0)^k`. -/
noncomputable def ca1_pp (k : ℕ) (y : ℝ) : ℝ := (max y 0) ^ k

theorem ca1_pp_nonneg (k : ℕ) (y : ℝ) : 0 ≤ ca1_pp k y := pow_nonneg (le_max_right _ _) _

theorem ca1_pp_of_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : ca1_pp k y = y ^ k := by
  simp [ca1_pp, max_eq_left hy]

theorem ca1_pp_of_nonpos (k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : y ≤ 0) : ca1_pp k y = 0 := by
  simp [ca1_pp, max_eq_right hy, zero_pow (by omega : k ≠ 0)]

/-- For `k ≥ 2` the truncated power is differentiable with derivative `k (max y 0)^{k-1}`. -/
theorem ca1_pp_hasDerivAt (k : ℕ) (hk : 2 ≤ k) (y : ℝ) :
    HasDerivAt (ca1_pp k) ((k : ℝ) * ca1_pp (k - 1) y) y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have : ca1_pp k =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact ca1_pp_of_nonpos k (by omega) (le_of_lt hz)
    rw [ca1_pp_of_nonpos (k - 1) (by omega) hy.le, mul_zero]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq this
  · subst hy
    rw [ca1_pp_of_nonpos (k - 1) (by omega) le_rfl, mul_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, smul_eq_mul, mul_zero, sub_zero]
    have hbound : ∀ h : ℝ, |ca1_pp k h - ca1_pp k 0| ≤ |h| ^ k := by
      intro h
      rw [ca1_pp_of_nonpos k (by omega) le_rfl, sub_zero, abs_of_nonneg (ca1_pp_nonneg k h)]
      unfold ca1_pp
      rcases le_total h 0 with h0 | h0
      · rw [max_eq_right h0]; simp [zero_pow (by omega : k ≠ 0)]
      · rw [max_eq_left h0, abs_of_nonneg h0]
    have hO : (fun h : ℝ => ca1_pp k h - ca1_pp k 0) =O[𝓝 0] fun h : ℝ => h ^ k := by
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow]
      exact hbound h
    exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by omega))
  · have : ca1_pp k =ᶠ[𝓝 y] fun z => z ^ k := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact ca1_pp_of_nonneg k (le_of_lt hz)
    rw [ca1_pp_of_nonneg (k - 1) hy.le]
    exact (hasDerivAt_pow k y).congr_of_eventuallyEq this


theorem ca1_pp_continuous (k : ℕ) : Continuous (ca1_pp k) := by
  unfold ca1_pp; fun_prop

theorem ca1_pp_contDiff (k : ℕ) (hk : 2 ≤ k) : ContDiff ℝ 1 (ca1_pp k) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun y => (ca1_pp_hasDerivAt k hk y).differentiableAt, ?_⟩
  have : deriv (ca1_pp k) = fun y => (k : ℝ) * ca1_pp (k - 1) y :=
    funext fun y => (ca1_pp_hasDerivAt k hk y).deriv
  rw [this]
  exact continuous_const.mul (ca1_pp_continuous _)

/-- The one-dimensional profile `g(t) = (1 - t²)₊³`. -/
noncomputable def ca1_g (t : ℝ) : ℝ := ca1_pp 3 (1 - t ^ 2)
/-- Its square `G(t) = (1 - t²)₊⁶`. -/
noncomputable def ca1_G (t : ℝ) : ℝ := ca1_pp 6 (1 - t ^ 2)
/-- The derivative of `G`. -/
noncomputable def ca1_dG (t : ℝ) : ℝ := -12 * t * ca1_pp 5 (1 - t ^ 2)

theorem ca1_g_nonneg (t : ℝ) : 0 ≤ ca1_g t := ca1_pp_nonneg _ _

theorem ca1_G_eq (t : ℝ) : ca1_G t = ca1_g t ^ 2 := by
  unfold ca1_G ca1_g ca1_pp
  rw [← pow_mul]

theorem ca1_g_le_one (t : ℝ) : ca1_g t ≤ 1 := by
  unfold ca1_g ca1_pp
  refine pow_le_one₀ (le_max_right _ _) ?_
  exact max_le (by nlinarith only [sq_nonneg t]) zero_le_one

theorem ca1_g_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : ca1_g t = 0 := by
  unfold ca1_g
  refine ca1_pp_of_nonpos 3 (by omega) ?_
  have : 1 ≤ t ^ 2 := by
    have := sq_abs t
    nlinarith only [ht, this]
  linarith only [this]

theorem ca1_G_hasDerivAt (t : ℝ) : HasDerivAt ca1_G (ca1_dG t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 1)
  have h2 := (ca1_pp_hasDerivAt 6 (by norm_num) (1 - t ^ 2)).comp t h1
  rw [show ca1_G = ca1_pp 6 ∘ (fun t : ℝ => 1 - t ^ 2) from rfl]
  refine h2.congr_deriv ?_
  simp only [ca1_dG]
  norm_num
  ring

theorem ca1_G_contDiff : ContDiff ℝ 1 ca1_G := by
  unfold ca1_G
  exact (ca1_pp_contDiff 6 (by norm_num)).comp (by fun_prop)

theorem ca1_dG_contDiff : ContDiff ℝ 1 ca1_dG := by
  unfold ca1_dG
  exact (contDiff_const.mul contDiff_id).mul ((ca1_pp_contDiff 5 (by norm_num)).comp (by fun_prop))

theorem ca1_dG_abs_le (t : ℝ) : |ca1_dG t| ≤ 12 * ca1_g t := by
  by_cases ht : |t| < 1
  · have hy : 0 < 1 - t ^ 2 := by
      have := sq_abs t
      nlinarith only [ht, this, abs_nonneg t]
    have hy1 : 1 - t ^ 2 ≤ 1 := by nlinarith only [sq_nonneg t]
    unfold ca1_dG ca1_g
    rw [ca1_pp_of_nonneg _ hy.le, ca1_pp_of_nonneg _ hy.le]
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hy.le _)]
    have h1 : |t| * (1 - t ^ 2) ^ 2 ≤ 1 := by
      have : (1 - t ^ 2) ^ 2 ≤ 1 := by nlinarith only [hy, hy1]
      calc |t| * (1 - t ^ 2) ^ 2 ≤ 1 * 1 :=
          mul_le_mul ht.le this (by positivity) zero_le_one
        _ = 1 := by norm_num
    have : (1 - t ^ 2) ^ 5 = (1 - t ^ 2) ^ 3 * (1 - t ^ 2) ^ 2 := by ring
    rw [this]
    have h3 : 0 ≤ (1 - t ^ 2) ^ 3 := pow_nonneg hy.le _
    norm_num [abs_neg]
    nlinarith only [h1, h3, abs_nonneg t]
  · rw [not_lt] at ht
    have h0 : ca1_dG t = 0 := by
      unfold ca1_dG
      rw [ca1_pp_of_nonpos 5 (by omega), mul_zero]
      have := sq_abs t
      nlinarith only [ht, this]
    rw [h0, abs_zero]
    exact mul_nonneg (by norm_num) (ca1_g_nonneg t)


variable {d : ℕ}

/-- The cutoff weight `Φ₁ = ∏ G(x_k)`, the square of `φ₁`. -/
noncomputable def ca1_Phi1 (x : Vec d) : ℝ := ∏ k, ca1_G (x k)
/-- The cutoff `φ₁ = ∏ g(x_k)`. -/
noncomputable def ca1_phi1 (x : Vec d) : ℝ := ∏ k, ca1_g (x k)
/-- The `i`-th partial derivative of `Φ₁`. -/
noncomputable def ca1_E1 (i : Fin d) (x : Vec d) : ℝ :=
  ca1_dG (x i) * ∏ k ∈ Finset.univ.erase i, ca1_G (x k)

theorem ca1_Phi1_eq (x : Vec d) : ca1_Phi1 x = ca1_phi1 x ^ 2 := by
  unfold ca1_Phi1 ca1_phi1
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun k _ => ca1_G_eq _

theorem ca1_phi1_nonneg (x : Vec d) : 0 ≤ ca1_phi1 x :=
  Finset.prod_nonneg fun _ _ => ca1_g_nonneg _

theorem ca1_phi1_le_one (x : Vec d) : ca1_phi1 x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => ca1_g_nonneg _) fun _ _ => ca1_g_le_one _

theorem ca1_Phi1_contDiff : ContDiff ℝ 1 (ca1_Phi1 (d := d)) := by
  unfold ca1_Phi1
  exact contDiff_prod fun _ _ => ca1_G_contDiff.comp (contDiff_apply ℝ ℝ _)

theorem ca1_E1_contDiff (i : Fin d) : ContDiff ℝ 1 (ca1_E1 i) := by
  unfold ca1_E1
  refine (ca1_dG_contDiff.comp (contDiff_apply ℝ ℝ i)).mul ?_
  exact contDiff_prod fun _ _ => ca1_G_contDiff.comp (contDiff_apply ℝ ℝ _)

theorem ca1_Phi1_fderiv (i : Fin d) (x : Vec d) :
    fderiv ℝ ca1_Phi1 x (basisVec i) = ca1_E1 i x := by
  have hF : HasFDerivAt (ca1_Phi1 (d := d)) (fderiv ℝ ca1_Phi1 x) x :=
    ((ca1_Phi1_contDiff (d := d)).differentiable (by simp) x).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => x + t • basisVec i) (basisVec i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i)).const_add x
  have h1 := hF.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have h2 : HasDerivAt (fun t : ℝ => ca1_Phi1 (x + t • basisVec i)) (ca1_E1 i x) 0 := by
    have e : (fun t : ℝ => ca1_Phi1 (x + t • basisVec i)) =
        fun t : ℝ => ca1_G (x i + t) * ∏ k ∈ Finset.univ.erase i, ca1_G (x k) := by
      funext t
      unfold ca1_Phi1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      · simp [basisVec]
      · refine Finset.prod_congr rfl fun k hk => ?_
        have : k ≠ i := Finset.ne_of_mem_erase hk
        simp [basisVec, this]
    rw [e]
    have h3 := (HasDerivAt.comp_const_add (x i) (0 : ℝ) (ca1_G_hasDerivAt (x i + 0))).mul_const
      (∏ k ∈ Finset.univ.erase i, ca1_G (x k))
    simpa [ca1_E1] using h3
  exact h1.unique h2


theorem ca1_G_le_g (t : ℝ) : ca1_G t ≤ ca1_g t := by
  rw [ca1_G_eq]
  have h0 := ca1_g_nonneg t
  have h1 := ca1_g_le_one t
  nlinarith only [h0, h1]

theorem ca1_G_nonneg (t : ℝ) : 0 ≤ ca1_G t := ca1_pp_nonneg _ _

theorem ca1_E1_abs_le (i : Fin d) (x : Vec d) : |ca1_E1 i x| ≤ 12 * ca1_phi1 x := by
  unfold ca1_E1 ca1_phi1
  rw [abs_mul, ← Finset.mul_prod_erase Finset.univ (fun k => ca1_g (x k)) (Finset.mem_univ i),
    abs_of_nonneg (Finset.prod_nonneg fun k _ => ca1_G_nonneg _)]
  have h1 := ca1_dG_abs_le (x i)
  have h2 : ∏ k ∈ Finset.univ.erase i, ca1_G (x k) ≤ ∏ k ∈ Finset.univ.erase i, ca1_g (x k) :=
    Finset.prod_le_prod₀ (fun k _ => ca1_G_nonneg _) fun k _ => ca1_G_le_g _
  have h3 : 0 ≤ ∏ k ∈ Finset.univ.erase i, ca1_G (x k) :=
    Finset.prod_nonneg fun k _ => ca1_G_nonneg _
  calc |ca1_dG (x i)| * ∏ k ∈ Finset.univ.erase i, ca1_G (x k)
      ≤ (12 * ca1_g (x i)) * ∏ k ∈ Finset.univ.erase i, ca1_g (x k) :=
        mul_le_mul h1 h2 h3 (by have := ca1_g_nonneg (x i); positivity)
    _ = 12 * (ca1_g (x i) * ∏ k ∈ Finset.univ.erase i, ca1_g (x k)) := by ring

theorem ca1_phi1_eq_zero {x : Vec d} {k : Fin d} (hk : 1 ≤ |x k|) : ca1_phi1 x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ k) (ca1_g_eq_zero hk)

/-- One-dimensional layer smallness. -/
theorem ca1_layer_1d {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 1 - δ ≤ |t|) :
    ca1_G t ≤ (2 * δ) ^ 6 ∧ |ca1_dG t| ≤ 12 * (2 * δ) ^ 5 := by
  by_cases h1 : 1 ≤ |t|
  · have : ca1_g t = 0 := ca1_g_eq_zero h1
    refine ⟨?_, ?_⟩
    · have h0 : ca1_G t = 0 := by rw [ca1_G_eq, this]; norm_num
      rw [h0]; positivity
    · have := ca1_dG_abs_le t
      rw [‹ca1_g t = 0›, mul_zero] at this
      exact this.trans (by positivity)
  · rw [not_le] at h1
    have hy : 0 ≤ 1 - t ^ 2 := by
      have := sq_abs t
      nlinarith only [h1, this, abs_nonneg t]
    have hy2 : 1 - t ^ 2 ≤ 2 * δ := by
      have := sq_abs t
      nlinarith only [h1, this, abs_nonneg t, ht, hδ]
    refine ⟨?_, ?_⟩
    · unfold ca1_G
      rw [ca1_pp_of_nonneg _ hy]
      exact pow_le_pow_left₀ hy hy2 6
    · unfold ca1_dG
      rw [ca1_pp_of_nonneg _ hy, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hy _)]
      have h5 : (1 - t ^ 2) ^ 5 ≤ (2 * δ) ^ 5 := pow_le_pow_left₀ hy hy2 5
      have : |t| ≤ 1 := h1.le
      norm_num [abs_neg]
      calc 12 * |t| * (1 - t ^ 2) ^ 5 ≤ 12 * 1 * (2 * δ) ^ 5 :=
            mul_le_mul (by nlinarith only [this, abs_nonneg t]) h5 (pow_nonneg hy _) (by norm_num)
        _ = 12 * (2 * δ) ^ 5 := by ring

theorem ca1_E1_layer {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : 2 * δ ≤ 1) (i : Fin d) {x : Vec d} {j : Fin d}
    (hj : 1 - δ ≤ |x j|) : |ca1_E1 i x| ≤ 12 * (2 * δ) ^ 5 := by
  have hG1 : ∀ k, ca1_G (x k) ≤ 1 := fun k => (ca1_G_le_g _).trans (ca1_g_le_one _)
  have h2δ : 0 ≤ 2 * δ := by linarith only [hδ]
  unfold ca1_E1
  rw [abs_mul]
  by_cases hji : j = i
  · subst hji
    have h1 := (ca1_layer_1d hδ hj).2
    have h2 : ∏ k ∈ Finset.univ.erase j, ca1_G (x k) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => ca1_G_nonneg _) fun k _ => hG1 k
    rw [abs_of_nonneg (Finset.prod_nonneg fun k _ => ca1_G_nonneg _)]
    calc |ca1_dG (x j)| * ∏ k ∈ Finset.univ.erase j, ca1_G (x k)
        ≤ (12 * (2 * δ) ^ 5) * 1 :=
          mul_le_mul h1 h2 (Finset.prod_nonneg fun k _ => ca1_G_nonneg _) (by positivity)
      _ = 12 * (2 * δ) ^ 5 := by ring
  · have h1 : |ca1_dG (x i)| ≤ 12 := by
      have := ca1_dG_abs_le (x i)
      linarith only [this, ca1_g_le_one (x i)]
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩
    have h2 : ∏ k ∈ Finset.univ.erase i, ca1_G (x k) ≤ (2 * δ) ^ 5 := by
      rw [← Finset.mul_prod_erase _ _ hmem]
      have hr : ∏ k ∈ (Finset.univ.erase i).erase j, ca1_G (x k) ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => ca1_G_nonneg _) fun k _ => hG1 k
      have hr0 : 0 ≤ ∏ k ∈ (Finset.univ.erase i).erase j, ca1_G (x k) :=
        Finset.prod_nonneg fun _ _ => ca1_G_nonneg _
      have hj6 := (ca1_layer_1d hδ hj).1
      have hj5 : (2 * δ) ^ 6 ≤ (2 * δ) ^ 5 := by
        have : (2 * δ) ^ 6 = (2 * δ) ^ 5 * (2 * δ) := by ring
        rw [this]
        nlinarith only [pow_nonneg h2δ 5, hδ2]
      calc ca1_G (x j) * ∏ k ∈ (Finset.univ.erase i).erase j, ca1_G (x k) ≤ (2 * δ) ^ 6 * 1 :=
            mul_le_mul hj6 hr hr0 (by positivity)
        _ ≤ (2 * δ) ^ 5 := by linarith only [hj5]
    rw [abs_of_nonneg (Finset.prod_nonneg fun k _ => ca1_G_nonneg _)]
    calc |ca1_dG (x i)| * ∏ k ∈ Finset.univ.erase i, ca1_G (x k) ≤ 12 * (2 * δ) ^ 5 :=
          mul_le_mul h1 h2 (Finset.prod_nonneg fun k _ => ca1_G_nonneg _) (by norm_num)


/-- Harnack inequality for the one-dimensional profile. -/
theorem ca1_g_harnack {h t t' : ℝ} (hh : 0 ≤ h) (ht : |t| + h ≤ 1) (htt : |t' - t| ≤ h) :
    ca1_g t' ≤ 64 * ca1_g t := by
  have ht' : |t'| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub t' t
    linarith only [this, htt, ht]
  have h1 : 1 - |t'| ≤ 2 * (1 - |t|) := by
    have := abs_sub_abs_le_abs_sub t t'
    rw [abs_sub_comm] at this
    linarith only [this, htt, ht]
  have hy : 0 ≤ 1 - t' ^ 2 := by
    have := sq_abs t'
    nlinarith only [ht', this, abs_nonneg t']
  have hy0 : 0 ≤ 1 - t ^ 2 := by
    have e := sq_abs t
    have : |t| ≤ 1 := by linarith only [ht, hh]
    nlinarith only [this, e, abs_nonneg t]
  have hy' : 1 - t' ^ 2 ≤ 4 * (1 - t ^ 2) := by
    have e1 : 1 - t' ^ 2 = (1 - |t'|) * (1 + |t'|) := by rw [← sq_abs t']; ring
    have e2 : 1 - t ^ 2 = (1 - |t|) * (1 + |t|) := by rw [← sq_abs t]; ring
    rw [e1, e2]
    have ha : 0 ≤ 1 - |t|  := by linarith only [ht, hh, abs_nonneg t]
    nlinarith only [h1, ht', abs_nonneg t', abs_nonneg t, ha, mul_nonneg ha (abs_nonneg t)]
  unfold ca1_g
  rw [ca1_pp_of_nonneg _ hy, ca1_pp_of_nonneg _ hy0]
  calc (1 - t' ^ 2) ^ 3 ≤ (4 * (1 - t ^ 2)) ^ 3 := pow_le_pow_left₀ hy hy' 3
    _ = 64 * (1 - t ^ 2) ^ 3 := by ring

theorem ca1_phi1_harnack {h : ℝ} (hh : 0 ≤ h) {x y : Vec d} (hx : ∀ k, |x k| + h ≤ 1)
    (hxy : ∀ k, |y k - x k| ≤ h) : ca1_phi1 y ≤ 64 ^ d * ca1_phi1 x := by
  unfold ca1_phi1
  calc ∏ k, ca1_g (y k) ≤ ∏ k : Fin d, (64 * ca1_g (x k)) :=
        Finset.prod_le_prod₀ (fun _ _ => ca1_g_nonneg _) fun k _ => ca1_g_harnack hh (hx k) (hxy k)
    _ = 64 ^ d * ∏ k, ca1_g (x k) := by
        rw [Finset.prod_mul_distrib]; simp

theorem ca1_phi1_lower {x : Vec d} (hx : ∀ k, |x k| ≤ 2 / 3) :
    (125 / 729 : ℝ) ^ d ≤ ca1_phi1 x := by
  unfold ca1_phi1
  calc (125 / 729 : ℝ) ^ d = ∏ _k : Fin d, (125 / 729 : ℝ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ k, ca1_g (x k) := by
        refine Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun k _ => ?_
        have h1 : x k ^ 2 ≤ 4 / 9 := by
          have := sq_abs (x k)
          nlinarith only [hx k, this, abs_nonneg (x k)]
        have h2 : (5 / 9 : ℝ) ≤ 1 - x k ^ 2 := by linarith only [h1]
        unfold ca1_g
        rw [ca1_pp_of_nonneg _ (by linarith only [h2])]
        calc (125 / 729 : ℝ) = (5 / 9) ^ 3 := by norm_num
          _ ≤ (1 - x k ^ 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3

theorem ca1_phi1_eq_zero_of_not_mem {x : Vec d} (hx : x ∉ Metric.closedBall (0 : Vec d) 1) :
    ca1_phi1 x = 0 := by
  by_contra hne
  apply hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  rw [Real.norm_eq_abs]
  by_contra hk
  exact hne (ca1_phi1_eq_zero (le_of_lt (not_le.1 hk)))

theorem ca1_support_Phi1 : Function.support (ca1_Phi1 (d := d)) ⊆ Metric.closedBall 0 1 := by
  intro x hx
  by_contra hn
  apply hx
  rw [ca1_Phi1_eq, ca1_phi1_eq_zero_of_not_mem hn]
  norm_num

theorem ca1_support_E1 (i : Fin d) : Function.support (ca1_E1 i) ⊆ Metric.closedBall 0 1 := by
  intro x hx
  by_contra hn
  apply hx
  have := ca1_E1_abs_le i x
  rw [ca1_phi1_eq_zero_of_not_mem hn, mul_zero] at this
  exact abs_nonpos_iff.1 this

theorem ca1_hasCompactSupport_Phi1 : HasCompactSupport (ca1_Phi1 (d := d)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) ca1_support_Phi1

theorem ca1_hasCompactSupport_E1 (i : Fin d) : HasCompactSupport (ca1_E1 i) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (ca1_support_E1 i)

theorem ca1_lipschitz1 : ∃ K : ℝ≥0, LipschitzWith K (ca1_Phi1 (d := d)) ∧
    ∀ i : Fin d, LipschitzWith K (ca1_E1 i) := by
  obtain ⟨K0, hK0⟩ := ca1_Phi1_contDiff.lipschitzWith_of_hasCompactSupport ca1_hasCompactSupport_Phi1
    (by simp)
  choose Ki hKi using fun i : Fin d => (ca1_E1_contDiff i).lipschitzWith_of_hasCompactSupport
    (ca1_hasCompactSupport_E1 i) (by simp)
  refine ⟨K0 + ∑ i, Ki i, hK0.weaken (by simp), fun i => (hKi i).weaken ?_⟩
  have := Finset.single_le_sum (f := Ki) (fun _ _ => zero_le) (Finset.mem_univ i)
  exact le_add_left this


/-- The cutoff weight `Φ_a(x) = Φ₁(x/a)` on the cube of half-side `a`. -/
noncomputable def ca1_Phi (a : ℝ) (x : Vec d) : ℝ := ca1_Phi1 (a⁻¹ • x)
/-- The cutoff `φ_a(x) = φ₁(x/a)`. -/
noncomputable def ca1_phi (a : ℝ) (x : Vec d) : ℝ := ca1_phi1 (a⁻¹ • x)
/-- The `i`-th partial derivative of `Φ_a`. -/
noncomputable def ca1_E (a : ℝ) (i : Fin d) (x : Vec d) : ℝ := a⁻¹ * ca1_E1 i (a⁻¹ • x)

theorem ca1_Phi_eq (a : ℝ) (x : Vec d) : ca1_Phi a x = ca1_phi a x ^ 2 := ca1_Phi1_eq _

theorem ca1_phi_nonneg (a : ℝ) (x : Vec d) : 0 ≤ ca1_phi a x := ca1_phi1_nonneg _

theorem ca1_phi_le_one (a : ℝ) (x : Vec d) : ca1_phi a x ≤ 1 := ca1_phi1_le_one _

theorem ca1_Phi_fderiv (a : ℝ) (i : Fin d) (x : Vec d) :
    fderiv ℝ (ca1_Phi a) x (basisVec i) = ca1_E a i x := by
  have hF : HasFDerivAt (ca1_Phi1 (d := d)) (fderiv ℝ ca1_Phi1 (a⁻¹ • x)) (a⁻¹ • x) :=
    ((ca1_Phi1_contDiff (d := d)).differentiable (by simp) _).hasFDerivAt
  have hg : HasFDerivAt (fun y : Vec d => a⁻¹ • y) (a⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).const_smul a⁻¹
  have h := hF.comp x hg
  unfold ca1_Phi
  rw [show (ca1_Phi1 ∘ fun y : Vec d => a⁻¹ • y) = fun y => ca1_Phi1 (a⁻¹ • y) from rfl] at h
  rw [h.fderiv]
  simp [ca1_E, ca1_Phi1_fderiv]

theorem ca1_lipschitz : ∃ K : ℝ≥0, ∀ a : ℝ, 0 < a → LipschitzWith (K * Real.toNNReal a⁻¹) (ca1_Phi (d := d) a) ∧
    ∀ i : Fin d, LipschitzWith (K * Real.toNNReal a⁻¹ ^ 2) (ca1_E a i) := by
  obtain ⟨K, hK1, hK2⟩ := ca1_lipschitz1 (d := d)
  refine ⟨K, fun a ha => ⟨?_, fun i => ?_⟩⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := (hK1.dist_le_mul (a⁻¹ • x) (a⁻¹ • y))
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)] at h
    unfold ca1_Phi
    push_cast
    rw [Real.coe_toNNReal _ (inv_pos.2 ha).le]
    calc _ ≤ _ := h
      _ = _ := by ring
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := ((hK2 i).dist_le_mul (a⁻¹ • x) (a⁻¹ • y))
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)] at h
    unfold ca1_E
    push_cast
    rw [Real.coe_toNNReal _ (inv_pos.2 ha).le, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.2 ha)]
    rw [Real.dist_eq] at h
    calc a⁻¹ * |ca1_E1 i (a⁻¹ • x) - ca1_E1 i (a⁻¹ • y)| ≤ a⁻¹ * (K * (a⁻¹ * dist x y)) :=
          mul_le_mul_of_nonneg_left h (inv_pos.2 ha).le
      _ = _ := by ring


theorem ca1_abs_smul_coord (a : ℝ) (ha : 0 < a) (x : Vec d) (k : Fin d) :
    |(a⁻¹ • x) k| = a⁻¹ * |x k| := by
  simp [abs_mul, abs_of_pos (inv_pos.2 ha)]

theorem ca1_E_abs_le {a : ℝ} (ha : 0 < a) (i : Fin d) (x : Vec d) :
    |ca1_E a i x| ≤ 12 * a⁻¹ * ca1_phi a x := by
  unfold ca1_E ca1_phi
  rw [abs_mul, abs_of_pos (inv_pos.2 ha)]
  calc a⁻¹ * |ca1_E1 i (a⁻¹ • x)| ≤ a⁻¹ * (12 * ca1_phi1 (a⁻¹ • x)) :=
        mul_le_mul_of_nonneg_left (ca1_E1_abs_le i _) (inv_pos.2 ha).le
    _ = _ := by ring

theorem ca1_E_layer {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hδ2 : 2 * δ ≤ 1) (i : Fin d) {x : Vec d}
    {j : Fin d} (hj : a * (1 - δ) ≤ |x j|) : |ca1_E a i x| ≤ 12 * a⁻¹ * (2 * δ) ^ 5 := by
  unfold ca1_E
  rw [abs_mul, abs_of_pos (inv_pos.2 ha)]
  have h1 : 1 - δ ≤ |(a⁻¹ • x) j| := by
    rw [ca1_abs_smul_coord a ha]
    have : a⁻¹ * (a * (1 - δ)) ≤ a⁻¹ * |x j| := mul_le_mul_of_nonneg_left hj (inv_pos.2 ha).le
    rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at this
  calc a⁻¹ * |ca1_E1 i (a⁻¹ • x)| ≤ a⁻¹ * (12 * (2 * δ) ^ 5) :=
        mul_le_mul_of_nonneg_left (ca1_E1_layer hδ hδ2 i h1) (inv_pos.2 ha).le
    _ = _ := by ring

theorem ca1_phi_harnack {a η : ℝ} (ha : 0 < a) (hη : 0 ≤ η) {x y : Vec d}
    (hx : ∀ k, |x k| + η ≤ a) (hxy : ∀ k, |y k - x k| ≤ η) :
    ca1_phi a y ≤ 64 ^ d * ca1_phi a x := by
  unfold ca1_phi
  refine ca1_phi1_harnack (h := a⁻¹ * η) (mul_nonneg (inv_pos.2 ha).le hη) (fun k => ?_) fun k => ?_
  · rw [ca1_abs_smul_coord a ha]
    have := mul_le_mul_of_nonneg_left (hx k) (inv_pos.2 ha).le
    rw [mul_add, inv_mul_cancel₀ ha.ne'] at this
    exact this
  · have : (a⁻¹ • y) k - (a⁻¹ • x) k = a⁻¹ * (y k - x k) := by simp [mul_sub]
    rw [this, abs_mul, abs_of_pos (inv_pos.2 ha)]
    exact mul_le_mul_of_nonneg_left (hxy k) (inv_pos.2 ha).le

theorem ca1_phi_lower {a : ℝ} (ha : 0 < a) {x : Vec d} (hx : ∀ k, |x k| ≤ 2 / 3 * a) :
    (125 / 729 : ℝ) ^ d ≤ ca1_phi a x := by
  unfold ca1_phi
  refine ca1_phi1_lower fun k => ?_
  rw [ca1_abs_smul_coord a ha]
  calc a⁻¹ * |x k| ≤ a⁻¹ * (2 / 3 * a) := mul_le_mul_of_nonneg_left (hx k) (inv_pos.2 ha).le
    _ = 2 / 3 := by field_simp

theorem ca1_phi_eq_zero {a : ℝ} (ha : 0 < a) {x : Vec d} {k : Fin d} (hk : a ≤ |x k|) :
    ca1_phi a x = 0 := by
  unfold ca1_phi
  refine ca1_phi1_eq_zero (k := k) ?_
  rw [ca1_abs_smul_coord a ha]
  have := mul_le_mul_of_nonneg_left hk (inv_pos.2 ha).le
  rwa [inv_mul_cancel₀ ha.ne'] at this

theorem ca1_phi_eq_zero_of_not_mem {a : ℝ} (ha : 0 < a) {x : Vec d}
    (hx : x ∉ Metric.closedBall (0 : Vec d) a) : ca1_phi a x = 0 := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg ha.le] at hx
  push Not at hx
  obtain ⟨k, hk⟩ := hx
  rw [Real.norm_eq_abs] at hk
  exact ca1_phi_eq_zero ha hk.le

theorem ca1_support_Phi_subset {a : ℝ} (ha : 0 < a) :
    Function.support (ca1_Phi (d := d) a) ⊆ Metric.closedBall 0 a := by
  intro x hx
  by_contra hn
  apply hx
  rw [ca1_Phi_eq, ca1_phi_eq_zero_of_not_mem ha hn]; norm_num

theorem ca1_tsupport_Phi_subset {a : ℝ} (ha : 0 < a) :
    tsupport (ca1_Phi (d := d) a) ⊆ Metric.closedBall 0 a :=
  closure_minimal (ca1_support_Phi_subset ha) Metric.isClosed_closedBall

theorem ca1_hasCompactSupport_Phi {a : ℝ} (ha : 0 < a) : HasCompactSupport (ca1_Phi (d := d) a) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec d) a)
    (ca1_support_Phi_subset ha)

theorem ca1_hasCompactSupport_E {a : ℝ} (ha : 0 < a) (i : Fin d) : HasCompactSupport (ca1_E a i) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec d) a) ?_
  intro x hx
  by_contra hn
  apply hx
  have := ca1_E_abs_le ha i x
  rw [ca1_phi_eq_zero_of_not_mem ha hn, mul_zero] at this
  exact abs_nonpos_iff.1 this

theorem ca1_closedBall_subset_openCube (m : ℤ) {a : ℝ} (ha : a < 3 ^ m / 2) :
    Metric.closedBall (0 : Vec d) a ⊆ openCubeSet (originCube d m) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h1 : |x i| ≤ a := by
    have := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at this
    exact this.trans hx
  rw [abs_le] at h1
  constructor <;> linarith only [h1.1, h1.2, ha]

theorem ca1_mem_openCube_iff (R : TriadicCube d) (x : Vec d) :
    x ∈ openCubeSet R ↔ ∀ k, |x k - triadicCubeShift R k| < cubeScaleFactor R / 2 := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, mem_translateSet_iff_sub_mem,
    mem_openCubeSet_originCube_iff]
  have h3 : cubeScaleFactor R = (3 : ℝ) ^ R.scale := by simp [cubeScaleFactor]
  refine forall_congr' fun k => ?_
  rw [abs_lt, h3]
  simp only [Pi.sub_apply]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]

theorem ca1_abs_le_center (R : TriadicCube d) {x : Vec d} (hx : x ∈ openCubeSet R) (k : Fin d) :
    |x k| ≤ |triadicCubeShift R k| + cubeScaleFactor R / 2 := by
  have h := (ca1_mem_openCube_iff R x).1 hx k
  have := abs_sub_abs_le_abs_sub (x k) (triadicCubeShift R k)
  linarith only [this, h]

theorem ca1_abs_ge_center (R : TriadicCube d) {x : Vec d} (hx : x ∈ openCubeSet R) (k : Fin d) :
    |triadicCubeShift R k| - cubeScaleFactor R / 2 ≤ |x k| := by
  have h := (ca1_mem_openCube_iff R x).1 hx k
  have := abs_sub_abs_le_abs_sub (triadicCubeShift R k) (x k)
  rw [abs_sub_comm] at this
  linarith only [this, h]

/-- Harnack bound on an interior grid cube: `|E_a| ≤ 12 · 64^d a⁻¹ φ_a(center)`. -/
theorem ca1_harnack_cube {a : ℝ} (ha : 0 < a) (R : TriadicCube d)
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) :
    ∀ x ∈ openCubeSet R, ∀ i, |ca1_E a i x| ≤ 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) := by
  intro x hx i
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  have hH := ca1_phi_harnack (a := a) (η := cubeScaleFactor R) ha hℓ.le (x := triadicCubeShift R) (y := x)
    (fun k => by linarith only [hint k, hℓ])
    (fun k => by
      have := (ca1_mem_openCube_iff R x).1 hx k
      exact this.le.trans (by linarith only [hℓ]))
  refine (ca1_E_abs_le ha i x).trans ?_
  have h12 : 0 ≤ 12 * a⁻¹ := by positivity
  calc 12 * a⁻¹ * ca1_phi a x ≤ 12 * a⁻¹ * (64 ^ d * ca1_phi a (triadicCubeShift R)) :=
        mul_le_mul_of_nonneg_left hH h12
    _ = _ := by ring

/-- Layer bound on a non-interior grid cube. -/
theorem ca1_layer_cube {a : ℝ} (ha : 0 < a) (R : TriadicCube d) (hl : 4 * cubeScaleFactor R ≤ a)
    (hnot : ¬ ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) :
    ∀ x ∈ openCubeSet R, ∀ i, |ca1_E a i x| ≤ 12 * a⁻¹ * (4 * cubeScaleFactor R / a) ^ 5 := by
  intro x hx i
  push Not at hnot
  obtain ⟨k, hk⟩ := hnot
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  have h1 := ca1_abs_ge_center R hx k
  have := ca1_E_layer (a := a) (δ := 2 * cubeScaleFactor R / a) ha (by positivity)
    (by rw [mul_div_assoc']; rw [div_le_one ha]; linarith only [hl]) i (x := x) (j := k) (by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ ha.ne']
      linarith only [h1, hk])
  refine this.trans (le_of_eq ?_)
  ring

/-- Far cubes carry no cutoff. -/
theorem ca1_far_cube {a : ℝ} (ha : 0 < a) (R : TriadicCube d)
    (hfar : ¬ ∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2) :
    ∀ x ∈ openCubeSet R, ∀ i, ca1_E a i x = 0 := by
  intro x hx i
  push Not at hfar
  obtain ⟨k, hk⟩ := hfar
  have h1 := ca1_abs_ge_center R hx k
  have h0 : ca1_phi a x = 0 := ca1_phi_eq_zero ha (k := k) (by linarith only [h1, hk])
  have := ca1_E_abs_le ha i x
  rw [h0, mul_zero] at this
  exact abs_nonpos_iff.1 this

theorem ca1_near_cube (R : TriadicCube d) {a r : ℝ}
    (hnear : ∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2)
    (hr : a + cubeScaleFactor R ≤ 2 / 3 * r) :
    ∀ x ∈ openCubeSet R, ∀ k, |x k| ≤ 2 / 3 * r := by
  intro x hx k
  have h1 := ca1_abs_le_center R hx k
  linarith only [h1, hnear k, hr]

theorem ca1_phi_continuous (a : ℝ) : Continuous (ca1_phi (d := d) a) := by
  unfold ca1_phi ca1_phi1 ca1_g
  exact continuous_finsetProd _ fun k _ => (ca1_pp_continuous 3).comp (by fun_prop)

/-- The Lipschitz constant of the cutoff family (dimension only). -/
noncomputable def ca1_K0 (d : ℕ) : ℝ≥0 := (ca1_lipschitz (d := d)).choose

theorem ca1_K0_spec (d : ℕ) : ∀ a : ℝ, 0 < a → LipschitzWith (ca1_K0 d * Real.toNNReal a⁻¹) (ca1_Phi (d := d) a) ∧
    ∀ i : Fin d, LipschitzWith (ca1_K0 d * Real.toNNReal a⁻¹ ^ 2) (ca1_E a i) :=
  (ca1_lipschitz (d := d)).choose_spec

/-- Cauchy-Schwarz for normalized finite sums. -/
theorem ca1_cs {ι : Type*} (s : Finset ι) (N : ℝ) (hN : 0 < N) (a b : ι → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)     (hAa : N⁻¹ * ∑ i ∈ s, a i ^ 2 ≤ A ^ 2) (hBb : N⁻¹ * ∑ i ∈ s, b i ^ 2 ≤ B ^ 2) :
    N⁻¹ * ∑ i ∈ s, a i * b i ≤ A * B := by
  have h1 : ∑ i ∈ s, a i ^ 2 ≤ N * A ^ 2 := by
    have := mul_le_mul_of_nonneg_left hAa hN.le
    rwa [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
  have h2 : ∑ i ∈ s, b i ^ 2 ≤ N * B ^ 2 := by
    have := mul_le_mul_of_nonneg_left hBb hN.le
    rwa [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq s a b
  have h4 : (∑ i ∈ s, a i * b i) ^ 2 ≤ (N * A * B) ^ 2 := by
    calc (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2 := h3
      _ ≤ (N * A ^ 2) * (N * B ^ 2) :=
        mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ = (N * A * B) ^ 2 := by ring
  have h5 : ∑ i ∈ s, a i * b i ≤ N * A * B :=
    abs_le_of_sq_le_sq' h4 (by positivity) |>.2
  calc N⁻¹ * ∑ i ∈ s, a i * b i ≤ N⁻¹ * (N * A * B) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = A * B := by field_simp

theorem ca1_sum_abstract {ι : Type*} [DecidableEq ι] (s Zi Zb : Finset ι) (N : ℝ) (hN : 0 < N)
    (hZi : Zi ⊆ s) (hZb : Zb ⊆ s) (hdisj : Disjoint Zi Zb)
    (x e W F P M : ι → ℝ) {α β Mb K2 Kd ε Wg Fg Pg Eg : ℝ}
    (hMb : 0 ≤ Mb) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hK2 : 0 ≤ K2) (hKd : 0 ≤ Kd) (hε : 0 ≤ ε)
    (hWg : 0 ≤ Wg) (hFg : 0 ≤ Fg) (hPg : 0 ≤ Pg) (hEg : 0 ≤ Eg)
    (hx : ∀ R, 0 ≤ x R) (hx0 : ∀ R ∈ s, R ∉ Zi → R ∉ Zb → x R ≤ 0)
    (he : ∀ R, 0 ≤ e R) (hW : ∀ R, 0 ≤ W R) (hF : ∀ R, 0 ≤ F R) (hP : ∀ R, 0 ≤ P R)
    (hint : ∀ R ∈ Zi, x R ≤ (α * e R + β * F R) * (M R * W R + K2 * (M R * e R + Kd * W R)))
    (hM : ∀ R ∈ Zi, 0 ≤ M R ∧ M R ≤ Mb ∧ M R * e R ≤ P R)
    (hbd : ∀ R ∈ Zb, x R ≤ ε * (e R * W R))
    (hWs : N⁻¹ * ∑ R ∈ s, W R ^ 2 ≤ Wg ^ 2) (hFs : N⁻¹ * ∑ R ∈ s, F R ^ 2 ≤ Fg ^ 2)
    (hPs : N⁻¹ * ∑ R ∈ s, P R ^ 2 ≤ Pg ^ 2)
    (hEs : N⁻¹ * ∑ R ∈ Zi ∪ Zb, e R ^ 2 ≤ Eg ^ 2) :
    N⁻¹ * ∑ R ∈ s, x R ≤ α * (Pg * Wg) + K2 * α * (Pg * Eg) + K2 * Kd * α * (Eg * Wg) +
      β * Mb * (Fg * Wg) + K2 * β * Mb * (Fg * Eg) + K2 * Kd * β * (Fg * Wg) + ε * (Eg * Wg) := by
  classical
  set Z := Zi ∪ Zb with hZ
  have hZs : Z ⊆ s := Finset.union_subset hZi hZb
  have hsum : ∑ R ∈ s, x R = ∑ R ∈ Z, x R := by
    symm
    refine Finset.sum_subset hZs fun R hR hRZ => ?_
    have : R ∉ Zi := fun h => hRZ (Finset.mem_union_left _ h)
    have h2 : R ∉ Zb := fun h => hRZ (Finset.mem_union_right _ h)
    exact le_antisymm (hx0 R hR this h2) (hx R)
  have hsplit : ∑ R ∈ Z, x R = ∑ R ∈ Zi, x R + ∑ R ∈ Zb, x R := Finset.sum_union hdisj
  -- the per-cube majorant
  let y : ι → ℝ := fun R => α * (P R * W R) + K2 * α * (P R * e R) + K2 * Kd * α * (e R * W R) +
      β * Mb * (F R * W R) + K2 * β * Mb * (F R * e R) + K2 * Kd * β * (F R * W R) + ε * (e R * W R)
  have hy0 : ∀ R, 0 ≤ y R := by
    intro R
    have h1 := he R; have h2 := hW R; have h3 := hF R; have h4 := hP R
    positivity
  have hyZ : ∑ R ∈ Z, x R ≤ ∑ R ∈ Z, y R := by
    rw [hsplit, hZ, Finset.sum_union hdisj]
    refine add_le_add (Finset.sum_le_sum fun R hR => ?_) (Finset.sum_le_sum fun R hR => ?_)
    · obtain ⟨hM0, hMb', hMP⟩ := hM R hR
      have h1 := hint R hR
      have h2 := he R; have h3 := hW R; have h4 := hF R; have h5 := hP R
      have t1 : α * (M R * e R) * W R ≤ α * P R * W R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP hα) h3
      have t2 : K2 * α * e R * (M R * e R) ≤ K2 * α * e R * P R :=
        mul_le_mul_of_nonneg_left hMP (by positivity)
      have t4 : β * F R * (M R * W R) ≤ β * F R * (Mb * W R) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMb' h3) (by positivity)
      have t5 : K2 * β * F R * (M R * e R) ≤ K2 * β * F R * (Mb * e R) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMb' h2) (by positivity)
      have t7 : 0 ≤ ε * (e R * W R) := by positivity
      have e1 : (α * e R + β * F R) * (M R * W R + K2 * (M R * e R + Kd * W R)) =
          α * (M R * e R) * W R + K2 * α * e R * (M R * e R) + K2 * Kd * α * (e R * W R) +
            β * F R * (M R * W R) + K2 * β * F R * (M R * e R) + K2 * Kd * β * (F R * W R) := by ring
      show x R ≤ α * (P R * W R) + K2 * α * (P R * e R) + K2 * Kd * α * (e R * W R) +
        β * Mb * (F R * W R) + K2 * β * Mb * (F R * e R) + K2 * Kd * β * (F R * W R) + ε * (e R * W R)
      nlinarith only [h1, e1, t1, t2, t4, t5, t7]
    · have h1 := hbd R hR
      have h2 := he R; have h3 := hW R; have h4 := hF R; have h5 := hP R
      have hnn : 0 ≤ α * (P R * W R) + K2 * α * (P R * e R) + K2 * Kd * α * (e R * W R) +
          β * Mb * (F R * W R) + K2 * β * Mb * (F R * e R) + K2 * Kd * β * (F R * W R) := by positivity
      show x R ≤ α * (P R * W R) + K2 * α * (P R * e R) + K2 * Kd * α * (e R * W R) +
        β * Mb * (F R * W R) + K2 * β * Mb * (F R * e R) + K2 * Kd * β * (F R * W R) + ε * (e R * W R)
      linarith only [h1, hnn]
  have hsub : ∀ f : ι → ℝ, (∀ R, 0 ≤ f R) → ∑ R ∈ Z, f R ≤ ∑ R ∈ s, f R := fun f hf =>
    Finset.sum_le_sum_of_subset_of_nonneg hZs fun R _ _ => hf R
  have hWZ : N⁻¹ * ∑ R ∈ Z, W R ^ 2 ≤ Wg ^ 2 :=
    (mul_le_mul_of_nonneg_left (hsub (fun R => W R ^ 2) fun R => sq_nonneg _) (inv_nonneg.2 hN.le)).trans hWs
  have hFZ : N⁻¹ * ∑ R ∈ Z, F R ^ 2 ≤ Fg ^ 2 :=
    (mul_le_mul_of_nonneg_left (hsub (fun R => F R ^ 2) fun R => sq_nonneg _) (inv_nonneg.2 hN.le)).trans hFs
  have hPZ : N⁻¹ * ∑ R ∈ Z, P R ^ 2 ≤ Pg ^ 2 :=
    (mul_le_mul_of_nonneg_left (hsub (fun R => P R ^ 2) fun R => sq_nonneg _) (inv_nonneg.2 hN.le)).trans hPs
  have c1 := ca1_cs Z N hN P W hPg hWg hPZ hWZ
  have c2 := ca1_cs Z N hN P e hPg hEg hPZ hEs
  have c3 := ca1_cs Z N hN e W hEg hWg hEs hWZ
  have c4 := ca1_cs Z N hN F W hFg hWg hFZ hWZ
  have c5 := ca1_cs Z N hN F e hFg hEg hFZ hEs
  have hyN : N⁻¹ * ∑ R ∈ Z, y R =
      α * (N⁻¹ * ∑ R ∈ Z, P R * W R) + K2 * α * (N⁻¹ * ∑ R ∈ Z, P R * e R) +
      K2 * Kd * α * (N⁻¹ * ∑ R ∈ Z, e R * W R) + β * Mb * (N⁻¹ * ∑ R ∈ Z, F R * W R) +
      K2 * β * Mb * (N⁻¹ * ∑ R ∈ Z, F R * e R) + K2 * Kd * β * (N⁻¹ * ∑ R ∈ Z, F R * W R) +
      ε * (N⁻¹ * ∑ R ∈ Z, e R * W R) := by
    simp only [y, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hfin : N⁻¹ * ∑ R ∈ Z, y R ≤ α * (Pg * Wg) + K2 * α * (Pg * Eg) + K2 * Kd * α * (Eg * Wg) +
      β * Mb * (Fg * Wg) + K2 * β * Mb * (Fg * Eg) + K2 * Kd * β * (Fg * Wg) + ε * (Eg * Wg) := by
    rw [hyN]
    have d1 := mul_le_mul_of_nonneg_left c1 hα
    have d2 := mul_le_mul_of_nonneg_left c2 (mul_nonneg hK2 hα)
    have d3 := mul_le_mul_of_nonneg_left c3 (mul_nonneg (mul_nonneg hK2 hKd) hα)
    have d4 := mul_le_mul_of_nonneg_left c4 (mul_nonneg hβ hMb)
    have d5 := mul_le_mul_of_nonneg_left c5 (mul_nonneg (mul_nonneg hK2 hβ) hMb)
    have d6 := mul_le_mul_of_nonneg_left c4 (mul_nonneg (mul_nonneg hK2 hKd) hβ)
    have d7 := mul_le_mul_of_nonneg_left c3 hε
    linarith only [d1, d2, d3, d4, d5, d6, d7]
  rw [hsum]
  exact (mul_le_mul_of_nonneg_left hyZ (inv_nonneg.2 hN.le)).trans hfin

/-- Witness: the cutoff is `1` at the center, the Harnack hypotheses are met by a point and itself,
and the lower bound applies to the center. -/
example : ca1_phi (d := 2) 1 (0 : Vec 2) = 1 ∧ ca1_phi (d := 2) 1 (0 : Vec 2) ≤ 64 ^ 2 * ca1_phi 1 (0 : Vec 2) ∧
    (125 / 729 : ℝ) ^ 2 ≤ ca1_phi (d := 2) 1 (0 : Vec 2) := by
  refine ⟨?_, ca1_phi_harnack one_pos (η := 1 / 10) (by norm_num) (fun k => by simp; norm_num)
    (fun k => by simp), ca1_phi_lower one_pos fun k => by simp; norm_num⟩
  simp [ca1_phi, ca1_phi1, ca1_g, ca1_pp]

end SuperdiffusionCLT.Section7
