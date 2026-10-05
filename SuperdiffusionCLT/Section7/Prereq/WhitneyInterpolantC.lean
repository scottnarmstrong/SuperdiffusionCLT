/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyInterpolantB

/-!
# The gradient of the interpolant and the comparison of neighbouring values

On the cube `Q(k₀)` the interpolant is Lipschitz with constant `(d/h) ∑_{k ~ k₀} |c k - c k₀|`,
so its gradient is bounded by this constant at every point of the open cube.  The differences
`c k - c k₀` between neighbouring values are controlled by the local oscillations
`wh1_osc h r u c k = ∫⁻_{B_k} (u - c k)^2` (no assumption that `c k` is the average).

## Main results

* `Section7.wh1_fderiv_bound`: the pointwise gradient bound on the open cube of `k₀`.
* `Section7.wh1_lintegral_grad_le`: `∫⁻_{Q(k₀)} |∇A|^2` against the sum of squared differences.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The local oscillation of `u` against the value `c k` on the averaging cube `B_k`. -/
noncomputable def wh1_osc (h r : ℝ) (u : Vec d → ℝ) (c : (Fin d → ℤ) → ℝ) (k : Fin d → ℤ) : ℝ≥0∞ :=
  ∫⁻ x in wh1_box (wh1_pt h k) r, ENNReal.ofReal ((u x - c k) ^ 2)

theorem wh1_A_sub_eq {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) {x y : Vec d}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) (hy : ∀ i, |y i - h * (k₀ i : ℝ)| ≤ h / 2) :
    wh1_A h Z c x - wh1_A h Z c y =
      ∑ k ∈ wh1_nbhd k₀, (c k - c k₀) * (wh1_chi h k x - wh1_chi h k y) := by
  rw [wh1_A_eq_cell hh hZ c hx, wh1_A_eq_cell hh hZ c hy]
  have e : ∑ k ∈ wh1_nbhd k₀, (c k - c k₀) * (wh1_chi h k x - wh1_chi h k y) =
      ∑ k ∈ wh1_nbhd k₀, c k * wh1_chi h k x - ∑ k ∈ wh1_nbhd k₀, c k * wh1_chi h k y -
        c k₀ * (∑ k ∈ wh1_nbhd k₀, wh1_chi h k x - ∑ k ∈ wh1_nbhd k₀, wh1_chi h k y) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, wh1_chi_sum hh hx, wh1_chi_sum hh hy]
  ring

/-- The Lipschitz bound of the interpolant between two points of the cube of `k₀`. -/
theorem wh1_A_sub_le {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) {x y : Vec d}
    (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) (hy : ∀ i, |y i - h * (k₀ i : ℝ)| ≤ h / 2) :
    |wh1_A h Z c x - wh1_A h Z c y| ≤
      ((d : ℝ) / h * ∑ k ∈ wh1_nbhd k₀, |c k - c k₀|) * ‖x - y‖ := by
  rw [wh1_A_sub_eq hh hZ c hx hy]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm ((d : ℝ) / h), mul_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  rw [mul_comm]
  calc _ ≤ ((d : ℝ) / h * ‖x - y‖) * |c k - c k₀| := by
        gcongr
        exact wh1_chi_lip hh k x y
    _ = _ := by ring

theorem wh1_grad_const_nonneg {h : ℝ} (hh : 0 < h) (k₀ : Fin d → ℤ) (c : (Fin d → ℤ) → ℝ) :
    0 ≤ (d : ℝ) / h * ∑ k ∈ wh1_nbhd k₀, |c k - c k₀| :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) hh.le) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The pointwise gradient bound on the open cube of `k₀`. -/
theorem wh1_fderiv_bound {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) {x : Vec d}
    (hx : x ∈ wh1_box (wh1_pt h k₀) (h / 2)) (i : Fin d) :
    |fderiv ℝ (wh1_A h Z c) x (basisVec i)| ≤
      (d : ℝ) / h * ∑ k ∈ wh1_nbhd k₀, |c k - c k₀| := by
  set L := (d : ℝ) / h * ∑ k ∈ wh1_nbhd k₀, |c k - c k₀| with hL
  have hL0 : 0 ≤ L := wh1_grad_const_nonneg hh k₀ c
  have hlip : LipschitzOnWith (Real.toNNReal L) (wh1_A h Z c) (wh1_box (wh1_pt h k₀) (h / 2)) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]
    exact wh1_A_sub_le hh hZ c (wh1_cell_le hy) (wh1_cell_le hz)
  have hn : wh1_box (wh1_pt h k₀) (h / 2) ∈ nhds x := (wh1_box_isOpen _ _).mem_nhds hx
  have h1 := norm_fderiv_le_of_lipschitzOn ℝ hn hlip
  rw [Real.coe_toNNReal _ hL0] at h1
  have h2 : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]
  calc |fderiv ℝ (wh1_A h Z c) x (basisVec i)|
      = ‖fderiv ℝ (wh1_A h Z c) x (basisVec i)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (wh1_A h Z c) x‖ * ‖basisVec (d := d) i‖ := (fderiv ℝ _ x).le_opNorm _
    _ ≤ L := by rw [h2, mul_one]; exact h1

/-- The squared gradient of the interpolant on the cube of `k₀`, against the sum of squared
differences of the neighbouring values. -/
theorem wh1_lintegral_grad_le {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (c : (Fin d → ℤ) → ℝ) :
    ∫⁻ x in wh1_box (wh1_pt h k₀) (h / 2),
        ENNReal.ofReal (∑ i, (lipGradient (wh1_A h Z c) x i) ^ 2) ≤
      ENNReal.ofReal ((d : ℝ) ^ 3 * 3 ^ d * h ^ d / h ^ 2 *
        ∑ k ∈ wh1_nbhd k₀, (c k - c k₀) ^ 2) := by
  set L := (d : ℝ) / h * ∑ k ∈ wh1_nbhd k₀, |c k - c k₀| with hL
  have hpt : ∀ x ∈ wh1_box (wh1_pt h k₀) (h / 2),
      ENNReal.ofReal (∑ i, (lipGradient (wh1_A h Z c) x i) ^ 2) ≤ ENNReal.ofReal ((d : ℝ) * L ^ 2) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ i, (lipGradient (wh1_A h Z c) x i) ^ 2 ≤ ∑ _i : Fin d, L ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (wh1_fderiv_bound hh hZ c hx i) 2
      _ = (d : ℝ) * L ^ 2 := by simp
  calc ∫⁻ x in wh1_box (wh1_pt h k₀) (h / 2),
        ENNReal.ofReal (∑ i, (lipGradient (wh1_A h Z c) x i) ^ 2)
      ≤ ∫⁻ _x in wh1_box (wh1_pt h k₀) (h / 2), ENNReal.ofReal ((d : ℝ) * L ^ 2) :=
        setLIntegral_mono' (wh1_box_measurable _ _) hpt
    _ = ENNReal.ofReal ((d : ℝ) * L ^ 2) * ENNReal.ofReal (h ^ d) := by
        rw [setLIntegral_const, wh1_volume_box _ (by linarith only [hh])]
        congr 3
        ring
    _ = ENNReal.ofReal ((d : ℝ) * L ^ 2 * h ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hs : (∑ k ∈ wh1_nbhd k₀, |c k - c k₀|) ^ 2 ≤
            3 ^ d * ∑ k ∈ wh1_nbhd k₀, (c k - c k₀) ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := wh1_nbhd k₀) (f := fun k => |c k - c k₀|)
          rw [wh1_card_nbhd] at this
          simpa only [sq_abs, Nat.cast_pow, Nat.cast_ofNat] using this
        have e : (d : ℝ) * L ^ 2 * h ^ d = (d : ℝ) * ((d : ℝ) / h) ^ 2 * h ^ d *
            (∑ k ∈ wh1_nbhd k₀, |c k - c k₀|) ^ 2 := by rw [hL]; ring
        rw [e]
        have e2 : (d : ℝ) ^ 3 * 3 ^ d * h ^ d / h ^ 2 * ∑ k ∈ wh1_nbhd k₀, (c k - c k₀) ^ 2 =
            (d : ℝ) * ((d : ℝ) / h) ^ 2 * h ^ d *
              (3 ^ d * ∑ k ∈ wh1_nbhd k₀, (c k - c k₀) ^ 2) := by
          field_simp
        rw [e2]
        exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem wh1_ofReal_two_mul (x : ℝ) : ENNReal.ofReal (2 * x) = 2 * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- Overlap count: each grid index is a neighbour of at most `3^d` indices. -/
theorem wh1_mem_nbhd_iff {k₀ k : Fin d → ℤ} :
    k ∈ wh1_nbhd k₀ ↔ ∀ i, |k i - k₀ i| ≤ 1 := by
  unfold wh1_nbhd
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, abs_le]
  omega

theorem wh1_mem_nbhd_symm {k₀ k : Fin d → ℤ} : k ∈ wh1_nbhd k₀ ↔ k₀ ∈ wh1_nbhd k := by
  rw [wh1_mem_nbhd_iff, wh1_mem_nbhd_iff]
  refine forall_congr' fun i => ?_
  rw [abs_sub_comm]

theorem wh1_sum_nbhd_le {P : Finset (Fin d → ℤ)} (g : (Fin d → ℤ) → ℝ≥0∞) :
    ∑ k₀ ∈ P, ∑ k ∈ wh1_nbhd k₀, g k ≤ 3 ^ d * ∑ k ∈ P.biUnion wh1_nbhd, g k := by
  classical
  have e : ∑ k₀ ∈ P, ∑ k ∈ wh1_nbhd k₀, g k =
      ∑ k ∈ P.biUnion wh1_nbhd, ∑ k₀ ∈ P.filter (fun k₀ => k ∈ wh1_nbhd k₀), g k := by
    refine Finset.sum_comm' fun k₀ k => ?_
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, k₀, h1, h2⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr
  have : (P.filter (fun k₀ => k ∈ wh1_nbhd k₀)).card ≤ (wh1_nbhd k).card :=
    Finset.card_le_card fun k₀ hk₀ => wh1_mem_nbhd_symm.1 (Finset.mem_filter.1 hk₀).2
  rw [wh1_card_nbhd] at this
  exact_mod_cast this

/-- A union bound for lower integrals over a finite family of sets. -/
theorem wh1_lintegral_biUnion_le {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    (P : Finset ι) (s : ι → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in ⋃ i ∈ P, s i, f x ∂μ ≤ ∑ i ∈ P, ∫⁻ x in s i, f x ∂μ := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a P ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (by gcongr)

/-- The interpolant of constant values is that constant on the cube. -/
theorem wh1_A_const_cell {h : ℝ} (hh : 0 < h) {k₀ : Fin d → ℤ} {Z : Finset (Fin d → ℤ)}
    (hZ : wh1_nbhd k₀ ⊆ Z) (a : ℝ) {x : Vec d} (hx : ∀ i, |x i - h * (k₀ i : ℝ)| ≤ h / 2) :
    wh1_A h Z (fun _ => a) x = a := by
  rw [wh1_A_eq_cell hh hZ _ hx, ← Finset.mul_sum, wh1_chi_sum hh hx, mul_one]

/-- The global `L²` interpolation estimate over the cubes indexed by `P` (squared form of
`e.Dir.new.Whitney.u.minus.A`, with the neighbour overlap constant `3^d`). -/
theorem wh1_global_sub_A {h r : ℝ} (hh : 0 < h) (hr : 3 * h / 2 ≤ r)
    {P Z : Finset (Fin d → ℤ)} (hZ : P.biUnion wh1_nbhd ⊆ Z) (c : (Fin d → ℤ) → ℝ)
    (u : Vec d → ℝ)
    (hu : ∀ k₀ ∈ P, AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) r))) :
    ∫⁻ x in ⋃ k₀ ∈ P, wh1_box (wh1_pt h k₀) (h / 2),
        ENNReal.ofReal ((u x - wh1_A h Z c x) ^ 2) ≤
      (3 : ℝ≥0∞) ^ d * ∑ k ∈ P.biUnion wh1_nbhd, wh1_osc h r u c k := by
  refine (wh1_lintegral_biUnion_le P _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k₀ hk₀ => ?_)
    (wh1_sum_nbhd_le (P := P) (fun k => wh1_osc h r u c k))
  have hZ' : wh1_nbhd k₀ ⊆ Z := fun k hk => hZ (Finset.mem_biUnion.2 ⟨k₀, hk₀, hk⟩)
  have hu' : AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) (h / 2))) :=
    (hu k₀ hk₀).mono_measure (Measure.restrict_mono (wh1_box_mono _ (by linarith only [hh, hr]))
      le_rfl)
  exact wh1_lintegral_sub_A_le hh hr hZ' c u hu'

/-- The interpolant is globally Lipschitz. -/
theorem wh1_A_lipschitz {h : ℝ} (hh : 0 < h) (Z : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    LipschitzWith (Real.toNNReal ((d : ℝ) / h * ∑ k ∈ Z, |c k|)) (wh1_A h Z c) := by
  have hL0 : 0 ≤ (d : ℝ) / h * ∑ k ∈ Z, |c k| :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hh.le) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]
  unfold wh1_A
  rw [← Finset.sum_sub_distrib]
  calc |∑ k ∈ Z, (c k * wh1_chi h k x - c k * wh1_chi h k y)|
      ≤ ∑ k ∈ Z, |c k * wh1_chi h k x - c k * wh1_chi h k y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Z, |c k| * ((d : ℝ) / h * ‖x - y‖) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← mul_sub, abs_mul]
        gcongr
        exact wh1_chi_lip hh k x y
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A Lipschitz function has its a.e. derivative as weak gradient on every set. -/
theorem wh1_hasWeakGradient (U : Set (Vec d)) {K : ℝ≥0} {η : Vec d → ℝ}
    (hη : LipschitzWith K η) : HasWeakGradientOn U η (lipGradient η) := by
  intro i φ hφ hφc hφU
  have h := lipschitzWith_hasWeakPartialDerivOn_univ hη i φ hφ hφc (by simp)
  simp only [Measure.restrict_univ] at h
  have e1 : ∫ x in U, η x * fderiv ℝ φ x (basisVec i) =
      ∫ x, η x * fderiv ℝ φ x (basisVec i) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : fderiv ℝ φ x = 0 := by
      by_contra hne
      exact hx (hφU (support_fderiv_subset ℝ hne))
    simp [this]
  have e2 : ∫ x in U, lipGradient η x i * φ x = ∫ x, lipGradient η x i * φ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hφU h')
    simp [this]
  rw [e1, e2]
  exact h

/-- The interpolant as an element of `H¹(U)` for a set of finite volume. -/
noncomputable def wh1_H1 {h : ℝ} (hh : 0 < h) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (Z : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) : H1Function U where
  toFun := wh1_A h Z c
  grad := lipGradient (wh1_A h Z c)
  memL2 := by
    have : IsFiniteMeasure (volume.restrict U) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hU⟩
    refine MemLp.of_bound ((wh1_A_lipschitz hh Z c).continuous.aestronglyMeasurable)
      (∑ k ∈ Z, |c k|) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    unfold wh1_A
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (wh1_chi_nonneg h k x)]
    exact mul_le_of_le_one_right (abs_nonneg _) (wh1_chi_le_one h k x)
  gradMemL2 := by
    intro i
    have : IsFiniteMeasure (volume.restrict U) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hU⟩
    exact MemLp.of_bound
      ((aestronglyMeasurable_partialDeriv (wh1_A h Z c) i).mono_measure Measure.restrict_le_self)
      _ (ae_restrict_of_ae (lipschitzWith_ae_norm_partialDeriv_le (wh1_A_lipschitz hh Z c) i))
  hasWeakGradient := wh1_hasWeakGradient U (wh1_A_lipschitz hh Z c)

@[simp] theorem wh1_H1_toFun {h : ℝ} (hh : 0 < h) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (Z : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) : (wh1_H1 hh hU Z c).toFun = wh1_A h Z c :=
  rfl

@[simp] theorem wh1_H1_grad {h : ℝ} (hh : 0 < h) {U : Set (Vec d)} (hU : volume U ≠ ⊤)
    (Z : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    (wh1_H1 hh hU Z c).grad = lipGradient (wh1_A h Z c) := rfl

/-- The hypotheses of the global estimates can hold together: one cube, `Z` its neighbourhood,
the averaging cube of half-side `3h/2`, and a measurable `u`. -/
example (h : ℝ) (hh : 0 < h) :
    ∫⁻ x in ⋃ k₀ ∈ ({0} : Finset (Fin d → ℤ)), wh1_box (wh1_pt h k₀) (h / 2),
        ENNReal.ofReal (((fun _ : Vec d => (1 : ℝ)) x - wh1_A h (wh1_nbhd 0) (fun _ => 1) x) ^ 2) ≤
      (3 : ℝ≥0∞) ^ d * ∑ k ∈ ({0} : Finset (Fin d → ℤ)).biUnion wh1_nbhd,
        wh1_osc h (3 * h / 2) (fun _ => (1 : ℝ)) (fun _ => 1) k :=
  wh1_global_sub_A hh le_rfl (by simp) _ _ fun _ _ => aemeasurable_const

example (h : ℝ) (hh : 0 < h) (x : Vec d) (hx : ∀ i, |x i - h * ((0 : Fin d → ℤ) i : ℝ)| ≤ h / 2) :
    wh1_A h (wh1_nbhd 0) (fun _ => (1 : ℝ)) x = 1 :=
  wh1_A_const_cell hh subset_rfl 1 hx

end SuperdiffusionCLT.Section7
