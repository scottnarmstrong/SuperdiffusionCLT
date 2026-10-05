/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaN
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecay
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# One-dimensional ingredients for the face moments

Bump profiles, their integral bounds, the normal profile of width `h`, and the product-form test
functions `x ↦ ∏ i, Φ i (x i)` with their smoothness, support, `e`-derivative and box integrals.
-/

namespace SuperdiffusionCLT.Section7

section
variable {d : ℕ}



theorem r3d_integral_pi {a b : ℝ} (G : Fin d → ℝ → ℝ) :
    ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo a b), ∏ i, G i (x i) =
      ∏ i, ∫ t in Set.Ioo a b, G i t := by
  have hm : MeasurableSet (Set.pi Set.univ (fun _ : Fin d => Set.Ioo a b)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  rw [← integral_indicator hm]
  have h1 : (Set.pi Set.univ (fun _ : Fin d => Set.Ioo a b)).indicator (fun x => ∏ i, G i (x i)) =
      fun x : Fin d → ℝ => ∏ i, (Set.Ioo a b).indicator (G i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ (fun _ : Fin d => Set.Ioo a b)
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ Set.Ioo a b := by
        by_contra h
        push Not at h
        exact hx fun i _ => h i
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h1]
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
    (μ := fun _ => (volume : Measure ℝ)) (fun i => (Set.Ioo a b).indicator (G i))
  rw [volume_pi, this]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact integral_indicator measurableSet_Ioo

theorem r3d_prod_contDiff (Φ : Fin d → ℝ → ℝ) (hΦ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Φ i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∏ i, Φ i (x i)) :=
  contDiff_prod fun i _ => (hΦ i).comp (contDiff_apply ℝ ℝ i)

theorem r3d_prod_tsupport (Φ : Fin d → ℝ → ℝ) :
    tsupport (fun x : Vec d => ∏ i, Φ i (x i)) ⊆ {x | ∀ i, x i ∈ tsupport (Φ i)} := by
  intro x hx
  have h1 : Function.support (fun x : Vec d => ∏ i, Φ i (x i)) ⊆
      {x | ∀ i, x i ∈ tsupport (Φ i)} := by
    intro y hy i
    have : Φ i (y i) ≠ 0 := fun h0 => hy (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    exact subset_tsupport _ this
  have h2 : IsClosed {x : Vec d | ∀ i, x i ∈ tsupport (Φ i)} := by
    have : {x : Vec d | ∀ i, x i ∈ tsupport (Φ i)} = ⋂ i, (fun x : Vec d => x i) ⁻¹' tsupport (Φ i) := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i => (isClosed_tsupport _).preimage (continuous_apply i)
  exact closure_minimal h1 h2 hx

theorem r3d_prod_hasCompactSupport (Φ : Fin d → ℝ → ℝ) (hΦ : ∀ i, HasCompactSupport (Φ i)) :
    HasCompactSupport (fun x : Vec d => ∏ i, Φ i (x i)) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => hΦ i) (isClosed_tsupport _) ?_
  intro x hx i _
  exact r3d_prod_tsupport Φ hx i

theorem r3d_prod_grad_e (Φ : Fin d → ℝ → ℝ) (hΦ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Φ i)) (e : Fin d)
    (x : Vec d) :
    p12_grad (fun y : Vec d => ∏ i, Φ i (y i)) x e =
      (∏ j ∈ Finset.univ.erase e, Φ j (x j)) * deriv (Φ e) (x e) := by
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun y : Vec d => Φ i (y i)) (deriv (Φ i) (x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) x := by
    intro i _
    have h1 : HasDerivAt (Φ i) (deriv (Φ i) (x i)) (x i) :=
      ((hΦ i).differentiable (by simp) (x i)).hasDerivAt
    have h2 := HasFDerivAt.comp x (g := Φ i) (g' := ContinuousLinearMap.toSpanSingleton ℝ (deriv (Φ i) (x i)))
      (by simpa using h1.hasFDerivAt) (hasFDerivAt_apply i x)
    refine h2.congr_fderiv ?_
    ext y
    simp [mul_comm]
  have h3 := HasFDerivAt.finsetProd hf
  unfold p12_grad
  rw [h3.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single e]
  · simp [basisVec]
  · intro i _ hi
    simp [basisVec, hi]
  · simp

end


/-- A one-dimensional bump equal to `1` on `[-r/2, r/2]` and vanishing outside `(-r, r)`. -/
noncomputable def r3d_bump {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r / 2, r, by positivity, by linarith only [hr]⟩

theorem r3d_bump_contDiff {r : ℝ} (hr : 0 < r) : ContDiff ℝ (⊤ : ℕ∞) (r3d_bump hr) :=
  (r3d_bump hr).contDiff

theorem r3d_bump_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (r3d_bump hr) :=
  (r3d_bump hr).hasCompactSupport

theorem r3d_bump_nonneg {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ r3d_bump hr t := (r3d_bump hr).nonneg

theorem r3d_bump_le_one {r : ℝ} (hr : 0 < r) (t : ℝ) : r3d_bump hr t ≤ 1 := (r3d_bump hr).le_one

theorem r3d_bump_one {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : |t| ≤ r / 2) : r3d_bump hr t = 1 := by
  refine (r3d_bump hr).one_of_mem_closedBall ?_
  simpa [Metric.mem_closedBall, dist_eq_norm, r3d_bump] using ht

theorem r3d_bump_zero {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : r ≤ |t|) : r3d_bump hr t = 0 := by
  refine (r3d_bump hr).zero_of_le_dist ?_
  simpa [dist_eq_norm, r3d_bump] using ht

theorem r3d_bump_even {r : ℝ} (hr : 0 < r) (t : ℝ) : r3d_bump hr (-t) = r3d_bump hr t :=
  (r3d_bump hr).neg t

theorem r3d_bump_tsupport {r : ℝ} (hr : 0 < r) : tsupport (r3d_bump hr) ⊆ Set.Icc (-r) r := by
  intro t ht
  rw [(r3d_bump hr).tsupport_eq] at ht
  simpa [Metric.mem_closedBall, dist_eq_norm, r3d_bump, abs_le] using ht

theorem r3d_integrable_of_cont {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f := hf.integrable_of_hasCompactSupport hc

theorem r3d_setIntegral_le_of_support {f : ℝ → ℝ} {J S : Set ℝ} {C : ℝ} (hJ : MeasurableSet J)
    (hJf : volume J ≠ ⊤) (hf : Integrable f) (hf0 : ∀ t, 0 ≤ f t) (hfJ : ∀ t, t ∉ J → f t = 0)
    (hfC : ∀ t, f t ≤ C) : ∫ t in S, f t ≤ C * (volume J).toReal := by
  have h1 : ∫ t in S, f t ≤ ∫ t, f t := setIntegral_le_integral hf (Filter.Eventually.of_forall hf0)
  have h2 : ∫ t, f t = ∫ t, J.indicator f t := by
    congr 1
    funext t
    by_cases ht : t ∈ J
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, hfJ t ht]
  have h3 : ∫ t, J.indicator f t ≤ ∫ t, J.indicator (fun _ => C) t := by
    refine integral_mono (hf.indicator hJ)
      ((integrable_indicator_iff hJ).2 (integrableOn_const hJf)) fun t => ?_
    by_cases ht : t ∈ J
    · simp only [Set.indicator_of_mem ht]; exact hfC t
    · simp only [Set.indicator_of_notMem ht]; exact le_rfl
  have h4 : ∫ t, J.indicator (fun _ => C) t = C * (volume J).toReal := by
    rw [integral_indicator hJ]
    simp [Measure.real, mul_comm]
  linarith only [h1, h2, h3, h4]

theorem r3d_le_setIntegral {f : ℝ → ℝ} {J S : Set ℝ} {c : ℝ} (hJ : MeasurableSet J)
    (hJf : volume J ≠ ⊤) (hJS : J ⊆ S) (hf : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hfc : ∀ t ∈ J, c ≤ f t) : c * (volume J).toReal ≤ ∫ t in S, f t := by
  have h1 : ∫ t in J, f t ≤ ∫ t in S, f t :=
    setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall hf0)
      (Filter.Eventually.of_forall hJS)
  have h2 : ∫ t in J, c ≤ ∫ t in J, f t :=
    setIntegral_mono_on (integrableOn_const hJf) hf.integrableOn hJ hfc
  have h3 : ∫ t in J, c = c * (volume J).toReal := by
    simp [Measure.real, mul_comm]
  linarith only [h1, h2, h3]

theorem r3d_bump_integral_ge {L ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) :
    ρ ≤ ∫ t in Set.Ioo (-L) L, r3d_bump hρ t := by
  have hc := r3d_integrable_of_cont (r3d_bump hρ).continuous (r3d_bump_compact hρ)
  have h := r3d_le_setIntegral (J := Set.Icc (-(ρ / 2)) (ρ / 2)) (S := Set.Ioo (-L) L) (c := 1)
    measurableSet_Icc (by simp) (fun t ht => by
      simp only [Set.mem_Icc] at ht
      simp only [Set.mem_Ioo]
      constructor <;> linarith only [ht.1, ht.2, hρ, hρL]) hc (r3d_bump_nonneg hρ)
    (fun t ht => by
      rw [r3d_bump_one hρ (by rw [abs_le]; exact ht)])
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith only [hρ])] at h
  have e : (ρ / 2 - -(ρ / 2)) = ρ := by ring
  rw [e, one_mul] at h
  exact h

theorem r3d_bump_integral_sq_le {L ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Set.Ioo (-L) L, r3d_bump hρ t ^ 2 ≤ 2 * ρ := by
  have hc2 : HasCompactSupport (fun t => r3d_bump hρ t ^ 2) :=
    (r3d_bump_compact hρ).mono' (fun t ht => subset_tsupport _ (by
      intro h0
      apply ht
      simp [h0]))
  have hc := r3d_integrable_of_cont ((r3d_bump hρ).continuous.pow 2) hc2
  have h := r3d_setIntegral_le_of_support (S := Set.Ioo (-L) L) (C := 1) (J := Set.Ioo (-ρ) ρ)
    measurableSet_Ioo (by simp) hc (fun t => sq_nonneg _) (fun t ht => by
      have : ρ ≤ |t| := by
        by_contra h
        apply ht
        rw [Set.mem_Ioo, ← abs_lt]
        exact not_le.mp h
      simp [r3d_bump_zero hρ this]) (fun t => by
      have h0 := r3d_bump_nonneg hρ t
      have h1 := r3d_bump_le_one hρ t
      calc r3d_bump hρ t ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = 1 := one_pow 2)
  rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith only [hρ])] at h
  have e : (ρ - -ρ) = 2 * ρ := by ring
  rw [e, one_mul] at h
  exact h

theorem r3d_bump_integral_odd {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ) :
    ∫ t in Set.Ioo (-L) L, t * r3d_bump hρ t = 0 := by
  have h1 : ∫ t in Set.Ioo (-L) L, t * r3d_bump hρ t = ∫ t in (-L)..L, t * r3d_bump hρ t := by
    rw [intervalIntegral.integral_of_le (by linarith only [hL]), integral_Ioc_eq_integral_Ioo]
  have h2 : ∫ t in (-L)..L, t * r3d_bump hρ t = ∫ t in (-L)..L, (-t) * r3d_bump hρ (-t) := by
    have := intervalIntegral.integral_comp_neg (a := -L) (b := L) (fun t => t * r3d_bump hρ t)
    rw [this]
    simp
  have h3 : ∫ t in (-L)..L, (-t) * r3d_bump hρ (-t) = -∫ t in (-L)..L, t * r3d_bump hρ t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [r3d_bump_even hρ t]
    ring
  linarith only [h1, h2, h3]

theorem r3d_psi_compact {ρ : ℝ} (hρ : 0 < ρ) : HasCompactSupport (fun t => t * r3d_bump hρ t) :=
  (r3d_bump_compact hρ).mono' (fun t ht => subset_tsupport _ (by
    intro h0
    apply ht
    simp [h0]))

theorem r3d_psi_cont {ρ : ℝ} (hρ : 0 < ρ) : Continuous (fun t => t * r3d_bump hρ t) :=
  continuous_id.mul (r3d_bump hρ).continuous

theorem r3d_bump_integral_second_ge {L ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) :
    ρ ^ 3 / 12 ≤ ∫ t in Set.Ioo (-L) L, t * (t * r3d_bump hρ t) := by
  have hc : Integrable (fun t => t * (t * r3d_bump hρ t)) :=
    r3d_integrable_of_cont (continuous_id.mul (r3d_psi_cont hρ))
      ((r3d_psi_compact hρ).mono' (fun t ht => subset_tsupport _ (by
        intro h0
        apply ht
        simp [h0])))
  have hJS : Set.Icc (-(ρ / 2)) (ρ / 2) ⊆ Set.Ioo (-L) L := fun t ht => by
    simp only [Set.mem_Icc] at ht
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [ht.1, ht.2, hρ, hρL]
  have hnn : ∀ t : ℝ, 0 ≤ t * (t * r3d_bump hρ t) := fun t => by
    have : t * (t * r3d_bump hρ t) = t ^ 2 * r3d_bump hρ t := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg t) (r3d_bump_nonneg hρ t)
  have h1 : ∫ t in Set.Icc (-(ρ / 2)) (ρ / 2), t * (t * r3d_bump hρ t) ≤
      ∫ t in Set.Ioo (-L) L, t * (t * r3d_bump hρ t) :=
    setIntegral_mono_set hc.integrableOn (Filter.Eventually.of_forall hnn)
      (Filter.Eventually.of_forall hJS)
  have h2 : ∫ t in Set.Icc (-(ρ / 2)) (ρ / 2), t ^ 2 ≤
      ∫ t in Set.Icc (-(ρ / 2)) (ρ / 2), t * (t * r3d_bump hρ t) := by
    refine setIntegral_mono_on (continuous_id.pow 2).integrableOn_Icc hc.integrableOn
      measurableSet_Icc fun t ht => ?_
    rw [r3d_bump_one hρ (by rw [abs_le]; exact ht)]
    simp [sq]
  have h3 : ∫ t in Set.Icc (-(ρ / 2)) (ρ / 2), t ^ 2 = ρ ^ 3 / 12 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hρ]),
      integral_pow]
    ring
  linarith only [h1, h2, h3]

theorem r3d_bump_integral_psi_sq_le {L ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Set.Ioo (-L) L, (t * r3d_bump hρ t) ^ 2 ≤ 2 * ρ ^ 3 := by
  have hc2 : HasCompactSupport (fun t => (t * r3d_bump hρ t) ^ 2) :=
    (r3d_psi_compact hρ).mono' (fun t ht => subset_tsupport _ (by
      intro h0
      apply ht
      simp [h0]))
  have hc := r3d_integrable_of_cont ((r3d_psi_cont hρ).pow 2) hc2
  have h := r3d_setIntegral_le_of_support (S := Set.Ioo (-L) L) (C := ρ ^ 2) (J := Set.Ioo (-ρ) ρ)
    measurableSet_Ioo (by simp) hc (fun t => sq_nonneg _) (fun t ht => by
      have : ρ ≤ |t| := by
        by_contra h
        apply ht
        rw [Set.mem_Ioo, ← abs_lt]
        exact not_le.mp h
      simp [r3d_bump_zero hρ this]) (fun t => by
      have h0 := r3d_bump_nonneg hρ t
      have h1 := r3d_bump_le_one hρ t
      by_cases ht : ρ ≤ |t|
      · simp [r3d_bump_zero hρ ht]; positivity
      · push Not at ht
        have ht2 : t ^ 2 ≤ ρ ^ 2 := by
          have := sq_le_sq' (abs_lt.mp ht).1.le (abs_lt.mp ht).2.le
          exact this
        calc (t * r3d_bump hρ t) ^ 2 = t ^ 2 * r3d_bump hρ t ^ 2 := by ring
          _ ≤ ρ ^ 2 * 1 := mul_le_mul ht2 (by
              calc r3d_bump hρ t ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h1 2
                _ = 1 := one_pow 2) (sq_nonneg _) (sq_nonneg _)
          _ = ρ ^ 2 := mul_one _)
  rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith only [hρ])] at h
  have e : (ρ - -ρ) = 2 * ρ := by ring
  rw [e] at h
  simp only [Pi.pow_apply] at h
  have e2 : ρ ^ 2 * (2 * ρ) = 2 * ρ ^ 3 := by ring
  linarith only [h, e2]



/-- The normal profile: a bump of width `h` around the face `t = -L`. -/
noncomputable def r3d_prof (L h : ℝ) (t : ℝ) : ℝ := r3d_bump (r := 1) one_pos ((t + L) / h)

theorem r3d_prof_contDiff (L h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (r3d_prof L h) := by
  unfold r3d_prof
  exact (r3d_bump_contDiff one_pos).comp (((contDiff_id.add contDiff_const).div_const h))

theorem r3d_prof_zero (L : ℝ) {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : h ≤ |t + L|) : r3d_prof L h t = 0 := by
  unfold r3d_prof
  refine r3d_bump_zero one_pos ?_
  rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]
  linarith only [ht]

theorem r3d_prof_one (L : ℝ) {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : |t + L| ≤ h / 2) : r3d_prof L h t = 1 := by
  unfold r3d_prof
  refine r3d_bump_one one_pos ?_
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
  linarith only [ht]

theorem r3d_prof_nonneg (L h t : ℝ) : 0 ≤ r3d_prof L h t := r3d_bump_nonneg one_pos _

theorem r3d_prof_le_one (L h t : ℝ) : r3d_prof L h t ≤ 1 := r3d_bump_le_one one_pos _

theorem r3d_prof_tsupport (L : ℝ) {h : ℝ} (hh : 0 < h) :
    tsupport (r3d_prof L h) ⊆ Set.Icc (-L - h) (-L + h) := by
  refine closure_minimal ?_ isClosed_Icc
  intro t ht
  have h1 : ¬ h ≤ |t + L| := fun h2 => ht (r3d_prof_zero L hh h2)
  push Not at h1
  rw [abs_lt] at h1
  exact ⟨by linarith only [h1.1], by linarith only [h1.2]⟩

theorem r3d_prof_compact (L : ℝ) {h : ℝ} (hh : 0 < h) : HasCompactSupport (r3d_prof L h) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (r3d_prof_tsupport L hh)

theorem r3d_prof_hasDerivAt (L h t : ℝ) :
    HasDerivAt (r3d_prof L h) (deriv (r3d_bump (r := 1) one_pos) ((t + L) / h) * (1 / h)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t + L) / h) (1 / h) t :=
    ((hasDerivAt_id t).add_const L).div_const h
  have h2 : HasDerivAt (r3d_bump (r := 1) one_pos)
      (deriv (r3d_bump (r := 1) one_pos) ((t + L) / h)) ((t + L) / h) :=
    (((r3d_bump_contDiff one_pos).differentiable (by simp)) _).hasDerivAt
  exact h2.comp t h1

theorem r3d_exists_deriv_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |deriv (r3d_bump (r := 1) one_pos) t| ≤ K := by
  have hd : Continuous (deriv (r3d_bump (r := 1) one_pos)) :=
    (r3d_bump_contDiff one_pos).continuous_deriv (by simp)
  have hc : HasCompactSupport (deriv (r3d_bump (r := 1) one_pos)) := (r3d_bump_compact one_pos).deriv
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩


theorem r3d_deriv_bump_zero {s : ℝ} (hs : 1 < |s|) : deriv (r3d_bump (r := 1) one_pos) s = 0 := by
  have h : (r3d_bump (r := 1) one_pos) =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {u : ℝ | 1 < |u|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hs] with u hu
    exact r3d_bump_zero one_pos (le_of_lt hu)
  rw [h.deriv_eq]
  simp

theorem r3d_prof_integral_deriv (L : ℝ) {h : ℝ} (hh : 0 < h) (hL : 0 < L) (hhL : h ≤ 2 * L) :
    ∫ t in Set.Ioo (-L) L, deriv (r3d_prof L h) t = -1 := by
  have h1 : ∫ t in Set.Ioo (-L) L, deriv (r3d_prof L h) t = ∫ t in (-L)..L, deriv (r3d_prof L h) t := by
    rw [intervalIntegral.integral_of_le (by linarith only [hL]), integral_Ioc_eq_integral_Ioo]
  have hd : ∀ t, HasDerivAt (r3d_prof L h) (deriv (r3d_prof L h) t) t := fun t =>
    (((r3d_prof_contDiff L h).differentiable (by simp)) t).hasDerivAt
  have hint : IntervalIntegrable (deriv (r3d_prof L h)) volume (-L) L :=
    ((r3d_prof_contDiff L h).continuous_deriv (by simp)).intervalIntegrable _ _
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hint
  have h3 : r3d_prof L h L = 0 := by
    refine r3d_prof_zero L hh ?_
    rw [abs_of_pos (by linarith only [hL])]
    linarith only [hhL]
  have h4 : r3d_prof L h (-L) = 1 := by
    refine r3d_prof_one L hh ?_
    simp only [neg_add_cancel, abs_zero]
    linarith only [hh]
  rw [h1, h2, h3, h4]
  ring

theorem r3d_prof_integral_sq_le (L : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ t in Set.Ioo (-L) L, r3d_prof L h t ^ 2 ≤ 2 * h := by
  have hc2 : HasCompactSupport (fun t => r3d_prof L h t ^ 2) :=
    (r3d_prof_compact L hh).mono' (fun t ht => subset_tsupport _ (by
      intro h0
      apply ht
      simp [h0]))
  have hc := r3d_integrable_of_cont (((r3d_prof_contDiff L h).continuous).pow 2) hc2
  have h0 := r3d_setIntegral_le_of_support (S := Set.Ioo (-L) L) (C := 1)
    (J := Set.Icc (-L - h) (-L + h)) measurableSet_Icc (by simp) hc (fun t => sq_nonneg _)
    (fun t ht => by
      have : h ≤ |t + L| := by
        by_contra hne
        apply ht
        push Not at hne
        rw [abs_lt] at hne
        exact ⟨by linarith only [hne.1], by linarith only [hne.2]⟩
      simp [r3d_prof_zero L hh this]) (fun t => by
      calc r3d_prof L h t ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (r3d_prof_nonneg L h t) (r3d_prof_le_one L h t) 2
        _ = 1 := one_pow 2)
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith only [hh])] at h0
  have e : (-L + h - (-L - h)) = 2 * h := by ring
  rw [e, one_mul] at h0
  exact h0

theorem r3d_prof_integral_deriv_sq_le (L : ℝ) {h K : ℝ} (hh : 0 < h)
    (hKb : ∀ t, |deriv (r3d_bump (r := 1) one_pos) t| ≤ K) :
    ∫ t in Set.Ioo (-L) L, deriv (r3d_prof L h) t ^ 2 ≤ 2 * K ^ 2 / h := by
  have hder : ∀ t, deriv (r3d_prof L h) t = deriv (r3d_bump (r := 1) one_pos) ((t + L) / h) * (1 / h) :=
    fun t => (r3d_prof_hasDerivAt L h t).deriv
  have hcont : Continuous (deriv (r3d_prof L h)) :=
    (r3d_prof_contDiff L h).continuous_deriv (by simp)
  have hc2 : HasCompactSupport (fun t => deriv (r3d_prof L h) t ^ 2) := by
    refine IsCompact.of_isClosed_subset (isCompact_Icc (a := -L - h) (b := -L + h))
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    have h1 : ¬ h < |t + L| := by
      intro hlt
      apply ht
      have : 1 < |(t + L) / h| := by
        rw [abs_div, abs_of_pos hh, lt_div_iff₀ hh]
        linarith only [hlt]
      simp [hder t, r3d_deriv_bump_zero this]
    push Not at h1
    rw [abs_le] at h1
    exact ⟨by linarith only [h1.1], by linarith only [h1.2]⟩
  have hc : Integrable (fun t => deriv (r3d_prof L h) t ^ 2) :=
    r3d_integrable_of_cont (hcont.pow 2) hc2
  have h0 := r3d_setIntegral_le_of_support (S := Set.Ioo (-L) L) (C := (K / h) ^ 2)
    (J := Set.Icc (-L - h) (-L + h)) measurableSet_Icc (by simp) hc (fun t => sq_nonneg _)
    (fun t ht => by
      have : h < |t + L| := by
        by_contra hne
        apply ht
        push Not at hne
        rw [abs_le] at hne
        exact ⟨by linarith only [hne.1], by linarith only [hne.2]⟩
      have h1 : 1 < |(t + L) / h| := by
        rw [abs_div, abs_of_pos hh, lt_div_iff₀ hh]
        linarith only [this]
      simp [hder t, r3d_deriv_bump_zero h1]) (fun t => by
      rw [hder t]
      have : |deriv (r3d_bump (r := 1) one_pos) ((t + L) / h) * (1 / h)| ≤ K / h := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / h), div_eq_mul_one_div K h]
        exact mul_le_mul_of_nonneg_right (hKb _) (by positivity)
      calc (deriv (r3d_bump (r := 1) one_pos) ((t + L) / h) * (1 / h)) ^ 2
          = |deriv (r3d_bump (r := 1) one_pos) ((t + L) / h) * (1 / h)| ^ 2 := (sq_abs _).symm
        _ ≤ (K / h) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith only [hh])] at h0
  have e : (-L + h - (-L - h)) = 2 * h := by ring
  rw [e] at h0
  have e2 : (K / h) ^ 2 * (2 * h) = 2 * K ^ 2 / h := by field_simp
  linarith only [h0, e2]

end SuperdiffusionCLT.Section7
