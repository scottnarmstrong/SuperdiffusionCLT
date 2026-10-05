/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


/-!
# Morrey's inequality on bounded convex sets

For `u` of class `C¹` on a finite-dimensional real normed space with an additive Haar measure,
`K` bounded, convex, measurable of positive measure, and `p > max 1 d`:
`|u x - u_K| ≤ (1 - d/p)⁻¹ * δ * (μ(K)⁻¹ ∫_K ‖∇u‖^p)^(1/p)` for `x ∈ K`, where `δ` bounds the
distances from `x` to points of `K`; consequently the oscillation of `u` on `K` is at most twice
this. The proof is the potential estimate along the homotheties `y ↦ x + t (y - x)` followed by
Hölder's inequality.

The carrier is `C¹` functions (`ContDiff ℝ 1 u`); passing to `W^{1,p}` representatives is a
separate density step.
-/

@[expose] public section

open MeasureTheory Set

namespace SuperdiffusionCLT.Section7

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem enorm_sub_le_lintegral_fderiv {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x y : E) :
    ENNReal.ofReal |u y - u x| ≤
      ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) := by
  set g : ℝ → ℝ := fun t => u (x + t • (y - x)) with hg
  have hline : ∀ t, HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hd : ∀ t, HasDerivAt g (fderiv ℝ u (x + t • (y - x)) (y - x)) t := fun t =>
    ((hu.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt t (hline t)
  have hcont : Continuous fun t : ℝ => fderiv ℝ u (x + t • (y - x)) (y - x) := by
    have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
    have h2 : Continuous fun t : ℝ => x + t • (y - x) := by fun_prop
    exact (h1.comp h2).clm_apply continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)
  have h01 : g 1 - g 0 = u y - u x := by simp [hg]
  rw [h01] at hftc
  have hle : |u y - u x| ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖ := by
    rw [← hftc]
    have hnc : Continuous fun t : ℝ => ‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖ := by
      have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
      have h2 : Continuous fun t : ℝ => x + t • (y - x) := by fun_prop
      exact ((h1.comp h2).norm).mul continuous_const
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine intervalIntegral.integral_mono_on zero_le_one
      (hcont.abs.intervalIntegrable 0 1) (hnc.intervalIntegrable 0 1) ?_
    intro t _
    simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (fderiv ℝ u (x + t • (y - x))) (y - x)
  have hnc : Continuous fun t : ℝ => ‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖ := by
    have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
    have h2 : Continuous fun t : ℝ => x + t • (y - x) := by fun_prop
    exact ((h1.comp h2).norm).mul continuous_const
  calc ENNReal.ofReal |u y - u x|
      ≤ ENNReal.ofReal (∫ t in (0:ℝ)..1, ‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) :=
        ENNReal.ofReal_le_ofReal hle
    _ = _ := by
        rw [intervalIntegral.integral_of_le zero_le_one,
          ofReal_integral_eq_lintegral_ofReal]
        · exact (hnc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        · exact Filter.Eventually.of_forall fun t => by positivity

end Line

section Potential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The homothety of ratio `t` centred at `x`, as a homeomorphism. -/
noncomputable def homothetyHomeo (x : E) {t : ℝ} (ht : t ≠ 0) : E ≃ₜ E :=
  (Homeomorph.smulOfNeZero t ht).trans (Homeomorph.addLeft (x - t • x))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem homothetyHomeo_apply (x : E) {t : ℝ} (ht : t ≠ 0) (y : E) :
    homothetyHomeo x ht y = x + t • (y - x) := by
  simp [homothetyHomeo, smul_sub]; abel

theorem map_homothety (x : E) {t : ℝ} (ht : t ≠ 0) :
    μ.map (homothetyHomeo x ht) = ENNReal.ofReal |(t ^ Module.finrank ℝ E)⁻¹| • μ := by
  have : (homothetyHomeo x ht : E → E) =
      (fun w => (x - t • x) + w) ∘ (fun y => t • y) := by
    funext y; simp [homothetyHomeo, Homeomorph.smulOfNeZero]
  rw [this, ← Measure.map_map (measurable_const_add _) (measurable_const_smul t),
    Measure.map_addHaar_smul μ ht, Measure.map_smul, MeasureTheory.map_add_left_eq_self]
  exact (measurable_const_add _).aemeasurable

theorem lintegral_comp_homothety (x : E) {t : ℝ} (ht : t ≠ 0) (F : E → ENNReal) (hF : Measurable F)
    {K : Set E} (hK : MeasurableSet K) :
    ∫⁻ y in K, F (x + t • (y - x)) ∂μ =
      ENNReal.ofReal |(t ^ Module.finrank ℝ E)⁻¹| *
        ∫⁻ z in (fun a => x + t • (a - x)) '' K, F z ∂μ := by
  have hemb := (homothetyHomeo x ht).measurableEmbedding
  have h1 := setLIntegral_map (μ := μ) (hemb.measurableSet_image.2 hK) hF
    hemb.measurable
  rw [map_homothety μ x ht, Measure.restrict_smul, lintegral_smul_measure,
    Homeomorph.preimage_image] at h1
  simp only [homothetyHomeo_apply] at h1
  rw [← h1, smul_eq_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem setLIntegral_le_holder (S : Set E) {f : E → ENNReal} (hf : Measurable f)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫⁻ z in S, f z ∂μ ≤ (∫⁻ z in S, f z ^ p ∂μ) ^ (1 / p) * μ S ^ (1 / q) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq hf.aemeasurable
    (g := fun _ => 1) aemeasurable_const
  simpa using h

theorem lintegral_homothety_le {u : E → ℝ} (hu : ContDiff ℝ 1 u) {K : Set E}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) {x : E} (hx : x ∈ K) {δ : ℝ}
    (hδ : ∀ y ∈ K, ‖y - x‖ ≤ δ) {p q : ℝ} (hpq : p.HolderConjugate q) {t : ℝ}
    (ht : t ∈ Ioc (0:ℝ) 1) :
    ∫⁻ y in K, ENNReal.ofReal (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) ∂μ ≤
      ENNReal.ofReal δ * (∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) ^ (1 / p) *
        μ K ^ (1 / q) * ENNReal.ofReal (t ^ (-((Module.finrank ℝ E : ℝ) / p))) := by
  have ht0 : t ≠ 0 := ht.1.ne'
  have hGm : Measurable fun z => ‖fderiv ℝ u z‖ₑ :=
    (hu.continuous_fderiv one_ne_zero).enorm.measurable
  have hmono : ∫⁻ y in K, ENNReal.ofReal (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) ∂μ ≤
      ∫⁻ y in K, ENNReal.ofReal δ * ‖fderiv ℝ u (x + t • (y - x))‖ₑ ∂μ := by
    refine lintegral_mono_ae ((ae_restrict_iff' hK).2 (Filter.Eventually.of_forall fun y hy => ?_))
    rw [ENNReal.ofReal_mul (by positivity), ofReal_norm, mul_comm]
    gcongr
    exact hδ y hy
  refine hmono.trans ?_
  have hcm : Measurable fun y : E => ‖fderiv ℝ u (x + t • (y - x))‖ₑ :=
    hGm.comp (by fun_prop)
  rw [lintegral_const_mul _ hcm, lintegral_comp_homothety μ x ht0
    (fun z => ‖fderiv ℝ u z‖ₑ) hGm hK]
  set S : Set E := (fun a => x + t • (a - x)) '' K with hS
  have hSK : S ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hKc.add_smul_sub_mem hx hy ⟨ht.1.le, ht.2⟩
  have hSm : μ S = ENNReal.ofReal |t ^ Module.finrank ℝ E| * μ K := by
    have : (fun a => x + t • (a - x)) = ⇑(AffineMap.homothety x t) := by
      funext a; simp [AffineMap.homothety_apply, add_comm]
    rw [hS, this, Measure.addHaar_image_homothety]
  have hH := setLIntegral_le_holder μ S hGm hpq
  have hA : (∫⁻ z in S, ‖fderiv ℝ u z‖ₑ ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) ^ (1 / p) :=
    ENNReal.rpow_le_rpow (lintegral_mono_set hSK) (by have := hpq.pos; positivity)
  have hq0 : 0 ≤ 1 / q := by have := hpq.symm.pos; positivity
  set n := Module.finrank ℝ E with hn
  have ha : 0 < t ^ n := pow_pos ht.1 n
  have key : ENNReal.ofReal |(t ^ n)⁻¹| * μ S ^ (1 / q) =
      μ K ^ (1 / q) * ENNReal.ofReal (t ^ (-((n : ℝ) / p))) := by
    rw [hSm, ENNReal.mul_rpow_of_nonneg _ _ hq0, abs_of_pos ha, abs_of_pos (inv_pos.2 ha),
      ENNReal.ofReal_rpow_of_pos ha, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_pos.2 ha).le, mul_comm]
    congr 2
    have hpq1 : 1 / q = 1 - 1 / p := by linarith only [hpq.inv_add_inv_eq_one, one_div p, one_div q]
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.1.le, ← Real.rpow_mul ht.1.le,
      ← Real.rpow_add ht.1, hpq1]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal δ * (ENNReal.ofReal |(t ^ n)⁻¹| * ∫⁻ z in S, ‖fderiv ℝ u z‖ₑ ∂μ)
      ≤ ENNReal.ofReal δ * (ENNReal.ofReal |(t ^ n)⁻¹| *
          ((∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) ^ (1 / p) * μ S ^ (1 / q))) := by
        gcongr
        exact hH.trans (by gcongr)
    _ = ENNReal.ofReal δ * (∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) ^ (1 / p) *
        (ENNReal.ofReal |(t ^ n)⁻¹| * μ S ^ (1 / q)) := by ring
    _ = _ := by rw [key]; ring

theorem lintegral_rpow_neg_Ioc {r : ℝ} (hr : -1 < r) :
    ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (1 / (r + 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have h := integral_rpow (a := (0:ℝ)) (b := 1) (r := r) (Or.inl hr)
  have hr1 : r + 1 ≠ 0 := (by linarith only [hr] : 0 < r + 1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le zero_le_one, h, Real.zero_rpow hr1]
    simp
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
      Real.rpow_nonneg ht.1.le r)

theorem lintegral_sub_le {u : E → ℝ} (hu : ContDiff ℝ 1 u) {K : Set E}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) {x : E} (hx : x ∈ K) {δ : ℝ}
    (hδ : ∀ y ∈ K, ‖y - x‖ ≤ δ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hd : (Module.finrank ℝ E : ℝ) < p) :
    ∫⁻ y in K, ENNReal.ofReal |u y - u x| ∂μ ≤
      ENNReal.ofReal δ * (∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) ^ (1 / p) *
        μ K ^ (1 / q) * ENNReal.ofReal (1 / (1 - (Module.finrank ℝ E : ℝ) / p)) := by
  have hp := hpq.pos
  have hr : -1 < -((Module.finrank ℝ E : ℝ) / p) := by
    have : (Module.finrank ℝ E : ℝ) / p < 1 := (div_lt_one hp).2 hd
    linarith only [this]
  have hcont : Continuous fun yt : E × ℝ => ENNReal.ofReal
      (‖fderiv ℝ u (x + yt.2 • (yt.1 - x))‖ * ‖yt.1 - x‖) := by
    have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
    exact ENNReal.continuous_ofReal.comp
      ((h1.comp (by fun_prop)).norm.mul (by fun_prop))
  calc ∫⁻ y in K, ENNReal.ofReal |u y - u x| ∂μ
      ≤ ∫⁻ y in K, ∫⁻ t in Ioc (0:ℝ) 1,
          ENNReal.ofReal (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) ∂volume ∂μ :=
        lintegral_mono fun y => enorm_sub_le_lintegral_fderiv hu x y
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ y in K,
          ENNReal.ofReal (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) ∂μ ∂volume :=
        lintegral_lintegral_swap (f := fun y t => ENNReal.ofReal
          (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖)) hcont.measurable.aemeasurable
    _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal δ * (∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ) ^ (1 / p) *
          μ K ^ (1 / q) * ENNReal.ofReal (t ^ (-((Module.finrank ℝ E : ℝ) / p))) :=
        setLIntegral_mono' measurableSet_Ioc fun t ht =>
          lintegral_homothety_le μ hu hK hKc hx hδ hpq ht
    _ = _ := by
        rw [lintegral_const_mul'' _ (by fun_prop), lintegral_rpow_neg_Ioc hr]
        congr 3
        ring

theorem abs_sub_average_le {u : E → ℝ} (hu : ContDiff ℝ 1 u) {K : Set E}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : μ K ≠ 0) {x : E} (hx : x ∈ K) {δ : ℝ} (hδ : ∀ y ∈ K, ‖y - x‖ ≤ δ)
    {p : ℝ} (hp1 : 1 < p) (hd : (Module.finrank ℝ E : ℝ) < p) :
    |u x - (μ K).toReal⁻¹ * ∫ y in K, u y ∂μ| ≤
      1 / (1 - (Module.finrank ℝ E : ℝ) / p) * δ *
        ((μ K).toReal⁻¹ * ∫ y in K, ‖fderiv ℝ u y‖ ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith only [hp1]
  obtain ⟨q, hpq⟩ : ∃ q, p.HolderConjugate q := ⟨_, Real.HolderConjugate.conjExponent hp1⟩
  have hpq1 : 1 / q = 1 - 1 / p := by linarith only [hpq.inv_add_inv_eq_one, one_div p, one_div q]
  have hKfin : μ K < ⊤ := hKb.measure_lt_top
  have hcl : IsCompact (closure K) := hKb.isCompact_closure
  have hm : 0 < (μ K).toReal := ENNReal.toReal_pos hK0 hKfin.ne
  set m := (μ K).toReal with hmdef
  have hGc : Continuous fun y => ‖fderiv ℝ u y‖ :=
    (hu.continuous_fderiv one_ne_zero).norm
  have hGint : IntegrableOn (fun y => ‖fderiv ℝ u y‖ ^ p) K μ :=
    ((hGc.rpow_const (fun _ => Or.inr hp0.le)).continuousOn.integrableOn_compact hcl).mono_set
      subset_closure
  have huint : IntegrableOn u K μ :=
    (hu.continuous.continuousOn.integrableOn_compact hcl).mono_set subset_closure
  set Gr := ∫ y in K, ‖fderiv ℝ u y‖ ^ p ∂μ with hGr
  have hGr0 : 0 ≤ Gr := setIntegral_nonneg hK fun y _ => by positivity
  have hGeq : ∫⁻ y in K, ‖fderiv ℝ u y‖ₑ ^ p ∂μ = ENNReal.ofReal Gr := by
    rw [hGr, ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall fun y => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ofReal_norm]
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ x hx)
  have hhd : (Module.finrank ℝ E : ℝ) / p < 1 := (div_lt_one hp0).2 hd
  have hc : 0 < 1 / (1 - (Module.finrank ℝ E : ℝ) / p) :=
    one_div_pos.2 (by linarith only [hhd])
  set c := 1 / (1 - (Module.finrank ℝ E : ℝ) / p) with hcdef
  have hD := lintegral_sub_le μ hu hK hKc hx hδ hpq hd
  rw [hGeq, ← hcdef] at hD
  have hμK : μ K = ENNReal.ofReal m := (ENNReal.ofReal_toReal hKfin.ne).symm
  rw [hμK, ENNReal.ofReal_rpow_of_pos hm,
    ENNReal.ofReal_rpow_of_nonneg hGr0 (by positivity), ← ENNReal.ofReal_mul hδ0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hD
  have habs : IntegrableOn (fun y => |u y - u x|) K μ :=
    (huint.sub (integrableOn_const hKfin.ne)).abs
  rw [← ofReal_integral_eq_lintegral_ofReal habs
    (Filter.Eventually.of_forall fun y => abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hD
  have hrw : u x - m⁻¹ * ∫ y in K, u y ∂μ = m⁻¹ * ∫ y in K, (u x - u y) ∂μ := by
    rw [integral_sub (μ := μ.restrict K) (f := fun _ => u x) (g := u)
      (integrableOn_const hKfin.ne) huint, setIntegral_const, smul_eq_mul]
    have hmr : μ.real K = m := rfl
    rw [hmr]
    field_simp
  have hle : |u x - m⁻¹ * ∫ y in K, u y ∂μ| ≤ m⁻¹ * ∫ y in K, |u y - u x| ∂μ := by
    rw [hrw, abs_mul, abs_of_pos (inv_pos.2 hm)]
    gcongr
    have h := norm_integral_le_integral_norm (μ := μ.restrict K) fun y => u x - u y
    simp only [Real.norm_eq_abs] at h
    simpa only [abs_sub_comm (u x)] using h
  refine hle.trans ?_
  have hmq : m ^ (1 / q) = m * (m⁻¹) ^ (1 / p) := by
    rw [hpq1, Real.rpow_sub hm, Real.rpow_one, Real.inv_rpow hm.le, div_eq_mul_inv]
  calc m⁻¹ * ∫ y in K, |u y - u x| ∂μ ≤ m⁻¹ * (δ * Gr ^ (1 / p) * m ^ (1 / q) * c) := by gcongr
    _ = _ := by
        rw [Real.mul_rpow (inv_pos.2 hm).le hGr0, hmq]
        field_simp

/-- **Morrey's inequality on a bounded convex set** (`C¹` functions): the oscillation of `u`
on `K` is at most `2 / (1 - d / p)` times the diameter bound `δ` times the volume-normalized
`L^p` norm of the gradient. -/
theorem abs_sub_le_morrey {u : E → ℝ} (hu : ContDiff ℝ 1 u) {K : Set E}
    (hK : MeasurableSet K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hK0 : μ K ≠ 0) {δ : ℝ} (hδ : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ δ)
    {p : ℝ} (hp1 : 1 < p) (hd : (Module.finrank ℝ E : ℝ) < p) {x y : E} (hx : x ∈ K)
    (hy : y ∈ K) :
    |u x - u y| ≤ 2 * (1 / (1 - (Module.finrank ℝ E : ℝ) / p)) * δ *
        ((μ K).toReal⁻¹ * ∫ z in K, ‖fderiv ℝ u z‖ ^ p ∂μ) ^ (1 / p) := by
  have h1 := abs_sub_average_le μ hu hK hKc hKb hK0 hx (fun b hb => hδ b hb x hx) hp1 hd
  have h2 := abs_sub_average_le μ hu hK hKc hKb hK0 hy (fun b hb => hδ b hb y hy) hp1 hd
  calc |u x - u y| = |(u x - (μ K).toReal⁻¹ * ∫ z in K, u z ∂μ) -
        (u y - (μ K).toReal⁻¹ * ∫ z in K, u z ∂μ)| := by ring_nf
    _ ≤ _ := (abs_sub _ _).trans (by linarith only [h1, h2])

/-- Satisfiability witness: the affine function `u = id` on `[0, 1] ⊂ ℝ` with `p = 2`. -/
example : |(0:ℝ) - 1| ≤ 2 * (1 / (1 - (Module.finrank ℝ ℝ : ℝ) / 2)) * 1 *
    ((volume (Icc (0:ℝ) 1)).toReal⁻¹ * ∫ z in Icc (0:ℝ) 1,
      ‖fderiv ℝ (fun t : ℝ => t) z‖ ^ (2:ℝ) ∂volume) ^ (1 / (2:ℝ)) :=
  abs_sub_le_morrey volume (u := fun t : ℝ => t) contDiff_id measurableSet_Icc
    (convex_Icc 0 1) (Metric.isBounded_Icc 0 1) (by simp) (δ := 1)
    (fun a ha b hb => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2])
    (by norm_num) (by simp) (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩

end Potential

end SuperdiffusionCLT.Section7
