/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit
public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pG
public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Cutoffs times the normal coordinate are zero-trace on the cube

For the cube `openCubeSet (originCube d m)` and the face `x e = -3^m/2`, a smooth compactly supported
cutoff `η` inside the window around the face centre, multiplied by the normal coordinate
`n x = x e + 3^m/2`, belongs to `H¹₀` of the cube (the product vanishes on the face, and is
approximated by cutting off the thin layers `n < 2/(k+1)`).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3c_deriv_smoothTransition_bdd : ∃ B : ℝ, ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    ContDiff.continuous_deriv (Real.smoothTransition.contDiff (n := 1)) le_rfl
  have hk : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1)) fun t ht => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
        filter_upwards [Iio_mem_nhds h] with s hs
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
      rw [this.deriv_eq]; simp
    · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
        filter_upwards [Ioi_mem_nhds h] with s hs
        exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
      rw [this.deriv_eq]; simp
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hk
  exact ⟨B, fun t => by simpa using hB t⟩

/-- Normal coordinate to the flat face of the cube `originCube d m` through `-(3^m/2) e`. -/
noncomputable def r3c_nrm (e : Fin d) (m : ℤ) (x : Vec d) : ℝ := x e + (3 : ℝ) ^ m / 2

/-- The centre of the face `x e = -3^m/2`. -/
noncomputable def r3c_z0 (e : Fin d) (m : ℤ) : Vec d :=
  fun i => if i = e then -((3 : ℝ) ^ m / 2) else 0

theorem contDiff_r3c_nrm (e : Fin d) (m : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (r3c_nrm e m) := by
  unfold r3c_nrm
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) e).contDiff).add contDiff_const

theorem hasFDerivAt_r3c_nrm (e : Fin d) (m : ℤ) (x : Vec d) :
    HasFDerivAt (r3c_nrm e m) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) e) x := by
  unfold r3c_nrm
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) e).hasFDerivAt.add_const _

/-- The smooth cutoff in the normal variable: `0` for `n ≤ 1/(k+1)`, `1` for `n ≥ 2/(k+1)`. -/
noncomputable def r3c_theta (e : Fin d) (m : ℤ) (k : ℕ) (x : Vec d) : ℝ :=
  Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1)

theorem contDiff_r3c_theta (e : Fin d) (m : ℤ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (r3c_theta e m k) := by
  unfold r3c_theta
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_r3c_nrm e m)).sub contDiff_const)

theorem r3c_theta_zero (e : Fin d) (m : ℤ) (k : ℕ) {x : Vec d}
    (hx : r3c_nrm e m x ≤ 1 / ((k : ℝ) + 1)) : r3c_theta e m k x = 0 := by
  unfold r3c_theta
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hx hk.le
  rw [mul_one_div_cancel hk.ne'] at this
  linarith only [this]

theorem r3c_theta_one (e : Fin d) (m : ℤ) (k : ℕ) {x : Vec d}
    (hx : 2 / ((k : ℝ) + 1) ≤ r3c_nrm e m x) : r3c_theta e m k x = 1 := by
  unfold r3c_theta
  apply Real.smoothTransition.one_of_one_le
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hx hk.le
  rw [show ((k : ℝ) + 1) * (2 / ((k : ℝ) + 1)) = 2 by field_simp] at this
  linarith only [this]

theorem r3c_theta_01 (e : Fin d) (m : ℤ) (k : ℕ) (x : Vec d) :
    0 ≤ r3c_theta e m k x ∧ r3c_theta e m k x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem r3c_fderiv_theta (e : Fin d) (m : ℤ) (k : ℕ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (r3c_theta e m k) x (basisVec i) =
      deriv Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1) *
        (((k : ℝ) + 1) * (if i = e then 1 else 0)) := by
  have h1 : HasFDerivAt (fun x => ((k : ℝ) + 1) * r3c_nrm e m x - 1)
      (((k : ℝ) + 1) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) e)) x :=
    ((hasFDerivAt_r3c_nrm e m x).const_mul _).sub_const _
  have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (((k : ℝ) + 1) * r3c_nrm e m x - 1)).hasDerivAt.comp_hasFDerivAt x h1
  unfold r3c_theta
  rw [show (fun x => Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1)) =
    Real.smoothTransition ∘ fun x => ((k : ℝ) + 1) * r3c_nrm e m x - 1 from rfl, h2.fderiv]
  simp only [basisVec, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, Pi.single_apply]
  by_cases h : e = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem r3c_fderiv_theta_eq_zero (e : Fin d) (m : ℤ) (k : ℕ) (x : Vec d) (i : Fin d)
    (hx : 2 / ((k : ℝ) + 1) < r3c_nrm e m x) : fderiv ℝ (r3c_theta e m k) x (basisVec i) = 0 := by
  rw [r3c_fderiv_theta]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : (1 : ℝ) < ((k : ℝ) + 1) * r3c_nrm e m x - 1 := by
    have := mul_lt_mul_of_pos_left hx hk
    rw [show ((k : ℝ) + 1) * (2 / ((k : ℝ) + 1)) = 2 by field_simp] at this
    linarith only [this]
  have : Real.smoothTransition =ᶠ[𝓝 (((k : ℝ) + 1) * r3c_nrm e m x - 1)] fun _ => (1:ℝ) := by
    filter_upwards [Ioi_mem_nhds h1] with s hs
    exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
  rw [this.deriv_eq]; simp


theorem r3c_nrm_pos_of_mem (e : Fin d) (m : ℤ) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    0 < r3c_nrm e m x := by
  have := (hc_mem_openCubeSet_originCube_iff m x).1 hx e
  unfold r3c_nrm
  linarith only [this.1]

theorem measurableSet_r3c_strip (e : Fin d) (m : ℤ) (k : ℕ) :
    MeasurableSet {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)} :=
  measurableSet_le (contDiff_r3c_nrm e m).continuous.measurable measurable_const

theorem r3c_volume_openCubeSet_lt_top (m : ℤ) : volume (openCubeSet (originCube d m)) < ⊤ := by
  rw [p12d_openCubeSet_eq_axisCube]
  exact (isBoundedDomain_axisCube _ _).isBounded.measure_lt_top

/-- A sequence bounded by a constant on the thin strips `n ≤ 2/(k+1)` and vanishing elsewhere
tends to zero in `L²` of the cube. -/
theorem r3c_tendsto_strip (e : Fin d) (m : ℤ) {B : ℝ} (f : ℕ → Vec d → ℝ)
    (hfm : ∀ k, AEStronglyMeasurable (f k) (volume.restrict (openCubeSet (originCube d m))))
    (hf : ∀ k, ∀ x ∈ openCubeSet (originCube d m),
      ‖f k x‖ ≤ B * {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x) :
    Tendsto (fun k => eLpNorm (f k) 2 (volume.restrict (openCubeSet (originCube d m)))) atTop
      (𝓝 0) := by
  set D := openCubeSet (originCube d m) with hD
  have hDo : MeasurableSet D := (isOpen_openCubeSet _).measurableSet
  set S : ℕ → Set (Vec d) := fun k => {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)} with hS
  have hSm : ∀ k, MeasurableSet (S k) := measurableSet_r3c_strip e m
  have hanti : Antitone S := by
    intro k k' hkk' y hy
    simp only [hS, Set.mem_ofPred_eq] at hy ⊢
    refine hy.trans ?_
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkk : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by
      have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
      linarith only [this]
    exact div_le_div_of_nonneg_left (by norm_num) hk hkk
  have hfin : (volume.restrict D) (S 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Measure.restrict_apply_univ]; exact (r3c_volume_openCubeSet_lt_top m).ne)
      (measure_mono (Set.subset_univ _))
  have hlim := tendsto_measure_iInter_atTop (μ := volume.restrict D)
    (fun k => (hSm k).nullMeasurableSet) hanti ⟨0, hfin⟩
  have hint : (volume.restrict D) (⋂ k, S k) = 0 := by
    rw [Measure.restrict_apply' hDo]
    refine measure_mono_null (fun x hx => ?_) (measure_empty (μ := (volume : Measure (Vec d))))
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.mem_iInter, hS, Set.mem_ofPred_eq] at hx1
    have hpos := r3c_nrm_pos_of_mem e m hx2
    exfalso
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / r3c_nrm e m x)
    have h1 := hx1 k
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hpos] at hk
    rw [le_div_iff₀ hk0] at h1
    have h4 : r3c_nrm e m x * ((k : ℝ) + 1) = (k : ℝ) * r3c_nrm e m x + r3c_nrm e m x := by ring
    linarith only [hk, h1, h4, hpos]
  rw [hint] at hlim
  have h2 : Tendsto (fun k => ((volume.restrict D) (S k)) ^ (1 / (2 : ℝ≥0∞).toReal)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact this.comp hlim
  have h3 : Tendsto (fun k => ‖B‖ₑ * ((volume.restrict D) (S k)) ^ (1 / (2 : ℝ≥0∞).toReal)) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ‖B‖ₑ) h2 (Or.inr (by simp))
    rw [mul_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun k => bot_le)
    (fun k => ?_)
  have hmono : eLpNorm (f k) 2 (volume.restrict D) ≤
      eLpNorm ((S k).indicator (fun _ => B)) 2 (volume.restrict D) := by
    refine eLpNorm_mono_ae_real (hfm k) ?_
    filter_upwards [ae_restrict_mem hDo] with x hx
    have := hf k x hx
    by_cases hxS : x ∈ S k
    · have h1 : {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem hxS _
      rw [h1, mul_one] at this
      rw [Set.indicator_of_mem hxS]
      exact this
    · have h1 : {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem hxS _
      rw [h1, mul_zero] at this
      rw [Set.indicator_of_notMem hxS]
      exact this
  refine hmono.trans (le_of_eq ?_)
  rw [eLpNorm_indicator_const (hSm k).nullMeasurableSet (by norm_num) (by norm_num)]


theorem r3c_fderiv_mul_theta (e : Fin d) (m : ℤ) (k : ℕ) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y => g y * r3c_theta e m k y) x (basisVec i) =
      g x * fderiv ℝ (r3c_theta e m k) x (basisVec i) +
        r3c_theta e m k x * fderiv ℝ g x (basisVec i) := by
  have h1 : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ (r3c_theta e m k) x :=
    ((contDiff_r3c_theta e m k).differentiable (by simp)) x
  rw [fderiv_fun_mul h1 h2]
  simp

/-- Pointwise bounds for the difference of `g` and `g θ_k` and of their gradients. -/
theorem r3c_pointwise_bounds (e : Fin d) (m : ℤ) (k : ℕ) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {Mg B1 Bθ : ℝ} (x : Vec d) (hx : 0 < r3c_nrm e m x)
    (hgx : |g x| ≤ Mg * r3c_nrm e m x) (hB1 : ∀ i, |fderiv ℝ g x (basisVec i)| ≤ B1)
    (hBθ : ∀ t, |deriv Real.smoothTransition t| ≤ Bθ) (hMg : 0 ≤ Mg) (hB1' : 0 ≤ B1) (hBθ' : 0 ≤ Bθ) :
    ‖g x - g x * r3c_theta e m k x‖ ≤
        (2 * Mg + B1 + 2 * Mg * Bθ) *
          {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x ∧
      ∀ i, ‖fderiv ℝ g x (basisVec i) - fderiv ℝ (fun y => g y * r3c_theta e m k y) x (basisVec i)‖ ≤
        (2 * Mg + B1 + 2 * Mg * Bθ) *
          {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  by_cases hS : r3c_nrm e m x ≤ 2 / ((k : ℝ) + 1)
  · have hind : {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x = 1 :=
      Set.indicator_of_mem (show x ∈ {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)} from hS) _
    rw [hind, mul_one]
    have hθ := r3c_theta_01 e m k x
    have hn2 : (k + 1 : ℝ) * r3c_nrm e m x ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hS hk.le
      rwa [mul_div_cancel₀ _ hk.ne'] at this
    refine ⟨?_, fun i => ?_⟩
    · rw [Real.norm_eq_abs, ← mul_one_sub, abs_mul]
      have h1 : |1 - r3c_theta e m k x| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith only [hθ.1, hθ.2]
      have h2 : |g x| ≤ 2 * Mg := by
        have : Mg * ((k + 1 : ℝ) * r3c_nrm e m x) ≤ Mg * 2 := mul_le_mul_of_nonneg_left hn2 hMg
        have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have : Mg * r3c_nrm e m x ≤ Mg * ((k + 1 : ℝ) * r3c_nrm e m x) := by
          have : r3c_nrm e m x ≤ (k + 1 : ℝ) * r3c_nrm e m x := by
            nlinarith only [hk1, hx]
          exact mul_le_mul_of_nonneg_left this hMg
        linarith only [hgx, this, ‹Mg * ((k + 1 : ℝ) * r3c_nrm e m x) ≤ Mg * 2›]
      calc |g x| * |1 - r3c_theta e m k x| ≤ |g x| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ 2 * Mg := by linarith only [h2]
        _ ≤ 2 * Mg + B1 + 2 * Mg * Bθ := by
          have : 0 ≤ 2 * Mg * Bθ := by positivity
          linarith only [hB1', this]
    · rw [r3c_fderiv_mul_theta e m k hg x i, r3c_fderiv_theta, Real.norm_eq_abs]
      have e1 : fderiv ℝ g x (basisVec i) -
          (g x * (deriv Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1) *
            (((k : ℝ) + 1) * (if i = e then 1 else 0))) +
            r3c_theta e m k x * fderiv ℝ g x (basisVec i)) =
          (1 - r3c_theta e m k x) * fderiv ℝ g x (basisVec i) -
            g x * (deriv Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1) *
              (((k : ℝ) + 1) * (if i = e then 1 else 0))) := by ring
      rw [e1]
      refine (abs_sub _ _).trans ?_
      have h1 : |(1 - r3c_theta e m k x) * fderiv ℝ g x (basisVec i)| ≤ B1 := by
        rw [abs_mul]
        have h1' : |1 - r3c_theta e m k x| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith only [hθ.1, hθ.2]
        calc |1 - r3c_theta e m k x| * |fderiv ℝ g x (basisVec i)| ≤ 1 * B1 :=
              mul_le_mul h1' (hB1 i) (abs_nonneg _) zero_le_one
          _ = B1 := one_mul _
      have h2 : |g x * (deriv Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1) *
          (((k : ℝ) + 1) * (if i = e then 1 else 0)))| ≤ 2 * Mg * Bθ := by
        rw [abs_mul, abs_mul, abs_mul]
        have hi : |(if i = e then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
        have hkk : |(k : ℝ) + 1| = (k : ℝ) + 1 := abs_of_pos hk
        have h3 : |deriv Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1)| *
            (|(k : ℝ) + 1| * |(if i = e then (1 : ℝ) else 0)|) ≤ Bθ * ((k : ℝ) + 1) := by
          rw [hkk]
          have : (k : ℝ) + 1 ≥ 0 := hk.le
          calc _ ≤ Bθ * (((k : ℝ) + 1) * 1) := by
                refine mul_le_mul (hBθ _) (mul_le_mul_of_nonneg_left hi this) (by positivity) hBθ'
            _ = Bθ * ((k : ℝ) + 1) := by ring
        calc |g x| * (|deriv Real.smoothTransition (((k : ℝ) + 1) * r3c_nrm e m x - 1)| *
              (|(k : ℝ) + 1| * |(if i = e then (1 : ℝ) else 0)|))
            ≤ (Mg * r3c_nrm e m x) * (Bθ * ((k : ℝ) + 1)) :=
              mul_le_mul hgx h3 (by positivity) (by positivity)
          _ = Mg * Bθ * ((k + 1 : ℝ) * r3c_nrm e m x) := by ring
          _ ≤ Mg * Bθ * 2 := mul_le_mul_of_nonneg_left hn2 (by positivity)
          _ = 2 * Mg * Bθ := by ring
      have : 0 ≤ 2 * Mg := by positivity
      linarith only [h1, h2, this]
  · have hind : {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem (show x ∉ {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)} from hS) _
    rw [hind, mul_zero]
    have hlt : 2 / ((k : ℝ) + 1) < r3c_nrm e m x := not_le.1 hS
    have hθ1 := r3c_theta_one e m k hlt.le
    refine ⟨?_, fun i => ?_⟩
    · rw [hθ1]; simp
    · rw [r3c_fderiv_mul_theta e m k hg x i, r3c_fderiv_theta_eq_zero e m k x i hlt, hθ1]; simp


/-- **A smooth cutoff times the normal coordinate is `H¹₀` of the cube.**  For `η` smooth with compact
support in the window `{|x - z₀|_∞ < 3^m/2}` around the centre of the face `x e = -3^m/2`, the
function `η · n`, `n x = x e + 3^m/2`, is in `H¹₀(openCubeSet (originCube d m))`. -/
theorem r3c_memH10_mul_nrm (e : Fin d) (m : ℤ) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηT : tsupport η ⊆ {x | ∀ i, |x i - r3c_z0 e m i| < (3 : ℝ) ^ m / 2}) :
    MemH10 (openCubeSet (originCube d m)) (fun x => η x * r3c_nrm e m x) := by
  set U := openCubeSet (originCube d m) with hUdef
  have hU : IsOpen U := isOpen_openCubeSet _
  set g1 : Vec d → ℝ := fun x => η x * r3c_nrm e m x with hg1def
  have hg1 : ContDiff ℝ (⊤ : ℕ∞) g1 := hη.mul (contDiff_r3c_nrm e m)
  have hg1c : HasCompactSupport g1 := hηc.mul_right
  obtain ⟨Mη₀, hMη₀⟩ := hη.continuous.bounded_above_of_compact_support hηc
  set Mη : ℝ := |Mη₀| with hMη
  have hMη0 : 0 ≤ Mη := abs_nonneg _
  have hMη' : ∀ x, |η x| ≤ Mη := fun x => by
    have := hMη₀ x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hB1ex : ∀ i : Fin d, ∃ B : ℝ, ∀ x, ‖fderiv ℝ g1 x (basisVec i)‖ ≤ B := fun i => by
    have hc : Continuous (fun x => fderiv ℝ g1 x (basisVec i)) := by
      simpa using (hg1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hk : HasCompactSupport (fun x => fderiv ℝ g1 x (basisVec i)) := by
      simpa using hg1c.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact hc.bounded_above_of_compact_support hk
  choose Bi hBi using hB1ex
  set B1 : ℝ := ∑ i, |Bi i| with hB1
  have hB1' : ∀ x i, |fderiv ℝ g1 x (basisVec i)| ≤ B1 := fun x i => by
    have h1 := hBi i x
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun i => |Bi i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hB10 : 0 ≤ B1 := Finset.sum_nonneg fun i _ => abs_nonneg _
  obtain ⟨Bθ₀, hBθ₀⟩ := r3c_deriv_smoothTransition_bdd
  set Bθ : ℝ := |Bθ₀| with hBθ
  have hBθ0 : 0 ≤ Bθ := abs_nonneg _
  have hBθ' : ∀ t, |deriv Real.smoothTransition t| ≤ Bθ := fun t => (hBθ₀ t).trans (le_abs_self _)
  set B : ℝ := 2 * Mη + B1 + 2 * Mη * Bθ with hB
  -- the approximants
  set F : ℕ → Vec d → ℝ := fun k x => g1 x * r3c_theta e m k x with hF
  have hFs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (F k) := fun k => hg1.mul (contDiff_r3c_theta e m k)
  have hFc : ∀ k, HasCompactSupport (F k) := fun k => hg1c.mul_right
  have hFU : ∀ k, tsupport (F k) ⊆ U := by
    intro k x hx
    have h1 : x ∈ tsupport g1 := tsupport_mul_subset_left hx
    have h2 : x ∈ tsupport (r3c_theta e m k) := tsupport_mul_subset_right hx
    have h3 : x ∈ tsupport η := tsupport_mul_subset_left (f := η) (g := r3c_nrm e m) h1
    have h4 : 1 / ((k : ℝ) + 1) ≤ r3c_nrm e m x := by
      have hcl : tsupport (r3c_theta e m k) ⊆ {y | 1 / ((k : ℝ) + 1) ≤ r3c_nrm e m y} := by
        refine closure_minimal (fun y hy => ?_) (isClosed_le continuous_const
          (contDiff_r3c_nrm e m).continuous)
        by_contra hlt
        exact hy (r3c_theta_zero e m k (not_le.1 hlt).le)
      exact hcl h2
    have hw := hηT h3
    rw [hUdef, hc_mem_openCubeSet_originCube_iff]
    intro i
    have hwi := hw i
    rw [abs_lt] at hwi
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    by_cases hi : i = e
    · subst hi
      simp only [r3c_z0, ite_true] at hwi
      unfold r3c_nrm at h4
      constructor <;> linarith only [hwi.1, hwi.2, h4, hk, zpow_pos (by norm_num : (0 : ℝ) < 3) m]
    · simp only [r3c_z0, hi, ite_false, sub_zero] at hwi
      exact hwi
  let Fh : ℕ → H10Function U := fun k => H10Function.ofContDiff hU (hFs k) (hFc k) (hFU k)
  let f0 : H1Function U := H1Function.ofContDiff hU (hg1.of_le (by simp)) hg1c
  have hmeas0 : ∀ k, Continuous (fun x => g1 x - g1 x * r3c_theta e m k x) := fun k =>
    hg1.continuous.sub (hg1.continuous.mul (contDiff_r3c_theta e m k).continuous)
  have hbd : ∀ k, ∀ x ∈ U,
      (‖g1 x - g1 x * r3c_theta e m k x‖ ≤ B *
          {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x) ∧
      ∀ i, ‖fderiv ℝ g1 x (basisVec i) - fderiv ℝ (F k) x (basisVec i)‖ ≤ B *
          {y : Vec d | r3c_nrm e m y ≤ 2 / ((k : ℝ) + 1)}.indicator (fun _ => (1 : ℝ)) x := by
    intro k x hx
    have hpos := r3c_nrm_pos_of_mem e m hx
    have hgx : |g1 x| ≤ Mη * r3c_nrm e m x := by
      show |η x * r3c_nrm e m x| ≤ Mη * r3c_nrm e m x
      rw [abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right (hMη' x) hpos.le
    exact r3c_pointwise_bounds e m k hg1 (Mg := Mη) (B1 := B1) (Bθ := Bθ) x hpos hgx (hB1' x) hBθ'
      hMη0 hB10 hBθ0
  refine memH10_of_tendsto_H1 hU f0 (fun k => (Fh k).toH1Function) (fun k => ⟨Fh k, rfl⟩) ?_ ?_
  · exact r3c_tendsto_strip e m (B := B) (fun k x => g1 x - g1 x * r3c_theta e m k x)
      (fun k => (hmeas0 k).aestronglyMeasurable) (fun k x hx => (hbd k x hx).1)
  · intro i
    refine r3c_tendsto_strip e m (B := B)
      (fun k x => fderiv ℝ g1 x (basisVec i) - fderiv ℝ (F k) x (basisVec i)) (fun k => ?_)
      (fun k x hx => (hbd k x hx).2 i)
    refine Continuous.aestronglyMeasurable ?_
    have c1 : Continuous (fun x => fderiv ℝ g1 x (basisVec i)) := by
      simpa using (hg1.continuous_fderiv (by simp)).clm_apply continuous_const
    have c2 : Continuous (fun x => fderiv ℝ (F k) x (basisVec i)) := by
      simpa using ((hFs k).continuous_fderiv (by simp)).clm_apply continuous_const
    exact c1.sub c2

end SuperdiffusionCLT.Section7
