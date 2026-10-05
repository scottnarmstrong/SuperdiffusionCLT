/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryDetB
public import Mathlib.Order.CompletePartialOrder

/-!
# The boundary estimate at one centre: calculus for the case analysis

Comparison of the flatness about a constant, about the average and about the datum, the
interior estimate on a cube contained in the domain, and the frontier point of a ball that leaves
the domain.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_cases_lipL2_def (S : Set (Vec d)) (f : Vec d → ℝ) :
    lipL2 S f = (eLpNorm f 2 (((volume S)⁻¹) • volume.restrict S)).toReal := rfl

/-- The average on a set of finite positive measure minus a constant is bounded by the
normalized `L²` norm. -/
theorem lip_cases_abs_avg_le {S : Set (Vec d)} (hS0 : volume S ≠ 0) (hS : volume S ≠ ⊤)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict S)) (c : ℝ) :
    |(⨍ w in S, u w) - c| ≤ lipL2 S (fun x => u x - c) := by
  have hfin : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.lt_top⟩
  have hv : (((volume S)⁻¹) • volume.restrict S) Set.univ = 1 := by
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hS0 hS
  have : IsProbabilityMeasure (((volume S)⁻¹) • volume.restrict S) := ⟨hv⟩
  set ν : Measure (Vec d) := ((volume S)⁻¹) • volume.restrict S with hν
  have hmem : MemLp (fun x => u x - c) 2 ν :=
    lip_lpBar_memLp hS0 (hu.sub (memLp_const c))
  have hint : Integrable (fun x => u x - c) ν := hmem.integrable (by norm_num)
  have hu1 : Integrable u ν := (lip_lpBar_memLp hS0 hu).integrable (by norm_num)
  have h1 : (⨍ w in S, u w) - c = ∫ x, (u x - c) ∂ν := by
    have h0 : (⨍ w in S, u w) = ∫ x, u x ∂ν := setAverage_eq' volume u S
    rw [h0, integral_sub hu1 (integrable_const c)]
    simp
  rw [h1, lip_cases_lipL2_def]
  have h2 : |∫ x, (u x - c) ∂ν| ≤ ∫ x, ‖u x - c‖ ∂ν := by
    have := norm_integral_le_integral_norm (μ := ν) (fun x => u x - c)
    simpa [Real.norm_eq_abs] using this
  have h3 : ∫ x, ‖u x - c‖ ∂ν = (eLpNorm (fun x => u x - c) 1 ν).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hint,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
    exact hint.1
  have h4 : eLpNorm (fun x => u x - c) 1 ν ≤ eLpNorm (fun x => u x - c) 2 ν :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  refine h2.trans (h3 ▸ ENNReal.toReal_mono hmem.eLpNorm_lt_top.ne h4)


/-- Moving the subtracted function costs the sup bound of the difference. -/
theorem lip_cases_shift {S : Set (Vec d)} (hS : MeasurableSet S) (hS0 : volume S ≠ 0)
    (hSt : volume S ≠ ⊤) {u h h' : Vec d → ℝ} (hh : Continuous h) (hh' : Continuous h')
    (hu : MemLp (fun x => u x - h x) 2 (volume.restrict S)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ S, |h x - h' x| ≤ B) :
    lipL2 S (fun x => u x - h' x) ≤ lipL2 S (fun x => u x - h x) + B := by
  have hfin : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSt.lt_top⟩
  have hae : ∀ᵐ x ∂volume.restrict S, |h x - h' x| ≤ B :=
    (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hb)
  have hd : MemLp (fun x => h x - h' x) 2 (volume.restrict S) :=
    MemLp.of_bound (hh.sub hh').aestronglyMeasurable B
      (hae.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have e : (fun x => u x - h' x) = fun x => (u x - h x) + (h x - h' x) := by
    funext x; ring
  rw [e]
  have h1 := lipL2_add_le hS0 hSt hu hd
  have h2 : lipL2 S (fun x => h x - h' x) ≤ B := lipL2_le_of_ae_abs_le hB hS0 hSt hae
  linarith only [h1, h2]

/-- The flatness about the average is at most twice the flatness about any constant. -/
theorem lip_cases_avg_le {S : Set (Vec d)} (hS : MeasurableSet S) (hS0 : volume S ≠ 0)
    (hSt : volume S ≠ ⊤) {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict S)) (c : ℝ) :
    lipL2 S (fun x => u x - ⨍ w in S, u w) ≤ 2 * lipL2 S (fun x => u x - c) := by
  have hfin : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSt.lt_top⟩
  have h := lip_cases_shift hS hS0 hSt (u := u) (h := fun _ => c)
    (h' := fun _ => ⨍ w in S, u w) continuous_const continuous_const
    (hu.sub (memLp_const c)) (abs_nonneg (c - ⨍ w in S, u w)) (fun x _ => le_rfl)
  have h2 := lip_cases_abs_avg_le hS0 hSt hu c
  rw [abs_sub_comm] at h2
  linarith only [h, h2]

/-- A function with `‖fderiv‖ ≤ G1` on a ball is `G1`-Lipschitz about the centre, up to the
closed ball. -/
theorem lip_cases_g_close {g : Vec d → ℝ} (hg : ContDiff ℝ 2 g) {z : Vec d} {r G1 : ℝ}
    (hr : 0 < r) (hDg : ∀ x ∈ Metric.ball z r, ‖fderiv ℝ g x‖ ≤ G1) :
    ∀ y, ‖y - z‖ ≤ r → |g y - g z| ≤ G1 * ‖y - z‖ := by
  have hcl : IsClosed {y : Vec d | |g y - g z| ≤ G1 * ‖y - z‖} :=
    isClosed_le ((hg.continuous.sub continuous_const).abs)
      (continuous_const.mul ((continuous_id.sub continuous_const).norm))
  have hb : Metric.ball z r ⊆ {y : Vec d | |g y - g z| ≤ G1 * ‖y - z‖} := by
    intro y hy
    have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g)
      (fun x _ => (hg.differentiable (by norm_num)).differentiableAt) hDg
      (convex_ball z r) hz hy
    simpa [Real.norm_eq_abs] using this
  intro y hy
  have : y ∈ closure (Metric.ball z r) := by
    rw [closure_ball z hr.ne']
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hy
  exact (closure_minimal hb hcl) this


/-- The interior estimate, for a solution on `(z + □_m) ∩ W`, from a cube `z + □_k ⊆ W`. -/
theorem lip_cases_int [NeZero d] {a : CoeffField d} {nu s Cin F : ℝ} {W : Set (Vec d)}
    {z : Vec d} {n k m : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) (hkW : shiftCube z (k : ℤ) ⊆ W)
    (hI : LipIntAt a nu s Cin z n k) (hF0 : 0 ≤ F) (f : Vec d → ℝ)
    (u : H1Function (shiftCube z (m : ℤ) ∩ W))
    (hsol : IsWeakSolutionOn a (shiftCube z (m : ℤ) ∩ W) u f (fun _ => 0))
    (hFae : ∀ᵐ x ∂volume.restrict (shiftCube z (m : ℤ) ∩ W), |f x| ≤ F) :
    (Real.sqrt s)⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (n : ℤ) ∩ W) u.grad +
        ((3 : ℝ)⁻¹) ^ n * lipL2 (shiftCube z (n : ℤ) ∩ W)
          (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ W, u.toFun w) ≤
      Cin * (((3 : ℝ)⁻¹) ^ k * lipL2 (shiftCube z (k : ℤ))
          (fun x => u.toFun x - ⨍ w in shiftCube z (k : ℤ), u.toFun w) +
        s⁻¹ * (3 : ℝ) ^ k * F) := by
  have hsub : shiftCube z (k : ℤ) ⊆ shiftCube z (m : ℤ) ∩ W :=
    Set.subset_inter (lip_bdry_approx_cube_mono z hkm) hkW
  have hu' := hI f F (u.restrict (lip_bdry_approx_isOpen_cube z k) hsub)
    (hsol.restrict' (lip_bdry_approx_isOpen_cube z k) hsub) hF0
    (ae_restrict_of_ae_restrict_of_subset hsub hFae)
  have e : shiftCube z (n : ℤ) ∩ W = shiftCube z (n : ℤ) :=
    Set.inter_eq_left.2 ((lip_bdry_approx_cube_mono z hnk).trans hkW)
  rw [e]
  exact hu'

/-- A ball around a point of the open set `W` that is not contained in `W` meets the
frontier. -/
theorem lip_cases_frontier {W : Set (Vec d)} (hW : IsOpen W) {z : Vec d} {r : ℝ} (hz : z ∈ W)
    (hr : 0 < r) (h : ¬ Metric.ball z r ⊆ W) : ∃ x ∈ frontier W, ‖x - z‖ < r := by
  by_contra hcon
  have hcon' : ∀ x ∈ frontier W, r ≤ ‖x - z‖ := fun x hx => not_lt.1 fun h' => hcon ⟨x, hx, h'⟩
  have hs : IsPreconnected (Metric.ball z r) := (convex_ball z r).isPreconnected
  obtain ⟨x, hx1, hx2⟩ := Set.not_subset.1 h
  have hxf : x ∉ frontier W := fun hf => by
    have := hcon' x hf
    rw [Metric.mem_ball, dist_eq_norm] at hx1
    linarith only [this, hx1]
  have hxc : x ∉ closure W := by
    intro hc
    rw [closure_eq_interior_union_frontier, hW.interior_eq] at hc
    rcases hc with hc | hc
    · exact hx2 hc
    · exact hxf hc
  have hcov : Metric.ball z r ⊆ W ∪ (closure W)ᶜ := by
    intro y hy
    by_cases hyW : y ∈ W
    · exact Or.inl hyW
    · refine Or.inr fun hyc => ?_
      rw [closure_eq_interior_union_frontier, hW.interior_eq] at hyc
      rcases hyc with hyc | hyc
      · exact hyW hyc
      · have := hcon' y hyc
        rw [Metric.mem_ball, dist_eq_norm] at hy
        linarith only [this, hy]
  obtain ⟨y, hy1, hy2, hy3⟩ := hs W (closure W)ᶜ hW isClosed_closure.isOpen_compl hcov
    ⟨z, Metric.mem_ball_self hr, hz⟩ ⟨x, hx1, hxc⟩
  exact hy3 (subset_closure hy2)


theorem lip_cases_vol_succ (z : Vec d) (j : ℕ) :
    volume (shiftCube z ((j + 1 : ℕ) : ℤ)) =
      ENNReal.ofReal ((3 : ℝ) ^ d) * volume (shiftCube z (j : ℤ)) := by
  rw [lip_bdry_approx_vol_cube, lip_bdry_approx_vol_cube, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [pow_succ, mul_pow]
  ring

theorem lip_cases_pin0 (S : Set (Vec d)) (j : ℕ) (x₀ : Vec d) (c : ℝ) (u : Vec d → ℝ) :
    lipPin S j x₀ c u 0 = ((3 : ℝ)⁻¹) ^ j * lipL2 S (fun x => u x - c) := by
  unfold lipPin
  have : (fun x => u x - c - vecDot (0 : Vec d) (x - x₀)) = fun x => u x - c := by
    funext x
    rw [lip_localize_vecDot_zero]
    ring
  rw [this]

end SuperdiffusionCLT.Section7
