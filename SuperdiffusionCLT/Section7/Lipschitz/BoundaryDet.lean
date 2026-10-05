/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryStepD
public import SuperdiffusionCLT.Section7.Lipschitz.Iteration
public import SuperdiffusionCLT.Section7.Lipschitz.PinCalc
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorDetB
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorOriginC

/-!
# The boundary large-scale Lipschitz estimate, deterministic form: calculus

The gradient of a solution on the small cube from the boundary Caccioppoli block at the next
scale, for a solution defined on a larger cube, and the monotonicity of the `L²` block in its
constant.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **The gradient of `u` at the scale `k`**: the boundary Caccioppoli block at the scale `k + 1`
for `u`, defined on the larger cube of the scale `m`, against the datum `g`, with the pinned
flatness `Φ_{k+1}(p)`. -/
theorem lip_bdry_det_grad [NeZero d] {a : CoeffField d} {nu s Cin E lam Lam : ℝ}
    {W : Set (Vec d)} {z x₀ : Vec d} {k m : ℕ} (hkm : k + 1 ≤ m) (hnu : 0 < nu) (hs : 1 ≤ s) (hCin : 1 ≤ Cin)
    (hE : 0 ≤ E) (hk : 1 ≤ k) (hW : IsOpen W) (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 2)
    (hell : IsEllipticFieldOn lam Lam (shiftCube z (m : ℤ) ∩ W) a)
    (hc1 : LipCaccBdryS a nu s Cin E W z (k + 1))
    (hD0 : volume (shiftCube z (k : ℤ) ∩ W) ≠ 0)
    (f g : Vec d → ℝ) (F G1 G2 : ℝ) (u : H1Function (shiftCube z (m : ℤ) ∩ W))
    (hg : ContDiff ℝ 2 g) (hF0 : 0 ≤ F) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hDg : ∀ x ∈ shiftCube z (m : ℤ), ‖fderiv ℝ g x‖ ≤ G1)
    (hD2g : ∀ x ∈ shiftCube z (m : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2)
    (hFae : ∀ᵐ x ∂volume.restrict (shiftCube z (m : ℤ) ∩ W), |f x| ≤ F)
    (hsol : IsWeakSolutionOn a (shiftCube z (m : ℤ) ∩ W) u f (fun _ => 0))
    (hz : LocalizedZeroTraceFunctionOn (shiftCube z (m : ℤ) ∩ W)
      (shiftCube z (m : ℤ)) (fun x => u.toFun x - g x)) (p : Vec d) :
    (Real.sqrt s)⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (k : ℤ) ∩ W) u.grad ≤
      Cin * (lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p +
        (d : ℝ) * ‖p‖ + 2 * G1 + 3 * (s⁻¹ * (3 : ℝ) ^ k * F) +
        3 * (((k : ℝ)) ^ (-E) * (3 : ℝ) ^ k * G2)) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hQ01 : shiftCube z (k : ℤ) ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (by omega)
  have hQ12 : shiftCube z ((k + 1 : ℕ) : ℤ) ⊆ shiftCube z (m : ℤ) :=
    lip_bdry_approx_cube_mono z hkm
  have hD01 : shiftCube z (k : ℤ) ∩ W ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ01
  have hD12 : shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W ⊆ shiftCube z (m : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ12
  have hD1o : IsOpen (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW
  have hD2o : IsOpen (shiftCube z (m : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW
  have hD0t : volume (shiftCube z (k : ℤ) ∩ W) ≠ ⊤ :=
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z k)
      (measure_mono Set.inter_subset_left)
  have hD1t : volume (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) ≠ ⊤ :=
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z (k + 1))
      (measure_mono Set.inter_subset_left)
  have hD1v : volume (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) ≠ 0 := fun h =>
    hD0 (le_antisymm (h ▸ measure_mono hD01) bot_le)
  have hQ1ball : shiftCube z ((k + 1 : ℕ) : ℤ) = Metric.ball z ((3 : ℝ) ^ (k + 1) / 2) :=
    lip_bdry_approx_shiftCube_eq_ball z (k + 1)
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h3 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by rw [pow_succ]; ring
  have hx₀Q2 : x₀ ∈ shiftCube z ((k + 1 : ℕ) : ℤ) := by
    rw [hQ1ball, Metric.mem_ball, dist_eq_norm]
    linarith only [hx₀, h3, ht]
  have hconv : Convex ℝ (shiftCube z ((k + 1 : ℕ) : ℤ)) := by
    rw [hQ1ball]; exact convex_ball _ _
  set P : ℝ := ‖p‖ with hPdef
  have hP0 : 0 ≤ P := norm_nonneg _
  set Φ : ℝ := lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p with hΦdef
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦdef]; unfold lipPin lipL2
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  -- the pointwise bound of `u - g` against the affine function
  have hdist : ∀ x ∈ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W, ‖x - x₀‖ ≤ 3 * (3 : ℝ) ^ k :=
    fun x hx => lip_bdry_approx_dist_le hx₀ hx.1
  set B : ℝ := 3 * (3 : ℝ) ^ k * ((d : ℝ) * P + G1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hRb : ∀ x ∈ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W,
      |g x₀ + vecDot p (x - x₀) - g x| ≤ B := by
    intro x hx
    have hxQ2 : x ∈ shiftCube z ((k + 1 : ℕ) : ℤ) := hx.1
    have h1 := lip_bdry_approx_abs_vecDot_le p (x - x₀)
    have h2 : |g x₀ - g x| ≤ G1 * (3 * (3 : ℝ) ^ k) := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g)
        (fun y _ => (hg.differentiable (by norm_num)).differentiableAt)
        (fun y hy => hDg y (hQ12 hy)) hconv hxQ2 hx₀Q2
      rw [Real.norm_eq_abs] at this
      calc |g x₀ - g x| ≤ G1 * ‖x₀ - x‖ := this
        _ = G1 * ‖x - x₀‖ := by rw [norm_sub_rev]
        _ ≤ G1 * (3 * (3 : ℝ) ^ k) := mul_le_mul_of_nonneg_left (hdist x hx) hG1
    have h4 : (d : ℝ) * P * ‖x - x₀‖ ≤ (d : ℝ) * P * (3 * (3 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
    have h5 : g x₀ + vecDot p (x - x₀) - g x = vecDot p (x - x₀) + (g x₀ - g x) := by ring
    rw [h5]
    calc |vecDot p (x - x₀) + (g x₀ - g x)| ≤ |vecDot p (x - x₀)| + |g x₀ - g x| :=
          abs_add_le _ _
      _ ≤ _ := by rw [hB]; linarith only [h1, h2, h4]

  -- integrability
  have hmemu : MemLp u.toFun 2 (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    u.memL2.mono_measure (Measure.restrict_mono hD12 le_rfl)
  have hfin1 : IsFiniteMeasure (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    ⟨by simpa using hD1t.lt_top⟩
  have hcA : Continuous (fun x : Vec d => g x₀ + vecDot p (x - x₀)) :=
    continuous_const.add (lip_bdry_approx_continuous_aff p x₀)
  have hcR : Continuous (fun x : Vec d => g x₀ + vecDot p (x - x₀) - g x) :=
    hcA.sub hg.continuous
  have hRmem : MemLp (fun x : Vec d => g x₀ + vecDot p (x - x₀) - g x) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    MemLp.of_bound hcR.aestronglyMeasurable B
      ((ae_restrict_iff' (hD1o.measurableSet)).2 (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]; exact hRb x hx))
  have hAmem : MemLp (fun x : Vec d => g x₀ + vecDot p (x - x₀)) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) :=
    MemLp.of_bound hcA.aestronglyMeasurable (|g x₀| + (d : ℝ) * P * (3 * (3 : ℝ) ^ k))
      ((ae_restrict_iff' (hD1o.measurableSet)).2 (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]
        have h1 := lip_bdry_approx_abs_vecDot_le p (x - x₀)
        have h4 : (d : ℝ) * P * ‖x - x₀‖ ≤ (d : ℝ) * P * (3 * (3 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
        calc |g x₀ + vecDot p (x - x₀)| ≤ |g x₀| + |vecDot p (x - x₀)| := abs_add_le _ _
          _ ≤ _ := by linarith only [h1, h4]))
  have hU1mem : MemLp (fun x : Vec d => u.toFun x - g x₀ - vecDot p (x - x₀)) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) := by
    have e : (fun x : Vec d => u.toFun x - g x₀ - vecDot p (x - x₀)) =
        fun x => u.toFun x - (g x₀ + vecDot p (x - x₀)) := funext fun x => by ring
    rw [e]
    exact hmemu.sub hAmem
  have hugmem : MemLp (fun x : Vec d => u.toFun x - g x) 2
      (volume.restrict (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)) := by
    have e : (fun x : Vec d => u.toFun x - g x) =
        fun x => (u.toFun x - g x₀ - vecDot p (x - x₀)) +
          (g x₀ + vecDot p (x - x₀) - g x) := funext fun x => by ring
    rw [e]
    exact hU1mem.add hRmem
  have hL2 : lipL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (fun x => u.toFun x - g x) ≤
      3 * (3 : ℝ) ^ k * (Φ + (d : ℝ) * P + G1) := by
    have e : (fun x : Vec d => u.toFun x - g x) =
        fun x => (u.toFun x - g x₀ - vecDot p (x - x₀)) +
          (g x₀ + vecDot p (x - x₀) - g x) := funext fun x => by ring
    rw [e]
    refine (lipL2_add_le hD1v hD1t hU1mem hRmem).trans ?_
    have hR := lipL2_le_of_ae_abs_le hB0 hD1v hD1t
      (f := fun x : Vec d => g x₀ + vecDot p (x - x₀) - g x)
      ((ae_restrict_iff' (hD1o.measurableSet)).2 (Filter.Eventually.of_forall hRb))
    have hΦe : lipL2 (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)
        (fun x : Vec d => u.toFun x - g x₀ - vecDot p (x - x₀)) = 3 * (3 : ℝ) ^ k * Φ := by
      rw [hΦdef]; unfold lipPin
      have : 3 * (3 : ℝ) ^ k * ((3 : ℝ)⁻¹) ^ (k + 1) = 1 := by
        rw [← h3, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
      rw [← mul_assoc, this, one_mul]
    rw [hΦe]
    have : 3 * (3 : ℝ) ^ k * (Φ + (d : ℝ) * P + G1) = 3 * (3 : ℝ) ^ k * Φ + B := by
      rw [hB]; ring
    rw [this]
    exact add_le_add le_rfl hR
  -- the Caccioppoli block at the scale `k + 1`
  have e1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
  obtain ⟨f1, hf1m, hf1b, hf1sol, -⟩ := lip_bdry_approx_repl hD2o hD1o hD12 hell hsol hF0 hFae
  set u1 : H1Function (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) := u.restrict hD1o hD12 with hu1
  have hagree : (shiftCube z (m : ℤ) ∩ W) ∩ shiftCube z ((k + 1 : ℕ) : ℤ) =
      (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) ∩ shiftCube z ((k + 1 : ℕ) : ℤ) := by
    ext x
    constructor
    · rintro ⟨⟨_, hw⟩, hq⟩
      exact ⟨⟨hq, hw⟩, hq⟩
    · rintro ⟨⟨hq, hw⟩, _⟩
      exact ⟨⟨hQ12 hq, hw⟩, hq⟩
  have hz1 : LocalizedZeroTraceFunctionOn (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W)
      (shiftCube z ((k + 1 : ℕ) : ℤ)) (fun x => u1.toFun x - g x) :=
    lip_localized_restrict hD1o (lip_bdry_approx_isOpen_cube z _) hD12 hQ12 hagree hz
  have hQb : lpBar (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) 2 (fun x => u1.toFun x - g x) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (k + 1) * (Φ + (d : ℝ) * P + G1)) := by
    show lpBar (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) 2 (fun x => u.toFun x - g x) ≤ _
    rw [← ofReal_lipL2 hD1v hD1t hugmem]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [h3]
    exact hL2
  have hFb : lpBar (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) 2 f1 ≤ ENNReal.ofReal F :=
    lip_int_harm_of_l2_lpBar_le_of_ae_bound hD1v hD1t 2 hf1m hf1b
  have hQb0 : 0 ≤ (3 : ℝ) ^ (k + 1) * (Φ + (d : ℝ) * P + G1) := by positivity
  have cacc := lip_bdry_approx_cacc hc1 hnu hs0 hCin0 (by rw [e1]; exact hD0)
    (by rw [e1]; exact hD0t) (by rw [e1]; exact hD01) f1 g u1 hg hf1sol hz1 hQb hFb
    (fun x hx => hDg x (hQ12 hx.1)) (fun x hx => hD2g x (hQ12 hx.1))
    hQb0 hF0 hG1 hG2
  rw [e1] at cacc
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hqk : (((k + 1 : ℕ) : ℝ)) ^ (-E) ≤ (k : ℝ) ^ (-E) :=
    Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith only) (by linarith only [hE])
  have hq0 : 0 ≤ (((k + 1 : ℕ) : ℝ)) ^ (-E) := by positivity
  have harith := lip_bdry_approx_u_arith (Cin := Cin) (s := s) (Φ := Φ) (dP := (d : ℝ) * P)
    (G1 := G1) (G2 := G2) (F := F) (q := (((k + 1 : ℕ) : ℝ)) ^ (-E)) (kE := (k : ℝ) ^ (-E)) k
    hCin hs hΦ0 (by positivity) hG1 hG2 hF0 hq0 hqk
  have hX0 : 0 ≤ lipGradL2 (shiftCube z (k : ℤ) ∩ W) u1.grad := ENNReal.toReal_nonneg
  have hZ0 : 0 ≤ Cin * (Φ + (d : ℝ) * P + 2 * G1 + 3 * (s⁻¹ * (3 : ℝ) ^ k * F) +
        3 * (((k : ℝ)) ^ (-E) * (3 : ℝ) ^ k * G2)) := by positivity
  exact lip_bdry_approx_sgrad_le hnu hs0 hX0 hZ0 (cacc.trans harith)



/-- A cube of the scale `j` centred at a point of a uniformly `C^{1,1}` set contains a ball of
radius comparable to its side. -/
theorem lip_bdry_det_inner (d : ℕ) [NeZero d] (M₁ rU : ℝ) (hrU : 0 < rU) :
    ∃ c' : ℝ, 0 < c' ∧ c' ≤ 1 ∧
      ∀ (W : Set (Vec d)) (rW M₂W DW : ℝ) (z : Vec d) (j mt : ℕ),
        IsUniformC11Domain W rW M₁ M₂W DW → rU * (3 : ℝ) ^ mt ≤ rW → j ≤ mt → z ∈ W →
        ∃ q : Vec d, Metric.ball q (c' * (3 : ℝ) ^ j) ⊆ shiftCube z (j : ℤ) ∩ W := by
  obtain ⟨cin, hcin0, hcin1, hin⟩ := lip_inner_ball d M₁
  have hm0 : 0 < min (1 / 2 : ℝ) rU := lt_min (by norm_num) hrU
  refine ⟨cin * min (1 / 2 : ℝ) rU, by positivity, ?_, ?_⟩
  · calc cin * min (1 / 2 : ℝ) rU ≤ 1 * (1 / 2) :=
        mul_le_mul hcin1 (min_le_left _ _) hm0.le zero_le_one
      _ ≤ 1 := by norm_num
  intro W rW M₂W DW z j mt hW hrW hj hz
  have ht : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  set ρ : ℝ := min (1 / 2 : ℝ) rU * (3 : ℝ) ^ j with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ ≤ rW := by
    calc ρ ≤ rU * (3 : ℝ) ^ j := mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le
      _ ≤ rU * (3 : ℝ) ^ mt :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hrU.le
      _ ≤ rW := hrW
  obtain ⟨q, hq⟩ := hin W rW M₂W DW hW z hz ρ hρ0 hρr
  refine ⟨q, fun y hy => ⟨?_, (hq (by
    have : cin * ρ = cin * min (1 / 2 : ℝ) rU * (3 : ℝ) ^ j := by rw [hρ]; ring
    rwa [← this] at hy)).2⟩⟩
  have hy' : y ∈ Metric.ball z ρ := (hq (by
    have : cin * ρ = cin * min (1 / 2 : ℝ) rU * (3 : ℝ) ^ j := by rw [hρ]; ring
    rwa [← this] at hy)).1
  rw [lip_bdry_approx_shiftCube_eq_ball]
  refine Metric.ball_subset_ball ?_ hy'
  calc ρ ≤ (1 / 2) * (3 : ℝ) ^ j := mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le
    _ = (3 : ℝ) ^ j / 2 := by ring

end SuperdiffusionCLT.Section7
