/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Cover
public import SuperdiffusionCLT.Section7.Prereq.L2InteriorB
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryApprox
public import SuperdiffusionCLT.Section7.MinimalScale.GridMax
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalC

/-!
# The local inputs of the `L^∞` proposition: geometric and scalar lemmas

The pieces of the local inputs of the paper that do not involve the boundary Lipschitz estimate:
the dilated domain lies in a cube, the oscillation about the mean is at most twice the
oscillation about any constant, an `L²` average over a cube is bounded by the largest average
over the `3^d` tiles of a cube of triple side, the restriction of a solution to a cube, and the
passage from a bound at the centres of the tiles to the bounds on the cube.
-/

@[expose] public section

open MeasureTheory Homogenization Metric
open scoped Pointwise ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem linf_local_dil_subset {U : Set (Vec d)} (hU0 : U ⊆ openCubeSet (originCube d 0)) {R : ℝ}
    (hR : 0 < R) : R • U ⊆ ball (0 : Vec d) (R / 2) := by
  rintro x ⟨y, hy, rfl⟩
  have h1 := hU0 hy
  rw [← rc_shiftCube_zero, lip_datum_shiftCube_eq] at h1
  rw [mem_ball_zero_iff] at h1 ⊢
  have : ‖R • y‖ = R * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hR.le]
  rw [this]
  simp only [zpow_zero] at h1
  nlinarith only [h1, hR]

theorem linf_local_vol_le {U : Set (Vec d)} (hU0 : U ⊆ openCubeSet (originCube d 0)) {R : ℝ}
    (hR : 0 < R) : volume (R • U) ≤ ENNReal.ofReal (R ^ d) := by
  refine (measure_mono (linf_local_dil_subset hU0 hR)).trans ?_
  rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin]
  refine le_of_eq ?_
  congr 1
  rw [show 2 * (R / 2) = R by ring]


theorem linf_local_prob {S : Set (Vec d)} (h0 : volume S ≠ 0) (hT : volume S ≠ ⊤) :
    IsProbabilityMeasure (((volume S)⁻¹) • volume.restrict S) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 hT

theorem linf_local_avg_le {S : Set (Vec d)} (h0 : volume S ≠ 0) (hT : volume S ≠ ⊤)
    {f : Vec d → ℝ} (c0 : ℝ) (hf : MemLp f 2 (volume.restrict S)) :
    lpBar S 2 (fun x => f x - ⨍ w in S, f w) ≤ 2 * lpBar S 2 (fun x => f x - c0) := by
  have := linf_local_prob h0 hT
  set ν : Measure (Vec d) := ((volume S)⁻¹) • volume.restrict S with hν
  have hf' : MemLp f 2 ν := hf.smul_measure (ENNReal.inv_ne_top.2 h0)
  have hg : MemLp (fun x => f x - c0) 2 ν := hf'.sub (memLp_const c0)
  have hav : (⨍ w in S, f w) = ∫ w, f w ∂ν := by
    simp only [average, hν, Measure.restrict_apply_univ]
  have hint : Integrable f ν := hf'.integrable one_le_two
  have hsplit : (fun x => f x - ⨍ w in S, f w) =
      fun x => (f x - c0) + (c0 - ∫ w, f w ∂ν) := by
    funext x
    rw [hav]
    ring
  have hc : c0 - ∫ w, f w ∂ν = -∫ w, (f w - c0) ∂ν := by
    rw [integral_sub hint (integrable_const c0), integral_const]
    simp
  unfold lpBar
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  rw [eLpNorm_const _ (by norm_num) (NeZero.ne ν), measure_univ, ENNReal.one_rpow, mul_one]
  rw [two_mul]
  gcongr
  rw [hc, enorm_neg]
  calc ‖∫ w, (f w - c0) ∂ν‖ₑ ≤ ∫⁻ w, ‖f w - c0‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => f x - c0) 1 ν := (eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable).symm
    _ ≤ eLpNorm (fun x => f x - c0) 2 ν := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)


theorem linf_local_sq (μ : Measure (Vec d)) {h : Vec d → ℝ} (hh : AEStronglyMeasurable h μ) :
    eLpNorm h 2 μ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hh]
  have : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [this, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat, one_div, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_natCast]
  simp

theorem linf_local_lint_eq {T : Set (Vec d)} (h0 : volume T ≠ 0) (hT : volume T ≠ ⊤)
    {h : Vec d → ℝ} (hh : AEStronglyMeasurable h (volume.restrict T)) :
    ∫⁻ x in T, ‖h x‖ₑ ^ 2 = volume T * lpBar T 2 h ^ 2 := by
  unfold lpBar
  rw [linf_local_sq _ (hh.smul_measure _), lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel h0 hT, one_mul]


theorem linf_local_union_le {Q : Set (Vec d)} {ι : Type*} [Fintype ι] {T : ι → Set (Vec d)}
    (hQ0 : volume Q ≠ 0) (hQT : volume Q ≠ ⊤) (hTQ : ∀ i, T i ⊆ Q)
    (hcov : ∀ᵐ x ∂volume, x ∈ Q → ∃ i, x ∈ T i) (hsum : ∑ i, volume (T i) ≤ volume Q)
    {h : Vec d → ℝ} (hh : AEStronglyMeasurable h (volume.restrict Q)) {M : ℝ≥0∞}
    (hM : ∀ i, lpBar (T i) 2 h ≤ M) : lpBar Q 2 h ≤ M := by
  have hTle : ∀ i, volume (T i) ≤ volume Q := fun i => measure_mono (hTQ i)
  have hmT : ∀ i, AEStronglyMeasurable h (volume.restrict (T i)) := fun i =>
    hh.mono_measure (Measure.restrict_mono (hTQ i) le_rfl)
  have hstep : ∀ i, ∫⁻ x in T i, ‖h x‖ₑ ^ 2 ≤ volume (T i) * M ^ 2 := by
    intro i
    by_cases h0 : volume (T i) = 0
    · rw [Measure.restrict_eq_zero.2 h0]
      simp
    · rw [linf_local_lint_eq h0 ((hTle i).trans_lt hQT.lt_top).ne (hmT i)]
      gcongr
      exact hM i
  have hQeq := linf_local_lint_eq hQ0 hQT hh
  have h1 : ∫⁻ x in Q, ‖h x‖ₑ ^ 2 ≤ volume Q * M ^ 2 := by
    calc ∫⁻ x in Q, ‖h x‖ₑ ^ 2
        ≤ ∫⁻ x, ‖h x‖ₑ ^ 2 ∂(Measure.sum fun i => volume.restrict (T i)) := by
          refine lintegral_mono' ?_ le_rfl
          have : volume.restrict Q ≤ volume.restrict (⋃ i, T i) := by
            refine Measure.restrict_mono_ae ?_
            filter_upwards [hcov] with x hx hxQ
            obtain ⟨i, hi⟩ := hx hxQ
            exact Set.mem_iUnion.2 ⟨i, hi⟩
          exact this.trans Measure.restrict_iUnion_le
      _ = ∑ i, ∫⁻ x in T i, ‖h x‖ₑ ^ 2 := by
          rw [lintegral_sum_measure, tsum_fintype]
      _ ≤ ∑ i, volume (T i) * M ^ 2 := Finset.sum_le_sum fun i _ => hstep i
      _ = (∑ i, volume (T i)) * M ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ volume Q * M ^ 2 := by gcongr
  rw [hQeq] at h1
  have h2 : lpBar Q 2 h ^ 2 ≤ M ^ 2 := (ENNReal.mul_le_mul_iff_right hQ0 hQT).1 h1
  exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h2


theorem linf_local_osc_le {W S : Set (Vec d)} (hSW : S ⊆ W) {κ : ℝ} (hκ : 0 ≤ κ)
    (hS0 : volume S ≠ 0) (hW : volume W ≠ ⊤) (hvol : volume W ≤ ENNReal.ofReal κ * volume S)
    {φ gt : Vec d → ℝ} (hφ : MemLp φ 2 (volume.restrict W))
    (hgt : MemLp (fun x => φ x - gt x) 2 (volume.restrict W)) (c0 : ℝ) :
    lpBar S 2 (fun x => φ x - ⨍ w in S, φ w) + lpBar S 2 (fun x => φ x - gt x) ≤
      ENNReal.ofReal (Real.sqrt κ * (2 * lipL2 W (fun x => φ x - c0) +
        lipL2 W (fun x => φ x - gt x))) := by
  have hS : volume S ≠ ⊤ := fun h => hW (top_unique (h ▸ measure_mono hSW))
  have hmono : (volume.restrict S : Measure (Vec d)) ≤ volume.restrict W :=
    Measure.restrict_mono hSW le_rfl
  have hφS : MemLp φ 2 (volume.restrict S) := hφ.mono_measure hmono
  have hc : MemLp (fun x => φ x - c0) 2 (volume.restrict W) := by
    have : IsFiniteMeasure (volume.restrict W : Measure (Vec d)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hW.lt_top⟩
    exact hφ.sub (memLp_const c0)
  have h1 := linf_local_avg_le hS0 hS c0 hφS
  have h2 : lpBar S 2 (fun x => φ x - c0) = ENNReal.ofReal (lipL2 S (fun x => φ x - c0)) :=
    (ofReal_lipL2 hS0 hS (hc.mono_measure hmono)).symm
  have h3 : lpBar S 2 (fun x => φ x - gt x) =
      ENNReal.ofReal (lipL2 S (fun x => φ x - gt x)) :=
    (ofReal_lipL2 hS0 hS (hgt.mono_measure hmono)).symm
  have m2 := lipL2_mono_set hκ hSW hS0 hW hvol hc
  have m3 := lipL2_mono_set hκ hSW hS0 hW hvol hgt
  have hsq := Real.sqrt_nonneg κ
  calc lpBar S 2 (fun x => φ x - ⨍ w in S, φ w) + lpBar S 2 (fun x => φ x - gt x)
      ≤ 2 * ENNReal.ofReal (lipL2 S (fun x => φ x - c0)) +
          ENNReal.ofReal (lipL2 S (fun x => φ x - gt x)) := by
        rw [← h2, ← h3]
        exact add_le_add_left h1 _
    _ = ENNReal.ofReal (2 * lipL2 S (fun x => φ x - c0) + lipL2 S (fun x => φ x - gt x)) := by
        have n1 : 0 ≤ lipL2 S (fun x => φ x - c0) := ENNReal.toReal_nonneg
        have n2 : 0 ≤ lipL2 S (fun x => φ x - gt x) := ENNReal.toReal_nonneg
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) n1) n2,
          ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith only [m2, m3, hsq]


theorem linf_local_Rr_le {A1 A2 Eb Ec Ee : ℝ≥0∞} {a b c e F G G2 O : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hF : 0 ≤ F) (hG : 0 ≤ G) (hG2 : 0 ≤ G2) (hO : 0 ≤ O)
    (h1 : A1 + A2 ≤ ENNReal.ofReal O) (hEb : Eb ≤ ENNReal.ofReal F)
    (hEc : Ec ≤ ENNReal.ofReal G) (hEe : Ee ≤ ENNReal.ofReal G2) :
    ENNReal.ofReal a * (A1 + A2) + ENNReal.ofReal b * Eb + ENNReal.ofReal c * Ec +
        ENNReal.ofReal e * Ee ≤ ENNReal.ofReal (a * O + b * F + c * G + e * G2) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul hb, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul he]
  gcongr


theorem linf_local_essSup_le (μ : Measure (Vec d)) {g : Vec d → ℝ} {B : ℝ}
    (hm : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, |g x| ≤ B) :
    eLpNorm g ⊤ μ ≤ ENNReal.ofReal B := by
  rw [eLpNorm_exponent_top hm]
  exact eLpNormEssSup_le_of_ae_bound (by simpa [Real.norm_eq_abs] using h)

theorem linf_local_memLp_sub {W : Set (Vec d)} (hWm : MeasurableSet W) (hW : volume W ≠ ⊤) {r G : ℝ}
    (hWb : ∀ x ∈ W, ‖x‖ ≤ r) {gt : Vec d → ℝ} (hgt : ContDiff ℝ 1 gt)
    (hG : ∀ x, ‖fderiv ℝ gt x‖ ≤ G) {φ : Vec d → ℝ} (hφ : MemLp φ 2 (volume.restrict W)) :
    MemLp (fun x => φ x - gt x) 2 (volume.restrict W) := by
  have : IsFiniteMeasure (volume.restrict W : Measure (Vec d)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hW.lt_top⟩
  refine hφ.sub ?_
  refine MemLp.of_bound hgt.continuous.aestronglyMeasurable (‖gt 0‖ + G * r) ?_
  refine (ae_restrict_iff' ?_).2 (Filter.Eventually.of_forall fun x hx => ?_)
  · exact hWm
  · have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ) (f := gt)
      (x := 0) (y := x) (fun y _ => (hgt.differentiable (by norm_num)) y) (fun y _ => hG y)
      convex_univ (Set.mem_univ _) (Set.mem_univ _)
    have h2 := hWb x hx
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    have h3 : ‖gt x‖ ≤ ‖gt 0‖ + ‖gt x - gt 0‖ := by
      have := norm_le_norm_add_norm_sub' (gt x) (gt 0)
      linarith only [this]
    rw [sub_zero] at h1
    nlinarith only [h1, h2, h3, hG0]


/-- The centres of the `3^d` tiles of side `3^n` in the cube `z + □_{n+1}`. -/
noncomputable def linfTilePt (z : Vec d) (n : ℕ) (j : Fin d → Fin 3) : Vec d :=
  fun i => z i + (3 : ℝ) ^ n * (((j i : ℕ) : ℝ) - 1)

theorem linf_local_dist_tile (z : Vec d) (n : ℕ) (j : Fin d → Fin 3) :
    dist (linfTilePt z n j) z ≤ (3 : ℝ) ^ n := by
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq]
  simp only [linfTilePt, add_sub_cancel_left]
  rw [abs_mul, abs_of_pos (by positivity)]
  have : |((j i : ℕ) : ℝ) - 1| ≤ 1 := by
    have h2 : ((j i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 (j i).2
    have h0 : (0 : ℝ) ≤ ((j i : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith only [h0, h2]
  calc (3 : ℝ) ^ n * |((j i : ℕ) : ℝ) - 1| ≤ (3 : ℝ) ^ n * 1 := by gcongr
    _ = (3 : ℝ) ^ n := mul_one _

theorem linf_local_tile_sub (z : Vec d) (n : ℕ) (j : Fin d → Fin 3) :
    shiftCube (linfTilePt z n j) (n : ℤ) ⊆ shiftCube z ((n + 1 : ℕ) : ℤ) := by
  rw [lip_bdry_approx_shiftCube_eq_ball, lip_bdry_approx_shiftCube_eq_ball]
  refine Metric.ball_subset_ball' ?_
  have := linf_local_dist_tile z n j
  have h3 : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
  rw [h3]
  linarith only [this]

theorem linf_local_tile_vol_sum (z : Vec d) (n : ℕ) :
    ∑ j : Fin d → Fin 3, volume (shiftCube (linfTilePt z n j) (n : ℤ)) =
      volume (shiftCube z ((n + 1 : ℕ) : ℤ)) := by
  simp only [lip_bdry_approx_vol_cube, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  rw [pow_succ, mul_pow]
  ring

theorem linf_local_coord (t : ℝ) (h : |t| < 3 / 2) :
    ∃ r : Fin 3, |t - (((r : ℕ) : ℝ) - 1)| ≤ 1 / 2 := by
  rw [abs_lt] at h
  by_cases h1 : t < -(1 / 2)
  · refine ⟨0, ?_⟩
    simp only [Fin.val_zero, Nat.cast_zero]
    rw [abs_le]
    constructor <;> linarith only [h.1, h1]
  by_cases h2 : t ≤ 1 / 2
  · refine ⟨1, ?_⟩
    simp only [Fin.val_one, Nat.cast_one]
    rw [abs_le]
    constructor <;> linarith only [h1, h2]
  · refine ⟨2, ?_⟩
    simp only [Fin.val_two, Nat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [h.2, h2]

theorem linf_local_tile_cover [NeZero d] (z : Vec d) (n : ℕ) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ shiftCube z ((n + 1 : ℕ) : ℤ) →
      ∃ j : Fin d → Fin 3, x ∈ shiftCube (linfTilePt z n j) (n : ℤ) := by
  have hN : volume (⋃ j : Fin d → Fin 3, Metric.sphere (linfTilePt z n j) ((3 : ℝ) ^ n / 2)) = 0 :=
    measure_iUnion_null fun j => Measure.addHaar_sphere _ _ _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with x hxN hxQ
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball] at hxQ
  have hc : ∀ i, ∃ r : Fin 3, |(x i - z i) / (3 : ℝ) ^ n - (((r : ℕ) : ℝ) - 1)| ≤ 1 / 2 := by
    intro i
    refine linf_local_coord _ ?_
    rw [abs_div, abs_of_pos h3, div_lt_iff₀ h3]
    have := (dist_le_pi_dist x z i)
    rw [Real.dist_eq] at this
    have h4 : (3 : ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
    rw [dist_comm] at hxQ
    have h5 := lt_of_le_of_lt this (by rwa [dist_comm] at hxQ)
    linarith only [h5, h4]
  choose r hr using hc
  have hle : dist x (linfTilePt z n r) ≤ (3 : ℝ) ^ n / 2 := by
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq]
    have := hr i
    have e : x i - linfTilePt z n r i = (3 : ℝ) ^ n * ((x i - z i) / (3 : ℝ) ^ n - (((r i : ℕ) : ℝ) - 1)) := by
      simp only [linfTilePt]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos h3]
    calc (3 : ℝ) ^ n * |(x i - z i) / (3 : ℝ) ^ n - (((r i : ℕ) : ℝ) - 1)| ≤ (3 : ℝ) ^ n * (1 / 2) := by gcongr
      _ = (3 : ℝ) ^ n / 2 := by ring
  refine ⟨r, ?_⟩
  rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball]
  refine lt_of_le_of_ne hle fun heq => hxN ?_
  exact Set.mem_iUnion.2 ⟨r, by rw [Metric.mem_sphere]; exact heq⟩


/-- Restriction of the solution to a cube meeting the domain: weak equation and localized zero
trace. -/
theorem linf_local_restrict {a : CoeffField d} {W : Set (Vec d)} (hWo : IsOpen W) (z : Vec d)
    (m : ℕ) {v : H1Function W} {f gt : Vec d → ℝ}
    (hv : IsWeakSolutionOn a W v f (fun _ => 0)) (hv0 : MemH10 W (fun x => v.toFun x - gt x)) :
    IsWeakSolutionOn a (shiftCube z (m : ℤ) ∩ W)
        (v.restrict (((lip_bdry_approx_isOpen_cube z m).inter hWo)) Set.inter_subset_right) f
        (fun _ => 0) ∧
      LocalizedZeroTraceFunctionOn (shiftCube z (m : ℤ) ∩ W) (shiftCube z (m : ℤ))
        (fun x => v.toFun x - gt x) := by
  refine ⟨hv.restrict' _ _, ?_⟩
  obtain ⟨w, hw⟩ := hv0
  have h1 : LocalizedZeroTraceFunctionOn W Set.univ (fun x => v.toFun x - gt x) := by
    rw [← hw]
    exact localizedZeroTraceFunctionOn_of_h10_any w
  exact lip_localized_restrict ((lip_bdry_approx_isOpen_cube z m).inter hWo)
    (lip_bdry_approx_isOpen_cube z m) Set.inter_subset_right (Set.subset_univ _)
    (by ext x; simp only [Set.mem_inter_iff]; tauto) h1


/-- The unnormalized `L²` norm is the normalized one times the square root of the volume. -/
theorem linf_local_eLp_eq {S : Set (Vec d)} (h0 : volume S ≠ 0) (hT : volume S ≠ ⊤)
    (h : Vec d → ℝ) :
    eLpNorm h 2 (volume.restrict S) = (volume S) ^ (1 / (2 : ℝ)) * lpBar S 2 h := by
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.2 hT), smul_eq_mul, ← mul_assoc]
  have : (1 / (2 : ℝ≥0∞)).toReal = 1 / (2 : ℝ) := by
    rw [ENNReal.toReal_div]
    norm_num
  rw [this, ← ENNReal.mul_rpow_of_ne_top hT (ENNReal.inv_ne_top.2 h0),
    ENNReal.mul_inv_cancel h0 hT, ENNReal.one_rpow, one_mul]

/-- Dividing a bound by a positive constant. -/
theorem linf_local_le_of_mul_le {c : ℝ} (hc : 0 < c) {L A M : ℝ≥0∞}
    (h : ENNReal.ofReal c * L + A ≤ M) : L ≤ ENNReal.ofReal c⁻¹ * M := by
  have h1 : ENNReal.ofReal c * L ≤ M := le_trans le_self_add h
  calc L = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * L) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal c⁻¹ * M := by gcongr

/-- Points of the form `3^n q`, `q ∈ ℤ`, in a ball lie in the grid of mesh `3^{n-s}`. -/
theorem linf_local_mem_grid {p : Vec d} {n s : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hq : ∀ i, ∃ q : ℤ, p i = (3 : ℝ) ^ n * (q : ℝ)) (hb : ∀ i, |p i| ≤ R) :
    p ∈ gridPts d ((n : ℤ) - (s : ℤ)) R := by
  rw [mem_gridPts hR]
  choose q hq using hq
  refine ⟨fun i => (3 : ℤ) ^ s * q i, fun i => ?_, hb⟩
  rw [hq i]
  push_cast
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  field_simp

end SuperdiffusionCLT.Section7
