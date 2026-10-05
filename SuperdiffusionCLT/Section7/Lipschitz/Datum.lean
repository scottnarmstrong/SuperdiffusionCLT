/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section7.Prereq.LinftyReduction

/-!
# The mollified boundary datum

The mollification `gt` of a function `g` that is Lipschitz on a cube, at the scale `3^k`, and the
cut-off difference `ψ = ζ (g - gt)` for a cut-off `ζ` between the cubes `z + □_{k+1}` and
`z + □_{k+2}`, with the bounds on the first and second derivatives that the scale dictates.
-/

@[expose] public section

open Homogenization MeasureTheory Metric
open scoped NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_datum_bound1 (f : Vec d → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ K₁ := by
  have h1 : HasCompactSupport (fderiv ℝ f) := hcs.fderiv ℝ
  have c1 : Continuous (fderiv ℝ f) := hsm.continuous_fderiv (by simp)
  obtain ⟨K₁, hK₁⟩ := c1.bounded_above_of_compact_support h1
  exact ⟨max K₁ 0, le_max_right _ _, fun x => (hK₁ x).trans (le_max_left _ _)⟩

theorem lip_datum_lip1 (f : Vec d → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    ∃ K : ℝ≥0, LipschitzWith K (fderiv ℝ f) := by
  have h1 : HasCompactSupport (fderiv ℝ f) := hcs.fderiv ℝ
  have hsm0 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hsm.fderiv_right (by simp)
  have hsm1 : ContDiff ℝ 1 (fderiv ℝ f) := hsm0.of_le (by exact_mod_cast le_top)
  exact hsm1.lipschitzWith_of_hasCompactSupport h1 one_ne_zero

/-- A fixed smooth cutoff: `1` on the cube `‖x‖ ≤ 3/2`, supported in `‖x‖ ≤ 4`. -/
theorem lip_datum_base (d : ℕ) :
    ∃ ζ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 3 / 2 → ζ x = 1) ∧ tsupport ζ ⊆ closedBall 0 4 := by
  let b : ContDiffBump (0 : Vec d) := ⟨3 / 2, 4, by norm_num, by norm_num⟩
  have h1 : ∀ x : Vec d, ‖x‖ ≤ 3 / 2 → (b : Vec d → ℝ) x = 1 := fun x hx =>
    b.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hx)
  have h2 : tsupport (b : Vec d → ℝ) ⊆ closedBall 0 4 := by
    rw [b.tsupport_eq]
  exact ⟨b, b.contDiff, b.hasCompactSupport, fun x => ⟨b.nonneg, b.le_one⟩, h1, h2⟩

/-- The cutoff between the cubes of scales `k + 1` and `k + 2`, with the derivative bounds of the
scale `3^k`. -/
theorem lip_datum_cutoff (d : ℕ) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ (z : Vec d) (k : ℕ), ∃ ζ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
      (∀ x, ‖x - z‖ < (3 : ℝ) ^ (k + 1) / 2 → ζ x = 1) ∧
      tsupport ζ ⊆ ball z ((3 : ℝ) ^ (k + 2) / 2) ∧
      (∀ x, ‖fderiv ℝ ζ x‖ ≤ K₁ * ((3 : ℝ) ^ k)⁻¹) ∧
      ∀ x, ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ K₂ * (((3 : ℝ) ^ k)⁻¹) ^ 2 := by
  obtain ⟨ζ₀, hs, hc, hb, h1, h4⟩ := lip_datum_base d
  obtain ⟨M₁, hM₁, hM⟩ := lip_datum_bound1 ζ₀ hs hc
  obtain ⟨K, hK⟩ := lip_datum_lip1 ζ₀ hs hc
  refine ⟨M₁, K, hM₁, K.coe_nonneg, fun z k => ?_⟩
  set t : ℝ := ((3 : ℝ) ^ k)⁻¹ with ht
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have ht0 : 0 < t := inv_pos.2 h3k
  have htk : t * (3 : ℝ) ^ k = 1 := inv_mul_cancel₀ h3k.ne'
  set A : Vec d → Vec d := fun x => t • (x - z) with hA
  have hAnorm : ∀ x, ‖A x‖ = t * ‖x - z‖ := fun x => by
    rw [hA]; simp only; rw [norm_smul, Real.norm_of_nonneg ht0.le]
  have hAsub : ∀ x y, A x - A y = t • (x - y) := fun x y => by
    simp only [hA, smul_sub, sub_sub_sub_cancel_right]
  have hAs : ContDiff ℝ (⊤ : ℕ∞) A := (contDiff_id.sub contDiff_const).const_smul t
  have hsupp : ∀ x, 4 * (3 : ℝ) ^ k < ‖x - z‖ → ζ₀ (A x) = 0 := fun x hx => by
    have : A x ∉ tsupport ζ₀ := fun h => by
      have := mem_closedBall_zero_iff.1 (h4 h)
      rw [hAnorm] at this
      have h5 : t * ‖x - z‖ > t * (4 * (3 : ℝ) ^ k) := mul_lt_mul_of_pos_left hx ht0
      nlinarith only [this, h5, htk]
    exact image_eq_zero_of_notMem_tsupport this
  have hfd : ∀ x, fderiv ℝ (fun x => ζ₀ (A x)) x =
      (fderiv ℝ ζ₀ (A x)).comp (t • ContinuousLinearMap.id ℝ (Vec d)) := fun x => by
    have hA' : HasFDerivAt A (t • ContinuousLinearMap.id ℝ (Vec d)) x :=
      ((hasFDerivAt_id x).sub_const z).const_smul t
    exact (((hs.differentiable (by simp) (A x)).hasFDerivAt).comp x hA').fderiv
  have hid : ‖t • ContinuousLinearMap.id ℝ (Vec d)‖ ≤ t := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg ht0.le]
    exact mul_le_of_le_one_right ht0.le ContinuousLinearMap.norm_id_le
  refine ⟨fun x => ζ₀ (A x), ?_, ?_, fun x => hb _, ?_, ?_, ?_, ?_⟩
  · exact hs.comp hAs
  · refine HasCompactSupport.intro (isCompact_closedBall z (4 * (3 : ℝ) ^ k)) (fun x hx => ?_)
    refine hsupp x ?_
    rw [mem_closedBall_iff_norm, not_le] at hx
    exact hx
  · intro x hx
    refine h1 _ ?_
    rw [hAnorm]
    have : t * ‖x - z‖ ≤ t * ((3 : ℝ) ^ (k + 1) / 2) := mul_le_mul_of_nonneg_left hx.le ht0.le
    have e : t * ((3 : ℝ) ^ (k + 1) / 2) = 3 / 2 := by
      rw [pow_succ]
      nlinarith only [htk]
    linarith only [this, e]
  · have hsub : Function.support (fun x => ζ₀ (A x)) ⊆ closedBall z (4 * (3 : ℝ) ^ k) := by
      intro x hx
      rw [mem_closedBall_iff_norm]
      by_contra hcon
      exact hx (hsupp x (not_le.1 hcon))
    refine (closure_minimal hsub isClosed_closedBall).trans fun x hx => ?_
    rw [mem_closedBall_iff_norm] at hx
    rw [mem_ball_iff_norm, pow_add]
    nlinarith only [hx, h3k]
  · intro x
    rw [hfd x]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ M₁ * t := mul_le_mul (hM _) hid (norm_nonneg _) hM₁
      _ = _ := by rw [ht]
  · intro x
    have hlip : LipschitzWith (K * Real.toNNReal (t ^ 2)) (fderiv ℝ (fun x => ζ₀ (A x))) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, hfd x, hfd y, ← ContinuousLinearMap.sub_comp]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 := hK.dist_le_mul (A x) (A y)
      rw [dist_eq_norm, dist_eq_norm, hAsub, norm_smul, Real.norm_of_nonneg ht0.le] at h1
      have h2 : ‖fderiv ℝ ζ₀ (A x) - fderiv ℝ ζ₀ (A y)‖ * ‖t • ContinuousLinearMap.id ℝ (Vec d)‖ ≤
          (K * (t * ‖x - y‖)) * t :=
        mul_le_mul h1 hid (norm_nonneg _) (by positivity)
      refine h2.trans (le_of_eq ?_)
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
      ring
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hlip
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)] at this
    exact this

/-- The first derivative of a product. -/
theorem lip_datum_prod_fderiv (ζ h : Vec d → ℝ) (hζ : ContDiff ℝ 1 ζ) (hh : ContDiff ℝ 1 h) (x : Vec d) :
    fderiv ℝ (fun y => ζ y * h y) x = ζ x • fderiv ℝ h x + h x • fderiv ℝ ζ x :=
  fderiv_fun_mul (hζ.differentiable one_ne_zero x) (hh.differentiable one_ne_zero x)

/-- The second derivative of a product. -/
theorem lip_datum_prod_fderiv2 (ζ h : Vec d → ℝ) (hζ : ContDiff ℝ 2 ζ) (hh : ContDiff ℝ 2 h) (x : Vec d) :
    fderiv ℝ (fderiv ℝ (fun y => ζ y * h y)) x =
      ζ x • fderiv ℝ (fderiv ℝ h) x + (fderiv ℝ ζ x).smulRight (fderiv ℝ h x) +
        (h x • fderiv ℝ (fderiv ℝ ζ) x + (fderiv ℝ h x).smulRight (fderiv ℝ ζ x)) := by
  have e : fderiv ℝ (fun y => ζ y * h y) =
      fun y => ζ y • fderiv ℝ h y + h y • fderiv ℝ ζ y := by
    funext y
    exact lip_datum_prod_fderiv ζ h (hζ.of_le (by norm_num)) (hh.of_le (by norm_num)) y
  rw [e]
  have h1 : ContDiff ℝ 1 (fderiv ℝ ζ) := hζ.fderiv_right (m := 1) (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  have dζ : DifferentiableAt ℝ ζ x := (hζ.of_le (by norm_num)).differentiable one_ne_zero x
  have dh : DifferentiableAt ℝ h x := (hh.of_le (by norm_num)).differentiable one_ne_zero x
  have dζ' : DifferentiableAt ℝ (fderiv ℝ ζ) x := h1.differentiable one_ne_zero x
  have dh' : DifferentiableAt ℝ (fderiv ℝ h) x := h2.differentiable one_ne_zero x
  exact ((dζ.hasFDerivAt.smul dh'.hasFDerivAt).add (dh.hasFDerivAt.smul dζ'.hasFDerivAt)).fderiv

theorem lip_datum_prod_norm1 (ζ h : Vec d → ℝ) (hζ : ContDiff ℝ 1 ζ) (hh : ContDiff ℝ 1 h) (x : Vec d)
    (h0 : 0 ≤ ζ x) (h1 : ζ x ≤ 1) :
    ‖fderiv ℝ (fun y => ζ y * h y) x‖ ≤ |h x| * ‖fderiv ℝ ζ x‖ + ‖fderiv ℝ h x‖ := by
  rw [lip_datum_prod_fderiv ζ h hζ hh x]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
  have : ζ x * ‖fderiv ℝ h x‖ ≤ ‖fderiv ℝ h x‖ := mul_le_of_le_one_left (norm_nonneg _) h1
  linarith only [this]

theorem lip_datum_prod_norm2 (ζ h : Vec d → ℝ) (hζ : ContDiff ℝ 2 ζ) (hh : ContDiff ℝ 2 h) (x : Vec d)
    (h0 : 0 ≤ ζ x) (h1 : ζ x ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (fun y => ζ y * h y)) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ h) x‖ + 2 * (‖fderiv ℝ ζ x‖ * ‖fderiv ℝ h x‖) +
        |h x| * ‖fderiv ℝ (fderiv ℝ ζ) x‖ := by
  rw [lip_datum_prod_fderiv2 ζ h hζ hh x]
  have t1 : ‖ζ x • fderiv ℝ (fderiv ℝ h) x‖ ≤ ‖fderiv ℝ (fderiv ℝ h) x‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (ContinuousLinearMap.opNorm_nonneg _) h1
  have t2 : ‖(fderiv ℝ ζ x).smulRight (fderiv ℝ h x)‖ = ‖fderiv ℝ ζ x‖ * ‖fderiv ℝ h x‖ :=
    ContinuousLinearMap.norm_smulRight_apply _ _
  have t3 : ‖h x • fderiv ℝ (fderiv ℝ ζ) x‖ ≤ |h x| * ‖fderiv ℝ (fderiv ℝ ζ) x‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
  have t4 : ‖(fderiv ℝ h x).smulRight (fderiv ℝ ζ x)‖ = ‖fderiv ℝ h x‖ * ‖fderiv ℝ ζ x‖ :=
    ContinuousLinearMap.norm_smulRight_apply _ _
  have s1 := ContinuousLinearMap.opNorm_add_le (ζ x • fderiv ℝ (fderiv ℝ h) x) ((fderiv ℝ ζ x).smulRight (fderiv ℝ h x))
  have s2 := ContinuousLinearMap.opNorm_add_le (h x • fderiv ℝ (fderiv ℝ ζ) x) ((fderiv ℝ h x).smulRight (fderiv ℝ ζ x))
  have s3 := ContinuousLinearMap.opNorm_add_le (ζ x • fderiv ℝ (fderiv ℝ h) x + (fderiv ℝ ζ x).smulRight (fderiv ℝ h x))
    (h x • fderiv ℝ (fderiv ℝ ζ) x + (fderiv ℝ h x).smulRight (fderiv ℝ ζ x))
  have hc : ‖fderiv ℝ h x‖ * ‖fderiv ℝ ζ x‖ = ‖fderiv ℝ ζ x‖ * ‖fderiv ℝ h x‖ := mul_comm _ _
  linarith only [t1, t2, t3, t4, s1, s2, s3, hc]

/-- The shifted open cube is the sup-norm ball. -/
theorem lip_datum_shiftCube_eq (z : Vec d) (m : ℤ) : shiftCube z m = ball z ((3 : ℝ) ^ m / 2) := by
  ext x
  have hp : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by positivity
  have h : x ∈ shiftCube z m ↔ x - z ∈ openCubeSet (originCube d m) := by
    unfold shiftCube
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x - z, hx, by simp⟩
  rw [h, mem_ball_iff_norm, mem_openCubeSet_originCube_iff, pi_norm_lt_iff hp]
  refine forall_congr' fun i => ?_
  rw [Real.norm_eq_abs, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith only [h1, h2]
  · rintro ⟨h1, h2⟩
    constructor <;> linarith only [h1, h2]

theorem lip_datum_shiftCube_nat (z : Vec d) (n : ℕ) :
    shiftCube z (n : ℤ) = ball z ((3 : ℝ) ^ n / 2) := by
  rw [lip_datum_shiftCube_eq, zpow_natCast]

/-- **The mollified boundary datum**: `gt` is the mollification of `g` at the scale `3^k`,
`ψ = ζ (g - gt)` with a cutoff `ζ` between `z + □_{k+1}` and `z + □_{k+2}`. -/
theorem lip_datum (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (z : Vec d) (k : ℕ) (g : Vec d → ℝ) (G1 G2 : ℝ), ContDiff ℝ 2 g → 0 ≤ G1 → 0 ≤ G2 →
        (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
        (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
        ∃ gt ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) gt ∧ ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧
          tsupport ψ ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) ∧
          (∀ x ∈ shiftCube z ((k + 1 : ℕ) : ℤ), ψ x = g x - gt x) ∧
          (∀ x, |ψ x| ≤ C * (3 : ℝ) ^ k * G1) ∧ (∀ x, ‖fderiv ℝ ψ x‖ ≤ C * G1) ∧
          (∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ C * (((3 : ℝ) ^ k)⁻¹ * G1 + G2)) ∧
          (∀ x, ‖fderiv ℝ gt x‖ ≤ C * G1) ∧
          (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ C * ((3 : ℝ) ^ k)⁻¹ * G1) ∧
          ∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), |gt x - g x| ≤ C * (3 : ℝ) ^ k * G1 := by
  obtain ⟨Cm, hCm0, hmol⟩ := li1_exists_mollification_on d
  obtain ⟨K₁, K₂, hK₁, hK₂, hcut⟩ := lip_datum_cutoff d
  refine ⟨3 + Cm + 4 * K₁ + K₂, by linarith only [hCm0, hK₁, hK₂], ?_⟩
  intro z k g G1 G2 hg hG1 hG2 hDg hD2g
  set C : ℝ := 3 + Cm + 4 * K₁ + K₂ with hC
  have hC1 : 1 ≤ C := by linarith only [hCm0, hK₁, hK₂]
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  set t : ℝ := ((3 : ℝ) ^ k)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 h3k
  have htk : t * (3 : ℝ) ^ k = 1 := inv_mul_cancel₀ h3k.ne'
  have hQ : shiftCube z ((k + 2 : ℕ) : ℤ) = ball z ((3 : ℝ) ^ (k + 2) / 2) := lip_datum_shiftCube_nat z _
  have hQ1 : shiftCube z ((k + 1 : ℕ) : ℤ) = ball z ((3 : ℝ) ^ (k + 1) / 2) := lip_datum_shiftCube_nat z _
  -- Lipschitz bound of `g` on the cube
  have hLip : LipschitzOnWith G1.toNNReal g (ball z ((3 : ℝ) ^ (k + 2) / 2)) := by
    refine (convex_ball z _).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hg.differentiable (by norm_num) x) (fun x hx => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hG1]
    exact hDg x (by rw [hQ]; exact hx)
  obtain ⟨gt, hgt, happ, hD1, hLipD, -⟩ := hmol _ g G1.toNNReal ((3 : ℝ) ^ k) h3k hLip
  rw [Real.coe_toNNReal _ hG1] at happ hD1 hLipD
  have hD2gt : ∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ Cm * t * G1 := by
    intro x
    have hl : LipschitzWith (Real.toNNReal (Cm * G1 / (3 : ℝ) ^ k)) (fderiv ℝ gt) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      exact hLipD x y
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hl
    rw [Real.coe_toNNReal _ (by positivity)] at this
    refine this.trans (le_of_eq ?_)
    rw [ht]; ring
  obtain ⟨ζ, hζs, hζc, hζb, hζ1, hζt, hζ1', hζ2'⟩ := hcut z k
  have hζ2 : ContDiff ℝ 2 ζ := hζs.of_le (WithTop.coe_le_coe.2 le_top)
  have hgt2 : ContDiff ℝ 2 gt := hgt.of_le (WithTop.coe_le_coe.2 le_top)
  have hh : ContDiff ℝ 2 (fun x => g x - gt x) := hg.sub hgt2
  have hh1 : ContDiff ℝ 1 (fun x => g x - gt x) := hh.of_le (by norm_num)
  have hζ1c : ContDiff ℝ 1 ζ := hζ2.of_le (by norm_num)
  have hdg : ∀ x, DifferentiableAt ℝ (fderiv ℝ g) x := fun x =>
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hdgt : ∀ x, DifferentiableAt ℝ (fderiv ℝ gt) x := fun x =>
    (hgt2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hfh : ∀ x, fderiv ℝ (fun x => g x - gt x) x = fderiv ℝ g x - fderiv ℝ gt x := fun x =>
    fderiv_sub (hg.differentiable (by norm_num) x) (hgt2.differentiable (by norm_num) x)
  have hfh2 : ∀ x, fderiv ℝ (fderiv ℝ (fun x => g x - gt x)) x =
      fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ gt) x := fun x => by
    have : fderiv ℝ (fun x => g x - gt x) = fun x => fderiv ℝ g x - fderiv ℝ gt x := funext hfh
    rw [this]
    exact fderiv_sub (hdg x) (hdgt x)
  refine ⟨gt, fun x => ζ x * (g x - gt x), hgt, hζ2.mul hh, hζc.mul_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact tsupport_mul_subset_left.trans hζt
  · intro x hx
    rw [hQ1, mem_ball_iff_norm] at hx
    show ζ x * (g x - gt x) = _
    rw [hζ1 x hx, one_mul]
  · intro x
    show |ζ x * (g x - gt x)| ≤ _
    have hCG : 0 ≤ C * (3 : ℝ) ^ k * G1 := by positivity
    by_cases hx : x ∈ tsupport ζ
    · have hxQ : x ∈ ball z ((3 : ℝ) ^ (k + 2) / 2) := hζt hx
      have h1 : |g x - gt x| ≤ (3 : ℝ) ^ k * G1 := by
        rw [abs_sub_comm]; exact happ x hxQ
      rw [abs_mul, abs_of_nonneg (hζb x).1]
      have h2 : ζ x * |g x - gt x| ≤ |g x - gt x| := mul_le_of_le_one_left (abs_nonneg _) (hζb x).2
      have h3 : (3 : ℝ) ^ k * G1 ≤ C * (3 : ℝ) ^ k * G1 := by
        have : 0 ≤ (3 : ℝ) ^ k * G1 := by positivity
        nlinarith only [this, hC1]
      linarith only [h1, h2, h3]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, abs_zero]
      exact hCG
  · intro x
    by_cases hx : x ∈ tsupport ζ
    · have hxQ : x ∈ ball z ((3 : ℝ) ^ (k + 2) / 2) := hζt hx
      have hxQ' : x ∈ shiftCube z ((k + 2 : ℕ) : ℤ) := by rw [hQ]; exact hxQ
      have h1 : |g x - gt x| ≤ (3 : ℝ) ^ k * G1 := by
        rw [abs_sub_comm]; exact happ x hxQ
      have hn := lip_datum_prod_norm1 ζ (fun x => g x - gt x) hζ1c hh1 x (hζb x).1 (hζb x).2
      have hDh : ‖fderiv ℝ (fun x => g x - gt x) x‖ ≤ 2 * G1 := by
        rw [hfh x]
        have s1 := norm_sub_le (fderiv ℝ g x) (fderiv ℝ gt x)
        have s2 := hDg x hxQ'
        have s3 := hD1 x
        linarith only [s1, s2, s3]
      have hprod : |g x - gt x| * ‖fderiv ℝ ζ x‖ ≤ K₁ * G1 := by
        calc _ ≤ ((3 : ℝ) ^ k * G1) * (K₁ * t) :=
              mul_le_mul h1 (hζ1' x) (norm_nonneg _) (by positivity)
          _ = K₁ * G1 * (t * (3 : ℝ) ^ k) := by ring
          _ = K₁ * G1 := by rw [htk, mul_one]
      have hCK : (K₁ + 2) * G1 ≤ C * G1 := by
        refine mul_le_mul_of_nonneg_right ?_ hG1
        linarith only [hC, hCm0, hK₁, hK₂]
      show ‖fderiv ℝ (fun x => ζ x * (g x - gt x)) x‖ ≤ _
      linarith only [hn, hDh, hprod, hCK]
    · have e0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have e1 : fderiv ℝ ζ x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
      show ‖fderiv ℝ (fun x => ζ x * (g x - gt x)) x‖ ≤ _
      rw [lip_datum_prod_fderiv ζ _ hζ1c hh1 x, e0, e1]
      simp only [zero_smul, smul_zero, add_zero, norm_zero]
      positivity
  · intro x
    show ‖fderiv ℝ (fderiv ℝ (fun x => ζ x * (g x - gt x))) x‖ ≤ _
    by_cases hx : x ∈ tsupport ζ
    · have hxQ : x ∈ ball z ((3 : ℝ) ^ (k + 2) / 2) := hζt hx
      have hxQ' : x ∈ shiftCube z ((k + 2 : ℕ) : ℤ) := by rw [hQ]; exact hxQ
      have h1 : |g x - gt x| ≤ (3 : ℝ) ^ k * G1 := by
        rw [abs_sub_comm]; exact happ x hxQ
      have hn := lip_datum_prod_norm2 ζ (fun x => g x - gt x) hζ2 hh x (hζb x).1 (hζb x).2
      have hDh : ‖fderiv ℝ (fun x => g x - gt x) x‖ ≤ 2 * G1 := by
        rw [hfh x]
        have s1 := norm_sub_le (fderiv ℝ g x) (fderiv ℝ gt x)
        have s2 := hDg x hxQ'
        have s3 := hD1 x
        linarith only [s1, s2, s3]
      have hD2h : ‖fderiv ℝ (fderiv ℝ (fun x => g x - gt x)) x‖ ≤ G2 + Cm * t * G1 := by
        rw [hfh2 x]
        have s1 := norm_sub_le (fderiv ℝ (fderiv ℝ g) x) (fderiv ℝ (fderiv ℝ gt) x)
        have s2 := hD2g x hxQ'
        have s3 := hD2gt x
        linarith only [s1, s2, s3]
      have hA : ‖fderiv ℝ ζ x‖ * ‖fderiv ℝ (fun x => g x - gt x) x‖ ≤ (K₁ * t) * (2 * G1) :=
        mul_le_mul (hζ1' x) hDh (norm_nonneg _) (by positivity)
      have hB : |g x - gt x| * ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ ((3 : ℝ) ^ k * G1) * (K₂ * t ^ 2) :=
        mul_le_mul h1 (hζ2' x) (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      have hBe : ((3 : ℝ) ^ k * G1) * (K₂ * t ^ 2) = K₂ * (t * G1) * (t * (3 : ℝ) ^ k) := by ring
      rw [htk, mul_one] at hBe
      have ha : 0 ≤ t * G1 := by positivity
      have hCa : (Cm + 4 * K₁ + K₂) * (t * G1) ≤ C * (t * G1) :=
        mul_le_mul_of_nonneg_right (by linarith only [hC, hK₁, hK₂]) ha
      have hCb : 1 * G2 ≤ C * G2 := mul_le_mul_of_nonneg_right hC1 hG2
      linarith only [hn, hD2h, hA, hB, hBe, hCa, hCb]
    · have e0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have e1 : fderiv ℝ ζ x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
      have e2 : fderiv ℝ (fderiv ℝ ζ) x = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (tsupport_fderiv_subset ℝ h))
      rw [lip_datum_prod_fderiv2 ζ _ hζ2 hh x, e0, e1, e2]
      have hz : (0 : ℝ) • fderiv ℝ (fderiv ℝ fun x => g x - gt x) x +
          (0 : Vec d →L[ℝ] ℝ).smulRight (fderiv ℝ (fun x => g x - gt x) x) +
          ((g x - gt x) • (0 : Vec d →L[ℝ] Vec d →L[ℝ] ℝ) +
            (fderiv ℝ (fun x => g x - gt x) x).smulRight (0 : Vec d →L[ℝ] ℝ)) = 0 := by
        ext v w
        simp only [add_apply, smul_apply, zero_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
          zero_mul, mul_zero, add_zero]
      rw [hz, ContinuousLinearMap.opNorm_zero]
      positivity
  · intro x
    refine (hD1 x).trans ?_
    have := mul_le_mul_of_nonneg_right hC1 hG1
    linarith only [this]
  · intro x
    refine (hD2gt x).trans ?_
    have hCmC : Cm ≤ C := by linarith only [hC, hK₁, hK₂]
    have := mul_le_mul_of_nonneg_right hCmC (mul_nonneg ht0.le hG1)
    linarith only [this]
  · intro x hx
    rw [hQ] at hx
    refine (happ x hx).trans ?_
    have : 0 ≤ (3 : ℝ) ^ k * G1 := by positivity
    nlinarith only [hC1, this]

/-- Satisfiability: the zero datum. -/
example (d : ℕ) (z : Vec d) (k : ℕ) : True := by
  obtain ⟨C, -, h⟩ := lip_datum d
  obtain ⟨gt, ψ, -⟩ := h z k (fun _ => 0) 0 0 contDiff_const le_rfl le_rfl
    (fun x _ => by simp) (fun x _ => by
      rw [show fderiv ℝ (fderiv ℝ (fun _ : Vec d => (0 : ℝ))) x = 0 by simp]
      exact le_of_eq ContinuousLinearMap.opNorm_zero)
  trivial

end SuperdiffusionCLT.Section7
