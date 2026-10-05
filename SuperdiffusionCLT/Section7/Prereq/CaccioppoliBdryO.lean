/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryN

/-!
# The normalized edge-and-layer term

`Vq⁻¹ |∫_B h| ≤ ν τ ‖φ_c ∇u‖² + (ν/16)(‖φ ∇u‖² + G1² + (‖u - γ‖/L)²)` when the measure of `B` is
a small fraction `ϑ` of the cube and `Λ² ϑ^{1/d}` is small compared with `ν² τ`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constant of the edge-and-layer term. -/
noncomputable def ca2_C1 (d : ℕ) : ℝ :=
  1 + 6912 * (ca2_CS d : ℝ) ^ 2 * (d : ℝ) ^ 2 + 768 * (ca2_CS d : ℝ) ^ 2 * (d : ℝ) ^ 2 * (ca1_K0 d : ℝ) ^ 2

/-- The smallness constant of the edge-and-layer term. -/
noncomputable def ca2_CB (d : ℕ) : ℝ := 8 * (d : ℝ) * ca2_C1 d / (((125 / 729 : ℝ) ^ d) ^ 2)

theorem ca2_cubeVolume_originCube (d : ℕ) (m : ℤ) : cubeVolume (originCube d m) = ((3 : ℝ) ^ m) ^ d := by
  simp [cubeVolume, cubeScaleFactor, originCube]

theorem ca2_volume_openCube_toReal (Q : TriadicCube d) :
    (volume (openCubeSet Q)).toReal = cubeVolume Q := by
  have h := congrArg (fun μ : Measure (Vec d) => μ Set.univ)
    (volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q)
  simp only [Measure.restrict_apply_univ] at h
  rw [← h, volume_cubeSet_toReal]

/-- The pure-algebra core of the normalized edge-and-layer term. -/
theorem ca2_Bnorm_alg {Λ ν τ c0 Zn Gc G G1 w ϑ C1 dd : ℝ} (hΛ : 0 < Λ) (hν : 0 < ν) (hτ : 0 < τ)
    (hc0 : 0 < c0) (hZn : Zn ≤ c0⁻¹ ^ 2 * Gc ^ 2)
    {Y : ℝ} (hY : Y ≤ dd * ϑ * C1 * (G ^ 2 + G1 ^ 2 + w ^ 2))
    (hεB : 8 * dd * C1 / c0 ^ 2 * Λ ^ 2 * ϑ ≤ ν ^ 2 * τ) :
    Λ * (2 * ν * τ * c0 ^ 2 / Λ / 2 * Zn + (2 * ν * τ * c0 ^ 2 / Λ)⁻¹ * Y) ≤
      ν * τ * Gc ^ 2 + ν / 16 * (G ^ 2 + G1 ^ 2 + w ^ 2) := by
  have hc2 : 0 < c0 ^ 2 := by positivity
  have e1 : Λ * (2 * ν * τ * c0 ^ 2 / Λ / 2 * Zn) = ν * τ * c0 ^ 2 * Zn := by
    field_simp
  have e2 : Λ * ((2 * ν * τ * c0 ^ 2 / Λ)⁻¹ * Y) = Λ ^ 2 / (2 * ν * τ * c0 ^ 2) * Y := by
    field_simp
  have h1 : ν * τ * c0 ^ 2 * Zn ≤ ν * τ * Gc ^ 2 := by
    have : c0 ^ 2 * Zn ≤ Gc ^ 2 := by
      have := mul_le_mul_of_nonneg_left hZn hc2.le
      calc c0 ^ 2 * Zn ≤ c0 ^ 2 * (c0⁻¹ ^ 2 * Gc ^ 2) := this
        _ = Gc ^ 2 := by field_simp
    have h' := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ ν * τ)
    linarith only [h']
  have h2 : Λ ^ 2 / (2 * ν * τ * c0 ^ 2) * Y ≤ ν / 16 * (G ^ 2 + G1 ^ 2 + w ^ 2) := by
    have hk : Λ ^ 2 / (2 * ν * τ * c0 ^ 2) * (dd * ϑ * C1) ≤ ν / 16 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : Λ ^ 2 * (dd * ϑ * C1) = (dd * C1 / c0 ^ 2 * Λ ^ 2 * ϑ) * c0 ^ 2 := by field_simp
      rw [this]
      have h3 : dd * C1 / c0 ^ 2 * Λ ^ 2 * ϑ ≤ ν ^ 2 * τ / 8 := by
        have : 8 * dd * C1 / c0 ^ 2 * Λ ^ 2 * ϑ = 8 * (dd * C1 / c0 ^ 2 * Λ ^ 2 * ϑ) := by ring
        linarith only [hεB, this]
      calc dd * C1 / c0 ^ 2 * Λ ^ 2 * ϑ * c0 ^ 2 ≤ ν ^ 2 * τ / 8 * c0 ^ 2 :=
            mul_le_mul_of_nonneg_right h3 hc2.le
        _ = ν / 16 * (2 * ν * τ * c0 ^ 2) := by ring
    have hpos : 0 ≤ Λ ^ 2 / (2 * ν * τ * c0 ^ 2) := by positivity
    calc Λ ^ 2 / (2 * ν * τ * c0 ^ 2) * Y
        ≤ Λ ^ 2 / (2 * ν * τ * c0 ^ 2) * (dd * ϑ * C1 * (G ^ 2 + G1 ^ 2 + w ^ 2)) :=
          mul_le_mul_of_nonneg_left hY hpos
      _ = (Λ ^ 2 / (2 * ν * τ * c0 ^ 2) * (dd * ϑ * C1)) * (G ^ 2 + G1 ^ 2 + w ^ 2) := by ring
      _ ≤ ν / 16 * (G ^ 2 + G1 ^ 2 + w ^ 2) :=
          mul_le_mul_of_nonneg_right hk (by positivity)
  rw [mul_add, e1, e2]
  linarith only [h1, h2]

theorem ca2_self_le_rpow {ϑ : ℝ} (h0 : 0 ≤ ϑ) (h1 : ϑ ≤ 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ϑ ≤ ϑ ^ θ := by
  rcases h0.eq_or_lt with rfl | hpos
  · rw [Real.zero_rpow hθ0.ne']
  · calc ϑ = ϑ ^ (1 : ℝ) := (Real.rpow_one ϑ).symm
      _ ≤ ϑ ^ θ := Real.rpow_le_rpow_of_exponent_ge hpos h1 hθ1

theorem ca2_Y_alg {L a Vq vB vD ϑ R P CSr K0 Kη G G1 Wn X1 XW dd : ℝ} (hL : 0 < L) (ha : a = L / 4)
    (hKe : Kη = K0 * a⁻¹ ^ 2) (hVq : 0 < Vq) (hvB : vB ≤ ϑ * Vq) (hvD : vD ≤ Vq) (hvD0 : 0 ≤ vD)
    (hP : P ≤ R * L ^ 2) (hR : ϑ ≤ R) (hϑ : 0 ≤ ϑ) (hX1 : X1 = Vq * G ^ 2)
    (hXW : XW = Vq * Wn ^ 2) (hd : 0 ≤ dd) :
    Vq⁻¹ * (dd * G1 ^ 2 * vB + dd * (CSr ^ 2 * dd ^ 2 * P *
        (3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW)))) ≤
      dd * R * (1 + 6912 * CSr ^ 2 * dd ^ 2 + 768 * CSr ^ 2 * dd ^ 2 * K0 ^ 2) *
        (G ^ 2 + G1 ^ 2 + (Wn / L) ^ 2) := by
  have hR0 : 0 ≤ R := hϑ.trans hR
  have hai : a⁻¹ ^ 2 = 16 / L ^ 2 := by rw [ha]; field_simp; norm_num
  have h1 : Vq⁻¹ * (dd * G1 ^ 2 * vB) ≤ dd * G1 ^ 2 * ϑ := by
    have : Vq⁻¹ * vB ≤ ϑ := by rw [inv_mul_le_iff₀ hVq]; linarith only [hvB]
    calc Vq⁻¹ * (dd * G1 ^ 2 * vB) = dd * G1 ^ 2 * (Vq⁻¹ * vB) := by ring
      _ ≤ dd * G1 ^ 2 * ϑ := mul_le_mul_of_nonneg_left this (by positivity)
  have hΘ : 3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW) ≤
      3 * (Vq * (144 * a⁻¹ ^ 2 * (G ^ 2 + G1 ^ 2) + Kη ^ 2 * Wn ^ 2)) := by
    have h2 : G1 ^ 2 * vD ≤ G1 ^ 2 * Vq := mul_le_mul_of_nonneg_left hvD (sq_nonneg _)
    have h3 : 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) ≤ 144 * a⁻¹ ^ 2 * (G1 ^ 2 * Vq) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hX1, hXW]
    nlinarith only [h3]
  have hΘ0 : 0 ≤ 3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW) := by
    rw [hX1, hXW]; positivity
  have h4 : Vq⁻¹ * (dd * (CSr ^ 2 * dd ^ 2 * P *
        (3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW)))) ≤
      dd * (CSr ^ 2 * dd ^ 2 * (R * L ^ 2) * (3 * (144 * a⁻¹ ^ 2 * (G ^ 2 + G1 ^ 2) + Kη ^ 2 * Wn ^ 2))) := by
    have h5 : P * (3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW)) ≤
        (R * L ^ 2) * (3 * (Vq * (144 * a⁻¹ ^ 2 * (G ^ 2 + G1 ^ 2) + Kη ^ 2 * Wn ^ 2))) :=
      mul_le_mul hP hΘ hΘ0 (by positivity)
    have e : Vq⁻¹ * (dd * (CSr ^ 2 * dd ^ 2 * P * (3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW)))) =
        (dd * CSr ^ 2 * dd ^ 2) * Vq⁻¹ * (P * (3 * (144 * a⁻¹ ^ 2 * X1 + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) + Kη ^ 2 * XW))) := by ring
    rw [e]
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ (dd * CSr ^ 2 * dd ^ 2) * Vq⁻¹)
    refine h6.trans (le_of_eq ?_)
    field_simp
  have h7 : dd * (CSr ^ 2 * dd ^ 2 * (R * L ^ 2) * (3 * (144 * a⁻¹ ^ 2 * (G ^ 2 + G1 ^ 2) + Kη ^ 2 * Wn ^ 2))) =
      dd * CSr ^ 2 * dd ^ 2 * R * (6912 * (G ^ 2 + G1 ^ 2) + 768 * K0 ^ 2 * (Wn / L) ^ 2) := by
    rw [hKe, hai]
    field_simp
    ring
  have h8 : dd * G1 ^ 2 * ϑ ≤ dd * G1 ^ 2 * R := mul_le_mul_of_nonneg_left hR (by positivity)
  have hfin : dd * G1 ^ 2 * R + dd * CSr ^ 2 * dd ^ 2 * R * (6912 * (G ^ 2 + G1 ^ 2) + 768 * K0 ^ 2 * (Wn / L) ^ 2) ≤
      dd * R * (1 + 6912 * CSr ^ 2 * dd ^ 2 + 768 * CSr ^ 2 * dd ^ 2 * K0 ^ 2) *
        (G ^ 2 + G1 ^ 2 + (Wn / L) ^ 2) := by
    have hq : 0 ≤ dd * R := mul_nonneg hd hR0
    have hw := sq_nonneg (Wn / L)
    have hg := sq_nonneg G
    have hg1 := sq_nonneg G1
    have hc : 0 ≤ CSr ^ 2 * dd ^ 2 := by positivity
    have hk : 0 ≤ CSr ^ 2 * dd ^ 2 * K0 ^ 2 := by positivity
    nlinarith only [mul_nonneg hq hw, mul_nonneg hq hg, mul_nonneg hq hg1, mul_nonneg (mul_nonneg hq hc) hw,
      mul_nonneg (mul_nonneg hq hc) hg, mul_nonneg (mul_nonneg hq hc) hg1, mul_nonneg (mul_nonneg hq hk) hw,
      mul_nonneg (mul_nonneg hq hk) hg, mul_nonneg (mul_nonneg hq hk) hg1]
  linarith only [h1, h4, h7, h8, hfin]


theorem ca2_Z_le [NeZero d] (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W)
    (u : H1Function (openCubeSet (originCube d m) ∩ W)) {a ac : ℝ} (ha : 0 < a) (hac0 : 0 < ac)
    (haac : a ≤ 2 / 3 * ac) :
    ∫ x in ca2_Bset m h a W, vecNormSq (u.grad x) ≤
      (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 *
        ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi ac x * vecNormSq (u.grad x) := by
  classical
  have hDo : IsOpen (openCubeSet (originCube d m) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hBD : ca2_Bset m h a W ⊆ openCubeSet (originCube d m) ∩ W := fun x hx => hx.1
  have hBm := ca2_Bset_measurable m h a hWo
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hX := ca2_integrable_energy u (ca2_contDiff_Phi (d := d) ac) (ca1_hasCompactSupport_Phi hac0)
  have hnn : ∀ x : Vec d, 0 ≤ vecNormSq (u.grad x) := fun x => by
    unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 : ∫ x in ca2_Bset m h a W, vecNormSq (u.grad x) ≤
      ∫ x in ca2_Bset m h a W, (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (ca1_Phi ac x * vecNormSq (u.grad x)) := by
    refine setIntegral_mono_on ?_ ?_ hBm ?_
    · exact (ca2_integrable_energy u (ca2_contDiff_Phi (d := d) a) (ca1_hasCompactSupport_Phi ha)).mono_set hBD |>.congr
        (Filter.Eventually.of_forall fun x => rfl) |> fun _ => by
          have h0 : Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict (openCubeSet (originCube d m) ∩ W)) := by
            have h1 : Integrable (fun x => eucNorm (u.grad x) ^ 2)
                (volume.restrict (openCubeSet (originCube d m) ∩ W)) := (memLp_eucNorm_grad u).integrable_sq
            have h2 : (fun x => eucNorm (u.grad x) ^ 2) = fun x => vecNormSq (u.grad x) := by
              funext x
              unfold eucNorm
              exact Real.sq_sqrt (hnn x)
            rw [h2] at h1
            exact h1
          exact h0.mono_measure (Measure.restrict_mono hBD le_rfl)
    · exact (hX.mono_set hBD).const_mul _
    · intro x hx
      have hxa := hx.2.1
      have hk : ∀ k, |x k| ≤ 2 / 3 * ac := fun k => by
        have := ((ca2_mem_ball_iff ha x).1 hxa k).le
        linarith only [this, haac]
      have hl := ca1_phi_lower hac0 hk
      have hΦ : ((125 / 729 : ℝ) ^ d) ^ 2 ≤ ca1_Phi ac x := by
        rw [ca1_Phi_eq]; exact pow_le_pow_left₀ hc0.le hl 2
      have h3 : 1 ≤ (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca1_Phi ac x := by
        have e : (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ((125 / 729 : ℝ) ^ d) ^ 2 = 1 := by field_simp
        calc (1 : ℝ) = (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ((125 / 729 : ℝ) ^ d) ^ 2 := e.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hΦ (sq_nonneg _)
      calc vecNormSq (u.grad x) = 1 * vecNormSq (u.grad x) := (one_mul _).symm
        _ ≤ ((((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca1_Phi ac x) * vecNormSq (u.grad x) :=
            mul_le_mul_of_nonneg_right h3 (hnn x)
        _ = _ := by ring
  refine h1.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  refine setIntegral_mono_set hX ?_ (Filter.Eventually.of_forall hBD)
  exact Filter.Eventually.of_forall fun x => mul_nonneg (by rw [ca1_Phi_eq]; exact sq_nonneg _) (hnn x)

theorem ca2_isOpen_cube (m : ℤ) : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _

theorem ca2_Bnorm [NeZero d] (hd : 2 ≤ d) (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W)
    {A : CoeffField d} {Λ ν : ℝ} (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hop : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ∀ v : Vec d,
      eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function (openCubeSet (originCube d m) ∩ W)) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m) ∩ W)
      (openCubeSet (originCube d m)) (fun x => u.toFun x - γ x))
    {a ac : ℝ} (ha4 : a = (3 : ℝ) ^ m / 4) (hac4 : ac = 23 / 50 * (3 : ℝ) ^ m) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) (hKe : (Kη : ℝ) = (ca1_K0 d : ℝ) * (a⁻¹) ^ 2)
    {G1 : ℝ} (hb1 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1)
    {G Gc Wn : ℝ}
    (hGs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi a x * vecNormSq (u.grad x) = G ^ 2)
    (hGcs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi ac x * vecNormSq (u.grad x) = Gc ^ 2)
    (hWs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (u.toFun x - γ x) ^ 2 = Wn ^ 2)
    {ϑ τ : ℝ} (hϑ0 : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hB : (volume (ca2_Bset m h a W)).toReal ≤ ϑ * cubeVolume (originCube d m)) (hτ : 0 < τ)
    (hεB : ca2_CB d * Λ ^ 2 * ϑ ^ (1 / (d : ℝ)) ≤ ν ^ 2 * τ) :
    (cubeVolume (originCube d m))⁻¹ * |∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| ≤
      ν * τ * Gc ^ 2 + ν / 16 * (G ^ 2 + G1 ^ 2 + (Wn / (3 : ℝ) ^ m) ^ 2) := by
  classical
  have hL : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have ha : 0 < a := by rw [ha4]; positivity
  have hat : a < 3 ^ m / 2 := by rw [ha4]; linarith only [hL]
  have haV : Metric.closedBall (0 : Vec d) a ⊆ openCubeSet (originCube d m) :=
    ca1_closedBall_subset_openCube m hat
  have hDo : IsOpen (openCubeSet (originCube d m) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hDb : Bornology.IsBounded (openCubeSet (originCube d m) ∩ W) :=
    (isBounded_openCubeSet (originCube d m)).subset Set.inter_subset_left
  have hBD : ca2_Bset m h a W ⊆ openCubeSet (originCube d m) ∩ W := fun x hx => hx.1
  have hBm := ca2_Bset_measurable m h a hWo
  have hV0 : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  set Vq := cubeVolume (originCube d m) with hVq
  have hVqL : Vq = ((3 : ℝ) ^ m) ^ d := ca2_cubeVolume_originCube d m
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hθ0 : 0 < 1 / (d : ℝ) := by positivity
  have hθ1 : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hd0]; exact_mod_cast (show 1 ≤ d by omega)
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hd1 : d ≠ 0 := by omega
  have hX1 : ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi a x * vecNormSq (u.grad x) = Vq * G ^ 2 := by
    rw [← hGs, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
  have hXc : ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi ac x * vecNormSq (u.grad x) = Vq * Gc ^ 2 := by
    rw [← hGcs, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
  have hXW : ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2 = Vq * Wn ^ 2 := by
    rw [← hWs, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
  have hvD : (volume (openCubeSet (originCube d m) ∩ W)).toReal ≤ Vq := by
    have h0 : (volume (openCubeSet (originCube d m))).toReal = Vq := ca2_volume_openCube_toReal _
    rw [← h0]
    exact ENNReal.toReal_mono (isBounded_openCubeSet (originCube d m)).measure_lt_top.ne
      (measure_mono Set.inter_subset_left)
  by_cases hΛ0 : Λ = 0
  · have hb := ca2_Bterm hd hDo (ca2_isOpen_cube m) hDb hΛ hop u hγ hZ ha haV hKη hb1 hBD hBm
      (s := 1) one_pos
    rw [hΛ0, zero_mul] at hb
    have : |∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| = 0 := le_antisymm hb (abs_nonneg _)
    rw [this, mul_zero]
    positivity
  · have hΛpos : 0 < Λ := lt_of_le_of_ne hΛ (Ne.symm hΛ0)
    have hs : 0 < 2 * ν * τ * ((125 / 729 : ℝ) ^ d) ^ 2 / Λ := by positivity
    have hb := ca2_Bterm hd hDo (ca2_isOpen_cube m) hDb hΛ hop u hγ hZ ha haV hKη hb1 hBD hBm hs
    have hZle := ca2_Z_le m h hWo u ha (ac := ac) (by rw [hac4]; positivity)
      (by rw [ha4, hac4]; linarith only [hL])
    rw [hXc] at hZle
    have hZn : Vq⁻¹ * (∫ x in ca2_Bset m h a W, vecNormSq (u.grad x)) ≤
        (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Gc ^ 2 := by
      have := mul_le_mul_of_nonneg_left hZle (inv_nonneg.2 hV0.le)
      refine this.trans (le_of_eq ?_)
      field_simp
    set vB := (volume (ca2_Bset m h a W)).toReal with hvB
    set vD := (volume (openCubeSet (originCube d m) ∩ W)).toReal with hvDdef
    have hvB0 : 0 ≤ vB := ENNReal.toReal_nonneg
    have hvD0 : 0 ≤ vD := ENNReal.toReal_nonneg
    have hP : (vB * vD) ^ (1 / (d : ℝ)) ≤ ϑ ^ (1 / (d : ℝ)) * ((3 : ℝ) ^ m) ^ 2 := by
      have h1 : vB * vD ≤ ϑ * Vq * Vq := mul_le_mul hB hvD hvD0 (by positivity)
      refine (Real.rpow_le_rpow (mul_nonneg hvB0 hvD0) h1 hθ0.le).trans (le_of_eq ?_)
      rw [Real.mul_rpow (by positivity) hV0.le, Real.mul_rpow hϑ0 hV0.le, hVqL,
        show (1 : ℝ) / d = (d : ℝ)⁻¹ from one_div _, Real.pow_rpow_inv_natCast hL.le hd1]
      ring
    have hY := ca2_Y_alg (L := (3 : ℝ) ^ m) (a := a) (Vq := Vq) (vB := vB) (vD := vD) (ϑ := ϑ)
      (R := ϑ ^ (1 / (d : ℝ))) (P := (vB * vD) ^ (1 / (d : ℝ))) (CSr := (ca2_CS d : ℝ)) (K0 := (ca1_K0 d : ℝ))
      (Kη := (Kη : ℝ)) (G := G) (G1 := G1) (Wn := Wn) (X1 := ∫ x in openCubeSet (originCube d m) ∩ W,
        ca1_Phi a x * vecNormSq (u.grad x)) (XW := ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2)
      (dd := (d : ℝ)) hL ha4 hKe hV0 hB hvD hvD0 hP (ca2_self_le_rpow hϑ0 hϑ1 hθ0 hθ1) hϑ0 hX1 hXW hd0.le
    have hmain := ca2_Bnorm_alg (Λ := Λ) (ν := ν) (τ := τ) (c0 := ((125 / 729 : ℝ) ^ d))
      (Zn := Vq⁻¹ * (∫ x in ca2_Bset m h a W, vecNormSq (u.grad x))) (Gc := Gc) (G := G) (G1 := G1)
      (w := Wn / (3 : ℝ) ^ m) (ϑ := ϑ ^ (1 / (d : ℝ))) (C1 := ca2_C1 d) (dd := (d : ℝ)) hΛpos hν hτ hc0 hZn
      (Y := Vq⁻¹ * ((d : ℝ) * G1 ^ 2 * vB + (d : ℝ) * ((ca2_CS d : ℝ) ^ 2 * (d : ℝ) ^ 2 *
        ((vB * vD) ^ (1 / (d : ℝ))) * (3 * (144 * a⁻¹ ^ 2 * (∫ x in openCubeSet (originCube d m) ∩ W,
          ca1_Phi a x * vecNormSq (u.grad x)) + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) +
          (Kη : ℝ) ^ 2 * ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2)))))
      (by unfold ca2_C1; exact hY) hεB
    have hbB : Vq⁻¹ * |∫ x in ca2_Bset m h a W, vecDot (matVecMul (A x) (u.grad x))
        (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x)| ≤
        Vq⁻¹ * (Λ * (2 * ν * τ * ((125 / 729 : ℝ) ^ d) ^ 2 / Λ / 2 * (∫ x in ca2_Bset m h a W, vecNormSq (u.grad x)) +
          (2 * ν * τ * ((125 / 729 : ℝ) ^ d) ^ 2 / Λ)⁻¹ * ((d : ℝ) * G1 ^ 2 * vB + (d : ℝ) * ((ca2_CS d : ℝ) ^ 2 *
          (d : ℝ) ^ 2 * ((vB * vD) ^ (1 / (d : ℝ))) * (3 * (144 * a⁻¹ ^ 2 * (∫ x in openCubeSet (originCube d m) ∩ W,
          ca1_Phi a x * vecNormSq (u.grad x)) + 144 * a⁻¹ ^ 2 * (G1 ^ 2 * vD) +
          (Kη : ℝ) ^ 2 * ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2)))))) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hV0.le)
    refine hbB.trans (le_trans (le_of_eq ?_) hmain)
    ring

end SuperdiffusionCLT.Section7
