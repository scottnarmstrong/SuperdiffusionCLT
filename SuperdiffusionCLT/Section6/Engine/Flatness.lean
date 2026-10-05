/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.AffineSlopeB
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.BallCube
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace

/-!
# Flatness of growth-space elements at every scale

Large-scale flatness of `φ = c + Φ e₀` on balls: the best affine approximation of `φ` on `B_r`
is within `C δ_k` of `φ` in `L̲²(B_r)`, relative to `‖φ‖_{L̲²(B_r)}`, when `2r ≤ 3^k ≤ 6r`.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb8a_exists_m (d : ℕ) [NeZero d] :
    ∃ m : ℕ, m ≤ d + 1 ∧ 3 * d ≤ 3 ^ m ∧ 3 ^ m ≤ 9 * d := by
  have hd : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨Nat.clog 3 (3 * d), ?_, Nat.le_pow_clog (by norm_num) _, ?_⟩
  · refine Nat.clog_le_of_le_pow ?_
    have := Nat.lt_pow_self (a := 3) (n := d) (by norm_num)
    rw [pow_succ]
    omega
  · rcases h : Nat.clog 3 (3 * d) with _ | m
    · simp only [pow_zero]
      omega
    · have := Nat.pow_pred_clog_lt_self (b := 3) (x := 3 * d) (by norm_num) (by omega)
      rw [h] at this
      simp only [Nat.pred_succ] at this
      rw [pow_succ]
      omega

theorem eb8a_memLp_ball [NeZero d] {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclidBall r))) : MemLp f 2 (ballMeasure r) := by
  unfold ballMeasure ProbabilityTheory.cond
  exact hf.smul_measure (ENNReal.inv_ne_top.2 (volume_euclidBall_ne_zero hr))

theorem eb8a_memLp_entire {a : CoeffField d} {u F : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsEntireSolution a u g) (hF : F =ᵐ[volume] u) {R : ℝ} (hR : 0 < R) :
    MemLp F 2 (volume.restrict (euclidBall R)) := by
  obtain ⟨v, hv1, _⟩ := h R hR
  exact (v.toH1.memL2.ae_eq hv1).ae_eq (ae_restrict_of_ae hF.symm)

theorem eb8a_memLp_cube [NeZero d] {a : CoeffField d} {u F : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsEntireSolution a u g) (hF : F =ᵐ[volume] u) (k : ℕ) :
    MemLp F 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
  have hs : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
  have hR : 0 < Real.sqrt d * (3 : ℝ) ^ k := by positivity
  have h1 := eb8a_memLp_entire h hF hR
  have hsub := e0d_cube_sub_ball (d := d) (r := Real.sqrt d * (3 : ℝ) ^ k) (k := k)
    (by linarith only [hR])
  exact memL2On_openCubeSet_normalizedCubeMeasure
    (h1.mono_measure (Measure.restrict_mono hsub le_rfl))


theorem eb8a_upper (d : ℕ) [NeZero d] :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (r : ℝ) (k : ℕ), 0 < r → 2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 54 * r →
      ∀ g : Vec d → ℝ, MemLp g 2 (normalizedCubeMeasure (originCube d (k : ℤ))) →
        MemLp g 2 (ballMeasure r) →
        ballL2 r (fun x => g x - ∫ y, g y ∂ballMeasure r) ≤
          ENNReal.ofReal (Cd * (3 : ℝ) ^ k * cubeFlat k g) := by
  obtain ⟨Cd, hCd1, hCd⟩ := ballL2_le_cubeL2 d
  refine ⟨Cd, hCd1, fun r k hr h2 h54 g hgc hgb => ?_⟩
  set A := cubeAverage (originCube d (k : ℤ)) g with hA
  have h1 := ballL2_sub_average_le hr hgb A
  have h2' := hCd r k hr h2 h54 (fun x => g x - A) (hgc.sub (memLp_const _))
  refine h1.trans (h2'.trans (le_of_eq ?_))
  congr 1
  have hu := e0c_inv_mul k
  have hflat : cubeFlat k g = ((3 : ℝ)⁻¹) ^ k * cubeL2 k (fun x => g x - A) := rfl
  rw [hflat]
  calc Cd * cubeL2 k (fun x => g x - A)
      = Cd * ((3 : ℝ) ^ k * ((3 : ℝ)⁻¹) ^ k) * cubeL2 k (fun x => g x - A) := by rw [hu]; ring
    _ = _ := by ring

theorem eb8a_memLp_vecDot [NeZero d] {r : ℝ} (hr : 0 < r) (e : Vec d) :
    MemLp (fun x => vecDot e x) 2 (ballMeasure r) := by
  have := isProbabilityMeasure_ballMeasure (d := d) hr
  refine MemLp.of_bound (e0c_continuous_vecDot e).aestronglyMeasurable (engNorm e * r) ?_
  have hae : ∀ᵐ x ∂ballMeasure (d := d) r, x ∈ euclidBall r :=
    ProbabilityTheory.ae_cond_mem (measurableSet_euclidBall r)
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs]
  refine (abs_vecDot_le_engNorm e x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (engNorm_nonneg e)
  have hx' : engNorm x ^ 2 < r ^ 2 := by rw [engNorm_sq]; exact hx
  exact (abs_lt_of_sq_lt_sq hx' hr.le).le.trans' (by rw [abs_of_nonneg (engNorm_nonneg x)])


theorem eb8a_ev_lower (d : ℕ) [NeZero d] :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (r : ℝ) (k : ℕ), d + 1 ≤ k → 2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 6 * r →
      ∀ e : Vec d, ENNReal.ofReal (c1 * (3 : ℝ) ^ k * engNorm e) ≤ ballL2 r (fun x => vecDot e x) := by
  obtain ⟨Cd, hCd1, hCd⟩ := cubeL2_le_ballL2 d
  obtain ⟨m, hm1, hm2, hm3⟩ := eb8a_exists_m d
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨1 / (2 * Real.sqrt 3 * (9 * d) * Cd), by positivity, ?_⟩
  intro r k hk h2 h6 e
  have hr : 0 < r := by
    have : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    linarith only [this, h6]
  obtain ⟨j, hj⟩ : ∃ j, k = j + m := ⟨k - m, by omega⟩
  have hm2' : (3 : ℝ) * d ≤ (3 : ℝ) ^ m := by exact_mod_cast hm2
  have hm3' : (3 : ℝ) ^ m ≤ 9 * d := by exact_mod_cast hm3
  have hj3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hk3 : (3 : ℝ) ^ k = (3 : ℝ) ^ j * (3 : ℝ) ^ m := by rw [hj, pow_add]
  have hsd : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith only [hd])]
    nlinarith only [hd]
  have hc1 : Real.sqrt d * (3 : ℝ) ^ j ≤ 2 * r := by
    have : (d : ℝ) * (3 : ℝ) ^ j ≤ 2 * r := by
      nlinarith only [h6, hk3, hm2', hj3]
    nlinarith only [this, hsd, hj3]
  have hc2 : r ≤ (d : ℝ) * (3 : ℝ) ^ (j + 2) := by
    have : (3 : ℝ) ^ (j + 2) = 9 * (3 : ℝ) ^ j := by rw [pow_add]; ring
    rw [this]
    nlinarith only [h2, hk3, hm3', hj3, hd]
  have hmem := eb8a_memLp_vecDot (d := d) hr e
  have h := hCd r j hc1 hc2 (fun x => vecDot e x) hmem
  have hcm := e0c_memLp j (e0c_continuous_vecDot e)
  have hfl := cubeFlat_vecDot (d := d) j e
  have hle := cubeFlat_le_of_sub_const hcm 0
  simp only [sub_zero] at hle
  rw [hfl] at hle
  have hu := e0c_inv_mul j
  have hA : (3 : ℝ) ^ j * (engNorm e / (2 * Real.sqrt 3)) ≤ cubeL2 j (fun x => vecDot e x) := by
    have := mul_le_mul_of_nonneg_left hle hj3.le
    rw [← mul_assoc, hu, one_mul] at this
    exact this
  have hT : ENNReal.ofReal (ballL2 r (fun x => vecDot e x)).toReal =
      ballL2 r (fun x => vecDot e x) := ENNReal.ofReal_toReal hmem.eLpNorm_ne_top
  rw [← hT]
  apply ENNReal.ofReal_le_ofReal
  set T := (ballL2 r (fun x => vecDot e x)).toReal
  have hCdpos : 0 < Cd := by linarith only [hCd1]
  have hdpos : (0 : ℝ) < d := by linarith only [hd]
  have hen := engNorm_nonneg e
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h5 : (3 : ℝ) ^ j * engNorm e ≤ 2 * Real.sqrt 3 * (Cd * T) := by
    have := le_trans hA h
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  rw [hk3]
  have h6' : (3 : ℝ) ^ j * engNorm e * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ j * engNorm e * (9 * d) :=
    mul_le_mul_of_nonneg_left hm3' (by positivity)
  have h7 : (3 : ℝ) ^ j * engNorm e * (9 * d) ≤ 2 * Real.sqrt 3 * (Cd * T) * (9 * d) :=
    mul_le_mul_of_nonneg_right h5 (by positivity)
  calc (3 : ℝ) ^ j * (3 : ℝ) ^ m * engNorm e
      = (3 : ℝ) ^ j * engNorm e * (3 : ℝ) ^ m := by ring
    _ ≤ _ := h6'.trans h7
    _ = _ := by ring


/-- **E-B8a (flatness at every scale)**, Step 8, first half. -/
theorem eng_flatness (d : ℕ) [NeZero d] (Cin Cl : ℝ) (hCin : 1 ≤ Cin) (hCl : 1 ≤ Cl) :
    ∃ (C c8 : ℝ), 1 ≤ C ∧ 0 < c8 ∧
      ∀ (η κ γ : ℝ) (a : CoeffField d) (δ : ℕ → ℝ) (mstar : ℕ)
        (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)) (Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)),
        d + 3 ≤ mstar →
        (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c8) →
        -- hVsol
        (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
          ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
        -- hVflat
        (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
          cubeFlat j (fun x => V j e x - vecDot e x) ≤ Cin * δ j * engNorm e) →
        -- hchain, surjectivity part
        (∀ m k : ℕ, mstar ≤ k → k ≤ m →
          ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q)) →
        -- hΦlim Cl (η - 6κ), anchored at `n = mstar`
        (∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
          affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
          ∀ k : ℕ, mstar ≤ k → k ≤ m →
            cubeFlat k (fun x => Φ e0 x - V m e x) ≤
              Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e) →
        -- hrep (third conclusion of `eng_liouville`)
        (∀ φ ∈ growthSpace a γ, ∃ (c : ℝ) (e0 : Vec d),
          (φ : Vec d → ℝ) =ᵐ[volume] fun x => c + Φ e0 x) →
        -- conclusion
        ∀ φ ∈ growthSpace a γ, ∀ (k : ℕ) (r : ℝ), mstar ≤ k →
          2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 6 * r →
          (⨅ e : Vec d,
              ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r)) ≤
            ENNReal.ofReal (C * δ k) * ballL2 r φ := by
  obtain ⟨Cd, hCd1, hCd⟩ := eb8a_upper d
  obtain ⟨c1, hc1, hlow⟩ := eb8a_ev_lower d
  have hK : 0 < Cl + Cin := by linarith only [hCin, hCl]
  have hCdpos : 0 < Cd := by linarith only [hCd1]
  refine ⟨1 + 2 * Cd * (Cl + Cin) / c1, c1 / (2 * Cd * (Cl + Cin)), ?_, by positivity, ?_⟩
  · have : 0 ≤ 2 * Cd * (Cl + Cin) / c1 := by positivity
    linarith only [this]
  intro η κ γ a δ mstar V Φ hms hδ hVsol hVflat hsurj hlim hrep φ hφ k r hk h2 h6
  have hk' : d + 1 ≤ k := by omega
  have hr : 0 < r := by
    have : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    linarith only [this, h6]
  have h54 : (3 : ℝ) ^ k ≤ 54 * r := by linarith only [h6, hr]
  have hprob := isProbabilityMeasure_ballMeasure (d := d) hr
  obtain ⟨c, e0, hae⟩ := hrep φ hφ
  obtain ⟨gφ, hgφ⟩ := hφ.1
  set F : Vec d → ℝ := fun x => c + Φ e0 x with hFdef
  have hF : F =ᵐ[volume] (φ : Vec d → ℝ) := hae.symm
  have hFcube : ∀ n : ℕ, MemLp F 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    fun n => eb8a_memLp_cube hgφ hF n
  have hFball : MemLp F 2 (ballMeasure r) :=
    eb8a_memLp_ball hr (eb8a_memLp_entire hgφ hF hr)
  have hψ : Φ e0 = fun x => F x - c := by
    funext x
    simp only [hFdef]
    ring
  have hψcube : ∀ n : ℕ, MemLp (Φ e0) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    intro n
    rw [hψ]
    exact (hFcube n).sub (memLp_const c)
  have hψball : MemLp (Φ e0) 2 (ballMeasure r) := by
    rw [hψ]
    exact hFball.sub (memLp_const c)
  -- the matching vector
  obtain ⟨e, he⟩ := hsurj k mstar le_rfl hk e0
  have hVe : MemLp (V k e) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    (IsSolOn.memLp (hVsol k hk e).choose_spec).1
  have h1 := hlim e0 k e hk he k hk le_rfl
  simp only [sub_self, mul_zero, neg_zero, Real.rpow_zero, mul_one] at h1
  have h2' := hVflat k hk e
  have hlin : MemLp (fun x => vecDot e x) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    e0c_memLp k (e0c_continuous_vecDot e)
  have hsum := cubeFlat_add_le (hψcube k |>.sub hVe) (hVe.sub hlin)
  have hfun : (fun x => (Φ e0 x - V k e x) + (V k e x - vecDot e x)) =
      fun x => Φ e0 x - vecDot e x := by
    funext x
    ring
  simp only [Pi.sub_apply, hfun] at hsum
  set g : Vec d → ℝ := fun x => Φ e0 x - vecDot e x with hg
  have hgcube : MemLp g 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := (hψcube k).sub hlin
  have hgball : MemLp g 2 (ballMeasure r) := hψball.sub (eb8a_memLp_vecDot hr e)
  have hδk := hδ k hk
  have hflat : cubeFlat k g ≤ (Cl + Cin) * δ k * engNorm e := by
    have : cubeFlat k g ≤ Cl * δ k * engNorm e + Cin * δ k * engNorm e :=
      hsum.trans (add_le_add h1 h2')
    linarith only [this]
  -- averages on the ball
  have hψint : Integrable (Φ e0) (ballMeasure r) := hψball.integrable one_le_two
  have hvint : Integrable (fun x => vecDot e x) (ballMeasure r) :=
    (eb8a_memLp_vecDot hr e).integrable one_le_two
  set I : ℝ := ∫ y, Φ e0 y ∂ballMeasure r with hI
  have hintg : ∫ y, g y ∂ballMeasure r = I := by
    simp only [hg]
    rw [integral_sub hψint hvint, integral_vecDot_ballMeasure hr e, sub_zero]
  have hintF : ∫ y, F y ∂ballMeasure r = c + I := by
    simp only [hFdef]
    rw [integral_add (integrable_const c) hψint]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  have hae_ball : (φ : Vec d → ℝ) =ᵐ[ballMeasure r] F :=
    (ballMeasure_absolutelyContinuous r).ae_eq hae
  have hintφ : ∫ y, φ y ∂ballMeasure r = c + I := (integral_congr_ae hae_ball).trans hintF
  have hballφ : ballL2 r φ = ballL2 r F := eLpNorm_congr_ae hae_ball
  have hX : ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r) =
      ballL2 r (fun x => g x - ∫ y, g y ∂ballMeasure r) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae_ball] with x hx
    rw [hx, hintφ, hintg]
    simp only [hFdef, hg]
    ring
  -- upper bound
  have hU := hCd r k hr h2 h54 g hgcube hgball
  have hδ0 := hδk.1
  have hT0 : Cd * (3 : ℝ) ^ k * cubeFlat k g ≤
      Cd * (3 : ℝ) ^ k * ((Cl + Cin) * δ k * engNorm e) :=
    mul_le_mul_of_nonneg_left hflat (by positivity)
  have hU' := hU.trans (ENNReal.ofReal_le_ofReal hT0)
  -- lower bound
  have hL := hlow r k hk' h2 h6 e
  have hdec : (fun x => vecDot e x) =
      (fun x => Φ e0 x - I) - (fun x => g x - I) := by
    funext x
    simp only [hg, Pi.sub_apply]
    ring
  have htri : ballL2 r (fun x => vecDot e x) ≤
      ballL2 r (fun x => Φ e0 x - I) + ballL2 r (fun x => g x - I) := by
    unfold ballL2
    rw [hdec]
    exact eLpNorm_sub_le one_le_two
  have hA1 : ballL2 r (fun x => Φ e0 x - I) ≤ ballL2 r F := by
    have h := ballL2_sub_average_le hr hFball 0
    rw [hintF] at h
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · congr 1
      funext x
      simp only [hFdef]
      ring
    · congr 1
      funext x
      ring
  have hA2 : ballL2 r (fun x => g x - I) ≤
      ENNReal.ofReal (Cd * (3 : ℝ) ^ k * ((Cl + Cin) * δ k * engNorm e)) := by
    rw [← hintg]
    exact hU'
  -- the constants
  have hen := engNorm_nonneg e
  have hKpos : 0 < 2 * Cd * (Cl + Cin) := by positivity
  have hδc : δ k * (2 * Cd * (Cl + Cin)) ≤ c1 := by
    have := hδk.2
    rwa [le_div_iff₀ hKpos] at this
  have hT1 : Cd * (3 : ℝ) ^ k * ((Cl + Cin) * δ k * engNorm e) ≤
      c1 / 2 * (3 : ℝ) ^ k * engNorm e := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ k * engNorm e := by positivity
    calc Cd * (3 : ℝ) ^ k * ((Cl + Cin) * δ k * engNorm e)
        = (δ k * (2 * Cd * (Cl + Cin))) / 2 * ((3 : ℝ) ^ k * engNorm e) := by ring
      _ ≤ c1 / 2 * ((3 : ℝ) ^ k * engNorm e) := by gcongr
      _ = _ := by ring
  have hHa : ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) ≤ ballL2 r φ := by
    have hsplit : ENNReal.ofReal (c1 * (3 : ℝ) ^ k * engNorm e) =
        ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) +
          ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have h5 : ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) +
        ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) ≤
        ballL2 r F + ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) := by
      rw [← hsplit]
      refine hL.trans (htri.trans (add_le_add hA1 (hA2.trans (ENNReal.ofReal_le_ofReal hT1))))
    rw [hballφ]
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h5
  -- conclusion
  calc (⨅ e : Vec d, ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r))
      ≤ ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r) := iInf_le _ e
    _ = ballL2 r (fun x => g x - ∫ y, g y ∂ballMeasure r) := hX
    _ ≤ ENNReal.ofReal (Cd * (3 : ℝ) ^ k * ((Cl + Cin) * δ k * engNorm e)) := hU'
    _ = ENNReal.ofReal (2 * Cd * (Cl + Cin) / c1 * δ k) *
          ENNReal.ofReal (c1 / 2 * (3 : ℝ) ^ k * engNorm e) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal ((1 + 2 * Cd * (Cl + Cin) / c1) * δ k) * ballL2 r φ := by
        gcongr
        have : 0 ≤ δ k := hδ0
        nlinarith only [this]

/-- Witness for the numerical hypotheses: `δ = 0`, `d + 3 ≤ mstar`, and any `c8 > 0`. -/
example : ∃ mstar : ℕ, 1 + 3 ≤ mstar ∧ ∀ c8 : ℝ, 0 < c8 →
    ∀ j : ℕ, mstar ≤ j → 0 ≤ (fun _ : ℕ => (0 : ℝ)) j ∧ (fun _ : ℕ => (0 : ℝ)) j ≤ c8 :=
  ⟨4, by norm_num, fun _ hc8 _ _ => ⟨le_rfl, hc8.le⟩⟩

end SuperdiffusionCLT.Section6
