/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.BallCube
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Engine.Chain
public import SuperdiffusionCLT.Section6.Engine.WindowFlat
public import SuperdiffusionCLT.Section6.Engine.Flatness
public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace

/-!
# Large-scale `C^{1,γ}` regularity: ingredients

Geometry of balls and cubes, the scale `m` attached to a radius, chains of slope-matched vectors
across scales, and the real-number combinations behind the gradient estimates.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb8b_exists_m (d : ℕ) [NeZero d] {R : ℝ} (hR : Real.sqrt d ≤ 2 * R) :
    ∃ m : ℕ, Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R ∧ 2 * R < Real.sqrt d * (3 : ℝ) ^ (m + 1) := by
  have hs : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
  have hx : 1 ≤ 2 * R / Real.sqrt d := by rwa [le_div_iff₀ hs, one_mul]
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_, ?_⟩
  · rwa [le_div_iff₀ hs, mul_comm] at h1
  · have := (div_lt_iff₀ hs).1 h2
    linarith only [this]

theorem eb8b_ball_mono (d : ℕ) [NeZero d] {Λ : ℝ} (hΛ : 1 ≤ Λ) {r ρ : ℝ} (hr : 0 < r)
    (hrρ : r ≤ ρ) (hρ : ρ ≤ Λ * r) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (ballMeasure ρ)) :
    ballL2 r f ≤ ENNReal.ofReal ((Real.sqrt d * Λ) ^ d) * ballL2 ρ f := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hs1 : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hspos : 0 < Real.sqrt d := by linarith only [hs1]
  have hρpos : 0 < ρ := lt_of_lt_of_le hr hrρ
  set C : ℝ := (Real.sqrt d * Λ) ^ d with hC
  have hC1 : 1 ≤ C := one_le_pow₀ (by nlinarith only [hs1, hΛ])
  have hC0 : 0 ≤ C := by linarith only [hC1]
  have hmpos : 0 < (2 * (r / Real.sqrt d)) ^ d := by positivity
  have h2ρ : 0 < (2 * ρ) ^ d := by positivity
  have hreal : ((2 * (r / Real.sqrt d)) ^ d)⁻¹ ≤ C ^ 2 * ((2 * ρ) ^ d)⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hmpos h2ρ, one_mul]
    have h3 : 2 * ρ ≤ Real.sqrt d * Λ * (2 * (r / Real.sqrt d)) := by
      have : Real.sqrt d * Λ * (2 * (r / Real.sqrt d)) = 2 * (Λ * r) := by
        field_simp
      rw [this]
      linarith only [hρ]
    calc (2 * ρ) ^ d ≤ (Real.sqrt d * Λ * (2 * (r / Real.sqrt d))) ^ d :=
          pow_le_pow_left₀ (by positivity) h3 d
      _ = C * (2 * (r / Real.sqrt d)) ^ d := mul_pow _ _ _
      _ ≤ C ^ 2 * (2 * (r / Real.sqrt d)) ^ d := by
        gcongr
        nlinarith only [hC1]
  have hcoef : (volume (euclidBall (d := d) r))⁻¹ ≤
      ENNReal.ofReal (C ^ 2) * (volume (euclidBall (d := d) ρ))⁻¹ := by
    calc (volume (euclidBall (d := d) r))⁻¹
        ≤ (ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d))⁻¹ :=
          ENNReal.inv_le_inv.2 (e0d_ball_vol_ge hr)
      _ = ENNReal.ofReal (((2 * (r / Real.sqrt d)) ^ d)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos hmpos).symm
      _ ≤ ENNReal.ofReal (C ^ 2 * ((2 * ρ) ^ d)⁻¹) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal ((2 * ρ) ^ d))⁻¹ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos h2ρ]
      _ ≤ _ := by gcongr; exact e0d_ball_vol_le hρpos
  have hle : ballMeasure (d := d) r ≤ ENNReal.ofReal (C ^ 2) • ballMeasure (d := d) ρ := by
    rw [Measure.le_iff]
    intro t ht
    rw [ballMeasure_apply, Measure.smul_apply, ballMeasure_apply, smul_eq_mul, ← mul_assoc]
    have hsub : euclidBall (d := d) r ∩ t ⊆ euclidBall ρ ∩ t :=
      Set.inter_subset_inter_left _ (euclidBall_mono hr.le hrρ)
    calc (volume (euclidBall (d := d) r))⁻¹ * volume (euclidBall r ∩ t)
        ≤ (ENNReal.ofReal (C ^ 2) * (volume (euclidBall (d := d) ρ))⁻¹) *
            volume (euclidBall r ∩ t) := by gcongr
      _ ≤ _ := by gcongr
  have h := e0d_eLpNorm_le hC0 hle f hf
  exact h

theorem eb8b_engNorm_memLp {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict U)) :
    MemLp (fun x => engNorm (F x)) 2 (volume.restrict U) := by
  have hcont : Continuous (fun e : Vec d => engNorm e) :=
    Real.continuous_sqrt.comp continuous_vecNormSq
  have hmeas : AEStronglyMeasurable (fun x => engNorm (F x)) (volume.restrict U) :=
    hcont.comp_aestronglyMeasurable hF.aestronglyMeasurable
  have hsum : MemLp (fun x => ∑ i : Fin d, |F x i|) 2 (volume.restrict U) :=
    memLp_finsetSum Finset.univ fun i _ => (hF.eval i).abs
  refine hsum.of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ engNorm (F x) := Real.sqrt_nonneg _
  have h1 : 0 ≤ ∑ i : Fin d, |F x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg h1]
  unfold engNorm
  refine Real.sqrt_le_iff.2 ⟨h1, ?_⟩
  unfold vecNormSq vecDot
  calc ∑ i, F x i * F x i = ∑ i, |F x i| * |F x i| :=
        Finset.sum_congr rfl fun i _ => (abs_mul_abs_self _).symm
    _ ≤ (∑ i, |F x i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum (f := fun j => |F x i| * |F x j|)
          (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)

theorem eb8b_gradMemLp_ball [NeZero d] {a : CoeffField d} {R : ℝ} (hR : 0 < R)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : IsBallSolution a R u g) :
    MemLp (fun x => engNorm (g x)) 2 (ballMeasure R) := by
  obtain ⟨v, -, hv2⟩ := h
  have hvec : MemLp v.toH1.grad 2 (volume.restrict (euclidBall R)) :=
    MeasureTheory.MemLp.of_eval fun i => v.toH1.gradMemL2 i
  have hg : MemLp g 2 (volume.restrict (euclidBall R)) := hvec.ae_eq hv2
  exact eb8a_memLp_ball hR (eb8b_engNorm_memLp hg)

theorem eb8b_entire_congr {a : CoeffField d} {u w : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsEntireSolution a u g) (huw : u =ᵐ[volume] w) : IsEntireSolution a w g := by
  intro R hR
  obtain ⟨v, hv1, hv2⟩ := h R hR
  exact ⟨v, hv1.trans (ae_restrict_of_ae huw), hv2⟩

theorem eb8b_iter [NeZero d] {mstar : ℕ} {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {δ : ℕ → ℝ}
    {Cz c9 : ℝ} (hCz : 0 ≤ Cz) (hc9 : 0 ≤ c9)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c9)
    (hfirst : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ e : Vec d,
      ∃ q : Vec d, affSlope k (V k q) = affSlope k (V m e))
    (hsurj : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ q : Vec d,
      ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q))
    (hcons : ∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
      affSlope n (V (m + 1) e') = affSlope n (V m e) →
      engNorm (e' - e) ≤ Cz * δ m * engNorm e)
    (t j : ℕ) (hj : mstar ≤ j) (e : Vec d) :
    ∃ e' : Vec d, affSlope mstar (V (j + t) e') = affSlope mstar (V j e) ∧
      engNorm e' ≤ (1 + Cz * c9) ^ t * engNorm e := by
  induction t with
  | zero => exact ⟨e, rfl, by simp⟩
  | succ t ih =>
    obtain ⟨e1, h1, hn1⟩ := ih
    have hjt : mstar ≤ j + t := by omega
    obtain ⟨q, hq⟩ := hfirst (j + t) mstar le_rfl hjt e1
    obtain ⟨e2, he2⟩ := hsurj (j + t + 1) mstar le_rfl (by omega) q
    have hslope : affSlope mstar (V (j + t + 1) e2) = affSlope mstar (V (j + t) e1) := by
      rw [he2, hq]
    have hc := hcons mstar (j + t) le_rfl hjt e1 e2 hslope
    refine ⟨e2, ?_, ?_⟩
    · rw [← h1]
      exact hslope
    · have hδj := hδ (j + t) hjt
      have hsplit : engNorm e2 ≤ engNorm (e2 - e1) + engNorm e1 := by
        have h := engNorm_add_le (e2 - e1) e1
        rwa [sub_add_cancel] at h
      have hn0 := engNorm_nonneg e1
      have hCd : Cz * δ (j + t) ≤ Cz * c9 := mul_le_mul_of_nonneg_left hδj.2 hCz
      have h2 : engNorm e2 ≤ (1 + Cz * c9) * engNorm e1 := by
        have h3 : Cz * δ (j + t) * engNorm e1 ≤ Cz * c9 * engNorm e1 :=
          mul_le_mul_of_nonneg_right hCd hn0
        linarith only [hsplit, hc, h3]
      calc engNorm e2 ≤ (1 + Cz * c9) * engNorm e1 := h2
        _ ≤ (1 + Cz * c9) * ((1 + Cz * c9) ^ t * engNorm e) := by
            gcongr
        _ = (1 + Cz * c9) ^ (t + 1) * engNorm e := by ring

theorem eb8b_flat_close [NeZero d] {k : ℕ} {u ψ W : Vec d → ℝ} {η κ Cf Cl δm Ω ne x : ℝ}
    (hu : MemLp u 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hW : MemLp W 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hψ : MemLp ψ 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hCf : 1 ≤ Cf) (hCl : 1 ≤ Cl) (hδ0 : 0 ≤ δm) (hδ1 : δm ≤ 1) (hΩ : 0 ≤ Ω) (hx : 0 ≤ x)
    (hκ : 0 ≤ κ)
    (h1 : cubeFlat k (fun y => u y - W y) ≤ Cf * (3 : ℝ) ^ (-((η - 3 * κ) * x)) * Ω)
    (h2 : cubeFlat k (fun y => ψ y - W y) ≤ Cl * δm * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * ne)
    (hne : ne ≤ Cf * Ω) :
    cubeFlat k (fun y => u y - ψ y) ≤ (Cf + Cl * Cf) * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * Ω := by
  have hsum := cubeFlat_add_le (hu.sub hW) (hW.sub hψ)
  have hfun : (fun y => (u y - W y) + (W y - ψ y)) = fun y => u y - ψ y := by
    funext y
    ring
  simp only [Pi.sub_apply, hfun] at hsum
  have hneg : cubeFlat k (fun y => W y - ψ y) = cubeFlat k (fun y => ψ y - W y) := by
    have h := cubeFlat_const_mul (d := d) k (-1) (fun y => ψ y - W y)
    have hf : (fun y => (-1 : ℝ) * (ψ y - W y)) = fun y => W y - ψ y := by
      funext y
      ring
    rw [hf] at h
    rw [h]
    simp
  have hP : (3 : ℝ) ^ (-((η - 3 * κ) * x)) ≤ (3 : ℝ) ^ (-((η - 6 * κ) * x)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith only [hκ, hx]
  have hP0 : 0 ≤ (3 : ℝ) ^ (-((η - 6 * κ) * x)) := by positivity
  have hCf0 : 0 ≤ Cf := by linarith only [hCf]
  have hCl0 : 0 ≤ Cl := by linarith only [hCl]
  have hA : Cf * (3 : ℝ) ^ (-((η - 3 * κ) * x)) * Ω ≤
      Cf * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * Ω := by gcongr
  have hB : Cl * δm * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * ne ≤
      Cl * δm * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * (Cf * Ω) :=
    mul_le_mul_of_nonneg_left hne (by positivity)
  have hC : Cl * δm * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * (Cf * Ω) ≤
      Cl * 1 * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * (Cf * Ω) := by gcongr
  have hall := hsum.trans (add_le_add (h1.trans hA) (hneg ▸ (h2.trans (hB.trans hC))))
  refine hall.trans (le_of_eq ?_)
  ring

theorem eb8b_sqrt_nine (y : ℝ) : Real.sqrt ((9 : ℝ) ^ y) = (3 : ℝ) ^ y := by
  have h : (9 : ℝ) ^ y = ((3 : ℝ) ^ y) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num [mul_comm]
  rw [h, Real.sqrt_sq (by positivity)]

theorem eb8b_combine {Cin Cs A sk sm Fl Om X Gh η κ x : ℝ} (hCin : 1 ≤ Cin) (hCs : 1 ≤ Cs)
    (hA : 0 ≤ A) (hsm : 0 < sm) (hFl : 0 ≤ Fl)
    (hHC : Gh ≤ Cin * Real.sqrt sk * Fl)
    (hfl : Fl ≤ A * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * Om)
    (hHP : Real.sqrt sm * Om ≤ Cin * X)
    (hs : sk ≤ Cs * (9 : ℝ) ^ (κ * x) * sm) :
    Gh ≤ (Cin * Cin * Real.sqrt Cs * A) * (3 : ℝ) ^ (-((η - 7 * κ) * x)) * X := by
  have hsk : Real.sqrt sk ≤ Real.sqrt Cs * (3 : ℝ) ^ (κ * x) * Real.sqrt sm := by
    refine (Real.sqrt_le_sqrt hs).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), eb8b_sqrt_nine]
  have hexp : (3 : ℝ) ^ (κ * x) * (3 : ℝ) ^ (-((η - 6 * κ) * x)) =
      (3 : ℝ) ^ (-((η - 7 * κ) * x)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hP : 0 ≤ (3 : ℝ) ^ (-((η - 6 * κ) * x)) := by positivity
  have hQ : 0 ≤ (3 : ℝ) ^ (κ * x) := by positivity
  have hsq : 0 ≤ Real.sqrt Cs := Real.sqrt_nonneg _
  calc Gh ≤ Cin * Real.sqrt sk * Fl := hHC
    _ ≤ Cin * (Real.sqrt Cs * (3 : ℝ) ^ (κ * x) * Real.sqrt sm) *
          (A * (3 : ℝ) ^ (-((η - 6 * κ) * x)) * Om) := by gcongr
    _ = (Cin * Real.sqrt Cs * A * ((3 : ℝ) ^ (κ * x) * (3 : ℝ) ^ (-((η - 6 * κ) * x)))) *
          (Real.sqrt sm * Om) := by ring
    _ ≤ (Cin * Real.sqrt Cs * A * ((3 : ℝ) ^ (κ * x) * (3 : ℝ) ^ (-((η - 6 * κ) * x)))) *
          (Cin * X) := by gcongr
    _ = _ := by rw [hexp]; ring

theorem eb8b_exp {η κ γ x q Λ : ℝ} (hη : η < 1) (hκ : 0 < κ) (hγ : 0 < γ) (hγη : γ + 7 * κ ≤ η)
    (hq : 0 < q) (hq1 : q ≤ 1) (hΛ : 1 ≤ Λ)
    (hqx : (3 : ℝ) ^ (-x) ≤ Λ * q) :
    (3 : ℝ) ^ (-((η - 7 * κ) * x)) ≤ Λ * q ^ γ := by
  have hε0 : 0 ≤ η - 7 * κ := by linarith only [hγ, hγη]
  have hε1 : η - 7 * κ ≤ 1 := by linarith only [hη, hκ]
  have h1 : (3 : ℝ) ^ (-((η - 7 * κ) * x)) = ((3 : ℝ) ^ (-x)) ^ (η - 7 * κ) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [h1]
  calc ((3 : ℝ) ^ (-x)) ^ (η - 7 * κ) ≤ (Λ * q) ^ (η - 7 * κ) :=
        Real.rpow_le_rpow (by positivity) hqx hε0
    _ = Λ ^ (η - 7 * κ) * q ^ (η - 7 * κ) := Real.mul_rpow (by linarith only [hΛ]) hq.le
    _ ≤ Λ * q ^ γ := by
        have ha : Λ ^ (η - 7 * κ) ≤ Λ := by
          calc Λ ^ (η - 7 * κ) ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ hε1
            _ = Λ := Real.rpow_one _
        have hb : q ^ (η - 7 * κ) ≤ q ^ γ :=
          Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith only [hγη])
        have hq0 : 0 ≤ q ^ (η - 7 * κ) := by positivity
        have hΛ0 : 0 ≤ Λ := by linarith only [hΛ]
        exact mul_le_mul ha hb hq0 hΛ0

end SuperdiffusionCLT.Section6
