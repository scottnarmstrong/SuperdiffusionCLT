/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.AffineSlopeB
public import SuperdiffusionCLT.Section6.Engine.BallCube

/-!
# Truncation and mean helpers for the global limit

Cubes restrictions of `L²` functions, truncation by the indicator of a cube, and the control of
an `L²(□_k)` norm by the flatness on `□_k` and the mean on a smaller cube.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb6b_memLp_down {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    MemLp f 2 (normalizedCubeMeasure (originCube d (l : ℤ))) := by
  induction k, hlk using Nat.le_induction with
  | base => exact hf
  | succ k _ ih => exact ih (e0b_memLp_step hf).1

theorem eb6b_vol_eq (k : ℕ) :
    volume.restrict (engCube d k) =
      ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) • normalizedCubeMeasure (originCube d (k : ℤ)) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.restrict_apply hs, Measure.smul_apply, e0d_normCube_apply k hs, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

theorem eb6b_memLp_restrict {m : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (m : ℤ)))) :
    MemLp f 2 (volume.restrict (engCube d m)) := by
  rw [eb6b_vol_eq]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem eb6b_memLp_trunc {m : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (m : ℤ)))) (k : ℕ) :
    MemLp ((engCube d m).indicator f) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
  have hmeas : MeasurableSet (engCube d m) := measurableSet_openCubeSet _
  have h1 : MemLp ((engCube d m).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hmeas).2 (eb6b_memLp_restrict hf)
  refine h1.of_measure_le_smul (c := ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹))
    ENNReal.ofReal_ne_top ?_
  refine Measure.le_iff.2 fun s hs => ?_
  rw [e0d_normCube_apply k hs, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (measure_mono Set.inter_subset_left) _

theorem eb6b_cubeL2_le_scale [NeZero d] {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeL2 l f ≤ (3 : ℝ) ^ (d * k) * cubeL2 k f := by
  have h := cubeL2_mono_scale hlk hf
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (d * l) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ (d * k) := one_le_pow₀ (by norm_num)
  have h0 := cubeL2_nonneg (d := d) l f
  have hk0 := cubeL2_nonneg (d := d) k f
  have h3 : cubeL2 l f ^ 2 ≤ ((3 : ℝ) ^ (d * k) * cubeL2 k f) ^ 2 := by
    have h4 : cubeL2 l f ^ 2 ≤ cubeL2 l f ^ 2 * (3 : ℝ) ^ (d * l) :=
      le_mul_of_one_le_right (sq_nonneg _) h1
    have h5 : cubeL2 k f ^ 2 * (3 : ℝ) ^ (d * k) ≤
        cubeL2 k f ^ 2 * ((3 : ℝ) ^ (d * k)) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [h2]) (sq_nonneg _)
    calc cubeL2 l f ^ 2 ≤ _ := h4
      _ ≤ _ := h
      _ ≤ _ := h5
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 h3

theorem eb6b_jensen {μ : Measure (Vec d)} [IsProbabilityMeasure μ] {g : Vec d → ℝ}
    (hg : MemLp g 2 μ) : (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h := e0b_expand hg (∫ x, g x ∂μ)
  have h0 : 0 ≤ ∫ x, (g x - ∫ y, g y ∂μ) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [h] at h0
  nlinarith only [h0]

theorem eb6b_cubeL2_const [NeZero d] (k : ℕ) (c : ℝ) :
    cubeL2 k (fun _ : Vec d => c) ≤ |c| := by
  have := e0b_isProb (d := d) k
  have h := e0c_cubeL2_sq k (g := fun _ : Vec d => c) (memLp_const _)
  simp only [integral_const, probReal_univ, one_smul] at h
  refine (pow_le_pow_iff_left₀ (cubeL2_nonneg _ _) (abs_nonneg c) two_ne_zero).1 ?_
  rw [h, sq_abs]

theorem eb6b_cubeL2_le_flat [NeZero d] {n k : ℕ} (hnk : n ≤ k) {h : Vec d → ℝ}
    (hh : MemLp h 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hmean : ∫ x, h x ∂(normalizedCubeMeasure (originCube d (n : ℤ))) = 0) :
    cubeL2 k h ≤ (1 + (3 : ℝ) ^ (d * k)) * ((3 : ℝ) ^ k * cubeFlat k h) := by
  have hpk := e0b_isProb (d := d) k
  have hpn := e0b_isProb (d := d) n
  set c := ∫ x, h x ∂(normalizedCubeMeasure (originCube d (k : ℤ))) with hc
  have hh0 : MemLp (fun x => h x - c) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    hh.sub (memLp_const _)
  have hflat : cubeFlat k h = ((3 : ℝ)⁻¹) ^ k * cubeL2 k (fun x => h x - c) := by
    unfold cubeFlat
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsplit : cubeL2 k h ≤ cubeL2 k (fun x => h x - c) + |c| := by
    have e : h = fun x => (h x - c) + (fun _ : Vec d => c) x := by funext x; simp
    calc cubeL2 k h = cubeL2 k (fun x => (h x - c) + (fun _ : Vec d => c) x) := by rw [← e]
      _ ≤ cubeL2 k (fun x => h x - c) + cubeL2 k (fun _ : Vec d => c) :=
          cubeL2_add_le hh0 (memLp_const _)
      _ ≤ _ := by gcongr; exact eb6b_cubeL2_const k c
  have hhn : MemLp h 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := eb6b_memLp_down hnk hh
  have hhn0 : MemLp (fun x => h x - c) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hhn.sub (memLp_const _)
  have hint : ∫ x, (h x - c) ∂(normalizedCubeMeasure (originCube d (n : ℤ))) = -c := by
    rw [integral_sub (hhn.integrable one_le_two) (integrable_const _), hmean]
    simp
  have hcn : |c| ≤ cubeL2 n (fun x => h x - c) := by
    have h1 := eb6b_jensen hhn0
    rw [hint, ← e0c_cubeL2_sq n hhn0] at h1
    refine (pow_le_pow_iff_left₀ (abs_nonneg c) (cubeL2_nonneg _ _) two_ne_zero).1 ?_
    rwa [sq_abs, ← neg_sq]
  have hcs := eb6b_cubeL2_le_scale hnk hh0
  have h3 : (3 : ℝ) ^ k * cubeFlat k h = cubeL2 k (fun x => h x - c) := by
    rw [hflat, ← mul_assoc, e0c_inv_mul, one_mul]
  rw [h3]
  nlinarith only [hsplit, hcn, hcs, cubeL2_nonneg (d := d) k (fun x => h x - c)]

theorem eb6b_affSlope_sub [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    affSlope n (fun x => f x - g x) = affSlope n f - affSlope n g := by
  have h := affSlope_add hf (hg.const_mul (-1))
  have h2 := affSlope_const_mul n (-1) g
  have e : (fun x => f x - g x) = fun x => f x + (-1 * g x) := by funext x; ring
  rw [e, h, h2, neg_one_smul, sub_eq_add_neg]

theorem eb6b_engNorm_neg (x : Vec d) : engNorm (-x) = engNorm x := by
  have := engNorm_smul (-1 : ℝ) x
  simpa using this

/-- Membership of a cube solution in `L²` of every smaller cube. -/
theorem eb6b_sol_memLp {a : CoeffField d} {m k : ℕ} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsSolOn a (engCube d m) u g) (hkm : k ≤ m) :
    MemLp u 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
  eb6b_memLp_down hkm h.memLp.1

/-- Components of the gradient of a cube solution are in `L²`. -/
theorem eb6b_grad_comp_memLp {a : CoeffField d} {m : ℕ} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsSolOn a (engCube d m) u g) (i : Fin d) :
    MemLp (fun x => g x i) 2 (normalizedCubeMeasure (originCube d (m : ℤ))) := by
  obtain ⟨v, -, hv2⟩ := h
  have h1 : MemLp (fun x => v.toH1.grad x i) 2 (volume.restrict (engCube d m)) :=
    v.toH1.gradMemL2 i
  have h2 : MemLp (fun x => g x i) 2 (volume.restrict (engCube d m)) :=
    h1.ae_eq (by filter_upwards [hv2] with x hx; rw [hx])
  exact memL2On_openCubeSet_normalizedCubeMeasure h2

theorem eb6b_solOn_congr {a : CoeffField d} {U : Set (Vec d)} (hU : MeasurableSet U)
    {u u' : Vec d → ℝ} {g g' : Vec d → Vec d} (h : IsSolOn a U u g)
    (hu : ∀ x ∈ U, u x = u' x) (hg : ∀ x ∈ U, g x = g' x) : IsSolOn a U u' g' := by
  obtain ⟨v, hv1, hv2⟩ := h
  refine ⟨v, hv1.trans ?_, hv2.trans ?_⟩
  · exact (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall hu)
  · exact (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall hg)

theorem eb6b_entire_congr {a : CoeffField d} {u u' : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsEntireSolution a u g) (hu : u' =ᵐ[volume] u) : IsEntireSolution a u' g := by
  intro R hR
  obtain ⟨v, hv1, hv2⟩ := h R hR
  exact ⟨v, hv1.trans (ae_restrict_of_ae hu.symm), hv2⟩

theorem eb6b_comp_le_engNorm (x : Vec d) (i : Fin d) : |x i| ≤ engNorm x := by
  unfold engNorm
  refine Real.abs_le_sqrt ?_
  unfold vecNormSq vecDot
  have : x i * x i ≤ ∑ j, x j * x j :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  nlinarith only [this]

theorem eb6b_cubeL2_comp_le {k : ℕ} {F : Vec d → Vec d} (i : Fin d)
    (hi : MemLp (fun x => F x i) 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hF : MemLp (fun x => engNorm (F x)) 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeL2 k (fun x => F x i) ≤ cubeGradL2 k F := by
  unfold cubeGradL2 cubeL2 cubeLpNorm
  refine ENNReal.toReal_mono hF.eLpNorm_ne_top ?_
  refine eLpNorm_mono_ae hi.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (engNorm_nonneg _)]
  exact eb6b_comp_le_engNorm (F x) i

theorem eb6b_slope_V [NeZero d] {a : CoeffField d} {mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    {n m : ℕ} (hn : mstar ≤ n) (hnm : n ≤ m) (e e' : Vec d) (c : ℝ) :
    affSlope n (V m (e + e')) = affSlope n (V m e) + affSlope n (V m e') ∧
      affSlope n (V m (c • e)) = c • affSlope n (V m e) := by
  have hmem : ∀ e, MemLp (V m e) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := fun e =>
    (hVsol m (hn.trans hnm) e).elim fun g hg => eb6b_sol_memLp hg hnm
  constructor
  · have : V m (e + e') = fun x => V m e x + V m e' x := by rw [map_add]; rfl
    rw [this]
    exact affSlope_add (hmem e) (hmem e')
  · have : V m (c • e) = fun x => c * V m e x := by rw [map_smul]; rfl
    rw [this]
    exact affSlope_const_mul n c _

/-- Uniqueness of the matching slope. -/
theorem eb6b_unique [NeZero d] {a : CoeffField d} {mstar : ℕ} {δ : ℕ → ℝ} {K : ℝ} {C : ℕ → ℕ → ℝ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      engNorm (affSlope j (V j e) - e) ≤ K * δ j * engNorm e)
    (hK : ∀ j : ℕ, mstar ≤ j → K * δ j ≤ 1 / 2)
    (hlow : ∀ m n : ℕ, mstar ≤ n → n ≤ m → ∀ e : Vec d, ∃ q : Vec d,
      affSlope n (V n q) = affSlope n (V m e) ∧ engNorm e ≤ C m n * engNorm q)
    {n m : ℕ} (hn : mstar ≤ n) (hnm : n ≤ m) {e e' : Vec d}
    (h : affSlope n (V m e) = affSlope n (V m e')) : e = e' := by
  have hmem : ∀ e, MemLp (V m e) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := fun e =>
    (hVsol m (hn.trans hnm) e).elim fun g hg => eb6b_sol_memLp hg hnm
  have h0 : affSlope n (V m (e - e')) = 0 := by
    have : V m (e - e') = fun x => V m e x - V m e' x := by rw [map_sub]; rfl
    rw [this, eb6b_affSlope_sub (hmem e) (hmem e'), h, sub_self]
  obtain ⟨q, hq1, hq2⟩ := hlow m n hn hnm (e - e')
  rw [h0] at hq1
  have h1 := hflat n hn q
  rw [hq1, zero_sub, eb6b_engNorm_neg] at h1
  have h2 := hK n hn
  have h3 : engNorm q = 0 := by
    have := engNorm_nonneg q
    nlinarith only [h1, h2, this, mul_le_mul_of_nonneg_right h2 this]
  rw [h3, mul_zero] at hq2
  exact sub_eq_zero.1 (e0c_engNorm_eq_zero (le_antisymm hq2 (engNorm_nonneg _)))

theorem eb6b_exists_Em [NeZero d] {a : CoeffField d} {mstar : ℕ} {δ : ℕ → ℝ} {K : ℝ} {C : ℕ → ℕ → ℝ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      engNorm (affSlope j (V j e) - e) ≤ K * δ j * engNorm e)
    (hK : ∀ j : ℕ, mstar ≤ j → K * δ j ≤ 1 / 2)
    (hlow : ∀ m n : ℕ, mstar ≤ n → n ≤ m → ∀ e : Vec d, ∃ q : Vec d,
      affSlope n (V n q) = affSlope n (V m e) ∧ engNorm e ≤ C m n * engNorm q)
    (hup : ∀ m n : ℕ, mstar ≤ n → n ≤ m → ∀ q : Vec d, ∃ e : Vec d,
      affSlope n (V m e) = affSlope n (V n q))
    {n : ℕ} (hn : mstar ≤ n) :
    ∃ Em : ℕ → Vec d →ₗ[ℝ] Vec d,
      ∀ (j : ℕ) (e0 : Vec d), affSlope n (V (n + j) (Em j e0)) = affSlope n (V n e0) := by
  choose E hE using fun (j : ℕ) (e0 : Vec d) => hup (n + j) n hn (Nat.le_add_right n j) e0
  have uniq : ∀ j : ℕ, ∀ {e e' : Vec d},
      affSlope n (V (n + j) e) = affSlope n (V (n + j) e') → e = e' :=
    fun j _ _ h => eb6b_unique hVsol hflat hK hlow hn (Nat.le_add_right n j) h
  have hadd : ∀ (j : ℕ) (e0 e1 : Vec d), E j (e0 + e1) = E j e0 + E j e1 := by
    intro j e0 e1
    refine uniq j ?_
    have h1 := (eb6b_slope_V hVsol hn (Nat.le_add_right n j) (E j e0) (E j e1) 1).1
    have h2 := (eb6b_slope_V hVsol hn le_rfl e0 e1 1).1
    rw [hE, h1, hE, hE, h2]
  have hsmul : ∀ (j : ℕ) (c : ℝ) (e0 : Vec d), E j (c • e0) = c • E j e0 := by
    intro j c e0
    refine uniq j ?_
    have h1 := (eb6b_slope_V hVsol hn (Nat.le_add_right n j) (E j e0) 0 c).2
    have h2 := (eb6b_slope_V hVsol hn le_rfl e0 0 c).2
    rw [hE, h1, hE, h2]
  exact ⟨fun j => ⟨⟨E j, hadd j⟩, fun c e0 => hsmul j c e0⟩, fun j e0 => hE j e0⟩

theorem eb6b_rpow_split (η κ m k : ℝ) (i : ℕ) :
    (3 : ℝ) ^ (-((η - 5 * κ) * (m + i - k))) * (3 : ℝ) ^ (κ * (i : ℝ)) =
      (3 : ℝ) ^ (-((η - 5 * κ) * (m - k))) * (3 : ℝ) ^ (-((η - 6 * κ) * (i : ℝ))) := by
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

theorem eb6b_rpow_le_geom {c : ℝ} (hc : 1 / 4 ≤ c) (i : ℕ) :
    (3 : ℝ) ^ (-(c * (i : ℝ))) ≤ ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ i := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith only [hc, this]

theorem eb6b_geom_pos : 0 < (3 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _

theorem eb6b_geom_lt_one : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem eb6b_one_add_le (κ : ℝ) (hκ : 0 ≤ κ) : 1 + κ ≤ (3 : ℝ) ^ κ := by
  have h1 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith only [this]
  rw [Real.rpow_def_of_pos (by norm_num)]
  have := Real.add_one_le_exp (Real.log 3 * κ)
  nlinarith only [this, h1, hκ]

theorem eb6b_growth {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℕ → Vec d} {B : ℕ → ℝ}
    (h : ∀ j, engNorm (ε (j + 1) - ε j) ≤ B j * engNorm (ε j)) (hB : ∀ j, B j ≤ κ) (j i : ℕ) :
    engNorm (ε (j + i)) ≤ (3 : ℝ) ^ (κ * (i : ℝ)) * engNorm (ε j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : ε (j + (i + 1)) = (ε (j + i + 1) - ε (j + i)) + ε (j + i) := by
      rw [← add_assoc]; abel
    have h1 := engNorm_add_le (ε (j + i + 1) - ε (j + i)) (ε (j + i))
    have h2 := h (j + i)
    have h3 := hB (j + i)
    have h4 := eb6b_one_add_le κ hκ
    have h0 := engNorm_nonneg (ε (j + i))
    have h5 : (3 : ℝ) ^ (κ * ((i + 1 : ℕ) : ℝ)) = (3 : ℝ) ^ (κ * (i : ℝ)) * (3 : ℝ) ^ κ := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
    rw [e, h5]
    have h6 : (1 + κ) * engNorm (ε (j + i)) ≤ (3 : ℝ) ^ κ * engNorm (ε (j + i)) :=
      mul_le_mul_of_nonneg_right h4 h0
    have h7 : (3 : ℝ) ^ κ * engNorm (ε (j + i)) ≤
        (3 : ℝ) ^ κ * ((3 : ℝ) ^ (κ * (i : ℝ)) * engNorm (ε j)) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have h8 : B (j + i) * engNorm (ε (j + i)) ≤ κ * engNorm (ε (j + i)) :=
      mul_le_mul_of_nonneg_right h3 h0
    nlinarith only [h1, h2, h6, h7, h8]

theorem eb6b_tail_real {η κ Cz m0 k0 : ℝ} (hη : 1 / 2 ≤ η) (hκ : κ ≤ 1 / 24) (hCz : 0 ≤ Cz)
    {D N f : ℕ → ℝ} (hD : ∀ i, D i ≤ D 0) (hD0 : ∀ i, 0 ≤ D i)
    (hN : ∀ i, N i ≤ (3 : ℝ) ^ (κ * (i : ℝ)) * N 0) (hN0 : ∀ i, 0 ≤ N i)
    (hf : ∀ i : ℕ, f i ≤ Cz * D i * (3 : ℝ) ^ (-((η - 5 * κ) * (m0 + i - k0))) * N i) (i : ℕ) :
    f i ≤ (Cz * D 0 * (3 : ℝ) ^ (-((η - 5 * κ) * (m0 - k0))) * N 0) *
      ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ i := by
  have h1 := eb6b_rpow_split η κ m0 k0 i
  have h2 := eb6b_rpow_le_geom (c := η - 6 * κ) (by linarith only [hη, hκ]) i
  have hp : (0 : ℝ) < (3 : ℝ) ^ (-((η - 5 * κ) * (m0 + i - k0))) := by positivity
  have hq : (0 : ℝ) < (3 : ℝ) ^ (κ * (i : ℝ)) := by positivity
  have hp0 : (0 : ℝ) < (3 : ℝ) ^ (-((η - 5 * κ) * (m0 - k0))) := by positivity
  calc f i ≤ Cz * D i * (3 : ℝ) ^ (-((η - 5 * κ) * (m0 + i - k0))) * N i := hf i
    _ ≤ Cz * D 0 * (3 : ℝ) ^ (-((η - 5 * κ) * (m0 + i - k0))) *
          ((3 : ℝ) ^ (κ * (i : ℝ)) * N 0) := by
        have := hD i
        have := hN i
        have := hD0 i
        have := hN0 i
        have := mul_nonneg (mul_nonneg hCz (hD0 0)) hp.le
        gcongr
    _ = (Cz * D 0 * N 0) * ((3 : ℝ) ^ (-((η - 5 * κ) * (m0 + i - k0))) *
          (3 : ℝ) ^ (κ * (i : ℝ))) := by ring
    _ = (Cz * D 0 * N 0) * ((3 : ℝ) ^ (-((η - 5 * κ) * (m0 - k0))) *
          (3 : ℝ) ^ (-((η - 6 * κ) * (i : ℝ)))) := by rw [h1]
    _ ≤ (Cz * D 0 * N 0) * ((3 : ℝ) ^ (-((η - 5 * κ) * (m0 - k0))) *
          ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ i) := by
        have := hD0 0
        have := hN0 0
        gcongr
    _ = _ := by ring

theorem eb6b_summable_of_bound {η κ C : ℝ} (hη : 1 / 2 ≤ η) (hκ : κ ≤ 1 / 24)
    (hC : 0 ≤ C) {n k : ℕ} {D N : ℕ → ℝ} (hD : ∀ i j : ℕ, i ≤ j → D j ≤ D i)
    (hD0 : ∀ i, 0 ≤ D i) (hN : ∀ j i : ℕ, N (j + i) ≤ (3 : ℝ) ^ (κ * (i : ℝ)) * N j)
    (hN0 : ∀ i, 0 ≤ N i) {t : ℕ → ℝ} (ht0 : ∀ j, 0 ≤ t j) (j0 : ℕ)
    (ht : ∀ j : ℕ, j0 ≤ j →
      t j ≤ C * D j * (3 : ℝ) ^ (-((η - 5 * κ) * (((n + j : ℕ) : ℝ) - (k : ℝ)))) * N j) :
    Summable t := by
  have hb := fun i : ℕ => eb6b_tail_real (η := η) (κ := κ) (Cz := C) (m0 := ((n + j0 : ℕ) : ℝ))
    (k0 := (k : ℝ)) hη hκ hC (D := fun i => D (j0 + i)) (N := fun i => N (j0 + i))
    (f := fun i => t (j0 + i)) (fun i => hD _ _ (Nat.le_add_right _ _)) (fun i => hD0 _)
    (fun i => hN j0 i) (fun i => hN0 _)
    (fun i => by
      have := ht (j0 + i) (Nat.le_add_right _ _)
      simpa [add_assoc, Nat.cast_add] using this) i
  have hs : Summable fun i : ℕ => t (j0 + i) :=
    Summable.of_nonneg_of_le (fun i => ht0 _) hb
      ((summable_geometric_of_lt_one eb6b_geom_pos.le eb6b_geom_lt_one).mul_left _)
  have : Summable fun i : ℕ => t (i + j0) := by simpa only [add_comm] using hs
  exact (summable_nat_add_iff j0).1 this

end SuperdiffusionCLT.Section6
