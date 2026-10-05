/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.LimitC
public import SuperdiffusionCLT.Section6.Engine.BallCube
public import SuperdiffusionCLT.Section6.Engine.ZeroSlopeB
public import SuperdiffusionCLT.Section6.Engine.BlockDecayB

/-!
# The Liouville theorem for the corrected affine functions: growth and averages
-/

@[expose] public section

open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter

variable {d : ℕ}

theorem eb7_entire_cube [NeZero d] {a : CoeffField d}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    {f : Vec d → ℝ} {g : Vec d → Vec d} (h : IsEntireSolution a f g) (k : ℕ) :
    IsSolOn a (engCube d k) f g := by
  have hpos : 0 < Real.sqrt d * (3 : ℝ) ^ k :=
    mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))) (by positivity)
  exact IsSolOn.cube_of_ball (hell k) (by linarith only [hpos]) (h _ hpos)

theorem eb7_entire_memLp [NeZero d] {a : CoeffField d}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    {f : Vec d → ℝ} {g : Vec d → Vec d} (h : IsEntireSolution a f g) (k : ℕ) :
    MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
  (eb7_entire_cube hell h k).memLp.1

theorem eb7_L2_le [NeZero d] {k : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeL2 k f ≤ |cubeAverage (originCube d (k : ℤ)) f| + (3 : ℝ) ^ k * cubeFlat k f := by
  set c := cubeAverage (originCube d (k : ℤ)) f with hc
  have hh0 : MemLp (fun x => f x - c) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    hf.sub (memLp_const _)
  have h3 : (3 : ℝ) ^ k * cubeFlat k f = cubeL2 k (fun x => f x - c) := by
    unfold cubeFlat
    rw [← hc, ← mul_assoc, e0c_inv_mul, one_mul]
  have e : f = fun x => (f x - c) + (fun _ : Vec d => c) x := by funext x; simp
  calc cubeL2 k f = cubeL2 k (fun x => (f x - c) + (fun _ : Vec d => c) x) := by rw [← e]
    _ ≤ cubeL2 k (fun x => f x - c) + cubeL2 k (fun _ : Vec d => c) :=
        cubeL2_add_le hh0 (memLp_const _)
    _ ≤ _ := by linarith only [h3, eb6b_cubeL2_const (d := d) k c]

theorem eb7_avg_step [NeZero d] {k : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ)))) :
    |cubeAverage (originCube d (k : ℤ)) f - cubeAverage (originCube d ((k + 1 : ℕ) : ℤ)) f| ≤
      (3 : ℝ) ^ d * ((3 : ℝ) ^ (k + 1) * cubeFlat (k + 1) f) := by
  set c := cubeAverage (originCube d ((k + 1 : ℕ) : ℤ)) f with hc
  have hg1 : MemLp (fun x => f x - c) 2
      (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ))) := hf.sub (memLp_const _)
  have hfk : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := (e0b_memLp_step hf).1
  have hg0 : MemLp (fun x => f x - c) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    hfk.sub (memLp_const _)
  have hpk := e0b_isProb (d := d) k
  have hint : cubeAverage (originCube d (k : ℤ)) f - c =
      ∫ x, (f x - c) ∂(normalizedCubeMeasure (originCube d (k : ℤ))) := by
    rw [integral_sub (hfk.integrable one_le_two) (integrable_const _),
      cubeAverage_eq_integral_normalizedCubeMeasure]
    simp
  have h1 : |∫ x, (f x - c) ∂(normalizedCubeMeasure (originCube d (k : ℤ)))| ≤
      cubeL2 k (fun x => f x - c) := by
    have h := eb6b_jensen hg0
    rw [← e0c_cubeL2_sq k hg0] at h
    exact abs_le_of_sq_le_sq h (cubeL2_nonneg _ _)
  have h2 : cubeL2 k (fun x => f x - c) ≤ (3 : ℝ) ^ d * cubeL2 (k + 1) (fun x => f x - c) := by
    have h := e0b_step hg1
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    refine (pow_le_pow_iff_left₀ (cubeL2_nonneg _ _) (mul_nonneg (by positivity) (cubeL2_nonneg _ _)) two_ne_zero).1 ?_
    calc cubeL2 k (fun x => f x - c) ^ 2 ≤ (3 : ℝ) ^ d * cubeL2 (k + 1) (fun x => f x - c) ^ 2 := h
      _ ≤ (3 : ℝ) ^ d * cubeL2 (k + 1) (fun x => f x - c) ^ 2 * (3 : ℝ) ^ d :=
        le_mul_of_one_le_right (by positivity) h3
      _ = _ := by ring
  have h4 : (3 : ℝ) ^ (k + 1) * cubeFlat (k + 1) f = cubeL2 (k + 1) (fun x => f x - c) := by
    unfold cubeFlat
    rw [← hc, ← mul_assoc, e0c_inv_mul, one_mul]
  rw [h4, hint]
  exact h1.trans h2

theorem eb7_avg_growth [NeZero d] {f : Vec d → ℝ} {s : ℕ} {B t : ℝ} (hB : 0 ≤ B) (ht : 1 ≤ t)
    (hf : ∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hfl : ∀ k : ℕ, s ≤ k → cubeFlat k f ≤ B * t ^ k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ, s ≤ k →
      |cubeAverage (originCube d (k : ℤ)) f| ≤ A * (3 * t) ^ k := by
  have h3d : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  refine ⟨|cubeAverage (originCube d (s : ℤ)) f| + 2 * (3 : ℝ) ^ d * B, by positivity, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (1 : ℝ) ≤ (3 * t) ^ s := one_le_pow₀ (by linarith only [ht])
    have h2 : 0 ≤ 2 * (3 : ℝ) ^ d * B := by positivity
    nlinarith only [h1, h2, abs_nonneg (cubeAverage (originCube d (s : ℤ)) f)]
  | succ k hsk ih =>
    have hs := eb7_avg_step (hf (k + 1))
    have hfl' := hfl (k + 1) (by omega)
    set A := |cubeAverage (originCube d (s : ℤ)) f| + 2 * (3 : ℝ) ^ d * B with hA
    have hA2 : 2 * (3 : ℝ) ^ d * B ≤ A := by
      have := abs_nonneg (cubeAverage (originCube d (s : ℤ)) f)
      linarith only [this]
    have hpow : (3 : ℝ) ^ (k + 1) * t ^ (k + 1) = (3 * t) ^ (k + 1) := (mul_pow 3 t (k + 1)).symm
    have hstep : (3 : ℝ) ^ d * ((3 : ℝ) ^ (k + 1) * cubeFlat (k + 1) f) ≤
        (3 : ℝ) ^ d * B * (3 * t) ^ (k + 1) := by
      calc (3 : ℝ) ^ d * ((3 : ℝ) ^ (k + 1) * cubeFlat (k + 1) f)
          ≤ (3 : ℝ) ^ d * ((3 : ℝ) ^ (k + 1) * (B * t ^ (k + 1))) := by gcongr
        _ = (3 : ℝ) ^ d * B * (3 * t) ^ (k + 1) := by rw [← hpow]; ring
    have hq : 0 ≤ (3 * t) ^ k := by positivity
    have hpk : (3 * t) ^ (k + 1) = (3 * t) ^ k * (3 * t) := pow_succ _ _
    have h4 : |cubeAverage (originCube d ((k + 1 : ℕ) : ℤ)) f| ≤
        |cubeAverage (originCube d (k : ℤ)) f| + (3 : ℝ) ^ d * B * (3 * t) ^ (k + 1) := by
      have := abs_sub_abs_le_abs_sub (cubeAverage (originCube d ((k + 1 : ℕ) : ℤ)) f)
        (cubeAverage (originCube d (k : ℤ)) f)
      rw [abs_sub_comm] at this
      linarith only [this, hs, hstep]
    rw [hpk] at h4 ⊢
    have hA0 : 0 ≤ (3 : ℝ) ^ d * B := by positivity
    have e1 : 0 ≤ (3 * t) ^ k * (A - 2 * ((3 : ℝ) ^ d * B)) * (3 * t - 1) :=
      mul_nonneg (mul_nonneg hq (by linarith only [hA2])) (by linarith only [ht])
    have e2 : 0 ≤ (3 * t) ^ k * ((3 : ℝ) ^ d * B) * (3 * t - 2) :=
      mul_nonneg (mul_nonneg hq hA0) (by linarith only [ht])
    nlinarith only [h4, ih, e1, e2]
  
theorem eb7_L2_growth [NeZero d] {f : Vec d → ℝ} {s : ℕ} {B t : ℝ} (hB : 0 ≤ B) (ht : 1 ≤ t)
    (hf : ∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hfl : ∀ k : ℕ, s ≤ k → cubeFlat k f ≤ B * t ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, s ≤ k → cubeL2 k f ≤ C * (3 * t) ^ k := by
  obtain ⟨A, hA, hAk⟩ := eb7_avg_growth hB ht hf hfl
  refine ⟨A + B, add_nonneg hA hB, fun k hk => ?_⟩
  have h1 := eb7_L2_le (hf k)
  have hpow : (3 : ℝ) ^ k * t ^ k = (3 * t) ^ k := (mul_pow 3 t k).symm
  have h2 : (3 : ℝ) ^ k * cubeFlat k f ≤ B * (3 * t) ^ k := by
    calc (3 : ℝ) ^ k * cubeFlat k f ≤ (3 : ℝ) ^ k * (B * t ^ k) := by gcongr; exact hfl k hk
      _ = B * (3 * t) ^ k := by rw [← hpow]; ring
  have h3 := hAk k hk
  linarith only [h1, h2, h3]

theorem eb7_rpow_pow_comm (κ : ℝ) (k : ℕ) :
    ((3 : ℝ) ^ κ) ^ k = ((3 : ℝ) ^ k) ^ κ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

theorem eb7_real_bound {γ κ r : ℝ} {k : ℕ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκγ : κ ≤ γ)
    (hr : 1 ≤ r) (h6 : (3 : ℝ) ^ k ≤ 6 * r) :
    r ^ (-(1 + γ)) * (3 * (3 : ℝ) ^ κ) ^ k ≤ 36 := by
  have hr0 : 0 < r := by linarith only [hr]
  have h1 : ((3 : ℝ) ^ κ) ^ k ≤ (6 * r) ^ κ := by
    rw [eb7_rpow_pow_comm]
    exact Real.rpow_le_rpow (by positivity) h6 hκ
  have h2 : (6 * r) ^ κ ≤ 6 * r ^ κ := by
    rw [Real.mul_rpow (by norm_num) hr0.le]
    have : (6 : ℝ) ^ κ ≤ 6 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hκ1
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h3 : (3 * (3 : ℝ) ^ κ) ^ k ≤ (6 * r) * (6 * r ^ κ) := by
    rw [mul_pow]
    exact mul_le_mul h6 (h1.trans h2) (by positivity) (by positivity)
  have h4 : r ^ (-(1 + γ)) * (r * r ^ κ) ≤ 1 := by
    have e : r * r ^ κ = r ^ (1 + κ) := by rw [Real.rpow_add hr0, Real.rpow_one]
    rw [e, ← Real.rpow_add hr0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith only [hκγ])
  have h5 : 0 ≤ r ^ (-(1 + γ)) := by positivity
  calc r ^ (-(1 + γ)) * (3 * (3 : ℝ) ^ κ) ^ k ≤ r ^ (-(1 + γ)) * ((6 * r) * (6 * r ^ κ)) :=
        mul_le_mul_of_nonneg_left h3 h5
    _ = 36 * (r ^ (-(1 + γ)) * (r * r ^ κ)) := by ring
    _ ≤ 36 * 1 := by gcongr
    _ = 36 := by norm_num

theorem eb7_exists_scale {r : ℝ} {s : ℕ} (hr : (3 : ℝ) ^ s ≤ r) (h1 : 1 ≤ r) :
    ∃ k : ℕ, s ≤ k ∧ 2 * r ≤ (3 : ℝ) ^ k ∧ (3 : ℝ) ^ k ≤ 6 * r := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := 2 * r) (by linarith only [h1])
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨n + 1, ?_, hn2.le, ?_⟩
  · have : (3 : ℝ) ^ s < 3 ^ (n + 1) := by linarith only [hr, hn2, h1]
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 this |>.le
  · rw [pow_succ]
    linarith only [hn1]

theorem eb7_limsup_of_cube (d : ℕ) [NeZero d] {γ κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκγ : κ ≤ γ) {f : Vec d → ℝ} {s : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k : ℕ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hbd : ∀ k : ℕ, s ≤ k → cubeL2 k f ≤ C * (3 * (3 : ℝ) ^ κ) ^ k) :
    Filter.limsup (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r f)
      Filter.atTop < ⊤ := by
  obtain ⟨Cd, hCd, hball⟩ := ballL2_le_cubeL2 d
  refine lt_of_le_of_lt (Filter.limsup_le_of_le (by isBoundedDefault)
    (a := ENNReal.ofReal (Cd * C * 36)) ?_) ENNReal.ofReal_lt_top
  filter_upwards [Filter.eventually_ge_atTop (max 1 ((3 : ℝ) ^ s))] with r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrs : (3 : ℝ) ^ s ≤ r := (le_max_right _ _).trans hr
  obtain ⟨k, hsk, h2, h6⟩ := eb7_exists_scale hrs hr1
  have hr0 : 0 < r := by linarith only [hr1]
  have hb := hball r k hr0 h2 (by linarith only [h6, hr1]) f (hf k)
  have hb2 : ballL2 r f ≤ ENNReal.ofReal (Cd * (C * (3 * (3 : ℝ) ^ κ) ^ k)) :=
    hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hbd k hsk)
      (by linarith only [hCd])))
  have hrb := eb7_real_bound (γ := γ) (k := k) hκ hκ1 hκγ hr1 h6
  calc ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r f
      ≤ ENNReal.ofReal (r ^ (-(1 + γ))) *
          ENNReal.ofReal (Cd * (C * (3 * (3 : ℝ) ^ κ) ^ k)) := by gcongr
    _ = ENNReal.ofReal (r ^ (-(1 + γ)) * (Cd * (C * (3 * (3 : ℝ) ^ κ) ^ k))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (Cd * C * 36) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc r ^ (-(1 + γ)) * (Cd * (C * (3 * (3 : ℝ) ^ κ) ^ k))
            = (Cd * C) * (r ^ (-(1 + γ)) * (3 * (3 : ℝ) ^ κ) ^ k) := by ring
          _ ≤ (Cd * C) * 36 := by
              gcongr

theorem eb7_ball_memLp [NeZero d] {a : CoeffField d} {r : ℝ} (hr : 0 < r) {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : IsBallSolution a r u g) : MemLp u 2 (ballMeasure r) := by
  obtain ⟨v, hv1, -⟩ := h
  have h1 : MemLp u 2 (volume.restrict (euclidBall r)) := v.toH1.memL2.ae_eq hv1
  have hpos : volume (euclidBall (d := d) r) ≠ 0 := by
    refine (IsOpen.measure_pos volume (isOpen_euclidBall r) ⟨0, ?_⟩).ne'
    show vecNormSq (0 : Vec d) < r ^ 2
    simp [vecNormSq, vecDot, hr]
  have hne : (volume (euclidBall (d := d) r))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hpos
  exact h1.smul_measure hne

theorem eb7_rpow_nat_pow (γ : ℝ) (m : ℕ) :
    ((3 : ℝ) ^ m) ^ γ = (3 : ℝ) ^ (γ * (m : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

theorem eb7_flat_of_limsup (d : ℕ) [NeZero d] {γ : ℝ} {a : CoeffField d}
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hsol : IsEntireSolution a u g)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hlim : Filter.limsup (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r u)
      Filter.atTop < ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      cubeFlat m u ≤ B * (3 : ℝ) ^ (γ * (m : ℝ)) := by
  obtain ⟨Cd, hCd, hball⟩ := cubeL2_le_ballL2 d
  obtain ⟨C, hlt, hCt⟩ := exists_between hlim
  have hev := Filter.eventually_lt_of_limsup_lt hlt
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨m0, hm0⟩ := pow_unbounded_of_one_lt R0 (by norm_num : (1 : ℝ) < 3)
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 hd1
  have hsd : Real.sqrt d ≤ d := by
    calc Real.sqrt d ≤ Real.sqrt d * Real.sqrt d := le_mul_of_one_le_right (by linarith only [hs1]) hs1
      _ = d := Real.mul_self_sqrt (by linarith only [hd1])
  refine ⟨Cd * C.toReal * Real.sqrt d ^ (1 + γ), by positivity, m0, fun m hm => ?_⟩
  set r : ℝ := Real.sqrt d * (3 : ℝ) ^ m with hr
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hr0 : 0 < r := mul_pos (by linarith only [hs1]) h3m
  have h3 : R0 ≤ (3 : ℝ) ^ m := hm0.le.trans (pow_le_pow_right₀ (by norm_num) hm)
  have hrR : R0 ≤ r := by
    calc R0 ≤ (3 : ℝ) ^ m := h3
      _ = 1 * (3 : ℝ) ^ m := (one_mul _).symm
      _ ≤ r := by rw [hr]; gcongr
  have hkey := (hR0 r hrR).le
  have hCfin : C ≠ ⊤ := hCt.ne
  have hmem := eb7_ball_memLp hr0 (hsol r hr0)
  have hc := hball r m (by rw [hr]; linarith only [h3m, hs1, mul_pos (by linarith only [hs1] : (0 : ℝ) < Real.sqrt d) h3m])
    (by
      have : (d : ℝ) * (3 : ℝ) ^ (m + 2) = 9 * ((d : ℝ) * (3 : ℝ) ^ m) := by rw [pow_add]; ring
      rw [this, hr]
      nlinarith only [hsd, h3m, hs1])
    u hmem
  have hb : ballL2 r u ≤ ENNReal.ofReal (r ^ (1 + γ)) * C := by
    have e : ballL2 r u = ENNReal.ofReal (r ^ (1 + γ)) *
        (ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r u) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hr0]
      simp
    rw [e]
    exact mul_le_mul' le_rfl hkey
  have hbt : (ballL2 r u).toReal ≤ r ^ (1 + γ) * C.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCfin) hb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hmu := eb6b_memLp_down (le_refl m) (eb7_entire_memLp hell hsol m)
  have hfl := cubeFlat_le_of_sub_const hmu 0
  simp only [sub_zero] at hfl
  have hr1 : r ^ (1 + γ) = Real.sqrt d ^ (1 + γ) * (3 : ℝ) ^ m * (3 : ℝ) ^ (γ * (m : ℝ)) := by
    rw [hr, Real.mul_rpow (by linarith only [hs1]) h3m.le, Real.rpow_add h3m, Real.rpow_one,
      eb7_rpow_nat_pow]
    ring
  calc cubeFlat m u ≤ ((3 : ℝ)⁻¹) ^ m * cubeL2 m u := hfl
    _ ≤ ((3 : ℝ)⁻¹) ^ m * (Cd * (r ^ (1 + γ) * C.toReal)) := by
        gcongr
        exact hc.trans (mul_le_mul_of_nonneg_left hbt (by linarith only [hCd]))
    _ = Cd * C.toReal * Real.sqrt d ^ (1 + γ) * (3 : ℝ) ^ (γ * (m : ℝ)) := by
        rw [hr1]
        have : ((3 : ℝ)⁻¹) ^ m * (3 : ℝ) ^ m = 1 := by rw [← mul_pow]; simp
        calc ((3 : ℝ)⁻¹) ^ m * (Cd * (Real.sqrt d ^ (1 + γ) * (3 : ℝ) ^ m * (3 : ℝ) ^ (γ * (m : ℝ)) * C.toReal))
            = (((3 : ℝ)⁻¹) ^ m * (3 : ℝ) ^ m) * (Cd * C.toReal * Real.sqrt d ^ (1 + γ) *
                (3 : ℝ) ^ (γ * (m : ℝ))) := by ring
          _ = _ := by rw [this, one_mul]

end SuperdiffusionCLT.Section6
