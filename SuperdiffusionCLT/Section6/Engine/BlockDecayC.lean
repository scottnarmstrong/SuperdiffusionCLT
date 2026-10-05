/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.BlockDecayB

/-!
# One-block decay: the basic step and the iteration

The basic step from a scale `t` to a lower scale `l` (harmonic approximation, a single affine
function for all target scales, replacement by `V_j e`), the iteration `ĥ` scales at a time, and
the one-block decay in simultaneous form.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb4_inv_pow_shift (n : ℕ) : ((3 : ℝ)⁻¹) ^ n = 27 * ((3 : ℝ)⁻¹) ^ (n + 3) := by
  rw [pow_add]
  norm_num
  ring

/-- The scale-normalized form of the harmonic approximation at one target scale. -/
theorem eb4_hF4_flat [NeZero d] {τ i : ℕ} {w : Vec d → ℝ} (hw : MemLp w 2 (eb4_mu d τ))
    (hi : i ≤ τ) {Ch : ℝ} {p : Vec d} {c : ℝ}
    (h1 : cubeL2 i (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (τ - i) ≤
      Ch * (3 : ℝ) ^ τ * cubeFlat τ w) :
    cubeFlat i (fun y => w y - vecDot p y) ≤ (Ch * cubeFlat τ w) * ((3 : ℝ)⁻¹) ^ (τ - i) := by
  have hm : MemLp (fun y => w y - vecDot p y) 2 (eb4_mu d i) :=
    (eb4_memLp_le hi hw).sub (e0c_memLp i (e0c_continuous_vecDot p))
  have h2 := cubeFlat_le_of_sub_const hm c
  have e : (fun x => (w x - vecDot p x) - c) = fun x => w x - c - vecDot p x := by
    funext x
    ring
  rw [e] at h2
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hs : i + s - i = s := by omega
  rw [hs] at h1 ⊢
  have h3 : (9 : ℝ) ^ s = (3 : ℝ) ^ s * (3 : ℝ) ^ s := by
    rw [← mul_pow]
    norm_num
  have h4 := e0c_inv_mul i
  have h5 := e0c_inv_mul s
  have hp9 : (0 : ℝ) < (9 : ℝ) ^ s := by positivity
  have hX := cubeL2_nonneg i (fun x => w x - c - vecDot p x)
  have hi3 : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ i := by positivity
  have h6 : cubeFlat i (fun y => w y - vecDot p y) * (9 : ℝ) ^ s ≤
      (Ch * cubeFlat (i + s) w) * ((3 : ℝ)⁻¹) ^ s * (9 : ℝ) ^ s := by
    have h7 : cubeFlat i (fun y => w y - vecDot p y) * (9 : ℝ) ^ s ≤
        ((3 : ℝ)⁻¹) ^ i * cubeL2 i (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right h2 hp9.le
    have h8 : ((3 : ℝ)⁻¹) ^ i * (cubeL2 i (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ s) ≤
        ((3 : ℝ)⁻¹) ^ i * (Ch * (3 : ℝ) ^ (i + s) * cubeFlat (i + s) w) :=
      mul_le_mul_of_nonneg_left h1 hi3
    have h9 : ((3 : ℝ)⁻¹) ^ i * (Ch * (3 : ℝ) ^ (i + s) * cubeFlat (i + s) w) =
        (Ch * cubeFlat (i + s) w) * (3 : ℝ) ^ s := by
      rw [pow_add]
      calc ((3 : ℝ)⁻¹) ^ i * (Ch * ((3 : ℝ) ^ i * (3 : ℝ) ^ s) * cubeFlat (i + s) w)
          = (((3 : ℝ) ^ i * ((3 : ℝ)⁻¹) ^ i)) * ((Ch * cubeFlat (i + s) w) * (3 : ℝ) ^ s) := by
            ring
        _ = _ := by rw [h4, one_mul]
    have h10 : (Ch * cubeFlat (i + s) w) * ((3 : ℝ)⁻¹) ^ s * (9 : ℝ) ^ s =
        (Ch * cubeFlat (i + s) w) * (3 : ℝ) ^ s := by
      rw [h3]
      calc (Ch * cubeFlat (i + s) w) * ((3 : ℝ)⁻¹) ^ s * ((3 : ℝ) ^ s * (3 : ℝ) ^ s)
          = (Ch * cubeFlat (i + s) w) * (((3 : ℝ) ^ s * ((3 : ℝ)⁻¹) ^ s)) * (3 : ℝ) ^ s := by
            ring
        _ = _ := by rw [h5]; ring
    rw [h10]
    nlinarith only [h7, h8, h9]
  exact le_of_mul_le_mul_right h6 hp9

/-- The constant `ρ³ + 27 Cin` bounding the oscillation of the harmonic part. -/
noncomputable def eb4_Wc (d : ℕ) (Cin : ℝ) : ℝ := eb4_rho d ^ 3 + 27 * Cin

/-- The constant of the harmonic part of the step. -/
noncomputable def eb4_C7 (d : ℕ) (Cin Ch : ℝ) : ℝ :=
  27 * (eb4_rho d ^ 3 + Ch * eb4_Wc d Cin) +
    27 * (2 * eb4_rho d + 3) * Ch * eb4_Wc d Cin

/-- The harmonic part of the basic step: one affine function serves every target scale. -/
theorem eb4_harm [NeZero d] {Cin Ch : ℝ} (hCin : 1 ≤ Cin) (hCh : 1 ≤ Ch)
    {a : CoeffField d} {δ : ℕ → ℝ} {Hb mstar : ℕ}
    (hF4 : ∀ (k l : ℕ), l + 1 ≤ k →
      ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
        IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
        ∃ (p : Vec d) (c : ℝ),
          cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤
              Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
            engNorm p ≤ Ch * cubeFlat k w)
    (hHA : ∀ j t : ℕ, mstar ≤ j → t ≤ j → j + 2 ≤ t + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
        ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
            cubeL2 (t - 3) (fun x => u x - w x) ≤
              Cin * δ j * (3 : ℝ) ^ t * cubeFlat t u)
    {j t l : ℕ} (hj : mstar ≤ j) (htj : t ≤ j) (hHb : j + 2 ≤ t + Hb) (hlt : l + 4 ≤ t)
    (hδ0 : 0 ≤ δ j) (hδ1 : δ j ≤ 1)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : IsSolOn a (engCube d t) u g) :
    ∃ p : Vec d, engNorm p ≤ Ch * eb4_Wc d Cin * cubeFlat t u ∧
      ∀ k : ℕ, l ≤ k → k ≤ t →
        cubeFlat k (fun y => u y - vecDot p y) ≤
          (eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ (t - k) +
            27 * Cin * eb4_rho d ^ (t - l) * δ j) * cubeFlat t u := by
  obtain ⟨w, gw, hw, hr⟩ := hHA j t hj htj hHb u g hu
  have hρ := eb4_rho_one_le d
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCh0 : 0 ≤ Ch := by linarith only [hCh]
  have hA0 := cubeFlat_nonneg t u
  set A := cubeFlat t u with hAdef
  set τ := t - 3 with hτ
  have htτ : t = τ + 3 := by omega
  have hmu : MemLp u 2 (eb4_mu d τ) := eb4_sol_memLp (by omega) hu
  have hmw : MemLp w 2 (eb4_mu d τ) := eb4_sol_memLp le_rfl hw
  have hmr : MemLp (fun x => u x - w x) 2 (eb4_mu d τ) := hmu.sub hmw
  -- flatness of the remainder at the scale `τ`
  have hr1 : cubeFlat τ (fun x => u x - w x) ≤ 27 * Cin * δ j * A := by
    have h1 := cubeFlat_le_of_sub_const hmr 0
    simp only [sub_zero] at h1
    have h2 : ((3 : ℝ)⁻¹) ^ τ * cubeL2 τ (fun x => u x - w x) ≤
        ((3 : ℝ)⁻¹) ^ τ * (Cin * δ j * (3 : ℝ) ^ t * A) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    have h3 : ((3 : ℝ)⁻¹) ^ τ * (Cin * δ j * (3 : ℝ) ^ t * A) = 27 * Cin * δ j * A := by
      rw [htτ, pow_add]
      have := e0c_inv_mul τ
      calc ((3 : ℝ)⁻¹) ^ τ * (Cin * δ j * ((3 : ℝ) ^ τ * (3 : ℝ) ^ 3) * A)
          = ((3 : ℝ) ^ τ * ((3 : ℝ)⁻¹) ^ τ) * (27 * Cin * δ j * A) := by ring
        _ = _ := by rw [this, one_mul]
    linarith only [h1, h2, h3]
  -- flatness of `w` at the scale `τ`
  have hW : cubeFlat τ w ≤ eb4_Wc d Cin * A := by
    have e : w = fun x => u x - (u x - w x) := by
      funext x
      ring
    have h1 := eb4_flat_sub_le hmu hmr
    rw [← e] at h1
    have h2 := eb4_flat_mono (show τ ≤ t by omega) (hu.memLp.1)
    have h3 : t - τ = 3 := by omega
    rw [h3] at h2
    unfold eb4_Wc
    have h4 : δ j * A ≤ A := by nlinarith only [hδ1, hA0]
    nlinarith only [h1, h2, hr1, h4, hCin0, hA0]
  -- the harmonic approximations at all target scales
  have key : ∀ i : ℕ, i + 1 ≤ τ → ∃ (p : Vec d) (c : ℝ),
      cubeL2 i (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (τ - i) ≤
          Ch * (3 : ℝ) ^ τ * cubeFlat τ w ∧ engNorm p ≤ Ch * cubeFlat τ w :=
    fun i hi => hF4 τ i hi w gw hw
  choose! P C hPC using key
  have hB0 : 0 ≤ Ch * cubeFlat τ w := mul_nonneg hCh0 (cubeFlat_nonneg _ _)
  have hlτ : l + 1 ≤ τ := by omega
  have htel := eb4_telescope (l := l) hmw P hB0 (fun i hli hi1 =>
    eb4_hF4_flat hmw (by omega) (hPC i hi1).1)
  refine ⟨P l, ?_, ?_⟩
  · have h1 := (hPC l hlτ).2
    have h2 : Ch * cubeFlat τ w ≤ Ch * (eb4_Wc d Cin * A) := mul_le_mul_of_nonneg_left hW hCh0
    linarith only [h1, h2, mul_assoc Ch (eb4_Wc d Cin) A]
  · intro k hlk hkt
    have hmuk : MemLp u 2 (eb4_mu d k) := eb4_sol_memLp hkt hu
    have hq3 : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ (t - k) := by positivity
    have hC7a : 0 ≤ Ch * eb4_Wc d Cin := mul_nonneg hCh0 (by unfold eb4_Wc; positivity)
    have hρ0 : 0 ≤ eb4_rho d := by linarith only [hρ]
    by_cases hk4 : k + 4 ≤ t
    · have hkτ : k + 1 ≤ τ := by omega
      have hmp : MemLp (fun y => w y - vecDot (P l) y) 2 (eb4_mu d k) :=
        (eb4_memLp_le (by omega) hmw).sub (e0c_memLp k (e0c_continuous_vecDot _))
      have hmuw : MemLp (fun x => u x - w x) 2 (eb4_mu d k) := eb4_memLp_le (by omega) hmr
      have e : (fun y => u y - vecDot (P l) y) =
          fun y => (u y - w y) + (w y - vecDot (P l) y) := by
        funext y
        ring
      have h1 := cubeFlat_add_le hmuw hmp
      rw [← e] at h1
      have h2 := eb4_flat_mono (show k ≤ τ by omega) hmr
      have h3 : eb4_rho d ^ (τ - k) ≤ eb4_rho d ^ (t - l) :=
        pow_le_pow_right₀ hρ (by omega)
      have h4 : eb4_rho d ^ (τ - k) * cubeFlat τ (fun x => u x - w x) ≤
          eb4_rho d ^ (t - l) * (27 * Cin * δ j * A) :=
        mul_le_mul h3 hr1 (cubeFlat_nonneg _ _) (by positivity)
      have h5 := htel k hlk (by omega)
      have h6 : ((3 : ℝ)⁻¹) ^ (τ - k) = 27 * ((3 : ℝ)⁻¹) ^ (t - k) := by
        have := eb4_inv_pow_shift (τ - k)
        rw [this]
        congr 2
        omega
      rw [h6] at h5
      have h7 : Ch * cubeFlat τ w ≤ Ch * (eb4_Wc d Cin * A) := mul_le_mul_of_nonneg_left hW hCh0
      have h8 : (2 * eb4_rho d + 3) * ((Ch * cubeFlat τ w) * (27 * ((3 : ℝ)⁻¹) ^ (t - k))) ≤
          (2 * eb4_rho d + 3) * ((Ch * (eb4_Wc d Cin * A)) * (27 * ((3 : ℝ)⁻¹) ^ (t - k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7 (by positivity))
          (by linarith only [hρ0])
      have h9 : 0 ≤ 27 * (eb4_rho d ^ 3 + Ch * eb4_Wc d Cin) * ((3 : ℝ)⁻¹) ^ (t - k) * A := by
        have : 0 ≤ eb4_rho d ^ 3 := by positivity
        positivity
      unfold eb4_C7
      nlinarith only [h1, h2, h4, h5, h8, h9]
    · have hk3 : t - k ≤ 3 := by omega
      have hl1 := e0c_memLp k (e0c_continuous_vecDot (P l))
      have h1 := eb4_flat_sub_le hmuk hl1
      rw [cubeFlat_vecDot] at h1
      have h2 := eb4_flat_mono hkt hu.memLp.1
      rw [← hAdef] at h2
      have h3 : eb4_rho d ^ (t - k) ≤ eb4_rho d ^ 3 := pow_le_pow_right₀ hρ hk3
      have h4 : eb4_rho d ^ (t - k) * A ≤ eb4_rho d ^ 3 * A :=
        mul_le_mul_of_nonneg_right h3 hA0
      have h5 : engNorm (P l) / (2 * Real.sqrt 3) ≤ engNorm (P l) := by
        have h3' : (3 : ℝ) ≤ 2 * Real.sqrt 3 := by linarith only [eb4_three_halves_le_sqrt]
        rw [div_le_iff₀ (by linarith only [h3'])]
        have := engNorm_nonneg (P l)
        nlinarith only [h3', this]
      have h6 := (hPC l hlτ).2
      have h7 : Ch * cubeFlat τ w ≤ Ch * (eb4_Wc d Cin * A) := mul_le_mul_of_nonneg_left hW hCh0
      have h8 : ((3 : ℝ)⁻¹) ^ 3 ≤ ((3 : ℝ)⁻¹) ^ (t - k) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk3
      have h9 : 1 ≤ 27 * ((3 : ℝ)⁻¹) ^ (t - k) := by
        have : (27 : ℝ) * ((3 : ℝ)⁻¹) ^ 3 = 1 := by norm_num
        nlinarith only [h8, this]
      have hb : 0 ≤ eb4_rho d ^ 3 * A + Ch * (eb4_Wc d Cin * A) := by
        have : 0 ≤ eb4_Wc d Cin := by unfold eb4_Wc; positivity
        positivity
      have h10 : eb4_rho d ^ 3 * A + Ch * (eb4_Wc d Cin * A) ≤
          27 * ((3 : ℝ)⁻¹) ^ (t - k) * (eb4_rho d ^ 3 * A + Ch * (eb4_Wc d Cin * A)) := by
        nlinarith only [h9, hb]
      have h11 : 0 ≤ 27 * (2 * eb4_rho d + 3) * Ch * eb4_Wc d Cin * ((3 : ℝ)⁻¹) ^ (t - k) * A := by
        have : 0 ≤ eb4_Wc d Cin := by unfold eb4_Wc; positivity
        positivity
      have h12 : 0 ≤ 27 * Cin * eb4_rho d ^ (t - l) * δ j * A := by positivity
      have hid : (eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ (t - k) +
            27 * Cin * eb4_rho d ^ (t - l) * δ j) * A =
          27 * ((3 : ℝ)⁻¹) ^ (t - k) * (eb4_rho d ^ 3 * A + Ch * (eb4_Wc d Cin * A)) +
          27 * (2 * eb4_rho d + 3) * Ch * eb4_Wc d Cin * ((3 : ℝ)⁻¹) ^ (t - k) * A +
          27 * Cin * eb4_rho d ^ (t - l) * δ j * A := by
        unfold eb4_C7
        ring
      linarith only [h1, h2, h4, h5, h6, h7, h10, h11, h12, hid]

theorem eb4_cube_mono {m n : ℕ} (h : m ≤ n) : engCube d m ⊆ engCube d n := by
  intro y hy
  have hy' := mem_openCubeSet_originCube_iff.1 hy
  show y ∈ openCubeSet (originCube d (n : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := hy' i
  have hle : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) h
  constructor <;> linarith only [hi.1, hi.2, hle]

theorem eb4_sol_restrict {a : CoeffField d} {t j : ℕ} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d t) a) (htj : t ≤ j)
    (hu : IsSolOn a (engCube d j) u g) : IsSolOn a (engCube d t) u g :=
  IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _) (eb4_cube_mono htj)
    (volume_openCubeSet_lt_top _).ne hell hu

/-- The basic step: from the scale `t` down to every scale in `[l, t]`, with one correction
`V_j x`. -/
theorem eb4_step [NeZero d] {Cin Ch K : ℝ} (hCin : 1 ≤ Cin) (hCh : 1 ≤ Ch) (hK : 1 ≤ K)
    {a : CoeffField d} {δ : ℕ → ℝ} {Hb mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hF4 : ∀ (k l : ℕ), l + 1 ≤ k →
      ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
        IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
        ∃ (p : Vec d) (c : ℝ),
          cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤
              Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
            engNorm p ≤ Ch * cubeFlat k w)
    (hHA : ∀ j t : ℕ, mstar ≤ j → t ≤ j → j + 2 ≤ t + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
        ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
            cubeL2 (t - 3) (fun x => u x - w x) ≤
              Cin * δ j * (3 : ℝ) ^ t * cubeFlat t u)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤
          K * δ j * engNorm e ∧
        engNorm (affSlope k (V j e) - e) ≤
          K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e)
    {j t l : ℕ} (hj : mstar ≤ j) (htj : t ≤ j) (hlt : l ≤ t) (hjl : j ≤ l + Hb)
    (hδ0 : 0 ≤ δ j) (hδ1 : δ j ≤ 1) (hKδ : K * δ j * ((Hb : ℝ) + 1) ≤ 1 / 2)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : IsSolOn a (engCube d j) u g) :
    ∃ x : Vec d, engNorm x ≤ 2 * (Ch * eb4_Wc d Cin) * cubeFlat t u ∧
      ∀ k : ℕ, l ≤ k → k ≤ t →
        cubeFlat k (fun y => u y - V j x y) ≤
          (eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ (t - k) +
            (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin)) * eb4_rho d ^ (t - l) * δ j) *
            cubeFlat t u := by
  have hρ := eb4_rho_one_le d
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCh0 : 0 ≤ Ch := by linarith only [hCh]
  have hWc : 0 ≤ eb4_Wc d Cin := by unfold eb4_Wc; positivity
  have hA0 := cubeFlat_nonneg t u
  have hut : IsSolOn a (engCube d t) u g := eb4_sol_restrict (hell t) htj hu
  by_cases hl4 : l + 4 ≤ t
  · obtain ⟨p, hpn, hpf⟩ := eb4_harm hCin hCh hF4 hHA hj htj (by omega) hl4 hδ0 hδ1 hut
    have hq0 : 0 ≤ K * δ j := mul_nonneg (by linarith only [hK]) hδ0
    have hfl : ∀ k : ℕ, k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
        cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤ K * δ j * engNorm e ∧
          engNorm (affSlope k (V j e) - e) ≤ K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e :=
      fun k hk hjk e => hflat j k hj hk hjk e
    obtain ⟨P, hP⟩ := eb4_slope_linear (a := a) (show l ≤ j by omega) (V j) (hVsol j hj)
    have hPc : ∀ x : Vec d, engNorm (P x - x) ≤ 1 / 2 * engNorm x := by
      intro x
      rw [hP]
      exact (eb4_V_flat hq0 hKδ (hVsol j hj) hfl (show l ≤ j by omega) hjl x).1
    obtain ⟨⟨_, hsurj⟩, hlow⟩ := engNorm_bijective_of_close P hPc
    obtain ⟨x, hx⟩ := hsurj p
    have hxn : engNorm x ≤ 2 * (Ch * eb4_Wc d Cin * cubeFlat t u) := by
      have := hlow x
      rw [hx] at this
      linarith only [this, hpn]
    refine ⟨x, by linarith only [hxn, mul_assoc 2 (Ch * eb4_Wc d Cin) (cubeFlat t u)], ?_⟩
    intro k hlk hkt
    have hmuk : MemLp u 2 (eb4_mu d k) := eb4_sol_memLp (by omega) hu
    have hmvk : MemLp (V j x) 2 (eb4_mu d k) := eb4_sol_memLp (by omega) (hVsol j hj x).choose_spec
    have hmp := e0c_memLp k (e0c_continuous_vecDot p)
    have hm1 : MemLp (fun y => u y - vecDot p y) 2 (eb4_mu d k) := hmuk.sub hmp
    have hm2 : MemLp (fun y => vecDot p y - V j x y) 2 (eb4_mu d k) := hmp.sub hmvk
    have e : (fun y => u y - V j x y) =
        fun y => (u y - vecDot p y) + (vecDot p y - V j x y) := by
      funext y
      ring
    have h1 := cubeFlat_add_le hm1 hm2
    rw [← e] at h1
    have h2 := eb4_flat_sub_comm k (fun y => vecDot p y) (fun y => V j x y)
    have h3 := eb4_V_drift (Hb := Hb) (hVsol j hj) hfl (show l ≤ k by omega)
      (show k ≤ j by omega) hjl x
    rw [← hP x, hx] at h3
    have h4 := hpf k hlk hkt
    have h5 : (2 + eb4_rho d ^ (k - l)) ≤ 3 * eb4_rho d ^ (t - l) := by
      have : eb4_rho d ^ (k - l) ≤ eb4_rho d ^ (t - l) := pow_le_pow_right₀ hρ (by omega)
      have h1' : 1 ≤ eb4_rho d ^ (t - l) := one_le_pow₀ hρ
      linarith only [this, h1']
    have h6 : K * δ j * engNorm x ≤ K * δ j * (2 * (Ch * eb4_Wc d Cin * cubeFlat t u)) :=
      mul_le_mul_of_nonneg_left hxn hq0
    have h7 : (2 + eb4_rho d ^ (k - l)) * (K * δ j * engNorm x) ≤
        (3 * eb4_rho d ^ (t - l)) * (K * δ j * (2 * (Ch * eb4_Wc d Cin * cubeFlat t u))) :=
      mul_le_mul h5 h6 (mul_nonneg hq0 (engNorm_nonneg x)) (by positivity)
    have hid : (eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ (t - k) +
            (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin)) * eb4_rho d ^ (t - l) * δ j) *
            cubeFlat t u =
        (eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ (t - k) +
            27 * Cin * eb4_rho d ^ (t - l) * δ j) * cubeFlat t u +
        (3 * eb4_rho d ^ (t - l)) * (K * δ j * (2 * (Ch * eb4_Wc d Cin * cubeFlat t u))) := by
      ring
    linarith only [h1, h2, h3, h4, h7, hid]
  · have hk3 : t - l ≤ 3 := by omega
    refine ⟨0, ?_, ?_⟩
    · have h0 : engNorm (0 : Vec d) = 0 := by simp [engNorm, vecNormSq, vecDot]
      rw [h0]
      have : 0 ≤ Ch * eb4_Wc d Cin := mul_nonneg hCh0 hWc
      positivity
    · intro k hlk hkt
      have hmuk : MemLp u 2 (eb4_mu d k) := eb4_sol_memLp (by omega) hu
      have e : (fun y => u y - V j 0 y) = u := by
        funext y
        simp
      rw [e]
      have h2 := eb4_flat_mono hkt hut.memLp.1
      have h3 : eb4_rho d ^ (t - k) ≤ eb4_rho d ^ 3 := pow_le_pow_right₀ hρ (by omega)
      have h4 : eb4_rho d ^ (t - k) * cubeFlat t u ≤ eb4_rho d ^ 3 * cubeFlat t u :=
        mul_le_mul_of_nonneg_right h3 hA0
      have h8 : ((3 : ℝ)⁻¹) ^ 3 ≤ ((3 : ℝ)⁻¹) ^ (t - k) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h9 : 1 ≤ 27 * ((3 : ℝ)⁻¹) ^ (t - k) := by
        have : (27 : ℝ) * ((3 : ℝ)⁻¹) ^ 3 = 1 := by norm_num
        nlinarith only [h8, this]
      have hb : 0 ≤ eb4_rho d ^ 3 * cubeFlat t u := by positivity
      have h10 : eb4_rho d ^ 3 * cubeFlat t u ≤
          27 * ((3 : ℝ)⁻¹) ^ (t - k) * (eb4_rho d ^ 3 * cubeFlat t u) := by
        nlinarith only [h9, hb]
      have hCW : 0 ≤ Ch * eb4_Wc d Cin := mul_nonneg hCh0 hWc
      have h11 : 0 ≤ 27 * (Ch * eb4_Wc d Cin) * ((3 : ℝ)⁻¹) ^ (t - k) * cubeFlat t u := by
        positivity
      have h12 : 0 ≤ 27 * (2 * eb4_rho d + 3) * Ch * eb4_Wc d Cin *
          ((3 : ℝ)⁻¹) ^ (t - k) * cubeFlat t u := by positivity
      have h13 : 0 ≤ (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin)) * eb4_rho d ^ (t - l) * δ j *
          cubeFlat t u := by
        have : 0 ≤ 6 * K * (Ch * eb4_Wc d Cin) := by
          have : 0 ≤ K := by linarith only [hK]
          positivity
        positivity
      have hid : (eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ (t - k) +
            (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin)) * eb4_rho d ^ (t - l) * δ j) *
            cubeFlat t u =
          27 * ((3 : ℝ)⁻¹) ^ (t - k) * (eb4_rho d ^ 3 * cubeFlat t u) +
          27 * (Ch * eb4_Wc d Cin) * ((3 : ℝ)⁻¹) ^ (t - k) * cubeFlat t u +
          27 * (2 * eb4_rho d + 3) * Ch * eb4_Wc d Cin * ((3 : ℝ)⁻¹) ^ (t - k) * cubeFlat t u +
          (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin)) * eb4_rho d ^ (t - l) * δ j *
            cubeFlat t u := by
        unfold eb4_C7
        ring
      linarith only [h2, h4, h10, h11, h12, h13, hid]

/-- The iteration, `ĥ` scales at a time. -/
theorem eb4_iter [NeZero d] {a : CoeffField d} {Hb j : ℕ} {V : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {δj Cx C4 C6 M η : ℝ} {hh : ℕ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hhh : 1 ≤ hh) (hC4 : 0 ≤ C4) (hCx : 0 ≤ Cx)
    (hM1 : 2 * (C4 + 1) ≤ M) (hM2 : 2 * Cx ≤ M)
    (hgain : C4 * ((3 : ℝ)⁻¹) ^ hh ≤ 1 / 4 * eb4_R η hh)
    (hsmall : C6 * eb4_rho d ^ hh * δj ≤ 1 / 4 * ((3 : ℝ)⁻¹) ^ hh)
    (hC6 : 0 ≤ C6) (hδ0 : 0 ≤ δj)
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d j) a)
    (hVsol : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V e) g)
    (hVflat : ∀ k : ℕ, k ≤ j → j ≤ k + Hb → ∀ e : Vec d, cubeFlat k (V e) ≤ engNorm e)
    (hstep : ∀ t l : ℕ, l ≤ t → t ≤ j → j ≤ l + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d j) u g →
        ∃ x : Vec d, engNorm x ≤ Cx * cubeFlat t u ∧
          ∀ k : ℕ, l ≤ k → k ≤ t →
            cubeFlat k (fun y => u y - V x y) ≤
              (C4 * ((3 : ℝ)⁻¹) ^ (t - k) + C6 * eb4_rho d ^ (t - l) * δj) * cubeFlat t u) :
    ∀ n t l : ℕ, t - l = n → l ≤ t → t ≤ j → j ≤ l + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d j) u g →
        ∃ e : Vec d, engNorm e ≤ M * cubeFlat t u ∧
          ∀ k : ℕ, l ≤ k → k ≤ t →
            cubeFlat k (fun y => u y - V e y) ≤ M * eb4_R η (t - k) * cubeFlat t u := by
  have hρ := eb4_rho_one_le d
  have hM0 : 0 ≤ M := by linarith only [hM1, hC4]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t l hn hlt htj hjl u g hu
    have hA0 := cubeFlat_nonneg t u
    obtain ⟨x, hxn, hxk⟩ := hstep t l hlt htj hjl u g hu
    -- the bound of one step, at every scale of the step
    have hsm : ∀ s : ℕ, s ≤ hh → ∀ m : ℕ, m ≤ hh →
        C6 * eb4_rho d ^ m * δj ≤ 1 / 4 * eb4_R η s := by
      intro s hs m hm
      have h1 : eb4_rho d ^ m ≤ eb4_rho d ^ hh := pow_le_pow_right₀ hρ hm
      have h2 : C6 * eb4_rho d ^ m * δj ≤ C6 * eb4_rho d ^ hh * δj :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC6) hδ0
      have h3 := eb4_inv_pow_le_R hη1 hh
      have h4 := eb4_R_anti hη0 hs
      linarith only [h2, hsmall, h3, h4]
    by_cases hn' : n < hh
    · refine ⟨x, ?_, ?_⟩
      · have : Cx * cubeFlat t u ≤ M * cubeFlat t u :=
          mul_le_mul_of_nonneg_right (by linarith only [hM2, hCx]) hA0
        linarith only [hxn, this]
      · intro k hlk hkt
        refine (hxk k hlk hkt).trans ?_
        have h1 := eb4_inv_pow_le_R hη1 (t - k)
        have h2 : C4 * ((3 : ℝ)⁻¹) ^ (t - k) ≤ C4 * eb4_R η (t - k) :=
          mul_le_mul_of_nonneg_left h1 hC4
        have h3 := hsm (t - k) (by omega) (t - l) (by omega)
        have h4 := eb4_R_pos η (t - k)
        have h5 : (C4 * ((3 : ℝ)⁻¹) ^ (t - k) + C6 * eb4_rho d ^ (t - l) * δj) ≤
            M * eb4_R η (t - k) := by
          have h6 := mul_le_mul_of_nonneg_right hM1 h4.le
          have h7 := mul_nonneg hC4 h4.le
          nlinarith only [h2, h3, h6, h7, h4]
        exact mul_le_mul_of_nonneg_right h5 hA0
    · have hhn : hh ≤ n := by omega
      obtain ⟨x, hxn, hxk⟩ := hstep t (t - hh) (by omega) htj (by omega) u g hu
      have hu' : IsSolOn a (engCube d j) (fun y => u y - V x y) _ :=
        IsSolOn.sub hell hu (hVsol x).choose_spec
      obtain ⟨e', hen, hek⟩ := ih (t - hh - l) (by omega) (t - hh) l (by omega) (by omega)
        (by omega) hjl (fun y => u y - V x y) _ hu'
      have hRh := eb4_R_le_one hη0 hh
      have hRp := eb4_R_pos η hh
      have hgain' : cubeFlat (t - hh) (fun y => u y - V x y) ≤
          1 / 2 * eb4_R η hh * cubeFlat t u := by
        refine (hxk (t - hh) le_rfl (Nat.sub_le _ _)).trans ?_
        have e1 : t - (t - hh) = hh := by omega
        rw [e1]
        have h3 := hsm hh le_rfl hh le_rfl
        have : (C4 * ((3 : ℝ)⁻¹) ^ hh + C6 * eb4_rho d ^ hh * δj) ≤ 1 / 2 * eb4_R η hh := by
          linarith only [hgain, h3]
        exact mul_le_mul_of_nonneg_right this hA0
      refine ⟨x + e', ?_, ?_⟩
      · have h1 : engNorm e' ≤ M * (1 / 2 * eb4_R η hh * cubeFlat t u) :=
          hen.trans (mul_le_mul_of_nonneg_left hgain' hM0)
        have h2 := engNorm_add_le x e'
        have h3 : Cx * cubeFlat t u ≤ 1 / 2 * M * cubeFlat t u :=
          mul_le_mul_of_nonneg_right (by linarith only [hM2]) hA0
        have h4 : M * (1 / 2 * eb4_R η hh * cubeFlat t u) ≤ 1 / 2 * M * cubeFlat t u := by
          have : M * (1 / 2 * eb4_R η hh * cubeFlat t u) =
              1 / 2 * M * (eb4_R η hh * cubeFlat t u) := by ring
          rw [this]
          have h5 : eb4_R η hh * cubeFlat t u ≤ cubeFlat t u := by nlinarith only [hRh, hA0]
          nlinarith only [h5, hM0]
        nlinarith only [h1, h2, h3, h4, hxn]
      · intro k hlk hkt
        have hmu : MemLp (fun y => u y - V x y) 2 (eb4_mu d k) :=
          eb4_sol_memLp (by omega) hu'
        have hmV : MemLp (V e') 2 (eb4_mu d k) := eb4_sol_memLp (by omega) (hVsol e').choose_spec
        have e : (fun y => u y - V (x + e') y) =
            fun y => (u y - V x y) - V e' y := by
          funext y
          rw [map_add]
          simp only [Pi.add_apply]
          ring
        rw [e]
        by_cases hk : k ≤ t - hh
        · have h1 := hek k hlk hk
          have e3 : t - k = hh + (t - hh - k) := by omega
          rw [e3, eb4_R_add]
          have h2 : cubeFlat (t - hh) (fun y => u y - V x y) ≤
              1 / 2 * eb4_R η hh * cubeFlat t u := hgain'
          have h3 : M * eb4_R η (t - hh - k) * cubeFlat (t - hh) (fun y => u y - V x y) ≤
              M * eb4_R η (t - hh - k) * (1 / 2 * eb4_R η hh * cubeFlat t u) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hM0 (eb4_R_pos η _).le)
          have h4 := eb4_R_pos η (t - hh - k)
          have h5 : 0 ≤ M * (eb4_R η hh * eb4_R η (t - hh - k)) * cubeFlat t u :=
            mul_nonneg (mul_nonneg hM0 (mul_pos hRp h4).le) hA0
          nlinarith only [h1, h3, h5]
        · have hk' : t - hh ≤ k := by omega
          have h1 := eb4_flat_sub_le hmu hmV
          have h2 := hxk k (by omega) hkt
          have h3 := hVflat k (by omega) (by omega) e'
          have h4 : C4 * ((3 : ℝ)⁻¹) ^ (t - k) + C6 * eb4_rho d ^ (t - (t - hh)) * δj ≤
              (C4 + 1 / 4) * eb4_R η (t - k) := by
            have h5 := eb4_inv_pow_le_R hη1 (t - k)
            have h6 : C4 * ((3 : ℝ)⁻¹) ^ (t - k) ≤ C4 * eb4_R η (t - k) :=
              mul_le_mul_of_nonneg_left h5 hC4
            have h7 := hsm (t - k) (by omega) (t - (t - hh)) (by omega)
            linarith only [h6, h7]
          have h8 : (C4 * ((3 : ℝ)⁻¹) ^ (t - k) + C6 * eb4_rho d ^ (t - (t - hh)) * δj) *
              cubeFlat t u ≤ (C4 + 1 / 4) * eb4_R η (t - k) * cubeFlat t u :=
            mul_le_mul_of_nonneg_right h4 hA0
          have h9 : engNorm e' ≤ M * (1 / 2 * eb4_R η hh * cubeFlat t u) :=
            hen.trans (mul_le_mul_of_nonneg_left hgain' hM0)
          have h10 := eb4_R_anti hη0 (show t - k ≤ hh by omega)
          have h11 : 0 ≤ M * (cubeFlat t u) := mul_nonneg hM0 hA0
          have h12 : eb4_R η (t - k) * cubeFlat t u ≥ 0 :=
            mul_nonneg (eb4_R_pos η _).le hA0
          have h13 : M * (1 / 2 * eb4_R η hh * cubeFlat t u) ≤
              M * (1 / 2 * eb4_R η (t - k) * cubeFlat t u) := by
            refine mul_le_mul_of_nonneg_left ?_ hM0
            exact mul_le_mul_of_nonneg_right (by linarith only [h10]) hA0
          nlinarith only [h1, h2, h3, h8, h9, h12, h13, hM1, hA0]

/-- **E-B4 (one-block decay, simultaneous form)**, Step 4. The constant `C5` precedes
`η`; only the step `hhat` and the smallness threshold `c1` depend on `η`. -/
theorem eng_block_decay (d : ℕ) [NeZero d] (Cin Ch K : ℝ) (hCin : 1 ≤ Cin) (hCh : 1 ≤ Ch)
    (hK : 1 ≤ K) :
    ∃ C5 : ℝ, 1 ≤ C5 ∧
      ∀ η : ℝ, 1 / 2 ≤ η → η < 1 →
        ∃ (hhat : ℕ) (c1 : ℝ), 0 < c1 ∧
          ∀ (a : CoeffField d) (δ : ℕ → ℝ) (Hb mstar : ℕ)
            (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
            hhat ≤ Hb → Hb + 3 ≤ mstar →
            (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c1 ∧ K * δ j * ((Hb : ℝ) + 1) ≤ 1 / 2) →
            -- hell
            (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
            -- hF4
            (∀ (k l : ℕ), l + 1 ≤ k →
              ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
                IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
                ∃ (p : Vec d) (c : ℝ),
                  cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤
                      Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
                    engNorm p ≤ Ch * cubeFlat k w) →
            -- hHA
            (∀ j t : ℕ, mstar ≤ j → t ≤ j → j + 2 ≤ t + Hb →
              ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
                ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
                  IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
                    cubeL2 (t - 3) (fun x => u x - w x) ≤
                      Cin * δ j * (3 : ℝ) ^ t * cubeFlat t u) →
            -- hVsol
            (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
              ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
            -- hflat K
            (∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
              cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤
                  K * δ j * engNorm e ∧
                engNorm (affSlope k (V j e) - e) ≤
                  K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e) →
            -- conclusion: hblock C5 η
            ∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
              ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
                ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
                  ∀ k : ℕ, l ≤ k → k ≤ j →
                    cubeFlat k (fun x => w x - V j e x) ≤
                      C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w := by
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCh0 : 0 ≤ Ch := by linarith only [hCh]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hρ := eb4_rho_one_le d
  have hWc : 0 ≤ eb4_Wc d Cin := by unfold eb4_Wc; positivity
  have hCW : 0 ≤ Ch * eb4_Wc d Cin := mul_nonneg hCh0 hWc
  have hC7 : 0 ≤ eb4_C7 d Cin Ch := by
    unfold eb4_C7
    have : 0 ≤ eb4_rho d ^ 3 := by positivity
    positivity
  have hC6 : 0 ≤ 27 * Cin + 6 * K * (Ch * eb4_Wc d Cin) := by positivity
  have hCx : 0 ≤ 2 * (Ch * eb4_Wc d Cin) := by positivity
  refine ⟨2 * (eb4_C7 d Cin Ch + 1) + 2 * (2 * (Ch * eb4_Wc d Cin)) + 1, by
    linarith only [hC7, hCx], ?_⟩
  intro η hη1 hη2
  have hη0 : 0 ≤ η := by linarith only [hη1]
  have hη1' : η ≤ 1 := hη2.le
  -- the step length
  have hlim : Filter.Tendsto (fun n : ℕ => (3 : ℝ) ^ ((1 - η) * (n : ℝ))) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 3 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith only [hη2]))
  obtain ⟨hh, hh2, hh1⟩ := ((hlim.eventually_ge_atTop (4 * eb4_C7 d Cin Ch)).and
    (Filter.eventually_ge_atTop 1)).exists
  have hgain : eb4_C7 d Cin Ch * ((3 : ℝ)⁻¹) ^ hh ≤ 1 / 4 * eb4_R η hh := by
    have h1 : (3 : ℝ) ^ ((1 - η) * (hh : ℝ)) * ((3 : ℝ)⁻¹) ^ hh = eb4_R η hh := by
      unfold eb4_R
      have : ((3 : ℝ)⁻¹) ^ hh = (3 : ℝ) ^ (-((hh : ℝ))) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
      rw [this, ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have h2 : 0 ≤ ((3 : ℝ)⁻¹) ^ hh := by positivity
    have := mul_le_mul_of_nonneg_right hh2 h2
    rw [h1] at this
    linarith only [this]
  refine ⟨hh, min 1 (1 / 4 * ((3 : ℝ)⁻¹) ^ hh /
    ((27 * Cin + 6 * K * (Ch * eb4_Wc d Cin) + 1) * eb4_rho d ^ hh)), ?_, ?_⟩
  · refine lt_min one_pos ?_
    have : 0 < eb4_rho d ^ hh := pow_pos (eb4_rho_pos d) _
    positivity
  intro a δ Hb mstar V _ _ hδ hell hF4 hHA hVsol hflat j l hmj hlj hjl w hw
  obtain ⟨g, hg⟩ := hw
  obtain ⟨hδ0, hδc, hKδ⟩ := hδ j hmj
  have hδ1 : δ j ≤ 1 := hδc.trans (min_le_left _ _)
  have hq0 : 0 ≤ K * δ j := mul_nonneg hK0 hδ0
  have hfl : ∀ k : ℕ, k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤ K * δ j * engNorm e ∧
        engNorm (affSlope k (V j e) - e) ≤ K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e :=
    fun k hk hjk e => hflat j k hmj hk hjk e
  have hsmall : (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin)) * eb4_rho d ^ hh * δ j ≤
      1 / 4 * ((3 : ℝ)⁻¹) ^ hh := by
    have hpos : 0 < (27 * Cin + 6 * K * (Ch * eb4_Wc d Cin) + 1) * eb4_rho d ^ hh := by
      have : 0 < eb4_rho d ^ hh := pow_pos (eb4_rho_pos d) _
      positivity
    have h1 : δ j ≤ 1 / 4 * ((3 : ℝ)⁻¹) ^ hh /
        ((27 * Cin + 6 * K * (Ch * eb4_Wc d Cin) + 1) * eb4_rho d ^ hh) :=
      hδc.trans (min_le_right _ _)
    rw [le_div_iff₀ hpos] at h1
    have h2 : 0 ≤ eb4_rho d ^ hh := by positivity
    nlinarith only [h1, hδ0, h2, hC6]
  have hit := eb4_iter (a := a) (Hb := Hb) (j := j) (V := V j) (δj := δ j)
    (Cx := 2 * (Ch * eb4_Wc d Cin)) (C4 := eb4_C7 d Cin Ch)
    (C6 := 27 * Cin + 6 * K * (Ch * eb4_Wc d Cin))
    (M := 2 * (eb4_C7 d Cin Ch + 1) + 2 * (2 * (Ch * eb4_Wc d Cin)) + 1) (η := η) (hh := hh)
    hη0 hη1' hh1 hC7 hCx (by linarith only [hCx]) (by linarith only [hC7, hCx]) hgain hsmall hC6
    hδ0 (hell j) (hVsol j hmj)
    (fun k hk hjk e => (eb4_V_flat hq0 hKδ (hVsol j hmj) hfl hk hjk e).2)
    (fun t l' hlt htj hjl' u g' hu =>
      eb4_step hCin hCh hK hell hF4 hHA hVsol hflat hmj htj hlt hjl' hδ0 hδ1 hKδ hu)
  obtain ⟨e, hen, hek⟩ := hit (j - l) j l rfl hlj le_rfl hjl w g hg
  refine ⟨e, hen, fun k hlk hkj => ?_⟩
  have h := hek k hlk hkj
  have hc : eb4_R η (j - k) = (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) := by
    unfold eb4_R
    rw [Nat.cast_sub hkj]
  rw [hc] at h
  exact h

/-- Witness for the numerical hypotheses of `eng_block_decay`: for every step length, smallness
threshold and slope constant, the offsets `Hb ≥ ĥ`, `mstar ≥ Hb + 3` and the constant sequence
`δ = 0` satisfy them. -/
example (hhat : ℕ) (K c1 : ℝ) (hc : 0 < c1) :
    ∃ (Hb mstar : ℕ) (δ : ℕ → ℝ), hhat ≤ Hb ∧ Hb + 3 ≤ mstar ∧
      ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c1 ∧ K * δ j * ((Hb : ℝ) + 1) ≤ 1 / 2 :=
  ⟨hhat, hhat + 3, fun _ => 0, le_rfl, le_rfl, fun _ _ => by
    simp only [mul_zero, zero_mul, le_refl, true_and]
    exact ⟨hc.le, by norm_num⟩⟩

end SuperdiffusionCLT.Section6
