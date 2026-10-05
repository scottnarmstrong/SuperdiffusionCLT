/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.WindowFlat

/-!
# Window flatness: the one-step estimate
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb3_scale_gain (k N : ℕ) (Ch X L : ℝ)
    (h : L * (9 : ℝ) ^ N ≤ Ch * (3 : ℝ) ^ (k + N) * X) :
    ((3 : ℝ)⁻¹) ^ k * L ≤ Ch * ((3 : ℝ)⁻¹) ^ N * X := by
  have hrr := e0c_inv_mul N
  have hss := e0c_inv_mul k
  have h9 : (9 : ℝ) ^ N = (3 : ℝ) ^ N * (3 : ℝ) ^ N := by
    rw [← mul_pow]; norm_num
  rw [h9, pow_add] at h
  have hnn : 0 ≤ ((3 : ℝ)⁻¹) ^ k * ((3 : ℝ)⁻¹) ^ N * ((3 : ℝ)⁻¹) ^ N := by positivity
  have h2 := mul_le_mul_of_nonneg_left h hnn
  have eL : ((3 : ℝ)⁻¹) ^ k * ((3 : ℝ)⁻¹) ^ N * ((3 : ℝ)⁻¹) ^ N *
      (L * ((3 : ℝ) ^ N * (3 : ℝ) ^ N)) = ((3 : ℝ)⁻¹) ^ k * L := by
    linear_combination (((3 : ℝ)⁻¹) ^ k * L * ((3 : ℝ) ^ N * ((3 : ℝ)⁻¹) ^ N + 1)) * hrr
  have eR : ((3 : ℝ)⁻¹) ^ k * ((3 : ℝ)⁻¹) ^ N * ((3 : ℝ)⁻¹) ^ N *
      (Ch * ((3 : ℝ) ^ k * (3 : ℝ) ^ N) * X) = Ch * ((3 : ℝ)⁻¹) ^ N * X := by
    linear_combination (Ch * X * ((3 : ℝ)⁻¹) ^ N) *
      (((3 : ℝ) ^ N * ((3 : ℝ)⁻¹) ^ N) * hss + hrr)
  rw [eL, eR] at h2
  exact h2

theorem eb3_step [NeZero d] (Cin Ch δ : ℝ) (hCh : 0 ≤ Ch)
    (k N : ℕ) (hN : 1 ≤ N) (W : Vec d → ℝ) (p : Vec d)
    (hW : MemLp W 2 (normalizedCubeMeasure (originCube d ((k + N + 3 : ℕ) : ℤ))))
    (hF4 : ∀ (k l : ℕ), l + 1 ≤ k →
      ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
        IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
        ∃ (p : Vec d) (c : ℝ),
          cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤
              Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
            engNorm p ≤ Ch * cubeFlat k w)
    (hHA : ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
      IsSolOn (fun _ => (1 : Mat d)) (engCube d (k + N)) w gw ∧
        cubeL2 (k + N) (fun x => W x - w x) ≤
          Cin * δ * (3 : ℝ) ^ (k + N + 3) * cubeFlat (k + N + 3) W) :
    cubeFlat k (fun x => W x - vecDot (affSlope k W) x) ≤
      ((3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin + 27 * Cin * Ch * ((3 : ℝ)⁻¹) ^ N) * δ *
          cubeFlat (k + N + 3) W +
        Ch * ((3 : ℝ)⁻¹) ^ N * (3 : ℝ) ^ ((d + 2) * 3) *
          cubeFlat (k + N + 3) (fun x => W x - vecDot p x) := by
  obtain ⟨w, gw, hw, hcl⟩ := hHA
  have hwm := hw.memLp.1
  have hWM : MemLp W 2 (normalizedCubeMeasure (originCube d ((k + N : ℕ) : ℤ))) :=
    eb3_memLp_le (by omega) hW
  have hWk : MemLp W 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    eb3_memLp_le (by omega) hW
  have hlp := fun (n : ℕ) (q : Vec d) => e0c_memLp n (e0c_continuous_vecDot q)
  have hlin : IsSolOn (fun _ => (1 : Mat d)) (engCube d (k + N))
      (fun x => w x - vecDot p x) (fun x => gw x - p) := by
    have h := IsSolOn.sub (eb3_isElliptic_one (d := d) (k + N)) hw (isSolOn_one_affine (k + N) 0 p)
    simpa only [zero_add] using h
  obtain ⟨p', c, h1, -⟩ := hF4 (k + N) k (by omega) _ _ hlin
  have hNk : k + N - k = N := by omega
  rw [hNk] at h1
  set X := cubeFlat (k + N) (fun x => w x - vecDot p x) with hXdef
  set E := cubeFlat (k + N + 3) (fun x => W x - vecDot p x) with hEdef
  set F := cubeFlat (k + N + 3) W with hFdef
  have hX0 : 0 ≤ X := cubeFlat_nonneg _ _
  have hF0 : 0 ≤ F := cubeFlat_nonneg _ _
  have hE0 : 0 ≤ E := cubeFlat_nonneg _ _
  have hss := e0c_inv_mul k
  have hMM := e0c_inv_mul (k + N)
  have hpow : (3 : ℝ) ^ (k + N + 3) = (3 : ℝ) ^ (k + N) * 27 := by
    rw [pow_add]; norm_num
  -- Goal A
  have hA : cubeFlat k (fun x => w x - vecDot (p + p') x) ≤ Ch * ((3 : ℝ)⁻¹) ^ N * X := by
    have hq : MemLp (fun x => w x - vecDot (p + p') x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      (eb3_memLp_le (by omega) hwm).sub (hlp k _)
    have h2 := cubeFlat_le_of_sub_const hq c
    have hfun : (fun x => (w x - vecDot (p + p') x) - c) =
        (fun x => (w x - vecDot p x) - c - vecDot p' x) := by
      funext x; rw [vecDot_add_left]; ring
    rw [hfun] at h2
    exact h2.trans (eb3_scale_gain k N Ch X _ h1)
  -- Goal B
  have hB : X ≤ (3 : ℝ) ^ ((d + 2) * 3) * E + 27 * Cin * δ * F := by
    have hWl : MemLp (fun x => W x - vecDot p x) 2
        (normalizedCubeMeasure (originCube d ((k + N : ℕ) : ℤ))) := hWM.sub (hlp _ p)
    have hwl : MemLp (fun x => w x - vecDot p x) 2
        (normalizedCubeMeasure (originCube d ((k + N : ℕ) : ℤ))) := hwm.sub (hlp _ p)
    have hd := eb3_flat_diff hwl hWl
    have hsym : cubeL2 (k + N) (fun x => (w x - vecDot p x) - (W x - vecDot p x)) =
        cubeL2 (k + N) (fun x => W x - w x) := by
      have e1 : (fun x => (w x - vecDot p x) - (W x - vecDot p x)) =
          fun x => (-1 : ℝ) * (W x - w x) := by funext x; ring
      rw [e1, cubeL2_const_mul]; simp
    rw [hsym] at hd
    have hWt : MemLp (fun x => W x - vecDot p x) 2
        (normalizedCubeMeasure (originCube d ((k + N + 3 : ℕ) : ℤ))) := hW.sub (hlp _ p)
    have h3 := eb3_flat_le (Nat.le_add_right (k + N) 3) hWt
    have h4 : k + N + 3 - (k + N) = 3 := by omega
    rw [h4] at h3
    have h5 := mul_le_mul_of_nonneg_left hcl (by positivity : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ (k + N))
    have h6 : ((3 : ℝ)⁻¹) ^ (k + N) * (Cin * δ * (3 : ℝ) ^ (k + N + 3) * F) =
        27 * Cin * δ * F := by
      rw [hpow]
      linear_combination (27 * Cin * δ * F) * hMM
    linarith only [hd, h3, h5, h6]
  -- Goal C
  have hC : cubeFlat k (fun x => W x - w x) ≤
      (3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin * δ * F := by
    have hWw : MemLp (fun x => W x - w x) 2
        (normalizedCubeMeasure (originCube d ((k + N : ℕ) : ℤ))) := hWM.sub hwm
    have hWwk : MemLp (fun x => W x - w x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) := eb3_memLp_le (by omega) hWw
    have h1 := cubeFlat_le_of_sub_const hWwk 0
    simp only [sub_zero] at h1
    have h2 := eb3_l2_le (Nat.le_add_right k N) hWw
    rw [hNk] at h2
    have h3 := h2.trans (mul_le_mul_of_nonneg_left hcl (by positivity))
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ k)
    have h5 : ((3 : ℝ)⁻¹) ^ k * ((3 : ℝ) ^ (d * N) * (Cin * δ * (3 : ℝ) ^ (k + N + 3) * F)) =
        (3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin * δ * F := by
      rw [pow_add, pow_add]
      linear_combination ((3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin * δ * F) * hss
    linarith only [h1, h4, h5]
  have hsplit : cubeFlat k (fun x => W x - vecDot (p + p') x) ≤
      cubeFlat k (fun x => W x - w x) + cubeFlat k (fun x => w x - vecDot (p + p') x) := by
    have hWwk : MemLp (fun x => W x - w x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      eb3_memLp_le (by omega) (hWM.sub hwm)
    have hwq : MemLp (fun x => w x - vecDot (p + p') x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      (eb3_memLp_le (by omega) hwm).sub (hlp k _)
    have h := cubeFlat_add_le hWwk hwq
    have e1 : (fun x => (W x - w x) + (w x - vecDot (p + p') x)) =
        fun x => W x - vecDot (p + p') x := by funext x; ring
    rw [e1] at h
    exact h
  have hmin := cubeFlat_sub_affSlope_le hWk (p + p')
  have hcoef : 0 ≤ Ch * ((3 : ℝ)⁻¹) ^ N := by positivity
  have h7 := mul_le_mul_of_nonneg_left hB hcoef
  have h8 : Ch * ((3 : ℝ)⁻¹) ^ N * X ≤ Ch * ((3 : ℝ)⁻¹) ^ N *
      ((3 : ℝ) ^ ((d + 2) * 3) * E + 27 * Cin * δ * F) := h7
  nlinarith only [hmin, hsplit, hC, hA, h8]

theorem eb3_one_le_sqrt : (1 : ℝ) ≤ 2 * Real.sqrt 3 := by
  have : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith only [this]

theorem eb3_flat_le_slope [NeZero d] {n : ℕ} {W : Vec d → ℝ}
    (hW : MemLp W 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (p : Vec d) :
    cubeFlat n W ≤ cubeFlat n (fun x => W x - vecDot p x) + engNorm p := by
  have hl := e0c_memLp n (e0c_continuous_vecDot p)
  have hWl : MemLp (fun x => W x - vecDot p x) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := hW.sub hl
  have h := cubeFlat_add_le hWl hl
  have e1 : (fun x => (W x - vecDot p x) + vecDot p x) = W := by funext x; ring
  rw [e1, cubeFlat_vecDot] at h
  have h2 : engNorm p / (2 * Real.sqrt 3) ≤ engNorm p :=
    div_le_self (engNorm_nonneg p) eb3_one_le_sqrt
  linarith only [h, h2]

/-- Induction over the scales: the flatness bound and the slope bound at every scale of the window. -/
theorem eb3_bounds [NeZero d] (Cin Ch : ℝ) (hCin : 1 ≤ Cin) (hCh : 1 ≤ Ch)
    (N : ℕ) (K1 K2 c0 : ℝ) (hN : 1 ≤ N)
    (hQ : Ch * ((3 : ℝ)⁻¹) ^ N * (3 : ℝ) ^ ((d + 2) * 3) ≤ 1 / 8)
    (hK1 : (3 : ℝ) ^ ((d + 2) * (N + 3)) * Cin ≤ K1)
    (hK1b : 3 * ((3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin + 27 * Cin * Ch * ((3 : ℝ)⁻¹) ^ N) ≤ K1)
    (hK2 : 4 * Cin + 4 * (3 : ℝ) ^ (d + 2) * K1 ≤ K2)
    (hc0A : ((3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin + 27 * Cin * Ch * ((3 : ℝ)⁻¹) ^ N) * c0 ≤ 1 / 8)
    (hc0K : K2 * c0 ≤ 1)
    (a : CoeffField d) (δ : ℝ) (Hb j : ℕ) (hδ : 0 ≤ δ) (hδc : δ * ((Hb : ℝ) + 1) ≤ c0)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hF4 : ∀ (k l : ℕ), l + 1 ≤ k →
      ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
        IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
        ∃ (p : Vec d) (c : ℝ),
          cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤
              Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
            engNorm p ≤ Ch * cubeFlat k w)
    (hHA : ∀ t : ℕ, t ≤ j → j + 2 ≤ t + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
        ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
            cubeL2 (t - 3) (fun x => u x - w x) ≤
              Cin * δ * (3 : ℝ) ^ t * cubeFlat t u)
    (W : Vec d → ℝ) (g : Vec d → Vec d) (hWsol : IsSolOn a (engCube d j) W g) (e : Vec d)
    (hWflat : cubeFlat j (fun x => W x - vecDot e x) ≤ Cin * δ * engNorm e) :
    ∀ i : ℕ, i ≤ j → j ≤ i + Hb →
      cubeFlat i (fun x => W x - vecDot (affSlope i W) x) ≤ K1 * δ * engNorm e ∧
        engNorm (affSlope i W - e) ≤ K2 * δ * (((j : ℝ) - (i : ℝ)) + 1) * engNorm e := by
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCh0 : 0 ≤ Ch := by linarith only [hCh]
  have hWmem := hWsol.memLp.1
  have hmem : ∀ i : ℕ, i ≤ j →
      MemLp W 2 (normalizedCubeMeasure (originCube d (i : ℤ))) :=
    fun i hi => eb3_memLp_le hi hWmem
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = δ * engNorm e := ⟨_, rfl⟩
  have hmul : ∀ c : ℝ, c * δ * engNorm e = c * u := fun c => by rw [hu, mul_assoc]
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg hδ (engNorm_nonneg e)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (3 : ℝ) ^ (d * N) * (3 : ℝ) ^ N * 27 * Cin +
      27 * Cin * Ch * ((3 : ℝ)⁻¹) ^ N := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  rw [← hAdef] at hK1b hc0A
  have hK10 : 0 ≤ K1 := by linarith only [hK1b, hA0]
  have hδc0 : δ ≤ c0 := by
    have : 0 ≤ δ * (Hb : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
    linarith only [hδc, this]
  have hC1 : 0 ≤ 4 * (3 : ℝ) ^ (d + 2) := by positivity
  have hK2a : 4 * Cin ≤ K2 := by
    have : 0 ≤ 4 * (3 : ℝ) ^ (d + 2) * K1 := mul_nonneg hC1 hK10
    linarith only [hK2, this]
  have hK2b : 4 * (3 : ℝ) ^ (d + 2) * K1 ≤ K2 := by linarith only [hK2, hCin0]
  have hflat0 : cubeFlat j (fun x => W x - vecDot e x) ≤ Cin * u := by
    rw [← hmul]; exact hWflat
  -- slope bound from flatness bounds
  have hslope : ∀ i : ℕ, i ≤ j → j ≤ i + Hb →
      (∀ i' : ℕ, i ≤ i' → i' ≤ j →
        cubeFlat i' (fun x => W x - vecDot (affSlope i' W) x) ≤ K1 * u) →
      engNorm (affSlope i W - e) ≤ K2 * u * (((j : ℝ) - (i : ℝ)) + 1) := by
    intro i hij hji hE
    have h := eb3_slope_chain hWmem e (Cin * u) (K1 * u) hflat0 (j - i) i (by omega) hE
    have hn : (((j - i : ℕ) : ℝ)) = (j : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub hij]
    rw [hn] at h
    have hn0 : 0 ≤ (j : ℝ) - (i : ℝ) := by rw [← hn]; exact Nat.cast_nonneg _
    have h1 : 4 * (3 : ℝ) ^ (d + 2) * (K1 * u) * ((j : ℝ) - (i : ℝ)) ≤
        K2 * u * ((j : ℝ) - (i : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hK2b hu0
      have h2 : 4 * (3 : ℝ) ^ (d + 2) * (K1 * u) = 4 * (3 : ℝ) ^ (d + 2) * K1 * u := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right this hn0
    have h3 : 4 * (Cin * u) ≤ K2 * u := by
      have := mul_le_mul_of_nonneg_right hK2a hu0
      linarith only [this]
    nlinarith only [h, h1, h3]
  -- the top of the window
  have htop : ∀ i : ℕ, i ≤ j → j - i ≤ N + 2 →
      cubeFlat i (fun x => W x - vecDot (affSlope i W) x) ≤ K1 * u := by
    intro i hij hc
    have hmin := cubeFlat_sub_affSlope_le (hmem i hij) e
    have hWe : MemLp (fun x => W x - vecDot e x) 2
        (normalizedCubeMeasure (originCube d (j : ℤ))) :=
      hWmem.sub (e0c_memLp j (e0c_continuous_vecDot e))
    have h1 := eb3_flat_le hij hWe
    have hp : (3 : ℝ) ^ ((d + 2) * (j - i)) ≤ (3 : ℝ) ^ ((d + 2) * (N + 3)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    have hc0' := cubeFlat_nonneg j (fun x => W x - vecDot e x)
    have h2 := mul_le_mul_of_nonneg_right hp hc0'
    have h3 := mul_le_mul_of_nonneg_left hflat0 (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ ((d + 2) * (N + 3)))
    have h4 := mul_le_mul_of_nonneg_right hK1 hu0
    nlinarith only [hmin, h1, h2, h3, h4]
  have hE : ∀ m : ℕ, ∀ i : ℕ, i ≤ j → j ≤ i + Hb → j - i ≤ m →
      cubeFlat i (fun x => W x - vecDot (affSlope i W) x) ≤ K1 * u := by
    intro m
    induction m with
    | zero => intro i hij _ hm; exact htop i hij (by omega)
    | succ m ih =>
      intro i hij hji hm
      by_cases hc : j - i ≤ N + 2
      · exact htop i hij hc
      have ht : i + N + 3 ≤ j := by omega
      have hEt : ∀ i' : ℕ, i + N + 3 ≤ i' → i' ≤ j →
          cubeFlat i' (fun x => W x - vecDot (affSlope i' W) x) ≤ K1 * u :=
        fun i' h1 h2 => ih i' h2 (by omega) (by omega)
      have hsl := hslope (i + N + 3) ht (by omega) hEt
      have hjt : (((j : ℝ) - ((i + N + 3 : ℕ) : ℝ)) + 1) ≤ (Hb : ℝ) + 1 := by
        have : (j : ℝ) ≤ (i : ℝ) + (Hb : ℝ) := by exact_mod_cast hji
        push_cast
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
        linarith only [this, hN0]
      have hpe : engNorm (affSlope (i + N + 3) W - e) ≤ engNorm e := by
        have h1 := mul_le_mul_of_nonneg_left hjt (mul_nonneg (by linarith only [hK2a, hCin0] : 0 ≤ K2) hu0)
        have h2 : K2 * u * ((Hb : ℝ) + 1) = K2 * (δ * ((Hb : ℝ) + 1)) * engNorm e := by
          rw [hu]; ring
        have h3 := mul_le_mul_of_nonneg_left hδc (by linarith only [hK2a, hCin0] : 0 ≤ K2)
        have h4 := mul_le_mul_of_nonneg_right (h3.trans hc0K) (engNorm_nonneg e)
        nlinarith only [hsl, h1, h2, h4]
      have hpn : engNorm (affSlope (i + N + 3) W) ≤ 2 * engNorm e := by
        have := engNorm_add_le (affSlope (i + N + 3) W - e) e
        have e2 : affSlope (i + N + 3) W - e + e = affSlope (i + N + 3) W := by abel
        rw [e2] at this
        linarith only [this, hpe]
      have hmemt := hmem (i + N + 3) ht
      have hFle := eb3_flat_le_slope hmemt (affSlope (i + N + 3) W)
      have hEt0 := hEt (i + N + 3) le_rfl ht
      have hsolt : IsSolOn a (engCube d (i + N + 3)) W g :=
        IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _) (eb3_cube_mono ht)
          (volume_openCubeSet_lt_top _).ne (hell _) hWsol
      have h3 : i + N + 3 - 3 = i + N := by omega
      obtain ⟨w, gw, hw, hcl⟩ := hHA (i + N + 3) ht (by omega) W g hsolt
      rw [h3] at hw hcl
      have hres := eb3_step Cin Ch δ hCh0 i N hN W (affSlope (i + N + 3) W) hmemt hF4
        ⟨w, gw, hw, hcl⟩
      rw [← hAdef] at hres
      have hAd : A * δ ≤ 1 / 8 := by
        have := mul_le_mul_of_nonneg_left hδc0 hA0
        linarith only [this, hc0A]
      have hAdn : 0 ≤ A * δ := mul_nonneg hA0 hδ
      have hF1 : cubeFlat (i + N + 3) W ≤ K1 * u + 2 * engNorm e := by
        linarith only [hFle, hEt0, hpn]
      have hk1 := mul_le_mul_of_nonneg_left hF1 hAdn
      have hk2 : A * δ * (K1 * u) ≤ 1 / 8 * (K1 * u) :=
        mul_le_mul_of_nonneg_right hAd (mul_nonneg hK10 hu0)
      have hk3 : 2 * A * u ≤ 2 / 3 * (K1 * u) := by
        have := mul_le_mul_of_nonneg_right hK1b hu0
        nlinarith only [this]
      have hk4 : A * δ * (2 * engNorm e) = 2 * A * u := by rw [hu]; ring
      have hQ0 : 0 ≤ Ch * ((3 : ℝ)⁻¹) ^ N * (3 : ℝ) ^ ((d + 2) * 3) := by positivity
      have hk5 := mul_le_mul_of_nonneg_left hEt0 hQ0
      have hk6 : Ch * ((3 : ℝ)⁻¹) ^ N * (3 : ℝ) ^ ((d + 2) * 3) * (K1 * u) ≤ 1 / 8 * (K1 * u) :=
        mul_le_mul_of_nonneg_right hQ (mul_nonneg hK10 hu0)
      have hk7 : A * δ * (K1 * u + 2 * engNorm e) = A * δ * (K1 * u) + 2 * A * u := by
        rw [mul_add, hk4]
      have hK1u : 0 ≤ K1 * u := mul_nonneg hK10 hu0
      nlinarith only [hres, hk1, hk2, hk3, hk5, hk6, hk7, hK1u]
  intro i hij hji
  have hEi := hE (j - i) i hij hji le_rfl
  refine ⟨by rw [hmul]; exact hEi, ?_⟩
  have := hslope i hij hji (fun i' h1 h2 => hE (j - i) i' h2 (by omega) (by omega))
  calc _ ≤ _ := this
    _ = _ := by rw [hu]; ring

/-- **E-B3 (flatness of a top-scale corrected affine inside its window)**, Step 3. -/
theorem eng_window_flat (d : ℕ) [NeZero d] (Cin Ch : ℝ) (hCin : 1 ≤ Cin) (hCh : 1 ≤ Ch) :
    ∃ (K c0 : ℝ) (N : ℕ), 1 ≤ K ∧ 0 < c0 ∧
      ∀ (a : CoeffField d) (δ : ℕ → ℝ) (Hb mstar : ℕ)
        (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
        N ≤ Hb → Hb + 3 ≤ mstar →
        (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c0) →
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
        -- hVflat
        (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
          cubeFlat j (fun x => V j e x - vecDot e x) ≤ Cin * δ j * engNorm e) →
        -- conclusion: hflat K
        ∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
          cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤
              K * δ j * engNorm e ∧
            engNorm (affSlope k (V j e) - e) ≤
              K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e := by
  classical
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (8 * (Ch * (3 : ℝ) ^ ((d + 2) * 3))) by positivity)
    (show ((3 : ℝ)⁻¹) < 1 by norm_num)
  have hCh0 : 0 < Ch := by linarith only [hCh]
  have hC3 : (0 : ℝ) < 3 ^ ((d + 2) * 3) := by positivity
  have hQ : Ch * ((3 : ℝ)⁻¹) ^ (n + 1) * (3 : ℝ) ^ ((d + 2) * 3) ≤ 1 / 8 := by
    have h1 : ((3 : ℝ)⁻¹) ^ (n + 1) ≤ ((3 : ℝ)⁻¹) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
    have hpos : 0 < Ch * (3 : ℝ) ^ ((d + 2) * 3) := mul_pos hCh0 hC3
    have h2 : ((3 : ℝ)⁻¹) ^ n * (8 * (Ch * (3 : ℝ) ^ ((d + 2) * 3))) < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (Ch * (3 : ℝ) ^ ((d + 2) * 3)))).1 hn
      exact this
    have h3 : ((3 : ℝ)⁻¹) ^ (n + 1) * (Ch * (3 : ℝ) ^ ((d + 2) * 3)) ≤
        ((3 : ℝ)⁻¹) ^ n * (Ch * (3 : ℝ) ^ ((d + 2) * 3)) :=
      mul_le_mul_of_nonneg_right h1 hpos.le
    nlinarith only [h2, h3]
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (3 : ℝ) ^ (d * (n + 1)) * (3 : ℝ) ^ (n + 1) * 27 * Cin +
      27 * Cin * Ch * ((3 : ℝ)⁻¹) ^ (n + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ, K1 = (3 : ℝ) ^ ((d + 2) * (n + 1 + 3)) * Cin + 3 * A + 1 :=
    ⟨_, rfl⟩
  have hK1pos : 0 ≤ (3 : ℝ) ^ ((d + 2) * (n + 1 + 3)) * Cin := by positivity
  have hK11 : 1 ≤ K1 := by rw [hK1def]; linarith only [hK1pos, hA0]
  obtain ⟨K2, hK2def⟩ : ∃ K2 : ℝ, K2 = 4 * Cin + 4 * (3 : ℝ) ^ (d + 2) * K1 := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by
    rw [hK2def]
    have : 0 ≤ 4 * (3 : ℝ) ^ (d + 2) * K1 := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * (3 : ℝ) ^ (d + 2)) (by linarith only [hK11] : (0 : ℝ) ≤ K1)
      exact this
    linarith only [this, hCin0]
  have hS : 0 < 8 * (A + K2 + 1) := by positivity
  refine ⟨K1 + K2, 1 / (8 * (A + K2 + 1)), n + 1, by linarith only [hK11, hK20],
    by positivity, ?_⟩
  intro a δ Hb mstar V _ _ hδ hell hF4 hHA hVsol hVflat j k hmj hkj hjk e
  have hc0 : 1 / (8 * (A + K2 + 1)) * (8 * (A + K2 + 1)) = 1 := by field_simp
  have hc0p : 0 < 1 / (8 * (A + K2 + 1)) := by positivity
  have hc0A : A * (1 / (8 * (A + K2 + 1))) ≤ 1 / 8 := by
    have h1 : A * (1 / (8 * (A + K2 + 1))) ≤ (A + K2 + 1) * (1 / (8 * (A + K2 + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith only [hK20]) hc0p.le
    nlinarith only [h1, hc0]
  have hc0K : K2 * (1 / (8 * (A + K2 + 1))) ≤ 1 := by
    have h1 : K2 * (1 / (8 * (A + K2 + 1))) ≤ (A + K2 + 1) * (1 / (8 * (A + K2 + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith only [hA0]) hc0p.le
    nlinarith only [h1, hc0]
  obtain ⟨g, hg⟩ := hVsol j hmj e
  have hb := eb3_bounds Cin Ch hCin hCh (n + 1) K1 K2 (1 / (8 * (A + K2 + 1))) (by omega) hQ
    (by rw [hK1def]; linarith only [hA0]) (by rw [hK1def, ← hAdef]; linarith only [hK1pos])
    (by rw [hK2def]) (by rw [← hAdef] ; exact hc0A) hc0K a (δ j) Hb j (hδ j hmj).1
    (hδ j hmj).2 hell hF4 (fun t h1 h2 u g' hu => hHA j t hmj h1 h2 u g' hu) (V j e) g hg e
    (hVflat j hmj e) k hkj hjk
  have hu0 : 0 ≤ δ j * engNorm e := mul_nonneg (hδ j hmj).1 (engNorm_nonneg e)
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right (by linarith only [hK20] : K1 ≤ K1 + K2) hu0
    nlinarith only [hb.1, this]
  · have hj0 : 0 ≤ ((j : ℝ) - (k : ℝ)) + 1 := by
      have : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
      linarith only [this]
    have h1 := mul_le_mul_of_nonneg_right (by linarith only [hK11] : K2 ≤ K1 + K2)
      (mul_nonneg hu0 hj0)
    nlinarith only [hb.2, h1]

/-- Witness for the numerical hypotheses: `δ = 0` with `Hb = N` and `mstar = N + 3` satisfies the
size and smallness conditions for every `c0 > 0`. -/
example (c0 : ℝ) (hc : 0 < c0) (N : ℕ) :
    ∃ (Hb mstar : ℕ) (δ : ℕ → ℝ), N ≤ Hb ∧ Hb + 3 ≤ mstar ∧
      ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c0 :=
  ⟨N, N + 3, fun _ => 0, le_rfl, le_rfl, fun _ _ => ⟨le_rfl, by simpa using hc.le⟩⟩

end SuperdiffusionCLT.Section6
