/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.FiniteB

/-!
# Finite-volume estimate: the iteration over blocks
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The iteration: increments `P t`, with the flatness of the remainder at the block endpoints,
the geometric bounds of the increments, and the flatness of the remainder inside each block. -/
theorem eb5b_iter [NeZero d] {a : CoeffField d} {C5 Ct c4 η κ : ℝ} {δ : ℕ → ℝ}
    {Hb mstar : ℕ} (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)) (hC5 : 1 ≤ C5) (hCt : 0 ≤ Ct)
    (hCtc4 : Ct * c4 ≤ 1) (hCb : 2 * C5 ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
        ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c4)
    (hblock : ∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
        ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
          ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
            ∀ k : ℕ, l ≤ k → k ≤ j →
              cubeFlat k (fun x => w x - V j e x) ≤
                C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w)
    (htrans : ∀ m j l : ℕ, mstar ≤ j → j ≤ m → l ≤ j → j ≤ l + Hb → ∀ p : Vec d,
        ∃ pt : Vec d,
          engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p ∧
            ∀ k : ℕ, l ≤ k → k ≤ j →
              cubeFlat k (fun x => V m pt x - V j p x) ≤
                Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p)
    {m k0 : ℕ} (hk0 : mstar ≤ k0) (hkm : k0 ≤ m)
    {w : Vec d → ℝ} (hw : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) (i : ℕ) :
    ∃ P : ℕ → Vec d,
      (∀ s : ℕ, s ≤ i →
        cubeFlat (max k0 (m - s * Hb)) (fun x => w x - V m (∑ t ∈ Finset.range s, P t) x) ≤
          (2 * C5) ^ s * (3 : ℝ) ^ (-(η * ((m : ℝ) - ((max k0 (m - s * Hb) : ℕ) : ℝ)))) *
            cubeFlat m w) ∧
      (∀ s : ℕ, s < i →
        engNorm (P s) ≤ Ct * C5 * (3 : ℝ) ^ (-((η - 2 * κ) * ((s : ℝ) * Hb))) * cubeFlat m w) ∧
      (∀ s : ℕ, s < i → ∀ k : ℕ, max k0 (m - (s + 1) * Hb) ≤ k → k ≤ max k0 (m - s * Hb) →
        cubeFlat k (fun x => w x - V m (∑ t ∈ Finset.range (s + 1), P t) x) ≤
          (2 * C5) ^ (s + 1) * (3 : ℝ) ^ (-(η * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) := by
  induction i with
  | zero =>
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro s hs
      have hs0 : s = 0 := by omega
      subst hs0
      have hm : max k0 (m - 0 * Hb) = m := by simp [hkm]
      rw [hm]
      simp
    · intro s hs; omega
    · intro s hs; omega
  | succ i ih =>
    obtain ⟨P, h1, h2, h3⟩ := ih
    obtain ⟨pt, hq1, hq2⟩ := eb5b_iter_step V hC5 hCt hCtc4 hCb hell hVsol hδ hblock htrans hk0 hkm
      hw i (∑ t ∈ Finset.range i, P t) (h1 i le_rfl)
    have hsum : ∀ s : ℕ, s ≤ i →
        ∑ t ∈ Finset.range s, (if t = i then pt else P t) = ∑ t ∈ Finset.range s, P t := by
      intro s hs
      refine Finset.sum_congr rfl fun t ht => ?_
      have := Finset.mem_range.1 ht
      simp only [show t ≠ i by omega, ↓reduceIte]
    have hsum1 : ∑ t ∈ Finset.range (i + 1), (if t = i then pt else P t) =
        ∑ t ∈ Finset.range i, P t + pt := by
      rw [Finset.sum_range_succ, hsum i le_rfl]
      simp
    refine ⟨fun t => if t = i then pt else P t, ?_, ?_, ?_⟩
    · intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hs) with hlt | heq
      · rw [hsum s (by omega)]
        exact h1 s (by omega)
      · subst heq
        rw [hsum1]
        exact hq1 _ le_rfl (eb5b_J_succ_le k0 m Hb i)
    · intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hlt | heq
      · simp only [show s ≠ i by omega, ↓reduceIte]
        exact h2 s hlt
      · subst heq
        simp only [↓reduceIte]
        exact hq2
    · intro s hs k hk1 hk2
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hlt | heq
      · rw [hsum (s + 1) (by omega)]
        exact h3 s hlt k hk1 hk2
      · subst heq
        rw [hsum1]
        exact hq1 k hk1 hk2

theorem eb5b_geom {x q0 : ℝ} (hx : 0 ≤ x) (hxq : x ≤ q0) (hq0 : q0 < 1) (a b : ℕ) :
    ∑ t ∈ Finset.Ico a b, x ^ t ≤ x ^ a * (1 / (1 - q0)) := by
  have h1 : x < 1 := lt_of_le_of_lt hxq hq0
  refine (geom_sum_Ico_le_of_lt_one hx h1).trans ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (pow_nonneg hx _) (by linarith only [hq0]) (by linarith only [hxq])

theorem eb5b_q_le {η κ : ℝ} {Hb : ℕ} (hη : 1 / 2 ≤ η) (hκ : κ ≤ 1 / 24) (hHb : 1 ≤ Hb) :
    (3 : ℝ) ^ (-((η - 2 * κ) * (Hb : ℝ))) ≤ (3 : ℝ) ^ (-(5 / 12 : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h1 : (1 : ℝ) ≤ Hb := by exact_mod_cast hHb
  have h2 : 0 ≤ η - 2 * κ := by linarith only [hη, hκ]
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  linarith only [h3, hη, hκ]

theorem eb5b_pow_eq (x : ℝ) (Hb t : ℕ) :
    (3 : ℝ) ^ (-(x * ((t : ℝ) * Hb))) = ((3 : ℝ) ^ (-(x * (Hb : ℝ)))) ^ t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

/-- **E-B5b (finite-volume `C^{1,η-3κ}` estimate, simultaneous form)**,
`e.sharp.Cone.finite.Cone.simultaneous` with `e.sharp.Cone.finite.Cone.slope`, in oscillation
form. -/
theorem eng_finite (d : ℕ) [NeZero d] (K C5 Cc Ct : ℝ) (hK : 1 ≤ K) (hC5 : 1 ≤ C5)
    (hCc : 1 ≤ Cc) (hCt : 1 ≤ Ct) :
    ∃ (Cf Cb c4 : ℝ), 1 ≤ Cf ∧ 1 ≤ Cb ∧ 0 < c4 ∧
      ∀ η κ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 / 24 →
        ∀ (a : CoeffField d) (δ : ℕ → ℝ) (Hb mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
          1 ≤ Hb → Hb + 3 ≤ mstar →
          Cb ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) →
          (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c4) →
          -- hell
          (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
          -- hVsol
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
          -- hflat K
          (∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
            cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤
                K * δ j * engNorm e ∧
              engNorm (affSlope k (V j e) - e) ≤
                K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e) →
          -- hblock C5 η
          (∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
              ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
                ∀ k : ℕ, l ≤ k → k ≤ j →
                  cubeFlat k (fun x => w x - V j e x) ≤
                    C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w) →
          -- hchain Cc κ
          (∀ m k : ℕ, mstar ≤ k → k ≤ m →
            (∀ e : Vec d, ∃ q : Vec d,
              affSlope k (V k q) = affSlope k (V m e) ∧
                cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
                engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
                engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
              ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q)) →
          -- htrans Ct η κ
          (∀ m j l : ℕ, mstar ≤ j → j ≤ m → l ≤ j → j ≤ l + Hb → ∀ p : Vec d,
            ∃ pt : Vec d,
              engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p ∧
                ∀ k : ℕ, l ≤ k → k ≤ j →
                  cubeFlat k (fun x => V m pt x - V j p x) ≤
                    Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p) →
          -- conclusion: hfin Cf (η - 3κ)
          ∀ m k0 : ℕ, mstar ≤ k0 → k0 ≤ m →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
              ∃ e : Vec d, engNorm e ≤ Cf * cubeFlat m w ∧
                ∀ k : ℕ, k0 ≤ k → k ≤ m →
                  cubeFlat k (fun x => w x - V m e x) ≤
                    Cf * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w := by
  have hCt0 : 0 ≤ Ct := by linarith only [hCt]
  have hC50 : 0 ≤ C5 := by linarith only [hC5]
  have hCc0 : 0 ≤ Cc := by linarith only [hCc]
  have hKCt : 0 < Ct + K := by linarith only [hCt, hK]
  have hq0lt : (3 : ℝ) ^ (-(5 / 12 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  set q0 : ℝ := (3 : ℝ) ^ (-(5 / 12 : ℝ)) with hq0
  set G : ℝ := 1 / (1 - q0) with hG
  have hGpos : 0 < G := by
    rw [hG]; exact one_div_pos.2 (by linarith only [hq0lt])
  have hbase : 0 ≤ Ct * C5 * G := mul_nonneg (mul_nonneg hCt0 hC50) hGpos.le
  have hcv : 0 ≤ Cc * (Cc + 2) * (Ct * C5 * G) :=
    mul_nonneg (mul_nonneg hCc0 (by linarith only [hCc0])) hbase
  refine ⟨1 + Ct * C5 * G + 2 * C5 + Cc * (Cc + 2) * (Ct * C5 * G), 2 * C5, 1 / (Ct + K),
    by linarith only [hbase, hcv, hC5], by linarith only [hC5], one_div_pos.2 hKCt, ?_⟩
  intro η κ hη1 hη2 hκ0 hκ1 a δ Hb mstar V hHb hmstar hCb hδ hell hVsol hflat hblock hchain
    htrans m k0 hk0 hkm w hw
  have hc4 : 1 / (Ct + K) ≤ 1 := by
    rw [div_le_one hKCt]; linarith only [hCt, hK]
  have hCtc4 : Ct * (1 / (Ct + K)) ≤ 1 := by
    rw [mul_one_div, div_le_one hKCt]; linarith only [hK]
  have hKc4 : K * (1 / (Ct + K)) ≤ 1 := by
    rw [mul_one_div, div_le_one hKCt]; linarith only [hCt]
  have hδ' : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ 1 / (Ct + K) :=
    fun j hj => ⟨(hδ j hj).1, by
      have h := (hδ j hj).2
      have h1 : (1 : ℝ) ≤ Hb := by exact_mod_cast hHb
      nlinarith only [h, h1, (hδ j hj).1]⟩
  have hδle : ∀ j : ℕ, mstar ≤ j → δ j ≤ 1 / (Ct + K) := by
    intro j hj
    obtain ⟨h0, h⟩ := hδ' j hj
    have : (0 : ℝ) ≤ Hb := Nat.cast_nonneg _
    nlinarith only [h0, h, this]
  obtain ⟨P, h1, h2, h3⟩ := eb5b_iter V hC5 hCt0 hCtc4 hCb hell hVsol hδ' hblock htrans hk0 hkm hw
    (m - k0 + 1)
  have hη' : 0 ≤ η - 2 * κ := by linarith only [hη1, hκ1]
  set q : ℝ := (3 : ℝ) ^ (-((η - 2 * κ) * (Hb : ℝ))) with hq
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq_le : q ≤ q0 := eb5b_q_le hη1 hκ1 hHb
  have hΩm := cubeFlat_nonneg m w
  have hPn : ∀ t : ℕ, t < m - k0 + 1 →
      engNorm (P t) ≤ Ct * C5 * cubeFlat m w * q ^ t := by
    intro t ht
    have h := h2 t ht
    rw [eb5b_pow_eq] at h
    linarith only [h]
  have hsumP : ∀ a b : ℕ, b ≤ m - k0 + 1 →
      engNorm (∑ t ∈ Finset.Ico a b, P t) ≤ Ct * C5 * cubeFlat m w * (q ^ a * G) := by
    intro a b hb
    refine (eb5b_engNorm_sum_le _ _).trans ?_
    calc ∑ t ∈ Finset.Ico a b, engNorm (P t)
        ≤ ∑ t ∈ Finset.Ico a b, Ct * C5 * cubeFlat m w * q ^ t :=
          Finset.sum_le_sum fun t ht => hPn t (by have := (Finset.mem_Ico.1 ht).2; omega)
      _ = Ct * C5 * cubeFlat m w * ∑ t ∈ Finset.Ico a b, q ^ t := by rw [← Finset.mul_sum]
      _ ≤ Ct * C5 * cubeFlat m w * (q ^ a * G) :=
          mul_le_mul_of_nonneg_left (eb5b_geom hq_nonneg hq_le hq0lt a b)
            (mul_nonneg (mul_nonneg hCt0 hC50) hΩm)
  refine ⟨∑ t ∈ Finset.range (m - k0 + 1), P t, ?_, ?_⟩
  · have h := hsumP 0 (m - k0 + 1) le_rfl
    rw [← Finset.range_eq_Ico] at h
    simp only [pow_zero, one_mul] at h
    have h0 : 0 ≤ Ct * C5 * cubeFlat m w * G :=
      mul_nonneg (mul_nonneg (mul_nonneg hCt0 hC50) hΩm) hGpos.le
    refine h.trans ?_
    have h5 : 0 ≤ (1 + 2 * C5 + Cc * (Cc + 2) * (Ct * C5 * G)) * cubeFlat m w :=
      mul_nonneg (by linarith only [hC50, hcv]) hΩm
    have e : (1 + Ct * C5 * G + 2 * C5 + Cc * (Cc + 2) * (Ct * C5 * G)) * cubeFlat m w =
        Ct * C5 * cubeFlat m w * G + (1 + 2 * C5 + Cc * (Cc + 2) * (Ct * C5 * G)) *
          cubeFlat m w := by ring
    linarith only [e, h5, h0]
  · intro k hk1 hk2
    have hkm' : k ≤ m := hk2
    set x : ℕ := m - k with hx
    set s : ℕ := x / Hb with hs
    have hHbpos : 0 < Hb := hHb
    have hs1 : s * Hb ≤ x := Nat.div_mul_le_self x Hb
    have hs2 : x < s * Hb + Hb := Nat.lt_div_mul_add hHbpos
    have hs3 : s ≤ x := Nat.div_le_self x Hb
    have hsuc : (s + 1) * Hb = s * Hb + Hb := Nat.succ_mul s Hb
    have hN : s + 1 ≤ m - k0 + 1 := by omega
    have hJ1 : max k0 (m - (s + 1) * Hb) ≤ k := by omega
    have hJ2 : k ≤ max k0 (m - s * Hb) := by omega
    set D : ℝ := (m : ℝ) - (k : ℝ) with hD
    have hD0 : 0 ≤ D := by
      have : (k : ℝ) ≤ m := by exact_mod_cast hkm'
      rw [hD]; linarith only [this]
    have hxD : (x : ℝ) = D := by rw [hx, Nat.cast_sub hkm']
    have hr1 : (s : ℝ) * Hb ≤ D := by
      have := (Nat.cast_le (α := ℝ)).2 hs1
      push_cast at this
      linarith only [this, hxD]
    have hr2 : D ≤ ((s : ℝ) + 1) * Hb := by
      have := (Nat.cast_le (α := ℝ)).2 (hs2.le.trans (le_of_eq hsuc.symm))
      push_cast at this
      linarith only [this, hxD]
    -- the remainder at the block
    have hA := h3 s (by omega) k hJ1 hJ2
    -- the increments below the block
    set T : Vec d := ∑ t ∈ Finset.Ico (s + 1) (m - k0 + 1), P t with hT
    have hsplit : ∑ t ∈ Finset.range (m - k0 + 1), P t =
        ∑ t ∈ Finset.range (s + 1), P t + T := by
      rw [hT, Finset.sum_range_add_sum_Ico _ hN]
    have hnT : engNorm T ≤ Ct * C5 * cubeFlat m w * (q ^ (s + 1) * G) :=
      hsumP (s + 1) (m - k0 + 1) le_rfl
    have hqs : q ^ (s + 1) ≤ (3 : ℝ) ^ (-((η - 2 * κ) * D)) := by
      rw [hq, ← eb5b_pow_eq]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (η - 2 * κ) * D ≤ (η - 2 * κ) * (((s + 1 : ℕ) : ℝ) * Hb) := by
        refine mul_le_mul_of_nonneg_left ?_ hη'
        push_cast
        exact hr2
      linarith only [this]
    have hVT := eb5b_V_bound (a := a) (K := K) (Cc := Cc) (δk := δ k) (κ := κ) (k := k) (m := m) V
      hell
      (by have := mul_le_mul_of_nonneg_left (hδle k (hk0.trans hk1)) (by linarith only [hK] : 0 ≤ K)
          linarith only [this, hKc4])
      (hδle k (hk0.trans hk1) |>.trans hc4) hCc hkm' (hVsol k (hk0.trans hk1))
      (hVsol m (hk0.trans hkm)) (hflat k k (hk0.trans hk1) le_rfl (by omega))
      (fun e => (hchain m k (hk0.trans hk1) hkm').1 e) T
    -- assemble
    have e1 : (fun y => w y - V m (∑ t ∈ Finset.range (m - k0 + 1), P t) y) =
        fun y => (w y - V m (∑ t ∈ Finset.range (s + 1), P t) y) - V m T y := by
      funext y
      rw [hsplit]
      simp only [map_add, Pi.add_apply]
      ring
    have hμ : ∀ n : ℕ, k ≤ n → n ≤ m → ∀ u : Vec d → ℝ,
        (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) u g) →
        MemLp u 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      fun n _ _ u hu => eb5b_memLp (hell k) hkm' hu
    have hμw := hμ k le_rfl hkm' w hw
    have hμV : ∀ z : Vec d, MemLp (V m z) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      fun z => eb5b_memLp (hell k) hkm' (hVsol m (hk0.trans hkm) z)
    have hμS : MemLp (fun y => w y - V m (∑ t ∈ Finset.range (s + 1), P t) y) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      hμw.sub (hμV _)
    have htri := eb5b_flat_sub_le hμS (hμV T)
    rw [e1]
    -- exponent bookkeeping
    set Y : ℝ := (3 : ℝ) ^ (-((η - 3 * κ) * D)) with hY
    have hYn : 0 ≤ Y := Real.rpow_nonneg (by norm_num) _
    have hB : (3 : ℝ) ^ (κ * D) * (3 : ℝ) ^ (-((η - 2 * κ) * D)) = Y := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hA' : (3 : ℝ) ^ (κ * D) * (3 : ℝ) ^ (-(η * D)) ≤ Y := by
      rw [← Real.rpow_add (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith only [hκ0, hD0]
    have hcb := eb5b_cb_pow (by linarith only [hC5] : 0 ≤ 2 * C5) hCb s
    have hcb' : (2 * C5) ^ s ≤ (3 : ℝ) ^ (κ * D) :=
      hcb.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hr1 hκ0.le))
    have hn1 : (3 : ℝ) ^ (κ * D) * (3 : ℝ) ^ (-(η * D)) * cubeFlat m w ≥ 0 := by positivity
    have hT1 : cubeFlat k (fun y => w y - V m (∑ t ∈ Finset.range (s + 1), P t) y) ≤
        2 * C5 * (Y * cubeFlat m w) := by
      have hpow : (2 * C5) ^ (s + 1) ≤ 2 * C5 * (3 : ℝ) ^ (κ * D) := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_left hcb' (by linarith only [hC5])
      have hE : 0 ≤ (3 : ℝ) ^ (-(η * ((m : ℝ) - (k : ℝ)))) := Real.rpow_nonneg (by norm_num) _
      calc _ ≤ _ := hA
        _ ≤ 2 * C5 * (3 : ℝ) ^ (κ * D) * (3 : ℝ) ^ (-(η * ((m : ℝ) - (k : ℝ)))) *
              cubeFlat m w :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hE) hΩm
        _ = 2 * C5 * ((3 : ℝ) ^ (κ * D) * (3 : ℝ) ^ (-(η * D)) * cubeFlat m w) := by
            rw [hD]; ring
        _ ≤ 2 * C5 * (Y * cubeFlat m w) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA' hΩm)
              (by linarith only [hC5])
    have hT2 : cubeFlat k (V m T) ≤
        Cc * (Cc + 2) * (Ct * C5 * G) * (Y * cubeFlat m w) := by
      have hN1 : engNorm T ≤ Ct * C5 * cubeFlat m w * ((3 : ℝ) ^ (-((η - 2 * κ) * D)) * G) :=
        hnT.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hqs hGpos.le)
          (mul_nonneg (mul_nonneg hCt0 hC50) hΩm))
      have hCv : 0 ≤ Cc * (Cc + 2) * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) :=
        mul_nonneg (mul_nonneg hCc0 (by linarith only [hCc0])) (Real.rpow_nonneg (by norm_num) _)
      calc cubeFlat k (V m T)
          ≤ Cc * (Cc + 2) * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm T := hVT
        _ ≤ Cc * (Cc + 2) * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) *
              (Ct * C5 * cubeFlat m w * ((3 : ℝ) ^ (-((η - 2 * κ) * D)) * G)) :=
            mul_le_mul_of_nonneg_left hN1 hCv
        _ = Cc * (Cc + 2) * (Ct * C5 * G) *
              ((3 : ℝ) ^ (κ * D) * (3 : ℝ) ^ (-((η - 2 * κ) * D)) * cubeFlat m w) := by
            rw [hD]; ring
        _ = _ := by rw [hB]
    have hrest : 0 ≤ (1 + Ct * C5 * G) * (Y * cubeFlat m w) := by positivity
    linarith only [htri, hT1, hT2, hrest]

/-- The numerical hypotheses of `eng_finite` are satisfiable: `C5 = 1`, `κ = 1/24`, `η = 1/2`,
`Hb = 16`, `mstar = 19`, `δ = 0`. -/
example (c4 : ℝ) (hc4 : 0 < c4) :
    ∃ (η κ : ℝ) (Hb mstar : ℕ), 1 / 2 ≤ η ∧ η < 1 ∧ 0 < κ ∧ κ ≤ 1 / 24 ∧ 1 ≤ Hb ∧
      Hb + 3 ≤ mstar ∧ 2 * (1 : ℝ) ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) ∧
      ∀ j : ℕ, mstar ≤ j → 0 ≤ (0 : ℝ) ∧ (0 : ℝ) * ((Hb : ℝ) + 1) ≤ c4 := by
  refine ⟨1 / 2, 1 / 24, 16, 19, le_rfl, by norm_num, by norm_num, le_rfl, by norm_num,
    by norm_num, ?_, fun j _ => ⟨le_rfl, by simpa using hc4.le⟩⟩
  have h : ((3 : ℝ) ^ (1 / 24 * ((16 : ℕ) : ℝ))) ^ 3 = 9 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  rw [h]; norm_num

end SuperdiffusionCLT.Section6
