/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.ZeroSlopeB
public import SuperdiffusionCLT.Section6.Engine.Solutions

/-!
# Zero bottom slope forces decay; consecutive scales

From the one-block estimates of the regularity iteration: a solution whose slope at the bottom
scale vanishes decays towards the bottom scale, and the bottom-anchored identification of the
scale-`m` and scale-`m+1` families is stable.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb6a_engCube_mono {a b : ℕ} (h : a ≤ b) : engCube d a ⊆ engCube d b := by
  intro y hy
  have hy' := mem_openCubeSet_originCube_iff.1 hy
  show y ∈ openCubeSet (originCube d (b : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := hy' i
  have hle : (3 : ℝ) ^ (a : ℤ) ≤ (3 : ℝ) ^ (b : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) h
  constructor <;> linarith only [hi.1, hi.2, hle]

/-- **E-B6a (zero bottom slope forces decay; consecutive scales)**. Replaces
`e.sharp.Cone.consecutive`, `e.sharp.Cone.T.close`, `e.sharp.Cone.T.inverse.close`. -/
theorem eng_zero_slope (d : ℕ) [NeZero d] (K Cc Cf : ℝ) (hK : 1 ≤ K) (hCc : 1 ≤ Cc)
    (hCf : 1 ≤ Cf) :
    ∃ (Cz c5 : ℝ), 1 ≤ Cz ∧ 0 < c5 ∧
      ∀ η κ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 / 24 →
        ∀ (a : CoeffField d) (δ : ℕ → ℝ) (Hb mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
          1 ≤ Hb → Hb + 3 ≤ mstar →
          (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c5) →
          (∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i) →
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
          -- hchain Cc κ
          (∀ m k : ℕ, mstar ≤ k → k ≤ m →
            (∀ e : Vec d, ∃ q : Vec d,
              affSlope k (V k q) = affSlope k (V m e) ∧
                cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
                engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
                engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
              ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q)) →
          -- hfin Cf (η - 3κ)
          (∀ m k0 : ℕ, mstar ≤ k0 → k0 ≤ m →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
              ∃ e : Vec d, engNorm e ≤ Cf * cubeFlat m w ∧
                ∀ k : ℕ, k0 ≤ k → k ≤ m →
                  cubeFlat k (fun x => w x - V m e x) ≤
                    Cf * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) →
          -- conclusion: hzd Cz (η - 5κ)
          (∀ n m : ℕ, mstar ≤ n → n ≤ m →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
              affSlope n w = 0 →
              ∀ k : ℕ, n ≤ k → k ≤ m →
                cubeFlat k w ≤
                  Cz * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) ∧
          -- conclusion: hcons Cz (η - 5κ)
          (∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
            affSlope n (V (m + 1) e') = affSlope n (V m e) →
            engNorm (e' - e) ≤ Cz * δ m * engNorm e ∧
              ∀ k : ℕ, n ≤ k → k ≤ m →
                cubeFlat k (fun x => V (m + 1) e' x - V m e x) ≤
                  Cz * δ m * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) *
                    engNorm e) := by
  have hCf0 : 0 ≤ Cf := by linarith only [hCf]
  have hCc0 : 0 ≤ Cc := by linarith only [hCc]
  have hK0 : 0 ≤ K := by linarith only [hK]
  obtain ⟨C2, hC2⟩ : ∃ C2 : ℝ, C2 = Cf * Cc * (8 * Cc + 1) := ⟨_, rfl⟩
  have hC20 : 0 ≤ C2 := by rw [hC2]; positivity
  obtain ⟨C3, hC3⟩ : ∃ C3 : ℝ, C3 = K * (2 + 12 * Cc) + 2 * C2 := ⟨_, rfl⟩
  have hC30 : 0 ≤ C3 := by rw [hC3]; positivity
  obtain ⟨Cz, hCz⟩ : ∃ Cz : ℝ, Cz = 1 + (16 * Cc ^ 2 + 1) * Cf * (2 * Cc + 1) + C3 := ⟨_, rfl⟩
  have hZ0 : 0 ≤ (16 * Cc ^ 2 + 1) * Cf * (2 * Cc + 1) := by positivity
  have hTpos : 0 < K + Cc + C2 := by linarith only [hK, hCc, hC20]
  obtain ⟨c5, hc5⟩ : ∃ c5 : ℝ, c5 = 1 / (4 * (K + Cc + C2)) := ⟨_, rfl⟩
  have hc5pos : 0 < c5 := by rw [hc5]; positivity
  have hTc : (K + Cc + C2) * c5 = 1 / 4 := by rw [hc5]; field_simp
  refine ⟨Cz, c5, by linarith only [hCz, hZ0, hC30], hc5pos, ?_⟩
  intro η κ hη1 hη2 hκ0 hκ1 a δ Hb mstar V hHb hm hsm hanti hell hVsol hflat hchain hfin
  have hVmem : ∀ j, mstar ≤ j → ∀ e : Vec d,
      MemLp (V j e) 2 (normalizedCubeMeasure (originCube d (j : ℤ))) := by
    intro j hj e
    obtain ⟨g, hg⟩ := hVsol j hj e
    exact hg.memLp.1
  have hδ : ∀ j, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c5 := by
    intro j hj
    obtain ⟨h0, h1⟩ := hsm j hj
    have hHb' : (2 : ℝ) ≤ (Hb : ℝ) + 1 := by
      have : (1 : ℝ) ≤ Hb := Nat.one_le_cast.2 hHb
      linarith only [this]
    exact ⟨h0, by nlinarith only [h0, h1, hHb', hc5pos, mul_nonneg h0 (sub_nonneg.2 hHb')]⟩
  have hbound : ∀ X : ℝ, 0 ≤ X → X ≤ K + Cc + C2 → ∀ j, mstar ≤ j → X * δ j ≤ 1 / 4 := by
    intro X hX hXT j hj
    have h1 := mul_le_mul_of_nonneg_left (hδ j hj).2 hX
    have h2 := mul_le_mul_of_nonneg_right hXT hc5pos.le
    linarith only [h1, h2, hTc]
  have hsm' : ∀ j, mstar ≤ j → 0 ≤ δ j ∧ K * δ j ≤ 1 / 4 ∧ Cc * δ j ≤ 1 := by
    intro j hj
    exact ⟨(hδ j hj).1, hbound K hK0 (by linarith only [hCc, hC20]) j hj,
      by linarith only [hbound Cc hCc0 (by linarith only [hK, hC20]) j hj]⟩
  have hflat0 : ∀ k, mstar ≤ k → ∀ e : Vec d,
      cubeFlat k (fun x => V k e x - vecDot (affSlope k (V k e)) x) ≤ K * δ k * engNorm e ∧
        engNorm (affSlope k (V k e) - e) ≤ K * δ k * engNorm e := by
    intro k hk e
    obtain ⟨h1, h2⟩ := hflat k k hk le_rfl (Nat.le_add_right k Hb) e
    refine ⟨h1, ?_⟩
    rw [sub_self, zero_add, mul_one] at h2
    exact h2
  have hch0 : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ e : Vec d, ∃ q : Vec d,
      affSlope k (V k q) = affSlope k (V m e) ∧
        cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
        engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q :=
    fun m k h1 h2 e => (hchain m k h1 h2).1 e
  have hCzle : (16 * Cc ^ 2 + 1) * Cf ≤ Cz := by
    have : 0 ≤ (16 * Cc ^ 2 + 1) * Cf * Cc := by positivity
    nlinarith only [hCz, hC30, this]
  refine ⟨?_, ?_⟩
  · intro n m hn hnm w hw hs k hnk hkm
    obtain ⟨e, he1, he2⟩ := hfin m n hn hnm w hw
    have hwm : MemLp w 2 (normalizedCubeMeasure (originCube d (m : ℤ))) := by
      obtain ⟨g, hg⟩ := hw
      exact hg.memLp.1
    have hRm : MemLp (fun x => w x - V m e x) 2
        (normalizedCubeMeasure (originCube d (m : ℤ))) := hwm.sub (hVmem m (le_trans hn hnm) e)
    have hfun : (fun x => V m e x + (w x - V m e x)) = w := by
      funext x
      ring
    have hs' : affSlope n (fun x => V m e x + (w x - V m e x)) = 0 := by
      rw [hfun]
      exact hs
    obtain ⟨_, hk2⟩ := eb6a_key K Cc hCc hη1 hκ0 hκ1 δ mstar V hsm' hVmem hflat0 hch0 hn hnm e
      (fun x => w x - V m e x) (Cf * cubeFlat m w) hRm
      (fun k h1 h2 => le_of_le_of_eq (he2 k h1 h2) (by ring)) hs'
    have h := hk2 k hnk hkm
    rw [hfun] at h
    have hE : 0 ≤ (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) :=
      Real.rpow_nonneg (by norm_num) _
    have hΩ := cubeFlat_nonneg m w
    have hX := mul_le_mul_of_nonneg_right hCzle (mul_nonneg hE hΩ)
    linarith only [h, hX]
  · intro n m hn hnm e e' hs
    have hmstar : mstar ≤ m := le_trans hn hnm
    obtain ⟨q, hq1, hq2, hq3, hq4⟩ := hch0 (m + 1) m hmstar (Nat.le_succ m) e'
    have hρ : ∃ g : Vec d → Vec d,
        IsSolOn a (engCube d m) (fun x => V (m + 1) e' x - V m q x) g := by
      obtain ⟨g1, h1⟩ := hVsol (m + 1) (by omega) e'
      obtain ⟨g2, h2⟩ := hVsol m hmstar q
      have h1' := IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _)
        (eb6a_engCube_mono (Nat.le_succ m)) (volume_openCubeSet_lt_top _).ne (hell m) h1
      exact ⟨_, IsSolOn.sub (hell m) h1' h2⟩
    obtain ⟨eρ, hρ1, hρ2⟩ := hfin m n hn hnm _ hρ
    have hρm : MemLp (fun x => V (m + 1) e' x - V m q x) 2
        (normalizedCubeMeasure (originCube d (m : ℤ))) := by
      obtain ⟨g, hg⟩ := hρ
      exact hg.memLp.1
    have hRm : MemLp (fun x => (V (m + 1) e' x - V m q x) - V m eρ x) 2
        (normalizedCubeMeasure (originCube d (m : ℤ))) := hρm.sub (hVmem m hmstar eρ)
    have hfun : (fun x => V m (q + eρ - e) x + ((V (m + 1) e' x - V m q x) - V m eρ x)) =
        fun x => V (m + 1) e' x - V m e x := by
      funext x
      simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
      ring
    have hs' : affSlope n (fun x => V m (q + eρ - e) x +
        ((V (m + 1) e' x - V m q x) - V m eρ x)) = 0 := by
      rw [hfun, eb6a_slope_sub (eb6a_memLp_mono (le_trans hnm (Nat.le_succ m))
        (hVmem (m + 1) (by omega) e')) (eb6a_memLp_mono hnm (hVmem m hmstar e)), hs]
      exact sub_self _
    obtain ⟨hf8, hk2⟩ := eb6a_key K Cc hCc hη1 hκ0 hκ1 δ mstar V hsm' hVmem hflat0 hch0 hn hnm
      (q + eρ - e) (fun x => (V (m + 1) e' x - V m q x) - V m eρ x)
      (Cf * cubeFlat m (fun x => V (m + 1) e' x - V m q x)) hRm
      (fun k h1 h2 => le_of_le_of_eq (hρ2 k h1 h2) (by ring)) hs'
    obtain ⟨hδ0, hδc⟩ := hδ m hmstar
    have hq0 := engNorm_nonneg q
    have he0 := engNorm_nonneg e
    have hY : Cf * cubeFlat m (fun x => V (m + 1) e' x - V m q x) ≤ Cf * (Cc * δ m * engNorm q) :=
      mul_le_mul_of_nonneg_left hq2 hCf0
    have hY0 : 0 ≤ Cf * (Cc * δ m * engNorm q) := by positivity
    -- `|q - e| ≤ C2 δ_m |q|`
    have hqe : engNorm (q - e) ≤ C2 * δ m * engNorm q := by
      have h1 : engNorm (q - e) ≤ engNorm (q + eρ - e) + engNorm eρ := by
        have := eb6a_engNorm_sub_le (q + eρ - e) eρ
        rwa [show q + eρ - e - eρ = q - e by abel] at this
      have h2 := mul_le_mul_of_nonneg_left hY (by linarith only [hCc] : (0 : ℝ) ≤ 8 * Cc + 1)
      have h3 : C2 * δ m * engNorm q = (8 * Cc + 1) * (Cf * (Cc * δ m * engNorm q)) := by
        rw [hC2]
        ring
      rw [h3]
      linarith only [h1, h2, hf8, hρ1, hY]
    have hC2d : C2 * δ m ≤ 1 / 4 := hbound C2 hC20 (by linarith only [hK, hCc]) m hmstar
    have hqe2 : engNorm q ≤ 2 * engNorm e := by
      have h1 := eb6a_norm_le_add' q e
      have h2 : C2 * δ m * engNorm q ≤ 1 / 4 * engNorm q := by nlinarith only [hC2d, hq0]
      linarith only [h1, h2, hqe, he0, hq0]
    have h3 : (3 : ℝ) ^ (κ * (((m + 1 : ℕ) : ℝ) - (m : ℝ))) ≤ 3 := by
      have : κ * (((m + 1 : ℕ) : ℝ) - (m : ℝ)) = κ := by
        push_cast
        ring
      rw [this]
      calc (3 : ℝ) ^ κ ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hκ1])
        _ = 3 := Real.rpow_one 3
    have he' : engNorm e' ≤ 3 * Cc * engNorm q := by
      have := mul_le_mul_of_nonneg_right h3 (mul_nonneg hCc0 hq0)
      linarith only [hq4, this]
    obtain ⟨_, hfl2⟩ := hflat (m + 1) m (by omega) (Nat.le_succ m) (by omega) e'
    have hcast : ((m + 1 : ℕ) : ℝ) - (m : ℝ) + 1 = 2 := by
      push_cast
      ring
    rw [hcast] at hfl2
    have hfl1 := (hflat0 m hmstar q).2
    rw [hq1] at hfl1
    have hanti' : K * δ (m + 1) ≤ K * δ m :=
      mul_le_mul_of_nonneg_left (hanti m (m + 1) hmstar (Nat.le_succ m)) hK0
    have hKδ0 : 0 ≤ K * δ m := mul_nonneg hK0 hδ0
    have he'q : engNorm (e' - q) ≤ (2 + 12 * Cc) * (K * δ m) * engNorm e := by
      have h1 := eb6a_tri e' (affSlope m (V (m + 1) e')) q
      rw [eb6a_engNorm_sub_comm e' (affSlope m (V (m + 1) e'))] at h1
      have h2 : K * δ (m + 1) * (2 * engNorm e') ≤ K * δ m * (2 * (3 * Cc * engNorm q)) :=
        mul_le_mul hanti' (by linarith only [he']) (by linarith only [engNorm_nonneg e']) hKδ0
      have h4 := mul_le_mul_of_nonneg_left hqe2 (mul_nonneg hKδ0 (by linarith only [hCc] :
        (0 : ℝ) ≤ 6 * Cc + 1))
      have h5 : K * δ (m + 1) * (2 * engNorm e') = K * δ (m + 1) * 2 * engNorm e' := by ring
      have h6 : K * δ m * engNorm q ≤ K * δ m * engNorm q := le_rfl
      nlinarith only [h1, hfl2, hfl1, h2, h4, h5, h6]
    have hee : engNorm (e' - e) ≤ C3 * δ m * engNorm e := by
      have h1 := eb6a_tri e' q e
      have h2 : C2 * δ m * engNorm q ≤ C2 * δ m * (2 * engNorm e) :=
        mul_le_mul_of_nonneg_left hqe2 (mul_nonneg hC20 hδ0)
      have h3 : C3 * δ m * engNorm e = (2 + 12 * Cc) * (K * δ m) * engNorm e +
          C2 * δ m * (2 * engNorm e) := by
        rw [hC3]
        ring
      rw [h3]
      linarith only [h1, h2, hqe, he'q]
    have hC3z : C3 ≤ Cz := by linarith only [hCz, hZ0]
    have hCzz : 2 * ((16 * Cc ^ 2 + 1) * Cf * Cc) ≤ Cz := by
      have : 0 ≤ (16 * Cc ^ 2 + 1) * Cf := by positivity
      nlinarith only [hCz, hC30, this, hCc]
    refine ⟨?_, ?_⟩
    · exact hee.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC3z hδ0) he0)
    · intro k hk hkm
      have h := hk2 k hk hkm
      rw [hfun] at h
      have hE : 0 ≤ (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) :=
        Real.rpow_nonneg (by norm_num) _
      have hZ : 0 ≤ 16 * Cc ^ 2 + 1 := by positivity
      have hB' : Cf * cubeFlat m (fun x => V (m + 1) e' x - V m q x) ≤
          Cf * (Cc * δ m * (2 * engNorm e)) :=
        hY.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hqe2 (mul_nonneg hCc0 hδ0)) hCf0)
      have h1 := mul_le_mul_of_nonneg_left hB'
        (mul_nonneg hZ hE : 0 ≤ (16 * Cc ^ 2 + 1) *
          (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))))
      have h2 := mul_le_mul_of_nonneg_right hCzz (mul_nonneg (mul_nonneg hδ0 hE) he0)
      linarith only [h, h1, h2]

/-- Witness for the numerical hypotheses: `η = 1/2`, `κ = 1/24`, `δ = 0`, `Hb = 1`, `mstar = 4`. -/
example (c5 : ℝ) (hc5 : 0 < c5) :
    (1 : ℝ) / 2 ≤ 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧ (0 : ℝ) < 1 / 24 ∧ (1 : ℝ) / 24 ≤ 1 / 24 ∧
      1 ≤ 1 ∧ 1 + 3 ≤ 4 ∧
      (∀ j : ℕ, 4 ≤ j → 0 ≤ (fun _ : ℕ => (0 : ℝ)) j ∧
        (fun _ : ℕ => (0 : ℝ)) j * (((1 : ℕ) : ℝ) + 1) ≤ c5) ∧
      (∀ i j : ℕ, 4 ≤ i → i ≤ j → (fun _ : ℕ => (0 : ℝ)) j ≤ (fun _ : ℕ => (0 : ℝ)) i) :=
  ⟨le_rfl, by norm_num, by norm_num, le_rfl, le_rfl, by norm_num,
    fun _ _ => ⟨le_rfl, by simpa using hc5.le⟩, fun _ _ _ _ => le_rfl⟩

end SuperdiffusionCLT.Section6
