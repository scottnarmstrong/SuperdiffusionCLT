/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Chain
public import SuperdiffusionCLT.Section6.Engine.Finite
public import SuperdiffusionCLT.Section6.Engine.BlockDecayB

/-!
# Transport of a local corrected affine function to the top scale, with the block gain

Given `p`, one finds `pt` whose top-scale corrected affine function `V m pt` is close to
`V j p` on every scale `k ∈ [l, j]`, with the block decay in `k`.  The map
`e ↦ slope_l (V m e)` is linear and bounded below, hence bijective; `pt` is a preimage of the
slope of `V j p`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb5t_resid [NeZero d] {l : ℕ} {f g : Vec d → ℝ} {B : ℝ}
    (hmem : MemLp (fun x => f x - g x) 2 (normalizedCubeMeasure (originCube d (l : ℤ))))
    (h4 : affSlope l f = affSlope l g + affSlope l (fun x => f x - g x))
    (hB : cubeFlat l (fun x => f x - g x) ≤ B) :
    engNorm (affSlope l f - affSlope l g) ≤ 4 * B := by
  have e : affSlope l f - affSlope l g = affSlope l (fun x => f x - g x) := by
    rw [h4]; abel
  rw [e]
  have h := engNorm_affSlope_le hmem
  have h3 := eb5a_sqrt3_le
  have h0 := cubeFlat_nonneg (d := d) l (fun x => f x - g x)
  nlinarith only [h, h3, h0, hB]

theorem eb5t_decomp [NeZero d] {a : CoeffField d} {C5 Cc η κ δj : ℝ} {m j l : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hC5 : 0 ≤ C5) (hjm : j ≤ m) (hlj : l ≤ j)
    (hVm : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) (V m e) g)
    (hVj : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hblock : ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
      ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
        ∀ k : ℕ, l ≤ k → k ≤ j →
          cubeFlat k (fun x => w x - V j e x) ≤
            C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w)
    (hch : ∀ e : Vec d, ∃ q : Vec d,
      affSlope j (V j q) = affSlope j (V m e) ∧
        cubeFlat j (fun x => V m e x - V j q x) ≤ Cc * δj * engNorm q ∧
        engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm e ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm q)
    (pt : Vec d) :
    ∃ q r : Vec d,
      engNorm pt ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm q ∧
      engNorm (r - q) ≤ C5 * (Cc * δj * engNorm q) ∧
      (∀ k : ℕ, l ≤ k → k ≤ j →
        cubeFlat k (fun x => V m pt x - V j r x) ≤
          C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * (Cc * δj * engNorm q)) ∧
      engNorm (affSlope l (V m pt) - affSlope l (V j r)) ≤
        4 * (C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (l : ℝ)))) * (Cc * δj * engNorm q)) := by
  obtain ⟨q, -, hq1, -, hq3⟩ := hch pt
  have hsol : ∃ g : Vec d → Vec d,
      IsSolOn a (engCube d j) (fun x => V m pt x - V j q x) g :=
    eb5b_sol_sub (hell j) (eb5b_restrict (hell j) hjm (hVm pt)) (hVj q)
  obtain ⟨p', hp1, hp2⟩ := hblock _ hsol
  have hfun : (fun x => V m pt x - V j (q + p') x) =
      fun x => (V m pt x - V j q x) - V j p' x := by
    funext x
    simp only [map_add, Pi.add_apply]
    ring
  have hB : ∀ k : ℕ, l ≤ k → k ≤ j →
      cubeFlat k (fun x => V m pt x - V j (q + p') x) ≤
        C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * (Cc * δj * engNorm q) := by
    intro k hk1 hk2
    rw [hfun]
    refine (hp2 k hk1 hk2).trans ?_
    exact mul_le_mul_of_nonneg_left hq1 (by positivity)
  have hmL : MemLp (V j (q + p')) 2 (normalizedCubeMeasure (originCube d (l : ℤ))) :=
    eb5b_memLp (hell l) hlj (hVj _)
  have hmρ : MemLp (fun x => V m pt x - V j (q + p') x) 2
      (normalizedCubeMeasure (originCube d (l : ℤ))) :=
    (eb5b_memLp (hell l) (hlj.trans hjm) (hVm pt)).sub hmL
  have h4 : affSlope l (V m pt) = affSlope l (V j (q + p')) +
      affSlope l (fun x => V m pt x - V j (q + p') x) := by
    have := affSlope_add hmL hmρ
    have e : (fun x => V j (q + p') x + (V m pt x - V j (q + p') x)) = V m pt := by
      funext x; ring
    rw [e] at this
    exact this
  refine ⟨q, q + p', hq3, ?_, hB, ?_⟩
  · rw [add_sub_cancel_left]
    exact hp1.trans (mul_le_mul_of_nonneg_left hq1 hC5)
  · exact eb5t_resid hmρ h4 (hB l le_rfl hlj)

/-- **E-B5t (transport of a local corrected affine to the top scale, with the block gain)**.
Replaces `e.sharp.Cone.block.transport`. -/
theorem eng_transport (d : ℕ) [NeZero d] (K C5 Cc : ℝ) (hK : 1 ≤ K) (hC5 : 1 ≤ C5)
    (hCc : 1 ≤ Cc) :
    ∃ (Ct c3 : ℝ), 1 ≤ Ct ∧ 0 < c3 ∧
      ∀ η κ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 →
        ∀ (a : CoeffField d) (δ : ℕ → ℝ) (Hb mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
          Hb + 3 ≤ mstar →
          (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c3) →
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
          -- conclusion: htrans Ct η κ
          ∀ m j l : ℕ, mstar ≤ j → j ≤ m → l ≤ j → j ≤ l + Hb → ∀ p : Vec d,
            ∃ pt : Vec d,
              engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p ∧
                ∀ k : ℕ, l ≤ k → k ≤ j →
                  cubeFlat k (fun x => V m pt x - V j p x) ≤
                    Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p := by
  have hK0 : 0 < K := by linarith only [hK]
  have hC50 : 0 < C5 := by linarith only [hC5]
  have hCc0 : 0 < Cc := by linarith only [hCc]
  refine ⟨18 * C5 * Cc, min (1 / (2 * K)) (1 / (18 * C5 * Cc)), ?_, ?_, ?_⟩
  · nlinarith only [hC5, hCc]
  · exact lt_min (by positivity) (by positivity)
  intro η κ hη1 hη2 hκ hκ1 a δ Hb mstar V hHb hδ hell hVsol hflat hblock hchain m j l hmj hjm hlj
    hjl p
  have hη0 : 0 ≤ η := by linarith only [hη1]
  set c3 := min (1 / (2 * K)) (1 / (18 * C5 * Cc)) with hc3
  have hc3a : c3 ≤ 1 / (2 * K) := min_le_left _ _
  have hc3b : c3 ≤ 1 / (18 * C5 * Cc) := min_le_right _ _
  obtain ⟨hδ0, hδc⟩ := hδ j hmj
  have hHb1 : (1 : ℝ) ≤ (Hb : ℝ) + 1 := by
    have : (0 : ℝ) ≤ Hb := Nat.cast_nonneg Hb
    linarith only [this]
  have hδc3 : δ j ≤ c3 := by nlinarith only [hδc, hδ0, hHb1]
  have hq : (K * δ j) * ((Hb : ℝ) + 1) ≤ 1 / 2 := by
    have h1 : K * (δ j * ((Hb : ℝ) + 1)) ≤ K * c3 := mul_le_mul_of_nonneg_left hδc hK0.le
    have h2 : K * c3 ≤ K * (1 / (2 * K)) := mul_le_mul_of_nonneg_left hc3a hK0.le
    have h3 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
    nlinarith only [h1, h2, h3]
  have hs : C5 * Cc * δ j ≤ 1 / 18 := by
    have h1 : δ j ≤ 1 / (18 * C5 * Cc) := hδc3.trans hc3b
    rw [le_div_iff₀ (by positivity)] at h1
    have : C5 * Cc * δ j = δ j * (18 * C5 * Cc) / 18 := by ring
    rw [this]
    linarith only [h1]
  have hKδ0 : 0 ≤ K * δ j := mul_nonneg hK0.le hδ0
  have hVj : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g :=
    hVsol j hmj
  have hVm : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) (V m e) g :=
    hVsol m (hmj.trans hjm)
  have hVf : ∀ k : ℕ, k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      engNorm (affSlope k (V j e) - e) ≤ 1 / 2 * engNorm e ∧ cubeFlat k (V j e) ≤ engNorm e :=
    fun k hk hjk e => eb4_V_flat hKδ0 hq hVj (fun k' hk' hjk' e' => hflat j k' hmj hk' hjk' e')
      hk hjk e
  obtain ⟨P, hP⟩ := eb4_slope_linear hlj (V j) hVj
  obtain ⟨S, hS⟩ := eb4_slope_linear (hlj.trans hjm) (V m) hVm
  have hPlow : ∀ e : Vec d, 1 / 2 * engNorm e ≤ engNorm (P e) := by
    intro e
    have h1 := (hVf l hlj hjl e).1
    rw [← hP e] at h1
    have h2 := eb5a_engNorm_le_sub_add e (P e)
    rw [eb5a_engNorm_sub_comm] at h2
    linarith only [h1, h2]
  have hdec := fun pt => eb5t_decomp (Cc := Cc) (η := η) (κ := κ) (δj := δ j) hell
    hC50.le hjm hlj hVm hVj (hblock j l hmj hlj hjl) (hchain m j hmj hjm).1 pt
  have hT0 : 0 < (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have hR1 : (3 : ℝ) ^ (-(η * ((j : ℝ) - (l : ℝ)))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : (0 : ℝ) ≤ (j : ℝ) - (l : ℝ) := by
      have : (l : ℝ) ≤ j := by exact_mod_cast hlj
      linarith only [this]
    have := mul_nonneg hη0 this
    linarith only [this]
  -- the quantity W and its smallness
  have hW : ∀ q : Vec d, C5 * (Cc * δ j * engNorm q) ≤ engNorm q / 18 := by
    intro q
    have h := mul_le_mul_of_nonneg_right hs (engNorm_nonneg q)
    nlinarith only [h]
  have hRW : ∀ q : Vec d, C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (l : ℝ)))) *
      (Cc * δ j * engNorm q) ≤ C5 * (Cc * δ j * engNorm q) := by
    intro q
    have h0 : 0 ≤ C5 * (Cc * δ j * engNorm q) :=
      mul_nonneg hC50.le (mul_nonneg (mul_nonneg hCc0.le hδ0) (engNorm_nonneg q))
    have := mul_le_mul_of_nonneg_right hR1 h0
    nlinarith only [this]
  -- lower bound of S
  have hlow : ∀ e : Vec d,
      1 / (4 * Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ)))) * engNorm e ≤ engNorm (S e) := by
    intro e
    obtain ⟨q, r, h1, h2, -, h4⟩ := hdec e
    have hPr := hPlow r
    have hP' : P r = affSlope l (V j r) := hP r
    have hS' : S e = affSlope l (V m e) := hS e
    have hW1 := hW q
    have hRW1 := hRW q
    have t1 := eb5a_engNorm_le_sub_add q r
    rw [eb5a_engNorm_sub_comm] at t1
    have t2 := eb5a_engNorm_le_sub_add (P r) (S e)
    rw [eb5a_engNorm_sub_comm, hP', hS'] at t2
    rw [hP'] at hPr
    rw [hS']
    have hq4 : engNorm q / 4 ≤ engNorm (affSlope l (V m e)) := by
      linarith only [h2, h4, hW1, hRW1, hPr, t1, t2]
    have hc : 1 / (4 * Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ)))) * engNorm e ≤
        engNorm q / 4 := by
      have := mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ) ≤ 1 / (4 * Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ)))))
      refine this.trans (le_of_eq ?_)
      field_simp
    exact hc.trans hq4
  have hbij := engNorm_bijective_of_lower S (by positivity) hlow
  obtain ⟨pt, hpt⟩ := hbij.2 (P p)
  obtain ⟨q, r, h1, h2, h3, h4⟩ := hdec pt
  have hP' : P r = affSlope l (V j r) := hP r
  have hS' : S pt = affSlope l (V m pt) := hS pt
  have hW1 := hW q
  have hRW1 := hRW q
  have h5 := hPlow (r - p)
  rw [map_sub, ← hpt, hP', hS',
    eb5a_engNorm_sub_comm (affSlope l (V j r)) (affSlope l (V m pt))] at h5
  have hrp2 : engNorm (r - p) ≤ 8 * (C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (l : ℝ)))) *
      (Cc * δ j * engNorm q)) := by linarith only [h5, h4]
  have hrp : engNorm (r - p) ≤ 8 * (C5 * (Cc * δ j * engNorm q)) := by
    linarith only [hrp2, hRW1]
  have t1 := eb5a_engNorm_le_sub_add q r
  rw [eb5a_engNorm_sub_comm] at t1
  have t2 := eb5a_engNorm_le_sub_add r p
  have hq2p : engNorm q ≤ 2 * engNorm p := by linarith only [t1, t2, h2, hrp, hW1]
  refine ⟨pt, ?_, ?_⟩
  · have h6 := mul_le_mul_of_nonneg_left hq2p (by positivity :
      (0 : ℝ) ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))))
    have hnn : 0 ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p :=
      mul_nonneg (by positivity) (engNorm_nonneg p)
    nlinarith only [h1, h6, hnn, hC5]
  · intro k hk1 hk2
    have hjk : j ≤ k + Hb := by omega
    have hmk : MemLp (V m pt) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      eb5b_memLp (hell k) (hk2.trans hjm) (hVm pt)
    have hjr : MemLp (V j r) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      eb5b_memLp (hell k) hk2 (hVj r)
    have hjrp : MemLp (V j (r - p)) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      eb5b_memLp (hell k) hk2 (hVj _)
    have hfun : (fun x => V m pt x - V j p x) =
        fun x => (V m pt x - V j r x) + V j (r - p) x := by
      funext x
      simp only [map_sub, Pi.sub_apply]
      ring
    have hmρ : MemLp (fun x => V m pt x - V j r x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) := hmk.sub hjr
    rw [hfun]
    refine (cubeFlat_add_le hmρ hjrp).trans ?_
    have a1 := h3 k hk1 hk2
    have a2 := (hVf k hk2 hjk (r - p)).2
    have hRk : (3 : ℝ) ^ (-(η * ((j : ℝ) - (l : ℝ)))) ≤
        (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (l : ℝ) ≤ k := by exact_mod_cast hk1
      have := mul_le_mul_of_nonneg_left this hη0
      nlinarith only [this]
    have hN0 : 0 ≤ C5 * (Cc * δ j * engNorm q) :=
      mul_nonneg hC50.le (mul_nonneg (mul_nonneg hCc0.le hδ0) (engNorm_nonneg q))
    have a3 := mul_le_mul_of_nonneg_right hRk hN0
    have hF0 : 0 ≤ C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * (Cc * δ j) :=
      mul_nonneg (mul_nonneg hC50.le (by positivity)) (mul_nonneg hCc0.le hδ0)
    have a4 := mul_le_mul_of_nonneg_left hq2p hF0
    nlinarith only [a1, a2, a3, a4, hrp2, hRW1]

/-- The numerical hypotheses of `eng_transport` are satisfiable (with `δ = 0`). -/
example (c3 : ℝ) (hc3 : 0 < c3) (Hb : ℕ) :
    ∃ (η κ : ℝ) (δ : ℕ → ℝ) (mstar : ℕ), 1 / 2 ≤ η ∧ η < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧
      Hb + 3 ≤ mstar ∧ ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c3 :=
  ⟨1 / 2, 1, fun _ => 0, Hb + 3, le_rfl, by norm_num, by norm_num, le_rfl, le_rfl,
    fun _ _ => ⟨le_rfl, by simpa using hc3.le⟩⟩

end SuperdiffusionCLT.Section6
