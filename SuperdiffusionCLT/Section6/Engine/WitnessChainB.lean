/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.WitnessChain
public import SuperdiffusionCLT.Section6.Engine.HarmonicAffineC
public import SuperdiffusionCLT.Section6.Engine.WindowFlatB
public import SuperdiffusionCLT.Section6.Engine.BlockDecayC
public import SuperdiffusionCLT.Section6.Engine.ChainB
public import SuperdiffusionCLT.Section6.Engine.Transport
public import SuperdiffusionCLT.Section6.Engine.FiniteC
public import SuperdiffusionCLT.Section6.Engine.ZeroSlope
public import SuperdiffusionCLT.Section6.Engine.LimitC
public import SuperdiffusionCLT.Section6.Engine.LiouvilleB
public import SuperdiffusionCLT.Section6.Engine.Flatness
public import SuperdiffusionCLT.Section6.Engine.RegularityB
public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace
public import SuperdiffusionCLT.Section6.Engine.WitnessScaled
public import SuperdiffusionCLT.Section6.Engine.Deterministic

/-!
# The witness chain

Every shared hypothesis block of the deterministic layer holds for the Laplace data and for the
scaled data, obtained by applying each producer, in order, to the witness.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- All shared hypothesis blocks hold for the family `V j = (1 + ε j) • engLin d`, `δ = ε`, `s = 1`
(the Laplace field), for every antitone nonnegative rate `ε` with `ε j (Hb + 1) ≤ c`; `ε = 0` is the
Laplace witness, `ε j = c / ((Hb + 1) (j + 1))` the positive-rate witness. -/
theorem ew2_blocks (d : ℕ) [NeZero d] :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∃ (Ch K C5 Cc Ct Cf Cz Cl Cfl Creg : ℝ) (C0 : ℕ),
        1 ≤ Ch ∧ 1 ≤ K ∧ 1 ≤ C5 ∧ 1 ≤ Cc ∧ 1 ≤ Ct ∧ 1 ≤ Cf ∧ 1 ≤ Cz ∧ 1 ≤ Cl ∧ 1 ≤ Cfl ∧
          1 ≤ Creg ∧
        (∀ (k l : ℕ), l + 1 ≤ k → ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d k) w gw →
          ∃ (p : Vec d) (c : ℝ),
            cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (k - l) ≤ Ch * (3 : ℝ) ^ k * cubeFlat k w ∧
              engNorm p ≤ Ch * cubeFlat k w) ∧
        ∀ γ : ℝ, 0 < γ → γ < 1 →
          ∃ (η κ c : ℝ) (Hb : ℕ), 1 / 2 ≤ η ∧ η < 1 ∧ 0 < κ ∧ κ ≤ 1 / 24 ∧ κ ≤ γ ∧
            γ + 5 * κ < η ∧ γ + 7 * κ ≤ η ∧ 0 < c ∧
            ∀ mstar : ℕ, Hb + d + 5 ≤ mstar →
              ∀ ε : ℕ → ℝ, (∀ j : ℕ, 0 ≤ ε j) → Antitone ε →
                (∀ j : ℕ, ε j * ((Hb : ℝ) + 1) ≤ c) →
                ∀ (a : CoeffField d) (δ s : ℕ → ℝ) (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
                  a = (fun _ => (1 : Mat d)) → δ = ε → (∀ j : ℕ, s j = 1) →
                  (∀ j : ℕ, V j = (1 + ε j) • engLin d) →
                  GrowthElliptic a ∧
                  (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) ∧
                  (∀ j t : ℕ, mstar ≤ j → t ≤ j → j + 2 ≤ t + Hb →
                    ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
                      ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
                        IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
                          cubeL2 (t - 3) (fun x => u x - w x) ≤ Cw * δ j * (3 : ℝ) ^ t * cubeFlat t u) ∧
                  (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) ∧
                  (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
                    cubeFlat j (fun x => V j e x - vecDot e x) ≤ Cw * δ j * engNorm e) ∧
                  (∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
                    cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤ K * δ j * engNorm e ∧
                      engNorm (affSlope k (V j e) - e) ≤ K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e) ∧
                  (∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
                    ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
                      ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
                        ∀ k : ℕ, l ≤ k → k ≤ j →
                          cubeFlat k (fun x => w x - V j e x) ≤
                            C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w) ∧
                  (∀ m k : ℕ, mstar ≤ k → k ≤ m →
                    (∀ e : Vec d, ∃ q : Vec d,
                      affSlope k (V k q) = affSlope k (V m e) ∧
                        cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
                        engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
                        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
                      ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q)) ∧
                  (∀ m j l : ℕ, mstar ≤ j → j ≤ m → l ≤ j → j ≤ l + Hb → ∀ p : Vec d,
                    ∃ pt : Vec d, engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p ∧
                      ∀ k : ℕ, l ≤ k → k ≤ j →
                        cubeFlat k (fun x => V m pt x - V j p x) ≤
                          Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p) ∧
                  (∀ m k0 : ℕ, mstar ≤ k0 → k0 ≤ m →
                    ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
                      ∃ e : Vec d, engNorm e ≤ Cf * cubeFlat m w ∧
                        ∀ k : ℕ, k0 ≤ k → k ≤ m →
                          cubeFlat k (fun x => w x - V m e x) ≤
                            Cf * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) ∧
                  (∀ n m : ℕ, mstar ≤ n → n ≤ m →
                    ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) → affSlope n w = 0 →
                      ∀ k : ℕ, n ≤ k → k ≤ m →
                        cubeFlat k w ≤ Cz * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) ∧
                  (∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
                    affSlope n (V (m + 1) e') = affSlope n (V m e) →
                    engNorm (e' - e) ≤ Cz * δ m * engNorm e ∧
                      ∀ k : ℕ, n ≤ k → k ≤ m →
                        cubeFlat k (fun x => V (m + 1) e' x - V m e x) ≤
                          Cz * δ m * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e) ∧
                  (∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d k) u g →
                    cubeGradL2 (k - 2) g ≤ Cw * Real.sqrt (s k) * cubeFlat k u) ∧
                  (∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d k) u g →
                    Real.sqrt (s k) * cubeFlat k u ≤ Cw * cubeGradL2 k g) ∧
                  (∀ k m : ℕ, mstar ≤ k → k ≤ m →
                    0 < s m ∧ s (m + 1) ≤ 2 * s m ∧ s k ≤ 1 * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * s m) ∧
                  (∃ (Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)) (GΦ : Vec d → Vec d → Vec d),
                    (∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0)) ∧
                    (∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
                      affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
                      ∀ k : ℕ, mstar ≤ k → k ≤ m →
                        cubeFlat k (fun x => Φ e0 x - V m e x) ≤
                          Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e) ∧
                    (Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ)) = 1 + d ∧
                      (∀ (c : ℝ) (e0 : Vec d),
                        ∃ hm : AEStronglyMeasurable (fun x => c + Φ e0 x) volume,
                          AEEqFun.mk (fun x => c + Φ e0 x) hm ∈ growthSpace a γ) ∧
                      ∀ φ ∈ growthSpace a γ, ∃ (c : ℝ) (e0 : Vec d),
                        (φ : Vec d → ℝ) =ᵐ[volume] fun x => c + Φ e0 x) ∧
                    (∀ φ ∈ growthSpace a γ, ∀ (k : ℕ) (r : ℝ), mstar ≤ k →
                      2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 6 * r →
                      (⨅ e : Vec d,
                          ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r)) ≤
                        ENNReal.ofReal (max Cfl Creg * δ k) * ballL2 r φ) ∧
                    (∀ R : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ R →
                      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsBallSolution a R u g →
                        ∃ φ ∈ growthSpace a γ, ∃ gφ : Vec d → Vec d,
                          IsEntireSolution a φ gφ ∧
                            ∀ r : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ r → r < R →
                              ballGradL2 r (fun x => g x - gφ x) ≤
                                ENNReal.ofReal (max Cfl Creg * (r / R) ^ γ) * ballGradL2 R g)) := by
  obtain ⟨Cw, hCw, hS⟩ := eng_witness_scaled d
  obtain ⟨-, -, hG, hE, -⟩ := eng_witness_laplace d
  obtain ⟨Ch, hCh, hF4⟩ := eng_harmonic_affine d
  obtain ⟨K, c0, N, hK, hc0, hwin⟩ := eng_window_flat d Cw Ch hCw hCh
  obtain ⟨C5, hC5, hbd⟩ := eng_block_decay d Cw Ch K hCw hCh hK
  obtain ⟨Cc, c2, H0, hCc, hc2, hch⟩ := eng_chain d K C5 hK hC5
  obtain ⟨Ct, c3, hCt, hc3, htr⟩ := eng_transport d K C5 Cc hK hC5 hCc
  obtain ⟨Cf, Cb, c4, hCf, hCb, hc4, hfn⟩ := eng_finite d K C5 Cc Ct hK hC5 hCc hCt
  obtain ⟨Cz, c5, hCz, hc5, hzs⟩ := eng_zero_slope d K Cc Cf hK hCc hCf
  obtain ⟨Cl, c6, hCl, hc6, hlm⟩ := eng_limit d Cw K Cc Cz hCw hK hCc hCz
  obtain ⟨c7, hc7, hlv⟩ := eng_liouville d Cw K Cc Cz Cl hCw hK hCc hCz hCl
  obtain ⟨Cfl, c8, hCfl, hc8, hfl⟩ := eng_flatness d Cw Cl hCw hCl
  obtain ⟨Creg, c9, C0, hCreg, hc9, hrg⟩ :=
    eng_regularity d Cw Cc Cf Cz Cl 1 hCw hCc hCf hCz hCl le_rfl
  have hK0 : 0 < K := by linarith only [hK]
  refine ⟨Cw, hCw, Ch, K, C5, Cc, Ct, Cf, Cz, Cl, Cfl, Creg, C0, hCh, hK, hC5, hCc, hCt, hCf, hCz,
    hCl, hCfl, hCreg, hF4, ?_⟩
  intro γ hγ0 hγ1
  obtain ⟨η, κ, hη1, hη2, hκ0, hκ1, hκγ, hγ5, hγ7⟩ := ew2_params γ hγ0 hγ1
  obtain ⟨hh, c1, hc1, hbk⟩ := hbd η hη1 hη2
  obtain ⟨Hb, hHbn, hHb1, hHbCb⟩ := ew2_block_length Cb κ hCb hκ0 (max (max N hh) H0)
  obtain ⟨c, hc, hcl⟩ := ew2_min_list
    [c0, c1, 1 / (2 * K), c2 * κ, c3, c4, c5, c6 * κ, c7, c8, c9, 1 / 2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        positivity)
  have ec0 := hcl c0 (by simp)
  have ec1 := hcl c1 (by simp)
  have ecK := hcl (1 / (2 * K)) (by simp)
  have ec2 := hcl (c2 * κ) (by simp)
  have ec3 := hcl c3 (by simp)
  have ec4 := hcl c4 (by simp)
  have ec5 := hcl c5 (by simp)
  have ec6 := hcl (c6 * κ) (by simp)
  have ec7 := hcl c7 (by simp)
  have ec8 := hcl c8 (by simp)
  have ec9 := hcl c9 (by simp)
  have ech := hcl (1 / 2) (by simp)
  have hN : N ≤ Hb := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hHbn
  have hhh : hh ≤ Hb := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hHbn
  have hH0 : H0 ≤ Hb := le_trans (le_max_right _ _) hHbn
  have hκ24 : κ ≤ 1 / 24 := hκ1
  have hκ1' : κ ≤ 1 := by linarith only [hκ1]
  have ec2' : c ≤ c2 := by nlinarith only [ec2, hκ1', hc2, hκ0]
  refine ⟨η, κ, c, Hb, hη1, hη2, hκ0, hκ24, hκγ, hγ5, hγ7, hc, ?_⟩
  intro mstar hmst ε hε0 hmono hεc a δ s V ha hδ hs hV
  subst a
  subst δ
  have hVf : V = fun j => (1 + ε j) • engLin d := funext hV
  subst V
  have hsf : s = fun _ => 1 := funext hs
  subst s
  have hδ0 : ∀ j : ℕ, mstar ≤ j → 0 ≤ ε j := fun j _ => hε0 j
  have hδle : ∀ ci : ℝ, c ≤ ci → ∀ j : ℕ, mstar ≤ j → ε j ≤ ci :=
    fun ci hci j hj => ew2_le_of_mul (hε0 j) (hεc j) hci
  have hε1 : ∀ j : ℕ, 0 ≤ ε j ∧ ε j ≤ 1 := fun j =>
    ⟨hε0 j, le_trans (ew2_le_of_mul (hε0 j) (hεc j) ech) (by norm_num)⟩
  have hKδ : ∀ j : ℕ, mstar ≤ j → K * ε j ≤ 1 / 2 :=
    fun j hj => ew2_K_le_half' hK (hε0 j) (hεc j) ecK
  have hmst3 : Hb + 3 ≤ mstar := by omega
  have hHA : ∀ j t : ℕ, mstar ≤ j → t ≤ j → j + 2 ≤ t + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn (fun _ => (1 : Mat d)) (engCube d t) u g →
        ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
            cubeL2 (t - 3) (fun x => u x - w x) ≤ Cw * ε j * (3 : ℝ) ^ t * cubeFlat t u := by
    intro j t hj htj hjt
    exact (hS ε hε1 j (by omega)).1 t (by omega) htj
  have hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d, ∃ g : Vec d → Vec d,
      IsSolOn (fun _ => (1 : Mat d)) (engCube d j) (((1 + ε j) • engLin d) e) g :=
    fun j hj e => ((hS ε hε1 j (by omega)).2.2 e).1
  have hVflat : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      cubeFlat j (fun x => ((1 + ε j) • engLin d) e x - vecDot e x) ≤ Cw * ε j * engNorm e :=
    fun j hj e => ((hS ε hε1 j (by omega)).2.2 e).2
  have hHC : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn (fun _ => (1 : Mat d)) (engCube d k) u g →
        cubeGradL2 (k - 2) g ≤ Cw * Real.sqrt 1 * cubeFlat k u :=
    fun k hk u g h => ((hS ε hε1 k (by omega)).2.1 u g h).1
  have hHP : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn (fun _ => (1 : Mat d)) (engCube d k) u g →
        Real.sqrt 1 * cubeFlat k u ≤ Cw * cubeGradL2 k g :=
    fun k hk u g h => ((hS ε hε1 k (by omega)).2.1 u g h).2
  have hmono' : ∀ i j : ℕ, mstar ≤ i → i ≤ j → ε j ≤ ε i := fun i j _ hij => hmono hij
  have hflat := hwin (fun _ => (1 : Mat d)) ε Hb mstar (fun j => (1 + ε j) • engLin d) hN hmst3
    (fun j hj => ⟨hε0 j, le_trans (hεc j) ec0⟩) hE hF4 hHA hVsol hVflat
  have hblock := hbk (fun _ => (1 : Mat d)) ε Hb mstar (fun j => (1 + ε j) • engLin d) hhh hmst3
    (fun j hj => ⟨hε0 j, hδle c1 ec1 j hj, ew2_K_le_half hK (hεc j) ecK⟩)
    hE hF4 hHA hVsol hflat
  have hchain := hch η κ hη1 hη2 hκ0 hκ1' (fun _ => (1 : Mat d)) ε Hb mstar
    (fun j => (1 + ε j) • engLin d) hH0 hmst3
    (fun j hj => ⟨hε0 j, le_trans (hεc j) ec2', hδle _ ec2 j hj⟩) hmono' hE hVsol hflat hblock
  have htrans := htr η κ hη1 hη2 hκ0 hκ1' (fun _ => (1 : Mat d)) ε Hb mstar
    (fun j => (1 + ε j) • engLin d) hmst3
    (fun j hj => ⟨hε0 j, le_trans (hεc j) ec3⟩) hE hVsol hflat hblock hchain
  have hfin := hfn η κ hη1 hη2 hκ0 hκ24 (fun _ => (1 : Mat d)) ε Hb mstar
    (fun j => (1 + ε j) • engLin d) hHb1 hmst3 hHbCb
    (fun j hj => ⟨hε0 j, le_trans (hεc j) ec4⟩) hE hVsol hflat hblock hchain htrans
  obtain ⟨hzd, hcons⟩ := hzs η κ hη1 hη2 hκ0 hκ24 (fun _ => (1 : Mat d)) ε Hb mstar
    (fun j => (1 + ε j) • engLin d) hHb1 hmst3
    (fun j hj => ⟨hε0 j, le_trans (hεc j) ec5⟩) hmono' hE hVsol hflat hchain hfin
  have hflat1 : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      engNorm (affSlope j (((1 + ε j) • engLin d) e) - e) ≤ K * ε j * engNorm e := by
    intro j hj e
    have := (hflat j j hj le_rfl (Nat.le_add_right _ _) e).2
    rwa [sub_self, zero_add, mul_one] at this
  have hmst3' : 3 ≤ mstar := by omega
  obtain ⟨Φ, GΦ, hΦsol, hΦlim⟩ := hlm η κ hη1 hη2 hκ0 hκ24 (fun _ => (1 : Mat d)) ε (fun _ => 1)
    mstar (fun j => (1 + ε j) • engLin d) hmst3'
    (fun j hj => ⟨hε0 j, hδle _ ec6 j hj⟩) hmono' hG hE hVsol hHC hflat1 hKδ hchain
    hcons mstar le_rfl
  have hliou := hlv η κ γ hη1 hη2 hκ0 hκ24 hγ0 hκγ hγ5 (fun _ => (1 : Mat d)) ε mstar
    (fun j => (1 + ε j) • engLin d) Φ GΦ hmst3'
    (fun j hj => ⟨hε0 j, hδle c7 ec7 j hj⟩) hG hE hVsol hVflat hflat1 hKδ hchain hzd
    hΦsol hΦlim
  have hflo := hfl η κ γ (fun _ => (1 : Mat d)) ε mstar (fun j => (1 + ε j) • engLin d) Φ
    (by omega) (fun j hj => ⟨hε0 j, hδle c8 ec8 j hj⟩) hVsol hVflat
    (fun m k hk hkm => (hchain m k hk hkm).2) hΦlim hliou.2.2
  have hVtop : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d, cubeFlat j (((1 + ε j) • engLin d) e) ≤
      Cw * engNorm e :=
    fun j hj e => ew2_top (hδle (1 / 2) ech j hj) hCw (hVsol j hj) (hVflat j hj) e
  have hreg := hrg η κ γ hη1 hη2 hκ0 hκ24 hγ0 hγ7 (fun _ => (1 : Mat d)) ε (fun _ => 1) mstar
    (fun j => (1 + ε j) • engLin d) Φ GΦ hmst3'
    (fun j hj => ⟨hε0 j, hδle c9 ec9 j hj⟩) hG hE (ew1b_hs 1 κ le_rfl hκ0 mstar) hVsol hVtop hHC
    hHP hchain hfin (fun n m hn hnm e e' h => (hcons n m hn hnm e e' h).1) hΦsol hΦlim
    (fun e0 => hliou.2.1 0 e0)
  refine ⟨hG, hE, hHA, hVsol, hVflat, hflat, hblock, hchain, htrans, hfin, hzd, hcons, hHC, hHP,
    ew1b_hs 1 κ le_rfl hκ0 mstar, Φ, GΦ, hΦsol, hΦlim, hliou, ?_, ?_⟩
  · intro φ hφ k r hk h1 h2
    exact le_trans (hflo φ hφ k r hk h1 h2)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (hε0 k))) le_rfl)
  · intro R hR u g hu
    obtain ⟨φ, hφ, gφ, hsol, hbound⟩ := hreg R hR u g hu
    refine ⟨φ, hφ, gφ, hsol, fun r hr hrR => le_trans (hbound r hr hrR) ?_⟩
    have hr0 : 0 ≤ r / R := div_nonneg (le_trans (by positivity) hr)
      (le_trans (le_trans (by positivity) hr) hrR.le)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr0 γ))) le_rfl

/-- The three conclusions, in the shape of the main statement, for the Laplace data
(`δ = 0`, `V j = engLin d`). -/
theorem ew2_laplace_frozen (d : ℕ) [NeZero d] :
    ∃ (C : ℝ) (C0 : ℕ), 1 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 →
      ∃ Hb : ℕ, ∀ mstar : ℕ, Hb + d + 5 ≤ mstar →
        Module.finrank ℝ (Submodule.span ℝ (growthSpace (fun _ : Vec d => (1 : Mat d)) γ)) = 1 + d ∧
      (∀ φ ∈ growthSpace (fun _ : Vec d => (1 : Mat d)) γ, ∀ (k : ℕ) (r : ℝ), mstar ≤ k →
        2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 6 * r →
        (⨅ e : Vec d,
            ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r)) ≤
          ENNReal.ofReal (C * 0) * ballL2 r φ) ∧
      ∀ R : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ R →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsBallSolution (fun _ : Vec d => (1 : Mat d)) R u g →
          ∃ φ ∈ growthSpace (fun _ : Vec d => (1 : Mat d)) γ, ∃ gφ : Vec d → Vec d,
            IsEntireSolution (fun _ : Vec d => (1 : Mat d)) φ gφ ∧
              ∀ r : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ r → r < R →
                ballGradL2 r (fun x => g x - gφ x) ≤
                  ENNReal.ofReal (C * (r / R) ^ γ) * ballGradL2 R g := by
  obtain ⟨Cw, hCw, Ch, K, C5, Cc, Ct, Cf, Cz, Cl, Cfl, Creg, C0, -, -, -, -, -, -, -, -, hCfl, -,
    -, hall⟩ := ew2_blocks d
  refine ⟨max Cfl Creg, C0, le_max_of_le_left hCfl, fun γ h0 h1 => ?_⟩
  obtain ⟨η, κ, c, Hb, -, -, -, -, -, -, -, hc, hmain⟩ := hall γ h0 h1
  refine ⟨Hb, fun mstar hm => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Φ, GΦ, -, -, hliou, hflo, hreg⟩ :=
    hmain mstar hm (fun _ => 0) (fun _ => le_rfl) (fun _ _ _ => le_rfl)
      (fun _ => by simpa using hc.le) (fun _ => (1 : Mat d)) (fun _ => 0) (fun _ => 1)
      (fun j => (1 + (fun _ : ℕ => (0 : ℝ)) j) • engLin d) rfl rfl (fun _ => rfl) (fun _ => rfl)
  exact ⟨hliou.1, hflo, hreg⟩

/-- The three conclusions, in the shape of the main statement, for the scaled data
(`δ j = c / ((Hb + 1) (j + 1)) > 0`, `V j = (1 + δ j) • engLin d`). -/
theorem ew2_scaled_frozen (d : ℕ) [NeZero d] :
    ∃ (C : ℝ) (C0 : ℕ), 1 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 →
      ∃ (c : ℝ) (Hb : ℕ), 0 < c ∧ ∀ mstar : ℕ, Hb + d + 5 ≤ mstar →
        (∀ j : ℕ, 0 < c / (((Hb : ℝ) + 1) * ((j : ℝ) + 1))) ∧
        Module.finrank ℝ (Submodule.span ℝ (growthSpace (fun _ : Vec d => (1 : Mat d)) γ)) = 1 + d ∧
      (∀ φ ∈ growthSpace (fun _ : Vec d => (1 : Mat d)) γ, ∀ (k : ℕ) (r : ℝ), mstar ≤ k →
        2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 6 * r →
        (⨅ e : Vec d,
            ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r)) ≤
          ENNReal.ofReal (C * (c / (((Hb : ℝ) + 1) * ((k : ℝ) + 1)))) * ballL2 r φ) ∧
      ∀ R : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ R →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsBallSolution (fun _ : Vec d => (1 : Mat d)) R u g →
          ∃ φ ∈ growthSpace (fun _ : Vec d => (1 : Mat d)) γ, ∃ gφ : Vec d → Vec d,
            IsEntireSolution (fun _ : Vec d => (1 : Mat d)) φ gφ ∧
              ∀ r : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ r → r < R →
                ballGradL2 r (fun x => g x - gφ x) ≤
                  ENNReal.ofReal (C * (r / R) ^ γ) * ballGradL2 R g := by
  obtain ⟨Cw, hCw, Ch, K, C5, Cc, Ct, Cf, Cz, Cl, Cfl, Creg, C0, -, -, -, -, -, -, -, -, hCfl, -,
    -, hall⟩ := ew2_blocks d
  refine ⟨max Cfl Creg, C0, le_max_of_le_left hCfl, fun γ h0 h1 => ?_⟩
  obtain ⟨η, κ, c, Hb, -, -, -, -, -, -, -, hc, hmain⟩ := hall γ h0 h1
  refine ⟨c, Hb, hc, fun mstar hm => ⟨fun j => by positivity, ?_⟩⟩
  have hHb : (0 : ℝ) < (Hb : ℝ) + 1 := by positivity
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Φ, GΦ, -, -, hliou, hflo, hreg⟩ :=
    hmain mstar hm (fun j => c / (((Hb : ℝ) + 1) * ((j : ℝ) + 1))) (fun j => by positivity)
      (fun i j hij => by
        have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
        have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
          have : (i : ℝ) ≤ j := by exact_mod_cast hij
          linarith only [this]
        exact div_le_div_of_nonneg_left hc.le (by positivity)
          (mul_le_mul_of_nonneg_left hij' hHb.le))
      (fun j => by
        have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
          linarith only [this]
        have : c / (((Hb : ℝ) + 1) * ((j : ℝ) + 1)) * ((Hb : ℝ) + 1) = c / ((j : ℝ) + 1) := by
          field_simp
        rw [this]
        exact div_le_self hc.le h1)
      (fun _ => (1 : Mat d)) (fun j => c / (((Hb : ℝ) + 1) * ((j : ℝ) + 1))) (fun _ => 1)
      (fun j => (1 + (fun j : ℕ => c / (((Hb : ℝ) + 1) * ((j : ℝ) + 1))) j) • engLin d)
      rfl rfl (fun _ => rfl) (fun _ => rfl)
  exact ⟨hliou.1, hflo, hreg⟩

/-- The assembly `eng_deterministic` applies to the Laplace witness (zero rate, `s = 1`), and to the
scaled witness with the positive antitone rate `min 1 (c / (Hb + 1)) / (j + 1)`. -/
example (d : ℕ) [NeZero d] :
    ∃ Cw C : ℝ, 1 ≤ Cw ∧ 1 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 →
      ∃ (κ c : ℝ) (Hb : ℕ), 0 < κ ∧ 0 < c ∧ ∀ mstar : ℕ, Hb + d + 5 ≤ mstar →
        Module.finrank ℝ (Submodule.span ℝ (growthSpace (fun _ : Vec d => (1 : Mat d)) γ)) =
          1 + d := by
  obtain ⟨Cw, hCw, hS⟩ := eng_witness_scaled d
  obtain ⟨-, -, hG, hE, -⟩ := eng_witness_laplace d
  obtain ⟨C, _, hC, hall⟩ := eng_deterministic d Cw 1 hCw le_rfl
  refine ⟨Cw, C, hCw, hC, fun γ h0 h1 => ?_⟩
  obtain ⟨κ, c, Hb, hκ, hc, hmain⟩ := hall γ h0 h1
  refine ⟨κ, c, Hb, hκ, hc, fun mstar hm => ?_⟩
  have hHb : (0 : ℝ) < (Hb : ℝ) + 1 := by positivity
  set e0 : ℝ := min 1 (c / ((Hb : ℝ) + 1)) with he0
  have he00 : 0 ≤ e0 := le_min zero_le_one (by positivity)
  have hε : ∀ j : ℕ, 0 ≤ e0 / ((j : ℝ) + 1) ∧ e0 / ((j : ℝ) + 1) ≤ 1 := by
    intro j
    have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith only [this]
    exact ⟨by positivity, le_trans (div_le_self he00 h1) (min_le_left _ _)⟩
  refine (hmain (fun _ => (1 : Mat d)) (fun j => e0 / ((j : ℝ) + 1)) (fun _ => 1) mstar hm
    (fun j _ => ⟨(hε j).1, ?_⟩) (fun i j _ hij => ?_) hG hE (ew1b_hs 1 κ le_rfl hκ _) ?_).1
  · have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith only [this]
    calc e0 / ((j : ℝ) + 1) * ((Hb : ℝ) + 1) ≤ e0 * ((Hb : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (div_le_self he00 h1) hHb.le
      _ ≤ c / ((Hb : ℝ) + 1) * ((Hb : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hHb.le
      _ = c := div_mul_cancel₀ _ hHb.ne'
  · have hi : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith only [this]
    exact div_le_div_of_nonneg_left he00 (by positivity) hi
  · intro j hj
    have hj3 : 3 ≤ j := by omega
    obtain ⟨hA, hCP, hV⟩ := hS _ hε j hj3
    exact ⟨fun t htj hj2 => hA t (by omega) htj, hCP, _, hV⟩

end SuperdiffusionCLT.Section6
