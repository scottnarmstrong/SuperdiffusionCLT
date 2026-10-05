/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.DeterministicB
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

/-!
# The deterministic chain

Composition of the deterministic layer: from the one-block inputs of a coefficient field to
Liouville, flatness and large-scale `C^{1,γ}` regularity, with the dimensional constants chosen
before `γ`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The deterministic chain: from the one-block inputs of a coefficient field to
the three conclusions, with the dimensional constants `C`, `C0` chosen before `γ`. -/
theorem eng_deterministic (d : ℕ) [NeZero d] (Cin Cs : ℝ) (hCin : 1 ≤ Cin) (hCs : 1 ≤ Cs) :
    ∃ (C : ℝ) (C0 : ℕ), 1 ≤ C ∧
      ∀ γ : ℝ, 0 < γ → γ < 1 →
        ∃ (κ c : ℝ) (Hb : ℕ), 0 < κ ∧ 0 < c ∧
          ∀ (a : CoeffField d) (δ s : ℕ → ℝ) (mstar : ℕ),
            Hb + d + 5 ≤ mstar →
            (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c) →
            (∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i) →
            GrowthElliptic a →
            (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
            -- hs
            (∀ k m : ℕ, mstar ≤ k → k ≤ m →
              0 < s m ∧ s (m + 1) ≤ 2 * s m ∧
                s k ≤ Cs * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * s m) →
            -- the one-block inputs at every top scale `j ≥ mstar`
            (∀ j : ℕ, mstar ≤ j →
              (∀ t : ℕ, t ≤ j → j + 2 ≤ t + Hb →
                ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
                  ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
                    IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
                      cubeL2 (t - 3) (fun x => u x - w x) ≤
                        Cin * δ j * (3 : ℝ) ^ t * cubeFlat t u) ∧
              (∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d j) u g →
                cubeGradL2 (j - 2) g ≤ Cin * Real.sqrt (s j) * cubeFlat j u ∧
                  Real.sqrt (s j) * cubeFlat j u ≤ Cin * cubeGradL2 j g) ∧
              ∃ W : Vec d →ₗ[ℝ] (Vec d → ℝ), ∀ e : Vec d,
                (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (W e) g) ∧
                  cubeFlat j (fun x => W e x - vecDot e x) ≤ Cin * δ j * engNorm e) →
            -- conclusions
            Module.finrank ℝ (Submodule.span ℝ (growthSpace a γ)) = 1 + d ∧
              (∀ φ ∈ growthSpace a γ, ∀ (k : ℕ) (r : ℝ), mstar ≤ k →
                2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 6 * r →
                (⨅ e : Vec d,
                    ballL2 r (fun x => φ x - vecDot e x - ∫ y, φ y ∂ballMeasure r)) ≤
                  ENNReal.ofReal (C * δ k) * ballL2 r φ) ∧
              ∀ R : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ R →
                ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsBallSolution a R u g →
                  ∃ φ ∈ growthSpace a γ, ∃ gφ : Vec d → Vec d,
                    IsEntireSolution a φ gφ ∧
                      ∀ r : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ r → r < R →
                        ballGradL2 r (fun x => g x - gφ x) ≤
                          ENNReal.ofReal (C * (r / R) ^ γ) * ballGradL2 R g := by
  obtain ⟨Ch, hCh, hF4⟩ := eng_harmonic_affine d
  obtain ⟨K, c0, N, hK, hc0, hwin⟩ := eng_window_flat d Cin Ch hCin hCh
  obtain ⟨C5, hC5, hbd⟩ := eng_block_decay d Cin Ch K hCin hCh hK
  obtain ⟨Cc, c2, H0, hCc, hc2, hch⟩ := eng_chain d K C5 hK hC5
  obtain ⟨Ct, c3, hCt, hc3, htr⟩ := eng_transport d K C5 Cc hK hC5 hCc
  obtain ⟨Cf, Cb, c4, hCf, hCb, hc4, hfn⟩ := eng_finite d K C5 Cc Ct hK hC5 hCc hCt
  obtain ⟨Cz, c5, hCz, hc5, hzs⟩ := eng_zero_slope d K Cc Cf hK hCc hCf
  obtain ⟨Cl, c6, hCl, hc6, hlm⟩ := eng_limit d Cin K Cc Cz hCin hK hCc hCz
  obtain ⟨c7, hc7, hlv⟩ := eng_liouville d Cin K Cc Cz Cl hCin hK hCc hCz hCl
  obtain ⟨Cfl, c8, hCfl, hc8, hfl⟩ := eng_flatness d Cin Cl hCin hCl
  obtain ⟨Creg, c9, C0, hCreg, hc9, hrg⟩ :=
    eng_regularity d Cin Cc Cf Cz Cl Cs hCin hCc hCf hCz hCl hCs
  have hK0 : 0 < K := by linarith only [hK]
  refine ⟨max Cfl Creg, C0, le_max_of_le_left hCfl, ?_⟩
  intro γ hγ0 hγ1
  obtain ⟨η, κ, hη1, hη2, hκ0, hκ1, hκγ, hγ5, hγ7⟩ := ec5_params γ hγ0 hγ1
  obtain ⟨hh, c1, hc1, hbk⟩ := hbd η hη1 hη2
  obtain ⟨Hb, hHbn, hHb1, hHbCb⟩ := ec5_block_length Cb κ hCb hκ0 (max (max N hh) H0)
  obtain ⟨c, hc, hcl⟩ := ec5_min_list
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
  refine ⟨κ, c, Hb, hκ0, hc, ?_⟩
  intro a δ s mstar hmst hδ hmono hGE hell hs hone
  have hex : ∀ j : ℕ, ∃ W : Vec d →ₗ[ℝ] (Vec d → ℝ), mstar ≤ j → ∀ e : Vec d,
      (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (W e) g) ∧
        cubeFlat j (fun x => W e x - vecDot e x) ≤ Cin * δ j * engNorm e := by
    intro j
    by_cases hj : mstar ≤ j
    · obtain ⟨W, hW⟩ := (hone j hj).2.2
      exact ⟨W, fun _ => hW⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose V hV using hex
  have hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g :=
    fun j hj e => (hV j hj e).1
  have hVflat : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      cubeFlat j (fun x => V j e x - vecDot e x) ≤ Cin * δ j * engNorm e :=
    fun j hj e => (hV j hj e).2
  have hHA : ∀ j t : ℕ, mstar ≤ j → t ≤ j → j + 2 ≤ t + Hb →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
        ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
            cubeL2 (t - 3) (fun x => u x - w x) ≤
              Cin * δ j * (3 : ℝ) ^ t * cubeFlat t u :=
    fun j t hj => (hone j hj).1 t
  have hHC : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn a (engCube d k) u g →
        cubeGradL2 (k - 2) g ≤ Cin * Real.sqrt (s k) * cubeFlat k u :=
    fun k hk u g h => ((hone k hk).2.1 u g h).1
  have hHP : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn a (engCube d k) u g →
        Real.sqrt (s k) * cubeFlat k u ≤ Cin * cubeGradL2 k g :=
    fun k hk u g h => ((hone k hk).2.1 u g h).2
  have hδ0 : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j := fun j hj => (hδ j hj).1
  have hδc : ∀ j : ℕ, mstar ≤ j → δ j * ((Hb : ℝ) + 1) ≤ c := fun j hj => (hδ j hj).2
  have hδle : ∀ ci : ℝ, c ≤ ci → ∀ j : ℕ, mstar ≤ j → δ j ≤ ci :=
    fun ci hci j hj => ec5_le_of_mul (hδ0 j hj) (hδc j hj) hci
  have hKδ : ∀ j : ℕ, mstar ≤ j → K * δ j ≤ 1 / 2 :=
    fun j hj => ec5_K_le_half' hK (hδ0 j hj) (hδc j hj) ecK
  have hmst3 : Hb + 3 ≤ mstar := by omega
  have hflat := hwin a δ Hb mstar V hN hmst3
    (fun j hj => ⟨hδ0 j hj, le_trans (hδc j hj) ec0⟩) hell hF4 hHA hVsol hVflat
  have hblock := hbk a δ Hb mstar V hhh hmst3
    (fun j hj => ⟨hδ0 j hj, hδle c1 ec1 j hj, ec5_K_le_half hK (hδc j hj) ecK⟩)
    hell hF4 hHA hVsol hflat
  have hchain := hch η κ hη1 hη2 hκ0 hκ1' a δ Hb mstar V hH0 hmst3
    (fun j hj => ⟨hδ0 j hj, le_trans (hδc j hj) ec2', hδle _ ec2 j hj⟩) hmono hell hVsol
    hflat hblock
  have htrans := htr η κ hη1 hη2 hκ0 hκ1' a δ Hb mstar V hmst3
    (fun j hj => ⟨hδ0 j hj, le_trans (hδc j hj) ec3⟩) hell hVsol hflat hblock hchain
  have hfin := hfn η κ hη1 hη2 hκ0 hκ24 a δ Hb mstar V hHb1 hmst3 hHbCb
    (fun j hj => ⟨hδ0 j hj, le_trans (hδc j hj) ec4⟩) hell hVsol hflat hblock hchain htrans
  obtain ⟨hzd, hcons⟩ := hzs η κ hη1 hη2 hκ0 hκ24 a δ Hb mstar V hHb1 hmst3
    (fun j hj => ⟨hδ0 j hj, le_trans (hδc j hj) ec5⟩) hmono hell hVsol hflat hchain hfin
  have hflat1 : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      engNorm (affSlope j (V j e) - e) ≤ K * δ j * engNorm e := by
    intro j hj e
    have := (hflat j j hj le_rfl (Nat.le_add_right _ _) e).2
    rwa [sub_self, zero_add, mul_one] at this
  have hmst3' : 3 ≤ mstar := by omega
  obtain ⟨Φ, GΦ, hΦsol, hΦlim⟩ := hlm η κ hη1 hη2 hκ0 hκ24 a δ s mstar V hmst3'
    (fun j hj => ⟨hδ0 j hj, hδle _ ec6 j hj⟩) hmono hGE hell hVsol hHC hflat1 hKδ hchain
    hcons mstar le_rfl
  have hliou := hlv η κ γ hη1 hη2 hκ0 hκ24 hγ0 hκγ hγ5 a δ mstar V Φ GΦ hmst3'
    (fun j hj => ⟨hδ0 j hj, hδle c7 ec7 j hj⟩) hGE hell hVsol hVflat hflat1 hKδ hchain hzd
    hΦsol hΦlim
  have hflo := hfl η κ γ a δ mstar V Φ (by omega)
    (fun j hj => ⟨hδ0 j hj, hδle c8 ec8 j hj⟩) hVsol hVflat (fun m k hk hkm => (hchain m k hk hkm).2)
    hΦlim hliou.2.2
  have hVtop : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d, cubeFlat j (V j e) ≤ Cin * engNorm e :=
    fun j hj e => ec5_top (hδle (1 / 2) ech j hj) hCin (hVsol j hj) (hVflat j hj) e
  have hreg := hrg η κ γ hη1 hη2 hκ0 hκ24 hγ0 hγ7 a δ s mstar V Φ GΦ hmst3'
    (fun j hj => ⟨hδ0 j hj, hδle c9 ec9 j hj⟩) hGE hell hs hVsol hVtop hHC hHP hchain hfin
    (fun n m hn hnm e e' h => (hcons n m hn hnm e e' h).1) hΦsol hΦlim
    (fun e0 => hliou.2.1 0 e0)
  refine ⟨hliou.1, ?_, ?_⟩
  · intro φ hφ k r hk h1 h2
    exact le_trans (hflo φ hφ k r hk h1 h2)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (hδ0 k hk))) le_rfl)
  · intro R hR u g hu
    obtain ⟨φ, hφ, gφ, hsol, hbound⟩ := hreg R hR u g hu
    refine ⟨φ, hφ, gφ, hsol, fun r hr hrR => le_trans (hbound r hr hrR) ?_⟩
    have hr0 : 0 ≤ r / R := div_nonneg (le_trans (by positivity) hr)
      (le_trans (le_trans (by positivity) hr) hrR.le)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr0 γ))) le_rfl

/-- The hypotheses of `eng_deterministic` are satisfied by the Laplace data (zero rate, `s = 1`,
`V j = engLin d`), so its conclusion holds for the Laplace field. -/
example (d : ℕ) [NeZero d] :
    ∃ Cw C : ℝ, 1 ≤ Cw ∧ 1 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 →
      ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
        Module.finrank ℝ (Submodule.span ℝ (growthSpace (fun _ : Vec d => (1 : Mat d)) γ)) =
          1 + d := by
  obtain ⟨Cw, hCw, hG, hE, h⟩ := eng_witness_laplace d
  obtain ⟨C, _, hC, hall⟩ := eng_deterministic d Cw 1 hCw le_rfl
  refine ⟨Cw, C, hCw, hC, fun γ h0 h1 => ?_⟩
  obtain ⟨κ, c, Hb, hκ, hc, hmain⟩ := hall γ h0 h1
  refine ⟨κ, c, hκ, hc, (hmain (fun _ => (1 : Mat d)) (fun _ => 0) (fun _ => 1)
    (Hb + d + 5) le_rfl (fun j _ => ⟨le_rfl, by simpa using hc.le⟩)
    (fun i j _ _ => le_rfl) hG hE (ew1b_hs 1 κ le_rfl hκ _) ?_).1⟩
  intro j hj
  have hj3 : 3 ≤ j := by omega
  obtain ⟨hA, hCP, hV⟩ := h j hj3
  exact ⟨fun t htj hj2 => hA t (by omega) htj, hCP, engLin d, hV⟩

/-- The same with a nonzero constant rate `ε = min 1 (c / (Hb + 1))` and
`V j = (1 + ε) • engLin d`. -/
example (d : ℕ) [NeZero d] :
    ∃ Cw C : ℝ, 1 ≤ Cw ∧ 1 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 →
      ∃ κ c : ℝ, 0 < κ ∧ 0 < c ∧
        Module.finrank ℝ (Submodule.span ℝ (growthSpace (fun _ : Vec d => (1 : Mat d)) γ)) =
          1 + d := by
  obtain ⟨Cw, hCw, hS⟩ := eng_witness_scaled d
  obtain ⟨-, -, hG, hE, -⟩ := eng_witness_laplace d
  obtain ⟨C, _, hC, hall⟩ := eng_deterministic d Cw 1 hCw le_rfl
  refine ⟨Cw, C, hCw, hC, fun γ h0 h1 => ?_⟩
  obtain ⟨κ, c, Hb, hκ, hc, hmain⟩ := hall γ h0 h1
  have hHb : (0 : ℝ) < (Hb : ℝ) + 1 := by positivity
  have hε : ∀ j : ℕ, 0 ≤ min 1 (c / ((Hb : ℝ) + 1)) ∧ min 1 (c / ((Hb : ℝ) + 1)) ≤ 1 :=
    fun _ => ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  refine ⟨κ, c, hκ, hc, (hmain (fun _ => (1 : Mat d)) (fun _ => min 1 (c / ((Hb : ℝ) + 1)))
    (fun _ => 1) (Hb + d + 5) le_rfl (fun j _ => ⟨(hε j).1, ?_⟩)
    (fun i j _ _ => le_rfl) hG hE (ew1b_hs 1 κ le_rfl hκ _) ?_).1⟩
  · calc min 1 (c / ((Hb : ℝ) + 1)) * ((Hb : ℝ) + 1) ≤ c / ((Hb : ℝ) + 1) * ((Hb : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hHb.le
      _ = c := div_mul_cancel₀ _ hHb.ne'
  intro j hj
  have hj3 : 3 ≤ j := by omega
  obtain ⟨hA, hCP, hV⟩ := hS _ hε j hj3
  exact ⟨fun t htj hj2 => hA t (by omega) htj, hCP, (1 + min 1 (c / ((Hb : ℝ) + 1))) • engLin d, hV⟩

end SuperdiffusionCLT.Section6
