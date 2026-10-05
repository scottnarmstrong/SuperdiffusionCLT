/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD2
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyC
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyC2

/-!
# Near-scale assembly: the probabilistic packaging

`srootNSD_assemble` is the field-free version of the probabilistic step of `hNear`: given the
witnesses of the local base (`Γ₁` part `X1`, `Γ_{1/3}` part `X2`, per cutoff, depth and cube), the
tail witnesses, the skew-average variable `W`, and the crude `Γ_{1/2}` cap `G`, there are `Y1`
(`Γ₁`) and `Y2` (`Γ_{1/3}`) with
`Σ_l w_l Mx_l ≤ DET + Y1 + Y2` almost surely, for every cutoff `L ≥ a`.

The `Γ₁` family is collected by one centered maximum over `(L, R)` for each depth
(`srootNS_gamma1_collect`); the `Γ_{1/3}` families by finite domination
(`srootNS_gamma_dominate`); the product term is capped (`srootNS_cap_final`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Homogenization.IndependentSums

noncomputable section

theorem srootNSD_gammaTriangleConst_pos (σ : ℝ) : 0 < gammaTriangleConst σ := by
  have hg : (2 : ℝ) ≤ gammaGrowthConst σ := le_max_left _ _
  have hpos : (0 : ℝ) < gammaGrowthConst σ := by linarith only [hg]
  simp only [gammaTriangleConst]
  positivity

/-- A nonnegative constant `c` is `O_{Γ_σ}(c)`. -/
theorem srootNSD_isBigO_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ c : ℝ}
    (hc : 0 ≤ c) :
    IsBigO μ (gammaSigma σ) (fun _ : Ω => c) c := by
  intro t ht
  have h1 : upperTailEvent (fun _ : Ω => |c|) (c * t) = ∅ := by
    ext ω
    simp only [mem_upperTailEvent, abs_of_nonneg hc, Set.mem_empty_iff_false, iff_false, not_lt]
    nlinarith only [ht, hc]
  rw [h1]
  simp only [measureReal_empty]
  exact inv_nonneg.2 (le_trans zero_le_one (one_le_gammaSigma (le_trans zero_le_one ht)))

/-- `c + b W` is `O_{Γ₁}(g (c + b A))`: the constant shift of a `Γ₁` variable. -/
theorem srootNSD_isBigO_affine {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {W : Ω → ℝ} {c b AW : ℝ} (hc : 0 < c) (hb : 0 < b) (hAW : 0 < AW)
    (hWm : Measurable W) (hW : IsBigO μ (gammaSigma 1) W AW) :
    IsBigO μ (gammaSigma 1) (fun ω => c + b * W ω)
      (gammaTriangleConst 1 * (c + b * AW)) :=
  SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO one_pos hc
    (mul_pos hb hAW) (srootNSD_isBigO_const hc.le) (hW.const_mul hb.le)
    measurable_const (hWm.const_mul b)

/-- The monotonicity of the finite-domination amplitude in the cardinality bound. -/
theorem srootNSD_dominate_amp_le {N Ncap β : ℝ} (hβ : 0 ≤ β) (hN : N ≤ Ncap) :
    (3 * Real.log (max 2 N)) ^ ((1 / 3 : ℝ)⁻¹) * β ≤
      (3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * β := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log 2 ≤ Real.log (max 2 N) := Real.log_le_log (by norm_num) (le_max_left _ _)
  have h2 : Real.log (max 2 N) ≤ Real.log (max 2 Ncap) :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) (max_le_max le_rfl hN)
  refine mul_le_mul_of_nonneg_right ?_ hβ
  exact Real.rpow_le_rpow (by linarith only [h1, hl2]) (by linarith only [h2]) (by norm_num)

/-- **The probabilistic packaging of `hNear`.** -/
theorem srootNSD_assemble {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : ℕ → Finset ι) (hS : ∀ l, (S l).Nonempty)
    (Φ : Ω → ℕ → ℕ → ι → ℝ) (Mx : Ω → ℕ → ℕ → ℝ) (q : Ω → ℕ → ℝ) (W G : Ω → ℝ)
    {a b Nl : ℕ} (hab : a ≤ b) (hNl : 0 < Nl)
    {s Cp Sg σi H0 h Kp lg L2 D AW βA βB E1 Ncap D0 κ m Au AY1 AY2 : ℝ}
    (hs : 0 < s) (hCp : 0 < Cp) (hSg : 0 < Sg) (hσi : 0 ≤ σi) (hH0 : 0 ≤ H0) (hh : 0 ≤ h)
    (hKp : 0 < Kp) (hlg : 0 < lg) (hL2 : 0 ≤ L2) (hD : 0 ≤ D) (hAW : 0 < AW) (hβA : 0 < βA)
    (hβB : 0 < βB) (hE1 : 0 < E1) (hD0 : 0 < D0) (hκ0 : 0 < κ) (hm : 1 ≤ m)
    (hMx : ∀ ω L l z, a ≤ L → l < Nl → (∀ R ∈ S l, Φ ω L l R ≤ z) → Mx ω L l ≤ z)
    (hcaseA : ∀ (L l : ℕ) (R : ι), ∃ X1 X2 : Ω → ℝ,
      a ≤ L → L ≤ b → l < Nl → R ∈ S l →
        Measurable X1 ∧ IsBigO μ (gammaSigma 1) X1 (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) ∧
        Measurable X2 ∧ IsBigO μ (gammaSigma (1 / 3)) X2 βA ∧
        ∀ ω, Φ ω L l R ≤ Cp * Sg * (q ω L + (2 * h + (l : ℝ)) + Kp * L2) + X1 ω +
          (1 + σi * q ω L) * X2 ω)
    (hcaseB : ∀ (l : ℕ) (R : ι), ∃ X1 X2 : Ω → ℝ,
      l < Nl → R ∈ S l →
        Measurable X1 ∧ Measurable X2 ∧ IsBigO μ (gammaSigma (1 / 3)) X1 E1 ∧
        IsBigO μ (gammaSigma (1 / 3)) X2 βB ∧
        ∀ᵐ ω ∂μ, ∀ L, b < L → Φ ω L l R ≤ Φ ω b l R + X1 ω + q ω b * X2 ω)
    (hWm : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (hWO : IsBigO μ (gammaSigma 1) W AW)
    (hq : ∀ ω L, a ≤ L → L ≤ b → 0 ≤ q ω L ∧ q ω L ≤ H0 + W ω)
    (hGm : Measurable G) (hGO : IsBigO μ (gammaSigma (1 / 2)) G (D0 * (1 + m) ^ (10 : ℝ)))
    (hGae : ∀ᵐ ω ∂μ, ∀ L l, ∀ R ∈ S l, Φ ω L l R ≤ G ω)
    (hlogN : ∀ l < Nl, Real.log (2 * (((b + 1 - a : ℕ) : ℝ) * ((S l).card : ℝ))) ≤
      2 * lg + 2 * D * (l : ℝ))
    (hNcap1 : (((Finset.Icc a (b + 1)) ×ˢ ((Finset.range Nl).sigma S)).card : ℝ) ≤ Ncap)
    (hNcap2 : (((Finset.range Nl).sigma S).card : ℝ) ≤ Ncap)
    (hAu : gammaTriangleConst 1 * ((1 + (σi + 1) * H0) + (σi + 1) * AW) ≤ Au)
    (hcapc : Au * ((3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * (βA + βB)) ≤
      m ^ (-(4900 : ℝ)))
    (hκ : 16384 * D0 ≤ κ ^ 2)
    (hY1 : gammaTriangleConst 1 * (Cp * Sg * AW + gammaTriangleConst 1 *
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
        (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg))) ≤ AY1)
    (hY2 : gammaTriangleConst (1 / 3) * ((3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * E1 +
      κ * m ^ (-(2000 : ℝ))) ≤ AY2) :
    ∃ Y1 Y2 : Ω → ℝ, Measurable Y1 ∧ IsBigO μ (gammaSigma 1) Y1 AY1 ∧
      Measurable Y2 ∧ IsBigO μ (gammaSigma (1 / 3)) Y2 AY2 ∧
      ∀ᵐ ω ∂μ, ∀ L, a ≤ L →
        ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * Mx ω L l ≤
          ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
            (Cp * Sg * (H0 + 2 * h + (l : ℝ) + Kp * L2) +
              Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ))) +
          Y1 ω + Y2 ω := by
  classical
  have hwpos : ∀ l : ℕ, 0 < Homogenization.geometricWeight s 2 l := fun l =>
    Homogenization.geometricWeight_pos l (by linarith only [hs])
  have hα : ∀ l : ℕ, 0 < Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg) := fun l => by positivity
  choose X1 X2 hX using hcaseA
  choose X1' X2' hX' using hcaseB
  -- the `Γ₁` family, collected by one centered maximum per depth
  obtain ⟨Yl, hYlm, hYl0, hYlO, hYlb, hYsm, hYsO⟩ := srootNS_gamma1_collect (μ := μ) (a := a)
    (b := b) hab Nl hNl S hS (fun l => Homogenization.geometricWeight s 2 l)
    (fun l => Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) hwpos hα X1
    (fun L hL l hl R hR => (hX L l R (Finset.mem_Icc.1 hL).1 (Finset.mem_Icc.1 hL).2 hl hR).1)
    (fun L hL l hl R hR =>
      (hX L l R (Finset.mem_Icc.1 hL).1 (Finset.mem_Icc.1 hL).2 hl hR).2.1)
  -- finite domination of the `Γ_{1/3}` families
  have hTne : ((Finset.Icc a (b + 1)) ×ˢ ((Finset.range Nl).sigma S)).Nonempty := by
    refine (Finset.nonempty_Icc.2 (by omega)).product ?_
    obtain ⟨R, hR⟩ := hS 0
    exact ⟨⟨0, R⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 hNl, hR⟩⟩
  have hTne' : ((Finset.range Nl).sigma S).Nonempty := by
    obtain ⟨R, hR⟩ := hS 0
    exact ⟨⟨0, R⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 hNl, hR⟩⟩
  obtain ⟨V, hVm, hV0, hVO, hVle⟩ := srootNS_gamma_dominate (μ := μ) (σ := 1 / 3)
    (β := βA + βB) (by norm_num) (by positivity)
    ((Finset.Icc a (b + 1)) ×ˢ ((Finset.range Nl).sigma S)) hTne
    (fun p : ℕ × (Σ _ : ℕ, ι) => fun ω =>
      if p.1 ≤ b then X2 p.1 p.2.1 p.2.2 ω else X2' p.2.1 p.2.2 ω)
    (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨hl, hR⟩ := Finset.mem_sigma.1 hp2
      have hl' := Finset.mem_range.1 hl
      have hp1' := Finset.mem_Icc.1 hp1
      by_cases hpb : p.1 ≤ b
      · have := (hX p.1 p.2.1 p.2.2 hp1'.1 hpb hl' hR).2.2.1
        simpa [hpb] using this
      · have := (hX' p.2.1 p.2.2 hl' hR).2.1
        simpa [hpb] using this)
    (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨hl, hR⟩ := Finset.mem_sigma.1 hp2
      have hl' := Finset.mem_range.1 hl
      have hp1' := Finset.mem_Icc.1 hp1
      by_cases hpb : p.1 ≤ b
      · have := (hX p.1 p.2.1 p.2.2 hp1'.1 hpb hl' hR).2.2.2.1
        simpa [hpb] using this.mono_scale (by linarith only [hβB] : βA ≤ βA + βB)
      · have := (hX' p.2.1 p.2.2 hl' hR).2.2.2.1
        simpa [hpb] using this.mono_scale (by linarith only [hβA] : βB ≤ βA + βB))
  obtain ⟨V1, hV1m, hV10, hV1O, hV1le⟩ := srootNS_gamma_dominate (μ := μ) (σ := 1 / 3) (β := E1)
    (by norm_num) hE1.le ((Finset.range Nl).sigma S) hTne'
    (fun p : (Σ _ : ℕ, ι) => X1' p.1 p.2)
    (fun p hp => by
      obtain ⟨hl, hR⟩ := Finset.mem_sigma.1 hp
      exact (hX' p.1 p.2 (Finset.mem_range.1 hl) hR).1)
    (fun p hp => by
      obtain ⟨hl, hR⟩ := Finset.mem_sigma.1 hp
      exact (hX' p.1 p.2 (Finset.mem_range.1 hl) hR).2.2.1)
  -- the cap on the product term
  have hTc : (((Finset.Icc a (b + 1)) ×ˢ ((Finset.range Nl).sigma S)).card : ℝ) ≤ Ncap := hNcap1
  have hBvpos : 0 < (3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * (βA + βB) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.log 2 ≤ Real.log (max 2 Ncap) := Real.log_le_log (by norm_num) (le_max_left _ _)
    have h3 : 0 < 3 * Real.log (max 2 Ncap) := by linarith only [this, hl2]
    positivity
  have hVO' : IsBigO μ (gammaSigma (1 / 3)) V
      ((3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * (βA + βB)) :=
    hVO.mono_scale (srootNSD_dominate_amp_le (by positivity) hTc)
  have hg1 := srootNSD_gammaTriangleConst_pos 1
  have hg3 := srootNSD_gammaTriangleConst_pos (1 / 3)
  have hc0 : 0 < 1 + (σi + 1) * H0 := by positivity
  have hAupos : 0 < Au := by
    have : 0 < gammaTriangleConst 1 * ((1 + (σi + 1) * H0) + (σi + 1) * AW) := by positivity
    linarith only [this, hAu]
  have hUO : IsBigO μ (gammaSigma 1) (fun ω => (1 + (σi + 1) * H0) + (σi + 1) * W ω) Au :=
    (srootNSD_isBigO_affine hc0 (by positivity : 0 < σi + 1) hAW hWm hWO).mono_scale hAu
  have hGO' : IsBigO μ (gammaSigma (1 / 2)) (fun ω => |G ω|) (D0 * (1 + m) ^ (10 : ℝ)) :=
    hGO.of_abs_le (fun ω => by simp)
  have hcap := srootNS_cap_final (μ := μ) (U := fun ω => (1 + (σi + 1) * H0) + (σi + 1) * W ω)
    (V := V) (G := fun ω => |G ω|) (A := Au) (Bv := (3 * Real.log (max 2 Ncap)) ^
      ((1 / 3 : ℝ)⁻¹) * (βA + βB)) (D0 := D0) (κ := κ) (m := m) hm hAupos hBvpos hD0 hκ0
    (fun ω => by have := hW0 ω; positivity) hV0 (fun ω => abs_nonneg _) hUO hVO' hGO' hcapc hκ
  -- the two output variables
  have hV1O' : IsBigO μ (gammaSigma (1 / 3)) V1
      ((3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * E1) :=
    hV1O.mono_scale (srootNSD_dominate_amp_le hE1.le hNcap2)
  have hV1pos : 0 < (3 * Real.log (max 2 Ncap)) ^ ((1 / 3 : ℝ)⁻¹) * E1 := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.log 2 ≤ Real.log (max 2 Ncap) := Real.log_le_log (by norm_num) (le_max_left _ _)
    have h3 : 0 < 3 * Real.log (max 2 Ncap) := by linarith only [this, hl2]
    positivity
  have hmpos : 0 < κ * m ^ (-(2000 : ℝ)) :=
    mul_pos hκ0 (Real.rpow_pos_of_pos (by linarith only [hm]) _)
  have hY2m : Measurable (fun ω => V1 ω + min (((1 + (σi + 1) * H0) + (σi + 1) * W ω) * V ω)
      |G ω|) :=
    hV1m.add ((((measurable_const.add (hWm.const_mul _))).mul hVm).min hGm.abs)
  have hY2O := (SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (by norm_num : (0 : ℝ) < 1 / 3) hV1pos hmpos hV1O' hcap hV1m
    ((((measurable_const.add (hWm.const_mul _))).mul hVm).min hGm.abs)).mono_scale hY2
  have hCS : 0 ≤ Cp * Sg := by positivity
  have hsumpos : 0 < ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l *
      (Cp * Sg * (2 * h + (l : ℝ) + 2 * Kp * lg)) :=
    Finset.sum_pos (fun l _ => mul_pos (hwpos l) (hα l)) (Finset.nonempty_range_iff.2 hNl.ne')
  have hY1m : Measurable (fun ω => Cp * Sg * W ω +
      ∑ l ∈ Finset.range Nl, Homogenization.geometricWeight s 2 l * Yl l ω) :=
    (hWm.const_mul _).add hYsm
  have hY1O := (SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    one_pos (by positivity : 0 < Cp * Sg * AW) (mul_pos hg1 hsumpos) (hWO.const_mul hCS) hYsO
    (hWm.const_mul _) hYsm).mono_scale hY1
  refine ⟨_, _, hY1m, hY1O, hY2m, hY2O, ?_⟩
  -- pathwise
  have hae1 : ∀ᵐ ω ∂μ, ∀ p ∈ (Finset.range Nl).sigma S, ∀ L, b < L →
      Φ ω L p.1 p.2 ≤ Φ ω b p.1 p.2 + X1' p.1 p.2 ω + q ω b * X2' p.1 p.2 ω := by
    rw [Filter.eventually_all_finset]
    intro p hp
    obtain ⟨hl, hR⟩ := Finset.mem_sigma.1 hp
    exact (hX' p.1 p.2 (Finset.mem_range.1 hl) hR).2.2.2.2
  filter_upwards [hae1, hGae] with ω hω1 hω2
  intro L hL
  have hmemT : ∀ L l R, a ≤ L → L ≤ b + 1 → l < Nl → R ∈ S l →
      (L, (⟨l, R⟩ : Σ _ : ℕ, ι)) ∈ (Finset.Icc a (b + 1)) ×ˢ ((Finset.range Nl).sigma S) :=
    fun L l R h1 h2 hl hR => Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩,
      Finset.mem_sigma.2 ⟨Finset.mem_range.2 hl, hR⟩⟩
  have hpw := srootNSD_pathwise S (Φ ω) (Mx ω) (q ω) (fun L l R => X1 L l R ω)
    (fun L l R => X2 L l R ω) (fun l R => X1' l R ω) (fun l R => X2' l R ω) (fun l => Yl l ω)
    hab hs hCp.le hSg.le hσi hH0 (hW0 ω) hh hKp.le hlg.le hL2 hD (hV0 ω) (hV10 ω)
    (abs_nonneg (G ω)) (fun l => hYl0 l ω) (hMx ω)
    (fun L haL hLb l hl R hR => (hX L l R haL hLb hl hR).2.2.2.2 ω)
    (fun L haL hLb => hq ω L haL hLb)
    (fun L haL hLb l hl R hR => by
      have h1 := hYlb ω L (Finset.mem_Icc.2 ⟨haL, hLb⟩) l hl R hR
      have h2 := mul_le_mul_of_nonneg_left (hlogN l hl) (hα l).le
      linarith only [le_abs_self (X1 L l R ω), h1, h2])
    (fun L haL hLb l hl R hR => by
      have := hVle _ (hmemT L l R haL (by omega) hl hR) ω
      simpa [hLb] using this)
    (fun L hLb l hl R hR => hω1 ⟨l, R⟩ (Finset.mem_sigma.2 ⟨Finset.mem_range.2 hl, hR⟩) L hLb)
    (fun l hl R hR => (le_abs_self _).trans (hV1le ⟨l, R⟩
      (Finset.mem_sigma.2 ⟨Finset.mem_range.2 hl, hR⟩) ω))
    (fun l hl R hR => by
      have := hVle _ (hmemT (b + 1) l R (by omega) le_rfl hl hR) ω
      simpa using this)
    (fun L _ l _ R hR => (hω2 L l R hR).trans (le_abs_self _)) L hL
  have e : ((1 + (σi + 1) * H0) + (σi + 1) * W ω) * V ω =
      (1 + (σi + 1) * (H0 + W ω)) * V ω := by ring
  rw [e]
  linarith only [hpw]

end

end SuperdiffusionCLT.Section4.MinimalScales
