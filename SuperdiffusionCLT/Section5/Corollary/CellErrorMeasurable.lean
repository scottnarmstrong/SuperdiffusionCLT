/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.LocalizationA
public import SuperdiffusionCLT.Section5.Localization.FluctC
public import SuperdiffusionCLT.Section5.Localization.Localization

/-!
# Measurable majorant for the cell error of `e.setup.basic-split`

The cell error `b_Q = ⨍_Q (2 P_z + S̃_z) · A_m S̃_z` of the subcube `Q` involves the minimizer `S̃_z`,
whose sample dependence is not known to be measurable. By the Young step of the localization bound,
`|b_Q| ≤ λ ⟪S_z,S_z⟫ + (λ⁻¹ + 1) ⟪F_z,F_z⟫`, where `⟪S_z,S_z⟫` is a coarse quadratic form
(measurable) and `⟪F_z,F_z⟫` is majorized pointwise by an explicit expression in the sample-dependent
`L⁴` norms of the fluctuations. These norms are measurable in the sample: the map
`f ↦ ∫ |f - v|⁴` is lower semicontinuous on `L²`. Hence `|b_Q|` has a measurable majorant `B_Q`
(`cellError_majorant`) independent of the choice of `S̃`, with `subcubeAvg` of the expectations at most
`C m^{-50}`. The sum over subcubes can then be taken under the expectation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

variable {d : ℕ}

open MeasureTheory Filter Topology Homogenization
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Frozen.Section2 SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal

/-- `(f, v) ↦ ∫ ‖f - v‖⁴` is lower semicontinuous on `L² × E`. -/
theorem cellError_lsc_pow_four_sub {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ ν : Measure α) (hν : ν ≪ μ) :
    LowerSemicontinuous (fun p : Lp E 2 μ × E => ∫⁻ x, ‖(p.1 : α → E) x - p.2‖ₑ ^ (4 : ℕ) ∂ν) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  refine IsSeqClosed.isClosed ?_
  intro u p hu hlim
  have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hlim
  have hT : Tendsto (fun n => eLpNorm (((u n).1 : α → E) - (p.1 : α → E)) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (p := 2) (f := fun n => (u n).1) (f_lim := p.1)).1 h1
  have hm : TendstoInMeasure μ (fun n => ((u n).1 : α → E)) atTop (p.1 : α → E) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hT
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hae' : ∀ᵐ x ∂ν, Tendsto (fun k => ‖((u (ns k)).1 : α → E) x - (u (ns k)).2‖ₑ ^ (4 : ℕ))
      atTop (𝓝 (‖(p.1 : α → E) x - p.2‖ₑ ^ (4 : ℕ))) := by
    filter_upwards [hν.ae_le hae] with x hx
    have h3 : Tendsto (fun k => ((u (ns k)).1 : α → E) x - (u (ns k)).2) atTop
        (𝓝 ((p.1 : α → E) x - p.2)) := hx.sub (h2.comp hns.tendsto_atTop)
    exact ((ENNReal.continuous_pow 4).tendsto _).comp ((continuous_enorm.tendsto _).comp h3)
  have hmeas : ∀ k, AEMeasurable (fun x => ‖((u (ns k)).1 : α → E) x - (u (ns k)).2‖ₑ ^ (4 : ℕ)) ν :=
    fun k => (((Lp.aestronglyMeasurable (u (ns k)).1).mono_ac hν).sub
      aestronglyMeasurable_const).enorm.pow_const 4
  have h1' : ∫⁻ x, ‖(p.1 : α → E) x - p.2‖ₑ ^ (4 : ℕ) ∂ν =
      ∫⁻ x, liminf (fun k => ‖((u (ns k)).1 : α → E) x - (u (ns k)).2‖ₑ ^ (4 : ℕ)) atTop ∂ν :=
    lintegral_congr_ae (hae'.mono fun x hx => hx.liminf_eq.symm)
  show ∫⁻ x, ‖(p.1 : α → E) x - p.2‖ₑ ^ (4 : ℕ) ∂ν ≤ y
  rw [h1']
  refine (lintegral_liminf_le' hmeas).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
  exact hu (ns k)


theorem cellError_ae_le_of_openCubeSet_subset {U : Set (Vec d)} {Q : TriadicCube d}
    (hV : openCubeSet Q ⊆ U) :
    normalizedCubeMeasure Q ≪ volumeMeasureOn U := by
  rw [SuperdiffusionCLT.Section2.Estimates.Stream.normalizedCubeMeasure_eq_smul_volume_restrict_cubeSet]
  refine Measure.AbsolutelyContinuous.trans (Measure.smul_absolutelyContinuous) ?_
  have : (volume.restrict (cubeSet Q) : Measure (Vec d)) = volume.restrict (openCubeSet Q) :=
    Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)
  rw [this]
  exact Measure.absolutelyContinuous_of_le (Measure.restrict_mono hV le_rfl)

theorem cellError_volumeAverage_cubeSet_eq_open (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  unfold volumeAverage
  rw [volume_cubeSet_toReal, volume_openCubeSet_toReal,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- The `L⁴` norm of the centered field is a measurable function of the sample. -/
theorem cellError_measurable_fluct_pow_four {U : Set (Vec d)} {Q : TriadicCube d}
    (hV : openCubeSet Q ⊆ U) {G : ShellSeq d → Vec d → Vec d}
    (hmem : ∀ omega, MemVectorL2 U (G omega))
    (hmeas : Measurable fun omega => toHilbertVectorL2OfVecField (hmem omega)) :
    Measurable fun omega => vecCubeLpENorm Q 4
      (fun x => G omega x - volumeAverageVec (cubeSet Q) (G omega)) ^ (4 : ℕ) := by
  have hν := cellError_ae_le_of_openCubeSet_subset hV
  have hΦ := cellError_lsc_pow_four_sub (E := HilbertVec d) (volumeMeasureOn U)
    (normalizedCubeMeasure Q) hν
  have havg : Measurable fun omega => volumeAverageVec (cubeSet Q) (G omega) := by
    refine measurable_pi_iff.2 fun i => ?_
    have h := loc_measurable_mean_of_class hV hmem hmeas i
    have e : (fun omega => volumeAverageVec (cubeSet Q) (G omega) i) =
        fun omega => volumeAverage (openCubeSet Q) (fun x => G omega x i) :=
      funext fun omega => cellError_volumeAverage_cubeSet_eq_open Q _
    rw [e]
    exact h
  have hpair : Measurable fun omega =>
      ((toHilbertVectorL2OfVecField (hmem omega) : HilbertVectorL2 U),
        HilbertVec.ofVec (volumeAverageVec (cubeSet Q) (G omega))) :=
    hmeas.prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp havg)
  have hcomp := hΦ.measurable.comp hpair
  have e : (fun omega => vecCubeLpENorm Q 4
      (fun x => G omega x - volumeAverageVec (cubeSet Q) (G omega)) ^ (4 : ℕ)) =
      (fun p : HilbertVectorL2 U × HilbertVec d => ∫⁻ x, ‖(p.1 : Vec d → HilbertVec d) x - p.2‖ₑ ^ (4 : ℕ)
        ∂normalizedCubeMeasure Q) ∘ fun omega =>
      ((toHilbertVectorL2OfVecField (hmem omega) : HilbertVectorL2 U),
        HilbertVec.ofVec (volumeAverageVec (cubeSet Q) (G omega))) := by
    funext omega
    rw [lintegral_enorm_pow_four_eq (loc_fluct_memL2 Q (hmem omega) hV)]
    refine lintegral_congr_ae ?_
    filter_upwards [hν.ae_le (coeFn_toHilbertVectorL2OfVecField (hmem omega))] with x hx
    simp only [hx, hilbertifyVecField, WithLp.toLp_sub]
  rw [e]
  exact hcomp

/-- The pointwise majorant of the fluctuation energy `⟪F_z, F_z⟫`. -/
noncomputable def cellError_maj (nu : ℝ) (m : ℕ) (Q : TriadicCube d) (s θ : ℝ)
    (gD gN : ShellSeq d → Vec d → Vec d) (omega : ShellSeq d) : ℝ≥0∞ :=
  ENNReal.ofReal ((nu * s⁻¹ + nu⁻¹ * s) * θ) +
    (ENNReal.ofReal (nu⁻¹ * s⁻¹ * θ) * locKFour m Q omega +
      ENNReal.ofReal ((nu * s⁻¹ + nu⁻¹ * s⁻¹ + nu⁻¹ * s) * θ⁻¹) *
        (vecCubeLpENorm Q 4 (gD omega) ^ 4 + vecCubeLpENorm Q 4 (gN omega) ^ 4))

theorem cellError_maj_pointwise [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ) (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) {θ : ℝ} (hθ : 0 < θ)
    {gD gN : ShellSeq d → Vec d → Vec d}
    (hD : ∀ omega, MemVectorL2 (openCubeSet Q) (gD omega))
    (hN : ∀ omega, MemVectorL2 (openCubeSet Q) (gN omega)) {F : ShellSeq d → BlockState d}
    (hFp : ∀ omega x, (F omega).potential x = s ^ (-(1 : ℝ) / 2) • gD omega x)
    (hFf : ∀ omega x, (F omega).flux x = s ^ ((1 : ℝ) / 2) • gN omega x) (omega : ShellSeq d) :
    ENNReal.ofReal (blockPairingAverage (cubeSet Q)
        (coefficientCutoff nu omega m).toCoeffField (F omega) (F omega)) ≤
      cellError_maj nu m Q s θ gD gN omega := by
  have hθ' : ENNReal.ofReal θ * ENNReal.ofReal θ⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hθ.le, mul_inv_cancel₀ hθ.ne', ENNReal.ofReal_one]
  refine (loc_pairing_fluct_le hnu omega m Q hs (hD omega) (hN omega) (hFp omega) (hFf omega)
    hθ' hθ' hθ').trans ?_
  exact loc_energy_combine (by positivity) (by positivity) (by positivity) hθ _ _ _

theorem cellError_maj_measurable {nu : ℝ} (m : ℕ) {U : Set (Vec d)} (Q : TriadicCube d) (s θ : ℝ)
    (hV : openCubeSet Q ⊆ U) {GD GN : ShellSeq d → Vec d → Vec d}
    (hmD : ∀ omega, MemVectorL2 U (GD omega)) (hmN : ∀ omega, MemVectorL2 U (GN omega))
    (hcD : Measurable fun omega => toHilbertVectorL2OfVecField (hmD omega))
    (hcN : Measurable fun omega => toHilbertVectorL2OfVecField (hmN omega)) :
    Measurable (cellError_maj nu m Q s θ
      (fun omega x => GD omega x - volumeAverageVec (cubeSet Q) (GD omega))
      (fun omega x => GN omega x - volumeAverageVec (cubeSet Q) (GN omega))) := by
  have h1 := cellError_measurable_fluct_pow_four hV hmD hcD
  have h2 := cellError_measurable_fluct_pow_four hV hmN hcN
  have hK := loc_measurable_kFour (d := d) m Q
  unfold cellError_maj
  exact measurable_const.add ((hK.const_mul _).add ((h1.add h2).const_mul _))

theorem cellError_maj_lintegral {μ : Measure (ShellSeq d)} [IsProbabilityMeasure μ] {nu : ℝ}
    (m : ℕ) (Q : TriadicCube d) (s θ : ℝ) (gD gN : ShellSeq d → Vec d → Vec d) :
    ∫⁻ omega, cellError_maj nu m Q s θ gD gN omega ∂μ =
      ENNReal.ofReal ((nu * s⁻¹ + nu⁻¹ * s) * θ) +
        (ENNReal.ofReal (nu⁻¹ * s⁻¹ * θ) * ∫⁻ omega, locKFour m Q omega ∂μ +
          ENNReal.ofReal ((nu * s⁻¹ + nu⁻¹ * s⁻¹ + nu⁻¹ * s) * θ⁻¹) *
            ∫⁻ omega, (vecCubeLpENorm Q 4 (gD omega) ^ 4 + vecCubeLpENorm Q 4 (gN omega) ^ 4) ∂μ) := by
  have hKm := loc_measurable_kFour (d := d) m Q
  unfold cellError_maj
  rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_add_left' ((hKm.const_mul _).aemeasurable),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Majorant form of `crude_Fz_bound`: the same bound for the measurable majorant
`cellError_maj`. -/
theorem cellError_fluct_maj_avg [NeZero d] (hd : 2 ≤ d) (Cg : ℝ) (hCg : 0 ≤ Cg) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
    ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ2 d P →
      ShellLawJ3 d P → ShellLawJ1Restriction d P → ShellLawJ4 d P →
    ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc → nu⁻¹ ^ 2 ≤ (m : ℝ) →
    ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
    ∀ n : ℕ, n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ →
    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
      (wD' : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ)))),
    (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) →
    (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wN omega)) →
    (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wD' omega)) →
    ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x - (wD' omega).toH1Function.grad x) ^ (2 : ℕ)
        ∂P.toMeasure ≤
      ENNReal.ofReal (Cg * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) *
        (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))) →
    subcubeAvg Kc n (fun Q => ∫⁻ omega, cellError_maj nu m Q (sigmaBarInfinite nu (m - h) P)
        (((nu⁻¹ * (m : ℝ)) ^ 200)⁻¹)
        (fun omega x => (wD omega).toH1Function.grad x -
          volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)
        (fun omega x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
          volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
            hshellFlux nu P m h omega e' y)) omega ∂P.toMeasure) ≤
      ENNReal.ofReal (C * ((nu⁻¹ * (m : ℝ)) ^ 190)⁻¹) := by
  obtain ⟨C5, hC5, H5⟩ := crude_Fz_bound hd Cg hCg
  set Ce : ℝ := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d with hCe
  have hCe1 : 1 ≤ Ce := SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d
  set kc : ℝ := locKConst d with hkc
  have hkc0 : 0 ≤ kc := by
    have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < (4 : ℝ) / 2 + 1)
    exact mul_nonneg (by positivity) (by linarith only [hG])
  refine ⟨max 1 ((1 + 2 * (2 * Ce)) + 4 * (2 * Ce) * kc + (1 + 3 * (2 * Ce)) * (2 * Ce) ^ 4 * C5),
    le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 hnm e e' he he' n hn wD wN wD'
    hwD hwN hwD' hgap
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hnK : n ≤ Kc := loc_n_le hnu hnu1 hm1 (by omega) hn
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hnK
  obtain ⟨hσ, hσinv, hσup⟩ := SuperdiffusionCLT.Section4.MinimalScales.srootD4_sigma_bounds
    hnu (m - h) hPre hJ2 hJ3 hJ4
  set σ : ℝ := sigmaBarInfinite nu (m - h) P with hσdef
  have hσu : σ ≤ (1 + 2 * Ce) * (nu⁻¹ * m) := by
    refine hσup.trans ?_
    have hmax : max 1 ((m - h : ℕ) : ℝ) ≤ m :=
      max_le hmR (by exact_mod_cast Nat.sub_le m h)
    have h1 : nu ≤ nu⁻¹ * m := by nlinarith only [hnu1, hnuinv, hmR]
    have h2 : 2 * Ce * nu⁻¹ * max 1 ((m - h : ℕ) : ℝ) ≤ 2 * Ce * (nu⁻¹ * m) := by
      calc _ ≤ 2 * Ce * nu⁻¹ * m := mul_le_mul_of_nonneg_left hmax (by positivity)
        _ = _ := by ring
    linarith only [h1, h2]
  have hR5 := H5 nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 hnm e e' he he' n hn wD wN wD'
    hwD hwN hwD' hgap
  set L : ℝ := nu⁻¹ * (m : ℝ) with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; nlinarith only [hmR, hnuinv]
  have hLpos : 0 < L := by linarith only [hL1]
  have hθpos : 0 < (L ^ 200)⁻¹ := by positivity
  have hMD : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wD omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMN : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wN omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMS : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (hshellFlux nu P m h omega e') := fun omega => memVectorL2_hshellFlux nu P omega e' Kc
  have hper : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ omega, cellError_maj nu m Q σ ((L ^ 200)⁻¹)
        (fun omega x => (wD omega).toH1Function.grad x -
          volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)
        (fun omega x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
          volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
            hshellFlux nu P m h omega e' y)) omega ∂P.toMeasure ≤
      ENNReal.ofReal ((nu * σ⁻¹ + nu⁻¹ * σ) * (L ^ 200)⁻¹) +
        (ENNReal.ofReal (nu⁻¹ * σ⁻¹ * (L ^ 200)⁻¹) * ∫⁻ omega, locKFour m Q omega ∂P.toMeasure +
          ENNReal.ofReal ((nu * σ⁻¹ + nu⁻¹ * σ⁻¹ + nu⁻¹ * σ) * ((L ^ 200)⁻¹)⁻¹) *
            ∫⁻ omega, (vecCubeLpENorm Q 4 (fun x => (wD omega).toH1Function.grad x -
                volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad) ^ 4 +
              vecCubeLpENorm Q 4 (fun x => ((wN omega).toH1Function.grad x +
                  hshellFlux nu P m h omega e' x) -
                volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
                  hshellFlux nu P m h omega e' y)) ^ 4) ∂P.toMeasure) := by
    intro Q _
    exact le_of_eq (cellError_maj_lintegral m Q σ ((L ^ 200)⁻¹) _ _)
  have hK : subcubeAvg Kc n (fun Q => ∫⁻ omega, locKFour m Q omega ∂P.toMeasure) ≤
      ENNReal.ofReal (kc * ((m : ℝ) + 1) ^ 2) :=
    (subcubeAvg_mono_on (fun Q _ => loc_lintegral_kFour_le hPre hJ2 hJ3 hJ4 m Q)).trans
      (le_of_eq (subcubeAvg_const hnK _))
  have hR5' : subcubeAvg Kc n (fun Q => ∫⁻ omega, (vecCubeLpENorm Q 4 (fun x =>
        (wD omega).toH1Function.grad x - volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad) ^ 4 +
      vecCubeLpENorm Q 4 (fun x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
        volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
          hshellFlux nu P m h omega e' y)) ^ 4) ∂P.toMeasure) ≤
      ENNReal.ofReal (C5 * σ⁻¹ ^ 4 * (L ^ 400)⁻¹) := by
    refine hR5.trans (le_of_eq ?_)
    congr 1
    rw [Real.rpow_neg hLpos.le, show (400 : ℝ) = ((400 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine (subcubeAvg_mono_on hper).trans ?_
  rw [loc_subcubeAvg_affine hnK]
  have hA1 : 0 ≤ nu⁻¹ * σ⁻¹ * (L ^ 200)⁻¹ := by positivity
  have hA2 : 0 ≤ (nu * σ⁻¹ + nu⁻¹ * σ⁻¹ + nu⁻¹ * σ) * ((L ^ 200)⁻¹)⁻¹ := by positivity
  have hfin : ENNReal.ofReal ((nu * σ⁻¹ + nu⁻¹ * σ) * (L ^ 200)⁻¹) +
      (ENNReal.ofReal (nu⁻¹ * σ⁻¹ * (L ^ 200)⁻¹) * ENNReal.ofReal (kc * ((m : ℝ) + 1) ^ 2) +
        ENNReal.ofReal ((nu * σ⁻¹ + nu⁻¹ * σ⁻¹ + nu⁻¹ * σ) * ((L ^ 200)⁻¹)⁻¹) *
          ENNReal.ofReal (C5 * σ⁻¹ ^ 4 * (L ^ 400)⁻¹)) ≤
      ENNReal.ofReal (max 1 ((1 + 2 * (2 * Ce)) + 4 * (2 * Ce) * kc +
        (1 + 3 * (2 * Ce)) * (2 * Ce) ^ 4 * C5) * (L ^ 190)⁻¹) := by
    have hC5' : 0 ≤ C5 := by linarith only [hC5]
    rw [← ENNReal.ofReal_mul hA1, ← ENNReal.ofReal_mul hA2,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have harith := loc_Fz_arith (c := 2 * Ce) (kc := kc) (C5 := C5) (σ := σ) hnu hnu1 hmR
      (by linarith only [hCe1]) hkc0 hC5' hσ hσinv hσu
    refine harith.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  exact (add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl hK) (mul_le_mul' le_rfl hR5'))).trans hfin

/-- **Measurable majorant of the cell error.** For every choice of block-offset minimizers `S̃`, the
cell error `|b_Q|` is at most a measurable function `B Q` of the sample, and the subcube average of
`E[B Q]` is at most `C m^{-50}`. The hypotheses are those of the localization lemma, except the
minimizers, which are quantified after `B`. -/
theorem cellError_majorant (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          2 * SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) →
          ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
          ∀ n : ℕ, n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ →
          ∀ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H10Function (openCubeSet (originCube d (Kc : ℤ))))
            (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e') (wN omega)) →
          ∃ B : TriadicCube d → SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ENNReal,
            (∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (B Q)) ∧
            (∀ (Stilde : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → TriadicCube d →
                BlockState d),
              (∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
                IsBlockOffsetMinimizer
                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
                  (cubeSet Q)
                  (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
                    (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
                  (Stilde omega Q)) →
              ∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
                ENNReal.ofReal
                  |volumeAverage (cubeSet Q) (fun x =>
                    blockVecDot
                      ((2 : ℝ) • blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
                          (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) +
                        (Stilde omega Q).eval x)
                      (blockMatVecMul
                        (blockCoeffField
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField x)
                        ((Stilde omega Q).eval x)))| ≤ B Q omega) ∧
            subcubeAvg Kc n (fun Q => ∫⁻ omega, B Q omega ∂P.toMeasure) ≤
              ENNReal.ofReal (C * (m : ℝ) ^ (-(50 : ℝ))) := by
  obtain ⟨C1, hC1, H1⟩ := crude_Sz_bound d hd
  obtain ⟨Cg, hCg, Hg⟩ := loc_gap_scaled (d := d) hd
  obtain ⟨C2, hC2, H2⟩ := cellError_fluct_maj_avg hd Cg (by linarith only [hCg])
  obtain ⟨C₀, hC₀, Hm⟩ := m_large_of_lNaught
  refine ⟨max C₀ (C1 + 2 * C2), ?_, ?_⟩
  · exact (by linarith only [hC₀] : (1 : ℝ) ≤ C₀).trans (le_max_left _ _)
  intro nu cStar K hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 hJ5 m h Kc hh h400 h100 hl e e' he he' n hn wD wN
    hwD hwN
  set C : ℝ := max C₀ (C1 + 2 * C2) with hCdef
  have hCC0 : C₀ ≤ C := le_max_left _ _
  have hlm : SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) := by
    by_cases h0 : SuperdiffusionCLT.Frozen.Section4.lNaught C C (3 / 4) cStar nu K ≤ 0
    · exact h0.trans (Nat.cast_nonneg m)
    · push Not at h0
      linarith only [hl, h0]
  obtain ⟨-, h16⟩ := Hm C hCC0 cStar hJ5.cStar_pos hJ5.cStar_le_two nu hnu hnu1 K hJ5.K_pos.le m hlm
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hnm : nu⁻¹ ^ 2 ≤ (m : ℝ) :=
    (pow_le_pow_right₀ hnuinv (by norm_num : 2 ≤ 16)).trans h16
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hnK : n ≤ Kc := loc_n_le hnu hnu1 hm1 (by omega) hn
  have hMS : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (hshellFlux nu P m h omega e') := fun omega => memVectorL2_hshellFlux nu P omega e' Kc
  choose wD' hwD' using fun omega => exists_isCubeDirichletResponse (originCube d (Kc : ℤ)) (hMS omega)
  have hgap := Hg nu hnu P hPre hJ1 hJ2 hJ3 hJ4 m h Kc hh (by omega) (by omega) e' he' wD' wN hwD' hwN
  have hF := H2 nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 hnm e e' he he' n hn wD wN wD'
    hwD hwN hwD' hgap
  obtain ⟨S, hS⟩ := loc_exists_minimizers (d := d) hnu m (fun omega Q =>
    blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
  have hSbd := H1 nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc n hh h400 h100 hnK e e' he he' wD wN hwD hwN
    S (fun omega Q _ => hS omega Q)
  set L : ℝ := nu⁻¹ * (m : ℝ) with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; nlinarith only [hmR, hnuinv]
  have hLpos : 0 < L := by linarith only [hL1]
  have hlam : 0 < (L ^ 90)⁻¹ := by positivity
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hnK
  have hMD : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wD omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMN : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wN omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMG : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) :=
    fun omega => (hMN omega).add (memVectorL2_hshellFlux nu P omega e' Kc)
  set σ : ℝ := sigmaBarInfinite nu (m - h) P with hσdef
  have hσ : 0 < σ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre
    hJ2 hJ3 hJ4
  have hθ : 0 < ((L ^ 200)⁻¹) := by positivity
  have hclD : Measurable fun omega => toHilbertVectorL2OfVecField (hMD omega) :=
    loc_measurable_gradClass_dirichlet nu P m h Kc e wD hwD
  have hclN : Measurable fun omega => toHilbertVectorL2OfVecField (hMG omega) := by
    have hfun : (fun omega => toHilbertVectorL2OfVecField (hMG omega)) = fun omega =>
        (wN omega).toH1Function.gradToHilbertVectorL2 + toHilbertVectorL2OfVecField
          (memVectorL2_hshellFlux nu P (m := m) (h := h) omega e' Kc) := by
      funext omega
      exact toHilbertVectorL2OfVecField_add (wN omega).toH1Function.grad_memVectorL2
        (memVectorL2_hshellFlux nu P omega e' Kc)
    rw [hfun]
    have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    exact (loc_measurable_gradClass_neumann nu P m h Kc e' wN hwN).add
      (loc_class_hshell_measurable nu P m h Kc e')
  have hsubQ : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)) := fun Q hQ =>
    openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
  have hpt : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ omega,
      ∀ St : BlockState d, IsBlockOffsetMinimizer
        (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
        (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
          (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y)) St →
      ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x =>
          blockVecDot
            ((2 : ℝ) • blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
                (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) +
              St.eval x)
            (blockMatVecMul
              (blockCoeffField
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField x)
              (St.eval x)))| ≤
        ENNReal.ofReal (L ^ 90)⁻¹ * ENNReal.ofReal (blockPairingAverage (cubeSet Q)
            (coefficientCutoff nu omega m).toCoeffField (S omega Q) (S omega Q)) +
          ENNReal.ofReal (((L ^ 90)⁻¹)⁻¹ + 1) * ENNReal.ofReal (blockPairingAverage
            (cubeSet Q) (coefficientCutoff nu omega m).toCoeffField
            (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
              (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
            (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
              (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))) := by
    intro Q hQ omega St hSt
    have hsub := hsubQ Q hQ
    obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
    have hFL2 := loc_isBlockL2_blockFluct nu (m - h) P Q
      (g1 := (wD omega).toH1Function.grad)
      (g2 := fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y)
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub (hMD omega))
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub (hMG omega))
    have habs := abs_volumeAverage_slope_add_le hEll hFL2 (hS omega Q) hSt
    have hs0 := blockPairingAverage_self_nonneg (a := (coefficientCutoff nu omega m).toCoeffField)
      hEll (S omega Q)
    have hf0 := blockPairingAverage_self_nonneg (a := (coefficientCutoff nu omega m).toCoeffField)
      hEll (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
    refine (ENNReal.ofReal_le_ofReal (habs.trans (loc_abs_le hs0 hf0 hlam))).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hlam.le,
      ENNReal.ofReal_mul (by positivity)]
  have hmajm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      Measurable (cellError_maj nu m Q σ ((L ^ 200)⁻¹)
        (fun omega x => (wD omega).toH1Function.grad x -
          volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)
        (fun omega x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
          volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
            hshellFlux nu P m h omega e' y))) := fun Q hQ =>
    cellError_maj_measurable (nu := nu) m Q σ ((L ^ 200)⁻¹) (hsubQ Q hQ) (GD := fun omega =>
      (wD omega).toH1Function.grad) (GN := fun omega y => (wN omega).toH1Function.grad y +
        hshellFlux nu P m h omega e' y) hMD hMG hclD hclN
  have hSmQ : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      Measurable fun omega => ENNReal.ofReal (blockPairingAverage (cubeSet Q)
        (coefficientCutoff nu omega m).toCoeffField (S omega Q) (S omega Q)) := fun Q hQ =>
    loc_measurable_pairing_S hnu P m h Kc e e' wD wN hwD hwN (hsubQ Q hQ)
      (fun omega => S omega Q) (fun omega => hS omega Q)
  refine ⟨fun Q omega => ENNReal.ofReal (L ^ 90)⁻¹ * ENNReal.ofReal (blockPairingAverage (cubeSet Q)
      (coefficientCutoff nu omega m).toCoeffField (S omega Q) (S omega Q)) +
    ENNReal.ofReal (((L ^ 90)⁻¹)⁻¹ + 1) * cellError_maj nu m Q σ ((L ^ 200)⁻¹)
      (fun omega x => (wD omega).toH1Function.grad x -
        volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)
      (fun omega x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
        volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
          hshellFlux nu P m h omega e' y)) omega, ?_, ?_, ?_⟩
  · intro Q hQ
    exact ((hSmQ Q hQ).const_mul _).add ((hmajm Q hQ).const_mul _)
  · intro Stilde hSt omega Q hQ
    refine (hpt Q hQ omega _ (hSt omega Q hQ)).trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_))
    have hsub := hsubQ Q hQ
    exact cellError_maj_pointwise hnu m Q hσ hθ
      (fun omega => loc_fluct_memL2 Q (hMD omega) hsub)
      (fun omega => loc_fluct_memL2 Q (hMG omega) hsub)
      (F := fun omega => blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
      (fun _ _ => rfl) (fun _ _ => rfl) omega
  · have hper : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ∫⁻ omega, (ENNReal.ofReal (L ^ 90)⁻¹ * ENNReal.ofReal (blockPairingAverage (cubeSet Q)
          (coefficientCutoff nu omega m).toCoeffField (S omega Q) (S omega Q)) +
        ENNReal.ofReal (((L ^ 90)⁻¹)⁻¹ + 1) * cellError_maj nu m Q σ ((L ^ 200)⁻¹)
          (fun omega x => (wD omega).toH1Function.grad x -
            volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)
          (fun omega x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
            volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
              hshellFlux nu P m h omega e' y)) omega) ∂P.toMeasure =
        ENNReal.ofReal (L ^ 90)⁻¹ * ∫⁻ omega, ENNReal.ofReal (blockPairingAverage (cubeSet Q)
            (coefficientCutoff nu omega m).toCoeffField (S omega Q) (S omega Q)) ∂P.toMeasure +
          ENNReal.ofReal (((L ^ 90)⁻¹)⁻¹ + 1) * ∫⁻ omega, cellError_maj nu m Q σ ((L ^ 200)⁻¹)
          (fun omega x => (wD omega).toH1Function.grad x -
            volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)
          (fun omega x => ((wN omega).toH1Function.grad x + hshellFlux nu P m h omega e' x) -
            volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
              hshellFlux nu P m h omega e' y)) omega ∂P.toMeasure := by
      intro Q hQ
      rw [lintegral_add_left' ((hSmQ Q hQ).const_mul _).aemeasurable,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (subcubeAvg_mono_on fun Q hQ => (hper Q hQ).le).trans ?_
    rw [subcubeAvg_add, subcubeAvg_const_mul, subcubeAvg_const_mul]
    refine (add_le_add (mul_le_mul' le_rfl hSbd) (mul_le_mul' le_rfl hF)).trans ?_
    have hC1' : 0 ≤ C1 := by linarith only [hC1]
    have hC2' : 0 ≤ C2 := by linarith only [hC2]
    have hfin := loc_final_arith hnu hnu1 hm1 hC1' hC2'
    have hCle : C1 + 2 * C2 ≤ C := le_max_right _ _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hfin.trans ?_)
    exact mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (Nat.cast_nonneg m) _)



/-- Satisfiability of the response hypotheses of `cellError_majorant`. -/
example [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h Kc n : ℕ) (hn : n ≤ Kc) (e e' : Vec d) :
    ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
      (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega e) (wD omega)) ∧
      (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega e') (wN omega)) := by
  obtain ⟨wD, wN, hD, hN, -⟩ := localization_hypotheses_satisfiable hnu P m h Kc n hn e e'
  exact ⟨wD, wN, hD, hN⟩

end SuperdiffusionCLT.Section5
