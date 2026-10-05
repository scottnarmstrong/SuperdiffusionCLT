/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.GeneratorToPathLaw
public import SuperdiffusionCLT.Section8.Prereq.HeatWitnessC
public import SuperdiffusionCLT.Section8.Convergence.GeneratorToPathLawB
public import SuperdiffusionCLT.Section8.Brownian.HeatCoreC
public import SuperdiffusionCLT.Section8.Rescaling.ReparametrisationB
public import SuperdiffusionCLT.Section6.Prereq.FullField

/-!
# From the generator approximation to convergence of the rescaled path laws

Model-independent assembly.  Let `S` be a conservative Feller semigroup with generator
`∇·(a∇·)` on `C²` (`IsDivergenceFormFeller a S`) and `Q` a continuous-path law of `S`.

* `genPath_tendsto_c0Semigroup`: generator approximation on `C_c^∞` gives strong convergence of the
  semigroups to the heat semigroup (Trotter--Kato through `CoreResolvent`, with the core property of
  `GeneratorToPathLawB`).
* `genPath_tendsto_scaled_integral`: for space scales `δ ε` and time scales `τ ε`, and the
  generator approximation for the operators `∇·(δ² τ a(·/δ)∇·)`, the rescaled path laws
  `Q x₀ ∘ scalePath (A ε) (τ ε)⁻¹` converge to `scalePath κ 1` of Brownian motion from `0`,
  whenever `A ε / δ ε → κ ≠ 0`.  No moment bound is used.
* `genPath_clause_i`: clause (i) of the quenched invariance principle for one sample, from the
  conclusion of the generator proposition, in the printed shape (every start `x₀`, every bounded
  continuous `F`), through the reparametrisation `δ(ε)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Homogenization MeasureTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.Semigroup
open scoped ENNReal NNReal ZeroAtInfty ContDiff BoundedContinuousFunction

noncomputable section

variable {d : ℕ}

/-- **Strong convergence of the semigroups from the generator approximation.**  Let `T i` be
Feller semigroups indexed along a filter `l`.  Suppose that every `f` of the differentiable class
of the heat generator which is smooth with compact support has approximants `w i`, `g i`, with
`w i` in the generator domain of `T i`, generator value `g i`, `w i → f` and `g i → ½ Δ f`.  Then
`T i t h → heat t h` in `C₀` for every `h` and every time `t`. -/
theorem genPath_tendsto_c0Semigroup {ι : Type*} {l : Filter ι}
    {T : ι → SubMarkovKernelSemigroup (Vec d)} (hT : ∀ i, (T i).IsFellerKernelSemigroup)
    (happrox : ∀ f : heatCore d, ContDiff ℝ ∞ (f : Vec d → ℝ) →
      HasCompactSupport (f : Vec d → ℝ) →
      ∃ w g : ι → C₀(Vec d, ℝ),
        (∀ᶠ i in l, ∃ hw : w i ∈ (hT i).c0Semigroup.generatorDomain,
          (hT i).c0Semigroup.generator ⟨w i, hw⟩ = g i) ∧
        Tendsto w l (𝓝 (f : C₀(Vec d, ℝ))) ∧
        Tendsto g l (𝓝 ((2 : ℝ)⁻¹ • heatCoreLaplacian f)))
    (t : ℝ≥0) (f : C₀(Vec d, ℝ)) :
    Tendsto (fun i => (hT i).c0Semigroup t f) l (𝓝 ((heatC0Semigroup d) t f)) := by
  classical
  let mu : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let D : Set (heatC0Semigroup d).generatorDomain :=
    {u | ∃ f' : heatCore d, ContDiff ℝ ∞ (f' : Vec d → ℝ) ∧ HasCompactSupport (f' : Vec d → ℝ) ∧
      u = ⟨(f' : C₀(Vec d, ℝ)), mem_generatorDomain_heatCore f'⟩}
  have hDdense : Dense {g : C₀(Vec d, ℝ) | ∃ u ∈ D,
      (mu : ℝ) • (u : C₀(Vec d, ℝ)) - (heatC0Semigroup d).generator u = g} := by
    refine (genPath_dense_smooth_range d).mono ?_
    rintro g ⟨f', hf1, hf2, rfl⟩
    refine ⟨⟨(f' : C₀(Vec d, ℝ)), mem_generatorDomain_heatCore f'⟩, ⟨f', hf1, hf2, rfl⟩, ?_⟩
    rw [generator_heatCore]
  have happrox' : ∀ u ∈ D, ∃ w : (i : ι) → (hT i).c0Semigroup.generatorDomain,
      Tendsto (fun i => ((w i : C₀(Vec d, ℝ)))) l (𝓝 (u : C₀(Vec d, ℝ))) ∧
        Tendsto (fun i => (hT i).c0Semigroup.generator (w i)) l
          (𝓝 ((heatC0Semigroup d).generator u)) := by
    rintro u ⟨f', hf1, hf2, rfl⟩
    obtain ⟨w, g, hev, hw, hg⟩ := happrox f' hf1 hf2
    refine ⟨fun i => if h : ∃ hw : w i ∈ (hT i).c0Semigroup.generatorDomain,
      (hT i).c0Semigroup.generator ⟨w i, hw⟩ = g i then ⟨w i, h.1⟩ else 0, ?_, ?_⟩
    · refine hw.congr' ?_
      filter_upwards [hev] with i hi
      simp only [hi, ↓reduceDIte]
    · rw [generator_heatCore]
      refine hg.congr' ?_
      filter_upwards [hev] with i hi
      simp only [hi, ↓reduceDIte]
      exact hi.choose_spec.symm
  exact tendsto_operator_of_tendsto_generator (S := fun i => (hT i).c0Semigroup)
    (S' := heatC0Semigroup d) (mu := mu) (D := D) hDdense happrox' f t

/-- Path identity: dilating a dilated path. -/
theorem genPath_scalePath_scalePath (s δ : ℝ) (τ : ℝ≥0) (w : ContinuousPath (Vec d)) :
    scalePath s 1 (scalePath δ τ w) = scalePath (s * δ) τ w := by
  refine ContinuousMap.ext fun t => ?_
  simp only [scalePath_apply, one_mul, smul_smul]

theorem genPath_dilate_isDivergenceFormFeller_c0 (a : CoeffField d)
    {S : SubMarkovKernelSemigroup (Vec d)} (hS : IsDivergenceFormFeller a S) {δ : ℝ}
    (hδ : δ ≠ 0) {τ : ℝ≥0} (hτ : 0 < τ) :
    ∃ hF : (fd_dilateSemigroup S hδ τ).IsFellerKernelSemigroup,
      (fd_dilateSemigroup S hδ τ).IsConservative ∧
      ∀ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 (⇑u) →
        (∀ x, v x = divForm ((δ ^ 2 * (τ : ℝ))) (fun y => a (δ⁻¹ • y)) (⇑u) x) →
          ∃ hu : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu⟩ = v := by
  obtain ⟨hc, hF, hgen⟩ := isDivergenceFormFeller_dilateSemigroup a hδ hτ hS
  have hr : δ ^ 2 * (τ : ℝ) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hδ) (NNReal.coe_pos.mpr hτ).ne'
  refine ⟨hF, hc, fun u v hu hv => hgen u v hu fun x => ?_⟩
  rw [divForm_smul_coeff (fun y => a (δ⁻¹ • y)) hr, hv x]
  unfold divForm
  rw [one_mul]

/-- **Generator approximation along a dilated family gives convergence of the rescaled path
laws to dilated Brownian motion.** -/
theorem genPath_tendsto_scaled_integral
    (a : CoeffField d) {S : SubMarkovKernelSemigroup (Vec d)} (hS : IsDivergenceFormFeller a S)
    {Q : Vec d → Measure (ContinuousPath (Vec d))} (hQ : IsContinuousPathLaw S Q)
    {δ A : ℝ → ℝ} {τ : ℝ → ℝ≥0} {κ : ℝ}
    (hδ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < δ ε) (hδ0 : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (hτ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < τ ε) (hκ : κ ≠ 0)
    (hA : Tendsto (fun ε => A ε / δ ε) (𝓝[>] 0) (𝓝 κ))
    (hgen : ∀ u : Vec d → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      ∃ uep : ℝ → Vec d → ℝ,
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ContDiff ℝ 2 (uep ε) ∧ IsC0Function (uep ε) ∧
          IsC0Function (divForm (δ ε ^ 2 * (τ ε : ℝ)) (fun y => a ((δ ε)⁻¹ • y)) (uep ε))) ∧
        Tendsto (fun ε => ⨆ x : Vec d, ENNReal.ofReal |uep ε x - u x|) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun ε => ⨆ x : Vec d, ENNReal.ofReal
          |divForm (δ ε ^ 2 * (τ ε : ℝ)) (fun y => a ((δ ε)⁻¹ • y)) (uep ε) x -
            (1 / 2) * Brownian.vecLaplacian u x|) (𝓝[>] 0) (𝓝 0))
    (x₀ : Vec d) (F : ContinuousPath (Vec d) →ᵇ ℝ) :
    Tendsto (fun ε => ∫ w, F (scalePath (A ε) (τ ε) w) ∂(Q x₀)) (𝓝[>] 0)
      (𝓝 (∫ w, F (scalePath κ 1 w) ∂(Brownian.brownianMotion d 0))) := by
  classical
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  -- junk-completed parameters
  set δ' : ℝ → ℝ := fun ε => if 0 < δ ε then δ ε else 1 with hδ'
  set τ' : ℝ → ℝ≥0 := fun ε => if 0 < τ ε then τ ε else 1 with hτ'
  set s' : ℝ → ℝ := fun ε => if A ε / δ ε ≠ 0 then A ε / δ ε else 1 with hs'
  have hδ'ne : ∀ ε, δ' ε ≠ 0 := fun ε => by
    by_cases h : 0 < δ ε
    · simp only [hδ', h, ↓reduceIte]; exact h.ne'
    · simp [hδ', h]
  have hτ'pos : ∀ ε, 0 < τ' ε := fun ε => by
    by_cases h : 0 < τ ε <;> simp [hτ', h]
  have hs'ne : ∀ ε, s' ε ≠ 0 := fun ε => by
    by_cases h : A ε / δ ε = 0
    · simp only [hs', h, ne_eq, not_true_eq_false, ↓reduceIte]; exact one_ne_zero
    · simp only [hs', h, ne_eq, not_false_eq_true, ↓reduceIte]
  have hδδ' : ∀ᶠ ε in l, δ' ε = δ ε := hδ.mono fun ε h => by simp [hδ', h]
  have hττ' : ∀ᶠ ε in l, τ' ε = τ ε := hτ.mono fun ε h => by simp [hτ', h]
  have hδ'0 : Tendsto δ' l (𝓝 0) := hδ0.congr' (hδδ'.mono fun ε h => h.symm)
  have hAne : ∀ᶠ ε in l, A ε / δ ε ≠ 0 := hA.eventually_ne hκ
  have hs'κ : Tendsto s' l (𝓝 κ) := by
    refine hA.congr' ?_
    filter_upwards [hAne] with ε hz
    simp only [hs', ne_eq, hz, not_false_eq_true, ↓reduceIte]
  have hFell : ∀ ε, ∃ hF : (fd_dilateSemigroup S (hδ'ne ε) (τ' ε)).IsFellerKernelSemigroup,
      (fd_dilateSemigroup S (hδ'ne ε) (τ' ε)).IsConservative ∧
      ∀ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 (⇑u) →
        (∀ x, v x = divForm ((δ' ε ^ 2 * (τ' ε : ℝ))) (fun y => a ((δ' ε)⁻¹ • y)) (⇑u) x) →
          ∃ hu : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu⟩ = v :=
    fun ε => genPath_dilate_isDivergenceFormFeller_c0 a hS (hδ'ne ε) (hτ'pos ε)
  choose hP hPc hPspec using hFell
  have hconvP : ∀ (t : ℝ≥0) (f : C₀(Vec d, ℝ)),
      Tendsto (fun ε => (hP ε).c0Semigroup t f) l (𝓝 ((heatC0Semigroup d) t f)) := by
    refine genPath_tendsto_c0Semigroup hP ?_
    intro f' hf1 hf2
    obtain ⟨uep, hev, h1, h2⟩ := hgen (f' : Vec d → ℝ) hf1 hf2
    let w : ℝ → C₀(Vec d, ℝ) := fun ε => if h : IsC0Function (uep ε) then h.choose else 0
    let g : ℝ → C₀(Vec d, ℝ) := fun ε =>
      if h : IsC0Function (divForm (δ ε ^ 2 * (τ ε : ℝ)) (fun y => a ((δ ε)⁻¹ • y)) (uep ε))
      then h.choose else 0
    have hw : ∀ᶠ ε in l, ⇑(w ε) = uep ε := hev.mono fun ε h => by
      simp only [w, h.2.1, ↓reduceDIte]
      exact h.2.1.choose_spec
    have hg : ∀ᶠ ε in l, ⇑(g ε) =
        divForm (δ ε ^ 2 * (τ ε : ℝ)) (fun y => a ((δ ε)⁻¹ • y)) (uep ε) := hev.mono fun ε h => by
      simp only [g, h.2.2, ↓reduceDIte]
      exact h.2.2.choose_spec
    refine ⟨w, g, ?_, ?_, ?_⟩
    · filter_upwards [hev, hδδ', hττ', hw, hg] with ε hev' hd ht hw' hg'
      refine hPspec ε (w ε) (g ε) (by rw [hw']; exact hev'.1) (fun x => ?_)
      rw [hd, ht, hw', hg']
    · refine genPath_tendsto_c0_of_iSup w (f' : C₀(Vec d, ℝ)) (h1.congr' ?_)
      filter_upwards [hw] with ε hw'
      simp only [hw']
    · refine genPath_tendsto_c0_of_iSup g _ (h2.congr' ?_)
      filter_upwards [hg] with ε hg'
      simp only [hg', ZeroAtInftyContinuousMap.smul_apply, heatCoreLaplacian_apply, smul_eq_mul,
        one_div]
  have hTF : ∀ ε, (fd_dilateSemigroup (fd_dilateSemigroup S (hδ'ne ε) (τ' ε)) (hs'ne ε) 1
      ).IsFellerKernelSemigroup := fun ε =>
    fd_feller_conj _ _ (hs'ne ε) (fd_dilateSemigroup_apply _ (hs'ne ε) 1) (hP ε)
  have hTc : ∀ ε, (fd_dilateSemigroup (fd_dilateSemigroup S (hδ'ne ε) (τ' ε)) (hs'ne ε) 1
      ).IsConservative := fun ε =>
    (fd_isRescaledConjugate (hs'ne ε) (fd_dilateSemigroup_apply _ (hs'ne ε) 1)).isConservative
      (hPc ε)
  have hHF : (fd_dilateSemigroup (Brownian.heatSemigroup d) hκ 1).IsFellerKernelSemigroup :=
    fd_feller_conj _ _ hκ (fd_dilateSemigroup_apply _ hκ 1)
      (Brownian.isFellerKernelSemigroup_heatSemigroup d)
  have hHc : (fd_dilateSemigroup (Brownian.heatSemigroup d) hκ 1).IsConservative :=
    (fd_isRescaledConjugate hκ (fd_dilateSemigroup_apply _ hκ 1)).isConservative
      (Brownian.isConservative_heatSemigroup d)
  have hconvT : ∀ (t : ℝ≥0) (f : C₀(Vec d, ℝ)),
      Tendsto (fun ε => (hTF ε).c0Semigroup t f) l (𝓝 (hHF.c0Semigroup t f)) := fun t f =>
    genPath_tendsto_dilate_c0 hP (Brownian.isFellerKernelSemigroup_heatSemigroup d) hconvP hs'ne hκ
      hs'κ hTF hHF t f
  -- path laws
  have hQP : ∀ ε, IsContinuousPathLaw (fd_dilateSemigroup S (hδ'ne ε) (τ' ε))
      (fun x => (Q ((δ' ε)⁻¹ • x)).map (scalePath (δ' ε) (τ' ε))) := fun ε =>
    isContinuousPathLaw_dilate hS.1 hQ (hδ'ne ε) (hτ'pos ε) (fd_dilateSemigroup_apply S _ _)
  have hQT : ∀ ε, IsContinuousPathLaw
      (fd_dilateSemigroup (fd_dilateSemigroup S (hδ'ne ε) (τ' ε)) (hs'ne ε) 1)
      (fun y => ((Q ((δ' ε)⁻¹ • (s' ε)⁻¹ • y)).map (scalePath (δ' ε) (τ' ε))).map
        (scalePath (s' ε) 1)) := fun ε =>
    isContinuousPathLaw_dilate (hPc ε) (hQP ε) (hs'ne ε) one_pos
      (fd_dilateSemigroup_apply _ (hs'ne ε) 1)
  have hQ0 : IsContinuousPathLaw (fd_dilateSemigroup (Brownian.heatSemigroup d) hκ 1)
      (fun y => (Brownian.brownianMotion d (κ⁻¹ • y)).map (scalePath κ 1)) :=
    isContinuousPathLaw_dilate (Brownian.isConservative_heatSemigroup d)
      (isContinuousPathLaw_brownianMotion d) hκ one_pos (fd_dilateSemigroup_apply _ hκ 1)
  set y : ℝ → Vec d := fun ε => s' ε • δ' ε • x₀ with hy
  have hy0 : Tendsto y l (𝓝 0) := by
    have := hs'κ.smul (hδ'0.smul_const x₀)
    simpa only [hy, zero_smul, smul_zero] using this
  have hKey := sgConv_tendsto_pathLaw_filter (l := l) (S := fun ε =>
      fd_dilateSemigroup (fd_dilateSemigroup S (hδ'ne ε) (τ' ε)) (hs'ne ε) 1)
    (T₀ := fd_dilateSemigroup (Brownian.heatSemigroup d) hκ 1) hTF hTc hHF hHc hconvT hy0
    (Q := fun ε => ⟨_, (hQT ε (y ε)).1⟩) (Q₀ := ⟨_, (hQ0 0).1⟩)
    (fun ε I => (hQT ε (y ε)).2 I) (fun I => (hQ0 0).2 I)
  have hInt := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hKey) F
  have hlim : ∫ w, F w ∂((Brownian.brownianMotion d (κ⁻¹ • (0 : Vec d))).map (scalePath κ 1)) =
      ∫ w, F (scalePath κ 1 w) ∂(Brownian.brownianMotion d 0) := by
    rw [smul_zero, integral_map (continuous_scalePath κ 1).aemeasurable
      F.continuous.aestronglyMeasurable]
  have hseq : ∀ ε, ∫ w, F w ∂(((Q ((δ' ε)⁻¹ • (s' ε)⁻¹ • y ε)).map
      (scalePath (δ' ε) (τ' ε))).map (scalePath (s' ε) 1)) =
      ∫ w, F (scalePath (s' ε * δ' ε) (τ' ε) w) ∂(Q x₀) := by
    intro ε
    have h1 : (δ' ε)⁻¹ • (s' ε)⁻¹ • y ε = x₀ := by
      simp only [hy, inv_smul_smul₀ (hs'ne ε), inv_smul_smul₀ (hδ'ne ε)]
    have hm : AEStronglyMeasurable (fun v : ContinuousPath (Vec d) => F (scalePath (s' ε) 1 v))
        (Measure.map (scalePath (δ' ε) (τ' ε)) (Q x₀)) :=
      (F.continuous.comp (continuous_scalePath (s' ε) 1)).aestronglyMeasurable
    rw [h1, integral_map (continuous_scalePath (s' ε) 1).aemeasurable
      F.continuous.aestronglyMeasurable,
      integral_map (continuous_scalePath (δ' ε) (τ' ε)).aemeasurable hm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [genPath_scalePath_scalePath]
  have hInt' : Tendsto (fun ε => ∫ w, F w ∂(((Q ((δ' ε)⁻¹ • (s' ε)⁻¹ • y ε)).map
      (scalePath (δ' ε) (τ' ε))).map (scalePath (s' ε) 1))) l
      (𝓝 (∫ w, F w ∂((Brownian.brownianMotion d (κ⁻¹ • (0 : Vec d))).map (scalePath κ 1)))) :=
    hInt
  rw [hlim] at hInt'
  refine (hInt'.congr hseq).congr' ?_
  filter_upwards [hAne, hδδ', hττ', hδ] with ε hz hd ht hpos
  have hsd : s' ε * δ' ε = A ε := by
    have h1 : s' ε = A ε / δ ε := by
      simp only [hs', ne_eq, hz, not_false_eq_true, ↓reduceIte]
    rw [h1, hd]
    exact div_mul_cancel₀ _ hpos.ne'
  rw [hsd, ht]

theorem genPath_timeScale_eq (cStar δ ε : ℝ) (h : Rescaling.reparamScale cStar δ = ε ^ 2) :
    timeScale cStar δ = (ε ^ 2)⁻¹ := by
  rw [← h, Rescaling.reparamScale, timeScale, mul_inv]

theorem genPath_prefactor (cStar δ ε : ℝ) (hc : 0 < cStar) (hδ : 0 < δ) (hε : 0 < ε)
    (h : Rescaling.reparamScale cStar δ = ε ^ 2) :
    δ ^ 2 * (((ε ^ 2)⁻¹.toNNReal : ℝ≥0) : ℝ) = opScale cStar δ := by
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr (by positivity)), ← genPath_timeScale_eq cStar δ ε h,
    sq_mul_timeScale cStar δ hc hδ]

/-- **Clause (i) of Theorem A for one sample, from the generator approximation.** -/
theorem genPath_clause_i (d : ℕ) (nu : ℝ) (cStar : ℝ) (hc : 0 < cStar)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (hgen :
      ∀ u : Homogenization.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
                ∃ uep : ℝ → Homogenization.Vec d → ℝ,
                  (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
                    ContDiff ℝ 2 (uep ε) ∧
                      SuperdiffusionCLT.Section8.IsC0Function (uep ε) ∧
                      SuperdiffusionCLT.Section8.IsC0Function
                        (SuperdiffusionCLT.Section8.divForm
                          (SuperdiffusionCLT.Section8.opScale cStar ε)
                          (SuperdiffusionCLT.Section8.epCoeff nu omega ε) (uep ε))) ∧
                  -- e.homogenization.giveth
                  Filter.Tendsto
                    (fun ε : ℝ => ⨆ x : Homogenization.Vec d, ENNReal.ofReal |uep ε x - u x|)
                    (𝓝[>] 0) (𝓝 0) ∧
                  -- e.RHS.converge
                  Filter.Tendsto
                    (fun ε : ℝ => ⨆ x : Homogenization.Vec d,
                      ENNReal.ofReal
                        |SuperdiffusionCLT.Section8.divForm
                            (SuperdiffusionCLT.Section8.opScale cStar ε)
                            (SuperdiffusionCLT.Section8.epCoeff nu omega ε) (uep ε) x -
                          (1 / 2) * SuperdiffusionCLT.Section8.Brownian.vecLaplacian u x|)
                    (𝓝[>] 0) (𝓝 0))
    {S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d)}
    (hS : IsDivergenceFormFeller (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) S)
    {Q : Homogenization.Vec d →
      MeasureTheory.Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d))}
    (hQ : IsContinuousPathLaw S Q) (x₀ : Homogenization.Vec d)
    (F : BoundedContinuousFunction (MarkovProcess.ContinuousPath (Homogenization.Vec d)) ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ w, F (scalePath (|Real.log (ε ^ 2)| ^ (-(1 / 4 : ℝ)) * ε)
        ((ε ^ 2)⁻¹).toNNReal w) ∂(Q x₀))
      (𝓝[>] 0)
      (𝓝 (∫ w, F (scalePath (Real.sqrt (2 * Real.sqrt cStar)) 1 w)
        ∂(Brownian.brownianMotion d 0))) := by
  obtain ⟨δ, hδ⟩ := Rescaling.repar_exists_fun hc
  have hδ0 : Tendsto δ (𝓝[>] 0) (𝓝[>] 0) := Rescaling.repar_tendsto_zero hc hδ
  have hratio := Rescaling.repar_tendsto_ratio hc hδ
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ ε ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    hδ0.eventually (Ioo_mem_nhdsGT (by norm_num))
  have hpref : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ ε ^ 2 * (((ε ^ 2)⁻¹.toNNReal : ℝ≥0) : ℝ) =
      opScale cStar (δ ε) := by
    filter_upwards [hδ, hpos] with ε h1 h2
    exact genPath_prefactor cStar (δ ε) ε hc h1.1.1 h2 h1.2
  refine genPath_tendsto_scaled_integral (S := S) (Q := Q) (δ := δ)
    (τ := fun ε => ((ε ^ 2)⁻¹).toNNReal) (κ := Real.sqrt (2 * Real.sqrt cStar))
    (A := fun ε => |Real.log (ε ^ 2)| ^ (-(1 / 4 : ℝ)) * ε) _ hS hQ
    (hδ.mono fun ε h => h.1.1) (tendsto_nhdsWithin_iff.mp hδ0).1 ?_ ?_ ?_ ?_ x₀ F
  · filter_upwards [hpos] with ε h
    exact Real.toNNReal_pos.mpr (inv_pos.mpr (by positivity))
  · exact (Real.sqrt_pos.mpr (by positivity)).ne'
  · refine hratio.congr fun ε => ?_
    rw [mul_comm]
  · intro u hu hcs
    obtain ⟨uep, hspec, hT1, hT2⟩ := hgen u hu hcs
    refine ⟨fun ε => uep (δ ε), ?_, hT1.comp hδ0, ?_⟩
    · filter_upwards [hsmall, hpref] with ε hε hp
      have h := hspec (δ ε) hε.1 hε.2.le
      rw [hp]
      exact h
    · refine (hT2.comp hδ0).congr' ?_
      filter_upwards [hpref] with ε hp
      rw [hp]
      rfl
  
end

end SuperdiffusionCLT.Section8.Convergence
