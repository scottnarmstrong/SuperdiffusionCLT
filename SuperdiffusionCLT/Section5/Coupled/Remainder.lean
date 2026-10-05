/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.FiniteToInfiniteC
public import SuperdiffusionCLT.Section5.Localization.SubcubeAvg
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# The coupling residual `R_z` of `lem.coupled.input` (`e.coupled.Rz.def`)

For the Dirichlet response `w_D` of the proof of `lem.coupled.input` (the case `e' = 0`), the
box averages are `e_{D,z} = (∇ w_D)_{z+cu_n}`, `B_z = ⨍_{z+cu_n} hshell ∇ w_D`, and the residual is
`R_z = B_z - hbar_z e_{D,z}`. This file defines these carriers (with the gradient field `gD` a
parameter) and proves the printed identity `R_z = ⨍ (hshell - hbar_z) (∇ w_D - e_{D,z})`
(`e.coupled.Rz.def`), and the shell oscillation bound `e.coupled.shell.osc`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

variable {d : ℕ}

/-- `e_{D,z} = (∇ w_D)_{z+cu_n}`, the box average of the gradient field `gD`. -/
noncomputable def coupledE (Q : TriadicCube d) (gD : Vec d → Vec d) : Vec d :=
  volumeAverageVec (cubeSet Q) gD

/-- `B_z = ⨍_{z+cu_n} hshell ∇ w_D`, with `hshell = k_m - k_{m-h}`. -/
noncomputable def coupledB (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d)
    (gD : Vec d → Vec d) : Vec d :=
  volumeAverageVec (cubeSet Q) (fun x => matVecMul (finiteShellIncrement omega (m - h) m x) (gD x))

/-- `R_z = B_z - hbar_z e_{D,z}` (`e.coupled.Rz.def`, first form). -/
noncomputable def coupledR (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d)
    (gD : Vec d → Vec d) : Vec d :=
  coupledB m h Q omega gD - matVecMul (principalGauge m h Q omega) (coupledE Q gD)

/-! ## The identity `R_z = ⨍ (hshell - hbar_z) g_{D,z}` -/

/-- Covariance identity for averages of two functions on a set of positive finite measure. -/
theorem volumeAverage_mul_sub_sub {U : Set (Vec d)}
    (hV0 : (volume U).toReal ≠ 0) (hVt : volume U ≠ ⊤) {a g : Vec d → ℝ}
    (ha : IntegrableOn a U) (hg : IntegrableOn g U) (hag : IntegrableOn (fun x => a x * g x) U) :
    volumeAverage U (fun x => (a x - volumeAverage U a) * (g x - volumeAverage U g)) =
      volumeAverage U (fun x => a x * g x) - volumeAverage U a * volumeAverage U g := by
  have hfin : IsFiniteMeasure (volume.restrict U) := ⟨by simpa only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using hVt.lt_top⟩
  have hint : ∀ c : ℝ, ∫ _x in U, c ∂volume = c * (volume U).toReal := by
    intro c
    rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
  have e1 : ∫ x in U, (a x - volumeAverage U a) * (g x - volumeAverage U g) ∂volume =
      ∫ x in U, a x * g x ∂volume - volumeAverage U g * ∫ x in U, a x ∂volume -
        volumeAverage U a * ∫ x in U, g x ∂volume +
        volumeAverage U a * volumeAverage U g * (volume U).toReal := by
    have h1 : ∀ x, (a x - volumeAverage U a) * (g x - volumeAverage U g) =
        (a x * g x - volumeAverage U g * a x) - volumeAverage U a * g x +
          volumeAverage U a * volumeAverage U g := by intro x; ring
    simp_rw [h1]
    rw [integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul, hint]
    · exact hag
    · exact ha.const_mul _
    · exact hag.sub (ha.const_mul _)
    · exact hg.const_mul _
    · exact (hag.sub (ha.const_mul _)).sub (hg.const_mul _)
    · exact integrable_const _
  have eA : ∫ x in U, a x ∂volume = volumeAverage U a * (volume U).toReal := by
    unfold volumeAverage; field_simp
  have eG : ∫ x in U, g x ∂volume = volumeAverage U g * (volume U).toReal := by
    unfold volumeAverage; field_simp
  unfold volumeAverage at *
  rw [e1]
  field_simp
  rw [eA, eG]
  field_simp
  ring


theorem coupled_continuous_finiteShellIncrement (l L : ℕ) (omega : ShellSeq d) :
    Continuous (fun x : Vec d => finiteShellIncrement omega l L x) := by
  have hs := continuous_finsetSum (Finset.Ioc l L) (fun k _ => (omega k).1.1.continuous)
  exact hs.congr (fun x => (finiteShellIncrement_apply omega l L x).symm)

theorem continuous_finiteShellIncrement_entry (omega : ShellSeq d) (l L : ℕ) (i j : Fin d) :
    Continuous (fun x : Vec d => finiteShellIncrement omega l L x i j) := by
  have hc : Continuous (fun x : Vec d => finiteShellIncrement omega l L x) := by
    have hs := continuous_finsetSum (Finset.Ioc l L) (fun k _ => (omega k).1.1.continuous)
    exact hs.congr (fun x => (finiteShellIncrement_apply omega l L x).symm)
  exact (continuous_apply j).comp ((continuous_apply i).comp hc)

/-- A bounded continuous entry of the shell increment times an integrable function is integrable
on a triadic cube. -/
theorem integrableOn_shellEntry_mul {omega : ShellSeq d} {l L : ℕ} (Q : TriadicCube d) (i j : Fin d)
    {g : Vec d → ℝ} (hg : IntegrableOn g (cubeSet Q)) :
    IntegrableOn (fun x => finiteShellIncrement omega l L x i j * g x) (cubeSet Q) := by
  have hcont := continuous_finiteShellIncrement_entry omega l L i j
  obtain ⟨C, hC⟩ := (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine Integrable.bdd_mul (c := C) hg hcont.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_cubeSet Q)]
  exact Filter.Eventually.of_forall fun x hx => hC x (cubeSet_subset_closedBall Q hx)


theorem volumeAverage_finset_sum {U : Set (Vec d)} {ι : Type*} (S : Finset ι) (f : ι → Vec d → ℝ)
    (hf : ∀ i ∈ S, IntegrableOn (f i) U) :
    volumeAverage U (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, volumeAverage U (f i) := by
  unfold volumeAverage
  rw [integral_finsetSum S hf, Finset.mul_sum]

theorem principalGauge_apply (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) (i j : Fin d) :
    principalGauge m h Q omega i j =
      volumeAverage (cubeSet Q) (fun x => finiteShellIncrement omega (m - h) m x i j) := by
  rw [principalGauge_eq_average]
  unfold volumeAverageMat
  congr 1
  funext x
  exact (congrFun (congrFun
    (finiteShellIncrement_apply_eq_streamCutoff_sub omega (Nat.sub_le m h) x) i) j).symm

/-- **`e.coupled.Rz.def`**: `R_z = ⨍_{z+cu_n} (hshell - hbar_z) g_{D,z}` with
`g_{D,z} = ∇ w_D - e_{D,z}`, for any gradient field integrable on the cube. -/
theorem coupledR_eq_average (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) {gD : Vec d → Vec d}
    (hg : ∀ i, IntegrableOn (fun x => gD x i) (cubeSet Q)) :
    coupledR m h Q omega gD =
      volumeAverageVec (cubeSet Q) (fun x =>
        matVecMul (finiteShellIncrement omega (m - h) m x - principalGauge m h Q omega)
          (gD x - coupledE Q gD)) := by
  have hV0 : (volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  have hVt : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  funext i
  simp only [coupledR, coupledB, coupledE, Pi.sub_apply, volumeAverageVec, matVecMul, Matrix.sub_apply,
    Pi.sub_apply]
  have hrw : ∀ x, ∑ j, (finiteShellIncrement omega (m - h) m x i j - principalGauge m h Q omega i j) *
      (gD x j - volumeAverage (cubeSet Q) (fun y => gD y j)) =
      ∑ j, ((finiteShellIncrement omega (m - h) m x i j -
          volumeAverage (cubeSet Q) (fun y => finiteShellIncrement omega (m - h) m y i j)) *
        (gD x j - volumeAverage (cubeSet Q) (fun y => gD y j))) := by
    intro x; refine Finset.sum_congr rfl fun j _ => ?_; rw [principalGauge_apply]
  simp_rw [hrw]
  have hA : ∀ j, IntegrableOn (fun x => finiteShellIncrement omega (m - h) m x i j) (cubeSet Q) :=
    fun j => integrableOn_entry_of_isBounded _ (isBounded_cubeSet Q) i j
  have hAG : ∀ j, IntegrableOn (fun x => finiteShellIncrement omega (m - h) m x i j * gD x j)
      (cubeSet Q) := fun j => integrableOn_shellEntry_mul Q i j (hg j)
  have hcov : ∀ j, IntegrableOn (fun x =>
      (finiteShellIncrement omega (m - h) m x i j -
          volumeAverage (cubeSet Q) (fun y => finiteShellIncrement omega (m - h) m y i j)) *
        (gD x j - volumeAverage (cubeSet Q) (fun y => gD y j))) (cubeSet Q) := by
    intro j
    have h1 := hAG j
    have h2 := (hA j).mul_const (volumeAverage (cubeSet Q) (fun y => gD y j))
    have h3 := (hg j).const_mul (volumeAverage (cubeSet Q) (fun y => finiteShellIncrement omega (m - h) m y i j))
    have h4 : IntegrableOn (fun _ : Vec d => volumeAverage (cubeSet Q) (fun y => finiteShellIncrement omega (m - h) m y i j) *
        volumeAverage (cubeSet Q) (fun y => gD y j)) (cubeSet Q) :=
      integrableOn_const hVt.lt_top.ne
    refine ((h1.sub h2).sub h3).add h4 |>.congr_fun (fun x _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring) (measurableSet_cubeSet Q)
  rw [volumeAverage_finset_sum _ _ (fun j _ => hcov j),
    volumeAverage_finset_sum _ _ (fun j _ => hAG j)]
  simp_rw [principalGauge_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [volumeAverage_mul_sub_sub hV0 hVt (hA j) (hg j) (hAG j)]


/-! ## The shell oscillation `e.coupled.shell.osc` -/

/-- `⨍_{z+cu_n} ‖hshell - hbar_z‖⁴`, the fourth power of `‖hshell - hbar_z‖_{L̲⁴(z+cu_n)}`. -/
noncomputable def shellOscFour (m h : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) : ℝ :=
  volumeAverage (cubeSet Q) (fun x =>
    Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega (m - h) m x -
      principalGauge m h Q omega) ^ (4 : ℕ))

theorem bddAbove_perturbSizeAtIndex (l L : ℕ) (R : TriadicCube d) (omega : ShellSeq d) :
    BddAbove (Set.range (SuperdiffusionCLT.Section2.Localization.localizationPerturbSizeAtIndex
      l L R omega)) := by
  have hn := Frozen.Assumptions.ShellField.continuous_matrixOperatorNorm.comp
    ((coupled_continuous_finiteShellIncrement l L omega).sub (continuous_const
      (y := SuperdiffusionCLT.Section2.Localization.localizationGaugeAverage l L R omega)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (cubeCenter R) (cubeRadius R)).exists_bound_of_continuousOn
    hn.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
    exact (le_abs_self _).trans ((hC x.1 (cubeSet_subset_closedBall R x.2)).trans (le_max_right _ _))


/-- Pointwise oscillation: on `z + cu_n` (`n ≤ m - h`), `|hshell - hbar_z| ≤ d √d 3^n g` with `g`
the derivative gauge of the translated shell sequence. -/
theorem norm_shell_sub_gauge_le {n m h : ℕ} (hn : n ≤ m - h) (Q : TriadicCube d)
    (hQ : Q.scale = (n : ℤ)) (omega : ShellSeq d) {x : Vec d} (hx : x ∈ cubeSet Q) :
    Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega (m - h) m x -
        principalGauge m h Q omega) ≤
      (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
          (ShellField.translateSequence (cubeCenter Q) omega)) := by
  have h1 := le_csSup (bddAbove_perturbSizeAtIndex (m - h) m Q omega)
    ⟨some ⟨x, hx⟩, rfl⟩
  have h2 := SuperdiffusionCLT.Section2.Localization.localizationDisplayK_perturbSize_le hn m Q hQ
    omega
  exact le_trans h1 h2

theorem shellOscFour_le {n m h : ℕ} (hn : n ≤ m - h) (Q : TriadicCube d)
    (hQ : Q.scale = (n : ℤ)) (omega : ShellSeq d) :
    shellOscFour m h Q omega ≤
      ((d : ℝ) * Real.sqrt d * (3 : ℝ) ^ n) ^ 4 *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
          (ShellField.translateSequence (cubeCenter Q) omega) ^ 4 := by
  set B : ℝ := (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
    SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge (m - h) m
      (ShellField.translateSequence (cubeCenter Q) omega)) with hB
  have hbd : ∀ x ∈ cubeSet Q, ‖Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega (m - h) m x -
      principalGauge m h Q omega) ^ (4 : ℕ)‖ ≤ B ^ 4 := by
    intro x hx
    have := norm_shell_sub_gauge_le hn Q hQ omega hx
    have h0 := Book.Ch02.matrixOperatorNorm_nonneg (finiteShellIncrement omega (m - h) m x -
      principalGauge m h Q omega)
    rw [Real.norm_of_nonneg (pow_nonneg h0 4)]
    exact pow_le_pow_left₀ h0 this 4
  have hV0 : (volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  have hnorm := norm_setIntegral_le_of_norm_le_const (volume_cubeSet_lt_top Q) hbd
  unfold shellOscFour volumeAverage
  have hVpos : 0 < (volume (cubeSet Q)).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  have hnn : 0 ≤ ∫ x in cubeSet Q, Book.Ch02.matrixOperatorNorm (finiteShellIncrement omega (m - h) m x -
      principalGauge m h Q omega) ^ (4 : ℕ) ∂volume :=
    setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ => pow_nonneg (Book.Ch02.matrixOperatorNorm_nonneg _) 4
  rw [Real.norm_of_nonneg hnn] at hnorm
  calc _ ≤ (volume (cubeSet Q)).toReal⁻¹ * (B ^ 4 * (volume (cubeSet Q)).toReal) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hVpos.le)
    _ = B ^ 4 := by field_simp
    _ = _ := by rw [hB]; ring


theorem scale_le_sub {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {m h n : ℕ} (h400 : 400 * h ≤ m)
    (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊) : n ≤ m - h := by
  have hhm : h ≤ m := by omega
  have := principal_scale_le hnu hnu1 h400 hm hnum hn
  have hcast : ((m - h : ℕ) : ℝ) = (m : ℝ) - h := Nat.cast_sub hhm
  have hl : 0 ≤ Real.logb 3 (nu⁻¹ * m) := by
    apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
    have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith only [this, hm']
  have : (n : ℝ) ≤ ((m - h : ℕ) : ℝ) := by rw [hcast]; linarith only [this, hl]
  exact_mod_cast this

/-- An average of values bounded by `c` is bounded by `c`. -/
theorem subcubeAvg_le_of_le {Kc n : ℕ} {f : TriadicCube d → ENNReal} {c : ENNReal}
    (hf : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), f Q ≤ c) :
    subcubeAvg Kc n f ≤ c := by
  unfold subcubeAvg
  set D := descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)
  by_cases hD : D.card = 0
  · rw [Finset.card_eq_zero.mp hD]; simp
  · have hs : ∑ Q ∈ D, f Q ≤ D.card * c := by
      have := Finset.sum_le_card_nsmul D f c hf
      simpa only [nsmul_eq_mul] using this
    calc (D.card : ENNReal)⁻¹ * ∑ Q ∈ D, f Q ≤ (D.card : ENNReal)⁻¹ * (D.card * c) :=
          mul_le_mul_right hs _
      _ = c := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hD) (ENNReal.natCast_ne_top _),
            one_mul]

/-- The constant of `e.coupled.shell.osc`. -/
noncomputable def shellOscConst (d : ℕ) : ℝ :=
  (d : ℝ) * Real.sqrt d * Homogenization.IndependentSums.gammaTriangleConst 2 * gaugeMomentConst 4

theorem shellOscConst_nonneg (d : ℕ) : 0 ≤ shellOscConst d := by
  unfold shellOscConst
  have h4 := gaugeMomentConst_pos 4 (by norm_num)
  have hg := Homogenization.IndependentSums.gammaTriangleConst_pos (σ := 2)
  have : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d := by positivity
  positivity

/-- The fourth moment of the scaled gauge: `E[(d √d 3^n g_R)⁴] ≤ (K m^{-100})⁴`. -/
theorem lintegral_scaledGauge_pow_four_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h n : ℕ} (hh : 1 ≤ h)
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊)
    (R : TriadicCube d) :
    ∫⁻ ω, ENNReal.ofReal (((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
        finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter R) ω))) ^ 4)
        ∂P.toMeasure ≤
      ENNReal.ofReal ((shellOscConst d * ((m : ℝ) ^ 100)⁻¹) ^ 4) := by
  have hhm : h ≤ m := by omega
  set cc : ℝ := (d : ℝ) * Real.sqrt d with hcc
  set γ : ℝ := Homogenization.IndependentSums.gammaTriangleConst 2 with hγ
  set g : ShellSeq d → ℝ := fun ω =>
    finiteShellDerivGauge (m - h) m (ShellField.translateSequence (cubeCenter R) ω) with hg
  set α : ℝ := cc * (3 : ℝ) ^ n with hα
  have hα0 : 0 ≤ α := by positivity
  obtain ⟨hi4, hm4⟩ := gauge_moment hPrefix hJ3 hh hhm (cubeCenter R) 4 (by norm_num)
  have hpt : ∀ ω, ((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n * g ω)) ^ 4 = α ^ 4 * g ω ^ 4 := by
    intro ω; rw [hα, hcc]; ring
  simp_rw [hg] at hpt
  simp_rw [hpt]
  have hint : Integrable (fun ω => α ^ 4 * g ω ^ 4) P.toMeasure := hi4.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  have hratio := principal_pow_ratio_le hnu hnu1 h400 hm hnum hn
  have hm0 : (0 : ℝ) < m := by
    have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hm']
  have hmu : 0 < ((m : ℝ) ^ 100)⁻¹ := by positivity
  have hnu99 : (nu / m) ^ 100 ≤ ((m : ℝ) ^ 100)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
    calc nu ^ 100 * ((m : ℝ) ^ 100)⁻¹ ≤ 1 * ((m : ℝ) ^ 100)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hnu.le hnu1) hmu.le
      _ = _ := one_mul _
  have hγ0 : 0 < γ := Homogenization.IndependentSums.gammaTriangleConst_pos
  have hM4 := gaugeMomentConst_pos 4 (by norm_num)
  have hampl : α * (gaugeMomentConst 4 * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) ≤
      shellOscConst d * ((m : ℝ) ^ 100)⁻¹ := by
    have e1 : α * (gaugeMomentConst 4 * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) =
        (cc * gaugeMomentConst 4 * γ) * ((3 : ℝ) ^ n * ((3 : ℝ) ^ (m - h))⁻¹) := by
      rw [hα]; ring
    rw [e1]
    have e2 : shellOscConst d = cc * gaugeMomentConst 4 * γ := by
      unfold shellOscConst; rw [hcc, hγ]; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left (hratio.trans hnu99) (by positivity)
  calc α ^ 4 * ∫ ω, g ω ^ 4 ∂P.toMeasure
      ≤ α ^ 4 * (gaugeMomentConst 4 * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) ^ 4 :=
        mul_le_mul_of_nonneg_left hm4 (by positivity)
    _ = (α * (gaugeMomentConst 4 * (γ * ((3 : ℝ) ^ (m - h))⁻¹))) ^ 4 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hampl 4



/-- One cube: `E[⨍ ‖hshell - hbar_z‖⁴] ≤ (K m^{-100})⁴`. -/
theorem shellOscFour_lintegral_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h n : ℕ} (hh : 1 ≤ h)
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ)) :
    ∫⁻ ω, ENNReal.ofReal (shellOscFour m h R ω) ∂P.toMeasure ≤
      ENNReal.ofReal ((shellOscConst d * ((m : ℝ) ^ 100)⁻¹) ^ 4) := by
  have hnm := scale_le_sub hnu hnu1 h400 hm hnum hn
  refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
    (lintegral_scaledGauge_pow_four_le hnu hnu1 hPrefix hJ3 hh h400 hm hnum hn R)
  have := shellOscFour_le hnm R hR ω
  refine this.trans (le_of_eq ?_)
  ring

/-- **`e.coupled.shell.osc`**: the shell oscillation on the boxes `z + cu_n`,
`(avsum_z E ‖hshell - hbar_z‖⁴_{L̲⁴(z+cu_n)})^{1/4} ≤ C m^{-100}`. Only the shell prefix law and J3
are used (the stationarity is that of the translated gauge). The scale hypotheses are the standing
ones of `lem.coupled.input` (`1 ≤ h`, `400 h ≤ m`, `ν ≤ 1`, `ν⁻¹ ≤ m`, `m ≥ 10^6`), and `n` is
`e.n.def.recurrence`. -/
theorem coupled_shell_osc (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ3 d P →
      ∀ m h n Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 1000000 ≤ m → nu⁻¹ ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ → n ≤ Kc →
        (subcubeAvg Kc n (fun Q => ∫⁻ ω, ENNReal.ofReal (shellOscFour m h Q ω) ∂P.toMeasure)) ^
            ((1 : ℝ) / 4) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ (-(100 : ℝ))) := by
  set K := shellOscConst d with hK
  have hK0 : 0 ≤ K := shellOscConst_nonneg d
  refine ⟨max 1 K, le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ3 m h n Kc hh h400 hm hnum hn hnK
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm']
  have hmu : 0 < ((m : ℝ) ^ 100)⁻¹ := by positivity
  have hpow : (m : ℝ) ^ (-(100 : ℝ)) = ((m : ℝ) ^ 100)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  have hcube : ∀ R ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫⁻ ω, ENNReal.ofReal (shellOscFour m h R ω) ∂P.toMeasure ≤
        ENNReal.ofReal ((K * ((m : ℝ) ^ 100)⁻¹) ^ 4) := by
    intro R hR
    have hRs : R.scale = (n : ℤ) :=
      Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube
        (by exact_mod_cast hnK) hR
    exact shellOscFour_lintegral_le hnu hnu1 hPrefix hJ3 hh h400 hm hnum hn R hRs
  have havg := subcubeAvg_le_of_le hcube
  calc _ ≤ (ENNReal.ofReal ((K * ((m : ℝ) ^ 100)⁻¹) ^ 4)) ^ ((1 : ℝ) / 4) :=
        ENNReal.rpow_le_rpow havg (by norm_num)
    _ = ENNReal.ofReal (K * ((m : ℝ) ^ 100)⁻¹) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hmu.le)

/-- Satisfiability: `d = 2`, the Dirac law at the zero shell sequence, `ν = 1`, `m = 10^6`, `h = 1`,
`n` the printed scale, `K = n`; the conclusion is the statement of `coupled_shell_osc`. -/
example : ∃ C : ℝ, 1 ≤ C ∧
    (subcubeAvg (d := 2)
        (⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊)
        (⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊)
        (fun Q => ∫⁻ ω, ENNReal.ofReal (shellOscFour 1000000 1 Q ω)
          ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2).toMeasure)) ^ ((1 : ℝ) / 4) ≤
      ENNReal.ofReal (C * ((1000000 : ℕ) : ℝ) ^ (-(100 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := coupled_shell_osc 2
  exact ⟨C, hC, H 1 one_pos le_rfl _ (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw le_rfl)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw 1000000 1 _ _ le_rfl (by norm_num) le_rfl (by norm_num)
    rfl le_rfl⟩

end SuperdiffusionCLT.Section5
