/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CenteringE
public import SuperdiffusionCLT.Section7.Prereq.CenteringB
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockH
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.DiracJ1Restriction
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance

@[expose] public section

open scoped Pointwise ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# Centring: the bound consumed by the first root

For every `σ, ε > 0` there are constants and, for every admissible law, a random scale `K` (with
the `Γ_{2σ}` tail of the window estimates) such that almost surely, for every `m` with
`K ≤ 3^m`, every domain `W' = 3^m W` with `W` in the uniform `C^{1,1}` class inside the unit cube and
`|W| ≥ v₀`, and every entry `(i, j)`,
`|(k_{ij})_{W'} - (k_{ij})_{□_m}| ≤ C m^{σ+ε}`.
-/

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section6

variable {d : ℕ}

theorem kc3_pow_decay {m : ℕ} (hm : 1 ≤ m) {σ ε : ℝ} (hε : 0 < ε) :
    (m : ℝ) ^ (1 + σ) * (1 / 3 : ℝ) ^ m ≤ (m : ℝ) ^ (σ + ε) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith only [hm1]
  have h1 : (m : ℝ) * (1 / 3 : ℝ) ^ m ≤ 1 := by
    have : (m : ℝ) < (3 : ℝ) ^ m := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact this.le
  have h2 : (m : ℝ) ^ σ ≤ (m : ℝ) ^ (σ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith only [hε])
  have h3 : (m : ℝ) ^ (1 + σ) = (m : ℝ) * (m : ℝ) ^ σ := by
    rw [Real.rpow_add hm0, Real.rpow_one]
  have hs : 0 ≤ (m : ℝ) ^ σ := Real.rpow_nonneg hm0.le σ
  calc (m : ℝ) ^ (1 + σ) * (1 / 3 : ℝ) ^ m = ((m : ℝ) * (1 / 3 : ℝ) ^ m) * (m : ℝ) ^ σ := by
        rw [h3]; ring
    _ ≤ 1 * (m : ℝ) ^ σ := mul_le_mul_of_nonneg_right h1 hs
    _ ≤ _ := by linarith only [h2]

/-- An average of `f + c` is the average of `f` plus `c`. -/
theorem kc3_avg_add_const {S : Set (Vec d)} {f : Vec d → ℝ} (c : ℝ)
    (hpos : 0 < (volume S).toReal) (hint : IntegrableOn f S) :
    volumeAverage S (fun y => f y + c) = volumeAverage S f + c := by
  have hfin : volume S < ⊤ := lt_top_iff_ne_top.2 fun h0 => by simp [h0] at hpos
  have hfm : IsFiniteMeasure (volume.restrict S) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have h1 : ∫ y in S, (f y + c) = (∫ y in S, f y) + (volume S).toReal * c := by
    rw [integral_add hint (integrable_const c), setIntegral_const, smul_eq_mul]
    rfl
  unfold volumeAverage
  rw [h1]
  have hv : (volume S).toReal ≠ 0 := hpos.ne'
  field_simp

theorem kc3_integrableOn_cube {f : Vec d → ℝ} (hf : Continuous f) (m : ℕ) {S : Set (Vec d)}
    (hS : S ⊆ cubeSet (originCube d (m : ℤ))) : IntegrableOn f S :=
  (hf.continuousOn.integrableOn_compact (isBounded_cubeSet _).isCompact_closure).mono_set
    (hS.trans subset_closure)


/-- The constant of the centring bound. -/
noncomputable def kc3_const (d : ℕ) (σ ε C0 v₀ Cd : ℝ) : ℝ :=
  v₀⁻¹ * Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) * (1 + ε⁻¹) + 2 * kc3_aconst d σ C0)

/-- **Centring for one sample and one scale.** -/
theorem kc3_omega_bound [NeZero d] (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (hΦ : ∀ i j : Fin d, Continuous fun x => fullStreamRecentered omega x i j) {K C0 σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {m : ℕ} (hm : 2 ≤ m) (hK27 : 27 ≤ K) (hKm : K ≤ (3 : ℝ) ^ m)
    (hg : ∀ x : Vec d, matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
      C0 * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + σ)))
    (hwin : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ, (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
      n ≤ m → ∀ Q : TriadicCube d, Q.scale = (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
          matrixOperatorNorm (volumeAverageMat (cubeSet Q)
            (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) ≤
            A * Real.log (B * (m : ℝ)) * (1 / 2 : ℝ) * (m : ℝ) ^ σ)
    {r M₁ M₂ D : ℝ} {W : Set (Vec d)} (hU : IsUniformC11Domain W r M₁ M₂ D) (hWQ : W ⊆ kc2_Q0 d)
    {v₀ Cd : ℝ} (hv₀ : 0 < v₀) (hv : v₀ ≤ (volume W).toReal) (hCd : 0 ≤ Cd)
    (hdecay : ∀ t : ℕ, (∫ x, |kc2_incr (kc2_μ d) (kc2_sig d) (W.indicator (fun _ => (1 : ℝ))) t x|
        ∂(kc2_μ d) ≤ Cd * (1 / 3 : ℝ) ^ t) ∧
      ∫ x, |W.indicator (fun _ => (1 : ℝ)) x -
        ((kc2_μ d)[W.indicator (fun _ => (1 : ℝ)) | kc2_sig d t]) x| ∂(kc2_μ d) ≤
          Cd * (1 / 3 : ℝ) ^ t)
    (i j : Fin d) :
    |volumeAverage ((3 : ℝ) ^ m • W) (fun y => fullStreamRecentered omega y i j) -
        volumeAverage (cubeSet (originCube d (m : ℤ))) (fun y => fullStreamRecentered omega y i j)| ≤
      kc3_const d σ ε C0 v₀ Cd * (m : ℝ) ^ (σ + ε) ∧
    |volumeAverage ((3 : ℝ) ^ m • W)
          (fun y => centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y i j) -
        volumeAverage (cubeSet (originCube d (m : ℤ)))
          (fun y => centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y i j)| ≤
      kc3_const d σ ε C0 v₀ Cd * (m : ℝ) ^ (σ + ε) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set k : Vec d → Mat d := centeredStreamField omega (cubeSet (originCube d (m : ℤ))) with hkdef
  set Φ : Vec d → Mat d := fullStreamRecentered omega with hΦdef
  have hkΦ : ∀ x, k x = Φ x + k 0 := fun x => by
    have := SuperdiffusionCLT.Section2.Estimates.Stream.centeredStreamField_sub_eq_tsum omega hguard m x 0
    have h2 : k x - k 0 = Φ x := this
    rw [← h2]; abel
  have hkc : Continuous fun x => k x i j := by
    have : (fun x => k x i j) = fun x => Φ x i j + k 0 i j := funext fun x => by
      rw [hkΦ x]; rfl
    rw [this]; exact (hΦ i j).add continuous_const
  have hgrow : ∀ x ∈ cubeSet (originCube d (m : ℤ)),
      matrixOperatorNorm (Φ x) ≤ kc3_aconst d σ C0 * (m : ℝ) ^ (1 + σ) := fun x hx =>
    kc3_growth_on_cube hm hK27 hKm hg hσ.le hx
  set R0 : ℝ := 2 * (kc3_aconst d σ C0 * (m : ℝ) ^ (1 + σ)) with hR0
  have hosc : ∀ x ∈ cubeSet (originCube d (m : ℤ)), ∀ y ∈ cubeSet (originCube d (m : ℤ)),
      |k x i j - k y i j| ≤ R0 := fun x hx y hy => by
    have e : k x i j - k y i j = Φ x i j - Φ y i j := by
      rw [hkΦ x, hkΦ y]
      simp only [Matrix.add_apply]
      ring
    rw [e]
    have h1 := abs_entry_le_matrixOperatorNorm (Φ x) i j
    have h2 := abs_entry_le_matrixOperatorNorm (Φ y) i j
    have h3 := hgrow x hx
    have h4 := hgrow y hy
    calc |Φ x i j - Φ y i j| ≤ |Φ x i j| + |Φ y i j| := abs_sub _ _
      _ ≤ _ := by linarith only [h1, h2, h3, h4]
  have hcore := kc3_centering_core i j hkc hm hε hwin hosc hU.1 hWQ hv₀ hv hCd
    (fun t => (hdecay t).1) (hdecay m).2
  have hma : 0 ≤ kc3_aconst d σ C0 := kc3_aconst_nonneg d σ C0
  have hdec := kc3_pow_decay (σ := σ) (by omega : 1 ≤ m) hε
  have hbound : v₀⁻¹ * (Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) *
        ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) + R0 * (Cd * (1 / 3 : ℝ) ^ m)) ≤
      kc3_const d σ ε C0 v₀ Cd * (m : ℝ) ^ (σ + ε) := by
    have h1 : R0 * (Cd * (1 / 3 : ℝ) ^ m) ≤ 2 * kc3_aconst d σ C0 * Cd * (m : ℝ) ^ (σ + ε) := by
      have : R0 * (Cd * (1 / 3 : ℝ) ^ m) =
          2 * kc3_aconst d σ C0 * Cd * ((m : ℝ) ^ (1 + σ) * (1 / 3 : ℝ) ^ m) := by
        rw [hR0]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hdec (by positivity)
    have h2 : v₀⁻¹ * (Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) *
        ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) + R0 * (Cd * (1 / 3 : ℝ) ^ m)) ≤
        v₀⁻¹ * (Cd * (((1 - 1 / 3 : ℝ)⁻¹ + ((1 - 1 / 3 : ℝ)⁻¹) ^ 2) *
        ((1 + ε⁻¹) * (m : ℝ) ^ (σ + ε))) + 2 * kc3_aconst d σ C0 * Cd * (m : ℝ) ^ (σ + ε)) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1]) (inv_pos.2 hv₀).le
    refine h2.trans (le_of_eq ?_)
    unfold kc3_const
    ring
  have hk_bound := hcore.trans hbound
  have hcW : (3 : ℝ) ^ m • W ⊆ cubeSet (originCube d (m : ℤ)) := by
    rw [← kc3_smul_Q0]; exact Set.smul_set_mono hWQ
  have hposS : 0 < (volume ((3 : ℝ) ^ m • W)).toReal := by
    rw [kc3_toReal_smul (by positivity)]
    exact mul_pos (by positivity) (lt_of_lt_of_le hv₀ hv)
  have hposT : 0 < (volume (cubeSet (originCube d (m : ℤ)))).toReal := by
    rw [volume_cubeSet_toReal]; exact cubeVolume_pos _
  have hent : Continuous fun y => Φ y i j := hΦ i j
  have hfun : (fun y => k y i j) = fun y => Φ y i j + k 0 i j := funext fun y => by
    rw [hkΦ y]; rfl
  have hS := kc3_avg_add_const (k 0 i j) hposS (kc3_integrableOn_cube hent m hcW)
  have hT := kc3_avg_add_const (k 0 i j) hposT
    (kc3_integrableOn_cube hent m (Set.Subset.refl _))
  rw [← hfun] at hS hT
  have e : volumeAverage ((3 : ℝ) ^ m • W) (fun y => Φ y i j) -
      volumeAverage (cubeSet (originCube d (m : ℤ))) (fun y => Φ y i j) =
      volumeAverage ((3 : ℝ) ^ m • W) (fun y => k y i j) -
      volumeAverage (cubeSet (originCube d (m : ℤ))) (fun y => k y i j) := by
    rw [hS, hT]; ring
  exact ⟨by rw [e]; exact hk_bound, hk_bound⟩


/-- **Centring, almost surely: the form consumed by the first root.** For `σ, ε > 0` and fixed
data `(r, M₁, D, v₀)` of the uniform `C^{1,1}` class there are constants `Cσ`, `Cf` and, for every
admissible law, a measurable random scale `K ≥ 27` with `log K = O_{Γ_{2σ}}(Cσ)` such that almost
surely, for every `m` with `K ≤ 3^m`, every `W ⊆ [-1/2, 1/2)^d` in the class with `|W| ≥ v₀` and
every entry `(i, j)`, the averages of the recentred stream `k - k(0)` (and of the centred stream
`k - (k)_{□_m}`) over `3^m W` and over `□_m` differ by at most `Cf m^{σ+ε}`. -/
theorem kc3_centering_ae (d : ℕ) [NeZero d] (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    (r M₁ D v₀ : ℝ) (hr : 0 < r) (hv₀ : 0 < v₀)
    (hV6 :
        ∃ C₂ : ℝ,
          ∀ s : ℝ, 0 < s → s < 1 →
            ∃ C₀ C₁ : ℝ,
              ∀ p : ℝ, 1 < p →
                ∃ C : ℝ,
                  ∀ P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    (∀ l m n : ℕ, n < m → m ≤ l →
                        (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                          Measurable X ∧
                            Homogenization.IndependentSums.IsBigO P.toMeasure
                              (Homogenization.IndependentSums.gammaSigma 2) X
                              (C * (3 : ℝ) ^ (s * (m : ℝ))) ∧
                            ∀ omega,
                              SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                  (Homogenization.originCube d (l : ℤ)) s
                                  (ENNReal.ofReal p)
                                  (fun x =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega n m x) ≤
                                ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ))
                                    (ENNReal.ofReal p)
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal
                                    (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ)) ∞
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                                    (Homogenization.originCube d (l : ℤ)) s
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega))) ∧
                      (∀ l n : ℕ,
                          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ᵐ omega ∂P.toMeasure,
                                (⨆ M : {M : ℕ // n < M},
                                  SuperdiffusionCLT.Section2.Norms.cubeEuclideanGagliardoESeminorm
                                    (Homogenization.originCube d (l : ℤ)) s 2
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n M.1 x)) ≤
                                  ENNReal.ofReal (X omega)) ∧
                      (∀ delta : ℝ, 0 < delta → delta < 1 →
                          ∀ sigma : ℝ, 0 < sigma →
                            ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                              Measurable Kfun ∧
                                (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
                                Homogenization.IndependentSums.IsBigO P.toMeasure
                                  (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                                  (fun omega => Real.log (Kfun omega))
                                  (C₀ *
                                    (C₁ * delta⁻¹ *
                                        Real.sqrt (sigma⁻¹ *
                                          Real.log (Real.exp 1 + C₂ * delta⁻¹ * sigma⁻¹))) ^
                                      sigma⁻¹) ∧
                                ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                                    ∂P.toMeasure,
                                  (∀ i : ℕ,
                                      Summable fun k : ℕ =>
                                        SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                          (Homogenization.openCubeSet
                                            (Homogenization.originCube d (i : ℤ)))
                                          (omega k)) →
                                    ((∀ m : ℕ,
                                        Kfun omega ≤ (3 : ℝ) ^ m →
                                    (ENNReal.ofReal ((m : ℝ)⁻¹) *
                                          SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                            (Homogenization.originCube d (m : ℤ)) ∞
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ m) *
                                          (∑' k : ℕ,
                                            ENNReal.ofReal
                                              (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                                (Homogenization.openCubeSet
                                                  (Homogenization.originCube d (m : ℤ)))
                                                (omega (m + 1 + k)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                                          SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                            (Homogenization.originCube d (m : ℤ)) s 2
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) ≤
                                      ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                                      ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                                        ∀ n : ℕ,
                                          (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                                            n ≤ m →
                                              ∀ Q : Homogenization.TriadicCube d,
                                                Q.scale = (n : ℤ) →
                                                  Homogenization.cubeCenter Q ∈
                                                      Homogenization.cubeSet
                                                        (Homogenization.originCube d (m : ℤ)) →
                                                    Homogenization.Book.Ch02.matrixOperatorNorm
                                                        (Homogenization.volumeAverageMat
                                                          (Homogenization.cubeSet Q)
                                                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                                            omega
                                                            (Homogenization.cubeSet
                                                              (Homogenization.originCube d (m : ℤ))))) ≤
                                                      A * Real.log (B * (m : ℝ)) * delta *
                                                        (m : ℝ) ^ sigma) ∧
                                      ∀ x : Homogenization.Vec d,
                                  Homogenization.Book.Ch02.matrixOperatorNorm
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) x -
                                          SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                                    C *
                                      Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                                        (2 * (1 + sigma))))) :

    ∃ Cσ Cf : ℝ,
      ∀ P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∃ K : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma (2 * σ))
              (fun omega => Real.log (K omega)) Cσ ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m → ∀ (W : Set (Vec d)) (M₂ : ℝ),
                IsUniformC11Domain W r M₁ M₂ D → W ⊆ kc2_Q0 d → v₀ ≤ (volume W).toReal →
                ∀ i j : Fin d,
                  |volumeAverage ((3 : ℝ) ^ m • W) (fun y => fullStreamRecentered omega y i j) -
                      volumeAverage (cubeSet (originCube d (m : ℤ)))
                        (fun y => fullStreamRecentered omega y i j)| ≤
                    Cf * (m : ℝ) ^ (σ + ε) ∧
                  |volumeAverage ((3 : ℝ) ^ m • W)
                        (fun y => centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y i j) -
                      volumeAverage (cubeSet (originCube d (m : ℤ)))
                        (fun y => centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y i j)| ≤
                    Cf * (m : ℝ) ^ (σ + ε) := by
  obtain ⟨Cd, hCd0, hCd⟩ := kc2_l1_incr_decay (d := d) r M₁ D hr
  obtain ⟨C₂, hC₂⟩ := hV6
  obtain ⟨C₀, C₁, hC₁⟩ := hC₂ (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨C, hC⟩ := hC₁ 2 (by norm_num)
  refine ⟨C₀ * (C₁ * ((1 / 2 : ℝ))⁻¹ *
      Real.sqrt (σ⁻¹ * Real.log (Real.exp 1 + C₂ * ((1 / 2 : ℝ))⁻¹ * σ⁻¹))) ^ σ⁻¹,
    kc3_const d σ ε C v₀ Cd, fun P hPre hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨-, -, hK⟩ := hC P hPre hJ1 hJ2 hJ3 hJ4
  obtain ⟨K, hKm, hK27, hKO, hKae⟩ := hK (1 / 2) (by norm_num) (by norm_num) σ hσ
  refine ⟨K, hKm, hK27, hKO, ?_⟩
  filter_upwards [hKae, ae_forall_summable_shellDerivLinftyNorm_originCube hJ3,
    ae_contDiff_fullStreamRecentered hJ3] with omega h1 hguard hcd m hm W M₂ hU hWQ hv i j
  have h := h1 hguard
  have hm3 : 2 ≤ m := by
    by_contra hlt
    have hle : m ≤ 1 := by omega
    have h3 : (3 : ℝ) ^ m ≤ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) hle
    linarith only [hK27 omega, hm, h3]
  have hg : ∀ x : Vec d, matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
      C * Real.log (K omega ^ 2 + vecNormSq x) ^ (2 * (1 + σ)) := fun x => by
    have h2 := h.2 x
    have h3 := SuperdiffusionCLT.Section2.Estimates.Stream.centeredStreamField_sub_eq_tsum
      omega hguard 0 x 0
    simp only [Nat.cast_zero] at h3
    rw [h3] at h2
    exact h2
  exact kc3_omega_bound omega hguard (fun i j => kc3_entry_continuous hcd i j) hσ hε hm3 (hK27 omega) hm hg
    ((h.1 m hm).2) hU hWQ hv₀ hv hCd0 (fun t => hCd hU hWQ t) i j


/-- **Centring for the dilates of a fixed smooth bounded domain: the form of the root's display
`e.Dir.new.U.centering`.** Let `U ⊆ [-1/2, 1/2)^d` be a smooth bounded domain.  For `σ, ε > 0` there
are constants `Cσ`, `Cf` and, for every admissible law, a random scale `K ≥ 27` (tail `Γ_{2σ}`) such
that almost surely, for every `m` with `K ≤ 3^m` and every `λ ∈ (1/3, 1]`, the operator norm of
`(k)_{RU} - (k)_{□_m}`, `R = 3^m λ`, is at most `Cf m^{σ+ε}`, for the recentred stream matrix
`k - k(0)` and for the centred one `k - (k)_{□_m}` alike. -/
theorem kc3_centering_smooth_ae (d : ℕ) [NeZero d] (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) (hUQ : U ⊆ kc2_Q0 d)
    (hV6 :
        ∃ C₂ : ℝ,
          ∀ s : ℝ, 0 < s → s < 1 →
            ∃ C₀ C₁ : ℝ,
              ∀ p : ℝ, 1 < p →
                ∃ C : ℝ,
                  ∀ P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    (∀ l m n : ℕ, n < m → m ≤ l →
                        (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                          Measurable X ∧
                            Homogenization.IndependentSums.IsBigO P.toMeasure
                              (Homogenization.IndependentSums.gammaSigma 2) X
                              (C * (3 : ℝ) ^ (s * (m : ℝ))) ∧
                            ∀ omega,
                              SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                  (Homogenization.originCube d (l : ℤ)) s
                                  (ENNReal.ofReal p)
                                  (fun x =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega n m x) ≤
                                ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ))
                                    (ENNReal.ofReal p)
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal
                                    (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ)) ∞
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                                    (Homogenization.originCube d (l : ℤ)) s
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega))) ∧
                      (∀ l n : ℕ,
                          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ᵐ omega ∂P.toMeasure,
                                (⨆ M : {M : ℕ // n < M},
                                  SuperdiffusionCLT.Section2.Norms.cubeEuclideanGagliardoESeminorm
                                    (Homogenization.originCube d (l : ℤ)) s 2
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n M.1 x)) ≤
                                  ENNReal.ofReal (X omega)) ∧
                      (∀ delta : ℝ, 0 < delta → delta < 1 →
                          ∀ sigma : ℝ, 0 < sigma →
                            ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                              Measurable Kfun ∧
                                (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
                                Homogenization.IndependentSums.IsBigO P.toMeasure
                                  (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                                  (fun omega => Real.log (Kfun omega))
                                  (C₀ *
                                    (C₁ * delta⁻¹ *
                                        Real.sqrt (sigma⁻¹ *
                                          Real.log (Real.exp 1 + C₂ * delta⁻¹ * sigma⁻¹))) ^
                                      sigma⁻¹) ∧
                                ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                                    ∂P.toMeasure,
                                  (∀ i : ℕ,
                                      Summable fun k : ℕ =>
                                        SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                          (Homogenization.openCubeSet
                                            (Homogenization.originCube d (i : ℤ)))
                                          (omega k)) →
                                    ((∀ m : ℕ,
                                        Kfun omega ≤ (3 : ℝ) ^ m →
                                    (ENNReal.ofReal ((m : ℝ)⁻¹) *
                                          SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                            (Homogenization.originCube d (m : ℤ)) ∞
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ m) *
                                          (∑' k : ℕ,
                                            ENNReal.ofReal
                                              (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                                (Homogenization.openCubeSet
                                                  (Homogenization.originCube d (m : ℤ)))
                                                (omega (m + 1 + k)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                                          SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                            (Homogenization.originCube d (m : ℤ)) s 2
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) ≤
                                      ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                                      ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                                        ∀ n : ℕ,
                                          (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                                            n ≤ m →
                                              ∀ Q : Homogenization.TriadicCube d,
                                                Q.scale = (n : ℤ) →
                                                  Homogenization.cubeCenter Q ∈
                                                      Homogenization.cubeSet
                                                        (Homogenization.originCube d (m : ℤ)) →
                                                    Homogenization.Book.Ch02.matrixOperatorNorm
                                                        (Homogenization.volumeAverageMat
                                                          (Homogenization.cubeSet Q)
                                                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                                            omega
                                                            (Homogenization.cubeSet
                                                              (Homogenization.originCube d (m : ℤ))))) ≤
                                                      A * Real.log (B * (m : ℝ)) * delta *
                                                        (m : ℝ) ^ sigma) ∧
                                      ∀ x : Homogenization.Vec d,
                                  Homogenization.Book.Ch02.matrixOperatorNorm
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) x -
                                          SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                                    C *
                                      Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                                        (2 * (1 + sigma))))) :

    ∃ Cσ Cf : ℝ,
      ∀ P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∃ K : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
              (Homogenization.IndependentSums.gammaSigma (2 * σ))
              (fun omega => Real.log (K omega)) Cσ ∧
            ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
              ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m → ∀ lam : ℝ, 1 / 3 < lam → lam ≤ 1 →
                matrixOperatorNorm
                    (volumeAverageMat ((3 : ℝ) ^ m • (lam • U)) (fullStreamRecentered omega) -
                      volumeAverageMat (cubeSet (originCube d (m : ℤ)))
                        (fullStreamRecentered omega)) ≤ Cf * (m : ℝ) ^ (σ + ε) ∧
                matrixOperatorNorm
                    (volumeAverageMat ((3 : ℝ) ^ m • (lam • U))
                        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) -
                      volumeAverageMat (cubeSet (originCube d (m : ℤ)))
                        (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) ≤
                  Cf * (m : ℝ) ^ (σ + ε) := by
  obtain ⟨r, M₁, M₂, D, hUnif⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  have hr : 0 < r := hUnif.2.1
  have hvolpos : 0 < volume U := hU.1.measure_pos volume hU.2.1.nonempty
  have hvolfin : volume U ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (kc2_Q0 d)) (by rw [kc2_volume_Q0]; exact ENNReal.one_ne_top)
      (measure_mono hUQ)
  have hUpos : 0 < (volume U).toReal := ENNReal.toReal_pos hvolpos.ne' hvolfin
  have hv₀ : 0 < (1 / 3 : ℝ) ^ d * (volume U).toReal := by positivity
  obtain ⟨Cσ, Cf, hmain⟩ := kc3_centering_ae d σ ε hσ hε (r / 3) M₁ (max D 0)
    ((1 / 3 : ℝ) ^ d * (volume U).toReal) (by positivity) hv₀ hV6
  refine ⟨Cσ, (d : ℝ) ^ 2 * Cf, fun P hPre hJ1 hJ2 hJ3 hJ4 => ?_⟩
  obtain ⟨K, hKm, hK27, hKO, hae⟩ := hmain P hPre hJ1 hJ2 hJ3 hJ4
  refine ⟨K, hKm, hK27, hKO, ?_⟩
  filter_upwards [hae] with omega h m hm lam hl0 hl1
  have hl : 0 < lam := by linarith only [hl0]
  have hv : (1 / 3 : ℝ) ^ d * (volume U).toReal ≤ (volume (lam • U)).toReal := by
    rw [kc3_toReal_smul hl]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hl0.le d) hUpos.le
  have h' := h m hm (lam • U) (3 * |M₂|) (kc3_unif_smul hUnif hl0 hl1)
    (kc3_smul_subset_Q0 hUQ hl hl1) hv
  refine ⟨?_, ?_⟩
  · have := kc3_opnorm_of_entries (B := Cf * (m : ℝ) ^ (σ + ε)) fun i j => (h' i j).1
    rwa [← mul_assoc] at this
  · have := kc3_opnorm_of_entries (B := Cf * (m : ℝ) ^ (σ + ε)) fun i j => (h' i j).2
    rwa [← mul_assoc] at this


/-- **Satisfiability.** The window statement supplies `hV6`; the Dirac zero law satisfies the
five law assumptions; the ball of radius `1/4` is a domain of the uniform class inside the unit cube
with positive volume.  So the hypotheses of `kc3_centering_ae` hold together, and its conclusion is
available for the Dirac zero law. -/
example [NeZero d] (hd : 2 ≤ d) :
    ∃ (r M₁ M₂ D v₀ : ℝ) (W : Set (Vec d)), 0 < r ∧ 0 < v₀ ∧ IsUniformC11Domain W r M₁ M₂ D ∧
      W ⊆ kc2_Q0 d ∧ v₀ ≤ (volume W).toReal ∧
      ∃ Cσ Cf : ℝ, ∃ K : ShellSeq d → ℝ, Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
        Homogenization.IndependentSums.IsBigO
          (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure
          (Homogenization.IndependentSums.gammaSigma (2 * 1))
          (fun omega => Real.log (K omega)) Cσ ∧
        ∀ᵐ omega ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
          ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m → ∀ i j : Fin d,
            |volumeAverage ((3 : ℝ) ^ m • W) (fun y => fullStreamRecentered omega y i j) -
                volumeAverage (cubeSet (originCube d (m : ℤ)))
                  (fun y => fullStreamRecentered omega y i j)| ≤
              Cf * (m : ℝ) ^ ((1 : ℝ) + 1) := by
  obtain ⟨r, M₁, M₂, D, hr, hW, hWQ⟩ := kc2_witness_ball (d := d)
  set W : Set (Vec d) := (fun y : Vec d => (1 / 4 : ℝ) • y + 0) '' Section6.euclidBall (d := d) 1
    with hWdef
  have hne : W.Nonempty := by
    refine ⟨(0 : Vec d), ⟨0, ?_, by simp⟩⟩
    show vecNormSq (0 : Vec d) < 1 ^ 2
    simp [vecNormSq, vecDot]
  have hpos : 0 < volume W := hW.1.measure_pos volume hne
  have hfin : volume W ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (kc2_Q0 d)) (by rw [kc2_volume_Q0]; exact ENNReal.one_ne_top)
      (measure_mono hWQ)
  have hv : 0 < (volume W).toReal := ENNReal.toReal_pos hpos.ne' hfin
  obtain ⟨Cσ, Cf, hC⟩ := kc3_centering_ae d 1 1 one_pos one_pos r M₁ D (volume W).toReal hr hv
    (SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d)
  obtain ⟨K, hK, h27, hO, hae⟩ := hC _ (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ1Restriction_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw
  refine ⟨r, M₁, M₂, D, (volume W).toReal, W, hr, hv, hW, hWQ, le_rfl, Cσ, Cf, K, hK, h27, hO, ?_⟩
  filter_upwards [hae] with omega h m hm i j
  exact (h m hm W M₂ hW hWQ le_rfl i j).1


/-- **Satisfiability of `kc3_centering_smooth_ae`**: the ball of radius `1/4` is a smooth bounded
domain inside the unit cube, and the Dirac zero law meets the law assumptions. -/
example [NeZero d] (hd : 2 ≤ d) :
    ∃ U : Set (Vec d), IsSmoothBoundedDomain U ∧ U ⊆ kc2_Q0 d ∧
      ∃ Cσ Cf : ℝ, ∃ K : ShellSeq d → ℝ, Measurable K ∧ (∀ omega, (27 : ℝ) ≤ K omega) ∧
        Homogenization.IndependentSums.IsBigO
          (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure
          (Homogenization.IndependentSums.gammaSigma (2 * 1))
          (fun omega => Real.log (K omega)) Cσ ∧
        ∀ᵐ omega ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
          ∀ m : ℕ, K omega ≤ (3 : ℝ) ^ m → ∀ lam : ℝ, 1 / 3 < lam → lam ≤ 1 →
            matrixOperatorNorm
                (volumeAverageMat ((3 : ℝ) ^ m • (lam • U)) (fullStreamRecentered omega) -
                  volumeAverageMat (cubeSet (originCube d (m : ℤ)))
                    (fullStreamRecentered omega)) ≤ Cf * (m : ℝ) ^ ((1 : ℝ) + 1) := by
  obtain ⟨r, M₁, M₂, D, hr, hW, hWQ⟩ := kc2_witness_ball (d := d)
  have hset : (fun x : Vec d => 0 + (1 / 4 : ℝ) • x) '' Section6.euclidBall (d := d) 1 =
      (fun y : Vec d => (1 / 4 : ℝ) • y + 0) '' Section6.euclidBall (d := d) 1 := by
    congr 1
    funext x
    simp
  have hU : IsSmoothBoundedDomain ((fun x : Vec d => 0 + (1 / 4 : ℝ) • x) ''
      Section6.euclidBall (d := d) 1) :=
    w0_isSmoothBoundedDomain_affineImage isSmoothBoundedDomain_euclidBall (by norm_num) 0
  rw [hset] at hU
  obtain ⟨Cσ, Cf, hC⟩ := kc3_centering_smooth_ae d 1 1 one_pos one_pos hU hWQ
    (SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d)
  obtain ⟨K, hK, h27, hO, hae⟩ := hC _ (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ1Restriction_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw
  refine ⟨_, hU, hWQ, Cσ, Cf, K, hK, h27, hO, ?_⟩
  filter_upwards [hae] with omega h m hm lam hl0 hl1
  exact (h m hm lam hl0 hl1).1

end SuperdiffusionCLT.Section7
