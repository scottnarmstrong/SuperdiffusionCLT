/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.CaccCube
public import SuperdiffusionCLT.Section6.Engine.PoincCube
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox

/-!
# Gradient-free harmonic approximation on an origin cube

Composition of the coarse Caccioppoli estimate on `cu_t` with the deterministic harmonic
approximation on `cu_{t-2}`, applied to the restriction of the solution.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

theorem ea4_cubeLpENorm_congr_ae (Q : TriadicCube d) (p : ENNReal) {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q p f =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q p g := by
  unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
  rw [MeasureTheory.eLpNorm_congr_ae]
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  refine MeasureTheory.Measure.ae_smul_measure ?_ _
  rw [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h

theorem eng_harmonic_cube (d : ℕ) [NeZero d] (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (t : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu delta : ℝ}, 3 ≤ t →
        IsEllipticFieldOn lam Lam (cubeSet (originCube d (t : ℤ))) a → 0 < lam → lam ≤ Lam →
        0 < sigma → 0 < nu →
        (∀ x ∈ cubeSet (originCube d (t : ℤ)), symmPart (a x) = nu • (1 : Mat d)) →
        sigma⁻¹ * LambdaSq (originCube d (t : ℤ)) (1 / 4) (MultiscaleExponent.finite 1) a +
            sigma * (lambdaSq (originCube d (t : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) a)⁻¹ ≤ B →
        HomogenizationErrorOnCube (originCube d ((t : ℤ) - 2)) (1 / 9)
            MultiscaleExponent.infinity (MultiscaleExponent.finite 2) a
            (sigma • (1 : Mat d)) ≤ delta →
        0 ≤ delta →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d t) u g →
          ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
            IsSolOn (fun _ => (1 : Mat d)) (engCube d (t - 3)) w gw ∧
              cubeL2 (t - 3) (fun x => u x - w x) ≤ C * delta * (3 : ℝ) ^ t * cubeFlat t u := by
  obtain ⟨Cc, hCc, hcacc⟩ := eng_cacc_cube d B hB
  obtain ⟨Ch, hCh, hharm⟩ := HarmonicApprox.harmonic_approximation_deterministic d
  refine ⟨max 1 (Ch * Cc), le_max_left _ _, ?_⟩
  intro t lam Lam a sigma nu delta ht hEll h0 hle hs hnu hsym hBd hdelta hd0 u g hsol
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
  have e1 : s + 3 - 2 = s + 1 := by omega
  have e2 : ((s + 1 : ℕ) : ℤ) - 1 = (s : ℤ) := by push_cast; ring
  have e3 : ((s + 3 : ℕ) : ℤ) - 2 = ((s + 1 : ℕ) : ℤ) := by push_cast; ring
  have hgrad := hcacc (s + 3) (by omega) hEll h0 hle hs hnu hsym hBd u g hsol
  rw [e1] at hgrad
  have hsubC : cubeSet (originCube d ((s + 1 : ℕ) : ℤ)) ⊆ cubeSet (originCube d ((s + 3 : ℕ) : ℤ)) := by
    have h1 := HarmonicApprox.originCube_pred_cubeSet_subset (d := d) ((s + 3 : ℕ) : ℤ)
    have h2 := HarmonicApprox.originCube_pred_cubeSet_subset (d := d) (((s + 3 : ℕ) : ℤ) - 1)
    have e4 : ((s + 3 : ℕ) : ℤ) - 1 - 1 = ((s + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e4] at h2
    exact h2.trans h1
  have hsubO : engCube d (s + 1) ⊆ engCube d (s + 3) := by
    have := ea1_engCube_subset (d := d) (s + 3) (by omega)
    rwa [e1] at this
  have hsubO' : engCube d s ⊆ engCube d (s + 1) := by
    have := HarmonicApprox.originCube_pred_openCubeSet_subset (d := d) ((s + 1 : ℕ) : ℤ)
    rwa [e2] at this
  have hEll' : IsEllipticFieldOn lam Lam (cubeSet (originCube d ((s + 1 : ℕ) : ℤ))) a :=
    hEll.mono (measurableSet_cubeSet _) hsubC
  have hsym' : ∀ x ∈ cubeSet (originCube d ((s + 1 : ℕ) : ℤ)), symmPart (a x) = nu • (1 : Mat d) :=
    fun x hx => hsym x (hsubC hx)
  have hsol' : IsSolOn a (engCube d (s + 1)) u g :=
    hsol.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _) hsubO (volume_openCubeSet_lt_top _).ne
      ⟨lam, Lam, hEll.mono (measurableSet_openCubeSet _)
        (hsubO.trans (openCubeSet_subset_cubeSet _))⟩
  obtain ⟨-, hg2⟩ := hsol'.memLp
  obtain ⟨v, hv1, hv2⟩ := hsol'
  have hH := hharm (delta := delta) ((s + 1 : ℕ) : ℤ) hEll' hs hnu hsym' (by simpa only [e3] using hdelta)
  rw [e2] at hH
  obtain ⟨w, hw⟩ := hH v
  have hv1' : v.toH1.toFun =ᵐ[volume.restrict (engCube d s)] u :=
    ae_restrict_of_ae_restrict_of_subset hsubO' hv1
  refine ⟨w.toH1.toFun, w.toH1.grad, ⟨w, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩, ?_⟩
  have hG : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d ((s + 1 : ℕ) : ℤ)) 2
      (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d ((s + 1 : ℕ) : ℤ)) 2
      (fun x => engNorm (g x)) := by
    refine ea4_cubeLpENorm_congr_ae _ _ ?_
    filter_upwards [hv2] with x hx
    rw [hx]
    rfl
  have hGfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d ((s + 1 : ℕ) : ℤ)) 2 (fun x => engNorm (g x)) ≠ ⊤ :=
    hg2.eLpNorm_lt_top.ne
  rw [hG] at hw
  have hW0 : 0 ≤ (3 : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) := by positivity
  have hsq : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hs
  have hsn : 0 < Real.sqrt nu := Real.sqrt_pos.2 hnu
  have hR0 : 0 ≤ Ch * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu := by positivity
  have hmono := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin) hw
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hW0,
    ENNReal.toReal_ofReal hR0] at hmono
  have hL : SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d (s : ℤ)) 2 (fun x => v.toH1.toFun x - w.toH1.toFun x) =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (s : ℤ)) 2
      (fun x => u x - w.toH1.toFun x) := by
    refine ea4_cubeLpENorm_congr_ae _ _ ?_
    filter_upwards [hv1'] with x hx
    rw [hx]
  rw [hL] at hmono
  change (3 : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) * cubeL2 s (fun x => u x - w.toH1.toFun x) ≤
    (Ch * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) * cubeGradL2 (s + 1) g at hmono
  set L := cubeL2 s (fun x => u x - w.toH1.toFun x) with hLdef
  set X := cubeGradL2 (s + 1) g with hXdef
  set F := cubeFlat (s + 3) u with hFdef
  have hF0 : 0 ≤ F := cubeFlat_nonneg _ _
  have hX0 : 0 ≤ X := cubeL2_nonneg _ _
  have hp : (0 : ℝ) < (3 : ℝ) ^ (s + 1) := by positivity
  have hneg : (3 : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) = ((3 : ℝ) ^ (s + 1))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hneg] at hmono
  have hL1 : L ≤ (3 : ℝ) ^ (s + 1) *
      ((Ch * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) * X) := by
    have := mul_le_mul_of_nonneg_left hmono hp.le
    rwa [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at this
  have hsd : Real.sqrt (sigma / nu) = Real.sqrt sigma / Real.sqrt nu := Real.sqrt_div hs.le nu
  have hX1 : X ≤ Cc * (Real.sqrt sigma / Real.sqrt nu) * F := by rw [← hsd]; exact hgrad
  have hkey : (Ch * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) * X ≤ (Ch * Cc) * delta * F := by
    have h1 := mul_le_mul_of_nonneg_left hX1 hR0
    refine h1.trans (le_of_eq ?_)
    field_simp
  have hp3 : (3 : ℝ) ^ (s + 1) ≤ (3 : ℝ) ^ (s + 3) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hCm : Ch * Cc ≤ max 1 (Ch * Cc) := le_max_right _ _
  have hCC : 0 ≤ Ch * Cc * delta * F := by positivity
  calc L ≤ (3 : ℝ) ^ (s + 1) * ((Ch * Cc) * delta * F) :=
        hL1.trans (mul_le_mul_of_nonneg_left hkey hp.le)
    _ ≤ (3 : ℝ) ^ (s + 3) * ((Ch * Cc) * delta * F) := mul_le_mul_of_nonneg_right hp3 hCC
    _ ≤ (3 : ℝ) ^ (s + 3) * (max 1 (Ch * Cc) * delta * F) := by
        gcongr
    _ = max 1 (Ch * Cc) * delta * (3 : ℝ) ^ (s + 3) * F := by ring

/-- Witness: the numerical hypotheses of `eng_harmonic_cube` hold for the identity field on
`□_3`, with `σ = ν = 1`, a suitable `B` and `δ`, and the zero solution. -/
example (d : ℕ) [NeZero d] : ∃ B delta : ℝ, 1 ≤ B ∧ 0 ≤ delta ∧
    IsEllipticFieldOn 1 1 (cubeSet (originCube d ((3 : ℕ) : ℤ))) (constantCoeffField (1 : Mat d)) ∧
    (∀ x ∈ cubeSet (originCube d ((3 : ℕ) : ℤ)),
      symmPart (constantCoeffField (1 : Mat d) x) = (1 : ℝ) • (1 : Mat d)) ∧
    (1 : ℝ)⁻¹ * LambdaSq (originCube d ((3 : ℕ) : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
        (constantCoeffField (1 : Mat d)) +
      1 * (lambdaSq (originCube d ((3 : ℕ) : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
        (constantCoeffField (1 : Mat d)))⁻¹ ≤ B ∧
    HomogenizationErrorOnCube (originCube d (((3 : ℕ) : ℤ) - 2)) (1 / 9)
        MultiscaleExponent.infinity (MultiscaleExponent.finite 2) (constantCoeffField (1 : Mat d))
        ((1 : ℝ) • (1 : Mat d)) ≤ delta ∧
    IsSolOn (constantCoeffField (1 : Mat d)) (engCube d 3) (fun _ => 0) (fun _ => 0) := by
  refine ⟨max 1 ((1 : ℝ)⁻¹ * LambdaSq (originCube d ((3 : ℕ) : ℤ)) (1 / 4)
      (MultiscaleExponent.finite 1) (constantCoeffField (1 : Mat d)) +
    1 * (lambdaSq (originCube d ((3 : ℕ) : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
      (constantCoeffField (1 : Mat d)))⁻¹),
    max 0 (HomogenizationErrorOnCube (originCube d (((3 : ℕ) : ℤ) - 2)) (1 / 9)
        MultiscaleExponent.infinity (MultiscaleExponent.finite 2) (constantCoeffField (1 : Mat d))
        ((1 : ℝ) • (1 : Mat d))), le_max_left _ _, le_max_left _ _, regEllipticity_witness _, ?_,
    le_max_right _ _, le_max_right _ _, ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl,
      Filter.EventuallyEq.rfl⟩⟩
  intro x _
  show symmPart (1 : Mat d) = _
  ext i j
  by_cases h : i = j
  · subst h
    simp [symmPart]
  · simp [symmPart, h, Ne.symm h]

end

end SuperdiffusionCLT.Section6
