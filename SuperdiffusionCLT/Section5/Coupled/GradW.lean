/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.RemainderB
public import SuperdiffusionCLT.Section5.Principal.AverageMomentD
public import SuperdiffusionCLT.Section5.Response.Assembly

/-!
# The product `hshell ∇w_D` of `lem.coupled.input`

display `e.coupled.hgradw`:
`E ‖hshell ∇w_D‖²_{L̲²(cu_K)} ≤ C shom_{m-h}^{-2} h²`.

The proof is Hölder on the cube (`L⁴ × L⁴ → L²`), the exponent downgrade `L⁸ → L⁴`, and a weighted
AM-GM in `ω` between the `L⁸` increment moment (`h^{1/2}`) and the `L⁸` gradient moment
(`shom^{-1} h^{1/2}`). No measurability of the response family is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open scoped ENNReal NNReal
open scoped Matrix.Norms.L2Operator
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms (cubeLpENorm)
open SuperdiffusionCLT.Section3.ResponseFields (vecCubeLpENorm)

variable {d : ℕ}

/-- The gradient of an `H¹` function on the open cube is strongly measurable for the normalized
cube measure. -/
private theorem coupled2_aesm_grad {Q : TriadicCube d} (u : H1Function (openCubeSet Q)) :
    AEStronglyMeasurable (hilbertifyVecField u.grad) (normalizedCubeMeasure Q) := by
  have h : AEStronglyMeasurable (hilbertifyVecField u.grad)
      (volume.restrict (openCubeSet Q)) :=
    (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2).aestronglyMeasurable
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h.smul_measure _

instance coupled2_holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 where
  inv_add_inv_eq_inv := by
    have h : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← two_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Hölder on one cube: `‖H G‖_{L̲²} ≤ ‖H‖_{L̲⁴} ‖G‖_{L̲⁴}` for a continuous matrix field `H`. -/
theorem coupled2_holder_matVec {Q : TriadicCube d} {H : Vec d → Mat d} (hH : Continuous H)
    {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 (fun x => matVecMul (H x) (G x)) ≤
      cubeLpENorm Q 4 H * vecCubeLpENorm Q 4 G := by
  have hHn : Continuous (fun x => ‖H x‖) := hH.norm
  have hGn : AEStronglyMeasurable (fun x => ‖hilbertifyVecField G x‖) (normalizedCubeMeasure Q) :=
    hG.norm
  have h1 : vecCubeLpENorm Q 2 (fun x => matVecMul (H x) (G x)) ≤
      eLpNorm (fun x => ‖H x‖ * ‖hilbertifyVecField G x‖) 2 (normalizedCubeMeasure Q) := by
    unfold vecCubeLpENorm cubeLpENorm
    refine eLpNorm_mono_ae
      (SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_matVecMul hH hG)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [SuperdiffusionCLT.Section3.ResponseFields.norm_hilbertifyVecField_apply,
      Real.norm_eq_abs, SuperdiffusionCLT.Section3.ResponseFields.norm_hilbertifyVecField_apply]
    refine (Homogenization.Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _).trans ?_
    exact le_abs_self _
  refine h1.trans ?_
  have h2 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (μ := normalizedCubeMeasure Q)
    (p := 4) (q := 4) (r := 2) (fun a b : ℝ => a * b) 1 continuous_mul hHn.aestronglyMeasurable hGn
    (Filter.Eventually.of_forall fun x => by simp [enorm_mul])
  rw [one_mul] at h2
  refine h2.trans (le_of_eq ?_)
  unfold vecCubeLpENorm cubeLpENorm
  rw [eLpNorm_norm _ hH.aestronglyMeasurable, eLpNorm_norm _ hG]

/-- The `L⁸(μ)` moment gives the `L⁴(μ)` moment (weighted AM-GM, no measurability of `X`). -/
theorem coupled2_pow_four_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ≥0∞) {B : ℝ} (hB : 0 < B)
    (h8 : ∫⁻ ω, (X ω) ^ (8 : ℕ) ∂μ ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ ω, (X ω) ^ (4 : ℕ) ∂μ ≤ 2 * ENNReal.ofReal (B ^ 4) := by
  set t : ℝ≥0∞ := ENNReal.ofReal (B ^ 4) with ht
  have ht0 : t ≠ 0 := by
    rw [ht]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htt : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ ω, (X ω) ^ (4 : ℕ) ≤ t + t⁻¹ * (X ω) ^ (8 : ℕ) := by
    intro ω
    have h2 := ennreal_mul_le_amgm 1 ((X ω) ^ (4 : ℕ)) t ht0 htt
    calc (X ω) ^ (4 : ℕ) = 1 * (X ω) ^ (4 : ℕ) := (one_mul _).symm
      _ ≤ _ := h2.trans (by
          refine le_of_eq ?_
          rw [one_pow, mul_one, ← pow_mul])
  calc ∫⁻ ω, (X ω) ^ (4 : ℕ) ∂μ
      ≤ ∫⁻ ω, (t + t⁻¹ * (X ω) ^ (8 : ℕ)) ∂μ := lintegral_mono hpt
    _ = t + t⁻¹ * ∫⁻ ω, (X ω) ^ (8 : ℕ) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht0)]
    _ ≤ t + t⁻¹ * ENNReal.ofReal (B ^ 8) := by gcongr
    _ = 2 * t := by
        have e8 : ENNReal.ofReal (B ^ 8) = t * t := by
          rw [ht, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        rw [e8, ← mul_assoc, ENNReal.inv_mul_cancel ht0 htt, one_mul, two_mul]

/-- From `I^{1/8} ≤ ofReal B` to `I ≤ ofReal (B^8)`. -/
theorem coupled2_le_of_rpow_eighth {I : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B)
    (hI : I ^ ((1 : ℝ) / 8) ≤ ENNReal.ofReal B) : I ≤ ENNReal.ofReal (B ^ 8) := by
  have := ENNReal.rpow_le_rpow hI (by norm_num : (0 : ℝ) ≤ 8)
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hB (by norm_num)] at this
  simpa [Real.rpow_natCast] using this

/-- **`e.coupled.hgradw`**: `E ‖hshell ∇w_D‖²_{L̲²(cu_K)} ≤ C shom_{m-h}^{-2} h²`.
The Neumann response of the gradient clause is produced internally, so it is not a binder. -/
theorem coupled_hgradw (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ2 d P →
        ShellLawJ3 d P → ShellLawJ1Restriction d P → ShellLawJ4 d P →
      ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
      ∀ e : Vec d, vecNormSq e ≤ 1 →
      ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ)))),
        (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
          (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
        ∫⁻ ω, (vecCubeLpENorm (originCube d (Kc : ℤ)) 2
            (fun x => matVecMul (finiteShellIncrement ω (m - h) m x)
              ((wD ω).toH1Function.grad x))) ^ (2 : ℕ) ∂P.toMeasure ≤
          ENNReal.ofReal (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^
            (-(2 : ℝ)) * (h : ℝ) ^ 2) := by
  obtain ⟨Cg, hCg1, HG⟩ := response_gradient_L8 d hd
  obtain ⟨Cz, hCz0, HZ⟩ := increment_L8_majorant d
  refine ⟨2 * (Cz + 1) ^ 4 + 2 * Cg ^ 4, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ Cg ^ 4 := one_le_pow₀ hCg1
    have h2 : 0 ≤ (Cz + 1) ^ 4 := by positivity
    linarith only [h1, h2]
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he wD hwD
  have hσ : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  set σ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P with hσdef
  obtain ⟨Z, hZm, hZle, hZint⟩ := HZ P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh (by omega) (by omega)
  obtain ⟨wD0, wN, -, hwN⟩ := exists_responses_hshellFlux (d := d) nu P m h Kc e
  have hG8 := HG nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he wD wN hwD hwN
  set r : ℝ := (h : ℝ) ^ ((1 : ℝ) / 2) with hr
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh
  have hrpos : 0 < r := Real.rpow_pos_of_pos hhpos _
  have hr2 : r ^ 2 = h := by
    rw [hr, ← Real.sqrt_eq_rpow, Real.sq_sqrt hhpos.le]
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  set Bz : ℝ := (Cz + 1) * r with hBz
  set Bg : ℝ := Cg * σ⁻¹ * r with hBg
  have hBzpos : 0 < Bz := by positivity
  have hBgpos : 0 < Bg := by
    have : 0 < Cg := by linarith only [hCg1]
    positivity
  -- moment of the increment majorant
  have hZ8 : ∫⁻ ω, (Z ω) ^ (8 : ℕ) ∂P.toMeasure ≤ ENNReal.ofReal (Bz ^ 8) := by
    refine hZint.trans ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Cz * r ≤ Bz := by rw [hBz]; nlinarith only [hrpos]
    exact pow_le_pow_left₀ (by positivity) this 8
  have hZ4 := coupled2_pow_four_le (μ := P.toMeasure) Z hBzpos hZ8
  -- moment of the gradient
  set V : ShellSeq d → ℝ≥0∞ := fun ω => vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD ω).toH1Function.grad with hV
  have hV8 : ∫⁻ ω, (V ω) ^ (8 : ℕ) ∂P.toMeasure ≤ ENNReal.ofReal (Bg ^ 8) := by
    refine le_trans (lintegral_mono fun ω => (le_self_add : (V ω) ^ (8 : ℕ) ≤ (V ω) ^ (8 : ℕ) +
      (vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wN ω).toH1Function.grad) ^ (8 : ℕ))) ?_
    exact coupled2_le_of_rpow_eighth hBgpos.le hG8
  have hV4 := coupled2_pow_four_le (μ := P.toMeasure) V hBgpos hV8
  -- pointwise
  set t : ℝ≥0∞ := ENNReal.ofReal (σ⁻¹ ^ 2) with ht
  have ht0 : t ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htt : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : ∀ ω, (vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (fun x => matVecMul (finiteShellIncrement ω (m - h) m x)
      ((wD ω).toH1Function.grad x))) ^ (2 : ℕ) ≤ t * (Z ω) ^ (4 : ℕ) + t⁻¹ * (V ω) ^ (4 : ℕ) := by
    intro ω
    have hcont := coupled_continuous_finiteShellIncrement (d := d) (m - h) m ω
    have h1 := coupled2_holder_matVec (Q := originCube d (Kc : ℤ)) hcont (coupled2_aesm_grad (wD ω).toH1Function)
    have h48 : cubeLpENorm (originCube d (Kc : ℤ)) 4 (fun x => finiteShellIncrement ω (m - h) m x) ≤
        cubeLpENorm (originCube d (Kc : ℤ)) 8 (fun x => finiteShellIncrement ω (m - h) m x) :=
      SuperdiffusionCLT.Section3.Terms.cubeLpENorm_mono_exponent (originCube d (Kc : ℤ))
        (by norm_num) hcont.aestronglyMeasurable
    have hZ' : cubeLpENorm (originCube d (Kc : ℤ)) 4 (fun x => finiteShellIncrement ω (m - h) m x) ≤ Z ω :=
      h48.trans (hZle ω)
    have hV' : vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (wD ω).toH1Function.grad ≤ V ω :=
      SuperdiffusionCLT.Section3.Terms.vecCubeLpENorm_mono_exponent
        (originCube d (Kc : ℤ)) (by norm_num) (coupled2_aesm_grad (wD ω).toH1Function)
    have h2 : vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (fun x => matVecMul (finiteShellIncrement ω (m - h) m x)
        ((wD ω).toH1Function.grad x)) ≤ Z ω * V ω := h1.trans (mul_le_mul' hZ' hV')
    have h3 := ennreal_mul_le_amgm ((Z ω) ^ 2) ((V ω) ^ 2) t ht0 htt
    calc _ ≤ (Z ω * V ω) ^ (2 : ℕ) := pow_le_pow_left' h2 2
      _ = (Z ω) ^ 2 * (V ω) ^ 2 := mul_pow _ _ _
      _ ≤ _ := h3.trans (le_of_eq (by rw [← pow_mul, ← pow_mul]))
  calc _ ≤ ∫⁻ ω, (t * (Z ω) ^ (4 : ℕ) + t⁻¹ * (V ω) ^ (4 : ℕ)) ∂P.toMeasure :=
        lintegral_mono hpt
    _ = t * ∫⁻ ω, (Z ω) ^ (4 : ℕ) ∂P.toMeasure + t⁻¹ * ∫⁻ ω, (V ω) ^ (4 : ℕ) ∂P.toMeasure := by
        rw [lintegral_add_left ((hZm.pow_const 4).const_mul t), lintegral_const_mul' _ _ htt,
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht0)]
    _ ≤ t * (2 * ENNReal.ofReal (Bz ^ 4)) + t⁻¹ * (2 * ENNReal.ofReal (Bg ^ 4)) := by gcongr
    _ = ENNReal.ofReal (2 * σ⁻¹ ^ 2 * Bz ^ 4 + 2 * (σ⁻¹ ^ 2)⁻¹ * Bg ^ 4) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [ht, ← ENNReal.ofReal_inv_of_pos (by positivity), h2,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hrp : (σ ^ (-(2 : ℝ))) = (σ ^ 2)⁻¹ := by
          rw [Real.rpow_neg hσ.le, Real.rpow_two]
        have hh2 : ((h : ℝ)) ^ 2 = (r ^ 2) ^ 2 := by rw [hr2]
        rw [hrp, hh2, hBz, hBg]
        apply le_of_eq
        field_simp

/-- **Satisfiability witness.** The scale and response hypotheses of `coupled_hgradw` are met
together at `(m, h, Kc) = (400, 1, 40000)` with `e = 0`. -/
example [NeZero d] (nu : ℝ) (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) :
    ∃ m h Kc : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 100 * m ≤ Kc ∧
      ∃ e : Vec d, vecNormSq e ≤ 1 ∧
        ∃ wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))),
          ∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega) := by
  refine ⟨400, 1, 40000, by norm_num, by norm_num, by norm_num, 0, ?_, ?_⟩
  · simp [vecNormSq, vecDot]
  · obtain ⟨wD, _, hD, _⟩ := exists_responses_hshellFlux nu P 400 1 40000 (0 : Vec d)
    exact ⟨wD, hD⟩

end SuperdiffusionCLT.Section5
