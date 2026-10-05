/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AverageMomentD
public import SuperdiffusionCLT.Section5.Response.ResponseData
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne

/-!
# `e.principal.uz`

`(avsum_z E[|e_{D,z}|⁸ + |e_{N,z}|⁸ + |shom⁻¹ hbar_z|⁸])^{1/8} ≤ C (1 + shom⁻¹ h^{1/2})`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite sigmaBarInfinite_pos)
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

theorem vecNorm_le_one_of_vecNormSq_le {v : Vec d} (h : vecNormSq v ≤ 1) : vecNorm v ≤ 1 := by
  have h0 := vecNorm_nonneg v
  have h2 := vecNorm_sq_eq_vecNormSq v
  nlinarith only [h0, h2, h]

/-- The real inequality closing `principal_uz`. -/
theorem uz_real_bound {Ccr Ar Cz t : ℝ} (hC : 0 ≤ Ccr) (hA : 0 ≤ Ar) (ht : 0 ≤ t) :
    Ccr * (1 + Ar * (Cz * t) ^ 8) ≤ ((1 + Ccr * (1 + Ar * Cz ^ 8)) * (1 + t)) ^ 8 := by
  set C0 := Ccr * (1 + Ar * Cz ^ 8) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  have h1 : (1 : ℝ) ≤ (1 + t) ^ 8 := one_le_pow₀ (by linarith only [ht])
  have h2 : t ^ 8 ≤ (1 + t) ^ 8 := pow_le_pow_left₀ ht (by linarith only) 8
  have hP : 0 ≤ Ar * Cz ^ 8 := by positivity
  have h3 : Ccr * (1 + Ar * (Cz * t) ^ 8) ≤ C0 * (1 + t) ^ 8 := by
    rw [mul_pow, hC0]
    have : Ar * (Cz ^ 8 * t ^ 8) = (Ar * Cz ^ 8) * t ^ 8 := by ring
    rw [this]
    have e : Ccr * (1 + Ar * Cz ^ 8) * (1 + t) ^ 8 =
        Ccr * (1 + t) ^ 8 + Ccr * ((Ar * Cz ^ 8) * (1 + t) ^ 8) := by ring
    rw [e, mul_add, mul_one]
    exact add_le_add (by nlinarith only [h1, hC]) (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 hP) hC)
  have hCge : (1 : ℝ) ≤ 1 + C0 := by linarith only [hC00]
  have h4 : C0 * (1 + t) ^ 8 ≤ (1 + C0) ^ 8 * (1 + t) ^ 8 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc C0 ≤ 1 + C0 := by linarith only
      _ = (1 + C0) ^ 1 := (pow_one _).symm
      _ ≤ (1 + C0) ^ 8 := pow_le_pow_right₀ hCge (by norm_num)
  exact (h3.trans h4).trans_eq (mul_pow _ _ _).symm

/-- **`e.principal.uz`**. -/
theorem principal_uz (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        ∀ m h Kc n : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc → n ≤ Kc →
        ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
        ∀ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H10Function (openCubeSet (originCube d (Kc : ℤ))))
          (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
          (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
            (hshellFlux nu P m h omega e) (wD omega)) →
          (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
            (hshellFlux nu P m h omega e') (wN omega)) →
          (subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
              (vecNorm (principalED Q e' (wD omega).toH1Function.grad) ^ 8 +
                vecNorm (principalEN Q e (fun y => (wN omega).toH1Function.grad y +
                  hshellFlux nu P m h omega e' y)) ^ 8 +
                matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ •
                  principalGauge m h Q omega) ^ 8) ∂P.toMeasure)) ^ ((1 : ℝ) / 8) ≤
            ENNReal.ofReal (C * (1 + (sigmaBarInfinite nu (m - h) P)⁻¹ *
              (h : ℝ) ^ ((1 : ℝ) / 2))) := by
  obtain ⟨Cap, hCapTop, hAp⟩ := SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd
  obtain ⟨Cz, hCz0, hZ⟩ := increment_L8_majorant d
  set Ccr : ℝ := 2 ^ 15 + ((d : ℝ) * d) ^ 8 with hCcr
  set Ar : ℝ := 2 * Cap.toReal ^ 8 + 1 with hAr
  have hCcr0 : 0 ≤ Ccr := by positivity
  have hAr0 : 0 ≤ Ar := by positivity
  refine ⟨1 + Ccr * (1 + Ar * Cz ^ 8), by have : 0 ≤ Ccr * (1 + Ar * Cz ^ 8) := by positivity
                                          linarith only [this], ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc n hh h400 h100 hnK e e' he he' wD wN hwD hwN
  have hσ : 0 < sigmaBarInfinite nu (m - h) P := sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  have hhm : h ≤ m := by omega
  have hmK : m ≤ Kc := by omega
  obtain ⟨Z, hZm, hZle, hZint⟩ := hZ P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh hhm hmK
  obtain ⟨wD0, wN0, hD0, hN0, _⟩ := exists_response_data hd nu P m h Kc e
  obtain ⟨wD1, wN1, hD1, hN1, _⟩ := exists_response_data hd nu P m h Kc e'
  set s : ℝ≥0∞ := ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ with hs
  set Cc : ℝ≥0∞ := (2 : ℝ≥0∞) ^ 15 + ((d : ℝ≥0∞) * d) ^ 8 with hCc
  set t : ℝ := (sigmaBarInfinite nu (m - h) P)⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2) with ht
  have ht0 : 0 ≤ t := by positivity
  have hCcE : Cc = ENNReal.ofReal Ccr := by
    rw [hCc, hCcr, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow
      (by norm_num), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]
    simp
  have hAE : (2 * Cap ^ (8 : ℕ) + 1 : ℝ≥0∞) = ENNReal.ofReal Ar := by
    rw [hAr, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCapTop.ne]
    simp
  have hKc : ∀ omega, SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
      (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x)
        ≤ Z omega := hZle
  have hflux8 : ∀ omega (v : Vec d), vecNormSq v ≤ 1 →
      vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega v) ≤ s * Z omega := by
    intro omega v hv
    have := vecCubeLpENorm_hshellFlux_le nu P m h omega hv (originCube d (Kc : ℤ)) 8
    rw [Real.enorm_eq_ofReal (inv_nonneg.2 hσ.le)] at this
    exact this.trans (mul_le_mul' le_rfl (hKc omega))
  have hJd : ∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad ≤
      Cap * (s * Z omega) := by
    intro omega
    have := (hAp Kc _ (wD omega) (wN0 omega) (hwD omega) (hN0 omega)).1
    exact (le_self_add.trans this).trans (mul_le_mul' le_rfl (hflux8 omega e he))
  have hJn : ∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wN omega).toH1Function.grad ≤
      Cap * (s * Z omega) := by
    intro omega
    have := (hAp Kc _ (wD1 omega) (wN omega) (hD1 omega) (hwN omega)).1
    exact (le_add_self.trans this).trans (mul_le_mul' le_rfl (hflux8 omega e' he'))
  have hpt : ∀ omega, subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (vecNorm (principalED Q e' (wD omega).toH1Function.grad) ^ 8 +
          vecNorm (principalEN Q e (fun y => (wN omega).toH1Function.grad y +
            hshellFlux nu P m h omega e' y)) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)) ≤
      Cc * (1 + (2 * Cap ^ (8 : ℕ) + 1) * (s ^ (8 : ℕ) * Z omega ^ (8 : ℕ))) := by
    intro omega
    refine (principal_uz_pointwise P m h hnK hσ omega (vecNorm_le_one_of_vecNormSq_le he)
      (vecNorm_le_one_of_vecNormSq_le he')
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_of_gradMemL2On _
        (wD omega).toH1Function.gradMemL2)
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_of_gradMemL2On _
        (wN omega).toH1Function.gradMemL2)).trans ?_
    refine mul_le_mul' le_rfl ?_
    have h1 := pow_le_pow_left' (hJd omega) 8
    have h2 := pow_le_pow_left' (hJn omega) 8
    have h3 := pow_le_pow_left' (hKc omega) 8
    calc 1 + vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad ^ (8 : ℕ) +
          vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wN omega).toH1Function.grad ^ (8 : ℕ) +
          s ^ (8 : ℕ) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
            (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x)
              ^ (8 : ℕ)
        ≤ 1 + (Cap * (s * Z omega)) ^ (8 : ℕ) + (Cap * (s * Z omega)) ^ (8 : ℕ) +
          s ^ (8 : ℕ) * Z omega ^ (8 : ℕ) := by gcongr
      _ = 1 + (2 * Cap ^ (8 : ℕ) + 1) * (s ^ (8 : ℕ) * Z omega ^ (8 : ℕ)) := by ring
  have hAfin : (2 * Cap ^ (8 : ℕ) + 1 : ℝ≥0∞) ≠ ⊤ := by
    rw [hAE]; exact ENNReal.ofReal_ne_top
  have hsfin : s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCcfin : Cc ≠ ⊤ := by rw [hCcE]; exact ENNReal.ofReal_ne_top
  have hmain : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
      (vecNorm (principalED Q e' (wD omega).toH1Function.grad) ^ 8 +
        vecNorm (principalEN Q e (fun y => (wN omega).toH1Function.grad y +
          hshellFlux nu P m h omega e' y)) ^ 8 +
        matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ •
          principalGauge m h Q omega) ^ 8) ∂P.toMeasure) ≤
      ENNReal.ofReal (Ccr * (1 + Ar * (Cz * t) ^ 8)) := by
    refine (pm_subcubeAvg_lintegral_le P.toMeasure hnK _).trans ?_
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ hCcfin, lintegral_add_left measurable_const, lintegral_const,
      MeasureTheory.measure_univ, mul_one, lintegral_const_mul' _ _ hAfin,
      lintegral_const_mul' _ _ (ENNReal.pow_ne_top hsfin)]
    have hb : s ^ (8 : ℕ) * ∫⁻ omega, Z omega ^ (8 : ℕ) ∂P.toMeasure ≤
        ENNReal.ofReal (Cz * t) ^ (8 : ℕ) := by
      calc s ^ (8 : ℕ) * ∫⁻ omega, Z omega ^ (8 : ℕ) ∂P.toMeasure
          ≤ s ^ (8 : ℕ) * ENNReal.ofReal (Cz * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ) :=
            mul_le_mul' le_rfl hZint
        _ = (s * ENNReal.ofReal (Cz * (h : ℝ) ^ ((1 : ℝ) / 2))) ^ (8 : ℕ) := (mul_pow _ _ _).symm
        _ = ENNReal.ofReal (Cz * t) ^ (8 : ℕ) := by
            rw [hs, ← ENNReal.ofReal_mul (inv_nonneg.2 hσ.le), ht]
            congr 2
            ring
    calc Cc * (1 + (2 * Cap ^ (8 : ℕ) + 1) * (s ^ (8 : ℕ) * ∫⁻ omega, Z omega ^ (8 : ℕ) ∂P.toMeasure))
        ≤ Cc * (1 + (2 * Cap ^ (8 : ℕ) + 1) * ENNReal.ofReal (Cz * t) ^ (8 : ℕ)) := by gcongr
      _ = ENNReal.ofReal (Ccr * (1 + Ar * (Cz * t) ^ 8)) := by
          rw [hCcE, hAE]
          have hCzt : 0 ≤ Cz * t := mul_nonneg hCz0 ht0
          rw [← ENNReal.ofReal_pow hCzt, ← ENNReal.ofReal_mul hAr0, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_mul hCcr0]
  have hreal := uz_real_bound (Ccr := Ccr) (Ar := Ar) (Cz := Cz) (t := t) hCcr0 hAr0 ht0
  refine (ENNReal.rpow_le_rpow hmain (by norm_num)).trans ?_
  refine (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hreal) (by norm_num)).trans (le_of_eq ?_)
  have hbase : 0 ≤ (1 + Ccr * (1 + Ar * Cz ^ 8)) * (1 + t) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul hbase]
  norm_num

/-- **Satisfiability witness** for the non-law hypotheses of `principal_uz`: scales
`(m, h, Kc, n) = (400, 1, 40000, 0)`, `e = e' = 0`, and Dirichlet and Neumann responses of the flux
for every sample. -/
example [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) :
    ∃ m h Kc n : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 100 * m ≤ Kc ∧ n ≤ Kc ∧
      ∃ e e' : Vec d, vecNormSq e ≤ 1 ∧ vecNormSq e' ≤ 1 ∧
        ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H10Function (openCubeSet (originCube d (Kc : ℤ))))
          (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
          (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
            (hshellFlux nu P m h omega e) (wD omega)) ∧
          (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
            (hshellFlux nu P m h omega e') (wN omega)) := by
  obtain ⟨wD, wN, hD, hN, _⟩ := exists_response_data hd nu P 400 1 40000 0
  refine ⟨400, 1, 40000, 0, by norm_num, by norm_num, by norm_num, by norm_num, 0, 0, ?_, ?_,
    wD, wN, hD, hN⟩ <;> simp [vecNormSq, vecDot]

end SuperdiffusionCLT.Section5
