/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzH
public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePolyB
public import SuperdiffusionCLT.Section2.Localization.LocalizationCubePassage
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne

/-!
# The crude bound on the local minimizers `S_z` (`e.crude.Sz.bound`)

This is Step 2 of the proof of `lem.localization`:
`avsum_z E[ ‖bfA_m^{1/2} S_z‖²_{L̲²(z+cu_n)} ] ≤ C ν^{-4} m⁴`, where
`‖bfA_m^{1/2} S_z‖² = ⟪S_z, S_z⟫ = P_z · bfA_m(z+cu_n) P_z` and `P_z = blockSlope`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

/-- The real arithmetic closing the crude bound. -/
theorem crude_arith {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {m h : ℕ} (hh : 1 ≤ h) (hhm : h ≤ m)
    {Ce Cm Csh C2 sg : ℝ} (hCe : 1 ≤ Ce) (hCm : 1 ≤ Cm) (hCsh : 1 ≤ Csh) (hC2 : 0 ≤ C2)
    (hsg : 0 < sg) (hsg1 : sg ≤ 2 * Ce * nu⁻¹) :
    (2 * Ce * (1 + 2 * Ce) * nu⁻¹ ^ 2 * (m : ℝ)) *
        (2 + (2 + 2 * (2 * Cm * Csh * sg * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 2) * C2 +
          24 * (2 * Cm * Csh * sg * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 2) ≤
      (2 * Ce * (1 + 2 * Ce) * (2 + 2 * C2 + (2 * C2 + 24) * (16 * Cm ^ 2 * Csh ^ 2 * Ce ^ 2))) *
        nu⁻¹ ^ 4 * (m : ℝ) ^ 4 := by
  have hiv : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hh.trans hhm
  have hhm' : (h : ℝ) ≤ m := by exact_mod_cast hhm
  set iv := nu⁻¹ with hivdef
  set t : ℝ := (h : ℝ) ^ ((1 : ℝ) / 2) with htdef
  have ht2 : t ^ 2 = h := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  set X : ℝ := iv ^ 2 * m with hX
  have hX1 : 1 ≤ X := by
    have : 1 ≤ iv ^ 2 := one_le_pow₀ hiv
    nlinarith only [this, hm1]
  have hB2 : (2 * Cm * Csh * sg * t) ^ 2 ≤ (16 * Cm ^ 2 * Csh ^ 2 * Ce ^ 2) * X := by
    have e1 : (2 * Cm * Csh * sg * t) ^ 2 = 4 * Cm ^ 2 * Csh ^ 2 * sg ^ 2 * (h : ℝ) := by
      rw [← ht2]; ring
    have h1 : sg ^ 2 ≤ (2 * Ce * iv) ^ 2 := pow_le_pow_left₀ hsg.le hsg1 2
    have h2 : sg ^ 2 * (h : ℝ) ≤ (2 * Ce * iv) ^ 2 * m :=
      mul_le_mul h1 hhm' (by positivity) (by positivity)
    have h3 : 0 ≤ 4 * Cm ^ 2 * Csh ^ 2 := by positivity
    calc (2 * Cm * Csh * sg * t) ^ 2 = 4 * Cm ^ 2 * Csh ^ 2 * (sg ^ 2 * (h : ℝ)) := by rw [e1]; ring
      _ ≤ 4 * Cm ^ 2 * Csh ^ 2 * ((2 * Ce * iv) ^ 2 * m) := mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by rw [hX]; ring
  set B2 := (2 * Cm * Csh * sg * t) ^ 2 with hB2def
  set be := 16 * Cm ^ 2 * Csh ^ 2 * Ce ^ 2 with hbe
  have hB2nn : 0 ≤ B2 := by positivity
  have hCenn : 0 ≤ 2 * Ce * (1 + 2 * Ce) := by positivity
  have hmain : 2 + (2 + 2 * B2) * C2 + 24 * B2 ≤ (2 + 2 * C2 + (2 * C2 + 24) * be) * X := by
    have hbe0 : 0 ≤ be := by positivity
    have : 2 + (2 + 2 * B2) * C2 + 24 * B2 = (2 + 2 * C2) + (2 * C2 + 24) * B2 := by ring
    rw [this]
    have a1 : (2 + 2 * C2) ≤ (2 + 2 * C2) * X := le_mul_of_one_le_right (by positivity) hX1
    have a2 : (2 * C2 + 24) * B2 ≤ (2 * C2 + 24) * (be * X) :=
      mul_le_mul_of_nonneg_left hB2 (by positivity)
    have a3 : (2 * C2 + 24) * (be * X) * X ≥ (2 * C2 + 24) * (be * X) := by
      refine le_mul_of_one_le_right (by positivity) hX1
    nlinarith only [a1, a2, a3, hX1]
  have hK : 0 ≤ 2 + 2 * C2 + (2 * C2 + 24) * be := by positivity
  have hX0 : 0 ≤ X := by linarith only [hX1]
  have e1 : (2 * Ce * (1 + 2 * Ce) * iv ^ 2 * (m : ℝ)) = (2 * Ce * (1 + 2 * Ce)) * X := by
    rw [hX]; ring
  rw [e1]
  have step : (2 * Ce * (1 + 2 * Ce)) * X * (2 + (2 + 2 * B2) * C2 + 24 * B2) ≤
      (2 * Ce * (1 + 2 * Ce)) * X * ((2 + 2 * C2 + (2 * C2 + 24) * be) * X) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  refine step.trans ?_
  · have hm2 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
    have e2 : X * X = iv ^ 4 * (m : ℝ) ^ 2 := by rw [hX]; ring
    have hiv4 : 0 ≤ iv ^ 4 := by positivity
    calc (2 * Ce * (1 + 2 * Ce)) * X * ((2 + 2 * C2 + (2 * C2 + 24) * be) * X)
        = (2 * Ce * (1 + 2 * Ce) * (2 + 2 * C2 + (2 * C2 + 24) * be)) * (X * X) := by ring
      _ = (2 * Ce * (1 + 2 * Ce) * (2 + 2 * C2 + (2 * C2 + 24) * be)) * (iv ^ 4 * (m : ℝ) ^ 2) := by
          rw [e2]
      _ ≤ (2 * Ce * (1 + 2 * Ce) * (2 + 2 * C2 + (2 * C2 + 24) * be)) * (iv ^ 4 * (m : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 hiv4) (by positivity)
      _ = _ := by ring

/-- The `ℝ≥0∞` identity `(x + y)² ≤ 2 (x² + y²)`. -/
theorem ennreal_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have h := ennreal_two_mul_le x y
  calc (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring
    _ ≤ x ^ 2 + (x ^ 2 + y ^ 2) + y ^ 2 := by gcongr
    _ = 2 * (x ^ 2 + y ^ 2) := by ring

/-- **`e.crude.Sz.bound`.** For the constant-offset minimizers `S_z` of
`lem.localization` (offset `P_z = blockSlope`, fields `g_D = ∇w_D`,
`g_N = ∇w_N + shom_{m-h}^{-1} hshell e'`), the average over the subcubes `z + cu_n` of `cu_K` of the
expected energies `E⟪S_z, S_z⟫ = E[P_z · bfA_m(z+cu_n) P_z]` is at most `C ν^{-4} m⁴`. -/
theorem crude_Sz_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (_hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (_hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (_hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m h Kc n : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc → n ≤ Kc →
          ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
          ∀ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H10Function (openCubeSet (originCube d (Kc : ℤ))))
            (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e') (wN omega)) →
          ∀ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → TriadicCube d → BlockState d,
            (∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
              IsBlockOffsetMinimizer
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
                (cubeSet Q)
                (constBlockState
                  (blockSlope nu (m - h) P Q e e' (wD omega).toH1Function.grad
                    (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y)))
                (S omega Q)) →
            subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
                (blockPairingAverage (cubeSet Q)
                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
                  (S omega Q) (S omega Q)) ∂P.toMeasure) ≤
              ENNReal.ofReal (C * nu⁻¹ ^ 4 * (m : ℝ) ^ 4) := by
  obtain ⟨Cap, hCapTop, hAp⟩ := SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd
  obtain ⟨Csh, hCsh1, hCsh⟩ := shell_flux_L8 d
  set Ce : ℝ := cutoffEnvelopeConst d with hCe
  set C2 : ℝ := (2 * Homogenization.IndependentSums.gammaMomentConst 1) ^ 2 with hC2def
  set Cm : ℝ := Cap.toReal + 1 with hCmdef
  have hCe1 : 1 ≤ Ce := one_le_cutoffEnvelopeConst d
  have hCm1 : 1 ≤ Cm := by
    have := ENNReal.toReal_nonneg (a := Cap)
    linarith only [this]
  have hC2nn : 0 ≤ C2 := by positivity
  refine ⟨max 1 ((2 * Ce * (1 + 2 * Ce)) *
    (2 + 2 * C2 + (2 * C2 + 24) * (16 * Cm ^ 2 * Csh ^ 2 * Ce ^ 2))), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc n hh h400 h100 hn e e' he he' wD wN hwD hwN S hS
  obtain ⟨hσ, hσinv, hσup⟩ := SuperdiffusionCLT.Section4.MinimalScales.srootD4_sigma_bounds hnu (m - h) hPre hJ2 hJ3 hJ4
  set σ : ℝ := sigmaBarInfinite nu (m - h) P with hσdef
  have hm1 : 1 ≤ m := by omega
  have hhm : h ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hiv : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  -- the constants
  set Lam : ℝ := (2 * Ce * (1 + 2 * Ce)) * nu⁻¹ ^ 2 * (m : ℝ) with hLamdef
  have hLam0 : 0 ≤ Lam := by positivity
  have hup1 := SuperdiffusionCLT.Section2.Localization.envelopeUpperScalar_le_nuInv_mul_max (d := d) hnu hnu1 m
  have hup2 := SuperdiffusionCLT.Section2.Localization.envelopeUpperScalar_le_nuInv_mul_max (d := d) hnu hnu1 (m - h)
  have hmax1 : max 1 (m : ℝ) = m := max_eq_right hmR
  have hmax2 : max 1 ((m - h : ℕ) : ℝ) ≤ m := by
    refine max_le hmR ?_
    exact_mod_cast Nat.sub_le m h
  have hinvσ : 0 < σ⁻¹ := inv_pos.2 hσ
  have hL1 : envelopeUpperScalar d nu m * σ⁻¹ ≤ Lam := by
    have h1 : envelopeUpperScalar d nu m ≤ (1 + 2 * Ce) * nu⁻¹ * m := by
      rw [hmax1] at hup1; exact hup1
    calc envelopeUpperScalar d nu m * σ⁻¹ ≤ ((1 + 2 * Ce) * nu⁻¹ * m) * (2 * Ce * nu⁻¹) :=
          mul_le_mul h1 hσinv hinvσ.le (by positivity)
      _ = Lam := by rw [hLamdef]; ring
  have hL2 : envelopeLowerScalar d nu * σ ≤ Lam := by
    have h1 : σ ≤ (1 + 2 * Ce) * nu⁻¹ * m := by
      refine hσup.trans ?_
      have : envelopeUpperScalar d nu (m - h) = nu + 2 * Ce * nu⁻¹ * max 1 ((m - h : ℕ) : ℝ) := rfl
      rw [← this]
      refine hup2.trans ?_
      gcongr
    calc envelopeLowerScalar d nu * σ ≤ (2 * Ce * nu⁻¹) * ((1 + 2 * Ce) * nu⁻¹ * m) := by
          unfold envelopeLowerScalar
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Lam := by rw [hLamdef]; ring
  -- shell majorants
  obtain ⟨We, hWem, hWele, hWeint⟩ := hCsh nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he
  obtain ⟨We', hWem', hWele', hWeint'⟩ :=
    hCsh nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e' he'
  set B : ℝ := 2 * Cm * Csh * σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2) with hBdef
  have hhpos : (0 : ℝ) < (h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hh) _
  have hBpos : 0 < B := by
    have : 0 < Csh := by linarith only [hCsh1]
    have : 0 < Cm := by linarith only [hCm1]
    positivity
  have hCapCm : Cap.toReal ≤ Cm := by rw [hCmdef]; linarith only
  have hcapm : Cap ≤ ENNReal.ofReal Cm :=
    (ENNReal.ofReal_toReal hCapTop.ne).symm.le.trans (ENNReal.ofReal_le_ofReal hCapCm)
  have honem : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Cm := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hCm1
  have hkm : Cap + 1 ≤ ENNReal.ofReal Cm := by
    have : Cap + 1 = ENNReal.ofReal (Cap.toReal + 1) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hCapTop.ne]
      simp
    rw [this, hCmdef]
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  -- membership in L²
  have hMD : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wD omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMN : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wN omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMS : ∀ omega e0, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (hshellFlux nu P m h omega e0) := fun omega e0 => memVectorL2_hshellFlux nu P omega e0 Kc
  have hMG : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) :=
    fun omega => (hMN omega).add (hMS omega e')
  -- the L⁸ bounds of the fields by the shell flux
  choose wN0 hwN0 using fun omega => exists_isCubeNeumannResponse (originCube d (Kc : ℤ))
    (hMS omega e)
  choose wD1 hwD1 using fun omega => exists_isCubeDirichletResponse (originCube d (Kc : ℤ))
    (hMS omega e')
  have hLD : ∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad ≤
      ENNReal.ofReal Cm * vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e) := by
    intro omega
    have h1 := (hAp Kc (hshellFlux nu P m h omega e) (wD omega) (wN0 omega) (hwD omega)
      (hwN0 omega)).1
    exact (le_self_add.trans h1).trans (mul_le_mul_left hcapm _)
  have hLN : ∀ omega,
      vecCubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ≤
      ENNReal.ofReal Cm * vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e') := by
    intro omega
    have h1 := (hAp Kc (hshellFlux nu P m h omega e') (wD1 omega) (wN omega) (hwD1 omega)
      (hwN omega)).1
    have h2 := vecCubeLpENorm_add_le (Q := originCube d (Kc : ℤ)) (q := 8) (by norm_num)
      (SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
        (hMN omega))
      (SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
        (hMS omega e'))
    have hN1 : vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wN omega).toH1Function.grad ≤
        Cap * vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e') :=
      le_add_self.trans h1
    calc _ ≤ _ := h2
      _ ≤ Cap * vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e') +
            1 * vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e') := by
          rw [one_mul]
          exact add_le_add hN1 le_rfl
      _ = (Cap + 1) * vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e') := by
          rw [add_mul, one_mul]
      _ ≤ _ := mul_le_mul_left hkm _
  -- the pointwise powers
  have hD8 : ∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad ^ (8 : ℕ) ≤
      ENNReal.ofReal Cm ^ (8 : ℕ) * We omega := fun omega =>
    ((pow_le_pow_left' (hLD omega) 8).trans (by
      rw [mul_pow]; exact mul_le_mul' le_rfl (hWele omega)))
  have hN8 : ∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 8
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ^ (8 : ℕ) ≤
      ENNReal.ofReal Cm ^ (8 : ℕ) * We' omega := fun omega =>
    ((pow_le_pow_left' (hLN omega) 8).trans (by
      rw [mul_pow]; exact mul_le_mul' le_rfl (hWele' omega)))
  set Wm : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ≥0∞ :=
    fun omega => ENNReal.ofReal Cm ^ (8 : ℕ) * (We omega + We' omega) with hWmdef
  have hWm : Measurable Wm := (hWem.add hWem').const_mul _
  have hu : ∀ omega,
      (subcubeAvg Kc n (fun Q => (vecCubeLpENorm Q 2 (wD omega).toH1Function.grad ^ (2 : ℕ)) ^ (2 : ℕ)) +
        subcubeAvg Kc n (fun Q => (vecCubeLpENorm Q 2
          (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ^ (2 : ℕ)) ^
            (2 : ℕ))) ^ 2 ≤ 256 * (Wm omega + 0) := by
    intro omega
    have h1 := subcubeAvg_L2_pow_four_le hn (hMD omega)
    have h2 := subcubeAvg_L2_pow_four_le hn (hMG omega)
    refine (pow_le_pow_left' (add_le_add h1 h2) 2).trans ?_
    refine (ennreal_add_sq_le _ _).trans ?_
    have h3 : (vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad ^ (4 : ℕ)) ^ 2 =
        vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad ^ (8 : ℕ) := by
      rw [← pow_mul]
    have h4 : (vecCubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ^ (4 : ℕ)) ^ 2 =
        vecCubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ^ (8 : ℕ) := by
      rw [← pow_mul]
    rw [h3, h4, add_zero]
    calc 2 * (_ + _) ≤ 2 * (ENNReal.ofReal Cm ^ (8 : ℕ) * We omega +
          ENNReal.ofReal Cm ^ (8 : ℕ) * We' omega) :=
          mul_le_mul' le_rfl (add_le_add (hD8 omega) (hN8 omega))
      _ = 2 * Wm omega := by rw [hWmdef]; ring
      _ ≤ 256 * Wm omega := mul_le_mul' (by norm_num) le_rfl
  have hWint : ∫⁻ omega, Wm omega ∂P.toMeasure ≤ ENNReal.ofReal B ^ (8 : ℕ) := by
    rw [hWmdef]
    simp only
    have hsum : Measurable (fun omega => We omega + We' omega) := hWem.add hWem'
    rw [lintegral_const_mul _ hsum, lintegral_add_left hWem]
    have hσe : (sigmaBarInfinite nu (m - h) P)⁻¹ = σ⁻¹ := rfl
    rw [hσe] at hWeint hWeint'
    calc ENNReal.ofReal Cm ^ (8 : ℕ) * (∫⁻ omega, We omega ∂P.toMeasure + ∫⁻ omega, We' omega ∂P.toMeasure)
        ≤ ENNReal.ofReal Cm ^ (8 : ℕ) * (ENNReal.ofReal (Csh * σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ) +
            ENNReal.ofReal (Csh * σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ)) :=
          mul_le_mul' le_rfl (add_le_add hWeint hWeint')
      _ = 2 * (ENNReal.ofReal Cm ^ (8 : ℕ) *
            ENNReal.ofReal (Csh * σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ)) := by ring
      _ ≤ 256 * (ENNReal.ofReal Cm ^ (8 : ℕ) *
            ENNReal.ofReal (Csh * σ⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ)) :=
          mul_le_mul' (by norm_num) le_rfl
      _ = ENNReal.ofReal B ^ (8 : ℕ) := by
          have hCm0 : 0 ≤ Cm := by linarith only [hCm1]
          have e256 : (256 : ℝ≥0∞) = ENNReal.ofReal 2 ^ (8 : ℕ) := by
            rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num
          rw [e256, ← mul_pow, ← mul_pow, ← ENNReal.ofReal_mul hCm0,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 2
          rw [hBdef]; ring
  have hf : ∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ENNReal.ofReal (blockPairingAverage (cubeSet Q)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
        (S omega Q) (S omega Q)) ≤
      ENNReal.ofReal (2 * Lam) * (ENNReal.ofReal (envelopeRatio m Q omega) *
        (2 + vecCubeLpENorm Q 2 (wD omega).toH1Function.grad ^ (2 : ℕ) +
          vecCubeLpENorm Q 2
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ^ (2 : ℕ))) := by
    intro omega Q hQ
    have hsub := openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
    have h1 := ofReal_pairing_le hnu P m h omega hσ hL1 hL2 he he' Q
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub (hMD omega))
      (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub (hMG omega)) (hS omega Q hQ)
    refine h1.trans (le_of_eq ?_)
    ring
  have hfin := crude_assembly (d := d) P.toMeasure hn (Lam := Lam) (B := B) (C2 := C2) hBpos hLam0
    hC2nn (fun Q omega => ENNReal.ofReal (envelopeRatio m Q omega))
    (fun Q omega => vecCubeLpENorm Q 2 (wD omega).toH1Function.grad ^ (2 : ℕ))
    (fun Q omega => vecCubeLpENorm Q 2
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) ^ (2 : ℕ))
    (fun Q omega => ENNReal.ofReal (blockPairingAverage (cubeSet Q)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
        (S omega Q) (S omega Q)))
    (fun _ => 0) Wm
    (fun Q => ENNReal.measurable_ofReal.comp (measurable_envelopeRatio m Q))
    (fun Q _ => lintegral_envelopeRatio_sq_le hPre hJ2 hJ3 hJ4 m Q) hWm hWint (by simp) hu hf
  refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
  have harith := crude_arith hnu hnu1 hh hhm hCe1 hCm1 hCsh1 hC2nn hinvσ hσinv
  refine harith.trans ?_
  have hnn : 0 ≤ nu⁻¹ ^ 4 * (m : ℝ) ^ 4 := by positivity
  calc _ = (2 * Ce * (1 + 2 * Ce) *
        (2 + 2 * C2 + (2 * C2 + 24) * (16 * Cm ^ 2 * Csh ^ 2 * Ce ^ 2))) *
        (nu⁻¹ ^ 4 * (m : ℝ) ^ 4) := by ring
    _ ≤ max 1 ((2 * Ce * (1 + 2 * Ce)) *
        (2 + 2 * C2 + (2 * C2 + 24) * (16 * Cm ^ 2 * Csh ^ 2 * Ce ^ 2))) *
        (nu⁻¹ ^ 4 * (m : ℝ) ^ 4) := mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
    _ = _ := by ring

end SuperdiffusionCLT.Section5
