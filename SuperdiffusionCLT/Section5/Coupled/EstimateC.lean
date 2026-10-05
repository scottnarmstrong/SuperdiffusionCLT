/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Coupled.EstimateB

/-!
# `lem.coupled.input`: the fixed-cube assembly

`coupled4_fixed` combines `coupled_pointwise_split`, `coupled_bulk_det`, the box Jensen bound for
`B_z` and the bounds on `R_z` and on the energy, at one large cube `cu_Kc`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section3.ResponseFields (vecCubeLpENorm)
open scoped ENNReal

variable {d : ℕ}

/-- The pointwise bound of one box and one sample by the bulk integrand plus the remainder terms. -/
theorem coupled4_pointwise [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (m h : ℕ)
    (Q : TriadicCube d) (omega : ShellSeq d) (hs : 0 < sigmaBarInfinite nu (m - h) P)
    (e : Vec d) (he : vecNormSq e = 1) (gD : Vec d → Vec d) (t s : ℝ) (ht : 0 < t) (hs' : 0 < s) :
    ENNReal.ofReal (blockVecDot (coupledVec nu P m h Q omega e gD)
        (coupledVec nu P m h Q omega e gD)) ≤
      ENNReal.ofReal (1 + vecNormSq (coupledE Q gD) +
          ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 * vecNormSq (coupledB m h Q omega gD) -
          2 * (sigmaBarInfinite nu (m - h) P)⁻¹ * ∑ i, e i * coupledB m h Q omega gD i) +
        (ENNReal.ofReal (((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 +
              ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 / t + (sigmaBarInfinite nu (m - h) P)⁻¹ / s) *
            ENNReal.ofReal (vecNormSq (coupledR m h Q omega gD)) +
          ENNReal.ofReal (((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 * t) *
            ENNReal.ofReal (vecNormSq (coupledB m h Q omega gD)) +
          ENNReal.ofReal ((sigmaBarInfinite nu (m - h) P)⁻¹ * s)) := by
  set c := (sigmaBarInfinite nu (m - h) P)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.mpr hs.le
  have hsplit := coupled_pointwise_split nu P m h Q omega hs e he gD
  have ham := coupled4_amgm c t s (vecNorm (coupledB m h Q omega gD))
    (vecNorm (coupledR m h Q omega gD)) hc0 ht hs'
  rw [vecNorm_sq_eq_vecNormSq, vecNorm_sq_eq_vecNormSq] at ham
  set X : ℝ := 1 + vecNormSq (coupledE Q gD) + c ^ 2 * vecNormSq (coupledB m h Q omega gD) -
    2 * c * ∑ i, e i * coupledB m h Q omega gD i with hX
  have hle : blockVecDot (coupledVec nu P m h Q omega e gD) (coupledVec nu P m h Q omega e gD) ≤
      X + ((c ^ 2 + c ^ 2 / t + c / s) * vecNormSq (coupledR m h Q omega gD) +
        c ^ 2 * t * vecNormSq (coupledB m h Q omega gD) + c * s) := by
    rw [hX]
    linarith only [hsplit, ham]
  have h1 : 0 ≤ c ^ 2 + c ^ 2 / t + c / s := by positivity
  have h2 : 0 ≤ c ^ 2 * t := by positivity
  have h3 : 0 ≤ c * s := by positivity
  have hR := vecNormSq_nonneg (coupledR m h Q omega gD)
  have hB := vecNormSq_nonneg (coupledB m h Q omega gD)
  calc _ ≤ ENNReal.ofReal (X + ((c ^ 2 + c ^ 2 / t + c / s) * vecNormSq (coupledR m h Q omega gD) +
        c ^ 2 * t * vecNormSq (coupledB m h Q omega gD) + c * s)) :=
        ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal X + ENNReal.ofReal ((c ^ 2 + c ^ 2 / t + c / s) *
          vecNormSq (coupledR m h Q omega gD) +
        c ^ 2 * t * vecNormSq (coupledB m h Q omega gD) + c * s) := ENNReal.ofReal_add_le
    _ = _ := by
        congr 1
        rw [ENNReal.ofReal_add (by positivity) h3, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h2]

section Fixed

variable [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (m h Kc n : ℕ)

/-- **The fixed-cube assembly of `e.coupled.estimate`.** -/
theorem coupled4_fixed (hn : n ≤ Kc) (hs : 0 < sigmaBarInfinite nu (m - h) P)
    (e : Vec d) (he : vecNormSq e = 1)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega))
    (b r gl : ℝ) (hb : 0 < b) (hr : 0 < r)
    (hH : ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
          ((wD omega).toH1Function.grad x)) ^ (2 : ℕ) ∂P.toMeasure ≤ ENNReal.ofReal (b ^ 2))
    (hR : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (vecNormSq (coupledR m h Q omega (wD omega).toH1Function.grad)) ∂P.toMeasure) ≤
      ENNReal.ofReal (r ^ 2))
    (hG : ENNReal.ofReal gl ≤ ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure) :
    subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (blockVecDot (coupledVec nu P m h Q omega e (wD omega).toH1Function.grad)
          (coupledVec nu P m h Q omega e (wD omega).toH1Function.grad)) ∂P.toMeasure) ≤
      ENNReal.ofReal (1 + ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 * b ^ 2 +
        (((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 * r ^ 2 +
          2 * ((sigmaBarInfinite nu (m - h) P)⁻¹) ^ 2 * b * r +
          2 * (sigmaBarInfinite nu (m - h) P)⁻¹ * r) - gl) := by
  classical
  set c := (sigmaBarInfinite nu (m - h) P)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.mpr hs.le
  set t : ℝ := r / b with htdef
  have ht : 0 < t := div_pos hr hb
  set a1 : ℝ := c ^ 2 + c ^ 2 / t + c / r with ha1
  set a2 : ℝ := c ^ 2 * t with ha2
  set a3 : ℝ := c * r with ha3
  have ha1n : 0 ≤ a1 := by positivity
  have ha2n : 0 ≤ a2 := by positivity
  have ha3n : 0 ≤ a3 := by positivity
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hsub : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)) :=
    fun Q hQ => openCubeSet_subset_of_mem_descendantsAtScale hk hQ
  set ρ : TriadicCube d → ShellSeq d → ℝ≥0∞ := fun Q omega =>
    ENNReal.ofReal (vecNormSq (coupledR m h Q omega (wD omega).toH1Function.grad)) with hρ
  set β : TriadicCube d → ShellSeq d → ℝ≥0∞ := fun Q omega =>
    ENNReal.ofReal (vecNormSq (coupledB m h Q omega (wD omega).toH1Function.grad)) with hβ
  have hρm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (ρ Q) :=
    fun Q hQ => ENNReal.measurable_ofReal.comp (coupled4_measurable_vecNormSq
      (coupled4_measurable_R nu P m h Kc e wD hwD Q (hsub Q hQ)))
  have hβm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (β Q) :=
    fun Q hQ => ENNReal.measurable_ofReal.comp (coupled4_measurable_vecNormSq
      (coupled4_measurable_B nu P m h Kc e wD hwD Q (hsub Q hQ)))
  have hav : ∀ f : TriadicCube d → ShellSeq d → ℝ≥0∞,
      (∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (f Q)) →
      Measurable (fun omega => subcubeAvg Kc n (fun Q => f Q omega)) := by
    intro f hf
    unfold subcubeAvg
    exact (Finset.measurable_sum _ hf).const_mul _
  set Em : ShellSeq d → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal a1 * subcubeAvg Kc n (fun Q => ρ Q omega) +
      ENNReal.ofReal a2 * subcubeAvg Kc n (fun Q => β Q omega) + ENNReal.ofReal a3 with hEmdef
  have hEm : Measurable Em :=
    (((hav ρ hρm).const_mul _).add ((hav β hβm).const_mul _)).add measurable_const
  set Aw : ShellSeq d → ℝ≥0∞ := fun omega => subcubeAvg Kc n (fun Q => ENNReal.ofReal
    (1 + vecNormSq (coupledE Q (wD omega).toH1Function.grad) +
      c ^ 2 * vecNormSq (coupledB m h Q omega (wD omega).toH1Function.grad) -
      2 * c * ∑ i, e i * coupledB m h Q omega (wD omega).toH1Function.grad i)) with hAw
  set Hw : ShellSeq d → ℝ≥0∞ := fun omega => vecCubeLpENorm (originCube d (Kc : ℤ)) 2
    (fun x => matVecMul (finiteShellIncrement omega (m - h) m x)
      ((wD omega).toH1Function.grad x)) ^ (2 : ℕ) with hHw
  set Gw : ShellSeq d → ℝ≥0∞ := fun omega => vecCubeLpENorm (originCube d (Kc : ℤ)) 2
    (wD omega).toH1Function.grad ^ (2 : ℕ) with hGw
  have hpt : ∀ omega, subcubeAvg Kc n (fun Q => ENNReal.ofReal
      (blockVecDot (coupledVec nu P m h Q omega e (wD omega).toH1Function.grad)
        (coupledVec nu P m h Q omega e (wD omega).toH1Function.grad))) ≤ Aw omega + Em omega := by
    intro omega
    calc _ ≤ subcubeAvg Kc n (fun Q => ENNReal.ofReal
          (1 + vecNormSq (coupledE Q (wD omega).toH1Function.grad) +
            c ^ 2 * vecNormSq (coupledB m h Q omega (wD omega).toH1Function.grad) -
            2 * c * ∑ i, e i * coupledB m h Q omega (wD omega).toH1Function.grad i) +
          (ENNReal.ofReal a1 * ρ Q omega + ENNReal.ofReal a2 * β Q omega + ENNReal.ofReal a3)) :=
          subcubeAvg_mono fun Q => coupled4_pointwise nu P m h Q omega hs e he _ t r ht hr
      _ = Aw omega + subcubeAvg Kc n (fun Q =>
          ENNReal.ofReal a1 * ρ Q omega + ENNReal.ofReal a2 * β Q omega + ENNReal.ofReal a3) :=
          subcubeAvg_add _ _
      _ ≤ Aw omega + Em omega := by
          refine add_le_add le_rfl ?_
          rw [subcubeAvg_add, subcubeAvg_add, subcubeAvg_const_mul, subcubeAvg_const_mul]
          exact add_le_add le_rfl (coupled4_subcubeAvg_const_le _)
  have hk' : ENNReal.ofReal (c ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hU : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
        (blockVecDot (coupledVec nu P m h Q omega e (wD omega).toH1Function.grad)
          (coupledVec nu P m h Q omega e (wD omega).toH1Function.grad)) ∂P.toMeasure) ≤
      ∫⁻ omega, (Aw omega + Em omega) ∂P.toMeasure :=
    (subcubeAvg_lintegral_le_lintegral_subcubeAvg _).trans (lintegral_mono hpt)
  have hEint : ∫⁻ omega, Em omega ∂P.toMeasure =
      ENNReal.ofReal a1 * subcubeAvg Kc n (fun Q => ∫⁻ omega, ρ Q omega ∂P.toMeasure) +
        ENNReal.ofReal a2 * subcubeAvg Kc n (fun Q => ∫⁻ omega, β Q omega ∂P.toMeasure) +
          ENNReal.ofReal a3 := by
    rw [hEmdef, lintegral_add_right _ measurable_const,
      lintegral_add_left (((hav ρ hρm).const_mul _)),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      coupled4_lintegral_subcubeAvg ρ hρm, coupled4_lintegral_subcubeAvg β hβm]
    simp
  have hβb : subcubeAvg Kc n (fun Q => ∫⁻ omega, β Q omega ∂P.toMeasure) ≤
      ENNReal.ofReal (b ^ 2) :=
    (subcubeAvg_lintegral_le_lintegral_subcubeAvg _).trans
      ((lintegral_mono fun omega => coupled4_avg_B_le m h Kc n hn omega
        (wD omega).toH1Function.grad_memVectorL2).trans hH)
  have hmain : ∫⁻ omega, (Aw omega + Em omega) ∂P.toMeasure + ENNReal.ofReal gl ≤
      ENNReal.ofReal (1 + c ^ 2 * b ^ 2 + (a1 * r ^ 2 + a2 * b ^ 2 + a3)) := by
    have h1 : ∫⁻ omega, (Aw omega + Em omega) ∂P.toMeasure + ∫⁻ omega, Gw omega ∂P.toMeasure ≤
        1 + ENNReal.ofReal (c ^ 2) * ∫⁻ omega, Hw omega ∂P.toMeasure +
          ∫⁻ omega, Em omega ∂P.toMeasure := by
      calc _ ≤ ∫⁻ omega, ((Aw omega + Em omega) + Gw omega) ∂P.toMeasure := le_lintegral_add _ _
        _ ≤ ∫⁻ omega, ((1 + ENNReal.ofReal (c ^ 2) * Hw omega) + Em omega) ∂P.toMeasure := by
            refine lintegral_mono fun omega => ?_
            have hb0 := coupled_bulk_det nu P m h Kc n hn omega e he (wD omega) (hwD omega)
            calc (Aw omega + Em omega) + Gw omega = (Aw omega + Gw omega) + Em omega := by ring
              _ ≤ _ := add_le_add hb0 le_rfl
        _ = ∫⁻ omega, (1 + ENNReal.ofReal (c ^ 2) * Hw omega) ∂P.toMeasure +
              ∫⁻ omega, Em omega ∂P.toMeasure := lintegral_add_right _ hEm
        _ = _ := by
            rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ hk']
            simp
    have h2 : ENNReal.ofReal (c ^ 2) * ∫⁻ omega, Hw omega ∂P.toMeasure ≤
        ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (b ^ 2) := mul_le_mul_right hH _
    have h3 : ∫⁻ omega, Em omega ∂P.toMeasure ≤
        ENNReal.ofReal a1 * ENNReal.ofReal (r ^ 2) + ENNReal.ofReal a2 * ENNReal.ofReal (b ^ 2) +
          ENNReal.ofReal a3 := by
      rw [hEint]
      exact add_le_add (add_le_add (mul_le_mul_right hR _) (mul_le_mul_right hβb _)) le_rfl
    have h4 : ENNReal.ofReal gl ≤ ∫⁻ omega, Gw omega ∂P.toMeasure := hG
    calc _ ≤ ∫⁻ omega, (Aw omega + Em omega) ∂P.toMeasure + ∫⁻ omega, Gw omega ∂P.toMeasure :=
          add_le_add le_rfl h4
      _ ≤ 1 + ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (b ^ 2) +
          (ENNReal.ofReal a1 * ENNReal.ofReal (r ^ 2) + ENNReal.ofReal a2 * ENNReal.ofReal (b ^ 2) +
            ENNReal.ofReal a3) := h1.trans (add_le_add (add_le_add le_rfl h2) h3)
      _ = _ := by
          have e1 : 0 ≤ c ^ 2 * b ^ 2 := by positivity
          have e2 : 0 ≤ a1 * r ^ 2 := mul_nonneg ha1n (sq_nonneg r)
          have e3 : 0 ≤ a2 * b ^ 2 := mul_nonneg ha2n (sq_nonneg b)
          rw [ENNReal.ofReal_add (add_nonneg zero_le_one e1)
              (add_nonneg (add_nonneg e2 e3) ha3n), ENNReal.ofReal_add zero_le_one e1,
            ENNReal.ofReal_add (add_nonneg e2 e3) ha3n, ENNReal.ofReal_add e2 e3,
            ENNReal.ofReal_mul (p := c ^ 2) (q := b ^ 2) (sq_nonneg c),
            ENNReal.ofReal_mul (p := a1) (q := r ^ 2) ha1n,
            ENNReal.ofReal_mul (p := a2) (q := b ^ 2) ha2n, ENNReal.ofReal_one]
  have hfin := coupled4_sub_of_add_le ((add_le_add hU le_rfl).trans hmain)
  refine hfin.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [ha1, ha2, ha3, htdef]
  field_simp
  ring

end Fixed

end SuperdiffusionCLT.Section5
