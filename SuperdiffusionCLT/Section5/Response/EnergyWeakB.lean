/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.EnergyWeak

/-!
# The second moment of the Neumann-minus-Dirichlet gradient

`e.abstract.response.ND.weak` (the a priori estimate) applied to the flux `hshellFlux`
on `cu_Kc`, fed with the three bounds of `EnergyWeak` (weak norm, `L⁴`, average), the exponent
bookkeeping `X^{1/5} Y^{4/5}` of the `Γ₂` calculus and the second moment of a `Γ₂` observable.
The result is the energy rate with the corrected exponent (see `ERRATA.md`),
`C h^{4/5} (1+(Kc-m))^{2/5} 3^{-(2/5)(Kc-m)} σ̄_{m-h}^{-2}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open Homogenization.IndependentSums
open scoped ENNReal

variable {d : ℕ}

theorem amplitude_rpow_mul (Chm Cl4 t k : ℝ) (hChm : 0 ≤ Chm)
    (hCl4 : 0 ≤ Cl4) (ht : 0 < t) (hk : 0 ≤ k) :
    (Chm * t * ((1 + k) * (3 : ℝ) ^ (-k))) ^ ((1 : ℝ) / 5) * (Cl4 * t) ^ ((4 : ℝ) / 5) =
      Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) * t *
        (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-k) := Real.rpow_nonneg (by norm_num) _
  have hk1 : (0 : ℝ) ≤ 1 + k := by linarith only [hk]
  have e2 : ((3 : ℝ) ^ (-k)) ^ ((1 : ℝ) / 5) = (3 : ℝ) ^ (-(k / 5)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring_nf
  have e3 : t ^ ((1 : ℝ) / 5) * t ^ ((4 : ℝ) / 5) = t := by
    rw [← Real.rpow_add ht]; norm_num
  rw [Real.mul_rpow (mul_nonneg hChm ht.le) (mul_nonneg hk1 h3),
    Real.mul_rpow hk1 h3, Real.mul_rpow hChm ht.le, Real.mul_rpow hCl4 ht.le, e2]
  calc
    Chm ^ ((1 : ℝ) / 5) * t ^ ((1 : ℝ) / 5) *
        ((1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5))) *
        (Cl4 ^ ((4 : ℝ) / 5) * t ^ ((4 : ℝ) / 5))
        = Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5) *
            (t ^ ((1 : ℝ) / 5) * t ^ ((4 : ℝ) / 5)) *
            (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by ring
    _ = _ := by rw [e3]

theorem rate_sq_eq (h k : ℝ) (hh : 0 ≤ h) (hk : 0 ≤ k) :
    (h ^ ((2 : ℝ) / 5) * (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5))) ^ 2 =
      h ^ ((4 : ℝ) / 5) * (1 + k) ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((2 : ℝ) / 5 * k)) := by
  have hk1 : (0 : ℝ) ≤ 1 + k := by linarith only [hk]
  have s1 : ∀ (x a : ℝ), 0 ≤ x → (x ^ a) ^ 2 = x ^ (2 * a) := by
    intro x a hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num [mul_comm]
  rw [mul_pow, mul_pow, s1 h _ hh, s1 (1 + k) _ hk1, s1 3 _ (by norm_num)]
  congr 2 <;> ring_nf

theorem hshellFlux_gap_second_moment [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P → ∀ (m h Kc : ℕ), 1 ≤ h → h ≤ m → m ≤ Kc →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
        (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
        (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
          (hshellFlux nu P m h omega e) (wD omega)) →
        (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
          (hshellFlux nu P m h omega e) (wN omega)) →
        ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
            (fun x => (wN omega).toH1Function.grad x - (wD omega).toH1Function.grad x) ^ (2 : ℕ)
            ∂P.toMeasure ≤
          ENNReal.ofReal (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
            (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) *
            (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))) := by
  classical
  obtain ⟨Cw, hCw, hW⟩ := hshellFlux_hatNeg_isBigO (d := d) hd
  obtain ⟨Ca, hCa, hA⟩ := hshellFlux_avg_isBigO (d := d) hd
  obtain ⟨C4, hC4, hL⟩ := hshellFlux_L4_isBigO (d := d) hd
  obtain ⟨Cs, hCstop, hCs⟩ := SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd
  set Cnd : ℝ := Cs.toReal + 1 with hCnddef
  have hCnd : 0 < Cnd := by
    have h := ENNReal.toReal_nonneg (a := Cs)
    rw [hCnddef]; linarith only [h]
  have hCle : Cs ≤ ENNReal.ofReal Cnd := by
    calc Cs = ENNReal.ofReal Cs.toReal := (ENNReal.ofReal_toReal hCstop.ne).symm
      _ ≤ ENNReal.ofReal Cnd :=
        ENNReal.ofReal_le_ofReal (by rw [hCnddef]; exact (lt_add_one _).le)
  have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hprod := SuperdiffusionCLT.Probability.orliczProductConst_pos 10 (5 / 2)
  set Kg : ℝ := Cnd * (gammaTriangleConst 2 *
    (SuperdiffusionCLT.Probability.orliczProductConst 10 (5 / 2) *
      (Cw ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5)) + Ca)) with hKg
  have hKg0 : 0 < Kg := by rw [hKg]; positivity
  refine ⟨max 1 (2 * Kg ^ 2), le_max_left _ _, ?_⟩
  intro nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he wD wN hwD hwN
  have hS : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set S := sigmaBarInfinite nu (m - h) P with hSdef
  have hSi : 0 < S⁻¹ := inv_pos.2 hS
  have hen : vecNorm e = 1 := by
    have h2 := SuperdiffusionCLT.Section3.Setup.vecNorm_sq_eq_vecNormSq (d := d) e
    rw [he] at h2
    have h0 := vecNorm_nonneg e
    nlinarith only [h2, h0]
  obtain ⟨Zw, hZw0, hZwm, hZwbig, hZwbd⟩ :=
    hW nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  obtain ⟨Za, hZa0, hZam, hZabig, hZabd⟩ :=
    hA nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  obtain ⟨Z4, hZ40, hZ4m, hZ4big, hZ4bd⟩ :=
    hL nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  set Dl : ℕ := Kc - m with hDl
  set k : ℝ := (Dl : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  set u : ℝ := (h : ℝ) ^ ((1 : ℝ) / 2) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by linarith only [hh1]) _
  set W : ℝ := (1 + k) * (3 : ℝ) ^ (-k) with hWdef
  have hW0 : 0 < W := by rw [hWdef]; have : (0:ℝ) < (3:ℝ) ^ (-k) := Real.rpow_pos_of_pos (by norm_num) _; positivity
  have hW1 : W ≤ 1 := by rw [hWdef, hk, hDl]; exact one_add_mul_three_pow_le_one _
  -- the Γ₂ amplitude of the gap observable
  set Zg : ShellSeq d → ℝ := fun ω => Cnd * (Zw ω ^ ((1 : ℝ) / 5) * Z4 ω ^ ((4 : ℝ) / 5) + Za ω)
    with hZg
  have hA0 : 0 < Cw * S⁻¹ * W := by positivity
  have hB0 : 0 < C4 * S⁻¹ * u := by positivity
  have hC0 : 0 < Ca * S⁻¹ * W := by positivity
  have hcomb := SuperdiffusionCLT.Section3.Setup.isBigO_gammaSigma_rpow_mul_add (mu := P.toMeasure) (Za := Zw) (Zb := Z4)
    (Zc := Za) hA0 hB0 hC0 hZw0 hZ40 hZwm hZ4m hZam hZwbig hZ4big hZabig
  set Y : ℝ := (h : ℝ) ^ ((2 : ℝ) / 5) * (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) with hY
  have hY0 : 0 < Y := by
    rw [hY]
    have : (0 : ℝ) < (3 : ℝ) ^ (-(k / 5)) := Real.rpow_pos_of_pos (by norm_num) _
    have : (0 : ℝ) < (h : ℝ) ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos (by linarith only [hh1]) _
    have : (0 : ℝ) < (1 + k) ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos (by linarith only [hk0]) _
    positivity
  have hZgbig : IsBigO P.toMeasure (gammaSigma 2) Zg (Kg * S⁻¹ * Y) := by
    refine (hcomb.const_mul (c := Cnd) hCnd.le).mono_scale ?_
    have hAB : (Cw * S⁻¹ * W) ^ ((1 : ℝ) / 5) * (C4 * S⁻¹ * u) ^ ((4 : ℝ) / 5) =
        Cw ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) * (S⁻¹ * Y) := by
      have e1 : C4 * S⁻¹ * u = (C4 * u) * S⁻¹ := by ring
      have e2 := amplitude_rpow_mul Cw (C4 * u) S⁻¹ k hCw.le (by positivity) hSi hk0
      have e3 : (C4 * u) ^ ((4 : ℝ) / 5) = C4 ^ ((4 : ℝ) / 5) * (h : ℝ) ^ ((2 : ℝ) / 5) := by
        rw [Real.mul_rpow hC4.le hu0.le, hudef, ← Real.rpow_mul (by linarith only [hh1])]
        norm_num
      rw [e1, hWdef]
      rw [e2, e3, hY]
      ring
    have hWY : W ≤ (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
      have hWr : W ^ ((1 : ℝ) / 5) = (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
        rw [hWdef, Real.mul_rpow (by linarith only [hk0]) (Real.rpow_nonneg (by norm_num) _),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        congr 2; ring
      rw [← hWr]
      calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
        _ ≤ W ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow_of_exponent_ge hW0 hW1 (by norm_num)
    have hhp : (1 : ℝ) ≤ (h : ℝ) ^ ((2 : ℝ) / 5) := Real.one_le_rpow hh1 (by norm_num)
    have hCc : Ca * S⁻¹ * W ≤ Ca * (S⁻¹ * Y) := by
      have : W ≤ Y := by
        rw [hY]
        have hV0 : (0 : ℝ) ≤ (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := by
          have : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k / 5)) := Real.rpow_nonneg (by norm_num) _
          have : (0 : ℝ) ≤ (1 + k) ^ ((1 : ℝ) / 5) := Real.rpow_nonneg (by linarith only [hk0]) _
          positivity
        calc W ≤ (1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5)) := hWY
          _ = 1 * ((1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5))) := (one_mul _).symm
          _ ≤ (h : ℝ) ^ ((2 : ℝ) / 5) * ((1 + k) ^ ((1 : ℝ) / 5) * (3 : ℝ) ^ (-(k / 5))) :=
            mul_le_mul_of_nonneg_right hhp hV0
          _ = _ := by ring
      calc Ca * S⁻¹ * W = Ca * (S⁻¹ * W) := by ring
        _ ≤ Ca * (S⁻¹ * Y) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left this hSi.le) hCa.le
    have hinner : gammaTriangleConst 2 *
        (SuperdiffusionCLT.Probability.orliczProductConst 10 (5 / 2) *
          ((Cw * S⁻¹ * W) ^ ((1 : ℝ) / 5) * (C4 * S⁻¹ * u) ^ ((4 : ℝ) / 5)) + Ca * S⁻¹ * W) ≤
        gammaTriangleConst 2 * (SuperdiffusionCLT.Probability.orliczProductConst 10 (5 / 2) *
          (Cw ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5)) + Ca) * (S⁻¹ * Y) := by
      rw [hAB]
      have : 0 ≤ S⁻¹ * Y := by positivity
      calc _ ≤ gammaTriangleConst 2 * (SuperdiffusionCLT.Probability.orliczProductConst 10 (5 / 2) *
              (Cw ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) * (S⁻¹ * Y)) + Ca * (S⁻¹ * Y)) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl hCc) htri.le
        _ = _ := by ring
    calc Cnd * (gammaTriangleConst 2 *
        (SuperdiffusionCLT.Probability.orliczProductConst 10 (5 / 2) *
          ((Cw * S⁻¹ * W) ^ ((1 : ℝ) / 5) * (C4 * S⁻¹ * u) ^ ((4 : ℝ) / 5)) + Ca * S⁻¹ * W))
        ≤ Cnd * (gammaTriangleConst 2 * (SuperdiffusionCLT.Probability.orliczProductConst 10 (5 / 2) *
          (Cw ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5)) + Ca) * (S⁻¹ * Y)) :=
          mul_le_mul_of_nonneg_left hinner hCnd.le
      _ = Kg * S⁻¹ * Y := by rw [hKg]; ring
  -- the pointwise bound
  have hND : ∀ ω, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
      (fun x => (wN ω).toH1Function.grad x - (wD ω).toH1Function.grad x) ≤
        ENNReal.ofReal (Zg ω) := by
    intro ω
    have hND0 : vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => (wN ω).toH1Function.grad x - (wD ω).toH1Function.grad x) ≤
        ENNReal.ofReal Cnd *
            (vecHatNegENormOrderOne (originCube d (Kc : ℤ))
              (fun x => hshellFlux nu P m h ω e x - volumeAverageVec
                (cubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h ω e))) ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (Kc : ℤ)) 4
              (fun x => hshellFlux nu P m h ω e x - volumeAverageVec
                (cubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h ω e))) ^ ((4 : ℝ) / 5) +
          ENNReal.ofReal Cnd * ‖HilbertVec.ofVec (volumeAverageVec
            (cubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h ω e))‖ₑ := by
      refine le_trans ((hCs Kc _ (wD ω) (wN ω) (hwD ω) (hwN ω)).2.2.2) ?_
      exact add_le_add (mul_le_mul' (mul_le_mul' hCle le_rfl) le_rfl) (mul_le_mul' hCle le_rfl)
    have := SuperdiffusionCLT.Section3.Setup.vecCubeLpENorm_grad_sub_le_of_responseNDWeak
      (hNDweak := hND0) (hZw0 ω) (hZ40 ω) (hZa0 ω) (hZwbd ω) (hZ4bd ω) (hZabd ω)
    refine this.trans ?_
    rw [← ENNReal.ofReal_mul hCnd.le]
  -- the second moment
  have hZg0 : ∀ ω, 0 ≤ Zg ω := fun ω => by
    have := hZw0 ω; have := hZ40 ω; have := hZa0 ω; rw [hZg]; positivity
  have hZgm : Measurable Zg :=
    (((hZwm.pow_const _).mul (hZ4m.pow_const _)).add hZam).const_mul _
  have hamp : 0 < Kg * S⁻¹ * Y := by positivity
  have hint := SuperdiffusionCLT.Section3.Setup.integrable_sq_of_isBigO_gammaSigma_two
    (mu := P.toMeasure) hamp hZgm.aemeasurable hZgbig
  have hmom := SuperdiffusionCLT.Section3.Setup.integral_sq_le_of_isBigO_gammaSigma_two
    (mu := P.toMeasure) hamp hZgm.aemeasurable hZgbig
  have hG2 : Real.Gamma 2 = 1 := by
    simp
  rw [hG2] at hmom
  calc ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x - (wD omega).toH1Function.grad x) ^ (2 : ℕ)
          ∂P.toMeasure
      ≤ ∫⁻ omega, ENNReal.ofReal (Zg omega ^ 2) ∂P.toMeasure := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.ofReal_pow (hZg0 ω)]
        exact pow_le_pow_left' (hND ω) 2
    _ = ENNReal.ofReal (∫ omega, Zg omega ^ 2 ∂P.toMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ ENNReal.ofReal ((Kg * S⁻¹ * Y) ^ 2 * (1 + 1)) := ENNReal.ofReal_le_ofReal hmom
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hY2 := rate_sq_eq (h : ℝ) k (by linarith only [hh1]) hk0
        have hSs : S ^ (-(2 : ℝ)) = S⁻¹ ^ 2 := by
          rw [Real.rpow_neg hS.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            inv_pow]
        rw [hSs]
        have hrate : (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + k) ^ ((2 : ℝ) / 5) *
            (3 : ℝ) ^ (-((2 : ℝ) / 5 * k)) = Y ^ 2 := by rw [hY]; exact hY2.symm
        rw [show (max 1 (2 * Kg ^ 2)) * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + k) ^ ((2 : ℝ) / 5) *
          (3 : ℝ) ^ (-((2 : ℝ) / 5 * k)) * S⁻¹ ^ 2 = (max 1 (2 * Kg ^ 2)) * (Y ^ 2 * S⁻¹ ^ 2) by
          rw [← hrate]; ring]
        have hq : 0 ≤ Y ^ 2 * S⁻¹ ^ 2 := by positivity
        calc (Kg * S⁻¹ * Y) ^ 2 * (1 + 1) = (2 * Kg ^ 2) * (Y ^ 2 * S⁻¹ ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hq

end SuperdiffusionCLT.Section5
