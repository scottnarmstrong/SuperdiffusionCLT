/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Neumann.NeumannInputD

/-!
# `lem.neumann.input`

The Neumann-input evaluation (`e.neumann.estimate.explicit`) in the shape consumed
by `cor.upper.ratio`: the `limsup` over the cube size `Kc`, of the subcube average of the annealed
block norm, is at most `1 + c⋆ (log 3) h shom_{m-h}^{-2} + K shom_{m-h}^{-2}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

/-- **`lem.neumann.input`.** -/
theorem neumann_input (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        ∀ (cStar K : ℝ),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ m h : ℕ, 1 ≤ h → 400 * h ≤ m → ∀ n : ℕ, ∀ e' : Vec d, vecNormSq e' = 1 →
        ∀ wN : (Kc : ℕ) → SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
            H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))),
          (∀ Kc : ℕ, 100 * m ≤ Kc → ∀ omega,
            SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e') (wN Kc omega)) →
          Filter.limsup (fun Kc : ℕ =>
            subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
              (blockVecDot
                (ahomSqrtApply nu (m - h) P
                  (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
                    (ahomInvSqrtApply nu (m - h) P
                      (e', volumeAverageVec (cubeSet Q)
                        (fun y => (wN Kc omega).toH1Function.grad y +
                          hshellFlux nu P m h omega e' y)))))
                (ahomSqrtApply nu (m - h) P
                  (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
                    (ahomInvSqrtApply nu (m - h) P
                      (e', volumeAverageVec (cubeSet Q)
                        (fun y => (wN Kc omega).toH1Function.grad y +
                          hshellFlux nu P m h omega e' y)))))) ∂P.toMeasure))
            Filter.atTop ≤
          ENNReal.ofReal (1 + cStar * Real.log 3 * (h : ℝ) * (sigmaBarInfinite nu (m - h) P) ^
            (-(2 : ℝ)) + K * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))) := by
  intro nu hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 cStar K hJ5 m h h1 hmh n e' he wN hwN
  obtain ⟨C, hC1, H⟩ := response_estimates d hd
  have hs : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set s := sigmaBarInfinite nu (m - h) P with hsdef
  set r : ℕ → ℝ := fun Kc => C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
    (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) with hr
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have h0 := tendsto_tail.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat m))
    have h2 := h0.const_mul (C * (h : ℝ) ^ ((4 : ℝ) / 5))
    rw [mul_zero] at h2
    refine h2.congr fun Kc => ?_
    simp only [hr, Function.comp_apply, mul_assoc]
  set Y : ℕ → ℝ := fun Kc => 1 + (cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)) +
    (r Kc + K) * s ^ (-(2 : ℝ))) with hY
  have hYlim : Tendsto Y atTop
      (𝓝 (1 + cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)) + K * s ^ (-(2 : ℝ)))) := by
    have h3 : Tendsto (fun Kc => 1 + (cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)) +
        (r Kc + K) * s ^ (-(2 : ℝ)))) atTop
        (𝓝 (1 + (cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)) +
          (0 + K) * s ^ (-(2 : ℝ))))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.add ((hrlim.add_const K).mul_const _))
    convert h3 using 2
    ring
  have hev : ∀ᶠ Kc : ℕ in atTop, subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal
      (blockVecDot
        (ahomSqrtApply nu (m - h) P
          (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
            (ahomInvSqrtApply nu (m - h) P
              (e', volumeAverageVec (cubeSet Q)
                (fun y => (wN Kc omega).toH1Function.grad y +
                  hshellFlux nu P m h omega e' y)))))
        (ahomSqrtApply nu (m - h) P
          (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
            (ahomInvSqrtApply nu (m - h) P
              (e', volumeAverageVec (cubeSet Q)
                (fun y => (wN Kc omega).toH1Function.grad y +
                  hshellFlux nu P m h omega e' y)))))) ∂P.toMeasure) ≤
      ENNReal.ofReal (Y Kc) := by
    filter_upwards [eventually_ge_atTop (max (100 * m) n)] with Kc hKc
    have hKm : 100 * m ≤ Kc := (le_max_left _ _).trans hKc
    have hKn : n ≤ Kc := (le_max_right _ _).trans hKc
    obtain ⟨wD, -, hwD, -, -⟩ :=
      SuperdiffusionCLT.Section5.exists_response_data hd nu P m h Kc e'
    obtain ⟨hA, -, hE⟩ := H nu hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 cStar K hJ5 m h Kc h1 hmh hKm
      e' he.le wD (wN Kc) hwD (hwN Kc hKm)
    obtain ⟨-, hEN⟩ := hE he
    have hg : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
        ((wN Kc omega).toH1Function.grad) := fun omega =>
      MeasureTheory.MemLp.of_eval (wN Kc omega).toH1Function.gradMemL2
    have hfin := lintegral_sq_ne_top_of_lintegral_pow_eight P.toMeasure
      (fun omega => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad)
      (fun omega => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 8 (wN Kc omega).toH1Function.grad)
      (fun omega => SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
        (originCube d (Kc : ℤ)) 2 (wN Kc omega).toH1Function.grad)
      (fun omega => vecCubeLpENorm_mono_exponent _ (by norm_num) _) ENNReal.ofReal_ne_top hA
    have hy := (abs_le.1 hEN).2
    exact lintegral_subcubeAvg_neumann_le nu P m h hs hKn e' he
      (fun omega => (wN Kc omega).toH1Function.grad) hg hfin
      (y := cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)) + (r Kc + K) * s ^ (-(2 : ℝ)))
      (by linarith only [hy])
  calc _ ≤ Filter.limsup (fun Kc => ENNReal.ofReal (Y Kc)) atTop :=
        Filter.limsup_le_limsup hev
    _ = ENNReal.ofReal (1 + cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)) +
          K * s ^ (-(2 : ℝ))) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp hYlim).limsup_eq

/-- **Satisfiability witness** for the non-law hypotheses of `neumann_input`: a unit vector `e'` and
a family of Neumann responses on every cube `cu_Kc`, for every `nu`, `P`, `m`, `h`. -/
theorem exists_neumann_input_data (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) :
    ∃ e' : Vec d, vecNormSq e' = 1 ∧
      ∃ wN : (Kc : ℕ) → SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
            H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))),
        ∀ Kc : ℕ, 100 * m ≤ Kc → ∀ omega,
          SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e') (wN Kc omega) := by
  refine ⟨Pi.single 0 1, ?_, ?_⟩
  · simp [vecNormSq, vecDot, Pi.single_apply]
  · have hex : ∀ Kc : ℕ, ∃ wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
        H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))),
        ∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
          (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega (Pi.single 0 1)) (wN omega) := by
      intro Kc
      obtain ⟨wD, wN, -, hN, -⟩ :=
        SuperdiffusionCLT.Section5.exists_response_data hd nu P m h Kc (Pi.single 0 1)
      exact ⟨wN, hN⟩
    choose wN hwN using hex
    exact ⟨wN, fun Kc _ => hwN Kc⟩

end SuperdiffusionCLT.Section5
