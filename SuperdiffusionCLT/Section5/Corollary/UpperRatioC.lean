/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.UpperRatioB

/-!
# `cor.upper.ratio`: the per-cube-size inequality

For every `Kc ≥ n`, `shom_m |p|²` is at most the sum of the subcube average of the principal term and the
subcube average of a measurable majorant of the cell errors.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields SuperdiffusionCLT.Section2.Localization
open scoped ENNReal

variable {d : ℕ}

theorem upperRatio_lintegral_subcubeAvg {Kc n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : TriadicCube d → Ω → ℝ≥0∞)
    (hf : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (f Q)) :
    ∫⁻ ω, subcubeAvg Kc n (fun Q => f Q ω) ∂μ = subcubeAvg Kc n (fun Q => ∫⁻ ω, f Q ω ∂μ) := by
  unfold subcubeAvg
  by_cases hD : (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card = 0
  · rw [Finset.card_eq_zero.mp hD]; simp
  · have hne : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (by exact_mod_cast hD)
    rw [lintegral_const_mul' _ _ hne, lintegral_finsetSum _ hf]

/-- Minimizers of the cell problem with offset the fluctuation exist, for the given response fields. -/
theorem upperRatio_exists_stilde [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc n : ℕ) (hn : n ≤ Kc) (e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))) :
    ∃ Stilde : ShellSeq d → TriadicCube d → BlockState d,
      ∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
          (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
          (Stilde omega Q) := by
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hex : ∀ (omega : ShellSeq d) (Q : TriadicCube d),
      ∃ X : BlockState d, Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ) →
        IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
          (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y)) X := by
    intro omega Q
    by_cases hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)
    · have hsub := openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
      obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
      have hFL2 := loc_isBlockL2_blockFluct nu (m - h) P Q
        (g1 := (wD omega).toH1Function.grad)
        (g2 := fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y)
        (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub (memVectorL2_grad _))
        (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hsub
          ((memVectorL2_grad (wN omega).toH1Function).add (memVectorL2_hshellFlux nu P omega e' Kc)))
      obtain ⟨X, hX, -⟩ := exists_isBlockOffsetMinimizer_cubeSet Q hEll hFL2.1 hFL2.2
      exact ⟨X, fun _ => hX⟩
    · exact ⟨constBlockState 0, fun h' => absurd h' hQ⟩
  choose S hS using hex
  exact ⟨S, fun omega Q hQ => hS omega Q hQ⟩


theorem upperRatio_perKc [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m h Kc n : ℕ) (hn : n ≤ Kc) (e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega (0 : Vec d)) (wD omega))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wN omega))
    (B : TriadicCube d → ShellSeq d → ℝ≥0∞)
    (hBm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), Measurable (B Q))
    (hBp : ∀ Stilde : ShellSeq d → TriadicCube d → BlockState d,
      (∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        IsBlockOffsetMinimizer (coefficientCutoff nu omega m).toCoeffField (cubeSet Q)
          (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
          (Stilde omega Q)) →
      ∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x => blockVecDot
          ((2 : ℝ) • blockSlope nu (m - h) P Q (0 : Vec d) e' (wD omega).toH1Function.grad
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) +
            (Stilde omega Q).eval x)
          (blockMatVecMul (blockCoeffField (coefficientCutoff nu omega m).toCoeffField x)
            ((Stilde omega Q).eval x)))| ≤ B Q omega)
    (X Y : ℝ≥0∞)
    (hX : subcubeAvg Kc n (fun Q => ∫⁻ omega, ENNReal.ofReal (blockVecDot
        (blockSlope nu (m - h) P Q (0 : Vec d) e' (wD omega).toH1Function.grad
          (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
        (blockMatVecMul (localizationCoarseAt nu m Q omega)
          (blockSlope nu (m - h) P Q (0 : Vec d) e' (wD omega).toH1Function.grad
            (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))))
        ∂P.toMeasure) ≤ X)
    (hY : subcubeAvg Kc n (fun Q => ∫⁻ omega, B Q omega ∂P.toMeasure) ≤ Y) :
    ENNReal.ofReal (sigmaBarSeq nu m P Kc *
      vecNormSq ((sigmaBarInfinite nu (m - h) P) ^ (-(1 : ℝ) / 2) • e')) ≤ X + Y := by
  set s := sigmaBarInfinite nu (m - h) P with hs
  set slope : ShellSeq d → TriadicCube d → BlockVec d := fun omega Q =>
    blockSlope nu (m - h) P Q (0 : Vec d) e' (wD omega).toH1Function.grad
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) with hslope
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hsubQ : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)) := fun Q hQ =>
    openCubeSet_subset_of_mem_descendantsAtScale hk' hQ
  obtain ⟨Stilde, hSt⟩ := upperRatio_exists_stilde hnu P m h Kc n hn e' wD wN
  obtain ⟨S, hS⟩ := loc_exists_minimizers (d := d) hnu m slope
  have hMD : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (wD omega).toH1Function.grad := fun omega => memVectorL2_grad _
  have hMG : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y) :=
    fun omega => (memVectorL2_grad _).add (memVectorL2_hshellFlux nu P omega e' Kc)
  -- the pointwise inequality
  have hpt : ∀ omega, ENNReal.ofReal (blockVecDot ((s ^ (-(1 : ℝ) / 2) • e', (0 : Vec d)))
      (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
        (coefficientCutoff nu omega m).toCoeffField) ((s ^ (-(1 : ℝ) / 2) • e', (0 : Vec d))))) ≤
      subcubeAvg Kc n (fun Q => ENNReal.ofReal (blockVecDot (slope omega Q)
        (blockMatVecMul (localizationCoarseAt nu m Q omega) (slope omega Q))) + B Q omega) := by
    intro omega
    obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m
      (originCube d (Kc : ℤ))
    have hGo := upperRatio_state_admissible (U := openCubeSet (originCube d (Kc : ℤ))) s
      (0 : Vec d) e' (hMD omega) (wD omega).isPotentialZeroTraceOn (hMG omega)
      (upperRatio_solenoidal _ (memVectorL2_hshellFlux nu P omega e' Kc) (hwN omega))
    rw [smul_zero] at hGo
    have hG := (isBlockOffsetAdmissible_constBlockState_iff _ _ _).1
      ((isBlockOffsetAdmissible_cubeSet_iff_openCubeSet (originCube d (Kc : ℤ))
      (constBlockState _) _).2 ((isBlockOffsetAdmissible_constBlockState_iff _ _ _).2 hGo))
    refine upperRatio_pointwise hn hEll
      (fun Q => exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q) hG
      (Pz := fun Q => slope omega Q)
      (Fz := fun Q => blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
        (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
      ?_ (S := fun Q => S omega Q) (St := fun Q => Stilde omega Q) (fun Q _ => hS omega Q)
      (fun Q hQ => hSt omega Q hQ) (B := fun Q => B Q omega) ?_
    · intro Q hQ x hx
      refine ⟨?_, ?_⟩
      · simp only [upperRatio_state, hslope, blockSlope, ahomInvSqrtApply, blockFluct, ← smul_add]
        congr 1
        abel
      · simp only [upperRatio_state, hslope, blockSlope, ahomInvSqrtApply, blockFluct, ← smul_add]
        congr 1
        abel
    · intro Q hQ
      exact hBp Stilde hSt omega Q hQ
  have hSm : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      Measurable fun omega => ENNReal.ofReal (blockVecDot (slope omega Q)
        (blockMatVecMul (localizationCoarseAt nu m Q omega) (slope omega Q))) := by
    intro Q hQ
    have hm := loc_measurable_pairing_S hnu P m h Kc (0 : Vec d) e' wD wN hwD hwN (hsubQ Q hQ)
      (fun omega => S omega Q) (fun omega => hS omega Q)
    have heq : (fun omega => ENNReal.ofReal (blockVecDot (slope omega Q)
        (blockMatVecMul (localizationCoarseAt nu m Q omega) (slope omega Q)))) =
        fun omega => ENNReal.ofReal (blockPairingAverage (cubeSet Q)
          (coefficientCutoff nu omega m).toCoeffField (S omega Q) (S omega Q)) := by
      funext omega
      obtain ⟨lam, Lam, hEll⟩ := exists_isEllipticFieldOn_coefficientCutoff_cubeSet hnu omega m Q
      rw [blockPairingAverage_self_eq_coarseBlockMatrix Q hEll _ (hS omega Q)]
      rfl
    rw [heq]
    exact hm
  have hge := upperRatio_lintegral_ge hnu hPrefix hJ2 hJ3 hJ4 m Kc (s ^ (-(1 : ℝ) / 2) • e')
  refine hge.trans ((lintegral_mono hpt).trans ?_)
  rw [upperRatio_lintegral_subcubeAvg (fun Q omega => ENNReal.ofReal (blockVecDot (slope omega Q)
    (blockMatVecMul (localizationCoarseAt nu m Q omega) (slope omega Q))) + B Q omega)
    (fun Q hQ => (hSm Q hQ).add (hBm Q hQ))]
  refine (subcubeAvg_mono_on fun Q hQ => (lintegral_add_left (hSm Q hQ) _).le).trans ?_
  rw [subcubeAvg_add]
  exact add_le_add hX hY

end SuperdiffusionCLT.Section5
