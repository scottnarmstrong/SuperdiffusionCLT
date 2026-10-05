/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.EnergyComparison

/-!
# The stationary comparison and the energy clause of `lem.response`, concrete flux

Continues `EnergyComparison.lean`. `wholeSpace_sandwich_hshellFlux` is the sandwich
`E ‖∇w_D‖² ≤ E |∇ŵ_e(0)|² ≤ E ‖∇w_N‖²` for the concrete flux `hshellFlux`, the whole-space
potential being the one of `exists_gradHatW_hshellFlux`.  `abs_energy_sub_hshell_le` combines it with
the gap identity and `abs_wholeSpaceEnergy_hshellFlux_sub_le` (nondegeneracy at `(m - h, m)`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Probability.Stationary
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The stationary comparison at `ShellSeq d`.**  For the flux `hshellFlux nu P m h · e` on `cu_Kc`
there is a whole-space potential `gradHatW` (the projection characterization `hproj`) with
`E ‖∇w_D‖² ≤ E |∇ŵ(0)|² ≤ E ‖∇w_N‖²`. -/
theorem wholeSpace_sandwich_hshellFlux [NeZero d] (hd : 2 ≤ d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) (m h Kc : ℕ) (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wN omega)) :
    ∃ (gradHatW : ShellSeq d → Vec d)
      (hFmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) 2 P.toMeasure)
      (hGmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
      (hGmemLp.toLp fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) =
        -@stationaryPotentialProjection d (ShellSeq d) _ P.toMeasure _ _
          (ShellField.vaddInvariantMeasure hPrefix hJ2)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (hshellFlux nu P m h omega e 0)) ∧
      (∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure ≤
        ∫⁻ omega, ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) ∧
      (∫⁻ omega, ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure) := by
  have hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure :=
    ShellField.vaddInvariantMeasure hPrefix hJ2
  obtain ⟨hF, gradHatW, hG, hproj⟩ := exists_gradHatW_hshellFlux hJ3 nu m h e hunit
  obtain ⟨uReal, hgrad, hueq⟩ :=
    SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization d hd P.toMeasure
      (fun omega => hshellFlux nu P m h omega e) gradHatW Kc (hshellFlux_cocycle nu P m h e)
      hF hG hproj
  have hmp : MeasureTheory.MeasurePreserving (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1)
      (P.toMeasure.prod (normalizedCubeMeasure (originCube d (Kc : ℤ)))) P.toMeasure :=
    ⟨measurable_vadd_shellSeq (d := d), map_vadd_prod_eq (P := P)⟩
  have hjointG : AEStronglyMeasurable
      (fun p : ShellSeq d × Vec d => HilbertVec.ofVec (gradHatW (p.2 +ᵥ p.1)))
      (P.toMeasure.prod (normalizedCubeMeasure (originCube d (Kc : ℤ)))) :=
    hG.aestronglyMeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have hjointF : AEStronglyMeasurable
      (fun p : ShellSeq d × Vec d => HilbertVec.ofVec (hshellFlux nu P m h (p.2 +ᵥ p.1) e 0))
      (P.toMeasure.prod (normalizedCubeMeasure (originCube d (Kc : ℤ)))) :=
    hF.aestronglyMeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have hDresp : ∀ omega, IsDirichletResponse omega m (m - h) Kc
      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ • e)
      (wD omega) := by
    intro omega
    have := hwD omega
    rw [hshellFlux_eq_dirichletRhsField] at this
    exact this
  have hNresp : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (dirichletRhsField omega m (m - h)
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ • e))
      (wN omega) := by
    intro omega
    have := hwN omega
    rw [hshellFlux_eq_dirichletRhsField] at this
    exact this
  have hDmeas := aestronglyMeasurable_vecCubeLpENorm_grad (mu := P.toMeasure) hDresp
  have hNmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (wN omega).toH1Function.grad) P.toMeasure :=
    (measurable_vecCubeLpENorm_grad_of_isCubeNeumannResponse hNresp).aestronglyMeasurable
  obtain ⟨hlow, hup⟩ :=
    SuperdiffusionCLT.Frozen.Section3.responseFields_stationary d hd P.toMeasure
      (fun omega => hshellFlux nu P m h omega e) gradHatW Kc wD wN hDmeas hNmeas uReal hjointG
      hjointF hgrad hueq (hshellFlux_cocycle nu P m h e) hF hG hproj hwD hwN
  exact ⟨gradHatW, hF, hG, hproj, hlow, hup⟩

/-- A real number to the power `-2` (real exponent) is nonnegative, for every base. -/
theorem rpow_neg_two_nonneg (s : ℝ) : 0 ≤ s ^ (-(2 : ℝ)) := by
  have h : s ^ (-(2 : ℝ)) = (s ^ 2)⁻¹ := by
    have h1 : (-(2 : ℝ)) = (((-2 : ℤ)) : ℝ) := by norm_num
    rw [h1, Real.rpow_intCast, zpow_neg, zpow_ofNat]
  rw [h]
  exact inv_nonneg.2 (sq_nonneg s)

/-- **The energy clause of `lem.response` (`e.response.energy`), from the gap bound.**  Let
`B = (C h^{4/5} (1 + (Kc - m))^{2/5} 3^{-(2/5)(Kc - m)}) shom_{m-h}^{-2}` and suppose
`E ‖∇w_N - ∇w_D‖²_{L̲²(cu_Kc)} ≤ B` (the second-moment form of the weak-norm bound).  Then both
cube energies lie within `B + K shom_{m-h}^{-2}` of `cStar (log 3) h shom_{m-h}^{-2}`. -/
theorem abs_energy_sub_hshell_le [NeZero d] (hd : 2 ≤ d)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) {cStar K : ℝ} (hJ5 : ShellLawJ5 d P cStar K hPrefix hJ2 hJ3)
    (nu : ℝ) {m h Kc : ℕ} (h1 : 1 ≤ h) (hh : h ≤ m) (e : Vec d)
    (he : vecNormSq e = 1) {C : ℝ} (hC : 0 ≤ C)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega))
    (hwN : ∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wN omega))
    (hgap : ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x - (wD omega).toH1Function.grad x) ^ (2 : ℕ)
        ∂P.toMeasure ≤
      ENNReal.ofReal (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)))) :
    |(∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure).toReal -
        cStar * Real.log 3 * (h : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))| ≤
      (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
          (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) + K) *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) ∧
    |(∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure).toReal -
        cStar * Real.log 3 * (h : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))| ≤
      (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
          (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) + K) *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) := by
  have hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure :=
    ShellField.vaddInvariantMeasure hPrefix hJ2
  have hunit : Book.Ch02.vecNorm e = 1 := by
    have h2 := Book.Ch02.vecNorm_sq_eq_vecNormSq e
    rw [he] at h2
    exact (pow_eq_one_iff_of_nonneg (Book.Ch02.vecNorm_nonneg e) two_ne_zero).1 h2
  set s := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P with hs
  set B : ℝ := C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
        (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) * s ^ (-(2 : ℝ)) with hB
  have hB0 : 0 ≤ B := by
    have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    have hx0 : (0 : ℝ) ≤ 1 + ((Kc - m : ℕ) : ℝ) := by positivity
    have := rpow_neg_two_nonneg s
    rw [hB]
    positivity
  obtain ⟨gradHatW, hF, hG, hproj, hlow, hup⟩ :=
    wholeSpace_sandwich_hshellFlux hd hPrefix hJ2 hJ3 nu m h Kc e hunit wD wN hwD hwN
  have hDresp : ∀ omega, IsDirichletResponse omega m (m - h) Kc (s⁻¹ • e) (wD omega) := by
    intro omega
    have := hwD omega
    rw [hshellFlux_eq_dirichletRhsField] at this
    exact this
  have hDmeas := aestronglyMeasurable_vecCubeLpENorm_grad (mu := P.toMeasure) hDresp
  have hnd := abs_wholeSpaceEnergy_hshellFlux_sub_le hPrefix hJ2 hJ3 hJ5 nu h1 hh e hunit
    gradHatW hF hG hproj
  have hD := abs_toReal_sub_wholeSpaceEnergy_le hwD hwN hDmeas hG hlow hup hB0 hgap
  have hN := abs_toReal_neumann_sub_wholeSpaceEnergy_le hwD hwN hDmeas hG hlow hup hB0 hgap
  have hrhs : (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
          (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) + K) * s ^ (-(2 : ℝ)) =
      B + K * s ^ (-(2 : ℝ)) := by
    rw [hB]
    ring
  rw [hrhs]
  constructor
  · calc _ = |((∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure).toReal -
            wholeSpaceEnergy P.toMeasure gradHatW) +
          (wholeSpaceEnergy P.toMeasure gradHatW - cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)))| := by
          congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hD hnd)
  · calc _ = |((∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
              (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure).toReal -
            wholeSpaceEnergy P.toMeasure gradHatW) +
          (wholeSpaceEnergy P.toMeasure gradHatW - cStar * Real.log 3 * (h : ℝ) * s ^ (-(2 : ℝ)))| := by
          congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hN hnd)

/-- **Satisfiability.**  The response hypotheses `hwD`, `hwN` of the two theorems above are
inhabited for every shell law, unit direction and scales: the flux `hshellFlux` is square integrable
on the cube.  (The gap bound `hgap` is the output of the weak-norm bound and is not asserted here.) -/
theorem exists_responses_hshellFlux [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (e : Vec d) :
    ∃ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
      (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega e) (wD omega)) ∧
      (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega e) (wN omega)) := by
  have hmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (hshellFlux nu P m h omega e) := by
    intro omega
    rw [hshellFlux_eq_dirichletRhsField]
    exact memVectorL2_dirichletRhsField omega m (m - h) Kc _
  choose wD hwD using fun omega : ShellSeq d =>
    exists_isCubeDirichletResponse (originCube d (Kc : ℤ)) (hmem omega)
  choose wN hwN using fun omega : ShellSeq d =>
    exists_isCubeNeumannResponse (originCube d (Kc : ℤ)) (hmem omega)
  exact ⟨wD, wN, hwD, hwN⟩

end

end SuperdiffusionCLT.Section5
