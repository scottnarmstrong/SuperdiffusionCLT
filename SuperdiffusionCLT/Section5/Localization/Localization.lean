/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.LocalizationC
public import SuperdiffusionCLT.Section5.Thresholds.HomogBelowAtScales
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# `lem.localization`: the two localization-error terms

The proof of `lem.localization` proceeds as follows. Step 1 is `abs_volumeAverage_slope_add_le`:
`|⨍_Q (2P_z + S̃_z) · A_m S̃_z| ≤ √⟪F_z,F_z⟫ (2√⟪S_z,S_z⟫ + √⟪F_z,F_z⟫)`.  The weighted
arithmetic-geometric mean inequality bounds the right-hand side by `λ ⟪S_z,S_z⟫ + (λ⁻¹+1) ⟪F_z,F_z⟫`,
and the two expectations, averaged over the subcubes, are bounded by `crude_Sz_bound`
(`C ν⁻⁴ m⁴`) and `crude_Fz_bound` (`C (ν⁻¹m)^{-190}`).  The two are added under the integral, which
needs `⟪S_z,S_z⟫` measurable in the sample (`loc_measurable_pairing_S`); with `λ = (ν⁻¹m)^{-90}` the
sum is at most `C m^{-50}`.  The energy gap of the Neumann and Dirichlet gradients, the input of
`crude_Fz_bound`, is `loc_gap_scaled`; `ν⁻² ≤ m` is `m_large_of_lNaught`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization

open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2 SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

/-- **Satisfiability of the non-law hypotheses of the localization-error estimate**: for every
parameter choice with `n ≤ Kc` the two response families exist, and the minimizers `S̃_z` exist on
every subcube, for every sample. -/
theorem localization_hypotheses_satisfiable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h Kc n : ℕ) (hn : n ≤ Kc) (e e' : Vec d) :
    ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
      (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega e) (wD omega)) ∧
      (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
        (hshellFlux nu P m h omega e') (wN omega)) ∧
      ∃ Stilde : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → TriadicCube d → BlockState d,
        ∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
          IsBlockOffsetMinimizer
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
            (cubeSet Q)
            (blockFluct nu (m - h) P Q (wD omega).toH1Function.grad
              (fun y => (wN omega).toH1Function.grad y + hshellFlux nu P m h omega e' y))
            (Stilde omega Q) := by
  choose wD hwD using fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
    exists_isCubeDirichletResponse (originCube d (Kc : ℤ)) (memVectorL2_hshellFlux nu P omega e Kc)
  choose wN hwN using fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
    exists_isCubeNeumannResponse (originCube d (Kc : ℤ)) (memVectorL2_hshellFlux nu P omega e' Kc)
  refine ⟨wD, wN, hwD, hwN, ?_⟩
  have hk' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hex : ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (Q : TriadicCube d),
      ∃ X : BlockState d, Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ) →
        IsBlockOffsetMinimizer
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega m).toCoeffField
          (cubeSet Q)
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

end SuperdiffusionCLT.Section5
