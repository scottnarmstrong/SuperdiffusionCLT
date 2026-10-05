/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffset
public import SuperdiffusionCLT.Section3.ResponseFields.ResponseHessianExistence

/-!
# The response fields of the shell flux exist, with weak Hessians

The non-law hypotheses of the response estimates of `lem.response` are satisfiable: for every
shell sequence the flux `hshellFlux` is `shom_{m-h}^{-1}` times `(k_m - k_{m-h}) e`, which is the
flux `dirichletRhsField` of the direction `shom_{m-h}^{-1} e`, so the Dirichlet and Neumann
responses exist on every cube, and the Dirichlet response has a weak Hessian
(`Section3.ResponseFields.exists_hasWeakHessianOn_dirichletResponse`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

/-- The flux `hshellFlux` is the stream flux of the rescaled direction. -/
theorem responseData_hshellFlux_eq_dirichletRhsField [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (m h : ℕ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e : Vec d) :
    hshellFlux nu P m h omega e =
      SuperdiffusionCLT.Section3.Setup.dirichletRhsField omega m (m - h)
        ((sigmaBarInfinite nu (m - h) P)⁻¹ • e) := by
  funext x
  simp [hshellFlux, SuperdiffusionCLT.Section3.Setup.dirichletRhsField, matVecMul_smul]

/-- **Satisfiability witness.** For every sample the Dirichlet and Neumann responses of the flux
`hshellFlux nu P m h omega e` on `cu_K` exist, and the Dirichlet responses have weak Hessians. -/
theorem exists_response_data [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h Kc : ℕ) (e : Vec d) :
    ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
          H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
      (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
        (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) ∧
      (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
        (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) ∧
      Nonempty (∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
        (wD omega).toH1Function) := by
  have hL2 : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (hshellFlux nu P m h omega e) := fun omega => by
    rw [responseData_hshellFlux_eq_dirichletRhsField]
    exact SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous _
      (SuperdiffusionCLT.Section3.Setup.continuous_dirichletRhsField _ _ _ _)
  choose wD hwD using fun omega =>
    SuperdiffusionCLT.Section3.ResponseFields.exists_isCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hL2 omega)
  choose wN hwN using fun omega =>
    SuperdiffusionCLT.Section3.ResponseFields.exists_isCubeNeumannResponse
      (originCube d (Kc : ℤ)) (hL2 omega)
  refine ⟨wD, wN, hwD, hwN, ⟨fun omega => Classical.choice ?_⟩⟩
  exact SuperdiffusionCLT.Section3.ResponseFields.exists_hasWeakHessianOn_dirichletResponse
    hd omega (Nat.sub_le m h) ((sigmaBarInfinite nu (m - h) P)⁻¹ • e) (wD omega)
    (by
      have hw := hwD omega
      rw [responseData_hshellFlux_eq_dirichletRhsField] at hw
      exact hw)

end SuperdiffusionCLT.Section5
