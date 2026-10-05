/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.GradientL8
public import SuperdiffusionCLT.Section5.Response.DirichletHessian
public import SuperdiffusionCLT.Section5.Response.EnergyComparisonB
public import SuperdiffusionCLT.Section5.Response.EnergyWeakB
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# `lem.response` assembled

The gradient `L⁸` clause, the Dirichlet Hessian `L⁸` clause and the two energy clauses, with one
constant `C` that is the maximum of the constants of the pieces.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

/-- `lem.response` as an ordinary lemma: gradient `L⁸`, Dirichlet Hessian `L⁸`, and the
energy clause with the E2-consequence exponent `(1 + (Kc - m))^{2/5}`. No Neumann Hessian. -/
theorem response_estimates (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ (cStar K : ℝ),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          ∀ e : Vec d, vecNormSq e ≤ 1 →
          ∀ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H10Function (openCubeSet (originCube d (Kc : ℤ))))
            (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) →
          ((∫⁻ omega, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (Kc : ℤ)) 8 (wD omega).toH1Function.grad) ^ (8 : ℕ) +
                (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (Kc : ℤ)) 8 (wN omega).toH1Function.grad) ^ (8 : ℕ)
                ∂P.toMeasure) ^ ((1 : ℝ) / 8) ≤
            ENNReal.ofReal (C * (sigmaBarInfinite nu (m - h) P)⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2))) ∧
          (∀ HD : ∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
                (wD omega).toH1Function,
            (∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (Kc : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (8 : ℕ)
                ∂P.toMeasure) ^ ((1 : ℝ) / 8) ≤
              ENNReal.ofReal (C * (sigmaBarInfinite nu (m - h) P)⁻¹ *
                (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) ∧
          (vecNormSq e = 1 →
            |(∫⁻ omega, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                    (originCube d (Kc : ℤ)) 2 (wD omega).toH1Function.grad) ^ (2 : ℕ)
                    ∂P.toMeasure).toReal -
                cStar * Real.log 3 * (h : ℝ) * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))| ≤
              (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
                    (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) + K) *
                (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) ∧
            |(∫⁻ omega, (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                    (originCube d (Kc : ℤ)) 2 (wN omega).toH1Function.grad) ^ (2 : ℕ)
                    ∂P.toMeasure).toReal -
                cStar * Real.log 3 * (h : ℝ) * (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))| ≤
              (C * (h : ℝ) ^ ((4 : ℝ) / 5) * (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) *
                    (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) + K) *
                (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ))) := by
  obtain ⟨C1, h1, H1⟩ := response_gradient_L8 d hd
  obtain ⟨C2, h2, H2⟩ := response_hessian_L8 d hd
  obtain ⟨C3, h3, H3⟩ := hshellFlux_gap_second_moment (d := d) hd
  have hC1 : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
  have hC2 : C2 ≤ max C1 (max C2 C3) := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : C3 ≤ max C1 (max C2 C3) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max C1 (max C2 C3), h1.trans hC1, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 cStar K hJ5 m h Kc hh h400 h100 e he wD wN hwD hwN
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  have hσi : 0 ≤ (sigmaBarInfinite nu (m - h) P)⁻¹ := inv_nonneg.2 hσ.le
  refine ⟨?_, ?_, ?_⟩
  · refine (H1 nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he wD wN hwD hwN).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hh0 : 0 ≤ (h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    gcongr
  · intro HD
    refine (H2 nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he wD wN hwD hwN HD).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hh0 : 0 ≤ (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    gcongr
  · intro he1
    have hmh : h ≤ m := by omega
    have hmK : m ≤ Kc := by omega
    have hgap := H3 nu hnu P hPre hJ1 hJ2 hJ3 hJ4 m h Kc hh hmh hmK e he1 wD wN hwD hwN
    have hC0 : 0 ≤ C3 := by linarith only [h3]
    exact abs_energy_sub_hshell_le hd hPre hJ2 hJ3 hJ5 nu hh hmh e he1
      (le_trans hC0 hC3) wD wN hwD hwN
      (hgap.trans (ENNReal.ofReal_le_ofReal (by
        have a1 : 0 ≤ (h : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have a2 : 0 ≤ (1 + ((Kc - m : ℕ) : ℝ)) ^ ((2 : ℝ) / 5) :=
          Real.rpow_nonneg (by positivity) _
        have a3 : 0 ≤ (3 : ℝ) ^ (-((2 : ℝ) / 5 * ((Kc - m : ℕ) : ℝ))) :=
          Real.rpow_nonneg (by norm_num) _
        have a4 : 0 ≤ (sigmaBarInfinite nu (m - h) P) ^ (-(2 : ℝ)) := rpow_neg_two_nonneg _
        gcongr)))

variable {d : ℕ}

/-- **Satisfiability witness.** The non-law hypotheses of `response_estimates` are met together at
`(m, h, Kc) = (400, 1, 40000)`, with a unit direction and Dirichlet and Neumann responses. -/
example [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) :
    ∃ m h Kc : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 100 * m ≤ Kc ∧
      ∃ e : Vec d, vecNormSq e = 1 ∧
        ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H10Function (openCubeSet (originCube d (Kc : ℤ))))
          (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
          (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) ∧
          (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) := by
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  refine ⟨400, 1, 40000, by norm_num, by norm_num, by norm_num, fun j => if j = i then 1 else 0, ?_, ?_⟩
  · simp [vecNormSq, vecDot]
  · obtain ⟨wD, wN, hD, hN⟩ := exists_responses_hshellFlux nu P 400 1 40000 (fun j => if j = i then 1 else 0)
    exact ⟨wD, wN, hD, hN⟩

end SuperdiffusionCLT.Section5
