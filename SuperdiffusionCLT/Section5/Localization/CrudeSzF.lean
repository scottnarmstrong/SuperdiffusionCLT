/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.CrudeSzE

/-!
# Fields of the crude bound: membership in `L²` and the shell flux in `L̲⁸`

The responses `∇w_D`, `∇w_N` and the flux `hshellFlux` lie in `L²(cu_K)`; the flux has a
measurable majorant for its `L̲⁸(cu_K)` norm to the eighth power whose expectation is at most
`(C shom_{m-h}^{-1} h^{1/2})⁸`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

theorem continuous_hshellFlux [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    {m h : ℕ} (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e : Vec d) :
    Continuous (hshellFlux nu P m h omega e) := by
  have hdelta : ∀ x, SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x =
      SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x :=
    fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
      omega (Nat.sub_le m h) x
  have hcont : Continuous (fun x : Vec d =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) := by
    have hfun : (fun x : Vec d =>
        SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) =
        fun x => ∑ k ∈ Finset.Ioc (m - h) m, (omega k) x := by
      funext x
      rw [SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply]
      rfl
    rw [hfun]
    exact continuous_finsetSum _ fun k _ => (omega k).1.1.continuous
  have hform : hshellFlux nu P m h omega e = fun x =>
      (sigmaBarInfinite nu (m - h) P)⁻¹ •
        matVecMul (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) e := by
    funext x
    rw [hshellFlux, hdelta]
  have hm : Continuous (fun x : Vec d => matVecMul
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) e) := by
    refine continuous_pi fun i => ?_
    simp only [matVecMul]
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp ((continuous_apply i).comp hcont)).mul continuous_const
  rw [hform]
  exact (continuous_const (y := (sigmaBarInfinite nu (m - h) P)⁻¹)).smul hm

theorem memVectorL2_hshellFlux [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    {m h : ℕ} (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e : Vec d)
    (Kc : ℕ) :
    MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h omega e) :=
  SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous (Kc : ℤ)
    (continuous_hshellFlux nu P omega e)

theorem memVectorL2_grad {U : Set (Vec d)} (u : H1Function U) : MemVectorL2 U u.grad :=
  MeasureTheory.MemLp.of_eval u.gradMemL2

/-- The `L̲⁸(cu_K)` norm of the shell flux, to the eighth power, has a measurable majorant with
expectation at most `(C shom_{m-h}^{-1} h^{1/2})⁸`. -/
theorem shell_flux_L8 (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          ∀ e : Vec d, vecNormSq e ≤ 1 →
          ∃ Wm : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ≥0∞, Measurable Wm ∧
            (∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 8 (hshellFlux nu P m h omega e) ^ (8 : ℕ) ≤
              Wm omega) ∧
            ∫⁻ omega, Wm omega ∂P.toMeasure ≤
              ENNReal.ofReal (C * (sigmaBarInfinite nu (m - h) P)⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) ^
                (8 : ℕ) := by
  obtain ⟨C, hC1, hC⟩ := shell_increment_L8 d
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e he
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  obtain ⟨W0, hW0m, hW0le, hW0int⟩ := hC nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100
  have hinv : ‖(sigmaBarInfinite nu (m - h) P)⁻¹‖ₑ =
      ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ :=
    Real.enorm_eq_ofReal (inv_nonneg.2 hσ.le)
  refine ⟨fun omega => ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ ^ (8 : ℕ) * W0 omega,
    hW0m.const_mul _, fun omega => ?_, ?_⟩
  · have h1 := vecCubeLpENorm_hshellFlux_le nu P m h omega he (originCube d (Kc : ℤ)) 8
    rw [hinv] at h1
    calc _ ≤ (ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
            (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x)) ^
          (8 : ℕ) := pow_le_pow_left' h1 8
      _ = _ := by rw [mul_pow]
      _ ≤ _ := mul_le_mul' le_rfl (hW0le omega)
  · rw [lintegral_const_mul _ hW0m]
    calc _ ≤ ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ ^ (8 : ℕ) *
          ENNReal.ofReal (C * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ (8 : ℕ) := mul_le_mul' le_rfl hW0int
      _ = _ := by
        rw [← mul_pow, ← ENNReal.ofReal_mul (inv_nonneg.2 hσ.le)]
        congr 2
        ring

end SuperdiffusionCLT.Section5
