/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.CubeScalarData
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.CubeTranslationFiniteP
public import Homogenization.Sobolev.Foundations.CubeDirichletH2.PoissonTranslation

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

/-!
# Cube scalar data on every triadic cube, and the vector form

`exists_cubeScalarData_gradLp_sobolev_triadic` transports `exists_cubeScalarData_gradLp_sobolev`
from the centred cube of the same scale to an arbitrary triadic cube, with the same constant.
`exists_cubeScalarData_gradVecLp_sobolev_triadic` is the vector form for the sup-norm gradient,
with constant `d` times the coordinatewise one.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem grad_eq_pushforward_untranslate (Q : TriadicCube d) (u : H10Function (openCubeSet Q))
    (i : Fin d) :
    (fun x => u.toH1Function.grad x i) =
      CubeCalderonZygmund.pushforwardFromOrigin Q
        (fun x => (CubeDirichletWeakPoissonProblem.untranslateToOriginFunction Q u).toH1Function.grad
          x i) := by
  funext x
  simp [CubeCalderonZygmund.pushforwardFromOrigin]

/-- **Scalar data on every triadic cube**, with the constant of the origin cubes. -/
theorem exists_cubeScalarData_gradLp_sobolev_triadic (hd : 2 ≤ d) (r q : FiniteLpExponent)
    (hr : r.exponent.toReal < d)
    (hq : (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (Q : TriadicCube d) (s : Vec d → ℝ),
      MemLp s 2 (normalizedCubeMeasure Q) →
      MemLp s r.exponent (normalizedCubeMeasure Q) →
      ∀ u : H10Function (openCubeSet Q),
        CubeDirichletWeakPoissonProblem Q u s →
        ∀ i : Fin d,
          MemLp (fun x => u.toH1Function.grad x i) q.exponent (normalizedCubeMeasure Q) ∧
            Section2.Norms.cubeLpENorm Q q.exponent (fun x => u.toH1Function.grad x i) ≤
              C * ENNReal.ofReal (cubeScaleFactor Q) *
                Section2.Norms.cubeLpENorm Q r.exponent s := by
  obtain ⟨C, hC, hCb⟩ := exists_cubeScalarData_gradLp_sobolev hd r q hr hq
  refine ⟨C, hC, ?_⟩
  intro Q s hs2 hsr u hu i
  have hs2' : MemLp (CubeCalderonZygmund.pullbackToOrigin Q s) 2
      (normalizedCubeMeasure (originCube d Q.scale)) :=
    CubeCalderonZygmund.memLp_pullbackToOrigin Q hs2
  have hsr' : MemLp (CubeCalderonZygmund.pullbackToOrigin Q s) r.exponent
      (normalizedCubeMeasure (originCube d Q.scale)) :=
    CubeCalderonZygmund.memLp_pullbackToOrigin Q hsr
  have hu' := CubeDirichletWeakPoissonProblem.untranslateToOrigin hu
  obtain ⟨hm, hb⟩ := hCb Q.scale (CubeCalderonZygmund.pullbackToOrigin Q s) hs2' hsr'
    (CubeDirichletWeakPoissonProblem.untranslateToOriginFunction Q u) hu' i
  rw [grad_eq_pushforward_untranslate Q u i]
  refine ⟨CubeCalderonZygmund.memLp_pushforwardFromOrigin Q hm, ?_⟩
  unfold Section2.Norms.cubeLpENorm at hb ⊢
  rw [CubeCalderonZygmund.eLpNorm_pushforwardFromOrigin_eq Q _ hm.aestronglyMeasurable]
  rw [CubeCalderonZygmund.eLpNorm_pullbackToOrigin_eq Q _ hsr.aestronglyMeasurable] at hb
  have e : (originCube d Q.scale).scale = Q.scale := rfl
  simpa [cubeScaleFactor, e] using hb

/-- **Vector form** (sup-norm gradient): `‖∇u‖_{L̲^{r^*}} ≤ d C 3^m ‖s‖_{L̲^r}`. -/
theorem exists_cubeScalarData_gradVecLp_sobolev_triadic (hd : 2 ≤ d) (r q : FiniteLpExponent)
    (hr : r.exponent.toReal < d)
    (hq : (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (Q : TriadicCube d) (s : Vec d → ℝ),
      MemLp s 2 (normalizedCubeMeasure Q) →
      MemLp s r.exponent (normalizedCubeMeasure Q) →
      ∀ u : H10Function (openCubeSet Q),
        CubeDirichletWeakPoissonProblem Q u s →
        MemLp u.toH1Function.grad q.exponent (normalizedCubeMeasure Q) ∧
          Section2.Norms.cubeLpENorm Q q.exponent u.toH1Function.grad ≤
            C * ENNReal.ofReal (cubeScaleFactor Q) *
              Section2.Norms.cubeLpENorm Q r.exponent s := by
  obtain ⟨C, hC, hCb⟩ := exists_cubeScalarData_gradLp_sobolev_triadic hd r q hr hq
  refine ⟨(d : ℝ≥0∞) * C, ENNReal.mul_lt_top (ENNReal.natCast_lt_top d) hC, ?_⟩
  intro Q s hs2 hsr u hu
  have hcoord := fun i => hCb Q s hs2 hsr u hu i
  have hmem : MemLp u.toH1Function.grad q.exponent (normalizedCubeMeasure Q) :=
    (memLp_pi_iff).2 fun i => (hcoord i).1
  refine ⟨hmem, ?_⟩
  set g := u.toH1Function.grad with hg
  have hmeas : ∀ i, AEStronglyMeasurable (fun x => g x i) (normalizedCubeMeasure Q) :=
    fun i => (hcoord i).1.aestronglyMeasurable
  have hpt : ∀ x, ‖g x‖ ≤ ‖(∑ i : Fin d, fun x => ‖g x i‖) x‖ := by
    intro x
    have h0 : 0 ≤ ∑ i : Fin d, ‖g x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [Finset.sum_apply, Real.norm_of_nonneg h0]
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    exact Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hq1 : 1 ≤ q.exponent := q.one_lt.le
  have h1 : eLpNorm g q.exponent (normalizedCubeMeasure Q) ≤
      eLpNorm (∑ i : Fin d, (fun x => ‖g x i‖)) q.exponent (normalizedCubeMeasure Q) :=
    eLpNorm_mono hmem.aestronglyMeasurable hpt
  have h2 := eLpNorm_sum_le (μ := normalizedCubeMeasure Q) (p := q.exponent)
    (s := Finset.univ) (f := fun i => fun x => ‖g x i‖) hq1
  have h3 : ∀ i : Fin d, eLpNorm (fun x => ‖g x i‖) q.exponent (normalizedCubeMeasure Q) =
      eLpNorm (fun x => g x i) q.exponent (normalizedCubeMeasure Q) :=
    fun i => eLpNorm_norm _ (hmeas i)
  unfold Section2.Norms.cubeLpENorm at hcoord ⊢
  calc eLpNorm g q.exponent (normalizedCubeMeasure Q)
      ≤ ∑ i : Fin d, eLpNorm (fun x => g x i) q.exponent (normalizedCubeMeasure Q) := by
        refine h1.trans (h2.trans_eq ?_)
        exact Finset.sum_congr rfl fun i _ => h3 i
    _ ≤ ∑ _i : Fin d, (C * ENNReal.ofReal (cubeScaleFactor Q) *
          eLpNorm s r.exponent (normalizedCubeMeasure Q)) :=
        Finset.sum_le_sum fun i _ => (hcoord i).2
    _ = _ := by simp; ring

/-- Satisfiability: `d = 3`, `r = 3/2`, `q = 3`, `s = 0`, `u = 0` on a non-origin cube. -/
example : ∃ (r q : FiniteLpExponent), r.exponent.toReal < (3 : ℕ) ∧
    (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - ((3 : ℕ) : ℝ)⁻¹ ∧
    ∃ Q : TriadicCube 3, triadicCubeShift Q ≠ 0 ∧
      ∃ u : H10Function (openCubeSet Q),
        CubeDirichletWeakPoissonProblem Q u (fun _ => 0) ∧
        MemLp (fun _ : Vec 3 => (0 : ℝ)) 2 (normalizedCubeMeasure Q) ∧
        MemLp (fun _ : Vec 3 => (0 : ℝ)) r.exponent (normalizedCubeMeasure Q) := by
  refine ⟨mkExp (3 / 2) (by norm_num), mkExp 3 (by norm_num), ?_, ?_,
    ⟨⟨0, fun _ => 1⟩, ?_, 0, ?_, by simp, by simp⟩⟩
  · rw [mkExp_toReal]; norm_num
  · rw [mkExp_toReal, mkExp_toReal]; norm_num
  · intro h
    have := congrFun h 0
    simp [triadicCubeShift, cubeScaleFactor] at this
  · intro φ
    have h0 : ∀ x, (H10Function.toH1Function
        (0 : H10Function (openCubeSet (⟨0, fun _ => 1⟩ : TriadicCube 3)))).grad x = 0 :=
      fun _ => rfl
    simp [vecDot, h0]

end SuperdiffusionCLT.Section7
