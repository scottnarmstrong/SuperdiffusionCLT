/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.LocalizationA
public import SuperdiffusionCLT.Section5.Response.EnergyWeakB
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB

/-!
# The energy gap for directions of length at most one

`hshellFlux_gap_second_moment` is stated for unit directions.  The responses are linear in the flux
(`IsCubeNeumannResponse`, `IsCubeDirichletResponse` are preserved by scalar multiplication) and the
gradient is unique as an `L²` class, so the gap of the direction `t • u` is `t` times the gap of
`u`, with `t ≤ 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

variable {d : ℕ}

theorem loc_isCubeNeumannResponse_smul (t : ℝ) {Q : TriadicCube d} {F : Vec d → Vec d}
    {w : H1MeanZeroFunction (openCubeSet Q)} (h : IsCubeNeumannResponse Q F w) :
    IsCubeNeumannResponse Q (fun x => t • F x) (t • w) := by
  intro φ
  have hg : ∀ x, (t • w).toH1Function.grad x = t • w.toH1Function.grad x := fun x => rfl
  simp only [hg, vecDot_smul_left]
  rw [integral_const_mul, integral_const_mul, h φ]
  ring

theorem loc_isCubeDirichletResponse_smul (t : ℝ) {Q : TriadicCube d} {F : Vec d → Vec d}
    {w : H10Function (openCubeSet Q)} (h : IsCubeDirichletResponse Q F w) :
    IsCubeDirichletResponse Q (fun x => t • F x) (t • w) := by
  intro φ
  have hg : ∀ x, (t • w).toH1Function.grad x = t • w.toH1Function.grad x := fun x => rfl
  simp only [hg, vecDot_smul_left]
  rw [integral_const_mul, integral_const_mul, h φ]
  ring

theorem loc_toHilbert_sub' {U : Set (Vec d)} {f g : Vec d → Vec d} (hf : MemVectorL2 U f)
    (hg : MemVectorL2 U g) (hfg : MemVectorL2 U (fun x => f x - g x)) :
    toHilbertVectorL2OfVecField hfg = toHilbertVectorL2OfVecField hf - toHilbertVectorL2OfVecField hg :=
  toHilbertVectorL2OfVecField_sub hf hg

/-- The norm of a difference of two weak gradients depends only on their `L²` classes. -/
theorem loc_vecCubeLpENorm_sub_grad_congr {Q : TriadicCube d} {u v u' v' : H1Function (openCubeSet Q)}
    (h1 : u.gradToHilbertVectorL2 = u'.gradToHilbertVectorL2)
    (h2 : v.gradToHilbertVectorL2 = v'.gradToHilbertVectorL2) :
    vecCubeLpENorm Q 2 (fun x => u.grad x - v.grad x) =
      vecCubeLpENorm Q 2 (fun x => u'.grad x - v'.grad x) := by
  have hm1 : MemVectorL2 (openCubeSet Q) (fun x => u.grad x - v.grad x) :=
    u.grad_memVectorL2.sub v.grad_memVectorL2
  have hm2 : MemVectorL2 (openCubeSet Q) (fun x => u'.grad x - v'.grad x) :=
    u'.grad_memVectorL2.sub v'.grad_memVectorL2
  rw [vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField hm1,
    vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField hm2,
    loc_toHilbert_sub' u.grad_memVectorL2 v.grad_memVectorL2 hm1,
    loc_toHilbert_sub' u'.grad_memVectorL2 v'.grad_memVectorL2 hm2]
  have e1 : toHilbertVectorL2OfVecField u.grad_memVectorL2 = u.gradToHilbertVectorL2 := rfl
  have e2 : toHilbertVectorL2OfVecField v.grad_memVectorL2 = v.gradToHilbertVectorL2 := rfl
  have e3 : toHilbertVectorL2OfVecField u'.grad_memVectorL2 = u'.gradToHilbertVectorL2 := rfl
  have e4 : toHilbertVectorL2OfVecField v'.grad_memVectorL2 = v'.gradToHilbertVectorL2 := rfl
  rw [e1, e2, e3, e4, h1, h2]

theorem loc_exists_unit_smul [NeZero d] (e : Vec d) (he : vecNormSq e ≤ 1) :
    ∃ (t : ℝ) (u : Vec d), 0 ≤ t ∧ t ≤ 1 ∧ vecNormSq u = 1 ∧ e = t • u := by
  by_cases h0 : vecNormSq e = 0
  · refine ⟨0, Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ 1, le_rfl, zero_le_one, ?_, ?_⟩
    · simp [vecNormSq, vecDot, Pi.single_apply]
    · rw [vecNormSq_eq_zero h0, zero_smul]
  · have hpos : 0 < vecNormSq e := lt_of_le_of_ne (vecNormSq_nonneg e) (Ne.symm h0)
    set t : ℝ := Real.sqrt (vecNormSq e) with ht
    have htpos : 0 < t := Real.sqrt_pos.2 hpos
    refine ⟨t, t⁻¹ • e, htpos.le, ?_, ?_, ?_⟩
    · rw [ht]; exact Real.sqrt_le_one.2 he
    · rw [vecNormSq_smul, inv_pow, ht, Real.sq_sqrt hpos.le]
      field_simp
    · rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]

theorem loc_hshellFlux_smul [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h : ℕ) (omega : ShellSeq d) (t : ℝ) (u : Vec d) :
    hshellFlux nu P m h omega (t • u) = fun x => t • hshellFlux nu P m h omega u x := by
  funext x
  simp only [hshellFlux, matVecMul_smul, smul_comm t]

/-- **The energy gap, for a direction of length at most one.** The unit-length statement
`hshellFlux_gap_second_moment`, extended by the linearity of the responses in the flux. -/
theorem loc_gap_scaled [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P → ∀ (m h Kc : ℕ), 1 ≤ h → h ≤ m → m ≤ Kc →
      ∀ e : Vec d, vecNormSq e ≤ 1 →
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
  obtain ⟨C, hC1, H⟩ := hshellFlux_gap_second_moment (d := d) hd
  refine ⟨C, hC1, ?_⟩
  intro nu hnu P hPre hJ1 hJ2 hJ3 hJ4 m h Kc hh hhm hmK e he wD wN hwD hwN
  obtain ⟨t, u, ht0, ht1, hu, rfl⟩ := loc_exists_unit_smul e he
  have hMS : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ)))
      (hshellFlux nu P m h omega u) := fun omega => memVectorL2_hshellFlux nu P omega u Kc
  choose wNu hwNu using fun omega => exists_isCubeNeumannResponse (originCube d (Kc : ℤ)) (hMS omega)
  choose wDu hwDu using fun omega => exists_isCubeDirichletResponse (originCube d (Kc : ℤ)) (hMS omega)
  refine le_trans (lintegral_mono fun omega => ?_) (H nu hnu P hPre hJ1 hJ2 hJ3 hJ4 m h Kc hh hhm hmK u hu
    wDu wNu hwDu hwNu)
  refine pow_le_pow_left' ?_ 2
  have hN' : IsCubeNeumannResponse (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega (t • u))
      (t • wNu omega) := by
    rw [loc_hshellFlux_smul]; exact loc_isCubeNeumannResponse_smul t (hwNu omega)
  have hD' : IsCubeDirichletResponse (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega (t • u))
      (t • wDu omega) := by
    rw [loc_hshellFlux_smul]; exact loc_isCubeDirichletResponse_smul t (hwDu omega)
  have c1 := gradToHilbertVectorL2_eq_of_gradToVectorL2_eq
    (gradToVectorL2_eq_of_isCubeNeumannResponse (hwN omega) hN')
  have c2 := gradToHilbertVectorL2_eq_of_gradToVectorL2_eq
    (gradToVectorL2_eq_of_isCubeDirichletResponse (hwD omega) hD')
  rw [loc_vecCubeLpENorm_sub_grad_congr c1 c2]
  have hfun : (fun x => (t • wNu omega).toH1Function.grad x - (t • wDu omega).toH1Function.grad x) =
      fun x => t • ((wNu omega).toH1Function.grad x - (wDu omega).toH1Function.grad x) := by
    funext x
    exact (smul_sub t _ _).symm
  rw [hfun, vecCubeLpENorm_const_smul]
  calc _ ≤ 1 * vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => (wNu omega).toH1Function.grad x - (wDu omega).toH1Function.grad x) := by
        refine mul_le_mul' ?_ le_rfl
        rw [Real.enorm_eq_ofReal ht0]
        exact ENNReal.ofReal_le_one.2 ht1
    _ = _ := one_mul _

end SuperdiffusionCLT.Section5
