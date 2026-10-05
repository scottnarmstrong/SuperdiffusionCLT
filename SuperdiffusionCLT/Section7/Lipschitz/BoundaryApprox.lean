/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Datum
public import SuperdiffusionCLT.Section7.Lipschitz.AuxHarmonic
public import SuperdiffusionCLT.Section7.Lipschitz.InnerBall
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarmC
public import SuperdiffusionCLT.Section7.Lipschitz.Calc

/-!
# The harmonic approximation near the boundary: calculus

Bounds for the normalized norms, volumes of the cubes `z + □_m`, the weak form of the difference of
two solutions, the Dirichlet solution of the Laplace problem with a right-hand side that may fail
to be measurable, and the localized zero trace of the pieces of the approximation.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Monotonicity of the real normalized `L²` norm in the function. -/
theorem lip_bdry_approx_lipL2_mono {S : Set (Vec d)} (hS0 : volume S ≠ 0) (hS : volume S ≠ ⊤)
    {f h : Vec d → ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    (hh : MemLp h 2 (volume.restrict S)) (hle : ∀ᵐ x ∂volume.restrict S, |f x| ≤ h x) :
    lipL2 S f ≤ lipL2 S h := by
  unfold lipL2 lpBar
  refine ENNReal.toReal_mono (lip_int_harm_of_l2_lpBar_lt_top hS0 hS hh) ?_
  refine eLpNorm_mono_ae_real (hf.smul_measure _) ?_
  filter_upwards [Measure.smul_absolutelyContinuous.ae_le hle] with x hx
  rw [Real.norm_eq_abs]
  exact hx

theorem lip_bdry_approx_shiftCube_eq_ball (z : Vec d) (m : ℕ) :
    shiftCube z (m : ℤ) = Metric.ball z ((3 : ℝ) ^ m / 2) := by
  have := g1q_shiftCube_eq_ball z (m : ℤ)
  rw [zpow_natCast] at this
  exact this

theorem lip_bdry_approx_isOpen_cube (z : Vec d) (m : ℕ) : IsOpen (shiftCube z (m : ℤ)) :=
  rc_isOpen_shiftCube z _

theorem lip_bdry_approx_cube_mono (z : Vec d) {m m' : ℕ} (h : m ≤ m') :
    shiftCube z (m : ℤ) ⊆ shiftCube z (m' : ℤ) := by
  rw [lip_bdry_approx_shiftCube_eq_ball, lip_bdry_approx_shiftCube_eq_ball]
  exact Metric.ball_subset_ball (by
    have : (3 : ℝ) ^ m ≤ 3 ^ m' := pow_le_pow_right₀ (by norm_num) h
    linarith only [this])

theorem lip_bdry_approx_vol_cube (z : Vec d) (m : ℕ) :
    volume (shiftCube z (m : ℤ)) = ENNReal.ofReal (((3 : ℝ) ^ m) ^ d) := by
  rw [lip_bdry_approx_shiftCube_eq_ball, Real.volume_pi_ball z (by positivity),
    Fintype.card_fin]
  congr 1
  congr 1
  ring

theorem lip_bdry_approx_vol_cube_ne_top (z : Vec d) (m : ℕ) : volume (shiftCube z (m : ℤ)) ≠ ⊤ := by
  rw [lip_bdry_approx_vol_cube]
  exact ENNReal.ofReal_ne_top

theorem lip_bdry_approx_isBoundedDomain {S : Set (Vec d)} {z : Vec d} {m : ℕ}
    (h : S ⊆ shiftCube z (m : ℤ)) : IsBoundedDomain S := by
  refine ⟨‖z‖ + (3 : ℝ) ^ m / 2 + 1, by positivity, fun x hx i => ?_⟩
  have h1 := h hx
  rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball, dist_eq_norm] at h1
  have h2 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := norm_le_norm_sub_add x z
  have h3 : |x i| ≤ ‖x‖ := by
    have := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at this
  linarith only [h1, h2, h3]

theorem lip_bdry_approx_vol_ne_zero_ne_top {S : Set (Vec d)} {V : Set (Vec d)} {z : Vec d} {m : ℕ}
    (hV0 : volume V ≠ 0) (hVS : V ⊆ S) (hS : S ⊆ shiftCube z (m : ℤ)) :
    volume S ≠ 0 ∧ volume S ≠ ⊤ :=
  ⟨fun h => hV0 (le_antisymm (h ▸ measure_mono hVS) bot_le),
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z m) (measure_mono hS)⟩

/-- The solution minus a solution of the homogeneous problem solves the same problem. -/
theorem lip_bdry_approx_weak_sub {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ} {u v : H1Function U}
    (hu : IsWeakSolutionOn a U u f (fun _ => 0)) (hv : IsWeakSolutionOn a U v 0 0) :
    IsWeakSolutionOn a U (u - v) f (fun _ => 0) := by
  intro φ
  have hint : ∀ w : H1Function U, MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.grad x)) (φ.toH1Function.grad x)) U :=
    fun w => integrableOn_vecDot_of_memVectorL2
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2)
      φ.toH1Function.grad_memVectorL2
  have h1 := hu φ
  have h2 := hv φ
  have hsplit : (fun x => vecDot (matVecMul (a x) ((u - v).grad x)) (φ.toH1Function.grad x)) =
      fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
        vecDot (matVecMul (a x) (v.grad x)) (φ.toH1Function.grad x) := by
    funext x
    simp only [H1Function.sub_grad, Pi.sub_apply, vecDot, matVecMul, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [hsplit, integral_sub (hint u) (hint v), h1, h2]
  simp [vecDot]

/-- The Dirichlet solution of the Laplace problem on `V` with the datum `u0` and a bounded
measurable right-hand side. -/
theorem lip_bdry_approx_ub_exists [NeZero d] {V : Set (Vec d)} (hVo : IsOpen V)
    (hbd : IsBoundedDomain V) (hVt : volume V ≠ ⊤) {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} {F : ℝ}
    (hF : ∀ᵐ x ∂volume.restrict V, |f x| ≤ F) (hm : AEStronglyMeasurable f (volume.restrict V))
    (u0 : H1Function V) :
    ∃ ub : H1Function V, IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0) ∧
      MemH10 V (fun x => ub.toFun x - u0.toFun x) := by
  have hell := rc_isEllipticFieldOn_smul_one hs hVo.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVt.lt_top⟩
  have hf2 : MemLp f 2 (volume.restrict V) :=
    MemLp.of_bound hm F (hF.mono fun x hx => by rwa [Real.norm_eq_abs])
  exact w0_dirichlet_exists hVo hbd hell hf2 u0

/-- Replacement of the right-hand side by one that is measurable on a subset `S`: either `f`, or
`0` when `f` is not almost everywhere measurable on `S`; in both cases `u` solves the problem on
`S` with the new right-hand side, and the two right-hand sides agree against `H¹₀(S)`. -/
theorem lip_bdry_approx_repl {Ω S : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω) (hEll : IsEllipticFieldOn lam Lam Ω a)
    {u : H1Function Ω} {f : Vec d → ℝ} {F : ℝ}
    (hu : IsWeakSolutionOn a Ω u f (fun _ => 0)) (hF0 : 0 ≤ F)
    (hF : ∀ᵐ x ∂volume.restrict Ω, |f x| ≤ F) :
    ∃ f' : Vec d → ℝ, AEStronglyMeasurable f' (volume.restrict S) ∧
      (∀ᵐ x ∂volume.restrict S, |f' x| ≤ F) ∧
      IsWeakSolutionOn a S (u.restrict hS hSΩ) f' (fun _ => 0) ∧
      ∀ φ : H10Function S, ∫ x in S, f x * φ.toH1Function.toFun x =
        ∫ x in S, f' x * φ.toH1Function.toFun x := by
  by_cases hm : AEStronglyMeasurable f (volume.restrict S)
  · exact ⟨f, hm, ae_restrict_of_ae_restrict_of_subset hSΩ hF,
      IsWeakSolutionOn.restrict' hu hS hSΩ, fun _ => rfl⟩
  · have hmΩ : ¬ AEStronglyMeasurable f (volume.restrict Ω) := fun h =>
      hm (h.mono_measure (Measure.restrict_mono hSΩ le_rfl))
    have hu0 := lip_int_harm_of_l2_weak_zero_of_not_meas hΩ hEll hu hmΩ
    refine ⟨fun _ => 0, aestronglyMeasurable_const, ?_, IsWeakSolutionOn.restrict' hu0 hS hSΩ, ?_⟩
    · refine Filter.Eventually.of_forall fun x => ?_
      simpa using hF0
    · intro φ
      have h1 := IsWeakSolutionOn.restrict' hu hS hSΩ φ
      have h2 := IsWeakSolutionOn.restrict' hu0 hS hSΩ φ
      rw [h2] at h1
      simp at h1 ⊢
      exact h1

theorem lip_bdry_approx_h10_mul {Ω : Set (Vec d)} {h : Vec d → ℝ} (hh : MemH10 Ω h)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    MemH10 Ω (fun y => η y * h y) := by
  obtain ⟨v, hv⟩ := hh
  refine ⟨v.mulContDiffHasCompactSupport hη hηc, ?_⟩
  rw [H10Function.mulContDiffHasCompactSupport_toFun]
  funext x
  rw [← hv]

theorem lip_bdry_approx_loc_of_h10 {Ω B : Set (Vec d)} {h : Vec d → ℝ} (hh : MemH10 Ω h) :
    LocalizedZeroTraceFunctionOn Ω B h :=
  fun _ hη hηc _ => lip_bdry_approx_h10_mul hh hη hηc

end SuperdiffusionCLT.Section7
