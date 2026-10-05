/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdry
public import SuperdiffusionCLT.Section7.Prereq.RhsLemma
public import SuperdiffusionCLT.Section7.Lipschitz.WitnessBdryB
public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace

/-!
# The energy identity of the boundary Caccioppoli inequality

For a weak solution `u` of `-∇·(A∇u) = f` in a bounded open set `V` with `sym (A) = ν Id` and a
localized zero trace of `u - γ`, testing with `Φ (u - γ)` gives
`ν ∫ Φ |∇u|² = ∫ f Φ (u - γ) + ∫ (A∇u)·(Φ ∇γ - (u - γ) ∇Φ)`
(`ca2_energy_identity`), the boundary analogue of `ca1_energy_identity`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The datum vector field of the energy identity. -/
noncomputable def ca2_G (Φ γ w : Vec d → ℝ) (x : Vec d) : Vec d :=
  Φ x • p12_grad γ x - w x • p12_grad Φ x

theorem ca2_vecDot_test (X U Γ N : Vec d) (Φ w : ℝ) :
    vecDot X (Φ • (U - Γ) + w • N) = Φ * vecDot X U - vecDot X (Φ • Γ - w • N) := by
  unfold vecDot
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have : ∀ i, X i * (Φ * U i) = Φ * (X i * U i) := fun i => by ring
  simp only [this]
  ring

theorem ca2_continuous_grad {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ 1 Φ) : Continuous (p12_grad Φ) := by
  refine continuous_pi fun i => ?_
  exact (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem ca2_hasCompactSupport_grad {Φ : Vec d → ℝ} (hΦc : HasCompactSupport Φ) (i : Fin d) :
    HasCompactSupport (fun x => p12_grad Φ x i) :=
  hΦc.fderiv_apply (𝕜 := ℝ) (basisVec i)

theorem ca2_memLp_G {V : Set (Vec d)} (u : H1Function V) {γ Φ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (i : Fin d) :
    MemLp (fun x => ca2_G Φ γ (fun y => u.toFun y - γ y) x i) 2 (volume.restrict V) := by
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by simp)
  have hDγ : Continuous (fun x => p12_grad γ x i) :=
    (continuous_apply i).comp (ca2_continuous_grad hγ1)
  have hDΦ : Continuous (fun x => p12_grad Φ x i) :=
    (continuous_apply i).comp (ca2_continuous_grad hΦ)
  have hDΦc := ca2_hasCompactSupport_grad hΦc i
  have h1 : MemLp (fun x => Φ x * p12_grad γ x i) 2 (volume.restrict V) :=
    ((hΦ.continuous.mul hDγ).memLp_of_hasCompactSupport hΦc.mul_right).restrict V
  have h2 : MemLp (fun x => γ x * p12_grad Φ x i) 2 (volume.restrict V) :=
    ((hγ.continuous.mul hDΦ).memLp_of_hasCompactSupport hDΦc.mul_left).restrict V
  obtain ⟨B, hB⟩ := hDΦ.bounded_above_of_compact_support hDΦc
  have h3 : MemLp (fun x => u.toFun x * p12_grad Φ x i) 2 (volume.restrict V) := by
    refine MemLp.of_le_mul (c := B) u.memL2 (u.memL2.aestronglyMeasurable.mul hDΦ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa using hB x) (norm_nonneg _)
  have e : (fun x => ca2_G Φ γ (fun y => u.toFun y - γ y) x i) =
      fun x => Φ x * p12_grad γ x i - u.toFun x * p12_grad Φ x i + γ x * p12_grad Φ x i := by
    funext x
    simp only [ca2_G, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact (h1.sub h3).add h2

theorem ca2_integrable_cross {V : Set (Vec d)} {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam V A) (u : H1Function V) {γ Φ : Vec d → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) :
    IntegrableOn (fun x => vecDot (matVecMul (A x) (u.grad x))
      (ca2_G Φ γ (fun y => u.toFun y - γ y) x)) V volume := by
  have hF : MemLp (fun x => matVecMul (A x) (u.grad x)) 2 (volume.restrict V) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have : (fun x => vecDot (matVecMul (A x) (u.grad x)) (ca2_G Φ γ (fun y => u.toFun y - γ y) x)) =
      fun x => ∑ i, matVecMul (A x) (u.grad x) i * ca2_G Φ γ (fun y => u.toFun y - γ y) x i := by
    funext x; rfl
  rw [this]
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  exact ((memLp_pi_iff.1 hF) i).integrable_mul (ca2_memLp_G u hγ hΦ hΦc i)

theorem ca2_integrable_energy {V : Set (Vec d)} (u : H1Function V) {Φ : Vec d → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) :
    IntegrableOn (fun x => Φ x * vecNormSq (u.grad x)) V volume := by
  have h1 : Integrable (fun x => eucNorm (u.grad x) ^ 2) (volume.restrict V) :=
    (memLp_eucNorm_grad u).integrable_sq
  have h2 : (fun x => eucNorm (u.grad x) ^ 2) = fun x => vecNormSq (u.grad x) := by
    funext x
    unfold eucNorm
    exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  rw [h2] at h1
  obtain ⟨B, hB⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  exact Integrable.bdd_mul (c := B) h1 hΦ.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using hB x)

theorem ca2_integrable_rhs {V : Set (Vec d)} (hVb : Bornology.IsBounded V) (hV : IsOpen V)
    (u : H1Function V) {γ Φ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) (hΦ : ContDiff ℝ 1 Φ)
    (hΦc : HasCompactSupport Φ) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict V)) :
    IntegrableOn (fun x => f x * (Φ x * (u.toFun x - γ x))) V volume := by
  have hγL : MemLp γ 2 (volume.restrict V) := lip_witness_bdry_memLp_cont hV hVb hγ.continuous
  have hw : MemLp (fun x => u.toFun x - γ x) 2 (volume.restrict V) := u.memL2.sub hγL
  obtain ⟨B, hB⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hΦw : MemLp (fun x => Φ x * (u.toFun x - γ x)) 2 (volume.restrict V) := by
    refine MemLp.of_le_mul (c := B) hw (hΦ.continuous.aestronglyMeasurable.mul hw.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hB x) (norm_nonneg _)
  exact hf.integrable_mul hΦw

/-- **The energy identity** for the test function `Φ (u - γ)`:
`ν ∫ Φ |∇u|² = ∫ f Φ (u - γ) + ∫ (A∇u)·(Φ ∇γ - (u - γ) ∇Φ)`. -/
theorem ca2_energy_identity {V T : Set (Vec d)} (hV : IsOpen V) (hT : IsOpen T) {lam Lam ν : ℝ} {A : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V A)
    (hsym : ∀ x ∈ V, symmPart (A x) = ν • (1 : Mat d)) (u : H1Function V) {f : Vec d → ℝ}
    (hu : IsWeakSolutionOn A V u f (fun _ => 0))
    {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn V T (fun x => u.toFun x - γ x)) {Φ : Vec d → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦT : tsupport Φ ⊆ T) :
    ν * ∫ x in V, Φ x * vecNormSq (u.grad x) =
      (∫ x in V, f x * (Φ x * (u.toFun x - γ x))) +
        ∫ x in V, vecDot (matVecMul (A x) (u.grad x)) (ca2_G Φ γ (fun y => u.toFun y - γ y) x) := by
  obtain ⟨φ, hφf, hφg⟩ := ca2_test_fn hV hT u hγ hZ hΦ hΦc hΦT
  have h := hu φ
  simp only [vecDot_zero_left, integral_zero, add_zero] at h
  have hVm : MeasurableSet V := hV.measurableSet
  have e1 : (∫ x in V, f x * φ.toH1Function.toFun x) =
      ∫ x in V, f x * (Φ x * (u.toFun x - γ x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hφf x]
  have e2 : (∫ x in V, vecDot (matVecMul (A x) (u.grad x)) (φ.toH1Function.grad x)) =
      ∫ x in V, (ν * (Φ x * vecNormSq (u.grad x)) -
        vecDot (matVecMul (A x) (u.grad x)) (ca2_G Φ γ (fun y => u.toFun y - γ y) x)) := by
    refine integral_congr_ae ?_
    filter_upwards [hφg, ae_restrict_mem hVm] with x hx hxV
    rw [hx, ca2_vecDot_test, r1_quad_symm (hsym x hxV)]
    simp only [ca2_G]
    ring
  rw [e1, e2, integral_sub ((ca2_integrable_energy u hΦ hΦc).const_mul ν)
    (ca2_integrable_cross hEll u hγ hΦ hΦc), integral_const_mul] at h
  linarith only [h]

/-- Witness: the hypotheses of `ca2_energy_identity` are met on the unit disc of `ℝ²` by the identity
field, the zero solution, zero datum and the zero weight. -/
example : True := by
  have hZ : LocalizedZeroTraceFunctionOn (Metric.ball (0 : Vec 2) 1) Set.univ
      (fun x => (0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x - (fun _ : Vec 2 => (0 : ℝ)) x) := by
    intro η _ _ _
    refine ⟨0, ?_⟩
    funext x
    show (0 : H10Function (Metric.ball (0 : Vec 2) 1)).toH1Function.toFun x = η x * ((0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x - 0)
    simp
    rfl
  have := ca2_energy_identity (d := 2) (V := Metric.ball (0 : Vec 2) 1) (T := Set.univ)
    Metric.isOpen_ball isOpen_univ (A := fun _ => (1 : Mat 2)) (lam := 1) (Lam := 1) (ν := 1)
    (Section6.ew1_ellip _ Metric.isOpen_ball.measurableSet)
    (fun x _ => by ext i j; simp [symmPart, Matrix.one_apply, eq_comm])
    (0 : H1Function (Metric.ball (0 : Vec 2) 1)) (f := fun _ => 0)
    (fun φ => by simp [matVecMul, vecDot]) (γ := fun _ => 0) contDiff_const hZ
    (Φ := fun _ => 0) contDiff_const HasCompactSupport.zero (by simp)
  trivial

end SuperdiffusionCLT.Section7
