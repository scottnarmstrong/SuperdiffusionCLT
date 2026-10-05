/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.BallBoundaryB
public import SuperdiffusionCLT.Section8.DivergenceForm.ScalarWeakSolution
public import Homogenization.Sobolev.Truncation.MatchedTrace
public import Homogenization.Sobolev.Truncation.Basic
public import Homogenization.Sobolev.H1.Algebra.H1Function
public import Homogenization.Sobolev.H1.Algebra.H10Function

/-!
# Comparison of a zero-trace solution with a classical supersolution

For `u ∈ H¹₀(U)` and `ψ ∈ H¹(U)` with `ψ ≥ 0` in `U`, the positive part of `u - ψ` is an `H¹₀(U)`
function, with the expected almost-everywhere gradient (`ballBdry_exists_positivePart`).  The
quadratic form of `ν Id + K` with `K` skew is nonnegative (`ballBdry_pointwise_nonneg`), and the
flux integrand of a bounded matrix field against `L²` vectors is integrable
(`ballBdry_integrable_flux`).  These give `ballBdry_compare`: a zero-trace weak solution of
`lam u - ∇·(a∇u) = 1` lies below every `C¹` function `ψ ≥ 0` whose flux `a ∇ψ` is a `C¹` field with
`-∇·(a∇ψ) ≥ 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm

variable {d : ℕ}

theorem ballBdry_h1_grad_ae_eq {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (p q : H1Function U) (h : p.toFun = q.toFun) :
    ∀ᵐ x ∂(volumeMeasureOn U), p.grad x = q.grad x := by
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hcoord : ∀ i : Fin d,
      (fun x => p.grad x i) =ᵐ[volumeMeasureOn U] fun x => q.grad x i := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc _ i) (hloc _ i) ?_ (q.hasWeakGradient i)
    have hweak := p.hasWeakGradient i
    rw [h] at hweak
    exact hweak
  filter_upwards [(ae_all_iff).2 hcoord] with x hx
  funext i
  exact hx i

/-- The positive part of `u - ψ` is an `H¹₀` function when `ψ ≥ 0` in `U` and `u ∈ H¹₀`. -/
theorem ballBdry_exists_positivePart {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (ψ : H1Function U) (hψ0 : ∀ x ∈ U, 0 ≤ ψ.toFun x) :
    ∃ v : H10Function U, (∀ x ∈ U, v.toH1Function.toFun x = max (u.toH1Function.toFun x - ψ.toFun x) 0) ∧
      ∀ᵐ x ∂(volumeMeasureOn U), v.toH1Function.grad x =
        {y | ψ.toFun y < u.toH1Function.toFun y}.indicator
          (fun y => u.toH1Function.grad y - ψ.grad y) x := by
  set w₁ : H1Function U := u.toH1Function - ψ with hw₁
  set w₂ : H1Function U := -ψ with hw₂
  have hmatch : MemH10 U (fun x => w₁.toFun x - w₂.toFun x) := by
    refine ⟨u, ?_⟩
    funext x
    simp [hw₁, hw₂]
  obtain ⟨v, hv⟩ := memH10_max_sub_matched hU w₁ w₂ hmatch 0
  obtain ⟨q₁, hq₁f, hq₁g⟩ := exists_h1_max_sub_const hU w₁ 0
  obtain ⟨q₂, hq₂f, hq₂g⟩ := exists_h1_max_sub_const hU w₂ 0
  have hms : MeasurableSet U := hU.isOpen.measurableSet
  have hvq : v.toH1Function.toFun = (q₁ - q₂).toFun := by
    funext x
    rw [hv]
    simp only [H1Function.sub_toFun, hq₁f, hq₂f]
  have hgrad := ballBdry_h1_grad_ae_eq hU v.toH1Function (q₁ - q₂) hvq
  refine ⟨v, fun x hx => ?_, ?_⟩
  · have := congrFun hv x
    rw [this]
    have h2 : max (w₂.toFun x - 0) 0 = 0 := by
      simp only [hw₂, H1Function.neg_toFun, sub_zero]
      exact max_eq_right (by linarith only [hψ0 x hx])
    rw [h2]
    simp [hw₁]
  · filter_upwards [hgrad, hq₁g, hq₂g, self_mem_ae_restrict hms] with x h1 h2 h3 hx
    rw [h1]
    have hne : ¬ (0 < w₂.toFun x) := by
      simp only [hw₂, H1Function.neg_toFun]
      linarith only [hψ0 x hx]
    have hw1g : w₁.grad = fun y => u.toH1Function.grad y - ψ.grad y := by
      simp only [hw₁, H1Function.sub_grad]
    have hw1f : ∀ y, w₁.toFun y = u.toH1Function.toFun y - ψ.toFun y := fun y => by
      simp only [hw₁, H1Function.sub_toFun]
    have hqs : (q₁ - q₂).grad x = q₁.grad x - q₂.grad x := by
      simp only [H1Function.sub_grad]
    rw [hqs]
    have hz : ({y | 0 < w₂.toFun y} : Set (Vec d)).indicator w₂.grad x = 0 :=
      Set.indicator_of_notMem (by simpa using hne) _
    rw [h2, h3, hz, sub_zero]
    by_cases hlt : ψ.toFun x < u.toH1Function.toFun x
    · rw [Set.indicator_of_mem (by simp only [hw1f, Set.mem_ofPred_eq]; linarith only [hlt]),
        Set.indicator_of_mem (by simpa using hlt), hw1g]
    · rw [Set.indicator_of_notMem (by simp only [hw1f, Set.mem_ofPred_eq]; linarith only [hlt]),
        Set.indicator_of_notMem (by simpa using hlt)]

theorem ballBdry_skew_vec {K : Mat d} (hK : ∀ i j, K i j = -K j i) (ξ : Vec d) :
    vecDot (matVecMul K ξ) ξ = 0 := by
  have := ballBdry_skew_quad hK ξ
  unfold vecDot matVecMul
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem ballBdry_pointwise_nonneg {ν : ℝ} (hν : 0 ≤ ν) {K : Mat d} (hK : ∀ i j, K i j = -K j i)
    (X Z W : Vec d) (hW : W = X - Z ∨ W = 0) :
    0 ≤ vecDot (matVecMul (ν • (1 : Mat d) + K) X) W -
      vecDot (matVecMul (ν • (1 : Mat d) + K) Z) W := by
  rcases hW with rfl | rfl
  · have h : vecDot (matVecMul (ν • (1 : Mat d) + K) X) (X - Z) -
        vecDot (matVecMul (ν • (1 : Mat d) + K) Z) (X - Z) =
        vecDot (matVecMul (ν • (1 : Mat d) + K) (X - Z)) (X - Z) := by
      unfold vecDot matVecMul
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_mul, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [h]
    have h2 : vecDot (matVecMul (ν • (1 : Mat d) + K) (X - Z)) (X - Z) =
        ν * vecDot (X - Z) (X - Z) + vecDot (matVecMul K (X - Z)) (X - Z) := by
      unfold vecDot matVecMul
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul]
      congr 1
      simp [smul_eq_mul, ite_mul, Finset.sum_ite_eq]
      ring
    rw [h2, ballBdry_skew_vec hK, add_zero]
    exact mul_nonneg hν (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  · simp [vecDot]

theorem ballBdry_memLp_bdd_mul {μ : Measure (Vec d)} {a f : Vec d → ℝ}
    (ha : AEStronglyMeasurable a μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, |a x| ≤ C)
    (hf : MemLp f 2 μ) : MemLp (fun x => a x * f x) 2 μ := by
  refine hf.of_le_mul (c := C) (ha.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hC] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem ballBdry_integrable_flux {μ : Measure (Vec d)} [IsFiniteMeasure μ] {A : Vec d → Mat d}
    (hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ) {C : ℝ}
    (hAb : ∀ᵐ x ∂μ, ∀ i j, |A x i j| ≤ C) {X Y : Vec d → Vec d}
    (hX : ∀ i, MemLp (fun x => X x i) 2 μ) (hY : ∀ i, MemLp (fun x => Y x i) 2 μ) :
    Integrable (fun x => vecDot (matVecMul (A x) (X x)) (Y x)) μ := by
  unfold vecDot matVecMul
  refine integrable_finsetSum _ fun i _ => ?_
  have : ∀ x, (∑ j, A x i j * X x j) * Y x i = ∑ j, (A x i j * X x j) * Y x i := fun x =>
    Finset.sum_mul _ _ _
  simp only [this]
  refine integrable_finsetSum _ fun j _ => ?_
  exact (ballBdry_memLp_bdd_mul (hAm i j) (by filter_upwards [hAb] with x hx using hx i j)
    (hX j)).integrable_mul (hY i)

/-- Entries of a continuous matrix field are bounded on a compact set. -/
theorem ballBdry_entry_bound {k : Vec d → Mat d} (hk : ∀ i j, Continuous fun x => k x i j)
    {S : Set (Vec d)} (hS : IsCompact S) : ∃ C : ℝ, ∀ x ∈ S, ∀ i j, |k x i j| ≤ C := by
  set g : Vec d → ℝ := fun x => ∑ i, ∑ j, |k x i j| with hg
  have hcont : Continuous g := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_abs.comp (hk i j)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x hx i j => ?_⟩
  have hle : ‖g x‖ ≤ C := hC x hx
  rw [Real.norm_eq_abs] at hle
  have hsingle : |k x i j| ≤ g x := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j' : Fin d, |k x i' j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin d => |k x i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  exact hsingle.trans ((le_abs_self (g x)).trans hle)

/-- **Comparison with a classical supersolution.**  A zero-trace weak solution `u` of
`lam u - ∇·(a∇u) = 1` is below every `C¹` function `ψ ≥ 0` in `U` whose flux `a ∇ψ` is a `C¹`
field with `-∇·(a∇ψ) ≥ 1` in `U`, where `a = ν Id + k` with `k` skew. -/
theorem ballBdry_compare {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {ν : ℝ}
    (hν : 0 < ν) {k : Vec d → Mat d} (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j))
    (hskew : ∀ x i j, k x i j = -k x j i) {lam : ℝ} (hlam : 0 < lam) (u : H10Function U)
    (hu : IsScalarForcedWeakSolution (fun x => ν • (1 : Mat d) + k x) U
      (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψ0 : ∀ x ∈ U, 0 ≤ ψ x) {x₀ : Vec d} {R : ℝ}
    (hR : 0 ≤ R) (hUR : U ⊆ Metric.closedBall x₀ R)
    (hG : ∀ i, ContDiff ℝ 1 (fun x =>
      matVecMul (ν • (1 : Mat d) + k x) (fun j => fderiv ℝ ψ x (basisVec j)) i))
    (hdiv : ∀ x ∈ U, 1 ≤ -ballBdry_div
      (fun x => matVecMul (ν • (1 : Mat d) + k x) (fun j => fderiv ℝ ψ x (basisVec j))) x) :
    ∀ᵐ x ∂(volumeMeasureOn U), u.toH1Function.toFun x ≤ ψ x := by
  have hfin : IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hms : MeasurableSet U := hU.isOpen.measurableSet
  set Gs : Vec d → Vec d := fun x =>
    matVecMul (ν • (1 : Mat d) + k x) (fun j => fderiv ℝ ψ x (basisVec j)) with hGs
  let ψh : H1Function U := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hψ
  have hψh : ∀ x, ψh.toFun x = ψ x := fun x => rfl
  have hψhg : ∀ x, ψh.grad x = fun j => fderiv ℝ ψ x (basisVec j) := fun x => rfl
  obtain ⟨v, hvval, hvgrad⟩ := ballBdry_exists_positivePart hU u ψh (fun x hx => by
    rw [hψh]; exact hψ0 x hx)
  -- bounds
  have hcompact : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
  have hcA : ∀ i j, Continuous (fun x => (ν • (1 : Mat d) + k x) i j) := fun i j =>
    (continuous_const (y := (ν • (1 : Mat d)) i j)).add (hk i j).continuous
  obtain ⟨C, hC⟩ := ballBdry_entry_bound (k := fun x => ν • (1 : Mat d) + k x) hcA hcompact
  have hdivcont : Continuous (ballBdry_div Gs) := ballBdry_continuous_div hG
  obtain ⟨D, hD⟩ := hcompact.exists_bound_of_continuousOn hdivcont.continuousOn
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => (ν • (1 : Mat d) + k x) i j)
      (volumeMeasureOn U) := fun i j => (hcA i j).aestronglyMeasurable
  have hAb : ∀ᵐ x ∂(volumeMeasureOn U), ∀ i j, |(ν • (1 : Mat d) + k x) i j| ≤ C := by
    filter_upwards [self_mem_ae_restrict hms] with x hx i j
    exact hC x (hUR hx) i j
  have hvL2 : ∀ i, MemLp (fun x => v.toH1Function.grad x i) 2 (volumeMeasureOn U) :=
    v.toH1Function.gradMemL2
  have huL2 : ∀ i, MemLp (fun x => u.toH1Function.grad x i) 2 (volumeMeasureOn U) :=
    u.toH1Function.gradMemL2
  have hpL2 : ∀ i, MemLp (fun x => ψh.grad x i) 2 (volumeMeasureOn U) := ψh.gradMemL2
  have hI1 := ballBdry_integrable_flux hAm hAb huL2 hvL2
  have hI2 := ballBdry_integrable_flux hAm hAb hpL2 hvL2
  have hvv : ∀ x ∈ U, v.toH1Function.toFun x = max (u.toH1Function.toFun x - ψ x) 0 := hvval
  have hv0 : ∀ x ∈ U, 0 ≤ v.toH1Function.toFun x := fun x hx => by
    rw [hvv x hx]; exact le_max_right _ _
  have E1 := hu.2 v
  have E2 := ballBdry_ibp_of_contDiff hU hG hR hUR v
  have hu2 : MemLp (fun y => 1 - lam * u.toH1Function.toFun y) 2 (volumeMeasureOn U) := hu.1
  have hI3 : Integrable (fun x => (1 - lam * u.toH1Function.toFun x) * v.toH1Function.toFun x)
      (volumeMeasureOn U) := hu2.integrable_mul v.toH1Function.memL2
  have hdivL2 : MemLp (ballBdry_div Gs) 2 (volumeMeasureOn U) :=
    MemLp.of_bound hdivcont.aestronglyMeasurable D (by
      filter_upwards [self_mem_ae_restrict hms] with x hx
      exact hD x (hUR hx))
  have hI4 : Integrable (fun x => ballBdry_div Gs x * v.toH1Function.toFun x)
      (volumeMeasureOn U) := hdivL2.integrable_mul v.toH1Function.memL2
  have hI5 : Integrable (fun x => u.toH1Function.toFun x * v.toH1Function.toFun x)
      (volumeMeasureOn U) := u.toH1Function.memL2.integrable_mul v.toH1Function.memL2
  have hI6 : Integrable (fun x => v.toH1Function.toFun x * v.toH1Function.toFun x)
      (volumeMeasureOn U) := v.toH1Function.memL2.integrable_mul v.toH1Function.memL2
  -- pointwise inequalities
  have P1 : ∀ᵐ x ∂(volumeMeasureOn U), 0 ≤
      vecDot (matVecMul (ν • (1 : Mat d) + k x) (u.toH1Function.grad x)) (v.toH1Function.grad x) -
        vecDot (Gs x) (v.toH1Function.grad x) := by
    filter_upwards [hvgrad] with x hx
    have hW : v.toH1Function.grad x = u.toH1Function.grad x - ψh.grad x ∨
        v.toH1Function.grad x = 0 := by
      rw [hx]
      by_cases hmem : x ∈ {y | ψh.toFun y < u.toH1Function.toFun y}
      · left
        rw [Set.indicator_of_mem hmem]
      · right
        rw [Set.indicator_of_notMem hmem]
    have hGx : Gs x = matVecMul (ν • (1 : Mat d) + k x) (ψh.grad x) := rfl
    rw [hGx]
    exact ballBdry_pointwise_nonneg hν.le (hskew x) _ _ _ hW
  have P2 : ∀ᵐ x ∂(volumeMeasureOn U),
      (1 - lam * u.toH1Function.toFun x) * v.toH1Function.toFun x +
        ballBdry_div Gs x * v.toH1Function.toFun x ≤
      -lam * (u.toH1Function.toFun x * v.toH1Function.toFun x) := by
    filter_upwards [self_mem_ae_restrict hms] with x hx
    have h1 := hdiv x hx
    have h2 := hv0 x hx
    have : (1 + ballBdry_div Gs x) * v.toH1Function.toFun x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [h1]) h2
    linarith only [this]
  have P3 : ∀ᵐ x ∂(volumeMeasureOn U),
      v.toH1Function.toFun x * v.toH1Function.toFun x ≤
        u.toH1Function.toFun x * v.toH1Function.toFun x := by
    filter_upwards [self_mem_ae_restrict hms] with x hx
    have h2 := hv0 x hx
    rcases (hv0 x hx).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hmax : max (u.toH1Function.toFun x - ψ x) 0 = v.toH1Function.toFun x := (hvv x hx).symm
      have hle : v.toH1Function.toFun x ≤ u.toH1Function.toFun x := by
        have hp := hψ0 x hx
        rcases max_cases (u.toH1Function.toFun x - ψ x) 0 with ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hm] at hmax; linarith only [hmax, hp]
        · rw [hm] at hmax; linarith only [hmax, hpos]
      exact mul_le_mul_of_nonneg_right hle h2
  -- integral chain
  have hdiff : 0 ≤ ∫ x in U,
      (vecDot (matVecMul (ν • (1 : Mat d) + k x) (u.toH1Function.grad x)) (v.toH1Function.grad x) -
        vecDot (Gs x) (v.toH1Function.grad x)) := integral_nonneg_of_ae P1
  rw [integral_sub hI1 (show Integrable (fun x => vecDot (Gs x) (v.toH1Function.grad x)) _ from hI2), E1, E2] at hdiff
  have hsum : ∫ x in U, ((1 - lam * u.toH1Function.toFun x) * v.toH1Function.toFun x +
      ballBdry_div Gs x * v.toH1Function.toFun x) ≤
      ∫ x in U, -lam * (u.toH1Function.toFun x * v.toH1Function.toFun x) :=
    integral_mono_ae (hI3.add hI4) (hI5.const_mul (-lam)) P2
  rw [integral_add hI3 hI4, integral_const_mul] at hsum
  have hvv_le : ∫ x in U, v.toH1Function.toFun x * v.toH1Function.toFun x ≤
      ∫ x in U, u.toH1Function.toFun x * v.toH1Function.toFun x :=
    integral_mono_ae hI6 hI5 P3
  have hvv_nonneg : 0 ≤ ∫ x in U, v.toH1Function.toFun x * v.toH1Function.toFun x :=
    integral_nonneg fun x => mul_self_nonneg _
  have huv : ∫ x in U, u.toH1Function.toFun x * v.toH1Function.toFun x ≤ 0 := by
    by_contra hcon
    replace hcon := not_le.mp hcon
    nlinarith only [hdiff, hsum, hcon, hlam]
  have hzero : ∫ x in U, v.toH1Function.toFun x * v.toH1Function.toFun x = 0 :=
    le_antisymm (hvv_le.trans huv) hvv_nonneg
  have hae0 : (fun x => v.toH1Function.toFun x * v.toH1Function.toFun x) =ᵐ[volumeMeasureOn U] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) hI6).1 hzero
  filter_upwards [hae0, self_mem_ae_restrict hms] with x hx hxU
  have hxv : v.toH1Function.toFun x = 0 := by
    have : v.toH1Function.toFun x * v.toH1Function.toFun x = 0 := hx
    exact mul_self_eq_zero.mp this
  rw [hvv x hxU] at hxv
  rcases max_cases (u.toH1Function.toFun x - ψ x) 0 with ⟨hm, hh⟩ | ⟨hm, hh⟩
  · rw [hm] at hxv; linarith only [hxv, hh]
  · linarith only [hh]

end SuperdiffusionCLT.Section8
