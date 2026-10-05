/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaN
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayB

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The face identity and the moments of a tangential affine function

For `u` with localized zero trace on a face window and a smooth compactly supported `θ`,
`∫ u ∂_e θ = - ∫ θ ∂_e u`.  Testing with product-form `θ` computes the moments of the
tangential-affine part `a + ∑ b_k x_k` exactly (box integrals factor over the coordinates).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}


/-- The Cauchy-Schwarz inequality in squared form. -/
theorem r3d_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G : α → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ x, F x * G x ∂μ) ^ 2 ≤ (∫ x, F x ^ 2 ∂μ) * ∫ x, G x ^ 2 ∂μ := by
  have iFF : Integrable (fun x => F x ^ 2) μ := hF.integrable_sq
  have iGG : Integrable (fun x => G x ^ 2) μ := hG.integrable_sq
  have iFG : Integrable (fun x => F x * G x) μ := hF.integrable_mul hG
  have key : ∀ t : ℝ, 0 ≤ (∫ x, F x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, F x * G x ∂μ) * t +
      ∫ x, G x ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * F x + G x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have h1 : ∫ x, (t * F x + G x) ^ 2 ∂μ =
        t * t * ∫ x, F x ^ 2 ∂μ + 2 * t * ∫ x, F x * G x ∂μ + ∫ x, G x ^ 2 ∂μ := by
      have e : ∀ x, (t * F x + G x) ^ 2 = (t * t) * F x ^ 2 + (2 * t) * (F x * G x) + G x ^ 2 := by
        intro x; ring
      simp_rw [e]
      have j1 : Integrable (fun x => t * t * F x ^ 2) μ := iFF.const_mul _
      have j2 : Integrable (fun x => 2 * t * (F x * G x)) μ := iFG.const_mul _
      have j12 : Integrable (fun x => t * t * F x ^ 2 + 2 * t * (F x * G x)) μ := j1.add j2
      rw [integral_add j12 iGG, integral_add j1 j2, integral_const_mul, integral_const_mul]
    rw [h1] at h0
    linarith only [h0]
  have hd := discrim_le_zero key
  unfold discrim at hd
  linarith only [hd]

/-- The tangential-affine function `a + ∑_{k ≠ e} b_k x_k`. -/
noncomputable def r3d_m (e : Fin d) (a : ℝ) (b : Vec d) (x : Vec d) : ℝ :=
  a + ∑ k ∈ Finset.univ.erase e, b k * x k

theorem r3d_m_continuous (e : Fin d) (a : ℝ) (b : Vec d) : Continuous (r3d_m e a b) := by
  unfold r3d_m
  exact continuous_const.add (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k))

theorem r3d_m_abs_le (e : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} {x : Vec d} (hx : ∀ i, |x i| ≤ L) :
    |r3d_m e a b x| ≤ |a| + L * ∑ k ∈ Finset.univ.erase e, |b k| := by
  unfold r3d_m
  calc |a + ∑ k ∈ Finset.univ.erase e, b k * x k|
      ≤ |a| + |∑ k ∈ Finset.univ.erase e, b k * x k| := abs_add_le _ _
    _ ≤ |a| + ∑ k ∈ Finset.univ.erase e, |b k * x k| :=
        add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ |a| + ∑ k ∈ Finset.univ.erase e, L * |b k| := by
        refine add_le_add_right (Finset.sum_le_sum fun k _ => ?_) _
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hx k) (abs_nonneg _)
    _ = |a| + L * ∑ k ∈ Finset.univ.erase e, |b k| := by rw [Finset.mul_sum]

theorem r3d_openCube_eq_pi (m : ℤ) :
    openCubeSet (originCube d m) =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2)) := by
  ext x
  rw [hc_mem_openCubeSet_originCube_iff]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]

/-- Integration by parts against a test function for a function with localized zero trace. -/
theorem r3d_parts (Q : TriadicCube d) (e : Fin d) {T : Set (Vec d)}
    (u : H1Function (openCubeSet Q))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet Q) T u.toFun) {θ : Vec d → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) (hθT : tsupport θ ⊆ T) :
    ∫ x in openCubeSet Q, u.toFun x * p12_grad θ x e =
      -∫ x in openCubeSet Q, θ x * u.grad x e := by
  have hconv := r3c_isOpenBoundedConvex_cube Q
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := hconv.isFiniteMeasure_restrict_volume
  have hfin' : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using hfin
  obtain ⟨W, hW⟩ := hZ θ hθ hθc hθT
  have hWf : ∀ x, W.toH1Function.toFun x = θ x * u.toFun x := fun x => congrFun hW x
  have hWg := p12_grad_ae Q hθ hθc u W hWf
  have hz := integral_vecDot_const_zeroTraceGrad_eq_zero W (basisVec e : Vec d)
  have hdot : ∀ x, vecDot (basisVec e : Vec d) (W.toH1Function.grad x) = W.toH1Function.grad x e := by
    intro x
    simp [vecDot, basisVec, Pi.single_apply]
  simp only [hdot] at hz
  have hint1 : Integrable (fun x => θ x * u.grad x e) (volume.restrict (openCubeSet Q)) := by
    have h1 : MemLp (fun x => θ x * u.grad x e) 2 (volume.restrict (openCubeSet Q)) :=
      memLp_two_mul_bdd (φ := θ) (C := (hθ.continuous.bounded_above_of_compact_support hθc).choose)
        hθ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          have := (hθ.continuous.bounded_above_of_compact_support hθc).choose_spec x
          simpa using this) (u.grad_memL2 e)
    exact h1.integrable one_le_two
  have hint2 : Integrable (fun x => u.toFun x * p12_grad θ x e) (volume.restrict (openCubeSet Q)) := by
    have hc : Continuous (fun x => p12_grad θ x e) := (continuous_apply e).comp (p12_continuous_grad hθ)
    have hcc : HasCompactSupport (fun x => p12_grad θ x e) :=
      hθc.fderiv_apply (𝕜 := ℝ) (basisVec e : Vec d)
    have h1 : MemLp (fun x => (fun x => p12_grad θ x e) x * u.toFun x) 2 (volume.restrict (openCubeSet Q)) :=
      memLp_two_mul_bdd (φ := fun x => p12_grad θ x e)
        (C := (hc.bounded_above_of_compact_support hcc).choose) hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          have := (hc.bounded_above_of_compact_support hcc).choose_spec x
          simpa using this) u.memL2
    have := h1.integrable one_le_two
    simpa [mul_comm] using this
  have hae : ∫ x in openCubeSet Q, W.toH1Function.grad x e =
      ∫ x in openCubeSet Q, (θ x * u.grad x e + u.toFun x * p12_grad θ x e) := by
    refine integral_congr_ae ?_
    filter_upwards [hWg] with x hx
    rw [hx]
    simp [mul_comm]
  rw [hae, integral_add hint1 hint2] at hz
  linarith only [hz]


theorem r3d_face_identity (Q : TriadicCube d) (e : Fin d) {T : Set (Vec d)}
    (u : H1Function (openCubeSet Q))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet Q) T u.toFun) {θ : Vec d → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) (hθT : tsupport θ ⊆ T)
    {mf : Vec d → ℝ} (hmc : Continuous mf) {Cm : ℝ} (hmb : ∀ x ∈ openCubeSet Q, |mf x| ≤ Cm)
    {E : Set (Vec d)} (hE : MeasurableSet E) (hEΩ : E ⊆ openCubeSet Q)
    (hθE : ∀ x ∈ openCubeSet Q, θ x ≠ 0 → x ∈ E) :
    (∫ x in openCubeSet Q, mf x * p12_grad θ x e) ^ 2 ≤
      2 * ((∫ x in openCubeSet Q, θ x ^ 2) * ∫ x in E, u.grad x e ^ 2) +
        2 * ((∫ x in openCubeSet Q, p12_grad θ x e ^ 2) *
          ∫ x in openCubeSet Q, (u.toFun x - mf x) ^ 2) := by
  classical
  have hQo : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  have hQm : MeasurableSet (openCubeSet Q) := hQo.measurableSet
  have hconv := r3c_isOpenBoundedConvex_cube Q
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := hconv.isFiniteMeasure_restrict_volume
  have hdc : Continuous (fun x => p12_grad θ x e) :=
    (continuous_apply e).comp (p12_continuous_grad hθ)
  have hdk : HasCompactSupport (fun x => p12_grad θ x e) :=
    hθc.fderiv_apply (𝕜 := ℝ) (basisVec e : Vec d)
  have hθ2 : MemLp θ 2 (volume.restrict (openCubeSet Q)) :=
    hθ.continuous.memLp_of_hasCompactSupport hθc
  have hd2 : MemLp (fun x => p12_grad θ x e) 2 (volume.restrict (openCubeSet Q)) :=
    hdc.memLp_of_hasCompactSupport hdk
  have hm2 : MemLp mf 2 (volume.restrict (openCubeSet Q)) :=
    MemLp.of_bound hmc.aestronglyMeasurable Cm (by
      filter_upwards [ae_restrict_mem hQm] with x hx
      rw [Real.norm_eq_abs]; exact hmb x hx)
  have hu2 : MemLp u.toFun 2 (volume.restrict (openCubeSet Q)) := u.memL2
  have hg2 : MemLp (fun x => u.toFun x - mf x) 2 (volume.restrict (openCubeSet Q)) := hu2.sub hm2
  have hparts := r3d_parts Q e u hZ hθ hθc hθT
  have i1 : Integrable (fun x => u.toFun x * p12_grad θ x e) (volume.restrict (openCubeSet Q)) :=
    hu2.integrable_mul hd2
  have i2 : Integrable (fun x => (u.toFun x - mf x) * p12_grad θ x e) (volume.restrict (openCubeSet Q)) :=
    hg2.integrable_mul hd2
  have hsplit : ∫ x in openCubeSet Q, mf x * p12_grad θ x e =
      (∫ x in openCubeSet Q, u.toFun x * p12_grad θ x e) -
        ∫ x in openCubeSet Q, (u.toFun x - mf x) * p12_grad θ x e := by
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    ring
  have hG2 : MemLp (E.indicator (fun x => u.grad x e)) 2 (volume.restrict (openCubeSet Q)) :=
    (u.grad_memL2 e).indicator hE
  have hcs1 := r3d_cs hθ2 hG2
  have hcs2 := r3d_cs hd2 hg2
  have hI3 : ∫ x in openCubeSet Q, θ x * u.grad x e =
      ∫ x in openCubeSet Q, θ x * E.indicator (fun x => u.grad x e) x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    by_cases hθx : θ x = 0
    · simp [hθx]
    · rw [Set.indicator_of_mem (hθE x hx hθx)]
  have hGsq : ∫ x in openCubeSet Q, E.indicator (fun x => u.grad x e) x ^ 2 = ∫ x in E, u.grad x e ^ 2 := by
    have : (fun x => E.indicator (fun x => u.grad x e) x ^ 2) = E.indicator (fun x => u.grad x e ^ 2) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [this, integral_indicator hE, Measure.restrict_restrict hE, Set.inter_eq_left.2 hEΩ]
  rw [hGsq] at hcs1
  rw [← hI3] at hcs1
  have hI2 : ∫ x in openCubeSet Q, p12_grad θ x e * (u.toFun x - mf x) =
      ∫ x in openCubeSet Q, (u.toFun x - mf x) * p12_grad θ x e := by
    congr 1; funext x; ring
  rw [hI2] at hcs2
  rw [hsplit, hparts]
  set A := ∫ x in openCubeSet Q, θ x * u.grad x e
  set B := ∫ x in openCubeSet Q, (u.toFun x - mf x) * p12_grad θ x e
  have e1 : (-A - B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    have : 0 ≤ (A - B) ^ 2 := sq_nonneg _
    linarith only [this, show (-A - B) ^ 2 = A ^ 2 + 2 * A * B + B ^ 2 by ring,
      show (A - B) ^ 2 = A ^ 2 - 2 * A * B + B ^ 2 by ring]
  have e2 := mul_le_mul_of_nonneg_left hcs1 (by norm_num : (0 : ℝ) ≤ 2)
  have e3 := mul_le_mul_of_nonneg_left hcs2 (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [e1, e2, e3]



theorem r3d_prod_integrable (H : Fin d → ℝ → ℝ) (hc : ∀ i, Continuous (H i))
    (hk : ∀ i, HasCompactSupport (H i)) :
    Integrable (fun x : Vec d => ∏ i, H i (x i)) := by
  have h1 : Continuous (fun x : Vec d => ∏ i, H i (x i)) :=
    continuous_finsetProd _ fun i _ => (hc i).comp (continuous_apply i)
  exact h1.integrable_of_hasCompactSupport (r3d_prod_hasCompactSupport H hk)

theorem r3d_moment (e : Fin d) {L : ℝ} (a : ℝ) (b : Vec d) (Ψ : Fin d → ℝ → ℝ) (P : ℝ → ℝ)
    (hΨc : ∀ i, Continuous (Ψ i)) (hΨk : ∀ i, HasCompactSupport (Ψ i)) (hPc : Continuous P)
    (hPk : HasCompactSupport P) (hP : ∫ t in Set.Ioo (-L) L, P t = -1) :
    ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L),
        (a + ∑ k ∈ Finset.univ.erase e, b k * x k) *
          ((∏ j ∈ Finset.univ.erase e, Ψ j (x j)) * P (x e)) =
      -(a * ∏ i ∈ Finset.univ.erase e, (∫ t in Set.Ioo (-L) L, Ψ i t) +
        ∑ k ∈ Finset.univ.erase e, b k * ∏ i ∈ Finset.univ.erase e,
          (if i = k then (∫ t in Set.Ioo (-L) L, t * Ψ i t) else (∫ t in Set.Ioo (-L) L, Ψ i t))) := by
  classical
  set H : Fin d → ℝ → ℝ := fun i => if i = e then P else Ψ i with hH
  have hHc : ∀ i, Continuous (H i) := fun i => by
    by_cases h : i = e <;> simp [hH, h, hPc, hΨc i]
  have hHk : ∀ i, HasCompactSupport (H i) := fun i => by
    by_cases h : i = e <;> simp [hH, h, hPk, hΨk i]
  set Hk : Fin d → Fin d → ℝ → ℝ := fun k i => if i = k then (fun t => t * H i t) else H i with hHk'
  have hHkc : ∀ k i, Continuous (Hk k i) := fun k i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [hHk', ite_true]; exact continuous_id.mul (hHc i)
    · simp only [hHk', h, ite_false]; exact hHc i
  have hHkk : ∀ k i, HasCompactSupport (Hk k i) := fun k i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [hHk', ite_true]
      exact (hHk i).mono' (fun t ht => subset_tsupport _ (by
        intro h0; apply ht; simp [h0]))
    · simp only [hHk', h, ite_false]; exact hHk i
  have hprod : ∀ x : Vec d, (∏ j ∈ Finset.univ.erase e, Ψ j (x j)) * P (x e) = ∏ i, H i (x i) := by
    intro x
    rw [← Finset.mul_prod_erase Finset.univ (fun i => H i (x i)) (Finset.mem_univ e), mul_comm]
    congr 1
    · simp [hH]
    · exact Finset.prod_congr rfl fun j hj => by
        have : j ≠ e := (Finset.mem_erase.1 hj).1
        simp [hH, this]
  have hprodk : ∀ k, ∀ x : Vec d, x k * ∏ i, H i (x i) = ∏ i, Hk k i (x i) := by
    intro k x
    rw [← Finset.mul_prod_erase Finset.univ (fun i => H i (x i)) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun i => Hk k i (x i)) (Finset.mem_univ k)]
    have h1 : Hk k k (x k) = x k * H k (x k) := by simp [hHk']
    rw [h1, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun j hj => by
      have : j ≠ k := (Finset.mem_erase.1 hj).1
      simp [hHk', this]
  have hint : ∀ k, Integrable (fun x : Vec d => ∏ i, Hk k i (x i)) := fun k =>
    r3d_prod_integrable _ (hHkc k) (hHkk k)
  have hint0 : Integrable (fun x : Vec d => ∏ i, H i (x i)) := r3d_prod_integrable _ hHc hHk
  have hpt : ∀ x : Vec d, (a + ∑ k ∈ Finset.univ.erase e, b k * x k) *
      ((∏ j ∈ Finset.univ.erase e, Ψ j (x j)) * P (x e)) =
      a * ∏ i, H i (x i) + ∑ k ∈ Finset.univ.erase e, b k * ∏ i, Hk k i (x i) := by
    intro x
    rw [hprod x, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hprodk k x]
    ring
  simp_rw [hpt]
  rw [integral_add (hint0.const_mul a).integrableOn
    (integrable_finsetSum _ fun k _ => (hint k).const_mul (b k)).integrableOn]
  have hA : ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L), ∏ i, H i (x i) =
      -∏ i ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ i t := by
    rw [r3d_integral_pi H, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
    have h1 : (∫ t in Set.Ioo (-L) L, H e t) = -1 := by simp [hH, hP]
    rw [h1]
    have h2 : ∏ i ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, H i t =
        ∏ i ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ i t :=
      Finset.prod_congr rfl fun j hj => by
        have : j ≠ e := (Finset.mem_erase.1 hj).1
        simp [hH, this]
    rw [h2]; ring
  have hB : ∀ k ∈ Finset.univ.erase e,
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L), ∏ i, Hk k i (x i) =
      -∏ i ∈ Finset.univ.erase e,
        (if i = k then ∫ t in Set.Ioo (-L) L, t * Ψ i t else ∫ t in Set.Ioo (-L) L, Ψ i t) := by
    intro k hk
    have hke : k ≠ e := (Finset.mem_erase.1 hk).1
    rw [r3d_integral_pi (Hk k), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
    have h1 : (∫ t in Set.Ioo (-L) L, Hk k e t) = -1 := by
      have : e ≠ k := Ne.symm hke
      simp [hHk', this, hH, hP]
    rw [h1]
    have h2 : ∏ i ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Hk k i t =
        ∏ i ∈ Finset.univ.erase e,
          (if i = k then ∫ t in Set.Ioo (-L) L, t * Ψ i t else ∫ t in Set.Ioo (-L) L, Ψ i t) :=
      Finset.prod_congr rfl fun j hj => by
        have hje : j ≠ e := (Finset.mem_erase.1 hj).1
        by_cases hjk : j = k
        · subst hjk
          simp [hHk', hH, hje]
        · simp [hHk', hH, hje, hjk]
    rw [h2]; ring
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => ((hint k).const_mul (b k)).integrableOn), hA]
  have h3 : ∑ k ∈ Finset.univ.erase e,
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L), b k * ∏ i, Hk k i (x i) =
      ∑ k ∈ Finset.univ.erase e, b k * -∏ i ∈ Finset.univ.erase e,
        (if i = k then ∫ t in Set.Ioo (-L) L, t * Ψ i t else ∫ t in Set.Ioo (-L) L, Ψ i t) :=
    Finset.sum_congr rfl fun k hk => by rw [integral_const_mul, hB k hk]
  rw [h3]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring



/-- The factor functions of the test function: the normal profile in direction `e` and `Ψ i` in
the other directions. -/
noncomputable def r3d_phi (e : Fin d) (L h : ℝ) (Ψ : Fin d → ℝ → ℝ) (i : Fin d) : ℝ → ℝ :=
  if i = e then r3d_prof L h else Ψ i

/-- The product-form test function. -/
noncomputable def r3d_theta (e : Fin d) (L h : ℝ) (Ψ : Fin d → ℝ → ℝ) (x : Vec d) : ℝ :=
  ∏ i, r3d_phi e L h Ψ i (x i)

theorem r3d_theta_contDiff (e : Fin d) (L h : ℝ) (Ψ : Fin d → ℝ → ℝ)
    (hΨ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i)) : ContDiff ℝ (⊤ : ℕ∞) (r3d_theta e L h Ψ) :=
  r3d_prod_contDiff _ fun i => by
    by_cases hi : i = e
    · simp [r3d_phi, hi, r3d_prof_contDiff L h]
    · simp [r3d_phi, hi, hΨ i]

theorem r3d_theta_compact (e : Fin d) {L h : ℝ} (hh : 0 < h) (Ψ : Fin d → ℝ → ℝ)
    (hΨ : ∀ i, HasCompactSupport (Ψ i)) : HasCompactSupport (r3d_theta e L h Ψ) :=
  r3d_prod_hasCompactSupport _ fun i => by
    by_cases hi : i = e
    · simp [r3d_phi, hi, r3d_prof_compact L hh]
    · simp [r3d_phi, hi, hΨ i]

theorem r3d_theta_tsupport (e : Fin d) {L h ρ : ℝ} (hh : 0 < h) (Ψ : Fin d → ℝ → ℝ)
    (hΨ : ∀ i, tsupport (Ψ i) ⊆ Set.Icc (-ρ) ρ) {x : Vec d} (hx : x ∈ tsupport (r3d_theta e L h Ψ)) :
    (∀ i, i ≠ e → |x i| ≤ ρ) ∧ |x e + L| ≤ h := by
  have h1 := r3d_prod_tsupport _ hx
  refine ⟨fun i hi => ?_, ?_⟩
  · have := h1 i
    simp only [r3d_phi, hi, ite_false] at this
    exact abs_le.2 (hΨ i this)
  · have := h1 e
    simp only [r3d_phi, ite_true] at this
    have h2 := r3d_prof_tsupport L hh this
    rw [abs_le]
    constructor <;> linarith only [h2.1, h2.2]

theorem r3d_theta_grad_e (e : Fin d) (L h : ℝ) (Ψ : Fin d → ℝ → ℝ)
    (hΨ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i)) (x : Vec d) :
    p12_grad (r3d_theta e L h Ψ) x e =
      (∏ j ∈ Finset.univ.erase e, Ψ j (x j)) * deriv (r3d_prof L h) (x e) := by
  have hΦ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (r3d_phi e L h Ψ i) := fun i => by
    by_cases hi : i = e
    · simp [r3d_phi, hi, r3d_prof_contDiff L h]
    · simp [r3d_phi, hi, hΨ i]
  have h1 := r3d_prod_grad_e (r3d_phi e L h Ψ) hΦ e x
  unfold r3d_theta
  rw [h1]
  congr 1
  · exact Finset.prod_congr rfl fun j hj => by
      have : j ≠ e := (Finset.mem_erase.1 hj).1
      simp [r3d_phi, this]
  · simp [r3d_phi]

theorem r3d_integral_prod_sq {a b : ℝ} (G : Fin d → ℝ → ℝ) :
    ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo a b), (∏ i, G i (x i)) ^ 2 =
      ∏ i, ∫ t in Set.Ioo a b, G i t ^ 2 := by
  have : ∀ x : Vec d, (∏ i, G i (x i)) ^ 2 = ∏ i, (G i (x i)) ^ 2 := fun x => (Finset.prod_pow _ _ _).symm
  simp_rw [this]
  exact r3d_integral_pi (fun i t => G i t ^ 2)

theorem r3d_theta_sq_integral (e : Fin d) (L h : ℝ) (Ψ : Fin d → ℝ → ℝ) :
    ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L), r3d_theta e L h Ψ x ^ 2 =
      (∫ t in Set.Ioo (-L) L, r3d_prof L h t ^ 2) *
        ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 := by
  unfold r3d_theta
  rw [r3d_integral_prod_sq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  congr 1
  · simp [r3d_phi]
  · exact Finset.prod_congr rfl fun j hj => by
      have : j ≠ e := (Finset.mem_erase.1 hj).1
      simp [r3d_phi, this]

theorem r3d_dtheta_sq_integral (e : Fin d) (L h : ℝ) (Ψ : Fin d → ℝ → ℝ)
    (hΨ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i)) :
    ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L),
        p12_grad (r3d_theta e L h Ψ) x e ^ 2 =
      (∫ t in Set.Ioo (-L) L, deriv (r3d_prof L h) t ^ 2) *
        ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 := by
  set H : Fin d → ℝ → ℝ := fun i => if i = e then deriv (r3d_prof L h) else Ψ i with hH
  have hpt : ∀ x : Vec d, p12_grad (r3d_theta e L h Ψ) x e = ∏ i, H i (x i) := by
    intro x
    have h1 : ∏ i, H i (x i) = H e (x e) * ∏ j ∈ Finset.univ.erase e, H j (x j) :=
      (Finset.mul_prod_erase Finset.univ (fun i => H i (x i)) (Finset.mem_univ e)).symm
    have h2 : ∏ j ∈ Finset.univ.erase e, H j (x j) = ∏ j ∈ Finset.univ.erase e, Ψ j (x j) :=
      Finset.prod_congr rfl fun j hj => by
        have : j ≠ e := (Finset.mem_erase.1 hj).1
        simp [hH, this]
    have h3 : H e (x e) = deriv (r3d_prof L h) (x e) := by simp [hH]
    rw [r3d_theta_grad_e e L h Ψ hΨ x, h1, h2, h3, mul_comm]
  simp_rw [hpt]
  rw [r3d_integral_prod_sq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  congr 1
  · simp [hH]
  · exact Finset.prod_congr rfl fun j hj => by
      have : j ≠ e := (Finset.mem_erase.1 hj).1
      simp [hH, this]


end SuperdiffusionCLT.Section7
