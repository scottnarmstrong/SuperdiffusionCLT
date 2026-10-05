/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaE
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaB

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The cutoff equation in scalar form

For `u ∈ H¹(U)` solving `-∇·(A∇u) = f - ∇·g` on a cube and a smooth compactly supported cutoff `χ`
with `χ u ∈ H¹₀`, the product `χ u` solves `-∇·(A∇(χu)) = F` with the scalar datum
`r3c_cutoffData`, in which every divergence has been expanded (`r3c_integral_mul_vec_h10`).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The scalar datum of the cutoff equation. -/
noncomputable def r3c_cutoffData {U : Set (Vec d)} (A : CoeffField d) (χ : Vec d → ℝ)
    (f : Vec d → ℝ) (g : Vec d → Vec d) (u : H1Function U) (x : Vec d) : ℝ :=
  (χ x * f x + vecDot (g x) (p12_grad χ x) - vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) -
    (r3c_div (fun y => χ y • g y) x +
      (vecDot (u.grad x) (matVecMul (A x) (p12_grad χ x)) +
        u.toFun x * r3c_div (fun y => matVecMul (A y) (p12_grad χ y)) x))

theorem r3c_memLp_mul_bdd_on {U : Set (Vec d)} (hU : MeasurableSet U) {a f : Vec d → ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict U)) {M : ℝ} (hM : ∀ x ∈ U, |a x| ≤ M)
    (hf : MemLp f 2 (volume.restrict U)) : MemLp (fun x => a x * f x) 2 (volume.restrict U) := by
  refine hf.of_le_mul (c := M) (ha.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)

theorem r3c_memLp_vecDot {U : Set (Vec d)} (hU : MeasurableSet U) {F H : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hHm : ∀ i, AEStronglyMeasurable (fun x => H x i) (volume.restrict U)) {M : ℝ}
    (hHb : ∀ x ∈ U, ∀ i, |H x i| ≤ M) :
    MemLp (fun x => vecDot (F x) (H x)) 2 (volume.restrict U) := by
  have : (fun x => vecDot (F x) (H x)) = fun x => ∑ i, H x i * F x i := by
    funext x; simp only [vecDot]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]
  exact memLp_finsetSum (s := Finset.univ) (f := fun i x => H x i * F x i) fun i _ =>
    r3c_memLp_mul_bdd_on hU (hHm i) (fun x hx => hHb x hx i) (hF i)

theorem r3c_integrable_vecDot {U : Set (Vec d)} {F H : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (volume.restrict U)) :
    Integrable (fun x => vecDot (F x) (H x)) (volume.restrict U) := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ => (hF i).integrable_mul (hH i)

theorem r3c_memLp_matVec {U : Set (Vec d)} (hU : MeasurableSet U) {A : CoeffField d} {MA : ℝ}
    (hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict U))
    (hAb : ∀ x ∈ U, ∀ i j, |A x i j| ≤ MA) {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U)) (i : Fin d) :
    MemLp (fun x => matVecMul (A x) (F x) i) 2 (volume.restrict U) := by
  have : (fun x => matVecMul (A x) (F x) i) = fun x => ∑ j, A x i j * F x j := by
    funext x; simp [matVecMul]
  rw [this]
  exact memLp_finsetSum (s := Finset.univ) (f := fun j x => A x i j * F x j) fun j _ =>
    r3c_memLp_mul_bdd_on hU (hAm i j) (fun x hx => hAb x hx i j) (hF j)


theorem r3c_bdd_of_cpt {f : Vec d → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  exact ⟨M, fun x => by simpa using hM x⟩

theorem r3c_hasCompactSupport_sum {ι : Type*} [Fintype ι] {f : ι → Vec d → ℝ}
    (h : ∀ j, HasCompactSupport (f j)) : HasCompactSupport (fun x => ∑ j, f j x) := by
  refine HasCompactSupport.intro (K := ⋃ j, tsupport (f j)) (isCompact_iUnion fun j => (h j)) ?_
  intro x hx
  simp only [Set.mem_iUnion, not_exists] at hx
  exact Finset.sum_eq_zero fun j _ => image_eq_zero_of_notMem_tsupport (hx j)

theorem r3c_contDiff_grad_apply {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => p12_grad χ x i) :=
  (hχ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem r3c_contDiff_div {B : Vec d → Vec d} (hB : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x i)) :
    ContDiff ℝ (⊤ : ℕ∞) (r3c_div B) := by
  unfold r3c_div
  exact ContDiff.sum fun i _ =>
    ((hB i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem r3c_hasCompactSupport_div {B : Vec d → Vec d}
    (hBc : ∀ i, HasCompactSupport (fun x => B x i)) : HasCompactSupport (r3c_div B) := by
  unfold r3c_div
  exact r3c_hasCompactSupport_sum fun i => (hBc i).fderiv_apply (𝕜 := ℝ) (basisVec i)

theorem r3c_contDiff_matVec_grad {A : CoeffField d} (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => matVecMul (A x) (p12_grad χ x) i) := by
  simp only [matVecMul]
  exact ContDiff.sum fun j _ => (hAs i j).mul (r3c_contDiff_grad_apply hχ j)

theorem r3c_hasCompactSupport_matVec_grad {A : CoeffField d} {χ : Vec d → ℝ}
    (hχc : HasCompactSupport χ) (i : Fin d) :
    HasCompactSupport (fun x => matVecMul (A x) (p12_grad χ x) i) := by
  simp only [matVecMul]
  exact r3c_hasCompactSupport_sum fun j =>
    HasCompactSupport.mul_left (hχc.fderiv_apply (𝕜 := ℝ) (basisVec j))


theorem r3c_isOpenBoundedConvex_cube (Q : TriadicCube d) :
    IsOpenBoundedConvexDomain (openCubeSet Q) := by
  rw [p12d_openCubeSet_eq_axisCube]
  exact isOpenBoundedConvexDomain_axisCube _ _

/-- **The cutoff equation in scalar form.** -/
theorem r3c_cutoff_scalar (Q : TriadicCube d) {A : CoeffField d} {K MA : ℝ}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    (hAb : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j| ≤ MA)
    (hK : ∀ x ∈ openCubeSet Q, ∀ y : Vec d, ‖matVecMul (A x) y‖ ≤ K * ‖y‖)
    {u : H1Function (openCubeSet Q)} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hgs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => g x i))
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hu : IsWeakSolutionOn A (openCubeSet Q) u f g)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    {M Λ : ℝ} (hM : ∀ x, |χ x| ≤ M) (hΛ : ∀ x, ‖p12_grad χ x‖ ≤ Λ)
    (w : H10Function (openCubeSet Q)) (hw : ∀ x, w.toH1Function.toFun x = χ x * u.toFun x) :
    IsH10WeakSolution A (openCubeSet Q) (r3c_cutoffData A χ f g u) (fun _ => 0) w := by
  intro ψ
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)) :=
    fun i j => (hAs i j).continuous.aestronglyMeasurable
  have hloc := p12_localize Q hAm hK hf hg hu hχ hχc hM hΛ w hw ψ
  have hUo : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  have hUm : MeasurableSet (openCubeSet Q) := hUo.measurableSet
  -- `L²` facts
  have hfL : MemLp f 2 (volume.restrict (openCubeSet Q)) := memLp_restrict_of_normalized Q hf
  have hgL : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (openCubeSet Q)) := fun i =>
    (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hg).of_le
      ((continuous_apply i).comp_aestronglyMeasurable
        (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hg).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (g x) i)
  have hugL : ∀ i, MemLp (fun x => u.grad x i) 2 (volume.restrict (openCubeSet Q)) := fun i => u.grad_memL2 i
  have huL : MemLp u.toFun 2 (volume.restrict (openCubeSet Q)) := u.memL2
  have hψg : ∀ i, MemLp (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict (openCubeSet Q)) := fun i =>
    ψ.toH1Function.grad_memL2 i
  have hψL : MemLp ψ.toH1Function.toFun 2 (volume.restrict (openCubeSet Q)) := ψ.toH1Function.memL2
  have hχm : AEStronglyMeasurable χ (volume.restrict (openCubeSet Q)) := hχ.continuous.aestronglyMeasurable
  have hgχm : ∀ i, AEStronglyMeasurable (fun x => p12_grad χ x i) (volume.restrict (openCubeSet Q)) := fun i =>
    (r3c_contDiff_grad_apply hχ i).continuous.aestronglyMeasurable
  have hgχb : ∀ x ∈ (openCubeSet Q), ∀ i, |p12_grad χ x i| ≤ Λ := fun x _ i => (r3c_abs_apply_le _ i).trans (hΛ x)
  -- the fields `B = A ∇χ` and `B₁ = χ g`
  set B : Vec d → Vec d := fun x => matVecMul (A x) (p12_grad χ x) with hBdef
  have hBs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x i) := fun i => r3c_contDiff_matVec_grad hAs hχ i
  have hBc : ∀ i, HasCompactSupport (fun x => B x i) := fun i => r3c_hasCompactSupport_matVec_grad hχc i
  set B1 : Vec d → Vec d := fun x => χ x • g x with hB1def
  have hB1s : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => B1 x i) := fun i => by
    simpa [hB1def] using hχ.mul (hgs i)
  have hB1c : ∀ i, HasCompactSupport (fun x => B1 x i) := fun i => by
    show HasCompactSupport (fun x => χ x * g x i)
    exact hχc.mul_right
  obtain ⟨MB, hMB⟩ : ∃ MB : ℝ, ∀ x i, |B x i| ≤ MB := by
    choose Mi hMi using fun i => r3c_bdd_of_cpt (hBs i).continuous (hBc i)
    exact ⟨∑ i, |Mi i|, fun x i => (hMi i x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Mi j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))⟩
  obtain ⟨MD, hMD⟩ := r3c_bdd_of_cpt (r3c_contDiff_div hBs).continuous (r3c_hasCompactSupport_div hBc)
  have hvec : ∀ i, MemLp (fun x => B1 x i) 2 (volume.restrict (openCubeSet Q)) := fun i => by
    simpa [hB1def] using r3c_memLp_mul_bdd_on hUm hχm (fun x _ => hM x) (hgL i)
  have hBL : ∀ i, MemLp (fun x => B x i) 2 (volume.restrict (openCubeSet Q)) := fun i =>
    flatW2p_memLp_two_of_continuous (hBs i).continuous (hBc i)
  have hDB : MemLp (r3c_div B) 2 (volume.restrict (openCubeSet Q)) :=
    flatW2p_memLp_two_of_continuous (r3c_contDiff_div hBs).continuous (r3c_hasCompactSupport_div hBc)
  have hDB1 : MemLp (r3c_div B1) 2 (volume.restrict (openCubeSet Q)) :=
    flatW2p_memLp_two_of_continuous (r3c_contDiff_div hB1s).continuous (r3c_hasCompactSupport_div hB1c)
  -- integrability of the pieces
  have int1 : Integrable (fun x => vecDot (B1 x) (ψ.toH1Function.grad x)) (volume.restrict (openCubeSet Q)) :=
    r3c_integrable_vecDot hvec hψg
  have hBm : ∀ i, AEStronglyMeasurable (fun x => B x i) (volume.restrict (openCubeSet Q)) := fun i =>
    (hBs i).continuous.aestronglyMeasurable
  have hDBm : AEStronglyMeasurable (r3c_div B) (volume.restrict (openCubeSet Q)) :=
    (r3c_contDiff_div hBs).continuous.aestronglyMeasurable
  have hu1 : ∀ i, MemLp (fun x => (u.toFun x • B x) i) 2 (volume.restrict (openCubeSet Q)) := fun i => by
    simpa [mul_comm] using r3c_memLp_mul_bdd_on hUm (hBm i) (fun x _ => hMB x i) huL
  have int2 : Integrable (fun x => vecDot (u.toFun x • B x) (ψ.toH1Function.grad x))
      (volume.restrict (openCubeSet Q)) := r3c_integrable_vecDot hu1 hψg
  -- the pieces of `s'` and `T`
  have hs1 : MemLp (fun x => χ x * f x) 2 (volume.restrict (openCubeSet Q)) :=
    r3c_memLp_mul_bdd_on hUm hχm (fun x _ => hM x) hfL
  have hs2 : MemLp (fun x => vecDot (g x) (p12_grad χ x)) 2 (volume.restrict (openCubeSet Q)) :=
    r3c_memLp_vecDot hUm hgL hgχm hgχb
  have hAu : ∀ i, MemLp (fun x => matVecMul (A x) (u.grad x) i) 2 (volume.restrict (openCubeSet Q)) := fun i =>
    r3c_memLp_matVec hUm hAm hAb hugL i
  have hs3 : MemLp (fun x => vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) 2
      (volume.restrict (openCubeSet Q)) := r3c_memLp_vecDot hUm hAu hgχm hgχb
  have hSL : MemLp (fun x => χ x * f x + vecDot (g x) (p12_grad χ x) -
      vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) 2 (volume.restrict (openCubeSet Q)) :=
    (hs1.add hs2).sub hs3
  have hT2a : MemLp (fun x => vecDot (u.grad x) (B x)) 2 (volume.restrict (openCubeSet Q)) :=
    r3c_memLp_vecDot hUm hugL hBm (fun x _ i => hMB x i)
  have hT2b : MemLp (fun x => u.toFun x * r3c_div B x) 2 (volume.restrict (openCubeSet Q)) := by
    simpa [mul_comm] using r3c_memLp_mul_bdd_on hUm hDBm (fun x _ => hMD x) huL
  have hT2 : MemLp (fun x => vecDot (u.grad x) (B x) + u.toFun x * r3c_div B x) 2
      (volume.restrict (openCubeSet Q)) := hT2a.add hT2b
  have iS : Integrable (fun x => (χ x * f x + vecDot (g x) (p12_grad χ x) -
      vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) * ψ.toH1Function.toFun x)
      (volume.restrict (openCubeSet Q)) := hSL.integrable_mul hψL
  have iT1 : Integrable (fun x => r3c_div B1 x * ψ.toH1Function.toFun x)
      (volume.restrict (openCubeSet Q)) := hDB1.integrable_mul hψL
  have iT2 : Integrable (fun x => (vecDot (u.grad x) (B x) + u.toFun x * r3c_div B x) *
      ψ.toH1Function.toFun x) (volume.restrict (openCubeSet Q)) := hT2.integrable_mul hψL
  -- the integration by parts identities
  have hconv := r3c_isOpenBoundedConvex_cube Q
  let v1 : H1Function (openCubeSet Q) := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hconv
    (f := fun _ => (1 : ℝ)) contDiff_const
  have hv1f : ∀ x, v1.toFun x = 1 := fun x => rfl
  have hv1g : ∀ x, v1.grad x = 0 := fun x => by
    funext i
    show fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x (basisVec i) = 0
    simp
  have hI1 := r3c_integral_mul_vec_h10 hUo v1 hB1s hB1c ψ
  simp only [hv1f, hv1g, one_smul, vecDot_zero_left, one_mul, zero_add] at hI1
  have hI2 := r3c_integral_mul_vec_h10 hUo u hBs hBc ψ
  have hsplit : ∫ x in (openCubeSet Q), vecDot (χ x • g x + u.toFun x • matVecMul (A x) (p12_grad χ x))
      (ψ.toH1Function.grad x) = (∫ x in (openCubeSet Q), vecDot (B1 x) (ψ.toH1Function.grad x)) +
        ∫ x in (openCubeSet Q), vecDot (u.toFun x • B x) (ψ.toH1Function.grad x) := by
    rw [← integral_add int1 int2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact p12_vecDot_add_left _ _ _
  have hFeq : (fun x => r3c_cutoffData A χ f g u x * ψ.toH1Function.toFun x) = fun x =>
      ((χ x * f x + vecDot (g x) (p12_grad χ x) - vecDot (matVecMul (A x) (u.grad x))
        (p12_grad χ x)) * ψ.toH1Function.toFun x - r3c_div B1 x * ψ.toH1Function.toFun x) -
      (vecDot (u.grad x) (B x) + u.toFun x * r3c_div B x) * ψ.toH1Function.toFun x := by
    funext x
    simp only [r3c_cutoffData, hB1def, hBdef]
    ring
  rw [hloc, hsplit, hI1, hI2]
  simp only [vecDot_zero_left, integral_zero, add_zero]
  have iA : Integrable (fun x => (χ x * f x + vecDot (g x) (p12_grad χ x) -
      vecDot (matVecMul (A x) (u.grad x)) (p12_grad χ x)) * ψ.toH1Function.toFun x -
      r3c_div B1 x * ψ.toH1Function.toFun x) (volume.restrict (openCubeSet Q)) := iS.sub iT1
  rw [hFeq, integral_sub iA iT2, integral_sub iS iT1]
  ring

end SuperdiffusionCLT.Section7
