/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2F

/-!
# Stage 2: `∂ₖu` is `C¹`

`v = ∂ₖu = Gₖ` is a continuous `H¹` function on the cube of scale `3^(m-2)` solving
`-Δ v = hv` with `hv ∈ L^P`; the Hessian estimate of `InteriorC2B` applies to it.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_bound_vec {K : Set (Vec d)} (hK : IsCompact K) {F : Fin d → Vec d → ℝ}
    (hF : ∀ i, ContinuousOn (F i) K) : ∃ M, ∀ x ∈ K, ∀ i, |F i x| ≤ M := by
  choose M hM using fun i ↦ hK.exists_bound_of_continuousOn (hF i)
  refine ⟨∑ i, |M i|, fun x hx i ↦ ?_⟩
  have h1 : |F i x| ≤ M i := by simpa only [Real.norm_eq_abs] using hM i x hx
  exact h1.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i ↦ |M i|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)))

theorem intC2_closure_cube_sub (m : ℤ) : closure (openCubeSet (originCube d (m - 1))) ⊆
    intC2_box d ((3 : ℝ) ^ m / 4) := by
  have hcl : IsClosed {x : Vec d | ∀ i, |x i| ≤ (3 : ℝ) ^ (m - 1) / 2} := by
    have : {x : Vec d | ∀ i, |x i| ≤ (3 : ℝ) ^ (m - 1) / 2} =
        ⋂ i, {x : Vec d | |x i| ≤ (3 : ℝ) ^ (m - 1) / 2} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
  have hsub : openCubeSet (originCube d (m - 1)) ⊆
      {x : Vec d | ∀ i, |x i| ≤ (3 : ℝ) ^ (m - 1) / 2} := by
    intro x hx i
    rw [mem_openCubeSet_originCube_iff] at hx
    have h := hx i
    rw [abs_le]
    constructor <;> linarith only [h.1, h.2]
  refine (closure_minimal hsub hcl).trans fun x hx i ↦ ?_
  have h := hx i
  have e : (3 : ℝ) ^ (m - 1) = 3 ^ m / 3 := by rw [zpow_sub_one₀ (by norm_num)]; ring
  have hp : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [e] at h
  linarith only [h, hp]

theorem intC2_isFinite_box (m : ℤ) : IsFiniteMeasure (volume.restrict (intC2_box d ((3 : ℝ) ^ m / 4))) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact ((isBounded_openCubeSet (originCube d m)).subset (intC2_box_subset_cube m)).measure_lt_top⟩

/-- `Gₖ` as an `H¹` function on the cube of scale `3^(m-1)`, with gradient `(Hs k j)ⱼ`. -/
theorem intC2_vH1 (m : ℤ) {G : Fin d → Vec d → ℝ} {Hs : Fin d → Fin d → Vec d → ℝ}
    (hGc : ∀ i, ContinuousOn (G i) (intC2_box d ((3 : ℝ) ^ m / 4)))
    (hHs : ∀ i j, HasWeakPartialDerivOn (intC2_box d ((3 : ℝ) ^ m / 4)) j (G i) (Hs i j))
    (hHs2 : ∀ i j, MemLp (Hs i j) 2 (volume.restrict (intC2_box d ((3 : ℝ) ^ m / 4)))) (k : Fin d) :
    ∃ v : H1Function (openCubeSet (originCube d (m - 1))),
      v.toFun = G k ∧ ∀ x j, v.grad x j = Hs k j x := by
  have hU2 : IsOpen (openCubeSet (originCube d (m - 1))) := isOpen_openCubeSet _
  have hsub : openCubeSet (originCube d (m - 1)) ⊆ intC2_box d ((3 : ℝ) ^ m / 4) :=
    intC2_box_quarter_sub m
  have hK : IsCompact (closure (openCubeSet (originCube d (m - 1)))) :=
    (isBounded_openCubeSet _).isCompact_closure
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hGc k).mono (intC2_closure_cube_sub m))
  refine ⟨{ toFun := G k
            grad := fun x j ↦ Hs k j x
            memL2 := ?_
            gradMemL2 := fun j ↦ (hHs2 k j).mono_measure (Measure.restrict_mono hsub le_rfl)
            hasWeakGradient := fun j ↦ (hHs k j).restrict hU2 hsub }, rfl, fun _ _ ↦ rfl⟩
  exact intC2_memLp_bdd (isBounded_openCubeSet _) hU2.measurableSet
    (((hGc k).mono hsub).aestronglyMeasurable hU2.measurableSet) (M := M) (fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using hM x (subset_closure hx)) 2

/-- The right-hand side of the equation for `∂ₖu`. -/
noncomputable def intC2_rhs (a : CoeffField d) (nu mu : ℝ) (g : Vec d → ℝ)
    (G : Fin d → Vec d → ℝ) (Hs : Fin d → Fin d → Vec d → ℝ) (k : Fin d) (x : Vec d) : ℝ :=
  (fderiv ℝ g x (basisVec k) - mu * G k x -
    ∑ i, (intW2p_drift a x i * Hs k i x +
      fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)) / nu

theorem intC2_rhs_memLp (m : ℤ) {P : ℝ} {a : CoeffField d} {nu mu : ℝ}
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    {G : Fin d → Vec d → ℝ} {Hs : Fin d → Fin d → Vec d → ℝ}
    (hGc : ∀ i, ContinuousOn (G i) (intC2_box d ((3 : ℝ) ^ m / 4)))
    (hHsL : ∀ i j, MemLp (Hs i j) (ENNReal.ofReal P)
      (volume.restrict (intC2_box d ((3 : ℝ) ^ m / 4)))) (k : Fin d) :
    MemLp (intC2_rhs a nu mu g G Hs k) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d (m - 1))) := by
  have hU2 : IsOpen (openCubeSet (originCube d (m - 1))) := isOpen_openCubeSet _
  have hb2 : Bornology.IsBounded (openCubeSet (originCube d (m - 1))) := isBounded_openCubeSet _
  have hsub : openCubeSet (originCube d (m - 1)) ⊆ intC2_box d ((3 : ℝ) ^ m / 4) :=
    intC2_box_quarter_sub m
  have hK : IsCompact (closure (openCubeSet (originCube d (m - 1)))) := hb2.isCompact_closure
  obtain ⟨M, hM⟩ := intC2_bound_vec hK fun i ↦ (hGc i).mono (intC2_closure_cube_sub m)
  have hGp : ∀ i, MemLp (G i) (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d (m - 1))) :=
    fun i ↦ intC2_memLp_cubeBdd (((hGc i).mono hsub).aestronglyMeasurable hU2.measurableSet)
      (M := M) (fun x hx ↦ hM x (subset_closure hx) i) _
  obtain ⟨Mg, hMg⟩ := intC2_bound_on hb2 ((hg.continuous_fderiv one_ne_zero).clm_apply
    (continuous_const (y := basisVec k)))
  obtain ⟨Mc, hMc0, hMc⟩ := intC2_drift_norm_bound ha hb2
  have t1 : MemLp (fun x ↦ fderiv ℝ g x (basisVec k)) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d (m - 1))) :=
    intC2_memLp_cubeBdd (((hg.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := basisVec k))).aestronglyMeasurable) hMg _
  have t3 : ∀ i, MemLp (fun x ↦ intW2p_drift a x i * Hs k i x) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d (m - 1))) := fun i ↦
    intC2_memLp_mul_bdd_cube (b := fun x ↦ intW2p_drift a x i)
      (intW2p_drift_contDiff ha i).continuous.aestronglyMeasurable (M := Mc) (fun x hx ↦ by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (intW2p_drift a x) i).trans
          (hMc x hx)) (intC2_memLp_cube_of_restrict hsub (hHsL k i))
  have t4 : ∀ i, MemLp (fun x ↦ fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)
      (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d (m - 1))) := fun i ↦ by
    obtain ⟨Md, hMd⟩ := intC2_bound_on hb2 (intC2_drift_d1_cont ha i k)
    exact intC2_memLp_mul_bdd_cube (b := fun x ↦ fderiv ℝ (fun y ↦ intW2p_drift a y i) x
      (basisVec k)) (intC2_drift_d1_cont ha i k).aestronglyMeasurable hMd (hGp i)
  have hsum : MemLp (fun x ↦ ∑ i, (intW2p_drift a x i * Hs k i x +
      fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x)) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d (m - 1))) := by
    have ti : ∀ i, MemLp (fun x ↦ intW2p_drift a x i * Hs k i x +
        fderiv ℝ (fun y ↦ intW2p_drift a y i) x (basisVec k) * G i x) (ENNReal.ofReal P)
        (normalizedCubeMeasure (originCube d (m - 1))) := fun i ↦ (t3 i).add (t4 i)
    exact memLp_finsetSum _ fun i _ ↦ ti i
  have := ((t1.sub ((hGp k).const_mul mu)).sub hsum).const_mul (1 / nu)
  refine this.ae_eq (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [intC2_rhs, Pi.sub_apply]
  ring

end SuperdiffusionCLT.Section8
