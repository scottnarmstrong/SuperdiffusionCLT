/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2
public import SuperdiffusionCLT.Section8.Prereq.InteriorW2pD
public import SuperdiffusionCLT.Section7.Analytic.Regularity.HolderGradientB

/-!
# From an `L^P` weak Hessian to a classical `C¹` function

On the origin cube of scale `3^m`, a continuous `H¹` solution `z` of `-Δ z = h` with `h`, `∇z`,
`z` in `L^P` (`P > d`) is `C¹` on the open box `|xᵢ| < 3^m/4`, with a continuous gradient
having weak derivatives in `L^P` there.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- Weak partial derivatives are invariant under almost-everywhere changes on the set. -/
theorem intC2_weak_congr {V : Set (Vec d)} {i : Fin d} {f f' g g' : Vec d → ℝ}
    (hf : f =ᵐ[volume.restrict V] f') (hg : g =ᵐ[volume.restrict V] g')
    (h : HasWeakPartialDerivOn V i f g) : HasWeakPartialDerivOn V i f' g' := by
  intro φ hφ hc hs
  have h1 := h φ hφ hc hs
  have e1 : ∫ x in V, f' x * fderiv ℝ φ x (basisVec i) = ∫ x in V, f x * fderiv ℝ φ x (basisVec i) :=
    integral_congr_ae (hf.mono fun x hx ↦ by simp only [hx])
  have e2 : ∫ x in V, g' x * φ x = ∫ x in V, g x * φ x :=
    integral_congr_ae (hg.mono fun x hx ↦ by simp only [hx])
  rw [e1, e2, h1]

/-- The open box `|xᵢ| < r`. -/
def intC2_box (d : ℕ) (r : ℝ) : Set (Vec d) := {x | ∀ i, |x i| < r}

theorem intC2_isOpen_box (r : ℝ) : IsOpen (intC2_box d r) := by
  have : intC2_box d r = ⋂ i, {x : Vec d | |x i| < r} := by
    ext x; simp [intC2_box]
  rw [this]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const

theorem intC2_box_subset {r s : ℝ} (h : r ≤ s) : intC2_box d r ⊆ intC2_box d s :=
  fun _ hx i ↦ (hx i).trans_le h

theorem intC2_box_subset_cube (m : ℤ) : intC2_box d ((3 : ℝ) ^ m / 4) ⊆
    openCubeSet (originCube d m) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h := abs_lt.1 (hx i)
  have hp : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  constructor <;> linarith only [h.1, h.2, hp]

/-- **Core to `C¹`.**  See the module docstring. -/
theorem intC2_core_c1 [NeZero d] (hd : 2 ≤ d) (m : ℤ) {P : ℝ} (hP : (d : ℝ) < P)
    {z : H1Function (openCubeSet (originCube d m))} {h : Vec d → ℝ}
    (hz : SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d))
      (openCubeSet (originCube d m)) z h (fun _ ↦ 0))
    (hh : MemLp h (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d m)))
    (hgz : ∀ i, MemLp (fun x ↦ z.grad x i) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d m)))
    (hzz : MemLp z.toFun (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d m)))
    (hcont : ContinuousOn z.toFun (openCubeSet (originCube d m))) :
    ∃ (G : Fin d → Vec d → ℝ) (Hs : Fin d → Fin d → Vec d → ℝ),
      (∀ i, ContinuousOn (G i) (intC2_box d ((3 : ℝ) ^ m / 4))) ∧
      (∀ x ∈ intC2_box d ((3 : ℝ) ^ m / 4), HasFDerivAt z.toFun (intC2_cand G x) x) ∧
      (∀ i, (G i) =ᵐ[volume.restrict (intC2_box d ((3 : ℝ) ^ m / 4))] fun x ↦ z.grad x i) ∧
      (∀ i j, HasWeakPartialDerivOn (intC2_box d ((3 : ℝ) ^ m / 4)) j (G i) (Hs i j)) ∧
      (∀ i j, MemLp (Hs i j) (ENNReal.ofReal P)
        (volume.restrict (intC2_box d ((3 : ℝ) ^ m / 4)))) := by
  obtain ⟨χ, w, H, hχ, hc, hsub, hone, hwf, hwg, hHp⟩ := intW2p_core hd m hP hz hh hgz hzz
  obtain ⟨g, hgc, hgae, -⟩ := SuperdiffusionCLT.Section7.holderGradient_of_weakHessian
    (originCube d m) hP H hHp
  set B := intC2_box d ((3 : ℝ) ^ m / 4) with hB
  have hBo : IsOpen B := intC2_isOpen_box _
  have hBU : B ⊆ openCubeSet (originCube d m) := intC2_box_subset_cube m
  have hBr : volume.restrict B ≤ volume.restrict (openCubeSet (originCube d m)) :=
    Measure.restrict_mono_set volume hBU
  have hχ1 : ∀ x ∈ B, χ x = 1 := fun x hx ↦ hone x fun i ↦ (hx i).le
  have hdχ : ∀ x ∈ B, fderiv ℝ χ x = 0 := fun x hx ↦ by
    have : χ =ᶠ[𝓝 x] fun _ ↦ 1 := Filter.eventually_of_mem (hBo.mem_nhds hx) hχ1
    rw [this.fderiv_eq]
    simp
  have hwz : ∀ x ∈ B, w.toH1Function.toFun x = z.toFun x := fun x hx ↦ by
    rw [hwf x, hχ1 x hx, one_mul]
  have hwgz : ∀ x ∈ B, ∀ i, w.toH1Function.grad x i = z.grad x i := fun x hx i ↦ by
    rw [hwg x, hχ1 x hx, hdχ x hx]
    simp
  have hae : ∀ i, (fun x ↦ g x i) =ᵐ[volume.restrict B] fun x ↦ z.grad x i := fun i ↦ by
    have h1 : (fun x ↦ g x i) =ᵐ[volume.restrict B] fun x ↦ w.toH1Function.grad x i :=
      (hgae i).filter_mono (ae_mono hBr)
    refine h1.trans ?_
    filter_upwards [ae_restrict_mem hBo.measurableSet] with x hx using hwgz x hx i
  have hwB : ∀ i, HasWeakPartialDerivOn B i w.toH1Function.toFun
      (fun x ↦ w.toH1Function.grad x i) := fun i ↦
    (w.toH1Function.hasWeakGradient i).restrict hBo hBU
  have hGc : ∀ i, ContinuousOn (fun x ↦ g x i) B := fun i ↦
    ((continuous_apply i).comp_continuousOn hgc).mono hBU
  have hmemB : ∀ᵐ x ∂(volume.restrict B), x ∈ B := ae_restrict_mem hBo.measurableSet
  have hmemB : ∀ᵐ x ∂(volume.restrict B), x ∈ B := ae_restrict_mem hBo.measurableSet
  have hweakz : ∀ i, HasWeakPartialDerivOn B i z.toFun (fun x ↦ g x i) := fun i ↦
    intC2_weak_congr (hmemB.mono fun x hx ↦ hwz x hx) ((hgae i).filter_mono (ae_mono hBr)).symm (hwB i)
  have hhess : ∀ i j, HasWeakPartialDerivOn B j (fun x ↦ g x i) (H.hess i j) := fun i j ↦
    intC2_weak_congr ((hgae i).filter_mono (ae_mono hBr)).symm (Filter.EventuallyEq.rfl)
      ((H.weak_second i j).restrict hBo hBU)
  have hmat := SuperdiffusionCLT.Section7.holderGradient_memLp_restrict (originCube d m) hHp
  have hent : ∀ i j, MemLp (fun x ↦ H.hess i j x) (ENNReal.ofReal P)
      (volume.restrict B) := fun i j ↦
    ((hmat.of_le (H.hess_memL2 i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using
          SuperdiffusionCLT.Section7.holderGradient_abs_entry_le (fun a b ↦ H.hess a b x) i j)
      ).mono_measure hBr)
  exact ⟨fun i x ↦ g x i, H.hess, hGc, fun x hx ↦ intC2_hasFDerivAt_of_weak_local hBo
    (hcont.mono hBU) hGc hweakz hx, hae, hhess, hent⟩

end SuperdiffusionCLT.Section8
