/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.LocalizeSwitch
public import SuperdiffusionCLT.Section5.Response.ResponseData
public import SuperdiffusionCLT.Section5.Localization.SubcubeAvg
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Analytic
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneB

/-!
# The Neumann input: the deterministic part

For the Neumann input of `lem.neumann.input` the block vector
`bfAhom^{1/2} G_{-hbar_z} bfAhom^{-1/2} (e', (grad w_N + shom^{-1} hshell e')_{z+cu_n})` equals
`(e', (grad w_N)_{z+cu_n})` (`neumannVector_eq`), so that its squared norm is
`1 + |(grad w_N)_{z+cu_n}|^2`, and the subcube average of the latter is at most
`1 + ‖grad w_N‖²_{L̲²(cu_K)}` (`subcubeAvg_unit_prod_le`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

/-- `bfAhom_L^{1/2}` applied to a block vector, `bfAhom = diag(shom Id, shom^{-1} Id)`. -/
noncomputable def ahomSqrtApply [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (X : BlockVec d) : BlockVec d :=
  ((sigmaBarInfinite nu L P) ^ ((1 : ℝ) / 2) • X.1,
    (sigmaBarInfinite nu L P) ^ (-(1 : ℝ) / 2) • X.2)

theorem volumeAverageVec_add_of_integrable {s : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : ∀ i : Fin d, Integrable (fun x : Vec d => f x i) (volume.restrict s))
    (hg : ∀ i : Fin d, Integrable (fun x : Vec d => g x i) (volume.restrict s)) :
    volumeAverageVec s (fun x => f x + g x) = volumeAverageVec s f + volumeAverageVec s g := by
  funext i
  show (volume s).toReal⁻¹ * ∫ x in s, f x i + g x i ∂volume
    = (volume s).toReal⁻¹ * ∫ x in s, f x i ∂volume +
      (volume s).toReal⁻¹ * ∫ x in s, g x i ∂volume
  rw [integral_add (hf i) (hg i)]
  ring

theorem volumeAverageVec_const_smul_of (U : Set (Vec d)) (c : ℝ) (f : Vec d → Vec d) :
    volumeAverageVec U (fun x => c • f x) = c • volumeAverageVec U f := by
  funext i
  simp only [volumeAverageVec, Pi.smul_apply, smul_eq_mul]
  rw [SuperdiffusionCLT.Section2.Norms.volumeAverage_const_mul]

/-- The cube average of the shell flux is `shom^{-1} hbar_z e`. -/
theorem volumeAverageVec_hshellFlux [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (Q : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e : Vec d) :
    volumeAverageVec (cubeSet Q) (hshellFlux nu P m h omega e) =
      (sigmaBarInfinite nu (m - h) P)⁻¹ • matVecMul (principalGauge m h Q omega) e := by
  have hM : Continuous (fun x : Vec d =>
      SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
        SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x) :=
    (SuperdiffusionCLT.Section2.Cutoff.continuous_streamCutoff_apply omega m).sub
      (SuperdiffusionCLT.Section2.Cutoff.continuous_streamCutoff_apply omega (m - h))
  have h1 : hshellFlux nu P m h omega e = fun x =>
      (sigmaBarInfinite nu (m - h) P)⁻¹ • matVecMul
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x) e := rfl
  rw [h1, volumeAverageVec_const_smul_of,
    SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageVec_matVecMul Q hM,
    principalGauge_eq_average]

theorem matVecMul_zero_left (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

theorem matVecMul_neg_left (A : Mat d) (x : Vec d) : matVecMul (-A) x = -matVecMul A x := by
  funext i
  simp [matVecMul, Finset.sum_neg_distrib]

/-- The gauge, the two conjugations and the shell flux: the block vector of the Neumann input is
`(e', (grad w_N)_{Q})`. -/
theorem neumannVector_eq [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (Q : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e' : Vec d) (g : Vec d → Vec d)
    (hs : 0 < sigmaBarInfinite nu (m - h) P)
    (hg : ∀ i : Fin d, Integrable (fun x : Vec d => g x i) (volume.restrict (cubeSet Q))) :
    ahomSqrtApply nu (m - h) P
        (blockMatVecMul (gaugeMat (-principalGauge m h Q omega))
          (ahomInvSqrtApply nu (m - h) P
            (e', volumeAverageVec (cubeSet Q)
              (fun y => g y + hshellFlux nu P m h omega e' y)))) =
      (e', volumeAverageVec (cubeSet Q) g) := by
  have hfl : ∀ i : Fin d, Integrable (fun x : Vec d => hshellFlux nu P m h omega e' x i)
      (volume.restrict (cubeSet Q)) := by
    intro i
    rw [responseData_hshellFlux_eq_dirichletRhsField]
    exact SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_cubeSet_of_continuous Q
      ((continuous_apply i).comp
      (SuperdiffusionCLT.Section3.Setup.continuous_dirichletRhsField _ _ _ _))
  rw [volumeAverageVec_add_of_integrable hg hfl, volumeAverageVec_hshellFlux]
  set s := sigmaBarInfinite nu (m - h) P with hsdef
  set a := volumeAverageVec (cubeSet Q) g with hadef
  set u := matVecMul (principalGauge m h Q omega) e' with hudef
  have hrt : s ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hs]
    norm_num
  have hrs : s ^ ((1 : ℝ) / 2) * s⁻¹ = s ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hs]
    norm_num
  have hu : ∀ c : ℝ, matVecMul (principalGauge m h Q omega) (c • e') = c • u := fun c =>
    matVecMul_smul _ _ _
  apply Prod.ext
  · funext i
    simp only [ahomSqrtApply, ahomInvSqrtApply, blockMatVecMul, gaugeMat, matVecMul_one,
      matVecMul_zero_left, Pi.smul_apply, smul_eq_mul, add_zero]
    linear_combination (e' i) * hrt
  · funext i
    simp only [ahomSqrtApply, ahomInvSqrtApply, blockMatVecMul, gaugeMat, matVecMul_one,
      matVecMul_neg_left, hu, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (a i) * hrt + (s ^ (-(1 : ℝ) / 2) * u i) * hrs

theorem ofReal_descendantsAverage {Q : TriadicCube d} {j : ℕ} {F : TriadicCube d → ℝ}
    (hF : ∀ R, 0 ≤ F R) :
    ENNReal.ofReal (descendantsAverage Q j F) =
      ((descendantsAtDepth Q j).card : ENNReal)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (F R) := by
  have hc : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    rw [descendantsAtDepth_card]
    positivity
  have h1 : descendantsAverage Q j F =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, F R := rfl
  rw [h1, ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ENNReal.ofReal_inv_of_pos hc,
    ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun R _ => hF R]

theorem descendantsAverage_one_add {Q : TriadicCube d} {j : ℕ} (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => 1 + F R) = 1 + descendantsAverage Q j F := by
  have hc : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    rw [descendantsAtDepth_card]
    positivity
  have h1 : ∀ G : TriadicCube d → ℝ, descendantsAverage Q j G =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, G R := fun _ => rfl
  rw [h1, h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, mul_add,
    inv_mul_cancel₀ hc.ne']

/-- **Jensen over the subcubes.** For an `L²` field `g` on `cu_Kc` and a unit vector `e'`, the
subcube average of `|(e', (g)_{z+cu_n})|^2` is at most `1 + ‖g‖²_{L̲²(cu_Kc)}`. -/
theorem subcubeAvg_unit_prod_le {Kc n : ℕ} (hn : n ≤ Kc) (e' : Vec d) (he : vecNormSq e' = 1)
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) g) :
    subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (blockVecDot (e', volumeAverageVec (cubeSet Q) g) (e', volumeAverageVec (cubeSet Q) g))) ≤
      ENNReal.ofReal (1 + SuperdiffusionCLT.Section2.Estimates.Stream.vecSqAvg
        (originCube d (Kc : ℤ)) g) := by
  have hdesc : descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ) =
      descendantsAtDepth (originCube d (Kc : ℤ)) (Kc - n) := by
    have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
      show (n : ℤ) ≤ (Kc : ℤ)
      exact_mod_cast hn
    rw [descendantsAtScale_eq_descendantsAtDepth _ hk]
    congr 1
    show Int.toNat ((Kc : ℤ) - (n : ℤ)) = Kc - n
    omega
  have hform : ∀ Q : TriadicCube d,
      blockVecDot (e', volumeAverageVec (cubeSet Q) g) (e', volumeAverageVec (cubeSet Q) g) =
        1 + vecNormSq (volumeAverageVec (cubeSet Q) g) := by
    intro Q
    show vecNormSq e' + vecNormSq (volumeAverageVec (cubeSet Q) g) = _
    rw [he]
  simp only [hform]
  unfold subcubeAvg
  rw [hdesc, ← ofReal_descendantsAverage
    (fun R => by have := vecNormSq_nonneg (volumeAverageVec (cubeSet R) g); linarith only [this]),
    descendantsAverage_one_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have := SuperdiffusionCLT.Section3.Terms.vecDepthSqMoment_le_vecSqAvg_of_memVectorL2
    (originCube d (Kc : ℤ)) (Kc - n) hg
  unfold SuperdiffusionCLT.Section2.Estimates.Stream.vecDepthSqMoment at this
  linarith only [this]

end SuperdiffusionCLT.Section5
