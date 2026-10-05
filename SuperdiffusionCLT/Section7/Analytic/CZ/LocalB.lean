/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.Cutoff.Box
public import Homogenization.Sobolev.H1.LocalizedZeroTrace
public import Homogenization.Sobolev.H1.Translation
public import SuperdiffusionCLT.Section5.Carriers.BlockOffsetMinimizerB
public import SuperdiffusionCLT.Section7.Analytic.CZ.CubePerturb
public import SuperdiffusionCLT.Section7.Analytic.CZ.CubeScalarDataB
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Analytic.CZ.Local

/-!
# Local `W^{1,p}` estimates: scalar and vector data, and the normalized Sobolev embedding

* `p12_czSV`: a zero-trace weak solution on a triadic cube of `-∇·(A∇w) = s - ∇·G`, with `A`
  entrywise `ε`-close to `Id`, has `∇w ∈ L̲^a` when `s ∈ L̲² ∩ L̲^c`, `G ∈ L̲² ∩ L̲^a`,
  `c⁻¹ = a⁻¹ + d⁻¹`, with `‖∇w‖ ≤ C (3^m ‖s‖_{L̲^c} + ‖G‖_{L̲^a})`.
* `p12_sobolev`: the normalized Sobolev embedding on a triadic cube for `H¹` functions.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}


theorem p12c_center_mem [NeZero d] (Q : TriadicCube d) :
    (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) ∈ openCubeSet Q := by
  intro i
  have h : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  constructor <;> nlinarith only [h]

theorem p12c_exists_poisson [NeZero d] (Q : TriadicCube d) {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    ∃ ψ : H10Function (openCubeSet Q), CubeDirichletWeakPoissonProblem Q ψ F := by
  have hF' : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using memLp_restrict_of_normalized Q hF
  have hg : MemVectorL2 (openCubeSet Q) (fun _ : Vec d => (0 : Vec d)) := by
    simp [MemVectorL2, volumeMeasureOn]
  have hne : (openCubeSet Q).Nonempty := ⟨_, p12c_center_mem Q⟩
  obtain ⟨ψ, hψ⟩ := exists_h10_weak_solution (isOpen_openCubeSet Q) (isBoundedDomain_openCubeSet Q)
    hne (Section5.isEllipticFieldOn_one (measurableSet_openCubeSet Q)) hF' hg
  refine ⟨ψ, fun φ => ?_⟩
  have := hψ φ
  simpa [matVecMul_one_left, vecDot_zero_left] using this

theorem p12c_le_of_toReal {X Y : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (hX : X ≠ ⊤) (hY : Y ≠ ⊤)
    (h : X.toReal ≤ c * Y.toReal) : X ≤ ENNReal.ofReal c * Y := by
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hY, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h

theorem p12c_integrable_matVec [NeZero d] (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {F : Vec d → Vec d} (hF : MemLp F 2 (normalizedCubeMeasure Q)) (φ : H10Function (openCubeSet Q)) :
    Integrable (fun x => vecDot (matVecMul (A x) (F x)) (φ.toH1Function.grad x))
      (volume.restrict (openCubeSet Q)) := by
  have hφ := memLp_two_grad Q φ
  have hP := (memLp_pert_and_norm_le Q hA hε0 hε hF).1
  have h := (integrable_vecDot_of_memLp Q hF hφ).add (integrable_vecDot_of_memLp Q hP hφ)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  rw [matVecMul_eq_add_pert (A x), vecDot_add_left]
  rfl

theorem p12_czSV [NeZero d] (hd : 2 ≤ d) {a c : ℝ} (hc : 1 < c) (ha : 1 < a)
    (hca : c⁻¹ = a⁻¹ + (d : ℝ)⁻¹) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (Q : TriadicCube d) (A : CoeffField d),
      (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
      (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
      ∀ (s : Vec d → ℝ) (G : Vec d → Vec d),
        MemLp s 2 (normalizedCubeMeasure Q) → MemLp s (ENNReal.ofReal c) (normalizedCubeMeasure Q) →
        MemLp G 2 (normalizedCubeMeasure Q) → MemLp G (ENNReal.ofReal a) (normalizedCubeMeasure Q) →
        ∀ w : H10Function (openCubeSet Q),
          IsWeakSolutionOn A (openCubeSet Q) w.toH1Function s G →
          MemLp w.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) ∧
            Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) w.toH1Function.grad ≤
              ENNReal.ofReal C * (ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal c) s +
                Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) G) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  have hapos : 0 < a := by linarith only [ha]
  obtain ⟨ε, Cp, hε, hCp, hCZ⟩ := cubePerturbativeCZ (d := d)
    (p := ENNReal.ofReal a) (by simpa using ha) ENNReal.ofReal_lt_top
  have hr : (mkExp c hc).exponent.toReal < d := by
    rw [mkExp_toReal]
    have h1 : c⁻¹ - a⁻¹ = (d : ℝ)⁻¹ := by linarith only [hca]
    have h2 : 0 < a⁻¹ := inv_pos.2 hapos
    have h3 : (d : ℝ)⁻¹ < c⁻¹ := by linarith only [h1, h2]
    have hc0 : 0 < c := by linarith only [hc]
    exact (inv_lt_inv₀ hdpos hc0).1 h3
  have hq : ((mkExp a ha).exponent.toReal)⁻¹ = (mkExp c hc).exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    rw [mkExp_toReal, mkExp_toReal]; linarith only [hca]
  obtain ⟨C1, hC1, hC1b⟩ := exists_cubeScalarData_gradVecLp_sobolev_triadic hd (mkExp c hc)
    (mkExp a ha) hr hq
  have hK0 : 0 ≤ C1.toReal := ENNReal.toReal_nonneg
  have hdε : 0 ≤ (d : ℝ) * ε := by positivity
  refine ⟨ε, Cp + (Cp * (d * ε) + 1) * C1.toReal + 1, hε, by positivity, ?_⟩
  intro Q A hA hAε s G hs2 hsc hG2 hGa w hw
  have hA' := hA
  obtain ⟨u, hu⟩ := p12c_exists_poisson Q hs2
  obtain ⟨hua, hub⟩ := hC1b Q s hs2 hsc u hu
  have hua' : MemLp u.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) := hua
  have hu2 := memLp_two_grad Q u
  have hw2 := memLp_two_grad Q w
  obtain ⟨hPa, hPn⟩ := memLp_pert_and_norm_le Q hA hε.le hAε hua'
  have hP2 := (memLp_pert_and_norm_le Q hA hε.le hAε hu2).1
  set P := pert A u.toH1Function.grad with hPdef
  have hG2' : MemLp (fun x => -(G x - P x)) 2 (normalizedCubeMeasure Q) := (hG2.sub hP2).neg
  have hGa' : MemLp (fun x => -(G x - P x)) (ENNReal.ofReal a) (normalizedCubeMeasure Q) :=
    (hGa.sub hPa).neg
  have heq : IsZeroTraceDirichletRhsWeakSolution A (openCubeSet Q) (w - u)
      (fun x => -(fun x => -(G x - P x)) x) := by
    intro φ
    have hφ := memLp_two_grad Q φ
    have i1 := p12c_integrable_matVec Q hA hε.le hAε hw2 φ
    have i2 := p12c_integrable_matVec Q hA hε.le hAε hu2 φ
    have i3 := integrable_vecDot_of_memLp Q hu2 hφ
    have i4 := integrable_vecDot_of_memLp Q hP2 hφ
    have i5 := integrable_vecDot_of_memLp Q hG2 hφ
    have e1 : ∀ x, vecDot (matVecMul (A x) ((w - u).toH1Function.grad x)) (φ.toH1Function.grad x) =
        vecDot (matVecMul (A x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) -
        vecDot (matVecMul (A x) (u.toH1Function.grad x)) (φ.toH1Function.grad x) := by
      intro x
      rw [grad_sub, matVecMul_sub_right, vecDot_sub_left']
    simp only [e1]
    rw [integral_sub i1 i2]
    have e2 : ∀ x, vecDot (matVecMul (A x) (u.toH1Function.grad x)) (φ.toH1Function.grad x) =
        vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x) +
        vecDot (P x) (φ.toH1Function.grad x) := by
      intro x
      rw [matVecMul_eq_add_pert (A x), vecDot_add_left]; rfl
    simp only [e2]
    rw [integral_add i3 i4]
    have e3 : ∀ x, vecDot (-(-(G x - P x))) (φ.toH1Function.grad x) =
        vecDot (G x) (φ.toH1Function.grad x) - vecDot (P x) (φ.toH1Function.grad x) := by
      intro x
      rw [neg_neg, vecDot_sub_left']
    simp only [e3]
    rw [integral_sub i5 i4]
    have h1 := hw φ
    have h2 := hu φ
    linarith only [h1, h2]
  obtain ⟨hm2, hn2⟩ := hCZ Q A hA hAε _ hG2' (by simpa using hGa') (w - u) heq
  have hgrad : w.toH1Function.grad =
      fun x => (w - u).toH1Function.grad x + u.toH1Function.grad x := by
    funext x; rw [grad_sub]; simp
  have hmem : MemLp w.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) := by
    rw [hgrad]; exact hm2.add hua'
  refine ⟨hmem, ?_⟩
  -- norm bookkeeping
  have ha1 : 1 ≤ ENNReal.ofReal a := by simpa using ha.le
  have hfin_u := hua'.eLpNorm_lt_top.ne
  have hfin_G := hGa.eLpNorm_lt_top.ne
  have hfin_P := hPa.eLpNorm_lt_top.ne
  have hfin_2 := hm2.eLpNorm_lt_top.ne
  -- ∇u bound
  have hubn : Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) u.toH1Function.grad ≤
      ENNReal.ofReal C1.toReal * (ENNReal.ofReal (cubeScaleFactor Q) *
        Section2.Norms.cubeLpENorm Q (ENNReal.ofReal c) s) := by
    have : Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) u.toH1Function.grad ≤
        C1 * ENNReal.ofReal (cubeScaleFactor Q) *
          Section2.Norms.cubeLpENorm Q (ENNReal.ofReal c) s := by
      simpa [mkExp] using hub
    rw [ENNReal.ofReal_toReal hC1.ne]
    rw [mul_assoc] at this
    exact this
  -- pert bound
  have hPb : eLpNorm P (ENNReal.ofReal a) (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d * ε) * eLpNorm u.toH1Function.grad (ENNReal.ofReal a)
        (normalizedCubeMeasure Q) :=
    p12c_le_of_toReal hdε hfin_P hfin_u hPn
  have hw2b : eLpNorm (w - u).toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal Cp * (eLpNorm G (ENNReal.ofReal a) (normalizedCubeMeasure Q) +
        ENNReal.ofReal (d * ε) * eLpNorm u.toH1Function.grad (ENNReal.ofReal a)
          (normalizedCubeMeasure Q)) := by
    have hX := p12c_le_of_toReal hCp.le hfin_2 (hGa'.eLpNorm_lt_top.ne) hn2
    refine hX.trans (mul_le_mul_right ?_ _)
    have hneg : eLpNorm (fun x => -(G x - P x)) (ENNReal.ofReal a) (normalizedCubeMeasure Q) =
        eLpNorm (fun x => G x - P x) (ENNReal.ofReal a) (normalizedCubeMeasure Q) :=
      eLpNorm_neg (fun x => G x - P x) _ _
    rw [hneg]
    exact (eLpNorm_sub_le ha1).trans
      (add_le_add le_rfl hPb)
  have hsum : eLpNorm w.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) ≤
      eLpNorm (w - u).toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) +
        eLpNorm u.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) := by
    rw [hgrad]
    exact eLpNorm_add_le ha1
  set X := ENNReal.ofReal (cubeScaleFactor Q) * Section2.Norms.cubeLpENorm Q (ENNReal.ofReal c) s
  set Y := eLpNorm G (ENNReal.ofReal a) (normalizedCubeMeasure Q)
  set Eu := eLpNorm u.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q)
  have hEu : Eu ≤ ENNReal.ofReal C1.toReal * X := hubn
  have hCe : ENNReal.ofReal (Cp + (Cp * (d * ε) + 1) * C1.toReal + 1) =
      ENNReal.ofReal Cp + (ENNReal.ofReal Cp * ENNReal.ofReal (d * ε) + 1) *
        ENNReal.ofReal C1.toReal + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hCp.le,
      ENNReal.ofReal_one]
  have hfin : eLpNorm w.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal Cp * Y + (ENNReal.ofReal Cp * ENNReal.ofReal (d * ε) + 1) *
        (ENNReal.ofReal C1.toReal * X) := by
    calc _ ≤ _ := hsum
      _ ≤ ENNReal.ofReal Cp * (Y + ENNReal.ofReal (d * ε) * Eu) + Eu := add_le_add hw2b le_rfl
      _ = ENNReal.ofReal Cp * Y + (ENNReal.ofReal Cp * ENNReal.ofReal (d * ε) + 1) * Eu := by ring
      _ ≤ _ := by gcongr
  show eLpNorm w.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) ≤ _
  rw [hCe]
  calc _ ≤ _ := hfin
    _ ≤ (ENNReal.ofReal Cp + (ENNReal.ofReal Cp * ENNReal.ofReal (d * ε) + 1) *
        ENNReal.ofReal C1.toReal + 1) * Y +
        (ENNReal.ofReal Cp + (ENNReal.ofReal Cp * ENNReal.ofReal (d * ε) + 1) *
        ENNReal.ofReal C1.toReal + 1) * X := by
      refine add_le_add ?_ ?_
      · gcongr; exact le_self_add.trans le_self_add
      · rw [← mul_assoc]; gcongr; exact le_add_self.trans le_self_add
    _ = _ := by rw [← mul_add, add_comm Y X]; rfl

/-- Satisfiability: `A = 1`, `s = 0`, `G = 0`, `w = 0`, `d = 3`, `c = 3/2`, `a = 3`. -/
example : (3 : ℝ)⁻¹ ⁻¹ = 3 ∧ (3 / 2 : ℝ)⁻¹ = (3 : ℝ)⁻¹ + ((3 : ℕ) : ℝ)⁻¹ ∧
    ∀ Q : TriadicCube 3, IsWeakSolutionOn (fun _ => (1 : Mat 3)) (openCubeSet Q)
      (0 : H10Function (openCubeSet Q)).toH1Function (fun _ => 0) (fun _ => 0) ∧
      MemLp (fun _ : Vec 3 => (0 : ℝ)) (ENNReal.ofReal (3 / 2)) (normalizedCubeMeasure Q) ∧
      MemLp (fun _ : Vec 3 => (0 : Vec 3)) (ENNReal.ofReal 3) (normalizedCubeMeasure Q) := by
  refine ⟨by norm_num, by norm_num, fun Q => ⟨?_, by simp, by simp⟩⟩
  intro φ
  have h0 : ∀ x, (0 : H10Function (openCubeSet Q)).toH1Function.grad x = 0 := fun _ => rfl
  simp [vecDot, matVecMul, h0]



theorem p12d_openCubeSet_eq_axisCube (Q : TriadicCube d) :
    openCubeSet Q =
      axisCube (fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        (cubeScaleFactor Q) := by
  have hupper : ∀ j : Fin d,
      ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
        ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro j
    ring
  ext x
  simp only [openCubeSet, axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]
  simp_rw [hupper]

theorem p12d_vol_rpow (Q : TriadicCube d) (hd : 0 < d) {a c : ℝ}
    (hca : c⁻¹ = a⁻¹ + (d : ℝ)⁻¹) :
    Homogenization.cubeVolume Q ^ c⁻¹ =
      Homogenization.cubeVolume Q ^ a⁻¹ * cubeScaleFactor Q := by
  have hL := cubeScaleFactor_pos' Q
  have hV := cubeVolume_pos' Q
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hca, Real.rpow_add hV]
  congr 1
  unfold Homogenization.cubeVolume
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, mul_inv_cancel₀ hd', Real.rpow_one]

/-- D: Sobolev embedding on a triadic cube, normalized. -/
theorem p12_sobolev (hd : 2 ≤ d) {a c : ℝ} (hc : 1 < c) (ha : 1 < a)
    (hca : c⁻¹ = a⁻¹ + (d : ℝ)⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d) (w : H1Function (openCubeSet Q)),
      MemLp w.toFun (ENNReal.ofReal c) (normalizedCubeMeasure Q) →
      MemLp w.grad (ENNReal.ofReal c) (normalizedCubeMeasure Q) →
      MemLp w.toFun (ENNReal.ofReal a) (normalizedCubeMeasure Q) ∧
        Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) w.toFun ≤
          ENNReal.ofReal C * (ENNReal.ofReal (cubeScaleFactor Q) *
              Section2.Norms.cubeLpENorm Q (ENNReal.ofReal c) w.grad +
            Section2.Norms.cubeLpENorm Q (ENNReal.ofReal c) w.toFun) := by
  have hd0 : 0 < d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  have hcd : c < d := by
    have h1 : (d : ℝ)⁻¹ < c⁻¹ := by
      rw [hca]; have : 0 < a⁻¹ := inv_pos.2 (by linarith only [ha])
      linarith only [this]
    exact (inv_lt_inv₀ hdpos (by linarith only [hc])).1 h1 |> fun h => by
      exact h
  have hr : (mkExp c hc).exponent.toReal < d := by rw [mkExp_toReal]; exact hcd
  obtain ⟨Cs, hCs0, hCs⟩ := Homogenization.cubeSobolevEmbedding_finiteLp hd0 (mkExp c hc) hr
  have hq : ((mkExp a ha).exponent.toReal)⁻¹ = (mkExp c hc).exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    rw [mkExp_toReal, mkExp_toReal]; linarith only [hca]
  refine ⟨(Cs : ℝ) * d, by positivity, ?_⟩
  intro Q w hwc hgc
  have hL := cubeScaleFactor_pos' Q
  have hV := cubeVolume_pos' Q
  set L := cubeScaleFactor Q with hLdef
  have hset := p12d_openCubeSet_eq_axisCube Q
  set z : Vec d := fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q with hz
  have hwr := memLp_restrict_of_normalized Q hwc
  have hgr : ∀ i, MemLp (fun x => w.grad x i) (ENNReal.ofReal c)
      (volume.restrict (openCubeSet Q)) := fun i =>
    memLp_restrict_of_normalized Q (((memLp_pi_iff).1 hgc) i)
  let u : W1pFunction (axisCube z L) (mkExp c hc).exponent :=
    ⟨w.toFun, w.grad, by rw [← hset]; exact hwr, fun i => by rw [← hset]; exact hgr i,
      by rw [← hset]; exact w.hasWeakGradient⟩
  have h1 := hCs (mkExp a ha) hq z L hL u
  have hmeas : volumeMeasureOn (axisCube z L) = volume.restrict (openCubeSet Q) := by
    rw [hset]
  rw [hmeas] at h1
  change eLpNorm w.toFun (mkExp a ha).exponent _ ≤ _ at h1
  simp only [mkExp_exponent] at h1
  set V := Homogenization.cubeVolume Q with hVdef
  set M := volume.restrict (openCubeSet Q) with hM
  have hVc := p12d_vol_rpow Q hd0 hca
  rw [← hVdef] at hVc
  have e1 : ∀ f : Vec d → ℝ, ∀ t : ℝ, 1 < t →
      eLpNorm f (ENNReal.ofReal t) M =
        ENNReal.ofReal (V ^ t⁻¹) * eLpNorm f (ENNReal.ofReal t) (normalizedCubeMeasure Q) := by
    intro f t ht
    rw [hM, eLpNorm_restrict_eq, ENNReal.toReal_ofReal (by linarith only [ht])]
  set ka := ENNReal.ofReal (V ^ a⁻¹) with hka
  set kc := ENNReal.ofReal (V ^ c⁻¹) with hkc
  have hkc' : kc = ka * ENNReal.ofReal L := by
    rw [hkc, hka, hVc, ENNReal.ofReal_mul (Real.rpow_nonneg hV.le _)]
  have hka0 : ka ≠ 0 := by
    rw [hka]; simpa using Real.rpow_pos_of_pos hV _
  have hkat : ka ≠ ⊤ := ENNReal.ofReal_ne_top
  set Ga := eLpNorm w.grad (ENNReal.ofReal c) (normalizedCubeMeasure Q) with hGa
  set Wc := eLpNorm w.toFun (ENNReal.ofReal c) (normalizedCubeMeasure Q) with hWc
  set Wa := eLpNorm w.toFun (ENNReal.ofReal a) (normalizedCubeMeasure Q) with hWa
  have hsum : (∑ i : Fin d, eLpNorm (fun x => w.grad x i) (ENNReal.ofReal c) M) ≤
      (d : ℝ≥0∞) * (kc * Ga) := by
    calc _ ≤ ∑ _i : Fin d, kc * Ga := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [e1 _ c hc]
          gcongr
          exact eLpNorm_mono (((memLp_pi_iff).1 hgc i).aestronglyMeasurable) fun x => norm_le_pi_norm (w.grad x) i
      _ = _ := by simp
  have h2 : ka * Wa ≤ (Cs : ℝ≥0∞) * ((d : ℝ≥0∞) * (kc * Ga) +
      ENNReal.ofReal L⁻¹ * (kc * Wc)) := by
    have := h1
    rw [e1 _ a ha, e1 _ c hc] at this
    refine this.trans ?_
    gcongr
  have hkL : ENNReal.ofReal L⁻¹ * ENNReal.ofReal L = 1 := by
    rw [← ENNReal.ofReal_mul (inv_pos.2 hL).le, inv_mul_cancel₀ hL.ne', ENNReal.ofReal_one]
  have h3 : ka * Wa ≤ ka * ((Cs : ℝ≥0∞) * (d : ℝ≥0∞) *
      (ENNReal.ofReal L * Ga + Wc)) := by
    refine h2.trans ?_
    rw [hkc']
    have e2 : ENNReal.ofReal L⁻¹ * (ka * ENNReal.ofReal L * Wc) = ka * Wc := by
      calc _ = ka * (ENNReal.ofReal L⁻¹ * ENNReal.ofReal L) * Wc := by ring
        _ = _ := by rw [hkL, mul_one]
    rw [e2]
    have hd1 : (1 : ℝ≥0∞) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    calc (Cs : ℝ≥0∞) * ((d : ℝ≥0∞) * (ka * ENNReal.ofReal L * Ga) + ka * Wc)
        ≤ (Cs : ℝ≥0∞) * ((d : ℝ≥0∞) * (ka * ENNReal.ofReal L * Ga) + d * (ka * Wc)) := by
          exact mul_le_mul_right (add_le_add_right (le_mul_of_one_le_left bot_le hd1) _) _
      _ = _ := by ring
  have h4 : Wa ≤ (Cs : ℝ≥0∞) * (d : ℝ≥0∞) * (ENNReal.ofReal L * Ga + Wc) :=
    (ENNReal.mul_le_mul_iff_right hka0 hkat).1 h3
  have hfin : Wa < ⊤ := by
    refine h4.trans_lt ?_
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgc.eLpNorm_lt_top
    · exact hwc.eLpNorm_lt_top
  have hm : MemLp w.toFun (ENNReal.ofReal a) (normalizedCubeMeasure Q) :=
    hfin
  refine ⟨hm, ?_⟩
  change Wa ≤ _
  refine h4.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  rfl

/-- Satisfiability: `d = 3`, `c = 3/2`, `a = 3`, the zero function. -/
example : ∃ (w : H1Function (openCubeSet (originCube 3 0))),
    MemLp w.toFun (ENNReal.ofReal (3 / 2)) (normalizedCubeMeasure (originCube 3 0)) ∧
    MemLp w.grad (ENNReal.ofReal (3 / 2)) (normalizedCubeMeasure (originCube 3 0)) ∧
    ((3 / 2 : ℝ))⁻¹ = (3 : ℝ)⁻¹ + ((3 : ℕ) : ℝ)⁻¹ := by
  refine ⟨0, by simp, ?_, by norm_num⟩ 
  · simp
  


/-- One bootstrap step: from `w = χ v ∈ H¹₀` with gradient and values in `L̲^t`, to
`w' = χ' v` (for a cutoff `χ'` supported where `χ = 1`) with gradient and values in `L̲^a`. -/
theorem p12_step [NeZero d] (hd : 2 ≤ d) {t a c Ps pf Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀)
    (ht : 2 ≤ t) (hc : 1 < c) (ha : 1 < a) (hca : c⁻¹ = a⁻¹ + (d : ℝ)⁻¹) (hct : c ≤ t)
    (hta : t ≤ a) (haP : a ≤ Ps) (hcf : c ≤ pf) (hP2 : 2 ≤ Ps) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (Q : TriadicCube d) (A : CoeffField d),
      (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
      (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d) (v : H1Function (openCubeSet Q)),
        IsWeakSolutionOn A (openCubeSet Q) v f g →
        MemLp f 2 (normalizedCubeMeasure Q) → MemLp f (ENNReal.ofReal pf) (normalizedCubeMeasure Q) →
        MemLp g (ENNReal.ofReal Ps) (normalizedCubeMeasure Q) →
        ∀ (χ χ' : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
          (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → ContDiff ℝ (⊤ : ℕ∞) χ' → HasCompactSupport χ' →
          (∀ x, 0 ≤ χ' x ∧ χ' x ≤ 1) → tsupport χ' ⊆ {x | χ x = 1} →
          (∀ x, ‖p12_grad χ' x‖ ≤ Λ₀ / cubeScaleFactor Q) →
          ∀ w : H10Function (openCubeSet Q), (∀ x, w.toH1Function.toFun x = χ x * v.toFun x) →
            (∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
              w.toH1Function.grad x = χ x • v.grad x + v.toFun x • p12_grad χ x) →
            MemLp w.toH1Function.toFun (ENNReal.ofReal t) (normalizedCubeMeasure Q) →
            MemLp w.toH1Function.grad (ENNReal.ofReal t) (normalizedCubeMeasure Q) →
            ∃ w' : H10Function (openCubeSet Q),
              (∀ x, w'.toH1Function.toFun x = χ' x * v.toFun x) ∧
              (∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
                w'.toH1Function.grad x = χ' x • v.grad x + v.toFun x • p12_grad χ' x) ∧
              MemLp w'.toH1Function.toFun (ENNReal.ofReal a) (normalizedCubeMeasure Q) ∧
              MemLp w'.toH1Function.grad (ENNReal.ofReal a) (normalizedCubeMeasure Q) ∧
              ENNReal.ofReal (cubeScaleFactor Q) *
                  Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) w'.toH1Function.grad +
                Section2.Norms.cubeLpENorm Q (ENNReal.ofReal a) w'.toH1Function.toFun ≤
                ENNReal.ofReal C *
                  ((ENNReal.ofReal (cubeScaleFactor Q) *
                      Section2.Norms.cubeLpENorm Q (ENNReal.ofReal t) w.toH1Function.grad +
                    Section2.Norms.cubeLpENorm Q (ENNReal.ofReal t) w.toH1Function.toFun) +
                  ENNReal.ofReal (cubeScaleFactor Q) ^ 2 *
                    Section2.Norms.cubeLpENorm Q (ENNReal.ofReal pf) f +
                  ENNReal.ofReal (cubeScaleFactor Q) *
                    Section2.Norms.cubeLpENorm Q (ENNReal.ofReal Ps) g) := by
  obtain ⟨εz, Cz, hεz, hCz, Hz⟩ := p12_czSV hd hc ha hca
  obtain ⟨Cs, hCs, Hs⟩ := p12_sobolev hd hc ha hca
  set K : ℝ := 1 + d with hKdef
  set cS : ℝ := 1 + d * Λ₀ + d * K * Λ₀ with hcS
  set cG : ℝ := 1 + K * Λ₀ * Cs with hcG
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hK0 : 0 ≤ K := add_nonneg zero_le_one hd0
  have hdΛ : (0 : ℝ) ≤ d * Λ₀ := mul_nonneg hd0 hΛ₀
  have hdKΛ : (0 : ℝ) ≤ d * K * Λ₀ := mul_nonneg (mul_nonneg hd0 hK0) hΛ₀
  have hKΛ : (0 : ℝ) ≤ K * Λ₀ := mul_nonneg hK0 hΛ₀
  have hKΛC : (0 : ℝ) ≤ K * Λ₀ * Cs := mul_nonneg hKΛ hCs
  have hcS0 : 0 ≤ cS := add_nonneg (add_nonneg zero_le_one hdΛ) hdKΛ
  have hcG0 : 0 ≤ cG := add_nonneg zero_le_one hKΛC
  refine ⟨min εz 1, Cz * (cS + cG) + Cs + 1, lt_min hεz one_pos,
    add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg hCz.le (add_nonneg hcS0 hcG0)) hCs) one_pos, ?_⟩
  intro Q A hA hε f g v hv hf2 hfp hgP χ χ' hχ hχc hχ01 hχ' hχ'c hχ'01 hnest hΛ' w hwf hwg hwt hgt
  have hℓ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  set ℓ := cubeScaleFactor Q with hℓdef
  set μ := normalizedCubeMeasure Q with hμ
  have hprob : IsProbabilityMeasure μ := p12_isProb Q
  have hεz' : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ εz :=
    fun x hx i j => (hε x hx i j).trans (min_le_left _ _)
  have hε1 : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ 1 :=
    fun x hx i j => (hε x hx i j).trans (min_le_right _ _)
  have hK : ∀ x ∈ openCubeSet Q, ∀ y : Vec d, ‖matVecMul (A x) y‖ ≤ K * ‖y‖ := by
    intro x hx y
    have h1 := norm_matVecMul_sub_one_le (hε1 x hx) y
    rw [matVecMul_eq_add_pert (A x) y]
    calc ‖y + matVecMul (A x - 1) y‖ ≤ ‖y‖ + ‖matVecMul (A x - 1) y‖ := norm_add_le _ _
      _ ≤ ‖y‖ + d * 1 * ‖y‖ := by linarith only [h1]
      _ = K * ‖y‖ := by rw [hKdef]; ring
  have hcle : c ≤ a := by
    have hc0 : 0 < c := by linarith only [hc]
    have ha0 : 0 < a := by linarith only [ha]
    have hd0 : 0 < (d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (by omega : 0 < d))
    have : a⁻¹ ≤ c⁻¹ := by rw [hca]; linarith only [hd0]
    exact (inv_le_inv₀ ha0 hc0).1 this
  have hcP : c ≤ Ps := hcle.trans haP
  have hc1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hc.le
  have hOR : ∀ {x y : ℝ}, x ≤ y → ENNReal.ofReal x ≤ ENNReal.ofReal y :=
    fun h => ENNReal.ofReal_le_ofReal h
  have hg2 : MemLp g 2 μ := by
    refine p12_memLp_mono_exp Q ?_ hgP
    have : (ENNReal.ofReal 2) ≤ ENNReal.ofReal Ps := hOR hP2
    simpa using this
  -- the new function
  set w' := w.mulContDiffHasCompactSupport hχ' hχ'c with hw'
  have hw'tf : ∀ x, w'.toH1Function.toFun x = χ' x * w.toH1Function.toFun x := fun x => by
    simp [hw']
  have hnest' : ∀ x, χ' x ≠ 0 → χ x = 1 := fun x hx =>
    hnest (subset_tsupport _ (Function.mem_support.2 hx))
  have hw'f : ∀ x, w'.toH1Function.toFun x = χ' x * v.toFun x := by
    intro x
    rw [hw'tf, hwf]
    by_cases hx : χ' x = 0
    · simp [hx]
    · rw [hnest' x hx]; ring
  have hgrad0 : ∀ x, p12_grad χ' x ≠ 0 → χ x = 1 := by
    intro x hx
    by_contra hne
    have hxs : x ∉ tsupport χ' := fun hxs => hne (hnest hxs)
    exact hx (p12_grad_eq_zero_of_notMem hxs)
  have hcont' : Continuous (p12_grad χ') := p12_continuous_grad hχ'
  have hM : ∀ x, |χ' x| ≤ 1 := fun x => by rw [abs_of_nonneg (hχ'01 x).1]; exact (hχ'01 x).2
  have hloc := p12_localize Q hA hK (u := v) (s := f) (G := g) hf2 hg2 hv hχ' hχ'c hM hΛ' w' hw'f
  have h2R : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by simp
  have hwc : MemLp w.toH1Function.toFun (ENNReal.ofReal c) μ :=
    p12_memLp_mono_exp Q (hOR hct) hwt
  have hgc : MemLp w.toH1Function.grad (ENNReal.ofReal c) μ :=
    p12_memLp_mono_exp Q (hOR hct) hgt
  obtain ⟨hwa, hwa_b⟩ := Hs Q w.toH1Function hwc hgc
  have hvf2 : MemLp v.toFun 2 μ := memLp_normalized_of_restrict Q v.memL2
  have hvg2 : MemLp v.grad 2 μ := memLp_normalized_of_memVectorL2 Q v.grad_memVectorL2
  have hAvg : AEStronglyMeasurable (fun x => matVecMul (A x) (v.grad x)) μ :=
    p12_aesm_matVec Q hA hvg2.aestronglyMeasurable
  have hcont' : Continuous (p12_grad χ') := p12_continuous_grad hχ'
  have hχ'cont : Continuous χ' := hχ'.continuous
  set S' : Vec d → ℝ := fun x => χ' x * f x + vecDot (g x) (p12_grad χ' x) -
    vecDot (matVecMul (A x) (v.grad x)) (p12_grad χ' x) with hS'
  set G'' : Vec d → Vec d := fun x => χ' x • g x +
    v.toFun x • matVecMul (A x) (p12_grad χ' x) with hG''
  have hS'meas : AEStronglyMeasurable S' μ :=
    ((hχ'cont.aestronglyMeasurable.mul hf2.aestronglyMeasurable).add
      (p12_aesm_vecDot Q hg2.aestronglyMeasurable hcont'.aestronglyMeasurable)).sub
      (p12_aesm_vecDot Q hAvg hcont'.aestronglyMeasurable)
  have hG''meas : AEStronglyMeasurable G'' μ :=
    (hχ'cont.aestronglyMeasurable.smul hg2.aestronglyMeasurable).add
      (hvf2.aestronglyMeasurable.smul (p12_aesm_matVec Q hA hcont'.aestronglyMeasurable))
  have hae : ∀ᵐ x ∂μ, x ∈ openCubeSet Q ∧
      (p12_grad χ' x ≠ 0 → w.toH1Function.grad x = v.grad x) := by
    have h1 := ae_mem_openCubeSet Q
    have h2 : ∀ᵐ x ∂μ, w.toH1Function.grad x =
        χ x • v.grad x + v.toFun x • p12_grad χ x := by
      rw [hμ, normalizedCubeMeasure_eq_smul]
      exact Measure.ae_smul_measure hwg _
    filter_upwards [h1, h2] with x hx hx2
    refine ⟨hx, fun hne => ?_⟩
    have h1x := hgrad0 x hne
    have h0 : p12_grad χ x = 0 := p12_grad_eq_zero_of_eq_one (fun y => (hχ01 y).2) h1x
    rw [hx2, h1x, h0]
    simp
  have hΛℓ : 0 ≤ Λ₀ / ℓ := div_nonneg hΛ₀ hℓ.le
  have hb1 : 0 ≤ (d : ℝ) * Λ₀ / ℓ := div_nonneg hdΛ hℓ.le
  have hc1' : 0 ≤ (d : ℝ) * K * Λ₀ / ℓ := div_nonneg hdKΛ hℓ.le
  have hb2 : 0 ≤ K * Λ₀ / ℓ := div_nonneg hKΛ hℓ.le
  have hSb : ∀ᵐ x ∂μ, ‖S' x‖ ≤ 1 * ‖f x‖ + (d * Λ₀ / ℓ) * ‖g x‖ +
      (d * K * Λ₀ / ℓ) * ‖w.toH1Function.grad x‖ := by
    filter_upwards [hae] with x ⟨hxU, hxg⟩
    have hΛx := hΛ' x
    have hAw : vecDot (matVecMul (A x) (v.grad x)) (p12_grad χ' x) =
        vecDot (matVecMul (A x) (w.toH1Function.grad x)) (p12_grad χ' x) := by
      by_cases hz : p12_grad χ' x = 0
      · simp [hz, vecDot]
      · rw [hxg hz]
    have e1 : |χ' x * f x| ≤ 1 * ‖f x‖ := by
      rw [abs_mul, abs_of_nonneg (hχ'01 x).1, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hχ'01 x).2 (abs_nonneg _)
    have e2 : |vecDot (g x) (p12_grad χ' x)| ≤ (d * Λ₀ / ℓ) * ‖g x‖ := by
      refine (p12_abs_vecDot_le _ _).trans ?_
      calc (d : ℝ) * (‖g x‖ * ‖p12_grad χ' x‖) ≤ d * (‖g x‖ * (Λ₀ / ℓ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛx (norm_nonneg _)) hd0
        _ = (d * Λ₀ / ℓ) * ‖g x‖ := by ring
    have e3 : |vecDot (matVecMul (A x) (w.toH1Function.grad x)) (p12_grad χ' x)| ≤
        (d * K * Λ₀ / ℓ) * ‖w.toH1Function.grad x‖ := by
      refine (p12_abs_vecDot_le _ _).trans ?_
      have := hK x hxU (w.toH1Function.grad x)
      calc (d : ℝ) * (‖matVecMul (A x) (w.toH1Function.grad x)‖ * ‖p12_grad χ' x‖)
          ≤ d * ((K * ‖w.toH1Function.grad x‖) * (Λ₀ / ℓ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul this hΛx (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))) hd0
        _ = (d * K * Λ₀ / ℓ) * ‖w.toH1Function.grad x‖ := by ring
    rw [Real.norm_eq_abs]
    calc |S' x| = |χ' x * f x + vecDot (g x) (p12_grad χ' x) -
            vecDot (matVecMul (A x) (w.toH1Function.grad x)) (p12_grad χ' x)| := by
          simp only [hS']; rw [hAw]
      _ ≤ |χ' x * f x + vecDot (g x) (p12_grad χ' x)| +
            |vecDot (matVecMul (A x) (w.toH1Function.grad x)) (p12_grad χ' x)| := abs_sub _ _
      _ ≤ (|χ' x * f x| + |vecDot (g x) (p12_grad χ' x)|) +
            |vecDot (matVecMul (A x) (w.toH1Function.grad x)) (p12_grad χ' x)| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith only [e1, e2, e3]
  have hGb : ∀ᵐ x ∂μ, ‖G'' x‖ ≤ 1 * ‖g x‖ + (K * Λ₀ / ℓ) * ‖w.toH1Function.toFun x‖ +
      0 * ‖w.toH1Function.toFun x‖ := by
    filter_upwards [hae] with x ⟨hxU, _⟩
    have hΛx := hΛ' x
    have hvw : v.toFun x • matVecMul (A x) (p12_grad χ' x) =
        w.toH1Function.toFun x • matVecMul (A x) (p12_grad χ' x) := by
      by_cases hz : p12_grad χ' x = 0
      · simp [hz, p12_matVecMul_zero]
      · rw [hwf x, hgrad0 x hz]; simp
    have hG1 : G'' x = χ' x • g x + w.toH1Function.toFun x • matVecMul (A x) (p12_grad χ' x) := by
      simp only [hG'']; rw [hvw]
    have f1 : ‖χ' x • g x‖ ≤ 1 * ‖g x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ'01 x).1]
      exact mul_le_mul_of_nonneg_right (hχ'01 x).2 (norm_nonneg _)
    have f2 : ‖w.toH1Function.toFun x • matVecMul (A x) (p12_grad χ' x)‖ ≤
        (K * Λ₀ / ℓ) * ‖w.toH1Function.toFun x‖ := by
      rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
      have := hK x hxU (p12_grad χ' x)
      calc ‖w.toH1Function.toFun x‖ * ‖matVecMul (A x) (p12_grad χ' x)‖
          ≤ ‖w.toH1Function.toFun x‖ * (K * (Λ₀ / ℓ)) :=
          mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left hΛx hK0)) (norm_nonneg _)
        _ = (K * Λ₀ / ℓ) * ‖w.toH1Function.toFun x‖ := by ring
    rw [hG1]
    calc ‖χ' x • g x + w.toH1Function.toFun x • matVecMul (A x) (p12_grad χ' x)‖
        ≤ ‖χ' x • g x‖ + ‖w.toH1Function.toFun x • matVecMul (A x) (p12_grad χ' x)‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith only [f1, f2, norm_nonneg (w.toH1Function.toFun x)]
  have h2t : (2 : ℝ≥0∞) ≤ ENNReal.ofReal t := by rw [← h2R]; exact hOR ht
  have hgrad2 : MemLp w.toH1Function.grad 2 μ := p12_memLp_mono_exp Q h2t hgt
  have hwL2 : MemLp w.toH1Function.toFun 2 μ := p12_memLp_mono_exp Q h2t hwt
  have hfc : MemLp f (ENNReal.ofReal c) μ := p12_memLp_mono_exp Q (hOR hcf) hfp
  have hgcc : MemLp g (ENNReal.ofReal c) μ := p12_memLp_mono_exp Q (hOR hcP) hgP
  have hga : MemLp g (ENNReal.ofReal a) μ := p12_memLp_mono_exp Q (hOR haP) hgP
  have hS2 : MemLp S' 2 μ := (p12_bound3 (p := 2) (by norm_num) (a := 1) (b := d * Λ₀ / ℓ)
    (c := d * K * Λ₀ / ℓ) (by norm_num) hb1 hc1' hS'meas hf2 hg2
    hgrad2 hSb).1
  obtain ⟨hSc, hSc_b⟩ := p12_bound3 (p := ENNReal.ofReal c) hc1 (a := 1) (b := d * Λ₀ / ℓ)
    (c := d * K * Λ₀ / ℓ) (by norm_num) hb1 hc1' hS'meas hfc hgcc hgc hSb
  have ha1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ha.le
  obtain ⟨hGa, hGa_b⟩ := p12_bound3 (p := ENNReal.ofReal a) ha1 (a := 1) (b := K * Λ₀ / ℓ)
    (c := 0) (by norm_num) hb2 le_rfl hG''meas hga hwa hwa hGb
  have h2a : (2 : ℝ≥0∞) ≤ ENNReal.ofReal a := by
    rw [← h2R]; exact hOR (ht.trans hta)
  have hG2 : MemLp G'' 2 μ := p12_memLp_mono_exp Q h2a hGa
  obtain ⟨hwg', hwg'b⟩ := Hz Q A hA hεz' S' G'' hS2 hSc hG2 hGa w' hloc
  -- the values of `w'`
  have hw'meas : AEStronglyMeasurable w'.toH1Function.toFun μ :=
    (memLp_normalized_of_restrict Q w'.toH1Function.memL2).aestronglyMeasurable
  have hw'le : ∀ᵐ x ∂μ, ‖w'.toH1Function.toFun x‖ ≤ ‖w.toH1Function.toFun x‖ := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [hw'tf, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ'01 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ'01 x).2
  have hw'a : MemLp w'.toH1Function.toFun (ENNReal.ofReal a) μ := hwa.of_le hw'meas hw'le
  have hw'a_b : eLpNorm w'.toH1Function.toFun (ENNReal.ofReal a) μ ≤
      eLpNorm w.toH1Function.toFun (ENNReal.ofReal a) μ := eLpNorm_mono_ae hw'meas hw'le
  refine ⟨w', hw'f, p12_grad_ae Q hχ' hχ'c v w' hw'f, hw'a, hwg', ?_⟩
  unfold Section2.Norms.cubeLpENorm at hwa_b hwg'b ⊢
  set Lw : ℝ≥0∞ := ENNReal.ofReal ℓ with hLw
  set nGt : ℝ≥0∞ := eLpNorm w.toH1Function.grad (ENNReal.ofReal t) μ with hnGt
  set nWt : ℝ≥0∞ := eLpNorm w.toH1Function.toFun (ENNReal.ofReal t) μ with hnWt
  set Nw : ℝ≥0∞ := Lw * nGt + nWt with hNw
  set F2 : ℝ≥0∞ := Lw ^ 2 * eLpNorm f (ENNReal.ofReal pf) μ with hF2
  set Gg : ℝ≥0∞ := Lw * eLpNorm g (ENNReal.ofReal Ps) μ with hGg
  have mf : eLpNorm f (ENNReal.ofReal c) μ ≤ eLpNorm f (ENNReal.ofReal pf) μ :=
    p12_eLpNorm_mono_exp Q (hOR hcf)
  have mg : eLpNorm g (ENNReal.ofReal c) μ ≤ eLpNorm g (ENNReal.ofReal Ps) μ :=
    p12_eLpNorm_mono_exp Q (hOR hcP)
  have mga : eLpNorm g (ENNReal.ofReal a) μ ≤ eLpNorm g (ENNReal.ofReal Ps) μ :=
    p12_eLpNorm_mono_exp Q (hOR haP)
  have mG : eLpNorm w.toH1Function.grad (ENNReal.ofReal c) μ ≤ nGt :=
    p12_eLpNorm_mono_exp Q (hOR hct)
  have mW : eLpNorm w.toH1Function.toFun (ENNReal.ofReal c) μ ≤ nWt :=
    p12_eLpNorm_mono_exp Q (hOR hct)
  -- (a) the Sobolev bound
  have hWa : eLpNorm w.toH1Function.toFun (ENNReal.ofReal a) μ ≤ ENNReal.ofReal Cs * Nw := by
    refine hwa_b.trans ?_
    rw [hNw]
    exact mul_le_mul_right (add_le_add (mul_le_mul_right mG _) mW) _
  -- (b) the scalar datum
  have hS_b : Lw * (Lw * eLpNorm S' (ENNReal.ofReal c) μ) ≤
      F2 + ENNReal.ofReal (d * Λ₀) * Gg + ENNReal.ofReal (d * K * Λ₀) * (Lw * nGt) := by
    calc Lw * (Lw * eLpNorm S' (ENNReal.ofReal c) μ)
        ≤ Lw * (Lw * (ENNReal.ofReal 1 * eLpNorm f (ENNReal.ofReal pf) μ +
            ENNReal.ofReal (d * Λ₀ / ℓ) * eLpNorm g (ENNReal.ofReal Ps) μ +
            ENNReal.ofReal (d * K * Λ₀ / ℓ) * nGt)) := by
          exact mul_le_mul_right (mul_le_mul_right (hSc_b.trans (add_le_add (add_le_add
            (mul_le_mul_right mf _) (mul_le_mul_right mg _)) (mul_le_mul_right mG _))) _) _
      _ = Lw ^ 2 * eLpNorm f (ENNReal.ofReal pf) μ +
            (Lw * ENNReal.ofReal (d * Λ₀ / ℓ)) * (Lw * eLpNorm g (ENNReal.ofReal Ps) μ) +
            (Lw * ENNReal.ofReal (d * K * Λ₀ / ℓ)) * (Lw * nGt) := by
          rw [ENNReal.ofReal_one, one_mul]; ring
      _ = _ := by
          rw [hLw, p12_ofReal_mul_ofReal_div hℓ, p12_ofReal_mul_ofReal_div hℓ]
  -- (c) the vector datum
  have hG_b : Lw * eLpNorm G'' (ENNReal.ofReal a) μ ≤
      Gg + ENNReal.ofReal (K * Λ₀) * eLpNorm w.toH1Function.toFun (ENNReal.ofReal a) μ := by
    calc Lw * eLpNorm G'' (ENNReal.ofReal a) μ
        ≤ Lw * (ENNReal.ofReal 1 * eLpNorm g (ENNReal.ofReal Ps) μ +
            ENNReal.ofReal (K * Λ₀ / ℓ) * eLpNorm w.toH1Function.toFun (ENNReal.ofReal a) μ) := by
          refine mul_le_mul_right (hGa_b.trans ?_) _
          rw [ENNReal.ofReal_zero, zero_mul, add_zero]
          exact add_le_add (mul_le_mul_right mga _) le_rfl
      _ = Lw * eLpNorm g (ENNReal.ofReal Ps) μ +
            (Lw * ENNReal.ofReal (K * Λ₀ / ℓ)) *
              eLpNorm w.toH1Function.toFun (ENNReal.ofReal a) μ := by
          rw [ENNReal.ofReal_one, one_mul]; ring
      _ = _ := by rw [hLw, p12_ofReal_mul_ofReal_div hℓ]
  have hLn : Lw * nGt ≤ Nw := by rw [hNw]; exact le_self_add
  have hN1 : Lw * eLpNorm w'.toH1Function.grad (ENNReal.ofReal a) μ +
      eLpNorm w'.toH1Function.toFun (ENNReal.ofReal a) μ ≤
      ENNReal.ofReal Cz * (F2 + ENNReal.ofReal (d * Λ₀) * Gg + ENNReal.ofReal (d * K * Λ₀) * Nw +
        (Gg + ENNReal.ofReal (K * Λ₀) * (ENNReal.ofReal Cs * Nw))) + ENNReal.ofReal Cs * Nw := by
    calc Lw * eLpNorm w'.toH1Function.grad (ENNReal.ofReal a) μ +
          eLpNorm w'.toH1Function.toFun (ENNReal.ofReal a) μ
        ≤ Lw * (ENNReal.ofReal Cz * (Lw * eLpNorm S' (ENNReal.ofReal c) μ +
            eLpNorm G'' (ENNReal.ofReal a) μ)) + ENNReal.ofReal Cs * Nw := by
          exact add_le_add (mul_le_mul_right hwg'b _) (hw'a_b.trans hWa)
      _ = ENNReal.ofReal Cz * (Lw * (Lw * eLpNorm S' (ENNReal.ofReal c) μ) +
            Lw * eLpNorm G'' (ENNReal.ofReal a) μ) + ENNReal.ofReal Cs * Nw := by ring
      _ ≤ ENNReal.ofReal Cz * ((F2 + ENNReal.ofReal (d * Λ₀) * Gg +
            ENNReal.ofReal (d * K * Λ₀) * (Lw * nGt)) +
            (Gg + ENNReal.ofReal (K * Λ₀) * (ENNReal.ofReal Cs * Nw))) +
            ENNReal.ofReal Cs * Nw := by
          exact add_le_add (mul_le_mul_right (add_le_add hS_b
            (hG_b.trans (add_le_add le_rfl (mul_le_mul_right hWa _)))) _) le_rfl
      _ ≤ _ := add_le_add (mul_le_mul_right
          (add_le_add (add_le_add le_rfl (mul_le_mul_right hLn _)) le_rfl) _) le_rfl
  have hα : ENNReal.ofReal (Cz * (d * K * Λ₀ + K * Λ₀ * Cs) + Cs) =
      ENNReal.ofReal Cz * (ENNReal.ofReal (d * K * Λ₀) + ENNReal.ofReal (K * Λ₀) *
        ENNReal.ofReal Cs) + ENNReal.ofReal Cs := by
    rw [ENNReal.ofReal_add (mul_nonneg hCz.le (add_nonneg hdKΛ hKΛC)) hCs, ENNReal.ofReal_mul hCz.le,
      ENNReal.ofReal_add hdKΛ hKΛC, ENNReal.ofReal_mul hKΛ]
  have hγ : ENNReal.ofReal (Cz * (d * Λ₀ + 1)) =
      ENNReal.ofReal Cz * (ENNReal.ofReal (d * Λ₀) + 1) := by
    rw [ENNReal.ofReal_mul hCz.le, ENNReal.ofReal_add hdΛ zero_le_one, ENNReal.ofReal_one]
  have hβ : ENNReal.ofReal Cz = ENNReal.ofReal Cz := rfl
  have hX : ENNReal.ofReal Cz * (F2 + ENNReal.ofReal (d * Λ₀) * Gg +
      ENNReal.ofReal (d * K * Λ₀) * Nw +
        (Gg + ENNReal.ofReal (K * Λ₀) * (ENNReal.ofReal Cs * Nw))) + ENNReal.ofReal Cs * Nw =
      ENNReal.ofReal (Cz * (d * K * Λ₀ + K * Λ₀ * Cs) + Cs) * Nw + ENNReal.ofReal Cz * F2 +
        ENNReal.ofReal (Cz * (d * Λ₀ + 1)) * Gg := by
    rw [hα, hγ]; ring
  refine p12_comb (x1 := Nw) (x2 := F2) (x3 := Gg) (α := Cz * (d * K * Λ₀ + K * Λ₀ * Cs) + Cs)
    (β := Cz) (γ := Cz * (d * Λ₀ + 1)) (C := Cz * (cS + cG) + Cs + 1)
    (hN1.trans_eq (hX.trans ?_)) ?_ ?_ ?_
  · rw [hβ]
  · have h1 : d * K * Λ₀ + K * Λ₀ * Cs ≤ cS + cG := by rw [hcS, hcG]; linarith only [hdΛ]
    have := mul_le_mul_of_nonneg_left h1 hCz.le
    linarith only [this]
  · have h1 : (1 : ℝ) ≤ cS + cG := by rw [hcS, hcG]; linarith only [hdΛ, hdKΛ, hKΛC]
    have := mul_le_mul_of_nonneg_left h1 hCz.le
    linarith only [this, hCs]
  · have h1 : d * Λ₀ + 1 ≤ cS + cG := by rw [hcS, hcG]; linarith only [hdKΛ, hKΛC]
    have := mul_le_mul_of_nonneg_left h1 hCz.le
    linarith only [this, hCs]

end SuperdiffusionCLT.Section7
