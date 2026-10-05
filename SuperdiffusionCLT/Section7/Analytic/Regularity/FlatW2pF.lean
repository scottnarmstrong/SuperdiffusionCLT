/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pE
public import SuperdiffusionCLT.Section7.Analytic.CZ.CubeScalarDataB
public import SuperdiffusionCLT.Section5.Carriers.BlockOffsetMinimizerB

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}` on a cube: scalar data

`-∇·(A∇w) = F` with `F ∈ L̲^p`, `p > 2`: the scalar datum is `∇·∇ψ` for the Laplace response `ψ`
of `F`, whose Hessian is controlled by the Calderón–Zygmund estimate and whose gradient by the
Sobolev step of `CubeScalarData`.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

/-- The Laplace response of an `L²` scalar datum on the origin cube. -/
theorem flatW2p_exists_poisson [NeZero d] (m : ℤ) {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure (originCube d m))) :
    ∃ ψ : H10Function (openCubeSet (originCube d m)), CubeDirichletWeakPoissonProblem
      (originCube d m) ψ F := by
  have hF' : MemScalarL2 (openCubeSet (originCube d m)) F := by
    simpa [MemScalarL2, volumeMeasureOn] using memLp_restrict_of_normalized (originCube d m) hF
  have hg : MemVectorL2 (openCubeSet (originCube d m)) (fun _ : Vec d => (0 : Vec d)) := by
    simp [MemVectorL2, volumeMeasureOn]
  have hne : (openCubeSet (originCube d m)).Nonempty := ⟨0, flatW2p_zero_mem_openCubeSet m⟩
  obtain ⟨ψ, hψ⟩ := exists_h10_weak_solution (isOpen_openCubeSet (originCube d m)) (isBoundedDomain_openCubeSet (originCube d m))
    hne (Section5.isEllipticFieldOn_one (measurableSet_openCubeSet (originCube d m))) hF' hg
  refine ⟨ψ, fun φ => ?_⟩
  have := hψ φ
  simpa [matVecMul_one_left, vecDot_zero_left] using this

theorem flatW2p_neg_jacobian {U : Set (Vec d)} {u : H1Function U} (H : HasWeakHessianOn U u) :
    HasWeakJacobianOn U (fun x => -u.grad x) (fun i x k => -H.hess i k x) := by
  intro i k
  exact flatW2p_weakPartial_neg (H.weak_second i k)

/-- **Flat `W^{2,p}`, scalar form.** -/
theorem flatW2p_scalar (hd : 2 ≤ d) {p : ℝ≥0∞} (hp2 : 2 < p) (hpt : p < ⊤) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ F : Vec d → ℝ, MemLp F p (normalizedCubeMeasure (originCube d m)) →
          ∀ w : H10Function (openCubeSet (originCube d m)),
            IsH10WeakSolution A (openCubeSet (originCube d m)) F (fun _ => 0) w →
            ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) w.toH1Function,
              MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) p
                (normalizedCubeMeasure (originCube d m)) ∧
              cubeLpNorm (originCube d m) p (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
                C * cubeLpNorm (originCube d m) p F := by
  have : NeZero d := ⟨by omega⟩
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2.le
  have hP2 : 2 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by norm_num) hpt.ne).2 hp2
    simpa using this
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = p.toReal := ⟨_, rfl⟩
  rw [← hPdef] at hP2
  obtain ⟨rr, hrrdef⟩ : ∃ rr : ℝ, rr = d * P / (d + P) := ⟨_, rfl⟩
  have hr1 : 1 < rr := by
    rw [hrrdef, lt_div_iff₀ (by positivity)]; nlinarith only [hd2, hP2]
  have hrd : rr < d := by
    rw [hrrdef, div_lt_iff₀ (by positivity)]; nlinarith only [hd2, hP2]
  have hrP : rr ≤ P := by
    rw [hrrdef, div_le_iff₀ (by positivity)]; nlinarith only [hd2, hP2]
  let r : FiniteLpExponent := mkExp rr hr1
  let pe : FiniteLpExponent := ⟨p, hp1, hpt⟩
  have hr : r.exponent.toReal < d := by
    show (mkExp rr hr1).exponent.toReal < d
    rw [mkExp_toReal]; exact hrd
  have hq : (pe.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹ := by
    show p.toReal⁻¹ = (mkExp rr hr1).exponent.toReal⁻¹ - (d : ℝ)⁻¹
    rw [mkExp_toReal, ← hPdef, hrrdef]
    have : (0 : ℝ) < d := by linarith only [hd2]
    have : (0 : ℝ) < P := by linarith only [hP2]
    field_simp
    ring
  obtain ⟨Cs, hCstop, hCs⟩ := exists_cubeScalarData_gradVecLp_sobolev_triadic hd r pe hr hq
  obtain ⟨Ch, hChtop, hCh⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d pe
  obtain ⟨ε, C₁, hε, hC₁, hdiv⟩ := flatW2p_divergence hd hp2.le hpt
  refine ⟨ε, C₁ * (Ch.toReal + Cs.toReal + 1), hε, by positivity, ?_⟩
  intro m A K hA hAε hAK hKℓ F hFp w hw
  have hprob : IsProbabilityMeasure (normalizedCubeMeasure (originCube d m)) :=
    ⟨normalizedCubeMeasure_apply_univ _⟩
  have hℓ : 0 < cubeScaleFactor (originCube d m) := cubeScaleFactor_pos' _
  have hF2 : MemLp F 2 (normalizedCubeMeasure (originCube d m)) := hFp.mono_exponent hp2.le
  have hrle : r.exponent ≤ p := by
    show (mkExp rr hr1).exponent ≤ p
    rw [mkExp_exponent]
    calc ENNReal.ofReal rr ≤ ENNReal.ofReal P := ENNReal.ofReal_le_ofReal hrP
      _ = p := by rw [hPdef, ENNReal.ofReal_toReal hpt.ne]
  have hFr : MemLp F r.exponent (normalizedCubeMeasure (originCube d m)) :=
    hFp.mono_exponent hrle
  obtain ⟨ψ, hψ⟩ := flatW2p_exists_poisson m hF2
  obtain ⟨hgm, hgb⟩ := hCs (originCube d m) F hF2 hFr ψ hψ
  obtain ⟨Hψ, hHm, hHb⟩ := hCh m F hF2 hFp ψ hψ
  have hGp : MemLp (fun x => -ψ.toH1Function.grad x) p (normalizedCubeMeasure (originCube d m)) :=
    hgm.neg
  have hweak := flatW2p_neg_jacobian Hψ
  have hjac : jacobianHilbertMat (fun i x k => -Hψ.hess i k x) =
      fun x => -(flatHessMat Hψ x) := by
    funext x; ext i j; simp [jacobianHilbertMat, flatHessMat]
  have hJp : MemLp (jacobianHilbertMat (fun i x k => -Hψ.hess i k x)) p
      (normalizedCubeMeasure (originCube d m)) := by
    rw [hjac]; exact hHm.neg
  have hw' : IsZeroTraceDirichletRhsWeakSolution A (openCubeSet (originCube d m)) w
      (fun x => -(fun x => -ψ.toH1Function.grad x) x) := by
    intro φ
    have a := hw φ
    have b := hψ φ
    simp only [neg_neg]
    simp only [vecDot_zero_left, integral_zero, add_zero] at a
    rw [a, ← b]
  obtain ⟨H, hHm', hHb'⟩ := hdiv m A K hA hAε hAK hKℓ _ _ hGp hweak hJp w hw'
  refine ⟨H, hHm', ?_⟩
  have hFfin : eLpNorm F p (normalizedCubeMeasure (originCube d m)) ≠ ⊤ := hFp.eLpNorm_lt_top.ne
  have h1 : cubeLpNorm (originCube d m) p (flatHessMat Hψ) ≤
      Ch.toReal * cubeLpNorm (originCube d m) p F := flatW2p_toReal_le hChtop.ne hFfin hHb
  have hn1 : cubeLpNorm (originCube d m) p (jacobianHilbertMat (fun i x k => -Hψ.hess i k x)) =
      cubeLpNorm (originCube d m) p (flatHessMat Hψ) := by
    rw [hjac]
    unfold cubeLpNorm
    rw [show (fun x => -(flatHessMat Hψ x)) = -(flatHessMat Hψ) from rfl, eLpNorm_neg]
  have hn2 : cubeLpNorm (originCube d m) p (fun x => -ψ.toH1Function.grad x) =
      cubeLpNorm (originCube d m) p ψ.toH1Function.grad := by
    unfold cubeLpNorm
    rw [show (fun x => -ψ.toH1Function.grad x) = -ψ.toH1Function.grad from rfl, eLpNorm_neg]
  have hFrp : eLpNorm F r.exponent (normalizedCubeMeasure (originCube d m)) ≤
      eLpNorm F p (normalizedCubeMeasure (originCube d m)) :=
    eLpNorm_le_eLpNorm_of_exponent_le hrle
  have hgb' : cubeLpNorm (originCube d m) p ψ.toH1Function.grad ≤
      Cs.toReal * cubeScaleFactor (originCube d m) *
        cubeLpNorm (originCube d m) p F := by
    have h2 : Section2.Norms.cubeLpENorm (originCube d m) p ψ.toH1Function.grad ≤
        (Cs * ENNReal.ofReal (cubeScaleFactor (originCube d m))) *
          eLpNorm F p (normalizedCubeMeasure (originCube d m)) :=
      hgb.trans (by
        unfold Section2.Norms.cubeLpENorm
        gcongr)
    have h3 := flatW2p_toReal_le (ENNReal.mul_ne_top hCstop.ne ENNReal.ofReal_ne_top) hFfin h2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hℓ.le] at h3
    exact h3
  have hnG : 0 ≤ cubeLpNorm (originCube d m) p F := ENNReal.toReal_nonneg
  have hnH : 0 ≤ cubeLpNorm (originCube d m) p (flatHessMat Hψ) := ENNReal.toReal_nonneg
  have hCh0 : 0 ≤ Ch.toReal := ENNReal.toReal_nonneg
  have hCs0 : 0 ≤ Cs.toReal := ENNReal.toReal_nonneg
  have hinv : (cubeScaleFactor (originCube d m))⁻¹ * (Cs.toReal * cubeScaleFactor (originCube d m) *
      cubeLpNorm (originCube d m) p F) = Cs.toReal * cubeLpNorm (originCube d m) p F := by
    field_simp
  rw [hn1] at hHb'
  rw [hn2] at hHb'
  have h4 : cubeLpNorm (originCube d m) p (flatHessMat Hψ) +
      (cubeScaleFactor (originCube d m))⁻¹ * cubeLpNorm (originCube d m) p ψ.toH1Function.grad ≤
      (Ch.toReal + Cs.toReal + 1) * cubeLpNorm (originCube d m) p F := by
    have h5 := mul_le_mul_of_nonneg_left hgb' (inv_nonneg.2 hℓ.le)
    rw [hinv] at h5
    have h6 : Ch.toReal * cubeLpNorm (originCube d m) p F ≥ 0 := by positivity
    linarith only [h1, h5, hnG, h6]
  calc _ ≤ C₁ * _ := hHb'
    _ ≤ C₁ * ((Ch.toReal + Cs.toReal + 1) * cubeLpNorm (originCube d m) p F) :=
        mul_le_mul_of_nonneg_left h4 hC₁.le
    _ = _ := by ring

end SuperdiffusionCLT.Section7
