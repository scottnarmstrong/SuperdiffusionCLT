/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pC

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}` on a cube: the divergence form

For a smooth coefficient field `A` with `A - 1` small and `∇A` of size `K ≤ ε / 3^m` on the origin
cube `Q` of side `3^m`, a zero-trace weak solution `w` of `-∇·(A∇w) = ∇·G` with `G` carrying a weak
Jacobian in `L̲^p`, `2 ≤ p < ∞`, has a weak Hessian in `L̲^p` with
`‖∇²w‖_{L̲^p} ≤ C (‖∇G‖_{L̲^p} + 3^{-m} ‖G‖_{L̲^p})`.

The proof is a Neumann series around the Laplacian: `w = ∑ₖ wₖ`, `w₀` the Laplace response of `G`,
`wₖ₊₁` the Laplace response of `(A - 1) ∇wₖ`.  The Hessian of each response is estimated by the
Calderón–Zygmund estimate for responses on cubes, using the product rule for the weak Jacobian of
`(A - 1) ∇wₖ`; the terms are geometrically small in `L̲^p`.  The gradients converge to `∇w` in
`L̲²` by the contraction of the `L̲²` Neumann iteration, which identifies the limit with `w`.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem flatW2p_pert_add (A : CoeffField d) (f g : Vec d → Vec d) :
    pert A (fun x => f x + g x) = fun x => pert A f x + pert A g x := by
  funext x i
  simp [pert, matVecMul, mul_add, Finset.sum_add_distrib]

theorem flatW2p_problem_add {Q : TriadicCube d} {w₁ w₂ : H10Function (openCubeSet Q)}
    {h₁ h₂ : Vec d → Vec d} (h₁2 : MemLp h₁ 2 (normalizedCubeMeasure Q))
    (h₂2 : MemLp h₂ 2 (normalizedCubeMeasure Q))
    (H₁ : CubeDirichletDivergenceProblem Q w₁ h₁) (H₂ : CubeDirichletDivergenceProblem Q w₂ h₂) :
    CubeDirichletDivergenceProblem Q (w₁ + w₂) (fun x => h₁ x + h₂ x) := by
  intro φ
  have hφ := memLp_two_grad Q φ
  have a1 := H₁ φ
  have a2 := H₂ φ
  have hg : (w₁ + w₂).toH1Function.grad =
      fun x => w₁.toH1Function.grad x + w₂.toH1Function.grad x := rfl
  rw [hg]
  simp only [vecDot_add_left]
  rw [integral_add (integrable_vecDot_of_memLp Q (memLp_two_grad Q w₁) hφ)
      (integrable_vecDot_of_memLp Q (memLp_two_grad Q w₂) hφ),
    integral_add (integrable_vecDot_of_memLp Q h₁2 hφ) (integrable_vecDot_of_memLp Q h₂2 hφ)]
  linarith only [a1, a2]

theorem flatW2p_partialSum_problem [NeZero d] (Q : TriadicCube d) {A : CoeffField d}
    (hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hAε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {G : Vec d → Vec d} (hG2 : MemLp G 2 (normalizedCubeMeasure Q))
    (x : ℕ → H10Function (openCubeSet Q))
    (h0 : CubeDirichletDivergenceProblem Q (x 0) G)
    (hs : ∀ n, CubeDirichletDivergenceProblem Q (x (n + 1)) (pert A (x n).toH1Function.grad)) :
    ∀ n, CubeDirichletDivergenceProblem Q (flatPartialSum x (n + 1))
      (fun y => G y + pert A (flatPartialSum x n).toH1Function.grad y) := by
  have hpm : ∀ F : Vec d → Vec d, MemLp F 2 (normalizedCubeMeasure Q) →
      MemLp (pert A F) 2 (normalizedCubeMeasure Q) :=
    fun F hF => (memLp_pert_and_norm_le Q hAm hε0 hAε hF).1
  intro n
  induction n with
  | zero =>
    have := flatW2p_problem_add hG2 (hpm _ (memLp_two_grad Q (x 0))) h0 (hs 0)
    simpa [flatPartialSum] using this
  | succ n ih =>
    have h1 : MemLp (fun y => G y + pert A (flatPartialSum x n).toH1Function.grad y) 2
        (normalizedCubeMeasure Q) := hG2.add (hpm _ (memLp_two_grad Q _))
    have := flatW2p_problem_add h1 (hpm _ (memLp_two_grad Q (x (n + 1)))) ih (hs (n + 1))
    have e : (fun y => (G y + pert A (flatPartialSum x n).toH1Function.grad y) +
        pert A (x (n + 1)).toH1Function.grad y) =
        fun y => G y + pert A (flatPartialSum x (n + 1)).toH1Function.grad y := by
      funext y
      rw [flatPartialSum_grad_succ, flatW2p_pert_add, add_assoc]
    rw [e] at this
    exact this

theorem flatW2p_arith {ax gx ay gy ℓ ε K Ch Cg D1 D3 : ℝ} (hℓ : 0 < ℓ) (hax : 0 ≤ ax)
    (hgx : 0 ≤ gx) (hCh : 0 ≤ Ch) (hD3 : 0 ≤ D3)
    (hKℓ : K * ℓ ≤ ε) (h1 : Ch * (D3 * ε) ≤ 1 / 4) (h2 : Cg * (D1 * ε) ≤ 1 / 4)
    (hay : ay ≤ Ch * (D3 * ε * ax + D3 * K * gx)) (hgy : gy ≤ Cg * (D1 * ε * gx)) :
    ay + ℓ⁻¹ * gy ≤ 1 / 2 * (ax + ℓ⁻¹ * gx) := by
  set γ : ℝ := ℓ⁻¹ * gx with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hgx_eq : gx = ℓ * γ := by rw [hγ]; field_simp
  have hKg : K * gx ≤ ε * γ := by
    rw [hgx_eq]
    calc K * (ℓ * γ) = (K * ℓ) * γ := by ring
      _ ≤ ε * γ := mul_le_mul_of_nonneg_right hKℓ hγ0
  have hay' : ay ≤ 1 / 4 * (ax + γ) := by
    calc ay ≤ Ch * (D3 * ε * ax + D3 * K * gx) := hay
      _ = Ch * (D3 * ε * ax + D3 * (K * gx)) := by ring
      _ ≤ Ch * (D3 * ε * ax + D3 * (ε * γ)) := by
          gcongr
      _ = (Ch * (D3 * ε)) * (ax + γ) := by ring
      _ ≤ 1 / 4 * (ax + γ) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hgy' : ℓ⁻¹ * gy ≤ 1 / 4 * γ := by
    calc ℓ⁻¹ * gy ≤ ℓ⁻¹ * (Cg * (D1 * ε * gx)) :=
          mul_le_mul_of_nonneg_left hgy (inv_nonneg.2 hℓ.le)
      _ = (Cg * (D1 * ε)) * γ := by rw [hγ]; ring
      _ ≤ 1 / 4 * γ := mul_le_mul_of_nonneg_right h2 hγ0
  linarith only [hay', hgy', hax]

theorem flatW2p_sequence [NeZero d] (hd : 2 ≤ d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤)
    {C₂ : ℝ} (hC₂ : 0 < C₂) :
    ∃ ε C₀ : ℝ, 0 < ε ∧ 0 < C₀ ∧ C₂ * ((d : ℝ) * ε) ≤ 1 / 2 ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        0 ≤ K → K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ (G : Vec d → Vec d) (DG : Fin d → Vec d → Vec d),
          MemLp G p (normalizedCubeMeasure (originCube d m)) →
          HasWeakJacobianOn (openCubeSet (originCube d m)) G DG →
          MemLp (jacobianHilbertMat DG) p (normalizedCubeMeasure (originCube d m)) →
          ∃ (x : ℕ → H10Function (openCubeSet (originCube d m)))
            (Hx : ∀ n, HasWeakHessianOn (openCubeSet (originCube d m)) (x n).toH1Function),
            CubeDirichletDivergenceProblem (originCube d m) (x 0) G ∧
            (∀ n, CubeDirichletDivergenceProblem (originCube d m) (x (n + 1))
              (pert A (x n).toH1Function.grad)) ∧
            (∀ n, MemLp (flatHessMat (Hx n)) p (normalizedCubeMeasure (originCube d m))) ∧
            (∀ n, cubeLpNorm (originCube d m) p (flatHessMat (Hx n)) ≤
              C₀ * (cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) +
                (cubeScaleFactor (originCube d m))⁻¹ * cubeLpNorm (originCube d m) p G) *
                (1 / 2) ^ n) := by
  obtain ⟨Cg0, Ch0, hCg0, hCh0, hinit⟩ := flatW2p_init_exists hd hp2 hpt
  obtain ⟨Cg, Ch, hCg, hCh, hstep⟩ := flatW2p_step_exists hd hp2 hpt
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans (by norm_num) hd)
  have hdpos : (0 : ℝ) < d := by linarith only [hd1]
  set D : ℝ := C₂ + Cg + Ch with hD
  have hD0 : 0 < D + 1 := by positivity
  set ε : ℝ := 1 / (4 * (D + 1) * (d : ℝ) ^ 3) with hεdef
  have hε : 0 < ε := by positivity
  have ht : (d : ℝ) ^ 3 * ε = 1 / (4 * (D + 1)) := by
    rw [hεdef]; field_simp
  have hdε : (d : ℝ) * ε ≤ (d : ℝ) ^ 3 * ε := by
    refine mul_le_mul_of_nonneg_right ?_ hε.le
    have h2 : 1 ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd1
    nlinarith only [h2, hdpos]
  have hq : ∀ c : ℝ, 0 ≤ c → c ≤ D + 1 → c * ((d : ℝ) * ε) ≤ 1 / 4 := by
    intro c hc hcD
    calc c * ((d : ℝ) * ε) ≤ c * ((d : ℝ) ^ 3 * ε) := mul_le_mul_of_nonneg_left hdε hc
      _ = c / (4 * (D + 1)) := by rw [ht]; ring
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [hcD]
  have hq3 : ∀ c : ℝ, 0 ≤ c → c ≤ D + 1 → c * ((d : ℝ) ^ 3 * ε) ≤ 1 / 4 := by
    intro c hc hcD
    calc c * ((d : ℝ) ^ 3 * ε) = c / (4 * (D + 1)) := by rw [ht]; ring
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [hcD]
  refine ⟨ε, Ch0 + Cg0, hε, by positivity, ?_, ?_⟩
  · have := hq C₂ hC₂.le (by linarith only [hD, hC₂, hCg, hCh])
    linarith only [this]
  intro m A K hA hAε hAK hK0 hKℓ G DG hGp hweak hJp
  set Q : TriadicCube d := originCube d m with hQ
  set ℓ : ℝ := cubeScaleFactor Q with hℓdef
  have hℓ : 0 < ℓ := cubeScaleFactor_pos' Q
  set Bf : ℝ := (Ch0 + Cg0) * (cubeLpNorm Q p (jacobianHilbertMat DG) +
    ℓ⁻¹ * cubeLpNorm Q p G) with hBf
  have hnJ : 0 ≤ cubeLpNorm Q p (jacobianHilbertMat DG) := ENNReal.toReal_nonneg
  have hnG : 0 ≤ cubeLpNorm Q p G := ENNReal.toReal_nonneg
  let X := Σ v : H10Function (openCubeSet Q), HasWeakHessianOn (openCubeSet Q) v.toH1Function
  let E : X → ℝ := fun x => cubeLpNorm Q p (flatHessMat x.2) +
    ℓ⁻¹ * cubeLpNorm Q p x.1.toH1Function.grad
  obtain ⟨s, hI0, hP, hR⟩ := exists_iterates (X := X)
    (fun x => MemLp x.1.toH1Function.grad p (normalizedCubeMeasure Q) ∧
      MemLp (flatHessMat x.2) p (normalizedCubeMeasure Q))
    (fun x => CubeDirichletDivergenceProblem Q x.1 G ∧ E x ≤ Bf)
    (fun x y => CubeDirichletDivergenceProblem Q y.1 (pert A x.1.toH1Function.grad) ∧
      E y ≤ 1 / 2 * E x)
    (by
      obtain ⟨y, Hy, hy, hyg, hyH, hgb, hHb⟩ := hinit m G DG hGp hweak hJp
      refine ⟨⟨y, Hy⟩, ⟨hyg, hyH⟩, hy, ?_⟩
      show cubeLpNorm Q p (flatHessMat Hy) + ℓ⁻¹ * cubeLpNorm Q p y.toH1Function.grad ≤ Bf
      have := mul_le_mul_of_nonneg_left hgb (inv_nonneg.2 hℓ.le)
      rw [hBf]
      have p1 : 0 ≤ Ch0 * (ℓ⁻¹ * cubeLpNorm (originCube d m) p G) := by positivity
      have p2 : 0 ≤ Cg0 * cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) := by positivity
      linarith only [hHb, this, p1, p2])
    (by
      rintro ⟨v, Hv⟩ ⟨hvg, hvH⟩
      obtain ⟨y, Hy, hy, hyg, hyH, hgb, hHb⟩ := hstep m A ε K hε.le hK0 hA hAε hAK v Hv hvg hvH
      refine ⟨⟨y, Hy⟩, ⟨hyg, hyH⟩, hy, ?_⟩
      show cubeLpNorm Q p (flatHessMat Hy) + ℓ⁻¹ * cubeLpNorm Q p y.toH1Function.grad ≤
        1 / 2 * (cubeLpNorm Q p (flatHessMat Hv) + ℓ⁻¹ * cubeLpNorm Q p v.toH1Function.grad)
      exact flatW2p_arith hℓ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hCh.le
        (by positivity) hKℓ (hq3 Ch hCh.le (by linarith only [hD, hC₂, hCg, hCh]))
        (hq Cg hCg.le (by linarith only [hD, hC₂, hCg, hCh])) hHb hgb)
  have hE : ∀ n, E (s n) ≤ Bf * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using (hI0).2
    | succ n ih =>
      calc E (s (n + 1)) ≤ 1 / 2 * E (s n) := (hR n).2
        _ ≤ 1 / 2 * (Bf * (1 / 2) ^ n) := by gcongr
        _ = Bf * (1 / 2) ^ (n + 1) := by ring
  refine ⟨fun n => (s n).1, fun n => (s n).2, hI0.1, fun n => (hR n).1, fun n => (hP n).2, ?_⟩
  intro n
  have h1 := hE n
  have h2 : 0 ≤ ℓ⁻¹ * cubeLpNorm Q p (s n).1.toH1Function.grad :=
    mul_nonneg (inv_nonneg.2 hℓ.le) ENNReal.toReal_nonneg
  have h3 : cubeLpNorm Q p (flatHessMat (s n).2) ≤ E (s n) := by
    show _ ≤ cubeLpNorm Q p (flatHessMat (s n).2) + ℓ⁻¹ * cubeLpNorm Q p (s n).1.toH1Function.grad
    linarith only [h2]
  exact h3.trans h1

end SuperdiffusionCLT.Section7
