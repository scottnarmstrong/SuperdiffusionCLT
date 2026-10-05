/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pE

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}` on the half cube: the divergence form

For a smooth coefficient field `A` with `A - 1` small and `∇A` of size `K ≤ ε 3^{-m}` on the half
cube `flatHalfCube e m`, a zero-trace weak solution `w` of `-∇·(A∇w) = ∇·G` with `G` carrying a weak
Jacobian in `L̲^p`, `2 ≤ p < ∞`, has a weak Hessian in `L̲^p` up to the flat face, with
`‖∇²w‖ ≤ C (‖∇G‖ + 3^{-m} ‖G‖)`.  The proof is the Neumann series of the cube, around the Laplacian
on the half cube whose inverse is built by odd reflection.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem hc_partialSum_problem [NeZero d] (e : Fin d) (m : ℤ) {A : CoeffField d}
    (hAm : ∀ i j, Continuous (fun x => A x i j))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hAε : ∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {G : Vec d → Vec d} (hG2 : MemLp G 2 (flatHalfMeasure e m))
    (x : ℕ → H10Function (flatHalfCube e m))
    (h0 : HalfDivProblem e m (x 0) G)
    (hs : ∀ n, HalfDivProblem e m (x (n + 1)) (pert A (x n).toH1Function.grad)) :
    ∀ n, HalfDivProblem e m (flatPartialSum x (n + 1))
      (fun y => G y + pert A (flatPartialSum x n).toH1Function.grad y) := by
  have hpm : ∀ F : Vec d → Vec d, MemLp F 2 (flatHalfMeasure e m) →
      MemLp (pert A F) 2 (flatHalfMeasure e m) :=
    fun F hF => (hc_memLp_pert_and_norm_le e m hAm hε0 hAε hF).1
  intro n
  induction n with
  | zero =>
    have := hc_problem_add hG2 (hpm _ (hc_gradL2 e m (x 0))) h0 (hs 0)
    simpa [flatPartialSum] using this
  | succ n ih =>
    have h1 : MemLp (fun y => G y + pert A (flatPartialSum x n).toH1Function.grad y) 2
        (flatHalfMeasure e m) := hG2.add (hpm _ (hc_gradL2 e m _))
    have := hc_problem_add h1 (hpm _ (hc_gradL2 e m (x (n + 1)))) ih (hs (n + 1))
    have e : (fun y => (G y + pert A (flatPartialSum x n).toH1Function.grad y) +
        pert A (x (n + 1)).toH1Function.grad y) =
        fun y => G y + pert A (flatPartialSum x (n + 1)).toH1Function.grad y := by
      funext y
      rw [flatPartialSum_grad_succ, flatW2p_pert_add, add_assoc]
    rw [e] at this
    exact this


theorem hc_sequence [NeZero d] (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤)
    {C₂ : ℝ} (hC₂ : 0 < C₂) :
    ∃ ε C₀ : ℝ, 0 < ε ∧ 0 < C₀ ∧ C₂ * ((d : ℝ) * ε) ≤ 1 / 2 ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ flatHalfCube e m, ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        0 ≤ K → K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ (G : Vec d → Vec d) (DG : Fin d → Vec d → Vec d),
          MemLp G p (flatHalfMeasure e m) →
          HasWeakJacobianOn (flatHalfCube e m) G DG →
          MemLp (jacobianHilbertMat DG) p (flatHalfMeasure e m) →
          ∃ (x : ℕ → H10Function (flatHalfCube e m))
            (Hx : ∀ n, HasWeakHessianOn (flatHalfCube e m) (x n).toH1Function),
            HalfDivProblem e m (x 0) G ∧
            (∀ n, HalfDivProblem e m (x (n + 1))
              (pert A (x n).toH1Function.grad)) ∧
            (∀ n, MemLp (flatHessMat (Hx n)) p (flatHalfMeasure e m)) ∧
            (∀ n, flatHalfNorm e m p (flatHessMat (Hx n)) ≤
              C₀ * (flatHalfNorm e m p (jacobianHilbertMat DG) +
                (cubeScaleFactor (originCube d m))⁻¹ * flatHalfNorm e m p G) *
                (1 / 2) ^ n) := by
  obtain ⟨Cg0, Ch0, hCg0, hCh0, hinit⟩ := hc_base_div hd e hp2 hpt
  obtain ⟨Cg, Ch, hCg, hCh, hstep⟩ := hc_step_exists hd e hp2 hpt
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
  set ℓ : ℝ := cubeScaleFactor (originCube d m) with hℓdef
  have hℓ : 0 < ℓ := cubeScaleFactor_pos' (originCube d m)
  set Bf : ℝ := (Ch0 + Cg0) * (flatHalfNorm e m p (jacobianHilbertMat DG) +
    ℓ⁻¹ * flatHalfNorm e m p G) with hBf
  have hnJ : 0 ≤ flatHalfNorm e m p (jacobianHilbertMat DG) := ENNReal.toReal_nonneg
  have hnG : 0 ≤ flatHalfNorm e m p G := ENNReal.toReal_nonneg
  let X := Σ v : H10Function (flatHalfCube e m), HasWeakHessianOn (flatHalfCube e m) v.toH1Function
  let E : X → ℝ := fun x => flatHalfNorm e m p (flatHessMat x.2) +
    ℓ⁻¹ * flatHalfNorm e m p x.1.toH1Function.grad
  obtain ⟨s, hI0, hP, hR⟩ := exists_iterates (X := X)
    (fun x => MemLp x.1.toH1Function.grad p (flatHalfMeasure e m) ∧
      MemLp (flatHessMat x.2) p (flatHalfMeasure e m))
    (fun x => HalfDivProblem e m x.1 G ∧ E x ≤ Bf)
    (fun x y => HalfDivProblem e m y.1 (pert A x.1.toH1Function.grad) ∧
      E y ≤ 1 / 2 * E x)
    (by
      obtain ⟨y, Hy, hy, hyg, hyH, hgb, hHb⟩ := hinit m G DG hGp hweak hJp
      refine ⟨⟨y, Hy⟩, ⟨hyg, hyH⟩, hy, ?_⟩
      show flatHalfNorm e m p (flatHessMat Hy) + ℓ⁻¹ * flatHalfNorm e m p y.toH1Function.grad ≤ Bf
      have := mul_le_mul_of_nonneg_left hgb (inv_nonneg.2 hℓ.le)
      rw [hBf]
      have p1 : 0 ≤ Ch0 * (ℓ⁻¹ * flatHalfNorm e m p G) := by positivity
      have p2 : 0 ≤ Cg0 * flatHalfNorm e m p (jacobianHilbertMat DG) := by positivity
      linarith only [hHb, this, p1, p2])
    (by
      rintro ⟨v, Hv⟩ ⟨hvg, hvH⟩
      obtain ⟨y, Hy, hy, hyg, hyH, hgb, hHb⟩ := hstep m A ε K hε.le hK0 hA hAε hAK v Hv hvg hvH
      refine ⟨⟨y, Hy⟩, ⟨hyg, hyH⟩, hy, ?_⟩
      show flatHalfNorm e m p (flatHessMat Hy) + ℓ⁻¹ * flatHalfNorm e m p y.toH1Function.grad ≤
        1 / 2 * (flatHalfNorm e m p (flatHessMat Hv) + ℓ⁻¹ * flatHalfNorm e m p v.toH1Function.grad)
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
  have h2 : 0 ≤ ℓ⁻¹ * flatHalfNorm e m p (s n).1.toH1Function.grad :=
    mul_nonneg (inv_nonneg.2 hℓ.le) ENNReal.toReal_nonneg
  have h3 : flatHalfNorm e m p (flatHessMat (s n).2) ≤ E (s n) := by
    show _ ≤ flatHalfNorm e m p (flatHessMat (s n).2) + ℓ⁻¹ * flatHalfNorm e m p (s n).1.toH1Function.grad
    linarith only [h2]
  exact h3.trans h1

/-- **Flat `W^{2,p}` on the half cube, divergence form.**  On the half cube
`{x ∈ (-3^m/2, 3^m/2)^d : 0 < x e}`, a smooth coefficient field close to the identity with
`3^m ‖∇A‖ ≤ ε` and a zero-trace solution `w` of `-∇·(A∇w) = ∇·G` with `G` carrying a weak Jacobian
in `L̲^p` has a weak Hessian in `L̲^p` up to the flat face `x e = 0`. -/
theorem flatW2p_halfCube_divergence (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (hpt : p < ⊤) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (K : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ flatHalfCube e m, ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        K * cubeScaleFactor (originCube d m) ≤ ε →
        ∀ (G : Vec d → Vec d) (DG : Fin d → Vec d → Vec d),
          MemLp G p (flatHalfMeasure e m) →
          HasWeakJacobianOn (flatHalfCube e m) G DG →
          MemLp (jacobianHilbertMat DG) p (flatHalfMeasure e m) →
          ∀ w : H10Function (flatHalfCube e m),
            IsZeroTraceDirichletRhsWeakSolution A (flatHalfCube e m) w (fun x => -G x) →
            ∃ H : HasWeakHessianOn (flatHalfCube e m) w.toH1Function,
              MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) p
                (flatHalfMeasure e m) ∧
              flatHalfNorm e m p (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
                C * (flatHalfNorm e m p (jacobianHilbertMat DG) +
                  (cubeScaleFactor (originCube d m))⁻¹ * flatHalfNorm e m p G) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hc_grad_estimate hd e (p := 2) (le_refl _) (by norm_num)
  obtain ⟨ε, C₀, hε, hC₀, hcontr, hseq⟩ := hc_sequence hd e hp2 hpt hC₂pos
  refine ⟨ε, 2 * C₀, hε, by positivity, ?_⟩
  intro m A K hA hAε hAK hKℓ G DG hGp hweak hJp w hw
  have hK0 : 0 ≤ K :=
    (abs_nonneg _).trans (hAK _ (flatHalfCube_nonempty e m).some_mem 0 0 0)
  have hG2 : MemLp G 2 (flatHalfMeasure e m) := hGp.mono_exponent hp2
  have hAc : ∀ i j, Continuous (fun x => A x i j) := fun i j => (hA i j).continuous
  obtain ⟨x, Hx, h0, hs, hHp, hHb⟩ := hseq m A K hA hAε hAK hK0 hKℓ G DG hGp hweak hJp
  have hprob := hc_problem_of_A e m hAc hε.le hAε hG2 hw
  have hS := hc_partialSum_problem e m hAc hε.le hAε hG2 x h0 hs
  have hlim := hc_l2_tendsto_of_contraction e m hAc hε.le hAε (hC₂ m) hC₂pos.le hcontr hG2
    (flatPartialSum x) hprob hS
  obtain ⟨H, hHmem, hHbd⟩ := hc_hessian_of_series e m hp2 hpt x Hx hHp hHb w hlim
  refine ⟨H, hHmem, ?_⟩
  have : 2 * (C₀ * (flatHalfNorm e m p (jacobianHilbertMat DG) +
      (cubeScaleFactor (originCube d m))⁻¹ * flatHalfNorm e m p G)) =
      2 * C₀ * (flatHalfNorm e m p (jacobianHilbertMat DG) +
      (cubeScaleFactor (originCube d m))⁻¹ * flatHalfNorm e m p G) := by ring
  rw [← this]
  exact hHbd

end SuperdiffusionCLT.Section7
