/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Response.JUpperBound
public import SuperdiffusionCLT.AKHC61.Response.CenteredResponses
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import Mathlib.Probability.Moments.Variance

/-!
# Package D2a: the arithmetic of the Step 2 `J`-bound

Source: Step 2 of the proof of Theorem 6.1 of [AK]
(`e.pq.bounds.prime`, `e.Enaught.vs.Ahom.prime(.one)`, the `EJ.minus.PQ` display).

For the cutoff law, at a parent scale `k` and child scale `k - ell` (the paper's `L` is `ell`
here; `L` is the cutoff index), with the geometric-mean special vectors `p_e, q_e` of package B1
and the centering term `½ p₀·q₀`, `p₀ = σ̄*⁻¹_k q_e - p_e`, `q₀ = q_e - σ̄_k p_e` (the paper's
`½ P·Q`), the route-W `J`-bound reads

`E J(cu_k, p_e, q_e) - ½ p₀·q₀ ≤ C(d) (σ δ^{1/2} Θ_k^{1/2} + 3^{-ell} Θ_k^{1/2} + (Θ_k W)^{1/2} + W)`,

where `W = σ̄_k E[G²] + σ̄*⁻¹_k E[F²]` is the route-W weak-norm energy: `G`, `F` are
`CoarseGraining`'s `s = 1/2` gradient and flux weak norms of the response maximizer, centered at
`p₀`, `q₀`. This file proves the elementary ingredients of that bound, which the weak-norm
packages (`AKHC61/WeakNorms`) and the Step 3 recursion consume:

* `akhcJB_expectedJ_originCube_eq`: the expected response at an origin cube is the scalar
  quadratic form in `σ̄*⁻¹_n` and `σ̄_n` (no cross term under `ShellLawJ4`);
* `akhcJB_tau_term_le`, `akhcJB_osc_term_le`, `akhcJB_linear_term_le`: the bounds on the
  `τ̄_{k,k-ell}` term, the oscillation term and the linear terms (with Jensen,
  `akhcJB_integral_le_sqrt_integral_sq`);
* supporting real-variable lemmas (`akhcJB_param`, `akhcJB_mul_sqrt_le_sqrt`,
  `akhcJB_sqrt_mul_sqrt_le`).

In route W the printed `E₀`-vs-`Ahom` averages do not enter the `J`-bound: `CoarseGraining`'s
div-curl bound carries no `M₀`-weighted average term. They are the average/mismatch terms of the
weak-norm maximizer bound, consumed by the weak-norm estimate (package C6).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

open Homogenization MeasureTheory

noncomputable section

theorem akhcJB_integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, f x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  by_cases hf : Integrable f μ
  · have hmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2
    have hvar := ProbabilityTheory.variance_nonneg f μ
    rw [ProbabilityTheory.variance_eq_sub hmem] at hvar
    have h : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
      have hpow : (∫ x, (f ^ 2) x ∂μ) = ∫ x, f x ^ 2 ∂μ := rfl
      linarith only [hvar, hpow]
    calc ∫ x, f x ∂μ ≤ |∫ x, f x ∂μ| := le_abs_self _
      _ = Real.sqrt ((∫ x, f x ∂μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := Real.sqrt_le_sqrt h
  · rw [integral_undef hf]
    exact Real.sqrt_nonneg _

theorem akhcJB_norm_le_one {d : ℕ} {e : Vec d} (he : vecNormSq e = 1) : ‖e‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have hi : e i * e i ≤ vecNormSq e := by
    unfold vecNormSq vecDot
    exact Finset.single_le_sum (f := fun j => e j * e j) (fun j _ => mul_self_nonneg (e j))
      (Finset.mem_univ i)
  rw [he] at hi
  have h := Real.abs_le_sqrt (x := e i) (y := 1) (by rw [sq]; exact hi)
  rw [Real.sqrt_one] at h
  rw [Real.norm_eq_abs]
  exact h

theorem akhcJB_norm_smul_le {d : ℕ} {e : Vec d} (he : vecNormSq e = 1) (x : ℝ) :
    ‖x • e‖ ≤ |x| := by
  rw [norm_smul, Real.norm_eq_abs]
  have h := akhcJB_norm_le_one he
  calc |x| * ‖e‖ ≤ |x| * 1 := mul_le_mul_of_nonneg_left h (abs_nonneg x)
    _ = |x| := mul_one _

/-- Evaluation of the scalar quadratic form at the special vectors `r⁻¹ • e`, `r • e`. -/
theorem akhcJB_quadratic_special {d : ℕ} {e : Vec d} (he : vecNormSq e = 1) {r : ℝ}
    (hr : 0 < r) (α β : ℝ) :
    (1 / 2 : ℝ) * vecDot (r • e) (α • (r • e)) - vecDot (r⁻¹ • e) (r • e) +
        (1 / 2 : ℝ) * vecDot (r⁻¹ • e) (β • (r⁻¹ • e)) =
      (1 / 2 : ℝ) * α * (r * r) - 1 + (1 / 2 : ℝ) * β * (r⁻¹ * r⁻¹) := by
  have he' : vecDot e e = 1 := he
  simp only [vecDot_smul_left, vecDot_smul_right, he']
  simp only [mul_one]
  rw [mul_inv_cancel₀ hr.ne']
  ring

theorem akhcJB_rpow_half_mul_self {c : ℝ} (hc : 0 < c) :
    c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c := by
  rw [← Real.rpow_add hc]
  norm_num

theorem akhcJB_rpow_neg_half {c : ℝ} (hc : 0 < c) :
    c ^ (-(1 / 2 : ℝ)) = (c ^ (1 / 2 : ℝ))⁻¹ :=
  Real.rpow_neg hc.le _

/-- The geometric-mean parametrization: with `c = √(B/A)` and `u = √(B A)`,
`A c = u` and `B = u c`. -/
theorem akhcJB_param {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * Real.sqrt (B / A) = Real.sqrt (B * A) ∧
      B = Real.sqrt (B * A) * Real.sqrt (B / A) := by
  constructor
  · have h : B * A = (A * A) * (B / A) := by field_simp
    rw [h, Real.sqrt_mul (mul_self_nonneg A), Real.sqrt_mul_self hA.le]
  · rw [← Real.sqrt_mul (mul_nonneg hB.le hA.le)]
    have h : B * A * (B / A) = B * B := by field_simp
    rw [h, Real.sqrt_mul_self hB.le]

/-! ## Pure real arithmetic for the four terms of the route-W right-hand side -/

/-- `x √G ≤ √Z` from `x² G ≤ Z`. -/
theorem akhcJB_mul_sqrt_le_sqrt {x G Z : ℝ} (hx : 0 ≤ x) (h : x * x * G ≤ Z) :
    x * Real.sqrt G ≤ Real.sqrt Z := by
  calc x * Real.sqrt G = Real.sqrt (x * x) * Real.sqrt G := by rw [Real.sqrt_mul_self hx]
    _ = Real.sqrt (x * x * G) := (Real.sqrt_mul (mul_self_nonneg x) G).symm
    _ ≤ Real.sqrt Z := Real.sqrt_le_sqrt h

/-- The additivity-defect term: `2 (1+b) √τ √EJ ≤ 4 (1+2^d) σ √δ u`. -/
theorem akhcJB_tau_term_le (d : ℕ) {b τ EJ u δ σ : ℝ} (hb : b ≤ 2 ^ d)
    (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hsmall : δ * σ ^ 2 ≤ 1) (hu : 0 ≤ u)
    (hτ : τ ≤ δ * σ ^ 2 * u) (hEJ : EJ ≤ (1 + δ * σ ^ 2) * u - 1) :
    2 * (1 + b) * (Real.sqrt τ * Real.sqrt EJ) ≤ 4 * (1 + 2 ^ d) * (σ * Real.sqrt δ * u) := by
  have hη : 0 ≤ δ * σ ^ 2 := mul_nonneg hδ (sq_nonneg σ)
  have hηu : δ * σ ^ 2 * u ≤ 1 * u := mul_le_mul_of_nonneg_right hsmall hu
  have hEJ2 : EJ ≤ 2 * u := by linarith only [hEJ, hηu]
  have hsqrtη : Real.sqrt (δ * σ ^ 2) = σ * Real.sqrt δ := by
    rw [Real.sqrt_mul hδ, Real.sqrt_sq hσ, mul_comm]
  have h4 : Real.sqrt (4 * (δ * σ ^ 2)) = 2 * (σ * Real.sqrt δ) := by
    rw [Real.sqrt_mul (by norm_num), hsqrtη, show (4 : ℝ) = 2 * 2 by norm_num,
      Real.sqrt_mul_self (by norm_num)]
  have hprod : Real.sqrt τ * Real.sqrt EJ ≤ 2 * (σ * Real.sqrt δ) * u := by
    calc Real.sqrt τ * Real.sqrt EJ
        ≤ Real.sqrt (δ * σ ^ 2 * u) * Real.sqrt (2 * u) :=
          mul_le_mul (Real.sqrt_le_sqrt hτ) (Real.sqrt_le_sqrt hEJ2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * (δ * σ ^ 2) * (u * u)) := by
          rw [← Real.sqrt_mul (mul_nonneg hη hu)]
          ring_nf
      _ = Real.sqrt (2 * (δ * σ ^ 2)) * u := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hη), Real.sqrt_mul_self hu]
      _ ≤ Real.sqrt (4 * (δ * σ ^ 2)) * u :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith only [hη])) hu
      _ = 2 * (σ * Real.sqrt δ) * u := by rw [h4]
  have hL0 : 0 ≤ Real.sqrt τ * Real.sqrt EJ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcoef : 2 * (1 + b) ≤ 2 * (1 + 2 ^ d) := by linarith only [hb]
  have hR0 : 0 ≤ 2 * (1 + (2 : ℝ) ^ d) := by positivity
  calc 2 * (1 + b) * (Real.sqrt τ * Real.sqrt EJ)
      ≤ 2 * (1 + 2 ^ d) * (2 * (σ * Real.sqrt δ) * u) :=
        mul_le_mul hcoef hprod hL0 hR0
    _ = 4 * (1 + 2 ^ d) * (σ * Real.sqrt δ * u) := by ring

/-- The cutoff-oscillation term: `(8 g b) t (u - 1) ≤ 8 g 2^d (t u)`. -/
theorem akhcJB_osc_term_le (d : ℕ) {g b t u : ℝ} (hg : 0 ≤ g) (hb0 : 0 ≤ b) (hb : b ≤ 2 ^ d)
    (ht : 0 ≤ t) (hu : 1 ≤ u) :
    8 * g * b * t * (u - 1) ≤ 8 * g * 2 ^ d * (t * u) := by
  have h1 : 8 * g * b * t * (u - 1) ≤ 8 * g * b * t * u :=
    mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
  have h2 : 8 * g * b * t * u ≤ 8 * g * 2 ^ d * t * u := by
    have hgb : 8 * g * b ≤ 8 * g * 2 ^ d := mul_le_mul_of_nonneg_left hb (by positivity)
    have htu : 0 ≤ t * u := mul_nonneg ht (by linarith only [hu])
    calc 8 * g * b * t * u = 8 * g * b * (t * u) := by ring
      _ ≤ 8 * g * 2 ^ d * (t * u) := mul_le_mul_of_nonneg_right hgb htu
      _ = 8 * g * 2 ^ d * t * u := by ring
  calc 8 * g * b * t * (u - 1) ≤ 8 * g * 2 ^ d * t * u := h1.trans h2
    _ = 8 * g * 2 ^ d * (t * u) := by ring

/-- One linear weak-norm term: `½ n (c I) ≤ ½ K √Z` from `I ≤ √G`, `n² G ≤ Z`. -/
theorem akhcJB_linear_term_le {n c K I G Z : ℝ} (hn : 0 ≤ n) (hc0 : 0 ≤ c) (hc : c ≤ K)
    (hI : I ≤ Real.sqrt G) (hZ : n * n * G ≤ Z) :
    (1 / 2 : ℝ) * n * (c * I) ≤ (1 / 2 : ℝ) * K * Real.sqrt Z := by
  have hn2 : 0 ≤ (1 / 2 : ℝ) * n := by positivity
  have hsq := akhcJB_mul_sqrt_le_sqrt hn hZ
  have hK : 0 ≤ K := hc0.trans hc
  calc (1 / 2 : ℝ) * n * (c * I) ≤ (1 / 2 : ℝ) * n * (c * Real.sqrt G) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI hc0) hn2
    _ ≤ (1 / 2 : ℝ) * n * (K * Real.sqrt G) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg G)) hn2
    _ = (1 / 2 : ℝ) * K * (n * Real.sqrt G) := by ring
    _ ≤ (1 / 2 : ℝ) * K * Real.sqrt Z := mul_le_mul_of_nonneg_left hsq (by positivity)

/-- The product term: `√G √F ≤ B G + A F` when `B A ≥ 1`. -/
theorem akhcJB_sqrt_mul_sqrt_le {A B G F : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : 1 ≤ B * A)
    (hG : 0 ≤ G) (hF : 0 ≤ F) :
    Real.sqrt G * Real.sqrt F ≤ B * G + A * F := by
  have hx : 0 ≤ B * G := mul_nonneg hB hG
  have hy : 0 ≤ A * F := mul_nonneg hA hF
  have h1 : 1 * (G * F) ≤ (B * A) * (G * F) := mul_le_mul_of_nonneg_right hBA (mul_nonneg hG hF)
  have h2 : (B * A) * (G * F) = (B * G) * (A * F) := by ring
  have h3 : (B * G + A * F) * (B * G + A * F) =
      (B * G) * (B * G) + 2 * ((B * G) * (A * F)) + (A * F) * (A * F) := by ring
  have hxx := mul_nonneg hx hx
  have hyy := mul_nonneg hy hy
  have hxy := mul_nonneg hx hy
  have hle : G * F ≤ (B * G + A * F) * (B * G + A * F) := by
    linarith only [h1, h2, h3, hxx, hyy, hxy]
  rw [← Real.sqrt_mul hG]
  calc Real.sqrt (G * F) ≤ Real.sqrt ((B * G + A * F) * (B * G + A * F)) := Real.sqrt_le_sqrt hle
    _ = B * G + A * F := Real.sqrt_mul_self (add_nonneg hx hy)

/-! ## The dimension-only constants -/

/-- The linear-term cutoff constant of `CoarseGraining`'s
`section53_linearCutoffCoeff_le_dimensional`. -/
noncomputable def akhcJB_linConst (d : ℕ) : ℝ :=
  (d : ℝ) *
    ((3 : ℝ) ^ ((d : ℝ) + 1) *
      ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d))

/-- The product-term cutoff constant of `CoarseGraining`'s
`section53CutoffProductCoeff_origin_le_dimensional`. -/
noncomputable def akhcJB_prodConst (d : ℕ) [NeZero d] : ℝ :=
  ((128 * quantitativeCubeCutoffHessianConst d +
          24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
    (((d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
      ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1))

/-- The constant `C(d)` of the route-W Step 2 `J`-bound. -/
noncomputable def akhcJB_const (d : ℕ) [NeZero d] : ℝ :=
  4 * (1 + 2 ^ d) + 8 * quantitativeCubeCutoffGradientConst d * 2 ^ d +
    akhcJB_linConst d + akhcJB_prodConst d

/-! ## The route-W interface objects at scale `k` -/

/-- The gradient centering vector `p₀ = σ̄*⁻¹_k q_e - p_e`, the expected spatial average of the
gradient of the response maximizer at the special vectors (`P` in Step 2 of the paper). -/
noncomputable def akhc_step2P0 {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (k : ℕ)
    (e : Vec d) : Vec d :=
  SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P k •
      SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e -
    SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e

/-- The flux centering vector `q₀ = q_e - σ̄_k p_e` (`Q` in Step 2 of the paper). -/
noncomputable def akhc_step2Q0 {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (k : ℕ)
    (e : Vec d) : Vec d :=
  SuperdiffusionCLT.AKHC61.Response.akhc_specialQ nu L P k e -
    SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P k •
      SuperdiffusionCLT.AKHC61.Response.akhc_specialP nu L P k e

section Law

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
        (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                  omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                  X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet
                  (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- The expected response at an origin cube is the scalar quadratic form in
`σ̄*⁻¹_n` and `σ̄_n` (no cross term under `ShellLawJ4`). -/
theorem akhcJB_expectedJ_originCube_eq (n : ℕ) (p q : Vec d) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet
        (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (n : ℤ)) p q =
      (1 / 2 : ℝ) *
          vecDot q (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n • q) -
        vecDot p q +
        (1 / 2 : ℝ) *
          vecDot p (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n • p) := by
  have hP := SuperdiffusionCLT.Section2.Annealed.restrictionLawCarrier_cutoffLaw hnu L P
  have hBlock :=
    SuperdiffusionCLT.AKHC61.Response.akhc_integrable_coarseFullBlockMatrixAtCube_cutoffLaw
      d hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 (originCube d (n : ℤ))
  have hraw :=
    hP.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
      (originCube d (n : ℤ)) p q hBlock
  have hLL : (Homogenization.Book.Ch04.annealedBlockMatrix
      (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
      (cubeSet (originCube d (n : ℤ)))).lowerLeft = 0 := by
    rw [← SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_eq_ch04 hnu L P
      (originCube d (n : ℤ))]
    exact SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_originCube_lowerLeft_eq_zero
      hnu L hJ4 (n : ℤ)
  have hUL : (Homogenization.Book.Ch04.annealedBlockMatrix
      (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
      (cubeSet (originCube d (n : ℤ)))).upperLeft =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu L P n) • (1 : Mat d) := by
    rw [← SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_eq_ch04 hnu L P
      (originCube d (n : ℤ)),
      SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar
        hnu L hJ4 (n : ℤ)]
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBar_originCube_eq_smul_one hnu L hJ4
      (n : ℤ)
  have hLR : (Homogenization.Book.Ch04.annealedBlockMatrix
      (SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P)
      (cubeSet (originCube d (n : ℤ)))).lowerRight =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n) • (1 : Mat d) := by
    rw [← SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix_eq_ch04 hnu L P
      (originCube d (n : ℤ))]
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInv_originCube_eq_smul_one hnu L
      hJ4 (n : ℤ)
  have hone : ∀ x : Vec d, Homogenization.matVecMul (1 : Mat d) x = x := fun x =>
    Matrix.one_mulVec x
  unfold Homogenization.Book.Ch04.expectedResponseJCubeSet
  have hzero : Homogenization.matVecMul (0 : Mat d) p = 0 := Matrix.zero_mulVec p
  rw [hraw, hLL, hUL, hLR, hzero, vecDot_zero_right,
    sub_zero, Homogenization.smul_matVecMul, Homogenization.smul_matVecMul, hone, hone]

end Law

end

end SuperdiffusionCLT.AKHC61.Step2
