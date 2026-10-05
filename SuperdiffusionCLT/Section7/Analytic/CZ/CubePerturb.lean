/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.DirichletEndpoint
public import Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge
public import Homogenization.PDE.DirichletRHS
public import Homogenization.Multiscale.NormalizedNorms

/-!
# Perturbative Calderón–Zygmund on a triadic cube

For a coefficient field uniformly entrywise close to the identity, the zero-trace weak solution of
`-∇·(A∇w) = ∇·G` on a triadic cube has gradient in `L^p` whenever `G ∈ L² ∩ L^p`, with the
normalized estimate.  The proof is a Neumann iteration around the constant Laplacian
Calderón–Zygmund estimate; the iterates converge to `w` in `H¹` (an `L²` contraction) and are
bounded in `L^p`, so Fatou transfers the bound to `∇w` with no a priori `L^p` hypothesis on `∇w`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem normalizedCubeMeasure_eq_smul (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal (cubeVolume Q)⁻¹ • volume.restrict (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

theorem memLp_normalized_of_memVectorL2 (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MemVectorL2 (openCubeSet Q) f) : MemLp f 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul]
  exact MemLp.smul_measure (by simpa [MemVectorL2, volumeMeasureOn] using hf) ENNReal.ofReal_ne_top

/-- The perturbation `(A - 1) F`. -/
def pert (A : CoeffField d) (F : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul (A x - 1) (F x)

theorem norm_matVecMul_sub_one_le [NeZero d] {M : Mat d} {ε : ℝ}
    (hM : ∀ i j, |M i j - (1 : Mat d) i j| ≤ ε) (v : Vec d) :
    ‖matVecMul (M - 1) v‖ ≤ d * ε * ‖v‖ := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hM 0 0)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [matVecMul, Real.norm_eq_abs]
  calc |∑ j, (M - 1) i j * v j| ≤ ∑ j, |(M - 1) i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, ε * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using hM i j) (by simpa using norm_le_pi_norm v j)
          (abs_nonneg _) hε
    _ = d * ε * ‖v‖ := by simp [mul_assoc]

theorem ae_mem_openCubeSet (Q : TriadicCube d) :
    ∀ᵐ x ∂(normalizedCubeMeasure Q), x ∈ openCubeSet Q := by
  rw [normalizedCubeMeasure_eq_smul]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_openCubeSet Q)) _

theorem aestronglyMeasurable_pert (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {F : Vec d → Vec d} (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (pert A F) (normalizedCubeMeasure Q) := by
  refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun i => ?_)
  simp only [pert, matVecMul]
  refine (Finset.univ.aestronglyMeasurable_fun_sum fun j _ => ?_).aemeasurable
  refine AEStronglyMeasurable.mul ?_ ?_
  · have h1 : AEStronglyMeasurable (fun x => A x i j) (normalizedCubeMeasure Q) := by
      rw [normalizedCubeMeasure_eq_smul]
      exact (hA i j).smul_measure _
    have h2 : AEStronglyMeasurable (fun x => A x i j - (1 : Mat d) i j) (normalizedCubeMeasure Q) :=
      h1.sub aestronglyMeasurable_const
    simpa only [Matrix.sub_apply] using h2
  · exact (continuous_apply j).comp_aestronglyMeasurable hF

theorem memLp_pert_and_norm_le [NeZero d] (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {q : ℝ≥0∞} {F : Vec d → Vec d} (hF : MemLp F q (normalizedCubeMeasure Q)) :
    MemLp (pert A F) q (normalizedCubeMeasure Q) ∧
      cubeLpNorm Q q (pert A F) ≤ d * ε * cubeLpNorm Q q F := by
  have hnorm : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      ‖pert A F x‖ ≤ ‖((d : ℝ) * ε) • F x‖ := by
    filter_upwards [ae_mem_openCubeSet Q] with x hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_matVecMul_sub_one_le (hε x hx) (F x)
  have hm := aestronglyMeasurable_pert Q hA hF.aestronglyMeasurable
  have hmem : MemLp (pert A F) q (normalizedCubeMeasure Q) :=
    (hF.const_smul ((d : ℝ) * ε)).mono hm hnorm
  refine ⟨hmem, ?_⟩
  have h0 : 0 ≤ (d : ℝ) * ε := by positivity
  rw [cubeLpNorm, cubeLpNorm, ← smul_eq_mul]
  have h1 : eLpNorm (pert A F) q (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal ((d : ℝ) * ε) * eLpNorm F q (normalizedCubeMeasure Q) := by
    calc eLpNorm (pert A F) q (normalizedCubeMeasure Q)
        ≤ eLpNorm (((d : ℝ) * ε) • F) q (normalizedCubeMeasure Q) := eLpNorm_mono_ae hm hnorm
      _ = _ := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal h0]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.eLpNorm_lt_top.ne) h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0] at h2

theorem matVecMul_one_left (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem matVecMul_eq_add_pert (M : Mat d) (v : Vec d) :
    matVecMul M v = v + matVecMul (M - 1) v := by
  funext i
  simp [matVecMul, Matrix.sub_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib]

theorem matVecMul_sub_right (M : Mat d) (u v : Vec d) :
    matVecMul M (u - v) = matVecMul M u - matVecMul M v := by
  funext i
  simp [matVecMul, mul_sub, Finset.sum_sub_distrib]

theorem vecDot_sub_left' (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

theorem isZeroTrace_one_iff {Q : TriadicCube d} {w : H10Function (openCubeSet Q)}
    {h : Vec d → Vec d} :
    IsZeroTraceDirichletRhsWeakSolution (fun _ => (1 : Mat d)) (openCubeSet Q) w
        (fun x => -h x) ↔ CubeDirichletDivergenceProblem Q w h := by
  unfold IsZeroTraceDirichletRhsWeakSolution CubeDirichletDivergenceProblem
  simp only [matVecMul_one_left, vecDot_neg_left, integral_neg]

theorem integrable_vecDot_of_memLp (Q : TriadicCube d) {F G : Vec d → Vec d}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => vecDot (F x) (G x)) (volume.restrict (openCubeSet Q)) :=
  integrableOn_vecDot_of_memVectorL2
    (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF)
    (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hG)

theorem memLp_two_grad (Q : TriadicCube d) (w : H10Function (openCubeSet Q)) :
    MemLp w.toH1Function.grad 2 (normalizedCubeMeasure Q) :=
  memLp_normalized_of_memVectorL2 Q w.toH1Function.grad_memVectorL2

theorem grad_sub (Q : TriadicCube d) (u v : H10Function (openCubeSet Q)) :
    (u - v).toH1Function.grad = fun x => u.toH1Function.grad x - v.toH1Function.grad x := by
  change (u.toH1Function - v.toH1Function).grad = _
  rw [H1Function.sub_grad]

theorem problem_sub {Q : TriadicCube d} {w₁ w₂ : H10Function (openCubeSet Q)}
    {h₁ h₂ : Vec d → Vec d} (h₁2 : MemLp h₁ 2 (normalizedCubeMeasure Q))
    (h₂2 : MemLp h₂ 2 (normalizedCubeMeasure Q))
    (H₁ : CubeDirichletDivergenceProblem Q w₁ h₁) (H₂ : CubeDirichletDivergenceProblem Q w₂ h₂) :
    CubeDirichletDivergenceProblem Q (w₁ - w₂) (fun x => h₁ x - h₂ x) := by
  intro φ
  have hφ := memLp_two_grad Q φ
  have a1 := H₁ φ
  have a2 := H₂ φ
  rw [grad_sub]
  simp only [vecDot_sub_left']
  rw [integral_sub (integrable_vecDot_of_memLp Q (memLp_two_grad Q w₁) hφ)
      (integrable_vecDot_of_memLp Q (memLp_two_grad Q w₂) hφ),
    integral_sub (integrable_vecDot_of_memLp Q h₁2 hφ) (integrable_vecDot_of_memLp Q h₂2 hφ)]
  linarith only [a1, a2]

theorem exists_solution_cz (Q : TriadicCube d) [NeZero d] (q : ℝ≥0∞) {C : ℝ}
    (hC : ∀ f : Vec d → Vec d, MemLp f q (normalizedCubeMeasure Q) →
      ∀ u : H10Function (openCubeSet Q),
        IsZeroTraceDirichletRhsWeakSolution (fun _ : Vec d => (1 : Mat d)) (openCubeSet Q) u
          (fun x => -f x) →
        MemLp u.toH1Function.grad q (normalizedCubeMeasure Q) ∧
          cubeLpNorm Q q u.toH1Function.grad ≤ C * cubeLpNorm Q q f)
    {h : Vec d → Vec d} (h2 : MemLp h 2 (normalizedCubeMeasure Q))
    (hq : MemLp h q (normalizedCubeMeasure Q)) :
    ∃ w : H10Function (openCubeSet Q), CubeDirichletDivergenceProblem Q w h ∧
      MemLp w.toH1Function.grad q (normalizedCubeMeasure Q) ∧
        cubeLpNorm Q q w.toH1Function.grad ≤ C * cubeLpNorm Q q h := by
  obtain ⟨w, hw⟩ := exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure h2
  exact ⟨w, hw, hC h hq w (isZeroTrace_one_iff.2 hw)⟩

theorem exists_iterates {X : Type*} (P I : X → Prop) (R : X → X → Prop)
    (hinit : ∃ x, P x ∧ I x) (hstep : ∀ x, P x → ∃ y, P y ∧ R x y) :
    ∃ s : ℕ → X, I (s 0) ∧ (∀ n, P (s n)) ∧ ∀ n, R (s n) (s (n + 1)) := by
  obtain ⟨x₀, hP, hI⟩ := hinit
  have : Nonempty X := ⟨x₀⟩
  choose! f hf using hstep
  have hall : ∀ n, P (f^[n] x₀) := by
    intro n
    induction n with
    | zero => exact hP
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hf _ ih).1
  refine ⟨fun n => f^[n] x₀, hI, hall, fun n => ?_⟩
  show R (f^[n] x₀) (f^[n + 1] x₀)
  rw [Function.iterate_succ_apply']
  exact (hf _ (hall n)).2

theorem cubeLpNorm_add_le (Q : TriadicCube d) {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : Vec d → Vec d}
    (hf : MemLp f p (normalizedCubeMeasure Q)) (hg : MemLp g p (normalizedCubeMeasure Q)) :
    cubeLpNorm Q p (fun x => f x + g x) ≤ cubeLpNorm Q p f + cubeLpNorm Q p g := by
  unfold cubeLpNorm
  rw [← ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_lt_top.ne, hg.eLpNorm_lt_top.ne⟩)
    (eLpNorm_add_le hp)

theorem memLp_of_tendsto_L2_of_bdd (Q : TriadicCube d) {p : ℝ≥0∞}
    {F : ℕ → Vec d → Vec d} {F₀ : Vec d → Vec d} {B : ℝ}
    (hF : ∀ n, MemLp (F n) p (normalizedCubeMeasure Q))
    (hB : ∀ n, cubeLpNorm Q p (F n) ≤ B)
    (h0 : AEStronglyMeasurable F₀ (normalizedCubeMeasure Q))
    (hlim : Tendsto (fun n => eLpNorm (fun x => F n x - F₀ x) 2 (normalizedCubeMeasure Q))
      atTop (𝓝 0)) :
    MemLp F₀ p (normalizedCubeMeasure Q) ∧ cubeLpNorm Q p F₀ ≤ B := by
  have hB0 : 0 ≤ B := le_trans ENNReal.toReal_nonneg (hB 0)
  have hmeas : TendstoInMeasure (normalizedCubeMeasure Q) F atTop F₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hlim
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) (μ := normalizedCubeMeasure Q)
    (f := fun i => F (ns i)) (fun i => (hF (ns i)).aestronglyMeasurable) F₀ h0 hae
  have hle : eLpNorm F₀ p (normalizedCubeMeasure Q) ≤ ENNReal.ofReal B := by
    refine hfat.trans (liminf_le_of_frequently_le' (Eventually.of_forall fun i => ?_).frequently)
    exact (ENNReal.le_ofReal_iff_toReal_le (hF (ns i)).eLpNorm_lt_top.ne hB0).2 (hB (ns i))
  have hlt : eLpNorm F₀ p (normalizedCubeMeasure Q) < ⊤ := hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hlt, ?_⟩
  unfold cubeLpNorm
  calc (eLpNorm F₀ p (normalizedCubeMeasure Q)).toReal ≤ (ENNReal.ofReal B).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = B := ENNReal.toReal_ofReal hB0

theorem problem_of_A [NeZero d] (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {G : Vec d → Vec d} (hG2 : MemLp G 2 (normalizedCubeMeasure Q))
    {w : H10Function (openCubeSet Q)}
    (hw : IsZeroTraceDirichletRhsWeakSolution A (openCubeSet Q) w (fun x => -G x)) :
    CubeDirichletDivergenceProblem Q w (fun x => G x + pert A w.toH1Function.grad x) := by
  intro φ
  have hφ := memLp_two_grad Q φ
  have hP := (memLp_pert_and_norm_le Q hA hε0 hε (memLp_two_grad Q w)).1
  have e : ∀ x, vecDot (matVecMul (A x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) =
      vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) +
        vecDot (pert A w.toH1Function.grad x) (φ.toH1Function.grad x) := by
    intro x
    rw [matVecMul_eq_add_pert (A x), vecDot_add_left]
    rfl
  have h := hw φ
  simp only [e, vecDot_neg_left] at h
  rw [integral_add (integrable_vecDot_of_memLp Q (memLp_two_grad Q w) hφ)
    (integrable_vecDot_of_memLp Q hP hφ), integral_neg] at h
  simp only [vecDot_add_left]
  rw [integral_add (integrable_vecDot_of_memLp Q hG2 hφ) (integrable_vecDot_of_memLp Q hP hφ)]
  linarith only [h]

theorem l2_tendsto_of_contraction [NeZero d] (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {C₂ : ℝ}
    (hC₂ : ∀ f : Vec d → Vec d, MemLp f 2 (normalizedCubeMeasure Q) →
      ∀ u : H10Function (openCubeSet Q),
        IsZeroTraceDirichletRhsWeakSolution (fun _ : Vec d => (1 : Mat d)) (openCubeSet Q) u
          (fun x => -f x) →
        MemLp u.toH1Function.grad 2 (normalizedCubeMeasure Q) ∧
          cubeLpNorm Q 2 u.toH1Function.grad ≤ C₂ * cubeLpNorm Q 2 f)
    (hC₂0 : 0 ≤ C₂) (hcontr : C₂ * (d * ε) ≤ 1 / 2)
    {G : Vec d → Vec d} (hG2 : MemLp G 2 (normalizedCubeMeasure Q))
    {w : H10Function (openCubeSet Q)} (s : ℕ → H10Function (openCubeSet Q))
    (hw : CubeDirichletDivergenceProblem Q w (fun x => G x + pert A w.toH1Function.grad x))
    (hs : ∀ n, CubeDirichletDivergenceProblem Q (s (n + 1))
      (fun x => G x + pert A (s n).toH1Function.grad x)) :
    Tendsto (fun n => eLpNorm (fun x => (s n).toH1Function.grad x - w.toH1Function.grad x) 2
      (normalizedCubeMeasure Q)) atTop (𝓝 0) := by
  have hpert2 : ∀ F : Vec d → Vec d, MemLp F 2 (normalizedCubeMeasure Q) →
      MemLp (pert A F) 2 (normalizedCubeMeasure Q) ∧
        cubeLpNorm Q 2 (pert A F) ≤ d * ε * cubeLpNorm Q 2 F :=
    fun F hF => memLp_pert_and_norm_le Q hA hε0 hε hF
  have hfun : ∀ n, (fun x => (G x + pert A w.toH1Function.grad x) -
      (G x + pert A (s n).toH1Function.grad x)) =
      pert A (w - s n).toH1Function.grad := by
    intro n
    funext x
    simp only [pert, grad_sub, matVecMul_sub_right]
    abel
  have hrec : ∀ n, CubeDirichletDivergenceProblem Q (w - s (n + 1))
      (pert A (w - s n).toH1Function.grad) := by
    intro n
    have m1 : MemLp (fun x => G x + pert A w.toH1Function.grad x) 2 (normalizedCubeMeasure Q) :=
      hG2.add (hpert2 _ (memLp_two_grad Q w)).1
    have m2 : MemLp (fun x => G x + pert A (s n).toH1Function.grad x) 2
        (normalizedCubeMeasure Q) := hG2.add (hpert2 _ (memLp_two_grad Q (s n))).1
    have := problem_sub m1 m2 hw (hs n)
    rwa [hfun] at this
  set a : ℕ → ℝ := fun n => cubeLpNorm Q 2 (w - s n).toH1Function.grad with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  have hstep : ∀ n, a (n + 1) ≤ 1 / 2 * a n := by
    intro n
    have h1 := (hC₂ _ (hpert2 _ (memLp_two_grad Q (w - s n))).1 (w - s (n + 1))
      (isZeroTrace_one_iff.2 (hrec n))).2
    have h2 := (hpert2 _ (memLp_two_grad Q (w - s n))).2
    have h3 : C₂ * cubeLpNorm Q 2 (pert A (w - s n).toH1Function.grad) ≤ C₂ * (d * ε * a n) :=
      mul_le_mul_of_nonneg_left h2 hC₂0
    have h4 : C₂ * (d * ε * a n) ≤ 1 / 2 * a n := by
      calc C₂ * (d * ε * a n) = (C₂ * (d * ε)) * a n := by ring
        _ ≤ 1 / 2 * a n := mul_le_mul_of_nonneg_right hcontr (ha0 n)
    exact le_trans h1 (le_trans h3 h4)
  have hgeo : ∀ n, a n ≤ (1 / 2) ^ n * a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a (n + 1) ≤ 1 / 2 * a n := hstep n
        _ ≤ 1 / 2 * ((1 / 2) ^ n * a 0) := by gcongr
        _ = (1 / 2) ^ (n + 1) * a 0 := by ring
  have hlim : Tendsto a atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * a 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul_const (a 0)
    exact squeeze_zero ha0 hgeo h0
  have hnorm : ∀ n, eLpNorm (fun x => (s n).toH1Function.grad x - w.toH1Function.grad x) 2
      (normalizedCubeMeasure Q) = ENNReal.ofReal (a n) := by
    intro n
    have hm := memLp_two_grad Q (w - s n)
    have : (fun x => (s n).toH1Function.grad x - w.toH1Function.grad x) =
        -(fun x => w.toH1Function.grad x - (s n).toH1Function.grad x) := by
      funext x
      simp
    rw [this, eLpNorm_neg, ha]
    simp only [cubeLpNorm, grad_sub]
    exact (ENNReal.ofReal_toReal (by simpa only [grad_sub] using hm.eLpNorm_lt_top.ne)).symm
  simp_rw [hnorm]
  simpa using ENNReal.tendsto_ofReal hlim

/-- **CZ-PERT.** Perturbative Calderón–Zygmund on a triadic cube, for every `1 < p < ∞`. -/
theorem cubePerturbativeCZ [NeZero d] {p : ℝ≥0∞} (hp1 : 1 < p) (hpt : p < ⊤) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (Q : TriadicCube d) (A : CoeffField d),
        (∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q))) →
        (∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j| ≤ ε) →
        ∀ (G : Vec d → Vec d), MemLp G 2 (normalizedCubeMeasure Q) →
          MemLp G p (normalizedCubeMeasure Q) →
          ∀ w : H10Function (openCubeSet Q),
            IsZeroTraceDirichletRhsWeakSolution A (openCubeSet Q) w (fun x => -G x) →
            MemLp w.toH1Function.grad p (normalizedCubeMeasure Q) ∧
              cubeLpNorm Q p w.toH1Function.grad ≤ C * cubeLpNorm Q p G := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨2, by norm_num, by simp⟩ : FiniteLpExponent)
  obtain ⟨Cp, hCppos, hCp⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨p, hp1, hpt⟩ : FiniteLpExponent)
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hsum : 0 < C₂ + Cp := by linarith only [hC₂pos, hCppos]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (2 * d * (C₂ + Cp)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hdε : (d : ℝ) * ε = 1 / (2 * (C₂ + Cp)) := by
    rw [hεdef]; field_simp
  have hc2 : C₂ * (d * ε) ≤ 1 / 2 := by
    rw [hdε, mul_one_div, div_le_iff₀ (by positivity)]
    linarith only [hCppos]
  have hcp : Cp * (d * ε) ≤ 1 / 2 := by
    rw [hdε, mul_one_div, div_le_iff₀ (by positivity)]
    linarith only [hC₂pos]
  have hdε0 : 0 ≤ (d : ℝ) * ε := by positivity
  refine ⟨ε, 2 * Cp, hεpos, by positivity, ?_⟩
  intro Q A hA hAε G hG2 hGp w hw
  have hGn : 0 ≤ cubeLpNorm Q p G := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ 2 * Cp * cubeLpNorm Q p G := by positivity
  have hprob := problem_of_A Q hA hεpos.le hAε hG2 hw
  have hstep : ∀ v : H10Function (openCubeSet Q),
      (MemLp v.toH1Function.grad p (normalizedCubeMeasure Q) ∧
        cubeLpNorm Q p v.toH1Function.grad ≤ 2 * Cp * cubeLpNorm Q p G) →
      ∃ y : H10Function (openCubeSet Q),
        (MemLp y.toH1Function.grad p (normalizedCubeMeasure Q) ∧
          cubeLpNorm Q p y.toH1Function.grad ≤ 2 * Cp * cubeLpNorm Q p G) ∧
        CubeDirichletDivergenceProblem Q y (fun x => G x + pert A v.toH1Function.grad x) := by
    rintro v ⟨hv, hvB⟩
    obtain ⟨hP2, -⟩ := memLp_pert_and_norm_le Q hA hεpos.le hAε (memLp_two_grad Q v)
    obtain ⟨hPp, hPn⟩ := memLp_pert_and_norm_le Q hA hεpos.le hAε hv
    have m2 : MemLp (fun x => G x + pert A v.toH1Function.grad x) 2 (normalizedCubeMeasure Q) :=
      hG2.add hP2
    have mp : MemLp (fun x => G x + pert A v.toH1Function.grad x) p (normalizedCubeMeasure Q) :=
      hGp.add hPp
    obtain ⟨y, hy, hyp, hyn⟩ := exists_solution_cz Q p (hCp Q) m2 mp
    refine ⟨y, ⟨hyp, ?_⟩, hy⟩
    have h1 := cubeLpNorm_add_le Q hp1.le hGp hPp
    have h2 : cubeLpNorm Q p (pert A v.toH1Function.grad) ≤
        d * ε * (2 * Cp * cubeLpNorm Q p G) :=
      hPn.trans (mul_le_mul_of_nonneg_left hvB hdε0)
    have h3 : Cp * (d * ε) * (2 * Cp * cubeLpNorm Q p G) ≤
        1 / 2 * (2 * Cp * cubeLpNorm Q p G) := mul_le_mul_of_nonneg_right hcp hB0
    have h4 : cubeLpNorm Q p (fun x => G x + pert A v.toH1Function.grad x) ≤
        cubeLpNorm Q p G + d * ε * (2 * Cp * cubeLpNorm Q p G) := h1.trans (by linarith only [h2])
    have h5 := mul_le_mul_of_nonneg_left h4 hCppos.le
    nlinarith only [hyn, h5, h3]
  obtain ⟨s, -, hsP, hsR⟩ := exists_iterates
    (X := H10Function (openCubeSet Q))
    (fun v => MemLp v.toH1Function.grad p (normalizedCubeMeasure Q) ∧
      cubeLpNorm Q p v.toH1Function.grad ≤ 2 * Cp * cubeLpNorm Q p G)
    (fun y => CubeDirichletDivergenceProblem Q y G)
    (fun v y => CubeDirichletDivergenceProblem Q y (fun x => G x + pert A v.toH1Function.grad x))
    (by
      obtain ⟨y, hy, hyp, hyn⟩ := exists_solution_cz Q p (hCp Q) hG2 hGp
      exact ⟨y, ⟨hyp, by nlinarith only [hyn, hCppos, hGn]⟩, hy⟩)
    hstep
  have hlim := l2_tendsto_of_contraction Q hA hεpos.le hAε (hC₂ Q) hC₂pos.le hc2 hG2 s hprob hsR
  exact memLp_of_tendsto_L2_of_bdd Q (F := fun n => (s n).toH1Function.grad)
    (F₀ := w.toH1Function.grad) (B := 2 * Cp * cubeLpNorm Q p G) (fun n => (hsP n).1)
    (fun n => (hsP n).2) (memLp_two_grad Q w).aestronglyMeasurable hlim

end SuperdiffusionCLT.Section7
