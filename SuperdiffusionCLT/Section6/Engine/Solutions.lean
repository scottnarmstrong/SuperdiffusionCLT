/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import Homogenization.Sobolev.Foundations.MeanZero
public import Homogenization.Sobolev.PotentialSolenoidalL2
public import Homogenization.CoarseGraining.MuRecovery.Setup
public import Homogenization.CoarseGraining.ThetaEllipticity

/-!
# Solutions on open sets: calculus

Restriction, sums, multiples, constants, the zero and affine solutions, and the passage between
solutions on origin cubes and on Euclidean balls.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

private theorem e0a_finite {V : Set (Vec d)} (hfin : volume V ≠ ⊤) :
    IsFiniteMeasure (volumeMeasureOn V) :=
  ⟨by simpa [volumeMeasureOn, Measure.restrict_apply_univ] using hfin.lt_top⟩

private theorem e0a_cube_finite (n : ℕ) : volume (engCube d n) ≠ ⊤ :=
  (volume_openCubeSet_lt_top _).ne

theorem IsSolOn.mono {a : CoeffField d} {U V : Set (Vec d)} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) (hfin : volume V ≠ ⊤)
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam V a)
    (h : IsSolOn a U u g) : IsSolOn a V u g := by
  have := e0a_finite hfin
  obtain ⟨v, hv1, hv2⟩ := h
  obtain ⟨lam, Lam, hE⟩ := hell
  refine ⟨⟨v.toH1.restrict hV hVU,
    v.isHarmonic.restrict_of_isOpen_of_isEllipticFieldOn hU hV hVU hE⟩, ?_, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset hVU hv1
  · exact ae_restrict_of_ae_restrict_of_subset hVU hv2

private theorem e0a_add_harm {a : CoeffField d} {U : Set (Vec d)}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam U a)
    (v w : AHarmonicFunction a U) :
    IsAHarmonicGradient a U (v.toH1 + w.toH1).grad := by
  obtain ⟨lam, Lam, hEll⟩ := hell
  have key : ∀ z : H1Function U, h10FluxIntegrable U (fun x => matVecMul (a x) (z.grad x)) := by
    intro z φ
    have hF := memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      (MeasureTheory.MemLp.of_eval fun i => z.gradMemL2 i)
    have hcoord : ∀ i : Fin d,
        MeasureTheory.IntegrableOn
          (fun x => matVecMul (a x) (z.grad x) i * φ.toH1Function.grad x i) U :=
      fun i => (hF.eval i).integrable_mul (φ.toH1Function.gradMemL2 i)
    have hsum : (fun x => vecDot (matVecMul (a x) (z.grad x)) (φ.toH1Function.grad x)) =
        fun x => ∑ i : Fin d, matVecMul (a x) (z.grad x) i * φ.toH1Function.grad x i := rfl
    rw [hsum]
    exact MeasureTheory.integrable_finsetSum _ fun i _ => hcoord i
  exact isAHarmonicGradient_add_of_integrable v.isHarmonic w.isHarmonic (key v.toH1) (key w.toH1)

theorem IsSolOn.add {a : CoeffField d} {U : Set (Vec d)} {u₁ u₂ : Vec d → ℝ}
    {g₁ g₂ : Vec d → Vec d} (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam U a)
    (h₁ : IsSolOn a U u₁ g₁) (h₂ : IsSolOn a U u₂ g₂) :
    IsSolOn a U (fun x => u₁ x + u₂ x) (fun x => g₁ x + g₂ x) := by
  obtain ⟨v, hv1, hv2⟩ := h₁
  obtain ⟨w, hw1, hw2⟩ := h₂
  refine ⟨⟨v.toH1 + w.toH1, e0a_add_harm hell v w⟩, ?_, ?_⟩
  · filter_upwards [hv1, hw1] with x hx hy
    simp [hx, hy]
  · filter_upwards [hv2, hw2] with x hx hy
    simp [hx, hy]

theorem IsSolOn.smul {a : CoeffField d} {U : Set (Vec d)} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (c : ℝ) (h : IsSolOn a U u g) :
    IsSolOn a U (fun x => c * u x) (fun x => c • g x) := by
  obtain ⟨v, hv1, hv2⟩ := h
  refine ⟨⟨c • v.toH1, isAHarmonicGradient_smul v.isHarmonic c⟩, ?_, ?_⟩
  · filter_upwards [hv1] with x hx
    simp [hx]
  · filter_upwards [hv2] with x hx
    simp [hx]

theorem IsSolOn.sub {a : CoeffField d} {U : Set (Vec d)} {u₁ u₂ : Vec d → ℝ}
    {g₁ g₂ : Vec d → Vec d} (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam U a)
    (h₁ : IsSolOn a U u₁ g₁) (h₂ : IsSolOn a U u₂ g₂) :
    IsSolOn a U (fun x => u₁ x - u₂ x) (fun x => g₁ x - g₂ x) := by
  have h := IsSolOn.add hell h₁ (IsSolOn.smul (-1) h₂)
  convert h using 2 <;> simp [sub_eq_add_neg]

theorem IsSolOn.add_const {a : CoeffField d} {U : Set (Vec d)} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hU : volume U ≠ ⊤) (c : ℝ) (h : IsSolOn a U u g) :
    IsSolOn a U (fun x => u x + c) g := by
  have := e0a_finite hU
  obtain ⟨v, hv1, hv2⟩ := h
  have hgrad : (v.toH1 + H1Function.const (U := U) c).grad = v.toH1.grad := by
    funext x
    simp
  refine ⟨⟨v.toH1 + H1Function.const (U := U) c, hgrad ▸ v.isHarmonic⟩, ?_, ?_⟩
  · filter_upwards [hv1] with x hx
    simp [hx]
  · filter_upwards [hv2] with x hx
    rw [hgrad]
    exact hx

private theorem e0a_memLp_cube {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (engCube d n))) :
    MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
  memL2On_openCubeSet_normalizedCubeMeasure hf

private theorem e0a_engNorm_memLp {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict U)) :
    MemLp (fun x => engNorm (F x)) 2 (volume.restrict U) := by
  have hcont : Continuous (fun e : Vec d => engNorm e) :=
    Real.continuous_sqrt.comp continuous_vecNormSq
  have hmeas : AEStronglyMeasurable (fun x => engNorm (F x)) (volume.restrict U) :=
    hcont.comp_aestronglyMeasurable hF.aestronglyMeasurable
  have hsum : MemLp (fun x => ∑ i : Fin d, |F x i|) 2 (volume.restrict U) :=
    memLp_finsetSum Finset.univ fun i _ => (hF.eval i).abs
  refine hsum.of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ engNorm (F x) := Real.sqrt_nonneg _
  have h1 : 0 ≤ ∑ i : Fin d, |F x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg h1]
  unfold engNorm
  refine Real.sqrt_le_iff.2 ⟨h1, ?_⟩
  unfold vecNormSq vecDot
  calc ∑ i, F x i * F x i = ∑ i, |F x i| * |F x i| :=
        Finset.sum_congr rfl fun i _ => (abs_mul_abs_self _).symm
    _ ≤ (∑ i, |F x i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum (f := fun j => |F x i| * |F x j|)
          (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)

theorem IsSolOn.memLp {a : CoeffField d} {n : ℕ} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsSolOn a (engCube d n) u g) :
    MemLp u 2 (normalizedCubeMeasure (originCube d (n : ℤ))) ∧
      MemLp (fun x => engNorm (g x)) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  obtain ⟨v, hv1, hv2⟩ := h
  refine ⟨e0a_memLp_cube (v.toH1.memL2.ae_eq hv1), e0a_memLp_cube ?_⟩
  have hvec : MemLp v.toH1.grad 2 (volume.restrict (engCube d n)) :=
    MeasureTheory.MemLp.of_eval fun i => v.toH1.gradMemL2 i
  exact e0a_engNorm_memLp (hvec.ae_eq hv2)

private theorem e0a_affine_harmonic {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hsobd : IsSobolevRegularDomain U) (hvol : (volume U).toReal ≠ 0) (p : Vec d) :
    IsAHarmonicGradient (fun _ : Vec d => (1 : Mat d)) U (fun _ : Vec d => p) := by
  refine ⟨⟨H1Function.affineOnIsSobolevRegularDomain hsobd p, ?_⟩, ?_⟩
  · funext x
    simp
  · have hconst : IsSolenoidalOn U (fun _ : Vec d => p) :=
      IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain hsobd hvol p
    simpa [matVecMul_one] using hconst

/-- Affine functions solve the Laplace equation on every origin cube. -/
theorem isSolOn_one_affine (n : ℕ) (c : ℝ) (p : Vec d) :
    IsSolOn (fun _ => (1 : Mat d)) (engCube d n) (fun x => c + vecDot p x) (fun _ => p) := by
  have := e0a_finite (e0a_cube_finite (d := d) n)
  have hsobd : IsSobolevRegularDomain (engCube d n) :=
    isSobolevRegularDomain_openCubeSet_originCube_recovery (d := d) (n : ℤ)
  have hvol : (volume (engCube d n)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos _).ne'
  have hgrad : (H1Function.affineOnIsSobolevRegularDomain hsobd p +
      H1Function.const (U := engCube d n) c).grad = fun _ => p := by
    funext x
    simp
  refine ⟨⟨H1Function.affineOnIsSobolevRegularDomain hsobd p +
      H1Function.const (U := engCube d n) c, hgrad ▸ e0a_affine_harmonic hsobd hvol p⟩, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    simp [vecDot, add_comm]
  · exact Filter.Eventually.of_forall fun x => congrFun hgrad x

private theorem e0a_zero_dim (hd : d = 0) {a : CoeffField d} {U : Set (Vec d)}
    (hfin : volume U ≠ ⊤) (u : Vec d → ℝ) (g : Vec d → Vec d) : IsSolOn a U u g := by
  subst hd
  have := e0a_finite hfin
  have hg : (H1Function.const (U := U) (u 0)).grad = g := by
    funext x
    exact Subsingleton.elim _ _
  have h0 : (H1Function.const (U := U) (u 0)).grad = 0 := rfl
  refine ⟨⟨H1Function.const (U := U) (u 0), h0 ▸ isAHarmonicGradient_zero⟩, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => congrArg u (Subsingleton.elim _ _)
  · exact Filter.Eventually.of_forall fun x => congrFun hg x

private theorem e0a_mem_cube {n : ℕ} {x : Vec d} :
    x ∈ engCube d n ↔ ∀ i, -((3 : ℝ) ^ n / 2) < x i ∧ x i < (3 : ℝ) ^ n / 2 := by
  have hs : cubeScaleFactor (originCube d (n : ℤ)) = (3 : ℝ) ^ n := by
    simp
  refine forall_congr' fun i => ?_
  change ((((0 : ℤ) : ℝ) - 1 / 2) * cubeScaleFactor (originCube d (n : ℤ)) < x i ∧
      x i < (((0 : ℤ) : ℝ) + 1 / 2) * cubeScaleFactor (originCube d (n : ℤ))) ↔ _
  rw [hs, Int.cast_zero]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

private theorem e0a_cube_sub_ball [NeZero d] (n : ℕ) :
    engCube d n ⊆ Metric.ball (0 : Vec d) ((3 : ℝ) ^ n / 2) := by
  intro x hx
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by positivity)]
  intro i
  have h := e0a_mem_cube.1 hx i
  rw [Real.norm_eq_abs, abs_lt]
  exact h

private theorem e0a_ball_sub_cube {R : ℝ} {n : ℕ} (hR : 0 < R) (hn : 2 * R ≤ (3 : ℝ) ^ n) :
    euclidBall (d := d) R ⊆ engCube d n := by
  intro x hx
  refine e0a_mem_cube.2 fun i => ?_
  have h1 : x i ^ 2 < R ^ 2 := lt_of_le_of_lt (sq_apply_le_vecNormSq x i) hx
  have h3 := abs_lt.1 (abs_lt_of_sq_lt_sq h1 hR.le)
  constructor <;> linarith only [h3.1, h3.2, hn]

/-- A solution on a ball is a solution on every origin cube inside it, and conversely. -/
theorem IsSolOn.cube_of_ball {a : CoeffField d} {R : ℝ} {n : ℕ} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hn : Real.sqrt d * (3 : ℝ) ^ n ≤ 2 * R) (h : IsBallSolution a R u g) :
    IsSolOn a (engCube d n) u g := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exact e0a_zero_dim hd (e0a_cube_finite n) u g
  · have : NeZero d := ⟨hd.ne'⟩
    have hsub : engCube d n ⊆ euclidBall R := by
      refine (e0a_cube_sub_ball n).trans ?_
      refine ball_subset_euclidBall.trans (euclidBall_mono (by positivity) ?_)
      linarith only [hn]
    exact IsSolOn.mono (isOpen_euclidBall R) (isOpen_openCubeSet _) hsub
      (e0a_cube_finite n) hell h

theorem IsSolOn.ball_of_cube {a : CoeffField d} {R : ℝ} {n : ℕ} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (euclidBall R) a)
    (hR : 0 < R) (hn : 2 * R ≤ (3 : ℝ) ^ n) (h : IsSolOn a (engCube d n) u g) :
    IsBallSolution a R u g :=
  IsSolOn.mono (isOpen_openCubeSet _) (isOpen_euclidBall R) (e0a_ball_sub_cube hR hn)
    (volume_euclidBall_ne_top hR) hell h

/-- Witness: the zero function. -/
example (a : CoeffField d) (n : ℕ) : IsSolOn a (engCube d n) (fun _ => 0) (fun _ => 0) :=
  ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

end SuperdiffusionCLT.Section6
