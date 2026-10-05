/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.CorrectorCubeB
public import SuperdiffusionCLT.Section6.Lemma.RegEllipticityB

/-!
# The corrected affines of one cube

`eng_corrector_cube`: a linear family `e ↦ W e` of solutions on `□_n`, flat to order `δ` against the
affine functions `e · x`, assembled from the affine Dirichlet solutions of the basis directions.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem ea3_lpNorm_add_le (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 2 (fun x => f x + g x) ≤ cubeLpNorm Q 2 f + cubeLpNorm Q 2 g := by
  unfold cubeLpNorm
  have h : eLpNorm (fun x => f x + g x) 2 (normalizedCubeMeasure Q) ≤
      eLpNorm f 2 (normalizedCubeMeasure Q) + eLpNorm g 2 (normalizedCubeMeasure Q) :=
    eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin : eLpNorm f 2 (normalizedCubeMeasure Q) + eLpNorm g 2 (normalizedCubeMeasure Q) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.eLpNorm_lt_top.ne, hg.eLpNorm_lt_top.ne⟩
  rw [← ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono hfin h

theorem ea3_flat_add (n : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeFlat n (fun x => f x + g x) ≤ cubeFlat n f + cubeFlat n g := by
  have := ea3_prob (originCube d (n : ℤ))
  have hi1 : Integrable f (normalizedCubeMeasure (originCube d (n : ℤ))) := hf.integrable (by norm_num)
  have hi2 : Integrable g (normalizedCubeMeasure (originCube d (n : ℤ))) := hg.integrable (by norm_num)
  have hav : cubeAverage (originCube d (n : ℤ)) (fun x => f x + g x) =
      cubeAverage (originCube d (n : ℤ)) f + cubeAverage (originCube d (n : ℤ)) g := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_add hi1 hi2
  unfold cubeFlat cubeL2
  have heq : (fun x => (f x + g x) - cubeAverage (originCube d (n : ℤ)) (fun x => f x + g x)) =
      fun x => (f x - cubeAverage (originCube d (n : ℤ)) f) +
        (g x - cubeAverage (originCube d (n : ℤ)) g) := by
    funext x; rw [hav]; ring
  rw [heq, ← mul_add]
  exact mul_le_mul_of_nonneg_left (ea3_lpNorm_add_le _ (hf.sub (memLp_const _))
    (hg.sub (memLp_const _))) (by positivity)

theorem ea3_flat_smul (n : ℕ) (c : ℝ) (f : Vec d → ℝ) :
    cubeFlat n (fun x => c * f x) = |c| * cubeFlat n f := by
  have hav : cubeAverage (originCube d (n : ℤ)) (fun x => c * f x) =
      c * cubeAverage (originCube d (n : ℤ)) f := by
    unfold cubeAverage
    rw [integral_const_mul]; ring
  unfold cubeFlat cubeL2
  have heq : (fun x => c * f x - cubeAverage (originCube d (n : ℤ)) (fun x => c * f x)) =
      fun x => c * (f x - cubeAverage (originCube d (n : ℤ)) f) := by
    funext x; rw [hav]; ring
  rw [heq, HarmonicApprox.cubeLpNorm_const_mul]
  ring

theorem ea3_flat_sum {ι : Type*} (n : ℕ) (c : ι → ℝ) (z : ι → Vec d → ℝ)
    (hz : ∀ i, MemLp (z i) 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (s : Finset ι) :
    cubeFlat n (fun x => ∑ i ∈ s, c i * z i x) ≤ ∑ i ∈ s, |c i| * cubeFlat n (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold cubeFlat cubeL2 cubeAverage
    simp
  | insert j s hj ih =>
    have h1 : (fun x => ∑ i ∈ insert j s, c i * z i x) =
        fun x => c j * z j x + ∑ i ∈ s, c i * z i x := by
      funext x; rw [Finset.sum_insert hj]
    rw [h1, Finset.sum_insert hj]
    refine (ea3_flat_add n ((hz j).const_mul (c j)) ?_).trans ?_
    · exact memLp_finsetSum s fun i _ => (hz i).const_mul (c i)
    · rw [ea3_flat_smul]
      linarith only [ih]

theorem ea3_isSol_sum {a : CoeffField d} {n : ℕ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a)
    (c : Fin d → ℝ) (u : Fin d → Vec d → ℝ) (g : Fin d → Vec d → Vec d)
    (h : ∀ i, IsSolOn a (engCube d n) (u i) (g i)) (s : Finset (Fin d)) :
    IsSolOn a (engCube d n) (fun x => ∑ i ∈ s, c i * u i x) (fun x => ∑ i ∈ s, c i • g i x) := by
  classical
  have hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a :=
    ⟨lam, Lam, hEll.mono (measurableSet_openCubeSet _) (openCubeSet_subset_cubeSet _)⟩
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  | insert j s hj ih =>
    have h1 : (fun x => ∑ i ∈ insert j s, c i * u i x) =
        fun x => c j * u j x + ∑ i ∈ s, c i * u i x := by
      funext x; rw [Finset.sum_insert hj]
    have h2 : (fun x => ∑ i ∈ insert j s, c i • g i x) =
        fun x => c j • g j x + ∑ i ∈ s, c i • g i x := by
      funext x; rw [Finset.sum_insert hj]
    rw [h1, h2]
    exact IsSolOn.add hell (IsSolOn.smul (c j) (h j)) ih

theorem ea3_flat_nonneg (n : ℕ) (f : Vec d → ℝ) : 0 ≤ cubeFlat n f := by
  unfold cubeFlat cubeL2
  exact mul_nonneg (by positivity) (cubeLpNorm_nonneg _ _ _)

theorem ea3_abs_le_engNorm (e : Vec d) (i : Fin d) : |e i| ≤ engNorm e := by
  unfold engNorm
  refine Real.abs_le_sqrt ?_
  unfold vecNormSq vecDot
  exact Finset.single_le_sum (f := fun j => e j * e j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i) |>.trans' (by rw [sq])


/-- **E-A3 (the corrected affines of one cube)**, `e.sharp.Cone.corrector.flat`: a linear family
of solutions on `□_n`, flat to order `delta`. -/
theorem eng_corrector_cube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu delta : ℝ},
        IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a → 0 < lam → lam ≤ Lam →
        0 < sigma → 0 < nu →
        (∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d)) →
        HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
            (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
        delta ≤ 1 →
        ∃ W : Vec d →ₗ[ℝ] (Vec d → ℝ), ∀ e : Vec d,
          (∃ g : Vec d → Vec d, IsSolOn a (engCube d n) (W e) g) ∧
            cubeFlat n (fun x => W e x - vecDot e x) ≤ C * delta * engNorm e := by
  obtain ⟨Cb, hCb, hbasis⟩ := ea3_basis d
  refine ⟨max 1 ((d : ℝ) * Cb), le_max_left _ _, ?_⟩
  intro n lam Lam a sigma nu delta hEll h0 hle hs hnu hsym hE hd1
  have hE' := hE
  rw [HarmonicApprox.homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))]
    at hE'
  have hdel : 0 ≤ delta := (WeakFlux.l6_error_two_nonneg _
    (HarmonicApprox.paddedFamily _ hEll h0 hle) (sigma • 1) (by norm_num)).trans hE'
  have hb : ∀ i : Fin d, ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn a (engCube d n) u g ∧
        MemLp (fun x => u x - vecDot (Pi.single i 1) x) 2
          (normalizedCubeMeasure (originCube d (n : ℤ))) ∧
        cubeFlat n (fun x => u x - vecDot (Pi.single i 1) x) ≤ Cb * delta := by
    intro i
    refine hbasis n hEll h0 hle hs hnu hsym hE hd1 (Pi.single i 1) ?_
    simp [vecNormSq, vecDot, Pi.single_apply]
  choose u g hsol hmem hflat using hb
  refine ⟨{ toFun := fun e x => ∑ i, e i * u i x
            map_add' := ?_
            map_smul' := ?_ }, fun e => ⟨⟨fun x => ∑ i, e i • g i x, ?_⟩, ?_⟩⟩
  · intro e f
    funext x
    simp [add_mul, Finset.sum_add_distrib]
  · intro c e
    funext x
    simp [Finset.mul_sum, mul_assoc]
  · exact ea3_isSol_sum hEll e u g hsol Finset.univ
  · have hfun : (fun x => (∑ i, e i * u i x) - vecDot e x) =
        fun x => ∑ i, e i * (u i x - vecDot (Pi.single i 1) x) := by
      funext x
      simp [vecDot, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    show cubeFlat n (fun x => (∑ i, e i * u i x) - vecDot e x) ≤ _
    rw [hfun]
    refine (ea3_flat_sum n e (fun i x => u i x - vecDot (Pi.single i 1) x) hmem Finset.univ).trans ?_
    have hn0 : 0 ≤ engNorm e := Real.sqrt_nonneg _
    calc ∑ i, |e i| * cubeFlat n (fun x => u i x - vecDot (Pi.single i 1) x)
        ≤ ∑ i : Fin d, engNorm e * (Cb * delta) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul (ea3_abs_le_engNorm e i) (hflat i) (ea3_flat_nonneg n _) hn0
      _ = (d : ℝ) * Cb * delta * engNorm e := by simp [Finset.sum_const]; ring
      _ ≤ max 1 ((d : ℝ) * Cb) * delta * engNorm e := by
          have := le_max_right 1 ((d : ℝ) * Cb)
          gcongr


/-- Witness: for the identity field, with `σ = ν = 1`, the affine family `e ↦ (x ↦ e · x)` solves
the equation and is flat to order `0`; the field is elliptic and its symmetric part is the
identity on every cube. -/
example (d : ℕ) [NeZero d] (n : ℕ) :
    IsEllipticFieldOn 1 1 (cubeSet (originCube d (n : ℤ))) (fun _ : Vec d => (1 : Mat d)) ∧
      (∀ x ∈ cubeSet (originCube d (n : ℤ)),
        symmPart ((fun _ : Vec d => (1 : Mat d)) x) = (1 : ℝ) • (1 : Mat d)) ∧
      ∃ W : Vec d →ₗ[ℝ] (Vec d → ℝ), ∀ e : Vec d,
        (∃ g : Vec d → Vec d, IsSolOn (fun _ => (1 : Mat d)) (engCube d n) (W e) g) ∧
          cubeFlat n (fun x => W e x - vecDot e x) ≤ 1 * 0 * engNorm e := by
  refine ⟨regEllipticity_witness _, ?_, ?_⟩
  · intro x _
    show symmPart (1 : Mat d) = _
    ext i j
    by_cases h : i = j
    · subst h
      simp [symmPart]
    · simp [symmPart, h, Ne.symm h]
  · refine ⟨{ toFun := fun e x => vecDot e x
              map_add' := fun e f => by funext x; simp [vecDot, add_mul, Finset.sum_add_distrib]
              map_smul' := fun c e => by
                funext x; simp [vecDot, mul_assoc, Finset.mul_sum] }, fun e => ⟨⟨fun _ => e, ?_⟩, ?_⟩⟩
    · have h : (fun x => vecDot e x) = fun x => 0 + vecDot e x := by
        funext x; simp
      show IsSolOn _ _ (fun x => vecDot e x) _
      rw [h]
      exact isSolOn_one_affine n 0 e
    · show cubeFlat n (fun x => vecDot e x - vecDot e x) ≤ _
      simp only [sub_self, zero_mul, mul_zero]
      unfold cubeFlat cubeL2 cubeAverage
      simp

end SuperdiffusionCLT.Section6
