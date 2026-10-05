/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalB
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocal
public import SuperdiffusionCLT.Section7.Prereq.WhitneyInterpolantC
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaC

/-!
# The local oscillation estimate on one translated cube

For a weak solution `u` on an open set `W` and a cube `z + □_n ⊆ W`, if the dual bound for the weak
gradient holds for solutions on `□_n` of the (transferred) field, then the squared oscillation of `u`
about its average on `z + □_n` is at most `2 (C 3^n)^2` times the dual bound squared:
`wh2_osc_cube`, the squared form of the chain of the paper
(dual fractional Poincare, then the right-hand side lemma).  Also the geometric fact that an open
translated cube inside the open cube `cu_m` has its half-open translate inside `cubeSet cu_m`
(`wh2_shift_image_subset`).  Also the bounded overlap `27^d` of the averaging cubes `z + □_n` on
the grid `3^{n-3} ℤ^d` (`wh2_sum_osc_le`), and the choice of the mesoscale (`wh2_scale_exists`,
`wh2_isBigO_max`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The squared normalized `L²` norm on a cube is the volume-normalized lintegral. -/
theorem wh2_lintegral_cube_eq (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : AEMeasurable g (volume.restrict (openCubeSet Q))) :
    ∫⁻ x in openCubeSet Q, ENNReal.ofReal (g x ^ 2) =
      volume (cubeSet Q) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 g ^ 2 := by
  unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := normalizedCubeMeasure Q) (f := g) (p := 2)
    (by norm_num)
  have hg' : AEStronglyMeasurable g (normalizedCubeMeasure Q) := by
    unfold normalizedCubeMeasure cubeMeasure
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hg.aestronglyMeasurable.smul_measure _
  have h2 : eLpNorm g 2 (normalizedCubeMeasure Q) ^ (2 : ℝ) =
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂normalizedCubeMeasure Q := by
    simpa using h hg'
  have hn : ∀ x, ‖g x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (g x ^ 2) := by
    intro x
    rw [ENNReal.rpow_two, ← ofReal_norm, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp only [hn] at h2
  rw [ENNReal.rpow_two] at h2
  rw [h2, normalizedCubeMeasure, lintegral_smul_measure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet, smul_eq_mul, ← mul_assoc,
    mul_comm (volume (cubeSet Q))]
  have hv : volume (cubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [← volume_cubeSet_toReal, ENNReal.ofReal_toReal (volume_cubeSet_lt_top Q).ne]
  rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (cubeVolume_pos Q).le),
    inv_mul_cancel₀ (cubeVolume_pos Q).ne', ENNReal.ofReal_one, one_mul]

theorem wh2_lintegral_translate (U : Set (Vec d)) (z : Vec d) (F : Vec d → ℝ≥0∞) :
    ∫⁻ y in U, F (y + z) = ∫⁻ x in translateSet z U, F x :=
  (measurePreserving_addRight_restrict_translateSet z U).lintegral_comp_emb
    (Homeomorph.addRight z).measurableEmbedding F

theorem wh2_enorm_sq_add_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 2) (by norm_num)
  have e : ((2 : ℝ≥0∞) ^ ((2 : ℝ) - 1)) = 2 := by norm_num
  rw [e] at h
  simpa [ENNReal.rpow_two] using h

instance wh2_isProb (Q : TriadicCube d) : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
  ⟨by simp⟩

theorem wh2_aemeasurable_eucNorm {U : Set (Vec d)} (v : H1Function U) :
    AEMeasurable (fun x => eucNorm (v.grad x)) (volume.restrict U) := by
  unfold eucNorm vecNormSq vecDot
  have h : AEMeasurable (fun x => ∑ i : Fin d, v.grad x i * v.grad x i)
      (volume.restrict U) :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
      ((v.gradMemL2 i).aestronglyMeasurable.aemeasurable.mul (v.gradMemL2 i).aestronglyMeasurable.aemeasurable)
  exact h.sqrt

theorem wh2_aemeasurable_translate {W : Set (Vec d)} {V : Set (Vec d)} (z : Vec d)
    (hsub : translateSet z V ⊆ W) {f : Vec d → ℝ} (hf : AEMeasurable f (volume.restrict W)) :
    AEMeasurable (fun x => f (x + z)) (volume.restrict V) := by
  have h1 : AEMeasurable f (volume.restrict (translateSet z V)) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  exact AEMeasurable.comp_quasiMeasurePreserving h1
    (measurePreserving_addRight_restrict_translateSet z V).quasiMeasurePreserving

/-- **The local oscillation estimate on one translated cube** (deterministic core).  If the dual
bound `hDual` holds for the solutions on `□_n` of the field `a'` (to which the translated field is
transferred by `hbr`), then the squared oscillation of `u` on `z + □_n` is bounded by the
gradient and the right-hand side. -/
theorem wh2_osc_cube (d : ℕ) [NeZero d] :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (n : ℕ) {W : Set (Vec d)} (z : Vec d),
      translateSet z (openCubeSet (originCube d (n : ℤ))) ⊆ W →
      ∀ {a a' : CoeffField d} {u : H1Function W} {f : Vec d → ℝ},
      AEMeasurable f (volume.restrict W) →
      IsWeakSolutionOn a W u f (fun _ => 0) →
      (∀ (v : H1Function (openCubeSet (originCube d (n : ℤ)))) (g : Vec d → ℝ),
        IsWeakSolutionOn (fun x => a (x + z)) (openCubeSet (originCube d (n : ℤ))) v g
            (fun _ => 0) →
          IsWeakSolutionOn a' (openCubeSet (originCube d (n : ℤ))) v g (fun _ => 0)) →
      ∀ (A Bf : ℝ) (q : ℝ≥0∞), q ≤ 2 →
      (∀ (v : H1Function (openCubeSet (originCube d (n : ℤ)))) (g : Vec d → ℝ),
        IsWeakSolutionOn a' (openCubeSet (originCube d (n : ℤ))) v g (fun _ => 0) →
          ENNReal.ofReal
              (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
                (1 / 4) v.grad) ≤
            ENNReal.ofReal A *
                SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
                  (fun x => eucNorm (v.grad x)) +
              ENNReal.ofReal Bf *
                SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) q g) →
      ∫⁻ x in translateSet z (openCubeSet (originCube d (n : ℤ))),
          ENNReal.ofReal
            ((u.toFun x - cubeAverage (originCube d (n : ℤ)) (fun y => u.toFun (y + z))) ^ 2) ≤
        2 * ENNReal.ofReal (Cp * (3 : ℝ) ^ n) ^ 2 *
          (ENNReal.ofReal A ^ 2 *
              (∫⁻ x in translateSet z (openCubeSet (originCube d (n : ℤ))),
                ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
            ENNReal.ofReal Bf ^ 2 *
              ∫⁻ x in translateSet z (openCubeSet (originCube d (n : ℤ))),
                ENNReal.ofReal (f x ^ 2)) := by
  obtain ⟨Cp, hCp, hP⟩ := wh2_poincare_dual_enorm d
  refine ⟨Cp, hCp, ?_⟩
  intro n W z hsub a a' u f hf hsol hbr A Bf q hq hDual
  set Q := originCube d (n : ℤ) with hQ
  set v := wh2_cubeFun Q z hsub u with hv
  have hvsol : IsWeakSolutionOn a' (openCubeSet Q) v (fun x => f (x + z)) (fun _ => 0) :=
    hbr v _ (wh2_isWeakSolutionOn_cube Q z hsub hsol)
  have hf' : AEMeasurable (fun x => f (x + z)) (volume.restrict (openCubeSet Q)) :=
    wh2_aemeasurable_translate z hsub hf
  have hvm : AEMeasurable (fun x => v.toFun x) (volume.restrict (openCubeSet Q)) :=
    v.memL2.aestronglyMeasurable.aemeasurable
  set c := cubeAverage Q (fun y => u.toFun (y + z)) with hc
  have hE := hP n v
  have hD := hDual v _ hvsol
  have hF : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q (fun x => f (x + z)) ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 (fun x => f (x + z)) :=
    eLpNorm_le_eLpNorm_of_exponent_le hq
  set P := ENNReal.ofReal (Cp * (3 : ℝ) ^ n) with hPdef
  set G := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 (fun x => eucNorm (v.grad x))
    with hG
  set F2 := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 (fun x => f (x + z)) with hF2
  set E := SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
    (fun x => v x - cubeAverage Q (fun x => v x)) with hEdef
  have hE2 : E ≤ P * (ENNReal.ofReal A * G + ENNReal.ofReal Bf * F2) := by
    refine hE.trans ?_
    gcongr
    refine hD.trans ?_
    gcongr
  have hE3 : E ^ 2 ≤ 2 * P ^ 2 * (ENNReal.ofReal A ^ 2 * G ^ 2 + ENNReal.ofReal Bf ^ 2 * F2 ^ 2) := by
    calc E ^ 2 ≤ (P * (ENNReal.ofReal A * G + ENNReal.ofReal Bf * F2)) ^ 2 := by gcongr
      _ = P ^ 2 * (ENNReal.ofReal A * G + ENNReal.ofReal Bf * F2) ^ 2 := by rw [mul_pow]
      _ ≤ P ^ 2 * (2 * ((ENNReal.ofReal A * G) ^ 2 + (ENNReal.ofReal Bf * F2) ^ 2)) := by
          gcongr
          exact wh2_enorm_sq_add_le _ _
      _ = _ := by rw [mul_pow, mul_pow]; ring
  have hLHS : ∫⁻ x in translateSet z (openCubeSet Q), ENNReal.ofReal ((u.toFun x - c) ^ 2) =
      volume (cubeSet Q) * E ^ 2 := by
    rw [← wh2_lintegral_translate (openCubeSet Q) z
      (fun x => ENNReal.ofReal ((u.toFun x - c) ^ 2))]
    have := wh2_lintegral_cube_eq Q (g := fun x => v x - cubeAverage Q (fun x => v x))
      (hvm.sub_const _)
    exact this
  have hG2 : ∫⁻ x in translateSet z (openCubeSet Q), ENNReal.ofReal (eucNorm (u.grad x) ^ 2) =
      volume (cubeSet Q) * G ^ 2 := by
    rw [← wh2_lintegral_translate (openCubeSet Q) z
      (fun x => ENNReal.ofReal (eucNorm (u.grad x) ^ 2))]
    exact wh2_lintegral_cube_eq Q (g := fun x => eucNorm (v.grad x)) (wh2_aemeasurable_eucNorm v)
  have hF22 : ∫⁻ x in translateSet z (openCubeSet Q), ENNReal.ofReal (f x ^ 2) =
      volume (cubeSet Q) * F2 ^ 2 := by
    rw [← wh2_lintegral_translate (openCubeSet Q) z (fun x => ENNReal.ofReal (f x ^ 2))]
    exact wh2_lintegral_cube_eq Q (g := fun x => f (x + z)) hf'
  rw [hLHS, hG2, hF22]
  calc volume (cubeSet Q) * E ^ 2
      ≤ volume (cubeSet Q) * (2 * P ^ 2 * (ENNReal.ofReal A ^ 2 * G ^ 2 +
          ENNReal.ofReal Bf ^ 2 * F2 ^ 2)) := by gcongr
    _ = _ := by ring

theorem wh2_mem_openCube {x : Vec d} {j : ℤ} :
    x ∈ openCubeSet (originCube d j) ↔ ∀ i, |x i| < (3 : ℝ) ^ j / 2 := by
  unfold openCubeSet
  simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add,
    Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  rw [abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

theorem wh2_mem_cubeSet {x : Vec d} {j : ℤ} :
    x ∈ cubeSet (originCube d j) ↔ ∀ i, -((3 : ℝ) ^ j / 2) ≤ x i ∧ x i < (3 : ℝ) ^ j / 2 := by
  unfold cubeSet
  simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add,
    Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

theorem wh2_shift_bounds (n m : ℕ) (z : Vec d)
    (h : translateSet z (openCubeSet (originCube d (n : ℤ))) ⊆ openCubeSet (originCube d (m : ℤ)))
    (i : Fin d) :
    z i + (3 : ℝ) ^ n / 2 ≤ (3 : ℝ) ^ m / 2 ∧ -((3 : ℝ) ^ m / 2) ≤ z i - (3 : ℝ) ^ n / 2 := by
  have hn : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have key : ∀ s : ℝ, |s| < (3 : ℝ) ^ n / 2 → |z i + s| < (3 : ℝ) ^ m / 2 := by
    intro s hs
    have hp : (z + Pi.single i s) ∈ translateSet z (openCubeSet (originCube d (n : ℤ))) := by
      rw [mem_translateSet_iff_sub_mem, add_sub_cancel_left, wh2_mem_openCube]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hs
      · simp only [Pi.single_apply, hj, ite_false, abs_zero]
        have : (3 : ℝ) ^ ((n : ℤ)) = (3 : ℝ) ^ n := by simp
        rw [this]
        positivity
    have := (wh2_mem_openCube.1 (h hp)) i
    simpa using this
  constructor
  · by_contra hc
    replace hc := not_le.1 hc
    set δ := z i + (3 : ℝ) ^ n / 2 - (3 : ℝ) ^ m / 2 with hδ
    have hδ0 : 0 < δ := by linarith only [hc, hδ]
    set ε := min δ ((3 : ℝ) ^ n / 4) with hε
    have hε0 : 0 < ε := lt_min hδ0 (by positivity)
    have hε1 : ε ≤ δ := min_le_left _ _
    have hε2 : ε ≤ (3 : ℝ) ^ n / 4 := min_le_right _ _
    have := key ((3 : ℝ) ^ n / 2 - ε) (by
      rw [abs_lt]; constructor <;> linarith only [hε0, hε2, hn])
    rw [abs_lt] at this
    linarith only [this.2, hε1, hδ]
  · by_contra hc
    replace hc := not_le.1 hc
    set δ := -((3 : ℝ) ^ m / 2) - (z i - (3 : ℝ) ^ n / 2) with hδ
    have hδ0 : 0 < δ := by linarith only [hc, hδ]
    set ε := min δ ((3 : ℝ) ^ n / 4) with hε
    have hε0 : 0 < ε := lt_min hδ0 (by positivity)
    have hε1 : ε ≤ δ := min_le_left _ _
    have hε2 : ε ≤ (3 : ℝ) ^ n / 4 := min_le_right _ _
    have := key (-((3 : ℝ) ^ n / 2 - ε)) (by
      rw [abs_lt]; constructor <;> linarith only [hε0, hε2, hn])
    rw [abs_lt] at this
    linarith only [this.1, hε1, hδ]

theorem wh2_shift_image_subset (n m : ℕ) (z : Vec d)
    (h : translateSet z (openCubeSet (originCube d (n : ℤ))) ⊆ openCubeSet (originCube d (m : ℤ))) :
    (fun x => z + x) '' cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [wh2_mem_cubeSet] at hw ⊢
  intro i
  have hb := wh2_shift_bounds n m z h i
  have e3 : (3 : ℝ) ^ ((n : ℤ)) = (3 : ℝ) ^ n := by simp
  have e4 : (3 : ℝ) ^ ((m : ℤ)) = (3 : ℝ) ^ m := by simp
  have := hw i
  rw [e3] at this
  rw [e4]
  simp only [Pi.add_apply]
  constructor <;> linarith only [hb.1, hb.2, this.1, this.2]

theorem wh2_mem_translate_iff (n : ℕ) (k : Fin d → ℤ) (x : Vec d) :
    x ∈ translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) (openCubeSet (originCube d (n : ℤ))) ↔
      ∀ i, |x i - (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)| < 27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2 := by
  rw [mem_translateSet_iff_sub_mem, wh2_mem_openCube]
  have e : (3 : ℝ) ^ ((n : ℤ)) = 27 * (3 : ℝ) ^ ((n : ℤ) - 3) := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
    field_simp
  simp only [Pi.sub_apply, e]

open scoped Classical in
theorem wh2_card_le (n : ℕ) (x : Vec d) (Z : Finset (Fin d → ℤ)) :
    (Z.filter (fun k : Fin d → ℤ => x ∈ translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
      (openCubeSet (originCube d (n : ℤ))))).card ≤ 27 ^ d := by
  classical
  set h : ℝ := (3 : ℝ) ^ ((n : ℤ) - 3) with hh
  have hh0 : 0 < h := by positivity
  set I : Fin d → Finset ℤ := fun i =>
    Finset.Icc (⌊x i / h - 27 / 2⌋ + 1) (⌊x i / h - 27 / 2⌋ + 27) with hI
  have hsub : (Z.filter (fun k : Fin d → ℤ => x ∈ translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
      (openCubeSet (originCube d (n : ℤ))))) ⊆ Fintype.piFinset I := by
    intro k hk
    rw [Finset.mem_filter, wh2_mem_translate_iff] at hk
    rw [Fintype.mem_piFinset]
    intro i
    have h1 := hk.2 i
    rw [← hh, abs_lt] at h1
    have h2 : x i / h - 27 / 2 < (k i : ℝ) := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hh0]
      linarith only [h1.2]
    have h3 : (k i : ℝ) < x i / h - 27 / 2 + 27 := by
      have : (k i : ℝ) * h < x i + 27 * h / 2 := by linarith only [h1.1]
      have h4 : (k i : ℝ) < (x i + 27 * h / 2) / h := by rw [lt_div_iff₀ hh0]; exact this
      have e : (x i + 27 * h / 2) / h = x i / h - 27 / 2 + 27 := by field_simp; ring
      rwa [e] at h4
    rw [hI]
    simp only [Finset.mem_Icc]
    constructor
    · have := Int.floor_le (x i / h - 27 / 2)
      have h5 : ⌊x i / h - 27 / 2⌋ < k i := by
        have : (⌊x i / h - 27 / 2⌋ : ℝ) < k i := lt_of_le_of_lt this h2
        exact_mod_cast this
      omega
    · have h5 := Int.lt_floor_add_one (x i / h - 27 / 2)
      have h6 : (k i : ℝ) < (⌊x i / h - 27 / 2⌋ : ℝ) + 28 := by linarith only [h3, h5]
      have h7 : k i < ⌊x i / h - 27 / 2⌋ + 28 := by exact_mod_cast h6
      omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  have : ∀ i, (I i).card = 27 := by
    intro i
    rw [hI]
    simp
  simp [this]

open scoped Classical in
/-- **Bounded overlap of the averaging cubes**: the sum over a finite set of grid cubes of the
integral of a function is at most `27^d` times its integral over any set containing them. -/
theorem wh2_sum_lintegral_le (n : ℕ) (Z : Finset (Fin d → ℤ)) {W : Set (Vec d)}
    (hZ : ∀ k ∈ Z, translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
      (openCubeSet (originCube d (n : ℤ))) ⊆ W)
    {g : Vec d → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict W)) :
    ∑ k ∈ Z, ∫⁻ x in translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
      (openCubeSet (originCube d (n : ℤ))), g x ≤ 27 ^ d * ∫⁻ x in W, g x := by
  set B : (Fin d → ℤ) → Set (Vec d) := fun k =>
    translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
      (openCubeSet (originCube d (n : ℤ))) with hB
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (wh2_isOpen_translateSet (isOpen_openCubeSet _) _).measurableSet
  have e1 : ∀ k ∈ Z, ∫⁻ x in B k, g x = ∫⁻ x in W, (B k).indicator g x := by
    intro k hk
    rw [lintegral_indicator (hBm k), Measure.restrict_restrict (hBm k),
      Set.inter_eq_left.2 (hZ k hk)]
  rw [Finset.sum_congr rfl e1, ← lintegral_finsetSum' _ (fun k _ => hg.indicator (hBm k))]
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => ?_
  have e2 : ∑ k ∈ Z, (B k).indicator g x = (Z.filter (fun k => x ∈ B k)).card • g x := by
    rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const]
  rw [e2, nsmul_eq_mul]
  have := wh2_card_le n x Z
  gcongr
  exact_mod_cast this

theorem wh2_box_eq (n : ℕ) (k : Fin d → ℤ) :
    wh1_box (wh1_pt ((3 : ℝ) ^ ((n : ℤ) - 3)) k) (27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2) =
      translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
        (openCubeSet (originCube d (n : ℤ))) := by
  ext x
  rw [wh2_mem_translate_iff]
  rfl

/-- The averaging cube of the grid point `k`. -/
def wh2_B (n : ℕ) (k : Fin d → ℤ) : Set (Vec d) :=
  translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) (openCubeSet (originCube d (n : ℤ)))

/-- The summed local estimate over a finite family of grid cubes inside `W`. -/
theorem wh2_sum_osc_le (n : ℕ) (Z : Finset (Fin d → ℤ)) {W : Set (Vec d)}
    (hZ : ∀ k ∈ Z, wh2_B n k ⊆ W)
    {G F : Vec d → ℝ≥0∞} (hG : AEMeasurable G (volume.restrict W))
    (hF : AEMeasurable F (volume.restrict W)) (u : Vec d → ℝ) (c : (Fin d → ℤ) → ℝ)
    (P2 A2 B2 : ℝ≥0∞)
    (hloc : ∀ k ∈ Z, wh1_osc ((3 : ℝ) ^ ((n : ℤ) - 3)) (27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2) u c k ≤
      P2 * (A2 * (∫⁻ x in wh2_B n k, G x) + B2 * ∫⁻ x in wh2_B n k, F x)) :
    ∑ k ∈ Z, wh1_osc ((3 : ℝ) ^ ((n : ℤ) - 3)) (27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2) u c k ≤
      27 ^ d * (P2 * (A2 * (∫⁻ x in W, G x) + B2 * ∫⁻ x in W, F x)) := by
  calc ∑ k ∈ Z, wh1_osc ((3 : ℝ) ^ ((n : ℤ) - 3)) (27 * (3 : ℝ) ^ ((n : ℤ) - 3) / 2) u c k
      ≤ ∑ k ∈ Z, P2 * (A2 * (∫⁻ x in wh2_B n k, G x) + B2 * ∫⁻ x in wh2_B n k, F x) :=
        Finset.sum_le_sum hloc
    _ = P2 * (A2 * (∑ k ∈ Z, ∫⁻ x in wh2_B n k, G x) + B2 * ∑ k ∈ Z, ∫⁻ x in wh2_B n k, F x) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ P2 * (A2 * (27 ^ d * ∫⁻ x in W, G x) + B2 * (27 ^ d * ∫⁻ x in W, F x)) := by
        gcongr
        · exact wh2_sum_lintegral_le n Z hZ hG
        · exact wh2_sum_lintegral_le n Z hZ hF
    _ = _ := by ring

theorem wh2_scale_exists {M : ℝ} (hM : 1 ≤ M) :
    ∃ L0 : ℝ, 21 ≤ L0 ∧ ∀ m : ℕ, L0 ≤ (m : ℝ) →
      (3 : ℤ) ≤ ⌈M * Real.log (m : ℝ)⌉ ∧ ⌈M * Real.log (m : ℝ)⌉ ≤ (m : ℤ) := by
  refine ⟨max 21 (4 * M ^ 2), le_max_left _ _, fun m hm => ?_⟩
  have h21 : (21 : ℝ) ≤ m := (le_max_left _ _).trans hm
  have h4 : 4 * M ^ 2 ≤ (m : ℝ) := (le_max_right _ _).trans hm
  have hm0 : (0 : ℝ) < m := by linarith only [h21]
  have hlog3 : 3 ≤ Real.log (m : ℝ) := by
    rw [Real.le_log_iff_exp_le hm0]
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := by gcongr
    linarith only [this, h21]
  constructor
  · have : (2 : ℤ) < ⌈M * Real.log (m : ℝ)⌉ :=
      Int.lt_ceil.2 (by push_cast; nlinarith only [hM, hlog3])
    omega
  · rw [Int.ceil_le]
    have h2 := Real.log_le_rpow_div hm0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h2
    have hs : 2 * M ≤ Real.sqrt (m : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      linarith only [h4]
    have hss : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = m := Real.mul_self_sqrt hm0.le
    have hs0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
    have h3 : Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
      have : Real.sqrt (m : ℝ) / (1 / 2) = 2 * Real.sqrt (m : ℝ) := by ring
      linarith only [h2, this]
    push_cast
    nlinarith only [h3, hs, hss, hM, hs0]

theorem wh2_isBigO_max {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X0 : Ω → ℝ} (h1 : ∀ ω, 1 ≤ X0 ω) {Lhat L' : ℝ} (hL : Lhat ≤ L') (hL0 : 0 < L')
    (hO : Homogenization.IndependentSums.IsBigO μ Ψ (fun ω => Real.log (X0 ω)) Lhat) :
    Homogenization.IndependentSums.IsBigO μ Ψ
      (fun ω => Real.log (max (X0 ω) ((3 : ℝ) ^ L'))) (2 * L') := by
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  refine (measureReal_mono ?_).trans (hO ht)
  intro ω hω
  simp only [Homogenization.IndependentSums.upperTailEvent, Set.mem_ofPred_eq] at hω ⊢
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ L' := Real.one_le_rpow (by norm_num) hL0.le
  have hmax : 1 ≤ max (X0 ω) ((3 : ℝ) ^ L') := le_trans (h1 ω) (le_max_left _ _)
  have hlog0 : 0 ≤ Real.log (max (X0 ω) ((3 : ℝ) ^ L')) := Real.log_nonneg hmax
  rw [abs_of_nonneg hlog0] at hω
  have hlog1 : 0 ≤ Real.log (X0 ω) := Real.log_nonneg (h1 ω)
  rw [abs_of_nonneg hlog1]
  rcases le_total (X0 ω) ((3 : ℝ) ^ L') with hle | hle
  · exfalso
    rw [max_eq_right hle, Real.log_rpow (by norm_num)] at hω
    have : Real.log 3 < 2 := by
      have := Real.log_two_lt_d9
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith only [this, h, e]
    nlinarith only [hω, this, hL0, ht]
  · rw [max_eq_left hle] at hω
    nlinarith only [hω, hL, hL0, ht]

end SuperdiffusionCLT.Section7
