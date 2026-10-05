/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryLocalizedB

/-!
# De Giorgi `L^∞–L²` bound up to the boundary under a localized zero trace

For `u ∈ H¹(U ∩ Q)` with `Q = axisCube z L` and localized zero trace in the window `Q`, solving
`-∇·(a∇u) = f - ∇·g` in `U ∩ Q`, the zero extension of `u` to `Q` (coefficient extended by `λ Id`,
data by zero) satisfies the level identity of the iteration, so `deGiorgi_eLpNorm_bound` applies.
The normalisation is that of the `H¹₀` version: `L^{-d/2} ‖u₊‖_{L²(U ∩ Q)}`, that is the
`L²` norm over `U ∩ Q` divided by `|Q|^{1/2}`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Level identity of the zero extension on the window**, under a localized zero trace. -/
theorem dgloc_level_identity {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (hQ : IsOpen Q)
    (hΩQ : Ω ⊆ Q) (hfin : volume Ω ≠ ⊤) (u : H1Function Ω)
    (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) (a : CoeffField d) (c : Mat d)
    (f : Vec d → ℝ) (g : Vec d → Vec d) (hu : IsWeakSolutionOn a Ω u f g) {k : ℝ} (hk : 0 ≤ k)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Q) :
    ∫ x in Q, vecDot (matVecMul (boundaryCoeff Ω c a x) ((dgloc_zeroExt hΩ hQ hΩQ u hz).grad x))
        (levelTest (dgloc_zeroExt hΩ hQ hΩQ u hz) k η x) =
      (∫ x in Q, Ω.indicator f x *
          (η x ^ 2 * max ((dgloc_zeroExt hΩ hQ hΩQ u hz).toFun x - k) 0)) +
        ∫ x in Q, vecDot (Ω.indicator g x)
          (levelTest (dgloc_zeroExt hΩ hQ hΩQ u hz) k η x) := by
  classical
  obtain ⟨φ, hφf, hφg⟩ := dgloc_levelTest_h10 hΩ hQ hfin u hz hk hη hηc hηs
  have hweak := hu φ
  have hΩm := hΩ.measurableSet
  have hWf : ∀ x ∈ Ω, (dgloc_zeroExt hΩ hQ hΩQ u hz).toFun x = u.toFun x := fun x hx =>
    Set.indicator_of_mem hx _
  have hWg : ∀ x ∈ Ω, (dgloc_zeroExt hΩ hQ hΩQ u hz).grad x = u.grad x := fun x hx =>
    Set.indicator_of_mem hx _
  have hWg0 : ∀ x, x ∉ Ω → (dgloc_zeroExt hΩ hQ hΩQ u hz).grad x = 0 := fun x hx =>
    Set.indicator_of_notMem hx _
  have hLT : ∀ x ∈ Ω, levelTest (dgloc_zeroExt hΩ hQ hΩQ u hz) k η x = levelTest u k η x :=
    fun x hx => levelTest_congr (hWf x hx) (hWg x hx)
  have hLTQ : ∀ x, x ∉ Q → levelTest u k η x = 0 := fun x hx =>
    levelTest_eq_zero_of_notMem _ k fun h => hx (hηs h)
  have hη0 : ∀ x, x ∉ Q → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hηs h)
  have e1 : ∫ x in Q, vecDot (matVecMul (boundaryCoeff Ω c a x)
        ((dgloc_zeroExt hΩ hQ hΩQ u hz).grad x))
        (levelTest (dgloc_zeroExt hΩ hQ hΩQ u hz) k η x) =
      ∫ x in Q, Ω.indicator (fun x => vecDot (matVecMul (a x) (u.grad x))
        (levelTest u k η x)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ω
    · simp only [Set.indicator_of_mem hx, boundaryCoeff, hx, ↓reduceIte, hWg x hx, hLT x hx]
    · simp [Set.indicator_of_notMem hx, hWg0 x hx, matVecMul, vecDot]
  have e2 : ∫ x in Q, Ω.indicator f x *
        (η x ^ 2 * max ((dgloc_zeroExt hΩ hQ hΩQ u hz).toFun x - k) 0) =
      ∫ x in Q, Ω.indicator (fun x => f x * (η x ^ 2 * max (u.toFun x - k) 0)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ω
    · simp only [Set.indicator_of_mem hx, hWf x hx]
    · simp [Set.indicator_of_notMem hx]
  have e3 : ∫ x in Q, vecDot (Ω.indicator g x) (levelTest (dgloc_zeroExt hΩ hQ hΩQ u hz) k η x) =
      ∫ x in Q, Ω.indicator (fun x => vecDot (g x) (levelTest u k η x)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ω
    · simp only [Set.indicator_of_mem hx, hLT x hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  rw [e1, e2, e3,
    integral_indicator_eq_of_vanish hΩm (fun x hx => by simp [hLTQ x hx, vecDot, matVecMul]),
    integral_indicator_eq_of_vanish hΩm (fun x hx => by simp [hη0 x hx]),
    integral_indicator_eq_of_vanish hΩm (fun x hx => by simp [hLTQ x hx, vecDot])]
  have hae : ∀ᵐ x ∂(volume.restrict Ω), levelTest u k η x = φ.toH1Function.grad x := by
    filter_upwards [hφg] with x hx
    rw [hx]
  have e4 : ∫ x in Ω, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
      ∫ x in Ω, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have e5 : ∫ x in Ω, vecDot (g x) (levelTest u k η x) =
      ∫ x in Ω, vecDot (g x) (φ.toH1Function.grad x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have e6 : ∫ x in Ω, f x * (η x ^ 2 * max (u.toFun x - k) 0) =
      ∫ x in Ω, f x * φ.toH1Function.toFun x :=
    setIntegral_congr_fun hΩm fun x _ => by simp only [hφf]
  rw [e4, e5, e6]
  exact hweak

theorem dgloc_halfCube_subset {z : Vec d} {L : ℝ} :
    halfCube z L ⊆ axisCube z L := by
  intro x hx j hj
  have h := hx j hj
  simp only [Set.mem_Ioo, Pi.add_apply] at h ⊢
  constructor <;> linarith only [h.1, h.2]

/-- **De Giorgi `L^∞–L²` bound up to the boundary, under a localized zero trace.**
For `u ∈ H¹(U ∩ Q)`, `Q = axisCube z L`, with `u = 0` on the part of `∂U` inside `Q` in the sense
`LocalizedZeroTraceFunctionOn (U ∩ Q) Q u`, and `-∇·(a∇u) = f - ∇·g` in `U ∩ Q`:
`sup_{U ∩ Q/2} u₊ ≤ C (Λ/λ)^N (L^{-d/2} ‖u₊‖_{L²(U ∩ Q)} + L²/λ ‖f‖_∞ + L/λ ‖g‖_∞)`,
with `N = deGiorgiPower d`, the exponent and normalisation of `deGiorgi_boundary_bound`. -/
theorem deGiorgi_boundary_localized (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}, IsOpen U →
      ∀ (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (U ∩ axisCube z L) a →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d),
        AEStronglyMeasurable g (volume.restrict (U ∩ axisCube z L)) →
        ∀ (u : H1Function (U ∩ axisCube z L)),
          LocalizedZeroTraceFunctionOn (U ∩ axisCube z L) (axisCube z L) u.toFun →
          IsWeakSolutionOn a (U ∩ axisCube z L) u f g →
          eLpNorm (fun x => max (u.toFun x) 0) ⊤ (volume.restrict (U ∩ halfCube z L)) ≤
            ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
              (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
                  eLpNorm (fun x => max (u.toFun x) 0) 2
                    (volume.restrict (U ∩ axisCube z L)) +
                ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (U ∩ axisCube z L)) +
                ENNReal.ofReal (L / lam) *
                  eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (U ∩ axisCube z L))) := by
  classical
  obtain ⟨C, hC, hmain⟩ := deGiorgi_eLpNorm_bound hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a U hUo z L hL hEll f g hgm u hz hw
  have hQo : IsOpen (axisCube z L) := isOpen_axisCube z L
  have hΩo : IsOpen (U ∩ axisCube z L) := hUo.inter hQo
  have hΩQ : U ∩ axisCube z L ⊆ axisCube z L := Set.inter_subset_right
  have hHQ : U ∩ halfCube z L = U ∩ axisCube z L ∩ halfCube z L := by
    ext x
    exact ⟨fun h => ⟨⟨h.1, dgloc_halfCube_subset h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rcases (U ∩ axisCube z L).eq_empty_or_nonempty with hU0 | ⟨x0, hx0⟩
  · have h0 : volume.restrict (U ∩ axisCube z L ∩ halfCube z L) = 0 := by
      rw [hU0]
      simp
    rw [hHQ, h0]
    simp
  have hfin : volume (U ∩ axisCube z L) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (by simpa using (isOpenBoundedConvexDomain_axisCube z L).isBoundedDomain.isFiniteMeasure_restrict_volume.measure_univ_lt_top.ne)
      (measure_mono hΩQ)
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 x0 hx0
  have hEll' := isEllipticFieldOn_boundaryCoeff hΩo.measurableSet hQo.measurableSet hlam hlamLam
    hEll
  set W := dgloc_zeroExt hΩo hQo hΩQ u hz with hW
  have hgm' : AEStronglyMeasurable ((U ∩ axisCube z L).indicator g)
      (volume.restrict (axisCube z L)) := by
    rw [aestronglyMeasurable_indicator_iff hΩo.measurableSet, Measure.restrict_restrict
      hΩo.measurableSet, Set.inter_eq_left.2 hΩQ]
    exact hgm
  have key := hmain z hL hEll' W ((U ∩ axisCube z L).indicator f)
    ((U ∩ axisCube z L).indicator g) hgm'
    (fun k hk _ hη hηc hηs => dgloc_level_identity hΩo hQo hΩQ hfin u hz a (scalarMatrix lam) f g
      hw hk hη hηc hηs)
  have hmaxW : (fun x => max (W.toFun x) 0) =
      (U ∩ axisCube z L).indicator (fun x => max (u.toFun x) 0) := by
    funext x
    by_cases hx : x ∈ U ∩ axisCube z L
    · rw [Set.indicator_of_mem hx, hW, dgloc_zeroExt_toFun, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hW, dgloc_zeroExt_toFun, Set.indicator_of_notMem hx]
      simp
  have hnormg : (fun x => eucNorm ((U ∩ axisCube z L).indicator g x)) =
      (U ∩ axisCube z L).indicator (fun x => eucNorm (g x)) := by
    funext x
    by_cases hx : x ∈ U ∩ axisCube z L
    · simp only [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, eucNorm, vecNormSq, vecDot]
  rw [hmaxW, hnormg] at key
  simp only [eLpNorm_indicator_restrict_inter hΩo.measurableSet] at key
  rw [hHQ]
  have hQQ : U ∩ axisCube z L ∩ axisCube z L = U ∩ axisCube z L := Set.inter_eq_left.2 hΩQ
  rw [hQQ] at key
  exact key

/-! ### The two-sided bound -/

theorem dgloc_eucNorm_neg (v : Vec d) : eucNorm (-v) = eucNorm v := by
  simp [eucNorm, vecNormSq, vecDot]

theorem dgloc_weak_neg {Ω : Set (Vec d)} {a : CoeffField d} {u : H1Function Ω}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (hu : IsWeakSolutionOn a Ω u f g) :
    IsWeakSolutionOn a Ω (-u) (fun x => -f x) (fun x => -g x) := by
  intro φ
  have h := hu φ
  have e1 : ∫ x in Ω, vecDot (matVecMul (a x) ((-u).grad x)) (φ.toH1Function.grad x) =
      -∫ x in Ω, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [vecDot, matVecMul, Finset.sum_neg_distrib, neg_mul]
  have e2 : ∫ x in Ω, (fun x => -f x) x * φ.toH1Function.toFun x =
      -∫ x in Ω, f x * φ.toH1Function.toFun x := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have e3 : ∫ x in Ω, vecDot ((fun x => -g x) x) (φ.toH1Function.grad x) =
      -∫ x in Ω, vecDot (g x) (φ.toH1Function.grad x) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [vecDot, Finset.sum_neg_distrib])
  rw [e1, e2, e3, h]
  ring

theorem dgloc_localized_neg {Ω Q : Set (Vec d)} {u : H1Function Ω}
    (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) :
    LocalizedZeroTraceFunctionOn Ω Q (-u).toFun := by
  have h : (-u).toFun = fun x => -u.toFun x := H1Function.neg_toFun u
  rw [h]
  exact localizedZeroTraceFunctionOn_neg hz

/-- **Two-sided De Giorgi `L^∞–L²` bound under a localized zero trace**: the bound of
`deGiorgi_boundary_localized` for `|u|`, with the `L²` norm of `u` itself. -/
theorem deGiorgi_boundary_localized_abs (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}, IsOpen U →
      ∀ (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (U ∩ axisCube z L) a →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d),
        AEStronglyMeasurable g (volume.restrict (U ∩ axisCube z L)) →
        ∀ (u : H1Function (U ∩ axisCube z L)),
          LocalizedZeroTraceFunctionOn (U ∩ axisCube z L) (axisCube z L) u.toFun →
          IsWeakSolutionOn a (U ∩ axisCube z L) u f g →
          eLpNorm u.toFun ⊤ (volume.restrict (U ∩ halfCube z L)) ≤
            ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
              (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
                  eLpNorm u.toFun 2 (volume.restrict (U ∩ axisCube z L)) +
                ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (U ∩ axisCube z L)) +
                ENNReal.ofReal (L / lam) *
                  eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (U ∩ axisCube z L))) := by
  obtain ⟨C, hC, hmain⟩ := deGiorgi_boundary_localized hd
  refine ⟨2 * C, by positivity, ?_⟩
  intro lam Lam a U hUo z L hL hEll f g hgm u hz hw
  have hp := hmain hUo z hL hEll f g hgm u hz hw
  have hn := hmain hUo z hL hEll (fun x => -f x) (fun x => -g x) hgm.neg (-u)
    (dgloc_localized_neg hz) (dgloc_weak_neg hw)
  have hnf : (-u).toFun = fun x => -u.toFun x := H1Function.neg_toFun u
  rw [hnf] at hn
  beta_reduce at hn
  set R : ℝ≥0∞ := ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * eLpNorm u.toFun 2 (volume.restrict (U ∩ axisCube z L)) +
    ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (U ∩ axisCube z L)) +
    ENNReal.ofReal (L / lam) * eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (U ∩ axisCube z L)) with hR
  have h2p : eLpNorm (fun x => max (u.toFun x) 0) 2 (volume.restrict (U ∩ axisCube z L)) ≤
      eLpNorm u.toFun 2 (volume.restrict (U ∩ axisCube z L)) :=
    eLpNorm_mono (u.memL2.aestronglyMeasurable.sup aestronglyMeasurable_const) fun x => by
      simp only [Real.norm_eq_abs]
      rcases le_total (u.toFun x) 0 with h | h
      · simp [max_eq_right h]
      · rw [max_eq_left h]
  have h2n : eLpNorm (fun x => max (-u.toFun x) 0) 2 (volume.restrict (U ∩ axisCube z L)) ≤
      eLpNorm u.toFun 2 (volume.restrict (U ∩ axisCube z L)) :=
    eLpNorm_mono (u.memL2.aestronglyMeasurable.neg.sup aestronglyMeasurable_const) fun x => by
      simp only [Real.norm_eq_abs]
      rcases le_total (-u.toFun x) 0 with h | h
      · simp [max_eq_right h]
      · rw [max_eq_left h]; exact (abs_neg _).le
  have hfn : eLpNorm (fun x => -f x) ⊤ (volume.restrict (U ∩ axisCube z L)) = eLpNorm f ⊤ (volume.restrict (U ∩ axisCube z L)) :=
    eLpNorm_neg f ⊤ _
  have hgn : eLpNorm (fun x => eucNorm ((fun x => -g x) x)) ⊤ (volume.restrict (U ∩ axisCube z L)) =
      eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (U ∩ axisCube z L)) := by
    simp only [dgloc_eucNorm_neg]
  rw [hfn, hgn] at hn
  have hmeas : ∀ μ : Measure (Vec d), μ ≤ volume.restrict (U ∩ axisCube z L) →
      AEStronglyMeasurable u.toFun μ := fun μ hμ =>
    (u.memL2.aestronglyMeasurable).mono_measure hμ
  have hle : volume.restrict (U ∩ halfCube z L) ≤ volume.restrict (U ∩ axisCube z L) := by
    refine Measure.restrict_mono ?_ le_rfl
    exact Set.inter_subset_inter_right _ (dgloc_halfCube_subset)
  have hum := hmeas _ hle
  have hsum : eLpNorm u.toFun ⊤ (volume.restrict (U ∩ halfCube z L)) ≤
      eLpNorm (fun x => max (u.toFun x) 0) ⊤ (volume.restrict (U ∩ halfCube z L)) +
        eLpNorm (fun x => max (-u.toFun x) 0) ⊤ (volume.restrict (U ∩ halfCube z L)) := by
    refine le_trans (eLpNorm_mono hum (g := fun x => max (u.toFun x) 0 + max (-u.toFun x) 0)
      fun x => ?_) (eLpNorm_add_le (f := fun x => max (u.toFun x) 0)
        (g := fun x => max (-u.toFun x) 0) le_top)
    simp only [Real.norm_eq_abs]
    rcases le_total (u.toFun x) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
      have : 0 ≤ |max (u.toFun x) 0 + -u.toFun x| := abs_nonneg _
      rw [abs_of_nonneg (by linarith only [h])]
      linarith only [h]
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
      rw [abs_of_nonneg (by linarith only [h])]
      linarith only [h]
  have hA : ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) * R + ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) * R =
      ENNReal.ofReal (2 * C * (Lam / lam) ^ deGiorgiPower d) * R := by
    rw [← add_mul, ← two_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    ring_nf
  refine hsum.trans ?_
  rw [← hA]
  refine add_le_add (hp.trans ?_) (hn.trans ?_)
  · exact mul_le_mul_right (add_le_add (add_le_add (mul_le_mul_right h2p _) le_rfl) le_rfl) _
  · exact mul_le_mul_right (add_le_add (add_le_add (mul_le_mul_right h2n _) le_rfl) le_rfl) _

/-! ### The consumer form -/

/-- The normalisation `L^{-d/2} ‖F‖_{L²(Ω)}` of the bounds above is at most the normalised norm
`lpBar Ω 2 F`, when `Ω` lies in a cube of side `L`. -/
theorem dgloc_scale_le_lpBar {Ω : Set (Vec d)} {z : Vec d} {L : ℝ} (hL : 0 < L)
    (hΩQ : Ω ⊆ axisCube z L) {F : Vec d → ℝ} (hF : AEStronglyMeasurable F (volume.restrict Ω)) :
    ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * eLpNorm F 2 (volume.restrict Ω) ≤ lpBar Ω 2 F := by
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) F _ hF, smul_eq_mul]
  gcongr ?_ * _
  have h12 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by simp
  rw [h12]
  have hQ := measure_univ_axisCube_rpow z hL (-(1 / 2 : ℝ))
  rw [Measure.restrict_apply_univ] at hQ
  have hexp : (d : ℝ) * -(1 / 2 : ℝ) = -(d : ℝ) / 2 := by ring
  rw [hexp] at hQ
  rw [← hQ, ENNReal.rpow_neg, ← ENNReal.inv_rpow]
  exact ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 (measure_mono hΩQ)) (by norm_num)

/-- **De Giorgi `L^∞–L²` bound under a localized zero trace, consumer form.**  With zero
divergence data `g = 0`, a cube of side `L` and `‖u‖_{L̲²(U ∩ Q)} ≤ L R`, the bound
`‖u‖_{L^∞(U ∩ S)} ≤ C (Λ/λ)^N (L R + L² λ⁻¹ ‖f‖_∞)` holds for every `S` inside the concentric
half cube.  (For `L = 3^n`, `S = z + □_{n-1}` this is `C (Λ/ν)^κ (3^n R + 9^n ν⁻¹ ‖f‖_∞)`.) -/
theorem deGiorgi_boundary_localized_scaled (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}, IsOpen U →
      ∀ (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (U ∩ axisCube z L) a →
      ∀ (f : Vec d → ℝ) (u : H1Function (U ∩ axisCube z L)),
        LocalizedZeroTraceFunctionOn (U ∩ axisCube z L) (axisCube z L) u.toFun →
        IsWeakSolutionOn a (U ∩ axisCube z L) u f (fun _ => 0) →
        ∀ R : ℝ≥0∞, lpBar (U ∩ axisCube z L) 2 u.toFun ≤ ENNReal.ofReal L * R →
        ∀ S : Set (Vec d), S ⊆ halfCube z L →
          eLpNorm u.toFun ⊤ (volume.restrict (U ∩ S)) ≤
            ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
              (ENNReal.ofReal L * R +
                ENNReal.ofReal (L ^ 2 / lam) *
                  eLpNorm f ⊤ (volume.restrict (U ∩ axisCube z L))) := by
  obtain ⟨C, hC, hmain⟩ := deGiorgi_boundary_localized_abs hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a U hUo z L hL hEll f u hz hw R hR S hS
  have h := hmain hUo z hL hEll f (fun _ => 0) aestronglyMeasurable_const u hz hw
  have h0 : eLpNorm (fun x => eucNorm ((fun _ => (0 : Vec d)) x)) ⊤
      (volume.restrict (U ∩ axisCube z L)) = 0 := by
    simp [eucNorm, vecNormSq, vecDot]
  rw [h0, mul_zero, add_zero] at h
  have hmono : eLpNorm u.toFun ⊤ (volume.restrict (U ∩ S)) ≤
      eLpNorm u.toFun ⊤ (volume.restrict (U ∩ halfCube z L)) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono (Set.inter_subset_inter_right _ hS) le_rfl)
  have hl := (dgloc_scale_le_lpBar hL (Set.inter_subset_right (s := U)) (F := u.toFun)
    (u.memL2.aestronglyMeasurable)).trans hR
  refine hmono.trans (h.trans ?_)
  gcongr

/-! ### Satisfiability witness

The hypotheses are met on the upper half of the unit square, `U = {x₁ > 0}`, by the zero function
with identity coefficients and zero data (the harmonic function `x₂` has the same shape: it vanishes
on the flat part of the boundary and not on the rest). -/

theorem dgloc_witness_open : IsOpen {x : Vec 2 | 0 < x 1} :=
  isOpen_lt continuous_const (continuous_apply 1)

theorem dgloc_witness_elliptic :
    IsEllipticFieldOn (1 : ℝ) 1 ({x : Vec 2 | 0 < x 1} ∩ axisCube (0 : Vec 2) 1)
      (fun _ => (1 : Mat 2)) :=
  ⟨measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
      Measurable.ite (dgloc_witness_open.inter (isOpen_axisCube (0 : Vec 2) 1)).measurableSet
        measurable_const measurable_const,
    fun _ _ => Homogenization.isEllipticMatrix_one_one le_rfl⟩

theorem dgloc_witness_trace :
    LocalizedZeroTraceFunctionOn ({x : Vec 2 | 0 < x 1} ∩ axisCube (0 : Vec 2) 1)
      (axisCube (0 : Vec 2) 1)
      (0 : H1Function ({x : Vec 2 | 0 < x 1} ∩ axisCube (0 : Vec 2) 1)).toFun := by
  intro η _ _ _
  have : (fun y => η y * (0 : H1Function ({x : Vec 2 | 0 < x 1} ∩
      axisCube (0 : Vec 2) 1)).toFun y) = 0 := by
    funext y
    simp
  rw [this]
  exact memH10_zero

theorem dgloc_witness_weak :
    IsWeakSolutionOn (fun _ => (1 : Mat 2)) ({x : Vec 2 | 0 < x 1} ∩ axisCube (0 : Vec 2) 1)
      (0 : H1Function ({x : Vec 2 | 0 < x 1} ∩ axisCube (0 : Vec 2) 1)) (fun _ => 0)
      (fun _ => 0) := by
  intro φ
  simp [vecDot, matVecMul]

example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_boundary_localized (d := 2) le_rfl
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) dgloc_witness_open
    (0 : Vec 2) one_pos dgloc_witness_elliptic (fun _ => 0) (fun _ => 0) aestronglyMeasurable_const
    0 dgloc_witness_trace dgloc_witness_weak
  trivial

example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_boundary_localized_abs (d := 2) le_rfl
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) dgloc_witness_open
    (0 : Vec 2) one_pos dgloc_witness_elliptic (fun _ => 0) (fun _ => 0) aestronglyMeasurable_const
    0 dgloc_witness_trace dgloc_witness_weak
  trivial

example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_boundary_localized_scaled (d := 2) le_rfl
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) dgloc_witness_open
    (0 : Vec 2) one_pos dgloc_witness_elliptic (fun _ => 0) 0 dgloc_witness_trace
    dgloc_witness_weak 0 (by simp [lpBar]) (halfCube (0 : Vec 2) 1) le_rfl
  trivial

end SuperdiffusionCLT.Section7
