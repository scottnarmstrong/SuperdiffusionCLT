/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayG

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Restriction and translation to the sub-cube touching the face

A solution on the cube with localized zero trace on the face window restricts to the sub-cube of
side `3^m / 3` touching the face and, translated, becomes a solution of the same kind on the
cube of scale `m - 1`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}


/-- A smooth cutoff equal to `1` on a compact set inside an open box. -/
theorem r3d_exists_box_cutoff (cz : Vec d) {R : ℝ} (hR : 0 < R) {η : Vec d → ℝ}
    (hηc : HasCompactSupport η) (hηT : tsupport η ⊆ {x | ∀ i, |x i - cz i| < R}) :
    ∃ ζ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ {x | ∀ i, |x i - cz i| < R} ∧ ∀ x ∈ tsupport η, ζ x = 1 := by
  classical
  by_cases hne : (tsupport η).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, fun x hx => by
      rw [hne] at hx; exact absurd hx (Set.notMem_empty x)⟩
    simp [tsupport]
  obtain ⟨y, hy, hymax⟩ := hηc.isCompact.exists_isMaxOn hne
    (continuous_norm.comp (continuous_id.sub continuous_const) : Continuous fun x : Vec d => ‖x - cz‖).continuousOn
  set r' : ℝ := ‖y - cz‖ with hr'
  have hr'0 : 0 ≤ r' := norm_nonneg _
  have hr'R : r' < R := by
    rw [hr', pi_norm_lt_iff hR]
    intro i
    simpa [Real.norm_eq_abs] using hηT hy i
  have hmax : ∀ x ∈ tsupport η, ∀ i, |x i - cz i| ≤ r' := by
    intro x hx i
    have h1 : ‖x - cz‖ ≤ r' := hymax hx
    have h2 : ‖(x - cz) i‖ ≤ ‖x - cz‖ := norm_le_pi_norm _ i
    simpa [Real.norm_eq_abs] using h2.trans h1
  set R' : ℝ := (r' + R) / 2 with hR'
  have hR'pos : 0 < R' := by rw [hR']; linarith only [hr'0, hR]
  have hrR' : r' < R' := by rw [hR']; linarith only [hr'R]
  have hRR' : R' < R := by rw [hR']; linarith only [hr'R]
  set rI : ℝ := (r' + R') / 2 with hrI
  have hrI0 : 0 < rI := by rw [hrI]; linarith only [hr'0, hR'pos]
  have hrIR : rI < R' := by rw [hrI]; linarith only [hrR']
  have hr'rI : r' ≤ rI := by rw [hrI]; linarith only [hrR']
  let b : Fin d → ContDiffBump (0 : ℝ) := fun _ => ⟨rI, R', hrI0, hrIR⟩
  let Φ : Fin d → ℝ → ℝ := fun i t => b i (t - cz i)
  have hΦs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Φ i) := fun i =>
    (b i).contDiff.comp (contDiff_id.sub contDiff_const)
  have hΦt : ∀ i, tsupport (Φ i) ⊆ Set.Icc (cz i - R') (cz i + R') := by
    intro i
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    have h1 : ¬ R' ≤ |t - cz i| := fun h2 => ht ((b i).zero_of_le_dist (by simpa [dist_eq_norm, b] using h2))
    push Not at h1
    rw [abs_lt] at h1
    exact ⟨by linarith only [h1.1], by linarith only [h1.2]⟩
  have hΦk : ∀ i, HasCompactSupport (Φ i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hΦt i)
  refine ⟨fun x => ∏ i, Φ i (x i), r3d_prod_contDiff Φ hΦs, r3d_prod_hasCompactSupport Φ hΦk, ?_, ?_⟩
  · intro x hx i
    have := r3d_prod_tsupport Φ hx i
    have h2 := hΦt i this
    rw [abs_lt]
    exact ⟨by linarith only [h2.1, hRR'], by linarith only [h2.2, hRR']⟩
  · intro x hx
    refine Finset.prod_eq_one fun i _ => ?_
    show b i (x i - cz i) = 1
    refine (b i).one_of_mem_closedBall ?_
    have := hmax x hx i
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, b]
    exact this.trans hr'rI

/-- Localized zero trace passes to an open subset containing the window part of the domain. -/
theorem r3d_localized_restrict {D Q : Set (Vec d)} {cz : Vec d} {R : ℝ} (hR : 0 < R)
    (hQ : IsOpen Q) (hQD : Q ⊆ D) (hTD : {x | ∀ i, |x i - cz i| < R} ∩ D ⊆ Q)
    (φ : H1Function D)
    (hZ : LocalizedZeroTraceFunctionOn D {x | ∀ i, |x i - cz i| < R} φ.toFun) :
    LocalizedZeroTraceFunctionOn Q {x | ∀ i, |x i - cz i| < R} (φ.restrict hQ hQD).toFun := by
  intro η hη hηc hηT
  obtain ⟨ζ, hζ, hζc, hζT, hζ1⟩ := r3d_exists_box_cutoff cz hR hηc hηT
  obtain ⟨W₁, hW₁⟩ := hZ ζ hζ hζc hζT
  let W := W₁.mulContDiffHasCompactSupport hη hηc
  have hsub : ∀ n, tsupport (W.approx n) ⊆ Q := fun n x hx =>
    hTD ⟨hηT (tsupport_mul_subset_left hx), W₁.approx_support_subset n
      (tsupport_mul_subset_right hx)⟩
  have hle : (volume.restrict Q : Measure (Vec d)) ≤ volume.restrict D := Measure.restrict_mono hQD le_rfl
  refine ⟨{ toH1Function := W.toH1Function.restrict hQ hQD
            approx := W.approx
            approx_smooth := W.approx_smooth
            approx_hasCompactSupport := W.approx_hasCompactSupport
            approx_support_subset := hsub
            tendsto_approx := ?_
            tendsto_approx_grad := fun i => ?_ }, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds W.tendsto_approx
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hle)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (W.tendsto_approx_grad i)
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hle)
  · funext x
    have h1 := congrFun hW₁ x
    show η x * W₁.toH1Function.toFun x = η x * φ.toFun x
    rw [h1]
    by_cases hx : η x = 0
    · simp [hx]
    · have : ζ x = 1 := hζ1 x (subset_tsupport _ hx)
      rw [← mul_assoc, this, mul_one]

/-- Localized zero trace is transported by a translation. -/
theorem r3d_localized_translate {Q T : Set (Vec d)} (u : H1Function Q) (z : Vec d)
    (hZ : LocalizedZeroTraceFunctionOn Q T u.toFun) :
    LocalizedZeroTraceFunctionOn (translateSet z Q) (translateSet z T) (u.translate z).toFun := by
  intro η hη hηc hηT
  have hη0 : ContDiff ℝ (⊤ : ℕ∞) (fun x => η (x + z)) :=
    hη.comp (contDiff_id.add contDiff_const)
  have hηc0 : HasCompactSupport (fun x => η (x + z)) :=
    hηc.comp_homeomorph (Homeomorph.addRight z)
  have hηT0 : tsupport (fun x => η (x + z)) ⊆ T := by
    intro x hx
    have h1 : x ∈ (Homeomorph.addRight z) ⁻¹' tsupport η := by
      rw [← tsupport_comp_eq_preimage]; exact hx
    have h2 : x + z ∈ translateSet z T := hηT h1
    exact (mem_translateSet_iff_sub_mem).1 h2 |> fun h => by simpa using h
  obtain ⟨W, hW⟩ := hZ _ hη0 hηc0 hηT0
  refine ⟨W.translate z, funext fun x => ?_⟩
  have h1 := congrFun hW (x - z)
  simp only [H10Function.translate_toH1Function, H1Function.translate_toFun, sub_add_cancel] at h1 ⊢
  exact h1



/-- The translation carrying the sub-cube of side `3^m / 3` touching the face onto the cube of
scale `m - 1` centred at the origin. -/
noncomputable def r3d_zT (e : Fin d) (m : ℤ) : Vec d :=
  fun i => if i = e then (3 : ℝ) ^ m / 3 else 0

theorem r3d_pow_pred (m : ℤ) : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := by
  rw [zpow_sub_one₀ (by norm_num)]; ring

/-- The sub-cube of side `3^m / 3` touching the face, as a subset of the cube. -/
def r3d_subV (e : Fin d) (m : ℤ) : Set (Vec d) :=
  {x | x + r3d_zT e m ∈ openCubeSet (originCube d (m - 1))}

theorem r3d_mem_subV_iff (e : Fin d) (m : ℤ) (x : Vec d) :
    x ∈ r3d_subV e m ↔ (∀ i, i ≠ e → |x i| < (3 : ℝ) ^ m / 6) ∧
      -((3 : ℝ) ^ m / 2) < x e ∧ x e < -((3 : ℝ) ^ m / 6) := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  unfold r3d_subV
  simp only [Set.mem_ofPred_eq, hc_mem_openCubeSet_originCube_iff, r3d_pow_pred]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · have := h i
      simp only [Pi.add_apply, r3d_zT, hi, ite_false, add_zero] at this
      rw [abs_lt]; constructor <;> linarith only [this.1, this.2]
    · have := h e
      simp only [Pi.add_apply, r3d_zT, ite_true] at this
      linarith only [this.1]
    · have := h e
      simp only [Pi.add_apply, r3d_zT, ite_true] at this
      linarith only [this.2]
  · rintro ⟨h1, h2, h3⟩ i
    by_cases hi : i = e
    · subst hi
      simp only [Pi.add_apply, r3d_zT, ite_true]
      constructor <;> linarith only [h2, h3, hℓ]
    · have := h1 i hi
      rw [abs_lt] at this
      simp only [Pi.add_apply, r3d_zT, hi, ite_false, add_zero]
      constructor <;> linarith only [this.1, this.2, hℓ]

theorem r3d_subV_open (e : Fin d) (m : ℤ) : IsOpen (r3d_subV e m) :=
  (isOpen_openCubeSet _).preimage (continuous_id.add continuous_const)

theorem r3d_subV_subset (e : Fin d) (m : ℤ) : r3d_subV e m ⊆ openCubeSet (originCube d m) := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := (r3d_mem_subV_iff e m x).1 hx
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [hc_mem_openCubeSet_originCube_iff]
  intro i
  by_cases hi : i = e
  · subst hi; constructor <;> linarith only [h2, h3, hℓ]
  · have := h1 i hi
    rw [abs_lt] at this
    constructor <;> linarith only [this.1, this.2, hℓ]

theorem r3d_subV_subset_Ebox (e : Fin d) (m : ℤ) : r3d_subV e m ⊆ r3d_Ebox e m ((3 : ℝ) ^ m / 3) := by
  intro x hx
  refine ⟨fun i => ?_, r3d_subV_subset e m hx⟩
  obtain ⟨h1, h2, h3⟩ := (r3d_mem_subV_iff e m x).1 hx
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  by_cases hi : i = e
  · subst hi
    simp only [r3c_z0, ite_true]
    rw [abs_le]; constructor <;> linarith only [h2, h3, hℓ]
  · simp only [r3c_z0, hi, ite_false, sub_zero]
    have := h1 i hi
    exact this.le.trans (by linarith only [hℓ])

/-- The small window near the face centre inside the sub-cube. -/
def r3d_window1 (e : Fin d) (m : ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - r3c_z0 e m i| < (3 : ℝ) ^ m / 6}

theorem r3d_window1_inter_subset (e : Fin d) (m : ℤ) :
    r3d_window1 e m ∩ openCubeSet (originCube d m) ⊆ r3d_subV e m := by
  rintro x ⟨h1, h2⟩
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [r3d_mem_subV_iff]
  have h2' := (hc_mem_openCubeSet_originCube_iff m x).1 h2 e
  have h1e := h1 e
  simp only [r3c_z0, ite_true] at h1e
  rw [abs_lt] at h1e
  refine ⟨fun i hi => ?_, by linarith only [h2'.1], by linarith only [h1e.2, hℓ]⟩
  have := h1 i
  simpa [r3c_z0, hi] using this

theorem r3d_window1_subset (e : Fin d) (m : ℤ) : r3d_window1 e m ⊆ r3d_window e m := by
  intro x hx i
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  exact (hx i).trans (by linarith only [hℓ])

theorem r3d_translate_window1 (e : Fin d) (m : ℤ) :
    translateSet (r3d_zT e m) (r3d_window1 e m) = r3d_window e (m - 1) := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  simp only [r3d_window1, r3d_window, Set.mem_ofPred_eq]
  refine forall_congr' fun i => ?_
  have h6 : (3 : ℝ) ^ m / 3 / 2 = (3 : ℝ) ^ m / 6 := by ring
  by_cases hi : i = e
  · subst hi
    simp only [Pi.sub_apply, r3d_zT, r3c_z0, ite_true, r3d_pow_pred, h6]
    have : y i - (3 : ℝ) ^ m / 3 - -((3 : ℝ) ^ m / 2) = y i - -((3 : ℝ) ^ m / 6) := by ring
    rw [this]
  · simp [r3d_zT, r3c_z0, hi, r3d_pow_pred, h6]

theorem r3d_translate_subV (e : Fin d) (m : ℤ) :
    translateSet (r3d_zT e m) (r3d_subV e m) = openCubeSet (originCube d (m - 1)) := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  simp only [r3d_subV, Set.mem_ofPred_eq, sub_add_cancel]


theorem r3d_localized_cast {S S' T : Set (Vec d)} {g : Vec d → ℝ} (h : S = S')
    (hZ : LocalizedZeroTraceFunctionOn S T g) : LocalizedZeroTraceFunctionOn S' T g := by
  subst h
  exact hZ

theorem r3d_subcube_data (e : Fin d) (m : ℤ) {A : CoeffField d} {f : Vec d → ℝ}
    {φ : H1Function (openCubeSet (originCube d m))}
    (hφ : IsWeakSolutionOn A (openCubeSet (originCube d m)) φ f (fun _ => 0))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) φ.toFun) :
    ∃ φ'' : H1Function (openCubeSet (originCube d (m - 1))),
      (∀ y, φ''.toFun y = φ.toFun (y - r3d_zT e m)) ∧ (∀ y, φ''.grad y = φ.grad (y - r3d_zT e m)) ∧
      IsWeakSolutionOn (fun y => A (y - r3d_zT e m)) (openCubeSet (originCube d (m - 1))) φ''
        (fun y => f (y - r3d_zT e m)) (fun _ => 0) ∧
      LocalizedZeroTraceFunctionOn (openCubeSet (originCube d (m - 1))) (r3d_window e (m - 1))
        φ''.toFun := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hVo := r3d_subV_open e m
  have hVU := r3d_subV_subset e m
  have hQo : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  have hsolV := p12_restrict_weak hQo hVo hVU hφ
  have hsolT := IsWeakSolutionOn.translate (r3d_zT e m) hsolV
  have hS := r3d_translate_subV e m
  -- localized zero trace
  have hZ1 : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window1 e m) φ.toFun :=
    fun η hη hηc hηT => hZ η hη hηc (hηT.trans (r3d_window1_subset e m))
  have hR6 : (0 : ℝ) < (3 : ℝ) ^ m / 6 := by positivity
  have hZV : LocalizedZeroTraceFunctionOn (r3d_subV e m) (r3d_window1 e m) (φ.restrict hVo hVU).toFun :=
    r3d_localized_restrict (cz := r3c_z0 e m) hR6 hVo hVU (r3d_window1_inter_subset e m) φ hZ1
  have hZT := r3d_localized_translate (φ.restrict hVo hVU) (r3d_zT e m) hZV
  rw [r3d_translate_window1] at hZT
  refine ⟨((φ.restrict hVo hVU).translate (r3d_zT e m)).castSet hS, fun y => by rw [H1Function.castSet_toFun]; rfl, fun y => by rw [H1Function.castSet_grad]; rfl, ?_, ?_⟩
  · exact r3c_isWeakSolutionOn_castSet hS hsolT
  · have h : (((φ.restrict hVo hVU).translate (r3d_zT e m)).castSet hS).toFun =
        ((φ.restrict hVo hVU).translate (r3d_zT e m)).toFun := funext fun y => by
      rw [H1Function.castSet_toFun]
    rw [h]
    exact r3d_localized_cast hS hZT

end SuperdiffusionCLT.Section7
