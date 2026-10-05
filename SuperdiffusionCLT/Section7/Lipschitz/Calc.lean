/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApi
public import Homogenization.Sobolev.H1.Translation
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.EquationRestrictionZeroExtension

/-!
# Calculus of the carriers and of the blocks of the Lipschitz chain

The normalized `L²` carriers `lipL2`, `lipGradL2` against the origin-cube carriers of Section 6,
their triangle inequality, monotonicity in the set, the `L^∞` bound, translation, the monotonicity
of the block predicates in their constants, and the restriction of weak solutions and of localized
zero traces to smaller open sets.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

theorem lip_lpBar_openCube {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ≥0∞)
    (F : Vec d → E) :
    lpBar (openCubeSet Q) p F = SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q p F := by
  unfold lpBar SuperdiffusionCLT.Section2.Norms.cubeLpENorm normalizedCubeMeasure cubeMeasure
  have hv : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [volume_openCubeSet_eq_volume_cubeSet, ← cubeMeasure_apply_univ,
      cubeMeasure_apply_univ_eq]
  rw [hv, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- On an origin cube the two normalized `L²` norms agree. -/
theorem lipL2_engCube [NeZero d] (n : ℕ) (f : Vec d → ℝ) :
    lipL2 (Section6.engCube d n) f = Section6.cubeL2 n f := by
  unfold lipL2 Section6.cubeL2
  rw [Section6.engCube, lip_lpBar_openCube,
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm_toReal_eq_cubeLpNorm]

theorem lipGradL2_engCube [NeZero d] (n : ℕ) (F : Vec d → Vec d) :
    lipGradL2 (Section6.engCube d n) F = Section6.cubeGradL2 n F := by
  unfold lipGradL2 Section6.cubeGradL2
  rw [← lipL2_engCube]
  rfl

/-- The origin cube as a shifted cube. -/
theorem shiftCube_zero_eq_engCube [NeZero d] (n : ℕ) :
    shiftCube (0 : Vec d) (n : ℤ) = Section6.engCube d n :=
  rc_shiftCube_zero _

/-- The normalized norm of a translated function. -/
theorem lpBar_translateSet {E : Type*} [NormedAddCommGroup E] (y : Vec d) (S : Set (Vec d))
    (p : ℝ≥0∞) (F : Vec d → E) :
    lpBar (translateSet (-y) S) p (fun x => F (x + y)) = lpBar S p F := by
  have hτ : MeasurableEmbedding (fun x : Vec d => x + y) := measurableEmbedding_addRight y
  have hT : translateSet (-y) S = (fun x : Vec d => x + y) ⁻¹' S := by
    ext x
    simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]
  have hmap : Measure.map (fun x : Vec d => x + y) volume = volume := map_add_right_eq_self _ y
  have hvol : volume (translateSet (-y) S) = volume S := by
    rw [hT]
    nth_rewrite 2 [← hmap]
    exact (hτ.map_apply volume S).symm
  unfold lpBar
  rw [hvol, show (fun x : Vec d => F (x + y)) = F ∘ (fun x : Vec d => x + y) from rfl,
    ← hτ.eLpNorm_map_measure (g := F) (f := fun x : Vec d => x + y)
    (μ := ((volume S)⁻¹) • volume.restrict (translateSet (-y) S)) (p := p)]
  congr 1
  rw [Measure.map_smul, hT, ← hτ.restrict_map, hmap]
  exact hτ.measurable.aemeasurable

theorem lip_lpBar_memLp {S : Set (Vec d)} {f : Vec d → ℝ} (hS0 : volume S ≠ 0)
    (hf : MemLp f 2 (volume.restrict S)) : MemLp f 2 (((volume S)⁻¹) • volume.restrict S) :=
  hf.smul_measure (ENNReal.inv_ne_top.2 hS0)

theorem lip_lpBar_ne_top {S : Set (Vec d)} {f : Vec d → ℝ} (hS0 : volume S ≠ 0)
    (hf : MemLp f 2 (volume.restrict S)) : lpBar S 2 f ≠ ⊤ :=
  (lip_lpBar_memLp hS0 hf).eLpNorm_lt_top.ne

/-- The real norm of a function in `L²` of a bounded set of positive measure. -/
theorem ofReal_lipL2 {S : Set (Vec d)} {f : Vec d → ℝ} (hS0 : volume S ≠ 0) (hS : volume S ≠ ⊤)
    (hf : MemLp f 2 (volume.restrict S)) : ENNReal.ofReal (lipL2 S f) = lpBar S 2 f := by
  have _ := hS
  exact ENNReal.ofReal_toReal (lip_lpBar_ne_top hS0 hf)

theorem lipL2_add_le {S : Set (Vec d)} {f g : Vec d → ℝ} (hS0 : volume S ≠ 0)
    (hS : volume S ≠ ⊤) (hf : MemLp f 2 (volume.restrict S)) (hg : MemLp g 2 (volume.restrict S)) :
    lipL2 S (fun x => f x + g x) ≤ lipL2 S f + lipL2 S g := by
  have _ := hS
  have hf' := lip_lpBar_memLp hS0 hf
  have hg' := lip_lpBar_memLp hS0 hg
  unfold lipL2
  rw [← ENNReal.toReal_add (lip_lpBar_ne_top hS0 hf) (lip_lpBar_ne_top hS0 hg)]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨lip_lpBar_ne_top hS0 hf,
    lip_lpBar_ne_top hS0 hg⟩) ?_
  exact eLpNorm_add_le (by norm_num)

/-- Restriction to a subset costs the square root of the volume ratio. -/
theorem lipL2_mono_set {S S' : Set (Vec d)} {f : Vec d → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hSS : S ⊆ S') (hS0 : volume S ≠ 0) (hS' : volume S' ≠ ⊤)
    (hvol : volume S' ≤ ENNReal.ofReal κ * volume S) (hf : MemLp f 2 (volume.restrict S')) :
    lipL2 S f ≤ Real.sqrt κ * lipL2 S' f := by
  have hS'0 : volume S' ≠ 0 := fun h => hS0 (measure_mono_null hSS h)
  have hS : volume S ≠ ⊤ := fun h => hS' (top_unique (h ▸ measure_mono hSS))
  have hne := lip_lpBar_ne_top hS'0 hf
  have hk0 : ENNReal.ofReal κ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hvol
    exact hS'0 (le_antisymm hvol bot_le)
  have hc : ((volume S)⁻¹) ≤ ENNReal.ofReal κ * (volume S')⁻¹ := by
    calc ((volume S)⁻¹) = (volume S)⁻¹ * ((volume S')⁻¹ * volume S') := by
          rw [ENNReal.inv_mul_cancel hS'0 hS', mul_one]
      _ ≤ (volume S)⁻¹ * ((volume S')⁻¹ * (ENNReal.ofReal κ * volume S)) := by gcongr
      _ = ENNReal.ofReal κ * (volume S')⁻¹ * ((volume S)⁻¹ * volume S) := by ring
      _ = ENNReal.ofReal κ * (volume S')⁻¹ := by
          rw [ENNReal.inv_mul_cancel hS0 hS, mul_one]
  have hmeas : ((volume S)⁻¹) • volume.restrict S ≤
      (ENNReal.ofReal κ * (volume S')⁻¹) • volume.restrict S' := by
    rw [Measure.le_iff']
    intro A
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul' hc (Measure.restrict_mono hSS le_rfl A)
  have h1 : lpBar S 2 f ≤ ENNReal.ofReal (Real.sqrt κ) * lpBar S' 2 f := by
    unfold lpBar
    calc eLpNorm f 2 (((volume S)⁻¹) • volume.restrict S)
        ≤ eLpNorm f 2 ((ENNReal.ofReal κ * (volume S')⁻¹) • volume.restrict S') :=
          eLpNorm_mono_measure f hmeas
      _ = ENNReal.ofReal (Real.sqrt κ) * eLpNorm f 2 (((volume S')⁻¹) • volume.restrict S') := by
          rw [← smul_smul, eLpNorm_smul_measure_of_ne_zero hk0, smul_eq_mul]
          congr 1
          have : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by
            rw [ENNReal.toReal_div]; norm_num
          rw [this, ENNReal.ofReal_rpow_of_nonneg hκ (by norm_num), Real.sqrt_eq_rpow]
  unfold lipL2
  calc (lpBar S 2 f).toReal ≤ (ENNReal.ofReal (Real.sqrt κ) * lpBar S' 2 f).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne) h1
    _ = Real.sqrt κ * (lpBar S' 2 f).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem lipL2_le_of_ae_abs_le {S : Set (Vec d)} {f : Vec d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hS0 : volume S ≠ 0) (hS : volume S ≠ ⊤) (hf : ∀ᵐ x ∂volume.restrict S, |f x| ≤ B) :
    lipL2 S f ≤ B := by
  unfold lipL2 lpBar
  by_cases hm : AEStronglyMeasurable f (((volume S)⁻¹) • volume.restrict S)
  · refine ENNReal.toReal_le_of_le_ofReal hB ?_
    have hae : ∀ᵐ x ∂(((volume S)⁻¹) • volume.restrict S), ‖f x‖ ≤ B := by
      refine Measure.ae_smul_measure ?_ _
      filter_upwards [hf] with x hx using by simpa [Real.norm_eq_abs] using hx
    have h := eLpNorm_le_of_ae_bound (p := 2) hm hae
    have hu : (((volume S)⁻¹) • volume.restrict S) Set.univ = 1 := by
      rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hS0 hS
    rw [hu] at h
    simpa using h
  · rw [eLpNorm_of_not_aestronglyMeasurable hm]
    simpa using hB

theorem lip_sqrt_le_two_mul {s s' : ℝ} (hs : s ≤ 4 * s') : Real.sqrt s ≤ 2 * Real.sqrt s' := by
  calc Real.sqrt s ≤ Real.sqrt (4 * s') := Real.sqrt_le_sqrt hs
    _ = 2 * Real.sqrt s' := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem lip_inv_sqrt_le {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (h : s' ≤ 4 * s) :
    (Real.sqrt s)⁻¹ ≤ 2 * (Real.sqrt s')⁻¹ := by
  have h1 : Real.sqrt s' ≤ 2 * Real.sqrt s := lip_sqrt_le_two_mul h
  have hp : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hp' : 0 < Real.sqrt s' := Real.sqrt_pos.2 hs'
  calc (Real.sqrt s)⁻¹ ≤ (Real.sqrt s' / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith only [h1])
    _ = 2 * (Real.sqrt s')⁻¹ := by rw [inv_div, div_eq_mul_inv, mul_comm]

theorem lip_inv_le {s s' : ℝ} (hs' : 0 < s') (h : s' ≤ 2 * s) :
    s⁻¹ ≤ 2 * s'⁻¹ := by
  calc s⁻¹ ≤ (s' / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith only [h])
    _ = 2 * s'⁻¹ := by rw [inv_div, div_eq_mul_inv, mul_comm]

/-- The blocks are monotone in their constants. -/
theorem LipCaccInt.mono {a : CoeffField d} {nu s s' C C' : ℝ} {rc k : ℕ}
    (h : LipCaccInt a nu s C rc k) (hs : 0 < s) (hs1 : s ≤ 2 * s') (hs2 : s' ≤ 2 * s)
    (hC : 0 ≤ C) (hCC : 2 * C ≤ C') : LipCaccInt a nu s' C' rc k := by
  intro f F u hsol hF hf
  have hs' : 0 < s' := by linarith only [hs, hs1]
  have h1 := h f F u hsol hF hf
  have e1 := lip_sqrt_le_two_mul (s := s) (s' := s') (by linarith only [hs1, hs'])
  have e2 := lip_inv_sqrt_le hs hs' (by linarith only [hs2, hs])
  have hfl : 0 ≤ Section6.cubeFlat k u.toFun := Section6.cubeFlat_nonneg k _
  have hp : 0 ≤ (3 : ℝ) ^ k * F := by positivity
  have hq : 0 ≤ Real.sqrt s' := Real.sqrt_nonneg _
  have hq' : 0 ≤ (Real.sqrt s')⁻¹ := inv_nonneg.2 hq
  calc Real.sqrt nu * Section6.cubeGradL2 (k - rc) u.grad
      ≤ C * (Real.sqrt s * Section6.cubeFlat k u.toFun + (Real.sqrt s)⁻¹ * (3 : ℝ) ^ k * F) := h1
    _ ≤ C * ((2 * Real.sqrt s') * Section6.cubeFlat k u.toFun +
          (2 * (Real.sqrt s')⁻¹) * (3 : ℝ) ^ k * F) := by
        gcongr
    _ = (2 * C) * (Real.sqrt s' * Section6.cubeFlat k u.toFun +
          (Real.sqrt s')⁻¹ * (3 : ℝ) ^ k * F) := by ring
    _ ≤ C' * (Real.sqrt s' * Section6.cubeFlat k u.toFun +
          (Real.sqrt s')⁻¹ * (3 : ℝ) ^ k * F) := by
        refine mul_le_mul_of_nonneg_right hCC ?_
        have : 0 ≤ (Real.sqrt s')⁻¹ * ((3 : ℝ) ^ k * F) := mul_nonneg hq' hp
        have h3 : 0 ≤ Real.sqrt s' * Section6.cubeFlat k u.toFun := mul_nonneg hq hfl
        linarith only [this, h3, mul_assoc (Real.sqrt s')⁻¹ ((3 : ℝ) ^ k) F]

theorem LipHarmInt.mono {a : CoeffField d} {s s' δ δ' C C' : ℝ} {k : ℕ}
    (h : LipHarmInt a s δ C k) (hs : 0 < s') (hs2 : s' ≤ 2 * s) (hδ : 0 ≤ δ)
    (hδδ : δ ≤ 2 * δ') (hC : 0 ≤ C) (hCC : 2 * C ≤ C') : LipHarmInt a s' δ' C' k := by
  intro f F u hsol hF hf
  obtain ⟨w, gw, hw, hb⟩ := h f F u hsol hF hf
  refine ⟨w, gw, hw, hb.trans ?_⟩
  have e2 := lip_inv_le hs hs2
  have hfl : 0 ≤ Section6.cubeFlat k u.toFun := Section6.cubeFlat_nonneg k _
  have hX : 0 ≤ (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun := by positivity
  have hY : 0 ≤ ((3 : ℝ) ^ k) ^ 2 * F := by positivity
  have hs'i : 0 ≤ s'⁻¹ := inv_nonneg.2 hs.le
  have hδ' : 0 ≤ δ' := by linarith only [hδ, hδδ]
  calc C * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun + s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F)
      ≤ C * (2 * (δ' * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) +
          2 * (s'⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC
        · calc δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun
              = δ * ((3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) := by ring
            _ ≤ (2 * δ') * ((3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) :=
                mul_le_mul_of_nonneg_right hδδ hX
            _ = 2 * (δ' * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) := by ring
        · calc s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F = s⁻¹ * (((3 : ℝ) ^ k) ^ 2 * F) := by ring
            _ ≤ (2 * s'⁻¹) * (((3 : ℝ) ^ k) ^ 2 * F) := mul_le_mul_of_nonneg_right e2 hY
            _ = 2 * (s'⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) := by ring
    _ = (2 * C) * (δ' * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun +
          s'⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) := by ring
    _ ≤ C' * (δ' * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun + s'⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F) := by
        refine mul_le_mul_of_nonneg_right hCC ?_
        have h1 : 0 ≤ δ' * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun := by
          have := mul_nonneg hδ' hX
          linarith only [this, mul_assoc δ' ((3 : ℝ) ^ k) (Section6.cubeFlat k u.toFun)]
        have h2 : 0 ≤ s'⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F := by
          have := mul_nonneg hs'i hY
          linarith only [this, mul_assoc s'⁻¹ (((3 : ℝ) ^ k) ^ 2) F]
        linarith only [h1, h2]

theorem LipCaccBdry.mono [NeZero d] {a : CoeffField d} {nu s s' C C' E : ℝ} {W : Set (Vec d)}
    {z : Vec d} {j : ℕ} (h : LipCaccBdry a nu s C E W z j) (hs : 0 < s) (hs1 : s ≤ 2 * s')
    (hs2 : s' ≤ 2 * s) (hC : 0 ≤ C) (hCC : 2 * C ≤ C') : LipCaccBdry a nu s' C' E W z j := by
  intro f γ u hγ hsol hz
  have hs' : 0 < s' := by linarith only [hs, hs1]
  refine (h f γ u hγ hsol hz).trans ?_
  have e1 : C * s ≤ C' * s' := by
    calc C * s ≤ C * (2 * s') := mul_le_mul_of_nonneg_left hs1 hC
      _ = (2 * C) * s' := by ring
      _ ≤ C' * s' := mul_le_mul_of_nonneg_right hCC hs'.le
  have e2 : C * s⁻¹ ≤ C' * s'⁻¹ := by
    calc C * s⁻¹ ≤ C * (2 * s'⁻¹) := mul_le_mul_of_nonneg_left (lip_inv_le hs' hs2) hC
      _ = (2 * C) * s'⁻¹ := by ring
      _ ≤ C' * s'⁻¹ := mul_le_mul_of_nonneg_right hCC (inv_nonneg.2 hs'.le)
  have e3 : C ≤ C' := by linarith only [hC, hCC]
  have e4 : ∀ t : ℝ, 0 ≤ t → C * t ≤ C' * t := fun t ht => mul_le_mul_of_nonneg_right e3 ht
  have o1 : C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2 ≤ C' * s' * (((3 : ℝ)⁻¹) ^ j) ^ 2 :=
    mul_le_mul_of_nonneg_right e1 (by positivity)
  have o2 : C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2 ≤ C' * s'⁻¹ * ((3 : ℝ) ^ j) ^ 2 :=
    mul_le_mul_of_nonneg_right e2 (by positivity)
  have o4 : C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 ≤
      C' * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 := by
    have := e4 (((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2) (by positivity)
    calc C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2
        = C * (((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2) := by ring
      _ ≤ C' * (((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2) := this
      _ = _ := by ring
  have o3 : C * s ≤ C' * s' := e1
  gcongr

theorem lip_exists_cutoff {K B' : Set (Vec d)} (hK : IsCompact K) (hB' : IsOpen B')
    (hKB : K ⊆ B') :
    ∃ ζ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ B' ∧
      ∀ x ∈ K, ζ x = 1 := by
  obtain ⟨ε, hε, hεB⟩ := hK.exists_cthickening_subset_open hB' hKB
  have hcl : IsClosed ((Metric.thickening ε K)ᶜ) := Metric.isOpen_thickening.isClosed_compl
  have hdis : Disjoint ((Metric.thickening ε K)ᶜ) K :=
    Set.disjoint_compl_left_iff_subset.2 (Metric.self_subset_thickening hε K)
  obtain ⟨ζ, hζ, -, hζ0, hζ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) hcl hK.isClosed hdis
  have hsupp : tsupport ζ ⊆ Metric.cthickening ε K := by
    refine closure_minimal ?_ Metric.isClosed_cthickening
    intro x hx
    by_contra hxn
    exact hx ((hζ0 x).1 (fun h => hxn (Metric.thickening_subset_cthickening _ _ h)))
  refine ⟨ζ, hζ, ?_, hsupp.trans hεB, fun x hx => (hζ1 x).1 hx⟩
  exact (hK.cthickening (r := ε)).of_isClosed_subset (isClosed_tsupport ζ) hsupp

/-- A localized zero trace restricts to a smaller open set and a smaller open window, when the two
sets agree inside the smaller window. -/
theorem lip_localized_restrict {Ω Ω' B B' : Set (Vec d)} {v : Vec d → ℝ} (hΩ' : IsOpen Ω')
    (hB' : IsOpen B') (hΩ : Ω' ⊆ Ω) (hBB : B' ⊆ B) (hagree : Ω ∩ B' = Ω' ∩ B')
    (h : LocalizedZeroTraceFunctionOn Ω B v) : LocalizedZeroTraceFunctionOn Ω' B' v := by
  intro η hη hηc hηT
  obtain ⟨ζ, hζ, hζc, hζT, hζ1⟩ := lip_exists_cutoff hηc hB' hηT
  obtain ⟨W₁, hW₁⟩ := h ζ hζ hζc (hζT.trans hBB)
  let W := W₁.mulContDiffHasCompactSupport hη hηc
  have hsub : ∀ n, tsupport (W.approx n) ⊆ Ω' := fun n x hx => by
    have h1 : x ∈ Ω ∩ B' := ⟨W₁.approx_support_subset n (tsupport_mul_subset_right hx),
      hηT (tsupport_mul_subset_left hx)⟩
    rw [hagree] at h1
    exact h1.1
  have hle : (volume.restrict Ω' : Measure (Vec d)) ≤ volume.restrict Ω :=
    Measure.restrict_mono hΩ le_rfl
  refine ⟨{ toH1Function := W.toH1Function.restrict hΩ' hΩ
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
    show η x * W₁.toH1Function.toFun x = η x * v x
    rw [h1]
    by_cases hx : η x = 0
    · simp [hx]
    · have : ζ x = 1 := hζ1 x (subset_tsupport _ hx)
      rw [← mul_assoc, this, mul_one]

theorem lip_restrict_integral_vecDot {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    (F : Vec d → Vec d) (phi : H10Function V) :
    ∫ x in W, vecDot (F x)
        ((Section8.Common.ExcessDecay.h10ExtendToSuperset phi hV hVW).toH1Function.grad x)
        ∂volume =
      ∫ x in V, vecDot (F x) (phi.toH1Function.grad x) ∂volume := by
  have hindicator :
      (fun x ↦ vecDot (F x)
        ((Section8.Common.ExcessDecay.h10ExtendToSuperset phi hV hVW).toH1Function.grad x)) =
        V.indicator (fun x ↦ vecDot (F x) (phi.toH1Function.grad x)) := by
    funext x
    rw [Section8.Common.ExcessDecay.h10ExtendToSuperset_grad phi hV hVW]
    by_cases hx : x ∈ V
    · simp only [Section8.Common.ExcessDecay.h10ZeroExtensionGrad_of_mem phi hx,
        Set.indicator_of_mem hx]
    · simp only [Section8.Common.ExcessDecay.h10ZeroExtensionGrad_of_not_mem phi hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [hindicator, integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVW]

theorem lip_restrict_integral_mul {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    (g : Vec d → ℝ) (phi : H10Function V) :
    ∫ x in W, g x *
        (Section8.Common.ExcessDecay.h10ExtendToSuperset phi hV hVW).toH1Function.toFun x
        ∂volume =
      ∫ x in V, g x * phi.toH1Function.toFun x ∂volume := by
  have hindicator :
      (fun x ↦ g x *
        (Section8.Common.ExcessDecay.h10ExtendToSuperset phi hV hVW).toH1Function.toFun x) =
        V.indicator (fun x ↦ g x * phi.toH1Function.toFun x) := by
    funext x
    rw [Section8.Common.ExcessDecay.h10ExtendToSuperset_toFun phi hV hVW]
    by_cases hx : x ∈ V
    · simp only [Section8.Common.ExcessDecay.h10ZeroExtension_of_mem phi hx,
        Set.indicator_of_mem hx]
    · simp only [Section8.Common.ExcessDecay.h10ZeroExtension_of_not_mem phi hx,
        Set.indicator_of_notMem hx, mul_zero]
  rw [hindicator, integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVW]

/-- Restriction of a weak solution to an open subset. -/
theorem IsWeakSolutionOn.restrict' {a : CoeffField d} {U V : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} (hw : IsWeakSolutionOn a U u f (fun _ => 0)) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsWeakSolutionOn a V (u.restrict hV hVU) f (fun _ => 0) := by
  intro phi
  have h := hw (Section8.Common.ExcessDecay.h10ExtendToSuperset phi hV.measurableSet hVU)
  rw [lip_restrict_integral_vecDot hV.measurableSet hVU, lip_restrict_integral_mul hV.measurableSet hVU,
    lip_restrict_integral_vecDot hV.measurableSet hVU] at h
  exact h

end SuperdiffusionCLT.Section7
