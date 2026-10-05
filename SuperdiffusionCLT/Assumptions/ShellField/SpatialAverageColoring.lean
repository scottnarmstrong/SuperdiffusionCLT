/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable
public import SuperdiffusionCLT.Assumptions.ShellField.SpatialAverage
public import SuperdiffusionCLT.Assumptions.ShellLaw.J1Consequences
public import Homogenization.Besov.Localization

/-!
# Colouring and deterministic bounds for shell spatial averages

This module prepares the geometry and the deterministic estimates behind the
manuscript's one-shell spatial-average bound `e.jk.spatialavg`.

Triadic cubes of a common scale are coloured by the coordinatewise residue of
their triadic index modulo `Nat.sqrt d + 2`. Two distinct cubes of one colour
at scale `k` are then at sup-distance at least `(Nat.sqrt d + 1) 3 ^ k`, hence
at Euclidean distance at least `3 ^ k √d`, which is exactly the separation
required by the marginal J1 assumption.

The deterministic half bounds every entry of a translated cube average by the
shell's exact `L∞` value norm on a natural cube, and writes the average over a
cube as the average of the averages over its descendants.

## Main definitions

* `shellColorPeriod`, `ShellCubeColor`, `cubeShellColor`.

## Main results

* `areShellSeparated_cubeSet_of_cubeShellColor_eq`: the colouring geometry.
* `abs_translatedShellCubeAverage_entry_le`: the deterministic `L∞` bound.
* `translatedShellCubeAverage_entry_eq_descendants`: the partition identity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization MeasureTheory
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## Colouring the triadic cubes at the J1 range -/

/-- The colour period used to separate triadic cubes at the marginal J1 range
`3 ^ k √d`: two triadic indices in the same residue class modulo this period
differ by at least `Nat.sqrt d + 2`, hence the corresponding scale-`k` cubes
are at sup-distance at least `(Nat.sqrt d + 1) 3 ^ k ≥ √d 3 ^ k`. The integer
square root keeps the period computable, so instance search never unfolds a
real-valued ceiling. -/
def shellColorPeriod (d : ℕ) : ℕ :=
  Nat.sqrt d + 2

theorem shellColorPeriod_pos (d : ℕ) : 0 < shellColorPeriod d := by
  simp only [shellColorPeriod]
  omega

theorem shellColorPeriod_int_pos (d : ℕ) : 0 < (shellColorPeriod d : ℤ) := by
  exact_mod_cast shellColorPeriod_pos d

theorem shellColorPeriod_int_ne_zero (d : ℕ) : (shellColorPeriod d : ℤ) ≠ 0 :=
  (shellColorPeriod_int_pos d).ne'

/-- The defining property of the colour period: one less than the period
already dominates `√d`. -/
theorem sqrt_le_shellColorPeriod_sub_one (d : ℕ) :
    Real.sqrt (d : ℝ) ≤ (shellColorPeriod d : ℝ) - 1 := by
  have h : Real.sqrt (d : ℝ) ≤ (Nat.sqrt d : ℝ) + 1 :=
    Real.real_sqrt_le_nat_sqrt_succ
  simp only [shellColorPeriod, Nat.cast_add, Nat.cast_ofNat]
  linarith only [h]

/-- The colours attached to triadic cubes at the marginal J1 range. -/
abbrev ShellCubeColor (d : ℕ) := Fin d → Fin (shellColorPeriod d)

/-- The colour of a triadic cube: the coordinatewise residue class of its
triadic index modulo `shellColorPeriod d`. -/
def cubeShellColor (Q : TriadicCube d) : ShellCubeColor d := fun i ↦
  ⟨Int.toNat (Q.index i % (shellColorPeriod d : ℤ)), by
    have hnonneg : 0 ≤ Q.index i % (shellColorPeriod d : ℤ) :=
      Int.emod_nonneg _ (shellColorPeriod_int_ne_zero d)
    have hlt : Q.index i % (shellColorPeriod d : ℤ) < (shellColorPeriod d : ℤ) :=
      Int.emod_lt_of_pos _ (shellColorPeriod_int_pos d)
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

theorem cubeShellColor_eq_iff_modEq {R S : TriadicCube d} :
    cubeShellColor R = cubeShellColor S ↔
      ∀ i, R.index i ≡ S.index i [ZMOD (shellColorPeriod d : ℤ)] := by
  have hR_nonneg : ∀ i : Fin d, 0 ≤ R.index i % (shellColorPeriod d : ℤ) :=
    fun i ↦ Int.emod_nonneg _ (shellColorPeriod_int_ne_zero d)
  have hS_nonneg : ∀ i : Fin d, 0 ≤ S.index i % (shellColorPeriod d : ℤ) :=
    fun i ↦ Int.emod_nonneg _ (shellColorPeriod_int_ne_zero d)
  constructor
  · intro h i
    change R.index i % (shellColorPeriod d : ℤ) =
      S.index i % (shellColorPeriod d : ℤ)
    have hval : Int.toNat (R.index i % (shellColorPeriod d : ℤ)) =
        Int.toNat (S.index i % (shellColorPeriod d : ℤ)) := by
      simpa only [cubeShellColor] using
        congrArg Fin.val (congrArg (fun c : ShellCubeColor d ↦ c i) h)
    have hcast : ((Int.toNat (R.index i % (shellColorPeriod d : ℤ)) : ℕ) : ℤ) =
        ((Int.toNat (S.index i % (shellColorPeriod d : ℤ)) : ℕ) : ℤ) := by
      exact_mod_cast hval
    rwa [Int.toNat_of_nonneg (hR_nonneg i),
      Int.toNat_of_nonneg (hS_nonneg i)] at hcast
  · intro h
    funext i
    apply Fin.ext
    have hmod : R.index i % (shellColorPeriod d : ℤ) =
        S.index i % (shellColorPeriod d : ℤ) := h i
    simpa only [cubeShellColor] using congrArg Int.toNat hmod

/-- Two distinct triadic indices in the same residue class differ by at least
the colour period. -/
private theorem index_add_shellColorPeriod_le_of_lt {R S : TriadicCube d}
    {i : Fin d} (hcolor : cubeShellColor R = cubeShellColor S)
    (hlt : R.index i < S.index i) :
    R.index i + (shellColorPeriod d : ℤ) ≤ S.index i := by
  have hmod : R.index i ≡ S.index i [ZMOD (shellColorPeriod d : ℤ)] :=
    (cubeShellColor_eq_iff_modEq.mp hcolor) i
  rw [Int.modEq_iff_dvd] at hmod
  obtain ⟨n, hn⟩ := hmod
  have hperiod_pos : 0 < (shellColorPeriod d : ℤ) := shellColorPeriod_int_pos d
  have hdiff_pos : 0 < (shellColorPeriod d : ℤ) * n := by
    rw [← hn]
    exact sub_pos.mpr hlt
  have hn_pos : 0 < n := by
    by_contra hcon
    have hn_le : n ≤ 0 := le_of_not_gt hcon
    exact absurd hdiff_pos
      (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hperiod_pos.le hn_le))
  have hperiod_le : (shellColorPeriod d : ℤ) ≤ (shellColorPeriod d : ℤ) * n := by
    calc
      (shellColorPeriod d : ℤ) = (shellColorPeriod d : ℤ) * 1 := (mul_one _).symm
      _ ≤ (shellColorPeriod d : ℤ) * n :=
        mul_le_mul_of_nonneg_left hn_pos hperiod_pos.le
  omega

/-- Distinct triadic cubes of the same scale and the same colour are separated
at the marginal J1 range for that scale. -/
theorem areShellSeparated_cubeSet_of_cubeShellColor_eq {k : ℕ}
    {R S : TriadicCube d} (hR : R.scale = (k : ℤ)) (hS : S.scale = (k : ℤ))
    (hcolor : cubeShellColor R = cubeShellColor S) (hne : R ≠ S) :
    AreShellSeparated k (cubeSet R) (cubeSet S) := by
  have hfactorR : cubeScaleFactor R = (3 : ℝ) ^ k := by
    rw [cubeScaleFactor, hR, zpow_natCast]
  have hfactorS : cubeScaleFactor S = (3 : ℝ) ^ k := by
    rw [cubeScaleFactor, hS, zpow_natCast]
  have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hindex_ne : ∃ i, R.index i ≠ S.index i := by
    by_contra hcon
    push Not at hcon
    refine hne ?_
    cases R with
    | mk scaleR indexR =>
        cases S with
        | mk scaleS indexS =>
            simp only [TriadicCube.mk.injEq]
            exact ⟨hR.trans hS.symm, funext hcon⟩
  obtain ⟨i, hi⟩ := hindex_ne
  have hgap : ∀ (x y : Vec d), x ∈ cubeSet R → y ∈ cubeSet S →
      (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k ≤ |x i - y i| := by
    intro x y hx hy
    have hxi := hx i
    have hyi := hy i
    rw [hfactorR] at hxi
    rw [hfactorS] at hyi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hle : R.index i + (shellColorPeriod d : ℤ) ≤ S.index i :=
        index_add_shellColorPeriod_le_of_lt hcolor hlt
      have hreal : ((R.index i : ℝ) + (shellColorPeriod d : ℝ)) ≤ (S.index i : ℝ) := by
        exact_mod_cast hle
      have hsub : (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k ≤ y i - x i := by
        have h1 : ((R.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ k +
            (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k ≤
            ((S.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ k := by
          have hcoeff : ((R.index i : ℝ) + (1 / 2 : ℝ)) +
              (shellColorPeriod d - 1 : ℝ) ≤ ((S.index i : ℝ) - (1 / 2 : ℝ)) := by
            linarith only [hreal]
          calc
            ((R.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ k +
                (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k
                = (((R.index i : ℝ) + (1 / 2 : ℝ)) +
                    (shellColorPeriod d - 1 : ℝ)) * (3 : ℝ) ^ k := by ring
            _ ≤ ((S.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right hcoeff hpow_pos.le
        linarith only [h1, hxi.2, hyi.1]
      calc
        (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k ≤ y i - x i := hsub
        _ ≤ |x i - y i| := by
          rw [abs_sub_comm]
          exact le_abs_self _
    · have hle : S.index i + (shellColorPeriod d : ℤ) ≤ R.index i :=
        index_add_shellColorPeriod_le_of_lt hcolor.symm hgt
      have hreal : ((S.index i : ℝ) + (shellColorPeriod d : ℝ)) ≤ (R.index i : ℝ) := by
        exact_mod_cast hle
      have hsub : (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k ≤ x i - y i := by
        have h1 : ((S.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ k +
            (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k ≤
            ((R.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ k := by
          have hcoeff : ((S.index i : ℝ) + (1 / 2 : ℝ)) +
              (shellColorPeriod d - 1 : ℝ) ≤ ((R.index i : ℝ) - (1 / 2 : ℝ)) := by
            linarith only [hreal]
          calc
            ((S.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ k +
                (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k
                = (((S.index i : ℝ) + (1 / 2 : ℝ)) +
                    (shellColorPeriod d - 1 : ℝ)) * (3 : ℝ) ^ k := by ring
            _ ≤ ((R.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right hcoeff hpow_pos.le
        linarith only [h1, hyi.2, hxi.1]
      exact hsub.trans (le_abs_self _)
  intro x y hx hy
  have hcoord : (3 : ℝ) ^ k * Real.sqrt (d : ℝ) ≤ |(x - y) i| := by
    have hle : (3 : ℝ) ^ k * Real.sqrt (d : ℝ) ≤
        (shellColorPeriod d - 1 : ℝ) * (3 : ℝ) ^ k := by
      rw [mul_comm ((3 : ℝ) ^ k)]
      exact mul_le_mul_of_nonneg_right (sqrt_le_shellColorPeriod_sub_one d)
        hpow_pos.le
    simpa only [Pi.sub_apply] using hle.trans (hgap x y hx hy)
  have hsup : |(x - y) i| ≤ ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  exact hcoord.trans (hsup.trans (norm_vec_le_vecNorm (x - y)))

/-- The J1 separation relation is invariant under a common translation of
both read regions. -/
theorem AreShellSeparated.translate {n : ℕ} {U V : Set (Vec d)} (z : Vec d)
    (h : AreShellSeparated n U V) :
    AreShellSeparated n (translateSet z U) (translateSet z V) := by
  intro x w hx hw
  rw [mem_translateSet_iff_sub_mem] at hx hw
  have hsub : x - w = (x - z) - (w - z) := by abel
  rw [hsub]
  exact h hx hw

/-- The translated read region of a triadic cube is measurable. -/
theorem measurableSet_translateSet_cubeSet (z : Vec d) (Q : TriadicCube d) :
    MeasurableSet (translateSet z (cubeSet Q)) := by
  rw [← preimage_subRight_eq_translateSet]
  exact (continuous_id.sub continuous_const).measurable (measurableSet_cubeSet Q)

/-! ## Deterministic bounds for translated cube averages -/

private theorem continuous_shellTranslateEntry (y : Vec d) (j : ShellField d)
    (i l : Fin d) : Continuous (fun x : Vec d ↦ j (x + y) i l) :=
  (continuous_apply l).comp
    ((continuous_apply i).comp
      (j.1.1.continuous.comp (continuous_id.add continuous_const)))

private theorem integrableOn_shellTranslateEntry (y : Vec d) (Q : TriadicCube d)
    (j : ShellField d) (i l : Fin d) :
    IntegrableOn (fun x : Vec d ↦ j (x + y) i l) (cubeSet Q) volume :=
  ((continuous_shellTranslateEntry y j i l).locallyIntegrable.integrableOn_isCompact
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))).mono_set
    (cubeSet_subset_closedBall Q)

/-- Every entry of a translated cube average is bounded by the shell's exact
`L∞` value norm on the natural scale-`k` cube after the matching translation,
provided the cube sits inside that translated natural cube. -/
theorem abs_translatedShellCubeAverage_entry_le (y z : Vec d)
    (Q : TriadicCube d) (k : ℕ) (j : ShellField d) (i l : Fin d)
    (hQ : ∀ x ∈ openCubeSet Q, x - z ∈ openCubeSet (originCube d (k : ℤ))) :
    |translatedShellCubeAverage y Q j i l| ≤
      shellCubeValueNorm k (translate (z + y) j) := by
  have hshift : ∀ x : Vec d, x - z + (z + y) = x + y := by
    intro x
    abel
  have hbound : ∀ x ∈ openCubeSet Q,
      ‖j (x + y) i l‖ ≤ shellCubeValueNorm k (translate (z + y) j) := by
    intro x hx
    have hmem : x - z ∈ openCubeSet (originCube d (k : ℤ)) := hQ x hx
    have hpoint : translate (z + y) j (x - z) = j (x + y) := by
      rw [translate_apply, hshift x]
    have hop : matrixOperatorNorm (j (x + y)) ≤
        shellCubeValueNorm k (translate (z + y) j) := by
      have := matrixOperatorNorm_apply_le_shellCubeValueNorm k
        (translate (z + y) j) ⟨x - z, hmem⟩
      rwa [hpoint] at this
    rw [Real.norm_eq_abs]
    exact (abs_entry_le_matrixOperatorNorm (j (x + y)) i l).trans hop
  have hfin : volume (openCubeSet Q) < ⊤ :=
    (isBounded_openCubeSet Q).measure_lt_top
  have hint : ‖∫ x in openCubeSet Q, j (x + y) i l ∂volume‖ ≤
      shellCubeValueNorm k (translate (z + y) j) *
        (volume (openCubeSet Q)).toReal :=
    norm_setIntegral_le_of_norm_le_const hfin hbound
  have hvol : (volume (openCubeSet Q)).toReal = cubeVolume Q :=
    volume_openCubeSet_toReal Q
  have hvolpos : 0 < cubeVolume Q := cubeVolume_pos Q
  have hEq : translatedShellCubeAverage y Q j i l =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, j (x + y) i l ∂volume := by
    change (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, j (x + y) i l ∂volume =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, j (x + y) i l ∂volume
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  rw [hEq, abs_mul, abs_of_nonneg (inv_nonneg.2 hvolpos.le)]
  calc
    (cubeVolume Q)⁻¹ * |∫ x in openCubeSet Q, j (x + y) i l ∂volume|
        ≤ (cubeVolume Q)⁻¹ *
          (shellCubeValueNorm k (translate (z + y) j) * cubeVolume Q) := by
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hvolpos.le)
      rw [← hvol]
      simpa only [Real.norm_eq_abs] using hint
    _ = shellCubeValueNorm k (translate (z + y) j) := by
      field_simp

/-- The centred natural cube of scale `h` sits inside the natural cube of any
larger natural scale. -/
theorem openCubeSet_originCube_subset_of_le {h : ℤ} {k : ℕ} (hhk : h ≤ (k : ℤ)) :
    openCubeSet (originCube d h) ⊆ openCubeSet (originCube d (k : ℤ)) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ h ≤ (3 : ℝ) ^ (k : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hhk
  have hpos : (0 : ℝ) < (3 : ℝ) ^ h := zpow_pos (by norm_num) h
  refine ⟨lt_of_le_of_lt ?_ (hx i).1, lt_of_lt_of_le (hx i).2 ?_⟩
  · nlinarith only [hpow, hpos]
  · nlinarith only [hpow, hpos]

/-- A triadic cube of natural scale `k` is the translate of the natural
scale-`k` cube by its centre. -/
theorem sub_cubeCenter_mem_openCubeSet_originCube {k : ℕ} {Q : TriadicCube d}
    (hQ : Q.scale = (k : ℤ)) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    x - cubeCenter Q ∈ openCubeSet (originCube d (k : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hfactor : cubeScaleFactor Q = (3 : ℝ) ^ (k : ℤ) := by
    rw [cubeScaleFactor, hQ]
  have hxi := hx i
  rw [hfactor] at hxi
  have hcenter : cubeCenter Q i = (Q.index i : ℝ) * (3 : ℝ) ^ (k : ℤ) := by
    rw [cubeCenter, hfactor]
  simp only [Pi.sub_apply, hcenter]
  constructor
  · nlinarith only [hxi.1]
  · nlinarith only [hxi.2]

/-- The translated average over a cube is the average of the translated
averages over its descendants at a fixed depth, entry by entry. -/
theorem translatedShellCubeAverage_entry_eq_descendants
    (y : Vec d) (Q : TriadicCube d) (m : ℕ) (j : ShellField d) (i l : Fin d) :
    translatedShellCubeAverage y Q j i l =
      ((descendantsAtDepth Q m).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q m, translatedShellCubeAverage y R j i l := by
  have h := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q m
    (fun x : Vec d ↦ j (x + y) i l)
    (integrableOn_shellTranslateEntry y Q j i l)
  change cubeAverage Q (fun x : Vec d ↦ j (x + y) i l) = _ at h
  rw [descendantsAverage] at h
  exact h

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
