/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Geometry.TriadicPartition
public import SuperdiffusionCLT.Assumptions.ShellLaw.J1Consequences
public import SuperdiffusionCLT.Section2.Annealed.MixingStepEConcentration

/-!
# The colour partition of the Step-E descendants

`MixingStepEConcentration` reduces the Step-E Loewner
input `hStepE` to an explicit colour partition of the depth-`(n - h)`
descendants of `cu_n` into `m`-shell-separated classes, which it carries as a hypothesis
`hpart`. This module *constructs* the partition and so discharges `hpart`.

## The colouring and its modulus

A descendant of `cu_n` at depth `(n - h)` is a scale-`h` triadic cube whose
lattice index runs over a translate of `{0, ..., 3^(n-h) - 1}^d`.  The colour of
such a cube is the coordinatewise residue class of its lattice index modulo the
explicit modulus

`descendantColorModulus d m = 3^m * d + 1`,

a vector in `Fin d → Fin (descendantColorModulus d m)`.  The number of colours
is at most `K^d` with `K = 3^m * d + 1`.

## Why the modulus carries a `d` and not just the `K - 1` slack

Two scale-`h` cubes at lattice offset `K` in a coordinate are only `(K - 1) * 3^h`
apart *as sets* (the half-open realizations meet on the intervening slabs), so a
naive residue-class colouring at modulus `K` does not separate: one needs
`(K - 1) * 3^h ≥ 3^m` for the *set* distance.  That is the slack `Δ ≥ 1` of the
source construction and it is not enough here, because `AreShellSeparated` is
measured in the *Euclidean* norm against the threshold `3^m * sqrt d`, and two
same-colour descendants need not differ in every coordinate (`(0, 0)` and
`(K, 0)` share the second lattice coordinate).  A single differing coordinate
must therefore carry the whole threshold `3^m * sqrt d`.  Taking
`K - 1 = 3^m * d` gives `(K - 1) * 3^h = 3^m * d * 3^h ≥ 3^m * sqrt d` for every
`h ≥ 0` and every `d`, and the modulus is *independent of `h` and `n`*, so the
colour type is fixed across the whole family.

## Main results

* `descendantColor`, `descendantColorModulus`: the colouring and its modulus;
* `descendantColor_eq_iff_modEq`: colour equality is coordinatewise congruence;
* `areShellSeparated_of_descendantColor_eq`: same-colour distinct cubes of equal
  scale are `m`-shell-separated (the geometric core);
* `descendantColorPartition`: the fibres of the colouring partition the
  descendants into nonempty, pairwise disjoint, `m`-shell-separated classes,
  covering the whole descendant family, with at most `K^d` classes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The modulus and the colouring -/

/-- The residue modulus of the descendant colouring at shell `m`: `K - 1 = 3^m * d`
makes the set distance `(K - 1) * 3^h` of two same-colour cubes clear the
Euclidean shell-`m` threshold `3^m * sqrt d`. -/
def descendantColorModulus (d m : ℕ) : ℕ := 3 ^ m * d + 1

theorem descendantColorModulus_pos (d m : ℕ) : 0 < descendantColorModulus d m := by
  unfold descendantColorModulus
  omega

/-- The colour of a triadic cube: the coordinatewise residue class of its
lattice index modulo the descendant modulus. -/
def descendantColor (d m : ℕ) (R : TriadicCube d) :
    Fin d → Fin (descendantColorModulus d m) := fun i =>
  ⟨Int.toNat (R.index i % (descendantColorModulus d m : ℤ)), by
    have hnonneg : 0 ≤ R.index i % (descendantColorModulus d m : ℤ) :=
      Int.emod_nonneg _ (by
        have h : (0 : ℤ) < (descendantColorModulus d m : ℤ) := by
          exact_mod_cast descendantColorModulus_pos d m
        omega)
    have hlt : R.index i % (descendantColorModulus d m : ℤ) <
        (descendantColorModulus d m : ℤ) :=
      Int.emod_lt_of_pos _ (by
        have h : (0 : ℤ) < (descendantColorModulus d m : ℤ) := by
          exact_mod_cast descendantColorModulus_pos d m
        exact h)
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

@[simp] theorem descendantColor_val (d m : ℕ) (R : TriadicCube d) (i : Fin d) :
    (descendantColor d m R i : ℕ) =
      Int.toNat (R.index i % (descendantColorModulus d m : ℤ)) := rfl

/-- Colour equality is exactly coordinatewise congruence of the lattice indices
modulo the descendant modulus. -/
theorem descendantColor_eq_iff_modEq {d m : ℕ} {R S : TriadicCube d} :
    descendantColor d m R = descendantColor d m S ↔
      ∀ i, R.index i ≡ S.index i [ZMOD (descendantColorModulus d m : ℤ)] := by
  constructor
  · intro h i
    change R.index i % (descendantColorModulus d m : ℤ) =
      S.index i % (descendantColorModulus d m : ℤ)
    have hval : Int.toNat (R.index i % (descendantColorModulus d m : ℤ)) =
        Int.toNat (S.index i % (descendantColorModulus d m : ℤ)) := by
      simpa only [descendantColor] using
        congrArg Fin.val (congrArg (fun c : Fin d → Fin (descendantColorModulus d m) => c i) h)
    have hcast : (((Int.toNat (R.index i % (descendantColorModulus d m : ℤ)) : ℕ) : ℤ)) =
        Int.toNat (S.index i % (descendantColorModulus d m : ℤ)) := by
      exact_mod_cast hval
    have hR_nonneg : 0 ≤ R.index i % (descendantColorModulus d m : ℤ) :=
      Int.emod_nonneg _ (by
        have h : (0 : ℤ) < (descendantColorModulus d m : ℤ) := by
          exact_mod_cast descendantColorModulus_pos d m
        omega)
    have hS_nonneg : 0 ≤ S.index i % (descendantColorModulus d m : ℤ) :=
      Int.emod_nonneg _ (by
        have h : (0 : ℤ) < (descendantColorModulus d m : ℤ) := by
          exact_mod_cast descendantColorModulus_pos d m
        omega)
    simpa only [Int.toNat_of_nonneg hR_nonneg, Int.toNat_of_nonneg hS_nonneg] using hcast
  · intro h
    funext i
    apply Fin.ext
    have hmod : R.index i % (descendantColorModulus d m : ℤ) =
        S.index i % (descendantColorModulus d m : ℤ) := by
      simpa only [Int.ModEq] using h i
    have hR_nonneg : 0 ≤ R.index i % (descendantColorModulus d m : ℤ) :=
      Int.emod_nonneg _ (by
        have h : (0 : ℤ) < (descendantColorModulus d m : ℤ) := by
          exact_mod_cast descendantColorModulus_pos d m
        omega)
    have hS_nonneg : 0 ≤ S.index i % (descendantColorModulus d m : ℤ) :=
      Int.emod_nonneg _ (by
        have h : (0 : ℤ) < (descendantColorModulus d m : ℤ) := by
          exact_mod_cast descendantColorModulus_pos d m
        omega)
    simpa only [descendantColor] using
      congrArg Int.toNat hmod

/-- Same colour gives divisibility of the lattice offset by the modulus. -/
theorem dvd_index_sub_of_descendantColor_eq {d m : ℕ} {R S : TriadicCube d}
    (hcolor : descendantColor d m R = descendantColor d m S) (i : Fin d) :
    (descendantColorModulus d m : ℤ) ∣ S.index i - R.index i :=
  Int.modEq_iff_dvd.mp ((descendantColor_eq_iff_modEq.mp hcolor) i)

/-- A nonzero multiple of `K > 0` is at least `K` in absolute value, in either
orientation. -/
theorem le_or_le_neg_of_dvd_sub {K : ℕ} (hK : 0 < K) {a b : ℤ}
    (hdvd : (K : ℤ) ∣ b - a) (hne : a ≠ b) :
    (K : ℤ) ≤ a - b ∨ (K : ℤ) ≤ b - a := by
  have hKZ : (0 : ℤ) < K := by exact_mod_cast hK
  have hne' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · left
    have hdvd' : (K : ℤ) ∣ -(b - a) := Int.dvd_neg.mpr hdvd
    have hpos : 0 < -(b - a) := by linarith only [hlt]
    have := (Int.le_iff_pos_of_dvd hKZ hdvd').mpr hpos
    linarith only [this]
  · right
    exact (Int.le_iff_pos_of_dvd hKZ hdvd).mpr hgt

/-- The Euclidean norm dominates every coordinate. -/
theorem abs_apply_le_vecNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ Homogenization.Book.Ch02.vecNorm v := by
  have hsq : (v i) ^ 2 ≤ Homogenization.Book.Ch02.vecNorm v ^ 2 := by
    rw [Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]
    exact sq_apply_le_vecNormSq v i
  calc |v i| = Real.sqrt ((v i) ^ 2) := (Real.sqrt_sq_eq_abs (v i)).symm
    _ ≤ Real.sqrt (Homogenization.Book.Ch02.vecNorm v ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Homogenization.Book.Ch02.vecNorm v :=
        Real.sqrt_sq (Homogenization.Book.Ch02.vecNorm_nonneg v)

theorem sqrt_natCast_le_self (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    calc (d : ℝ) = (d : ℝ) * 1 := by ring
      _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (d : ℝ) ^ 2 := by ring

/-- **The modulus clears the shell.**  `((K - 1) * 3^h)` dominates the Euclidean
threshold `3^m * sqrt d` for the explicit `K = 3^m * d + 1`, uniformly in `h`. -/
theorem modulus_bound {d m h : ℕ} :
    (3 : ℝ) ^ m * Real.sqrt (d : ℝ) ≤
      ((descendantColorModulus d m : ℝ) - 1) * (3 : ℝ) ^ h := by
  have hK : (descendantColorModulus d m : ℝ) - 1 = (3 : ℝ) ^ m * (d : ℝ) := by
    unfold descendantColorModulus
    push_cast
    ring
  rw [hK, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : (1 : ℝ) ≤ (3 : ℝ) ^ h := one_le_pow₀ (by norm_num)
  calc Real.sqrt (d : ℝ) ≤ (d : ℝ) := sqrt_natCast_le_self d
    _ = (d : ℝ) * 1 := by ring
    _ ≤ (d : ℝ) * (3 : ℝ) ^ h := mul_le_mul_of_nonneg_left hs (by positivity)

/-! ## The single-coordinate geometry -/

/-- If the lattice index of `R` exceeds that of `S` by at least the modulus, the
coordinate gap of any two points of the two cubes is at least `(K - 1) * 3^h`.
The half-open realizations are responsible for the `K - 1`. -/
theorem coord_le_of_index_le {d m h : ℕ} {R S : TriadicCube d} {i : Fin d}
    (hRscale : R.scale = (h : ℤ)) (hSscale : S.scale = (h : ℤ))
    (hle : (descendantColorModulus d m : ℤ) ≤ R.index i - S.index i)
    {x y : Vec d} (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet S) :
    ((descendantColorModulus d m : ℝ) - 1) * (3 : ℝ) ^ h ≤ x i - y i := by
  have hR := hx i
  have hS := hy i
  simp only [cubeScaleFactor, hRscale, hSscale, zpow_natCast] at hR hS
  have hs : (0 : ℝ) < (3 : ℝ) ^ h := by positivity
  have hKle : ((descendantColorModulus d m : ℝ) - 1) ≤
      ((R.index i : ℝ) - (S.index i : ℝ) - 1) := by
    have hcast : (descendantColorModulus d m : ℝ) ≤ (R.index i : ℝ) - (S.index i : ℝ) := by
      exact_mod_cast hle
    linarith only [hcast]
  have hmul : ((descendantColorModulus d m : ℝ) - 1) * (3 : ℝ) ^ h ≤
      ((R.index i : ℝ) - (S.index i : ℝ) - 1) * (3 : ℝ) ^ h :=
    mul_le_mul_of_nonneg_right hKle hs.le
  have h1 : (((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ h) ≤ x i := hR.1
  have h2 : -((((S.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ h)) < -y i := by linarith only [hS.2]
  have h3 := add_lt_add_of_le_of_lt h1 h2
  have h4 : ((R.index i : ℝ) - (S.index i : ℝ) - 1) * (3 : ℝ) ^ h =
      ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ h +
        (-((((S.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ h))) := by ring
  have hcoord : ((R.index i : ℝ) - (S.index i : ℝ) - 1) * (3 : ℝ) ^ h < x i - y i := by
    rw [h4]
    simpa only [sub_eq_add_neg] using h3
  linarith only [hmul, hcoord]

/-- The absolute coordinate gap bound, in whichever order the indices differ. -/
theorem modulus_sub_one_mul_scale_le_abs_coord {d m h : ℕ} {R S : TriadicCube d} {i : Fin d}
    (hRscale : R.scale = (h : ℤ)) (hSscale : S.scale = (h : ℤ))
    (hcase : (descendantColorModulus d m : ℤ) ≤ R.index i - S.index i ∨
      (descendantColorModulus d m : ℤ) ≤ S.index i - R.index i)
    {x y : Vec d} (hx : x ∈ cubeSet R) (hy : y ∈ cubeSet S) :
    ((descendantColorModulus d m : ℝ) - 1) * (3 : ℝ) ^ h ≤ |x i - y i| := by
  rcases hcase with hle | hle
  · exact le_trans (coord_le_of_index_le hRscale hSscale hle hx hy) (le_abs_self _)
  · have h := coord_le_of_index_le hSscale hRscale hle hy hx
    have hneg : y i - x i = -(x i - y i) := by ring
    rw [hneg] at h
    exact le_trans h (neg_le_abs _)

/-- **The geometric core**: two distinct same-colour cubes of the same scale `h`
are `m`-shell-separated. -/
theorem areShellSeparated_of_descendantColor_eq {d m h : ℕ} {R S : TriadicCube d}
    (hRscale : R.scale = (h : ℤ)) (hSscale : S.scale = (h : ℤ))
    (hne : R ≠ S) (hcolor : descendantColor d m R = descendantColor d m S) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.AreShellSeparated m
      (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  have hKpos : 0 < descendantColorModulus d m := descendantColorModulus_pos d m
  have hidx : ∃ i, R.index i ≠ S.index i := by
    by_contra h
    push Not at h
    apply hne
    have hidxeq : R.index = S.index := funext h
    rcases R with ⟨sR, iR⟩
    rcases S with ⟨sS, iS⟩
    have hscale : sR = sS := hRscale.trans hSscale.symm
    simp only [TriadicCube.mk.injEq]
    exact ⟨hscale, hidxeq⟩
  rcases hidx with ⟨i, hi⟩
  have hcoord := modulus_sub_one_mul_scale_le_abs_coord hRscale hSscale
    (le_or_le_neg_of_dvd_sub hKpos (dvd_index_sub_of_descendantColor_eq hcolor i) hi) hx hy
  have hnorm : |x i - y i| ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
    simpa only [Pi.sub_apply] using abs_apply_le_vecNorm (x - y) i
  exact le_trans (modulus_bound (d := d) (m := m) (h := h)) (le_trans hcoord hnorm)

/-! ## The partition -/

/-- The set of colours realised by the depth-`(n - h)` descendants of `cu_n`. -/
def descendantColorSet (d m n h : ℕ) : Finset (Fin d → Fin (descendantColorModulus d m)) :=
  (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).image (descendantColor d m)

/-- The colour class of `c`: the descendants of `cu_n` of colour `c`. -/
def descendantColorClass (d m n h : ℕ)
    (c : Fin d → Fin (descendantColorModulus d m)) : Finset (TriadicCube d) :=
  (descendantsAtDepth (originCube d (n : ℤ)) (n - h)).filter
    (fun R => descendantColor d m R = c)

theorem mem_descendantColorClass_iff {d m n h : ℕ} {R : TriadicCube d}
    {c : Fin d → Fin (descendantColorModulus d m)} :
    R ∈ descendantColorClass d m n h c ↔
      R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h) ∧
        descendantColor d m R = c := by
  simp only [descendantColorClass, Finset.mem_filter]

/-- A depth-`(n - h)` descendant of `cu_n` has scale `h`. -/
theorem scale_eq_of_mem_descendantsAtDepth_originCube {d n h : ℕ} (hle : h ≤ n)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h)) :
    R.scale = (h : ℤ) := by
  rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
  have : ((n - h : ℕ) : ℤ) = (n : ℤ) - (h : ℤ) := by omega
  rw [this]
  simp only [originCube]
  ring

theorem descendantColorSet_nonempty (d m n h : ℕ) :
    (descendantColorSet d m n h).Nonempty :=
  (descendantsAtDepth_nonempty (originCube d (n : ℤ)) (n - h)).image (descendantColor d m)

theorem disjoint_descendantColorClass_of_ne {d m n h : ℕ}
    {c₁ c₂ : Fin d → Fin (descendantColorModulus d m)} (hne : c₁ ≠ c₂) :
    Disjoint (descendantColorClass d m n h c₁) (descendantColorClass d m n h c₂) := by
  rw [Finset.disjoint_left]
  intro R hR₁ hR₂
  rw [mem_descendantColorClass_iff] at hR₁ hR₂
  exact hne (hR₁.2.symm.trans hR₂.2)

theorem pairwiseDisjoint_descendantColorClass (d m n h : ℕ) :
    ((descendantColorSet d m n h : Set (Fin d → Fin (descendantColorModulus d m)))).PairwiseDisjoint
      (descendantColorClass d m n h) := by
  intro c₁ _ c₂ _ hne
  exact disjoint_descendantColorClass_of_ne hne

/-- The colour classes cover the whole descendant family. -/
theorem biUnion_descendantColorClass (d m n h : ℕ) :
    (descendantColorSet d m n h).biUnion (descendantColorClass d m n h) =
      descendantsAtDepth (originCube d (n : ℤ)) (n - h) :=
  Finset.image_biUnion_filter_eq _ _

/-- Every realised colour has a nonempty class. -/
theorem exists_mem_of_mem_descendantColorSet {d m n h : ℕ}
    {c : Fin d → Fin (descendantColorModulus d m)} (hc : c ∈ descendantColorSet d m n h) :
    (descendantColorClass d m n h c).Nonempty := by
  rw [descendantColorSet, Finset.mem_image] at hc
  obtain ⟨R, hR, hRc⟩ := hc
  exact ⟨R, by rw [mem_descendantColorClass_iff]; exact ⟨hR, hRc⟩⟩

/-- Every class is pairwise `m`-shell-separated. -/
theorem areShellSeparated_of_mem_descendantColorClass {d m n h : ℕ} (hhm : h < m)
    (hmn : m ≤ n) {c : Fin d → Fin (descendantColorModulus d m)} {R S : TriadicCube d}
    (hR : R ∈ descendantColorClass d m n h c) (hS : S ∈ descendantColorClass d m n h c)
    (hne : R ≠ S) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.AreShellSeparated m
      (cubeSet R) (cubeSet S) := by
  have hle : h ≤ n := by omega
  rw [mem_descendantColorClass_iff] at hR hS
  have hcolor : descendantColor d m R = descendantColor d m S := hR.2.trans hS.2.symm
  exact areShellSeparated_of_descendantColor_eq
    (scale_eq_of_mem_descendantsAtDepth_originCube hle hR.1)
    (scale_eq_of_mem_descendantsAtDepth_originCube hle hS.1) hne hcolor

/-- The class count is at most `K^d`, the number of colour vectors. -/
theorem card_descendantColorSet_le (d m n h : ℕ) :
    (descendantColorSet d m n h).card ≤ (descendantColorModulus d m) ^ d := by
  calc (descendantColorSet d m n h).card
      ≤ (Finset.univ : Finset (Fin d → Fin (descendantColorModulus d m))).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (Fin d → Fin (descendantColorModulus d m)) := Finset.card_univ
    _ = (descendantColorModulus d m) ^ d := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **The colour partition of the Step-E descendants.**  The fibres of the
residue-class colouring `descendantColor` on the depth-`(n - h)` descendants of
`cu_n` are nonempty, pairwise disjoint, cover the whole family, and are pairwise
`m`-shell-separated; there are at most `K^d` of them, with the explicit modulus
`K = 3^m * d + 1`.  This is the hypothesis `hpart` of
the Step-E concentration argument. -/
theorem descendantColorPartition {m n h : ℕ} (hhm : h < m) (hmn : m ≤ n) :
    (descendantColorSet d m n h).Nonempty ∧
    ((descendantColorSet d m n h : Set (Fin d → Fin (descendantColorModulus d m)))).PairwiseDisjoint
      (descendantColorClass d m n h) ∧
    (descendantColorSet d m n h).biUnion (descendantColorClass d m n h) =
      descendantsAtDepth (originCube d (n : ℤ)) (n - h) ∧
    (∀ c ∈ descendantColorSet d m n h, (descendantColorClass d m n h c).Nonempty) ∧
    (∀ c ∈ descendantColorSet d m n h, ∀ R ∈ descendantColorClass d m n h c,
      ∀ S ∈ descendantColorClass d m n h c, R ≠ S →
        SuperdiffusionCLT.Frozen.Assumptions.ShellField.AreShellSeparated m
          (cubeSet R) (cubeSet S)) ∧
    (descendantColorSet d m n h).card ≤ (descendantColorModulus d m) ^ d :=
  ⟨descendantColorSet_nonempty d m n h, pairwiseDisjoint_descendantColorClass d m n h,
    biUnion_descendantColorClass d m n h, fun _ hc => exists_mem_of_mem_descendantColorSet hc,
    fun _ _ R hR S hS hne =>
      areShellSeparated_of_mem_descendantColorClass (R := R) (S := S) hhm hmn hR hS hne,
    card_descendantColorSet_le d m n h⟩

/-! ## `hpart` discharged in the Step-E reduction -/

end

end SuperdiffusionCLT.Section2.Annealed
