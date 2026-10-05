/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Geometry.TriadicCube
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Whitney interior of a ball: the digital ball

Local copies `wpd_shiftCube`, `wpd_whitneyInterior` of the carrier texts `shiftCube`,
`whitneyInterior`. For a Euclidean ball `V` of radius `ρ` the union of the grid cubes of side
`h = 3^j` whose enlargement by the scale `j + 3` stays in `V` is, as a set, the sublevel set `wpd_W0`
of the sum of squares of the rounded coordinates. Up to the null set of cube faces it equals the
open set `wpd_W`, where the absolute value is taken before rounding. The set `wpd_W` is open, lies in
`V`, contains a concentric ball at distance `(h/2 + r) √d`, is stable under the monotone
modification of the absolute values of coordinates, and is mapped into that concentric ball by the
shift `wpd_shift ℓ` of the large coordinates towards the origin, along segments inside `wpd_W`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The translated open triadic cube `y + cu_m` (local copy of the carrier text). -/
def wpd_shiftCube (y : Vec d) (m : ℤ) : Set (Vec d) :=
  (fun x => y + x) '' openCubeSet (originCube d m)

/-- The union of the grid cubes `z + cu_j`, `z ∈ 3^j ℤ^d ∩ V`, with `z + cu_{j+3} ⊆ V`
(local copy of the carrier text). -/
def wpd_whitneyInterior (V : Set (Vec d)) (j : ℤ) : Set (Vec d) :=
  ⋃ k : Fin d → ℤ,
    ⋃ (_ : (fun i => (3 : ℝ) ^ j * (k i : ℝ)) ∈ V ∧
        wpd_shiftCube (fun i => (3 : ℝ) ^ j * (k i : ℝ)) (j + 3) ⊆ V),
      (fun x => (fun i => (3 : ℝ) ^ j * (k i : ℝ)) + x) '' cubeSet (originCube d j)

theorem wpd_mem_shiftCube {y x : Vec d} {m : ℤ} :
    x ∈ wpd_shiftCube y m ↔ ∀ i, |x i - y i| < (3 : ℝ) ^ m / 2 := by
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    have h := hw i
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add] at h
    show |y i + w i - y i| < _
    rw [add_sub_cancel_left, abs_lt]
    constructor <;> linarith only [h.1, h.2]
  · intro h
    refine ⟨x - y, ?_, by simp⟩
    intro i
    have := abs_lt.1 (h i)
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add, Pi.sub_apply]
    constructor <;> linarith only [this.1, this.2]

theorem wpd_mem_cellImage {x : Vec d} {j : ℤ} (k : Fin d → ℤ) :
    x ∈ (fun x => (fun i => (3 : ℝ) ^ j * (k i : ℝ)) + x) '' cubeSet (originCube d j) ↔
      ∀ i, (3 : ℝ) ^ j * (k i : ℝ) - (3 : ℝ) ^ j / 2 ≤ x i ∧
        x i < (3 : ℝ) ^ j * (k i : ℝ) + (3 : ℝ) ^ j / 2 := by
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    have h := hw i
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add] at h
    show _ ≤ (3 : ℝ) ^ j * (k i : ℝ) + w i ∧ (3 : ℝ) ^ j * (k i : ℝ) + w i < _
    constructor <;> linarith only [h.1, h.2]
  · intro h
    refine ⟨x - fun i => (3 : ℝ) ^ j * (k i : ℝ), ?_, by simp⟩
    intro i
    have := h i
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add, Pi.sub_apply]
    constructor <;> linarith only [this.1, this.2]

theorem wpd_vecNormSq_eq (x : Vec d) : vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, sq]

/-- The open Euclidean ball of radius `ρ`, as a sublevel set. -/
def wpd_V (ρ : ℝ) : Set (Vec d) := {x | ∑ i, x i ^ 2 < ρ ^ 2}

theorem wpd_smul_euclidBall {t : ℝ} (ht : 0 < t) :
    t • Section6.euclidBall (d := d) (1 / 2) = wpd_V (t / 2) := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : vecNormSq y < (1 / 2) ^ 2 := hy
    show ∑ i, (t • y) i ^ 2 < (t / 2) ^ 2
    have : ∑ i, (t • y) i ^ 2 = t ^ 2 * vecNormSq y := by
      rw [← vecNormSq_smul, wpd_vecNormSq_eq]
    rw [this]
    have h2 : t ^ 2 * vecNormSq y < t ^ 2 * (1 / 2) ^ 2 := mul_lt_mul_of_pos_left hy' (by positivity)
    calc t ^ 2 * vecNormSq y < t ^ 2 * (1 / 2) ^ 2 := h2
      _ = (t / 2) ^ 2 := by ring
  · intro hx
    refine ⟨t⁻¹ • x, ?_, by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]⟩
    show vecNormSq (t⁻¹ • x) < (1 / 2) ^ 2
    rw [vecNormSq_smul, wpd_vecNormSq_eq]
    have hx' : ∑ i, x i ^ 2 < (t / 2) ^ 2 := hx
    have : (t⁻¹) ^ 2 * ∑ i, x i ^ 2 < (t⁻¹) ^ 2 * (t / 2) ^ 2 :=
      mul_lt_mul_of_pos_left hx' (by positivity)
    calc (t⁻¹) ^ 2 * ∑ i, x i ^ 2 < (t⁻¹) ^ 2 * (t / 2) ^ 2 := this
      _ = (1 / 2) ^ 2 := by field_simp

theorem wpd_shiftCube_subset_iff [NeZero d] {ρ : ℝ} (z : Vec d) (m : ℤ) :
    (z ∈ wpd_V ρ ∧ wpd_shiftCube z m ⊆ wpd_V ρ) ↔
      ∑ i, (|z i| + (3 : ℝ) ^ m / 2) ^ 2 ≤ ρ ^ 2 := by
  set r : ℝ := (3 : ℝ) ^ m / 2 with hr
  have hr0 : 0 < r := by positivity
  constructor
  · rintro ⟨-, hsub⟩
    set A : Fin d → ℝ := fun i => |z i| + r with hA
    have hpt : ∀ ε : ℝ, 0 < ε → ε < r → ∑ i, (A i - ε) ^ 2 < ρ ^ 2 := by
      intro ε hε hεr
      have hmem : (fun i => z i + (if 0 ≤ z i then 1 else -1) * (r - ε)) ∈ wpd_shiftCube z m := by
        rw [wpd_mem_shiftCube]
        intro i
        have : z i + (if 0 ≤ z i then 1 else -1) * (r - ε) - z i = (if 0 ≤ z i then 1 else -1) * (r - ε) := by ring
        rw [this, abs_mul]
        have h1 : |(if 0 ≤ z i then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
        have hpos : 0 < r - ε := by linarith only [hεr]
        rw [h1, one_mul, abs_of_pos hpos]
        linarith only [hε, hr]
      have := hsub hmem
      have hq : ∀ i, (z i + (if 0 ≤ z i then 1 else -1) * (r - ε)) ^ 2 = (A i - ε) ^ 2 := by
        intro i
        rw [hA]
        dsimp only
        by_cases h0 : 0 ≤ z i
        · simp only [h0, ↓reduceIte]; rw [abs_of_nonneg h0]; ring
        · simp only [h0, ↓reduceIte]; rw [abs_of_neg (not_le.1 h0)]; ring
      have h2 : ∑ i, (z i + (if 0 ≤ z i then 1 else -1) * (r - ε)) ^ 2 = ∑ i, (A i - ε) ^ 2 :=
        Finset.sum_congr rfl fun i _ => hq i
      rw [← h2]
      exact this
    have hcont : Continuous fun ε : ℝ => ∑ i, (A i - ε) ^ 2 := by fun_prop
    have hlim : Filter.Tendsto (fun ε : ℝ => ∑ i, (A i - ε) ^ 2) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i, (A i - 0) ^ 2)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∑ i, (A i - ε) ^ 2 ≤ ρ ^ 2 := by
      filter_upwards [Ioo_mem_nhdsGT hr0] with ε hε
      exact (hpt ε hε.1 hε.2).le
    have := le_of_tendsto hlim hev
    simpa [hA] using this
  · intro h
    have hsub : wpd_shiftCube z m ⊆ wpd_V ρ := by
      intro x hx
      rw [wpd_mem_shiftCube] at hx
      show ∑ i, x i ^ 2 < ρ ^ 2
      refine lt_of_lt_of_le ?_ h
      refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
      have h1 : |x i| < |z i| + r := by
        have := abs_sub_abs_le_abs_sub (x i) (z i)
        linarith only [this, hx i, hr]
      calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
        _ < (|z i| + r) ^ 2 := pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
    refine ⟨?_, hsub⟩
    refine hsub ?_
    rw [wpd_mem_shiftCube]
    intro i
    simp only [sub_self, abs_zero]
    linarith only [hr0, hr]

/-- Rounding to the grid `hℤ`. -/
noncomputable def wpd_psi (h u : ℝ) : ℝ := h * ((⌊u / h + 1 / 2⌋ : ℤ) : ℝ)

/-- The grid cubes (closed-form description of the carrier). -/
def wpd_W0 (d : ℕ) (h r ρ : ℝ) : Set (Vec d) :=
  {x | ∑ i, (h * |((⌊x i / h + 1 / 2⌋ : ℤ) : ℝ)| + r) ^ 2 ≤ ρ ^ 2}

/-- The open digital ball: the grid cubes through the rounding of `|x_i|`. -/
def wpd_W (d : ℕ) (h r ρ : ℝ) : Set (Vec d) :=
  {x | ∑ i, (wpd_psi h |x i| + r) ^ 2 ≤ ρ ^ 2}

theorem wpd_floor_cell {h : ℝ} (hh : 0 < h) (k : ℤ) (u : ℝ) :
    ⌊u / h + 1 / 2⌋ = k ↔ h * k - h / 2 ≤ u ∧ u < h * k + h / 2 := by
  rw [Int.floor_eq_iff]
  have e : h * (u / h + 1 / 2) = u + h / 2 := by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := mul_le_mul_of_nonneg_left h1 hh.le
    have a2 := mul_lt_mul_of_pos_left h2 hh
    rw [e] at a1 a2
    constructor <;> nlinarith only [a1, a2]
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hc
      have := mul_lt_mul_of_pos_left (not_le.1 hc) hh
      rw [e] at this
      linarith only [this, h1]
    · by_contra hc
      have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hh.le
      rw [e, mul_add, mul_one] at this
      linarith only [this, h2]

theorem wpd_interior_eq [NeZero d] (ρ : ℝ) (j : ℤ) :
    wpd_whitneyInterior (wpd_V ρ) j = wpd_W0 d ((3 : ℝ) ^ j) ((3 : ℝ) ^ (j + 3) / 2) ρ := by
  have hh : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  ext x
  simp only [wpd_whitneyInterior, Set.mem_iUnion, exists_prop, wpd_W0, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, hx⟩
    have hs := (wpd_shiftCube_subset_iff (ρ := ρ) (fun i => (3 : ℝ) ^ j * (k i : ℝ)) (j + 3)).1 hk
    rw [wpd_mem_cellImage] at hx
    have hfl : ∀ i, ⌊x i / (3 : ℝ) ^ j + 1 / 2⌋ = k i := fun i =>
      (wpd_floor_cell hh (k i) (x i)).2 ⟨(hx i).1, (hx i).2⟩
    have e : ∑ i, ((3 : ℝ) ^ j * |((⌊x i / (3 : ℝ) ^ j + 1 / 2⌋ : ℤ) : ℝ)| +
        (3 : ℝ) ^ (j + 3) / 2) ^ 2 =
        ∑ i, (|(3 : ℝ) ^ j * (k i : ℝ)| + (3 : ℝ) ^ (j + 3) / 2) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfl i, abs_mul, abs_of_pos hh]
    rw [e]
    exact hs
  · intro hx
    refine ⟨fun i => ⌊x i / (3 : ℝ) ^ j + 1 / 2⌋, ?_, ?_⟩
    · refine (wpd_shiftCube_subset_iff (ρ := ρ) _ (j + 3)).2 ?_
      have e : ∑ i, (|(3 : ℝ) ^ j * ((⌊x i / (3 : ℝ) ^ j + 1 / 2⌋ : ℤ) : ℝ)| +
          (3 : ℝ) ^ (j + 3) / 2) ^ 2 =
          ∑ i, ((3 : ℝ) ^ j * |((⌊x i / (3 : ℝ) ^ j + 1 / 2⌋ : ℤ) : ℝ)| +
            (3 : ℝ) ^ (j + 3) / 2) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_pos hh]
      rw [e]
      exact hx
    · rw [wpd_mem_cellImage]
      intro i
      exact (wpd_floor_cell hh _ (x i)).1 rfl

theorem wpd_psi_nonneg {h : ℝ} (hh : 0 < h) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ wpd_psi h u := by
  unfold wpd_psi
  refine mul_nonneg hh.le ?_
  exact_mod_cast Int.floor_nonneg.2 (by positivity)

theorem wpd_psi_le {h : ℝ} (hh : 0 < h) (u : ℝ) : wpd_psi h u ≤ u + h / 2 := by
  unfold wpd_psi
  have h1 := mul_le_mul_of_nonneg_left (Int.floor_le (u / h + 1 / 2)) hh.le
  have e : h * (u / h + 1 / 2) = u + h / 2 := by field_simp
  linarith only [h1, e]

theorem wpd_lt_psi {h : ℝ} (hh : 0 < h) (u : ℝ) : u - h / 2 < wpd_psi h u := by
  unfold wpd_psi
  have h1 := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (u / h + 1 / 2)) hh
  have e : h * (u / h + 1 / 2) = u + h / 2 := by field_simp
  rw [e, mul_add, mul_one] at h1
  linarith only [h1]

theorem wpd_psi_mono {h : ℝ} (hh : 0 < h) {u v : ℝ} (huv : u ≤ v) : wpd_psi h u ≤ wpd_psi h v := by
  unfold wpd_psi
  refine mul_le_mul_of_nonneg_left ?_ hh.le
  exact_mod_cast Int.floor_mono (by gcongr)

theorem wpd_W_mono {h r ρ : ℝ} (hh : 0 < h) (hr : 0 ≤ r) {x y : Vec d}
    (hx : x ∈ wpd_W d h r ρ) (hxy : ∀ i, |y i| ≤ |x i|) : y ∈ wpd_W d h r ρ := by
  show ∑ i, (wpd_psi h |y i| + r) ^ 2 ≤ ρ ^ 2
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (show ∑ i, (wpd_psi h |x i| + r) ^ 2 ≤ ρ ^ 2 from hx)
  have h0 := wpd_psi_nonneg hh (abs_nonneg (y i))
  exact pow_le_pow_left₀ (by linarith only [h0, hr]) (by linarith only [wpd_psi_mono hh (hxy i)]) 2

theorem wpd_W_subset_V [NeZero d] {h r ρ : ℝ} (hh : 0 < h) (hr : h / 2 < r) :
    wpd_W d h r ρ ⊆ wpd_V ρ := by
  intro x hx
  refine lt_of_lt_of_le ?_ (show ∑ i, (wpd_psi h |x i| + r) ^ 2 ≤ ρ ^ 2 from hx)
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
  have h1 := wpd_lt_psi hh |x i|
  calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
    _ < (wpd_psi h |x i| + r) ^ 2 :=
      pow_lt_pow_left₀ (by linarith only [h1, hr]) (abs_nonneg _) (by norm_num)

theorem wpd_V_subset_W [NeZero d] {h r ρ ρc : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hρ : ρc + (h / 2 + r) * Real.sqrt d ≤ ρ) (hρc : 0 ≤ ρc) : wpd_V ρc ⊆ wpd_W d h r ρ := by
  intro y hy
  have hy' : ∑ i, y i ^ 2 < ρc ^ 2 := hy
  set c : ℝ := h / 2 + r with hc
  have hc0 : 0 < c := by positivity
  set s : ℝ := Real.sqrt d with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hS1 : (∑ i, |y i|) ^ 2 ≤ d * ∑ i, y i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |y i|)
    simpa [sq_abs] using this
  have hS1' : ∑ i, |y i| < ρc * s := by
    have hlt : (∑ i, |y i|) ^ 2 < (ρc * s) ^ 2 := by
      calc (∑ i, |y i|) ^ 2 ≤ d * ∑ i, y i ^ 2 := hS1
        _ < d * ρc ^ 2 :=
          mul_lt_mul_of_pos_left hy' (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
        _ = (ρc * s) ^ 2 := by rw [mul_pow, hs2]; ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt
  have hexp : ∑ i, (|y i| + c) ^ 2 = ∑ i, y i ^ 2 + 2 * c * ∑ i, |y i| + d * c ^ 2 := by
    have : ∀ i, (|y i| + c) ^ 2 = y i ^ 2 + 2 * c * |y i| + c ^ 2 := fun i => by
      rw [← sq_abs (y i)]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hfin : ∑ i, (|y i| + c) ^ 2 ≤ ρ ^ 2 := by
    rw [hexp]
    have h1 : 2 * c * ∑ i, |y i| ≤ 2 * c * (ρc * s) :=
      mul_le_mul_of_nonneg_left hS1'.le (by positivity)
    have h2 : ρc + c * s ≤ ρ := hρ
    have h3 : (ρc + c * s) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    have h4 : (ρc + c * s) ^ 2 = ρc ^ 2 + 2 * c * (ρc * s) + d * c ^ 2 := by
      rw [← hs2]; ring
    nlinarith only [hy', h1, h3, h4]
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) hfin
  have h0 := wpd_psi_nonneg hh (abs_nonneg (y i))
  exact pow_le_pow_left₀ (by linarith only [h0, hr]) (by linarith only [wpd_psi_le hh |y i|, hc]) 2

theorem wpd_abs_floor_le (u : ℝ) :
    |((⌊u + 1 / 2⌋ : ℤ) : ℝ)| ≤ ((⌊|u| + 1 / 2⌋ : ℤ) : ℝ) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu, abs_of_nonneg]
    exact_mod_cast Int.floor_nonneg.2 (by linarith only [hu])
  · rw [abs_of_neg hu]
    have h1 : ⌊u + 1 / 2⌋ ≤ 0 := by
      have : ⌊u + 1 / 2⌋ < 1 := by
        rw [Int.floor_lt]; push_cast; linarith only [hu]
      omega
    have h2 := Int.le_floor_add_floor (u + 1 / 2) (-u + 1 / 2)
    have e : u + 1 / 2 + (-u + 1 / 2) = 1 := by ring
    rw [e, Int.floor_one] at h2
    have h3 : -⌊u + 1 / 2⌋ ≤ ⌊-u + 1 / 2⌋ := by omega
    have h4 : |((⌊u + 1 / 2⌋ : ℤ) : ℝ)| = ((-⌊u + 1 / 2⌋ : ℤ) : ℝ) := by
      rw [abs_of_nonpos (by exact_mod_cast h1)]; push_cast; ring
    rw [h4]
    exact_mod_cast h3

theorem wpd_abs_floor_eq (u : ℝ) (hu : u + 1 / 2 ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ((⌊|u| + 1 / 2⌋ : ℤ) : ℝ) = |((⌊u + 1 / 2⌋ : ℤ) : ℝ)| := by
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0, abs_of_nonneg]
    exact_mod_cast Int.floor_nonneg.2 (by linarith only [h0])
  · rw [abs_of_neg h0]
    have h1 : ⌊u + 1 / 2⌋ ≤ 0 := by
      have : ⌊u + 1 / 2⌋ < 1 := by
        rw [Int.floor_lt]; push_cast; linarith only [h0]
      omega
    have hc : ⌈u + 1 / 2⌉ = ⌊u + 1 / 2⌋ + 1 := (Int.ceil_eq_floor_add_one_iff_notMem _).2 hu
    have e : -u + 1 / 2 = -(u + 1 / 2) + 1 := by ring
    have h2 : ⌊-u + 1 / 2⌋ = -⌊u + 1 / 2⌋ := by
      rw [e, Int.floor_add_one, Int.floor_neg, hc]; ring
    rw [h2, abs_of_nonpos (by exact_mod_cast h1)]
    push_cast
    ring

theorem wpd_W_subset_W0 {h r ρ : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    wpd_W d h r ρ ⊆ wpd_W0 d h r ρ := by
  intro x hx
  show ∑ i, (h * |((⌊x i / h + 1 / 2⌋ : ℤ) : ℝ)| + r) ^ 2 ≤ ρ ^ 2
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (show ∑ i, (wpd_psi h |x i| + r) ^ 2 ≤ ρ ^ 2 from hx)
  have h1 := wpd_abs_floor_le (x i / h)
  have e : |x i / h| = |x i| / h := by rw [abs_div, abs_of_pos hh]
  rw [e] at h1
  have h2 : h * |((⌊x i / h + 1 / 2⌋ : ℤ) : ℝ)| ≤ wpd_psi h |x i| :=
    mul_le_mul_of_nonneg_left h1 hh.le
  exact pow_le_pow_left₀ (by positivity) (by linarith only [h2]) 2

/-- The null set of the faces: points with some coordinate on a half-integer grid plane. -/
def wpd_faces (d : ℕ) (h : ℝ) : Set (Vec d) := {x | ∃ i, ∃ n : ℤ, x i / h + 1 / 2 = n}

theorem wpd_volume_faces {h : ℝ} (hh : 0 < h) : volume (wpd_faces d h) = 0 := by
  have hsub : wpd_faces d h ⊆ ⋃ i : Fin d, ⋃ n : ℤ, {x : Vec d | x i = h * ((n : ℝ) - 1 / 2)} := by
    rintro x ⟨i, n, hn⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨i, n, ?_⟩
    have : x i / h = n - 1 / 2 := by linarith only [hn]
    rw [← this]
    field_simp
  refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun n => ?_)
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i _

theorem wpd_W0_ae_le {h r ρ : ℝ} (hh : 0 < h) :
    ∀ᵐ x : Vec d, x ∈ wpd_W0 d h r ρ → x ∈ wpd_W d h r ρ := by
  have hn : ∀ᵐ x : Vec d, x ∉ wpd_faces d h := measure_eq_zero_iff_ae_notMem.1 (wpd_volume_faces hh)
  filter_upwards [hn] with x hx hx0
  show ∑ i, (wpd_psi h |x i| + r) ^ 2 ≤ ρ ^ 2
  have hx0' : ∑ i, (h * |((⌊x i / h + 1 / 2⌋ : ℤ) : ℝ)| + r) ^ 2 ≤ ρ ^ 2 := hx0
  have : ∀ i, wpd_psi h |x i| = h * |((⌊x i / h + 1 / 2⌋ : ℤ) : ℝ)| := by
    intro i
    have hnot : x i / h + 1 / 2 ∉ Set.range (Int.cast : ℤ → ℝ) := by
      rintro ⟨n, hn'⟩
      exact hx ⟨i, n, hn'.symm⟩
    have e : |x i| / h = |x i / h| := by rw [abs_div, abs_of_pos hh]
    unfold wpd_psi
    rw [e, wpd_abs_floor_eq _ hnot]
  simpa only [this] using hx0'

theorem wpd_W_ae_eq {h r ρ : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    wpd_W0 d h r ρ =ᵐ[volume] wpd_W d h r ρ :=
  Filter.EventuallyLE.antisymm (wpd_W0_ae_le hh) (wpd_W_subset_W0 hh hr).eventuallyLE

theorem wpd_W_isOpen {h r ρ : ℝ} (hh : 0 < h) (hr : 0 ≤ r) : IsOpen (wpd_W d h r ρ) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hev : ∀ᶠ y in nhds x, ∀ i, ⌊|y i| / h + 1 / 2⌋ ≤ ⌊|x i| / h + 1 / 2⌋ := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous fun y : Vec d => |y i| / h + 1 / 2 := by fun_prop
    have := (hc.continuousAt (x := x)).eventually_lt continuousAt_const
      (Int.lt_floor_add_one (|x i| / h + 1 / 2))
    filter_upwards [this] with y hy
    refine Int.lt_add_one_iff.1 (Int.floor_lt.2 ?_)
    exact_mod_cast hy
  filter_upwards [hev] with y hy
  show ∑ i, (wpd_psi h |y i| + r) ^ 2 ≤ ρ ^ 2
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (show ∑ i, (wpd_psi h |x i| + r) ^ 2 ≤ ρ ^ 2 from hx)
  have h0 := wpd_psi_nonneg hh (abs_nonneg (y i))
  have h1 : wpd_psi h |y i| ≤ wpd_psi h |x i| := by
    unfold wpd_psi
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy i) hh.le
  exact pow_le_pow_left₀ (by linarith only [h0, hr]) (by linarith only [h1]) 2

/-- One coordinate of the shift: move `x` by `ℓ` towards the origin when `|x| ≥ ℓ`. -/
noncomputable def wpd_step (ℓ x : ℝ) : ℝ := if ℓ ≤ x then x - ℓ else if x ≤ -ℓ then x + ℓ else x

/-- The shift by `ℓ` towards the origin of the large coordinates. -/
noncomputable def wpd_shift (ℓ : ℝ) (x : Vec d) : Vec d := fun i => wpd_step ℓ (x i)

theorem wpd_step_seg_abs {ℓ : ℝ} (hℓ : 0 < ℓ) (x s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |x + s * (wpd_step ℓ x - x)| ≤ |x| := by
  unfold wpd_step
  by_cases h1 : ℓ ≤ x
  · simp only [h1, ↓reduceIte]
    have hx0 : |x| = x := abs_of_nonneg (by linarith only [h1, hℓ])
    rw [hx0, abs_le]
    have : s * ℓ ≤ ℓ := by nlinarith only [hs1, hℓ]
    have : 0 ≤ s * ℓ := by positivity
    constructor <;> nlinarith only [h1, hℓ, this, hs0, hs1]
  · by_cases h2 : x ≤ -ℓ
    · simp only [h1, h2, ↓reduceIte]
      have hx0 : |x| = -x := abs_of_nonpos (by linarith only [h2, hℓ])
      rw [hx0, abs_le]
      have : s * ℓ ≤ ℓ := by nlinarith only [hs1, hℓ]
      have : 0 ≤ s * ℓ := by positivity
      constructor <;> nlinarith only [h2, hℓ, this, hs0, hs1]
    · simp only [h1, h2, ↓reduceIte]
      have : x + s * (x - x) = x := by ring
      rw [this]

theorem wpd_shift_segment {h r ρ ℓ : ℝ} (hh : 0 < h) (hr : 0 ≤ r) (hℓ : 0 < ℓ) {x : Vec d}
    (hx : x ∈ wpd_W d h r ρ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x + s • (wpd_shift ℓ x - x) ∈ wpd_W d h r ρ := by
  refine wpd_W_mono hh hr hx fun i => ?_
  have := wpd_step_seg_abs hℓ (x i) s hs0 hs1
  simpa [wpd_shift] using this

theorem wpd_step_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    wpd_step ℓ x ^ 2 ≤ x ^ 2 - ℓ * (if ℓ ≤ |x| then |x| else 0) := by
  unfold wpd_step
  by_cases h1 : ℓ ≤ x
  · have h1' : ℓ ≤ |x| := by rw [abs_of_nonneg (by linarith only [h1, hℓ])]; exact h1
    simp only [h1, h1', ↓reduceIte]
    rw [abs_of_nonneg (by linarith only [h1, hℓ])]
    nlinarith only [h1, hℓ]
  · by_cases h2 : x ≤ -ℓ
    · have h2' : ℓ ≤ |x| := by rw [abs_of_nonpos (by linarith only [h2, hℓ])]; linarith only [h2]
      simp only [h1, h2, h2', ↓reduceIte]
      rw [abs_of_nonpos (by linarith only [h2, hℓ])]
      nlinarith only [h2, hℓ]
    · have h2' : ¬ ℓ ≤ |x| := by
        intro hc
        rcases le_abs'.1 hc with h | h
        · exact h2 h
        · exact h1 h
      simp only [h1, h2, h2', ↓reduceIte]
      ring_nf
      exact le_rfl

theorem wpd_shift_core [NeZero d] {c ρ : ℝ} (hc : 0 < c) (hρ : 17 * d * c ≤ ρ) {x : Vec d}
    (hx : x ∈ wpd_V ρ) :
    wpd_shift (8 * Real.sqrt d * c) x ∈ wpd_V (ρ - c * Real.sqrt d) := by
  set s : ℝ := Real.sqrt d with hs
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hsd : s ≤ d := by nlinarith only [hs2, hs0, hd1]
  have hs1 : 1 ≤ s := by nlinarith only [hs2, hs0, hd1]
  set ℓ : ℝ := 8 * s * c with hℓdef
  have hℓ : 0 < ℓ := by positivity
  set ρc : ℝ := ρ - c * s with hρc
  have hρ0 : 0 < ρ := by nlinarith only [hρ, hc, hd1]
  have hρc16 : 16 * d * c ≤ ρc := by
    have : c * s ≤ d * c := by nlinarith only [hsd, hc]
    linarith only [hρ, this, hρc]
  have hρc0 : 0 ≤ ρc := by nlinarith only [hρc16, hc, hd1]
  have hx' : ∑ i, x i ^ 2 < ρ ^ 2 := hx
  show ∑ i, (wpd_shift ℓ x i) ^ 2 < ρc ^ 2
  set u : Fin d → ℝ := fun i => if ℓ ≤ |x i| then |x i| else 0 with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => by
    simp only [hu]; split_ifs <;> positivity
  have hstep : ∑ i, (wpd_shift ℓ x i) ^ 2 ≤ ∑ i, x i ^ 2 - ℓ * ∑ i, u i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => wpd_step_sq_le hℓ (x i)
  have hU0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu0 i
  by_cases hA : ∑ i, x i ^ 2 < ρc ^ 2
  · have : 0 ≤ ℓ * ∑ i, u i := by positivity
    linarith only [hstep, hA, this]
  · have hB : ρc ^ 2 ≤ ∑ i, x i ^ 2 := not_lt.1 hA
    have hu2 : ∑ i, x i ^ 2 - d * ℓ ^ 2 ≤ ∑ i, u i ^ 2 := by
      have : ∑ i, x i ^ 2 - ∑ _i : Fin d, ℓ ^ 2 ≤ ∑ i, u i ^ 2 := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : ℓ ≤ |x i|
        · have : u i = |x i| := by simp only [hu, h, ↓reduceIte]
          rw [this, sq_abs]; nlinarith only [sq_nonneg ℓ]
        · have : u i = 0 := by simp only [hu, h, ↓reduceIte]
          rw [this]
          have h' : |x i| < ℓ := not_le.1 h
          have : x i ^ 2 < ℓ ^ 2 := by
            rw [← sq_abs]; exact pow_lt_pow_left₀ h' (abs_nonneg _) (by norm_num)
          nlinarith only [this]
      simpa using this
    have hU2 : ∑ i, u i ^ 2 ≤ (∑ i, u i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hu0 i
    have hdl : (d : ℝ) * ℓ ^ 2 = 64 * d ^ 2 * c ^ 2 := by
      rw [hℓdef, mul_pow, mul_pow, hs2]; ring
    have hq : ρc ^ 2 / 4 ≤ (∑ i, u i) ^ 2 := by
      have h1 : 256 * d ^ 2 * c ^ 2 ≤ ρc ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hρc16 2
        nlinarith only [this]
      nlinarith only [hu2, hU2, hB, hdl, h1]
    have hU : ρc / 2 ≤ ∑ i, u i := by
      have : (ρc / 2) ^ 2 ≤ (∑ i, u i) ^ 2 := by nlinarith only [hq]
      exact le_of_sq_le_sq this hU0 |>.trans' le_rfl
    have hρhalf : ρ / 2 ≤ ρc := by
      have : c * s ≤ d * c := by nlinarith only [hsd, hc]
      have h0 : 0 ≤ (d : ℝ) * c := by positivity
      linarith only [hρ, this, hρc, h0]
    have hk : ρ ^ 2 - ρc ^ 2 ≤ ℓ * (ρc / 2) := by
      have e : ρ ^ 2 - ρc ^ 2 = c * s * (ρ + ρc) := by rw [hρc]; ring
      rw [e, hℓdef]
      have : c * s * (ρ + ρc) ≤ c * s * (4 * ρc) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith only [hρhalf, hρ0]
      nlinarith only [this]
    have hmul : ℓ * (ρc / 2) ≤ ℓ * ∑ i, u i := mul_le_mul_of_nonneg_left hU hℓ.le
    linarith only [hstep, hx', hk, hmul]

end SuperdiffusionCLT.Section7
