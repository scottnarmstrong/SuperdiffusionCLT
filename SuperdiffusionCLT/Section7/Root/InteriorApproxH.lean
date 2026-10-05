/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorApproxG
public import SuperdiffusionCLT.Section7.Lipschitz.Datum
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonC
public import SuperdiffusionCLT.Section7.Root.HolderRootB
public import SuperdiffusionCLT.Section7.Prereq.L2InteriorC
public import SuperdiffusionCLT.Section6.Lemma.Assembly
public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlargeB
public import SuperdiffusionCLT.Section7.Analytic.Change.SkewShift
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Interior approximation: tiling by cells and the De Giorgi estimate on a cell

* `ip_tiling`: every point lies in a cell `y + 3^l j + □_l`.
* `ip_ae_cover`: an almost-everywhere statement on each cell of a countable cover holds almost
  everywhere on the covered set.
* `ip_cell_dg`: the `L^∞`-`L²` De Giorgi estimate on the ball of radius `3^{m}/4` of the cube
  `y + □_m`, in normalized form, for `u - c` with `c` a constant.
* the geometry of the cells and of the rounded cube inside `y + □_m` (`ip_cube_sub`, `ip_marg`, ...).
* `ip_isElliptic`, `ip_fmod`, `ip_centered_of_recentered`, `ip_center_mem_grid`: ellipticity of the centred field,
  the measurable representative of the right-hand side and the transfer of the equation to the centred
  field, the lattice of the cell centres inside the grid.
* `ip_flux_real`: the cell bound of the mollified flux in real form.
* `ia_exists_uhom`: the homogenized solution with the mollified solution as boundary datum.
* `ip_flux_sup`: the supremum of the mollified flux on the rounded cube (from the cell bounds and the
  Lipschitz estimate); `ip_moll_bound`: the mollification error `|u - η_h ∗ u|` (De Giorgi on the cells).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Every point lies in one cell `y + 3^l j + □_l`. -/
theorem ip_tiling (y x : Vec d) (l : ℕ) : ∃ j : Fin d → ℤ, x ∈ l2b_cell (y + l2b_pt l j) l := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  refine ⟨fun i => ⌊(x i - y i) / (3 : ℝ) ^ l + 1 / 2⌋, ?_⟩
  rw [l2b_mem_cell]
  intro i
  simp only [l2b_pt, Pi.add_apply]
  set t : ℝ := (x i - y i) / (3 : ℝ) ^ l with ht
  have hx : x i - y i = (3 : ℝ) ^ l * t := by rw [ht]; field_simp
  have h1 := Int.floor_le (t + 1 / 2)
  have h2 := Int.lt_floor_add_one (t + 1 / 2)
  have e : x i - (y i + (3 : ℝ) ^ l * ((⌊t + 1 / 2⌋ : ℤ) : ℝ)) =
      (3 : ℝ) ^ l * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ)) := by linarith only [hx]
  rw [e]
  constructor
  · nlinarith only [h3, h1]
  · nlinarith only [h3, h2]

/-- An almost-everywhere statement on each cell of a countable cover. -/
theorem ip_ae_cover {ι : Type*} [Countable ι] {E : Set (Vec d)} {cell : ι → Set (Vec d)}
    (hE : E ⊆ ⋃ i, cell i) {Φ : Vec d → Prop}
    (h : ∀ i, ∀ᵐ x ∂(volume.restrict (cell i)), Φ x) : ∀ᵐ x ∂(volume.restrict E), Φ x := by
  have h1 : ∀ᵐ x ∂(volume.restrict (⋃ i, cell i)), Φ x := (ae_restrict_iUnion_iff _ _).2 h
  exact ae_restrict_of_ae_restrict_of_subset hE h1

/-- The concentric half cube of the translated cube is the sup-ball of a quarter of its side. -/
theorem ip_halfCube_eq (z : Vec d) (m : ℕ) :
    halfCube (fun i => z i - (3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m) = Metric.ball z ((3 : ℝ) ^ m / 4) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  ext x
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff (by positivity)]
  unfold halfCube axisCube
  rw [Set.mem_pi]
  refine forall_congr' fun i => ?_
  simp only [Set.mem_univ, true_implies, Set.mem_Ioo, Pi.add_apply, Pi.sub_apply, Real.norm_eq_abs,
    abs_lt]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith only [a, b, h3]

/-- The normalized `L²` factor of the De Giorgi estimate on an axis cube. -/
theorem ip_dg_norm_eq {z : Vec d} {L : ℝ} (hL : 0 < L) (G : Vec d → ℝ)
    (hG : AEStronglyMeasurable G (volume.restrict (axisCube z L))) :
    ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * eLpNorm G 2 (volume.restrict (axisCube z L)) =
      lpBar (axisCube z L) 2 G := by
  have hvol : volume (axisCube z L) = ENNReal.ofReal (L ^ d) := by
    rw [axisCube, Real.volume_pi_Ioo]
    simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow hL.le]
  rw [ia_lpBar_eq_mul (by norm_num) (by norm_num) (by rw [hvol]; exact ENNReal.ofReal_ne_top) G hG,
    ← mul_assoc, hvol]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have key : ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * (ENNReal.ofReal (L ^ d)) ^ (1 / (2 : ℝ)) = 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    have : L ^ (-(d : ℝ) / 2) * (L ^ d) ^ (1 / (2 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
      have : -(d : ℝ) / 2 + (d : ℝ) * (1 / 2) = 0 := by ring
      rw [this, Real.rpow_zero]
    rw [this, ENNReal.ofReal_one]
  rw [key, one_mul]

/-- **De Giorgi on the ball of a quarter of the side of the cube `z + □_m`**, for `u - c`. -/
theorem ip_cell_dg (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) (m : ℕ),
      IsEllipticFieldOn lam Lam (shiftCube z (m : ℤ)) a →
      ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube z (m : ℤ))) (c : ℝ),
        IsWeakSolutionOn a (shiftCube z (m : ℤ)) u f (fun _ => 0) →
        eLpNorm (fun x => u.toFun x - c) ⊤ (volume.restrict (Metric.ball z ((3 : ℝ) ^ m / 4))) ≤
          ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
            (lpBar (shiftCube z (m : ℤ)) 2 (fun x => u.toFun x - c) +
              ENNReal.ofReal ((3 : ℝ) ^ (2 * m) / lam) *
                eLpNorm f ⊤ (volume.restrict (shiftCube z (m : ℤ)))) := by
  obtain ⟨C, hC, H⟩ := ip_dg_abs hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a z m hEll f u c hu
  have hshift : shiftCube z (m : ℤ) = axisCube (fun i => z i - (3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m) := by
    simpa using rc_shiftCube_eq_axisCube z (m : ℤ)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  generalize hz0 : (fun i => z i - (3 : ℝ) ^ m / 2) = z0 at hshift
  rw [← ip_halfCube_eq z m, hz0]
  revert hEll u hu
  rw [hshift]
  intro hEll u hu
  have hum : AEStronglyMeasurable (fun x => u.toFun x - c) (volume.restrict (axisCube z0 ((3 : ℝ) ^ m))) :=
    (u.memL2.aestronglyMeasurable).sub aestronglyMeasurable_const
  have := H z0 h3 hEll f u c hu
  rw [ip_dg_norm_eq h3 _ hum] at this
  refine this.trans (le_of_eq ?_)
  rw [pow_mul']


theorem ip_pow_gap {l m : ℕ} (h : l + 5 ≤ m) : 243 * (3 : ℝ) ^ l ≤ 3 ^ m := by
  have : (3 : ℝ) ^ m = 3 ^ l * 3 ^ (m - l) := by rw [← pow_add]; congr 1; omega
  rw [this]
  have h5 : (243 : ℝ) ≤ 3 ^ (m - l) := by
    calc (243 : ℝ) = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ (m - l) := pow_le_pow_right₀ (by norm_num) (by omega)
  have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 3 ^ l)
  linarith only [this]

/-- The translated cube as a sup-ball. -/
theorem ip_shiftCube_ball (z : Vec d) (m : ℕ) :
    shiftCube z (m : ℤ) = Metric.ball z ((3 : ℝ) ^ m / 2) := by
  rw [lip_datum_shiftCube_eq]
  simp

/-- Points of a cell are within half the cell side of its centre. -/
theorem ip_cell_dist {z x : Vec d} {l : ℕ} (hx : x ∈ l2b_cell z l) : dist x z ≤ (3 : ℝ) ^ l / 2 := by
  rw [l2b_mem_cell] at hx
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq, abs_le]
  have := hx i
  constructor <;> linarith only [this.1, this.2]

/-- The cells meeting the rounded cube have centres near `y`. -/
theorem ip_cell_center {y x : Vec d} {l m : ℕ} {j : Fin d → ℤ} (hx : dist x y < (3 : ℝ) ^ m / 4)
    (hc : x ∈ l2b_cell (y + l2b_pt l j) l) : dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l := by
  have h1 := ip_cell_dist hc
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  calc dist (y + l2b_pt l j) y ≤ dist (y + l2b_pt l j) x + dist x y := dist_triangle _ _ _
    _ ≤ (3 : ℝ) ^ l / 2 + (3 : ℝ) ^ m / 4 := by
        rw [dist_comm]; linarith only [h1, hx.le]
    _ ≤ _ := by linarith only [h3]

theorem ip_ball_sub {c c' : Vec d} {r r' : ℝ} (h : dist c c' + r ≤ r') :
    Metric.ball c r ⊆ Metric.ball c' r' := Metric.ball_subset_ball' (by linarith only [h])

/-- A cube `z + □_{l'}` around a relevant cell centre lies in `y + □_m`, for `l' ≤ l + 3`. -/
theorem ip_cube_sub {y z : Vec d} {l l' m : ℕ} (hml : l + 5 ≤ m) (hl' : l' ≤ l + 3)
    (hz : dist z y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l) :
    Metric.ball z ((3 : ℝ) ^ l' / 2) ⊆ Metric.ball y ((3 : ℝ) ^ m / 2) := by
  refine ip_ball_sub ?_
  have h1 := ip_pow_gap hml
  have h2 : (3 : ℝ) ^ l' ≤ 27 * 3 ^ l := by
    calc (3 : ℝ) ^ l' ≤ 3 ^ (l + 3) := pow_le_pow_right₀ (by norm_num) hl'
      _ = 27 * 3 ^ l := by rw [pow_add]; norm_num; ring
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  linarith only [hz, h1, h2, h3]

/-- The cube `z + □_{m-1}` around a relevant cell centre lies in `y + □_m`. -/
theorem ip_cube_sub_pred {y z : Vec d} {l m : ℕ} (hml : l + 5 ≤ m)
    (hz : dist z y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l) :
    Metric.ball z ((3 : ℝ) ^ (m - 1) / 2) ⊆ Metric.ball y ((3 : ℝ) ^ m / 2) := by
  refine ip_ball_sub ?_
  have h1 := ip_pow_gap hml
  have h2 : (3 : ℝ) ^ m = 3 * 3 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  linarith only [hz, h1, h2, h3]

/-- The sup-ball of radius `3^l` around a point of the cell lies in the De Giorgi ball. -/
theorem ip_closedBall_sub {z x : Vec d} {l : ℕ} (hx : x ∈ l2b_cell z l) :
    Metric.closedBall x ((3 : ℝ) ^ l) ⊆ Metric.ball z ((3 : ℝ) ^ (l + 3) / 4) := by
  intro w hw
  rw [Metric.mem_closedBall] at hw
  rw [Metric.mem_ball]
  have h1 := ip_cell_dist hx
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  have : (3 : ℝ) ^ (l + 3) = 27 * 3 ^ l := by rw [pow_add]; norm_num; ring
  calc dist w z ≤ dist w x + dist x z := dist_triangle _ _ _
    _ < _ := by rw [this]; linarith only [hw, h1, h3]

/-- Margin of the cthickening of the rounded cube. -/
theorem ip_marg [NeZero d] {y : Vec d} {l m : ℕ} (hml : l + 5 ≤ m) {V : Set (Vec d)}
    (hV : V ⊆ Metric.ball y ((3 : ℝ) ^ m / 4)) :
    ∀ x ∈ Metric.cthickening ((3 : ℝ) ^ l) V,
      x ∈ shiftCube y (m : ℤ) ∧ 2 * ((3 : ℝ) ^ m / 16) < Metric.infDist x (shiftCube y (m : ℤ))ᶜ := by
  intro x hx
  have h1 := ip_pow_gap hml
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  have hxb : dist x y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l := by
    have h4 := Metric.cthickening_subset_of_subset ((3 : ℝ) ^ l) hV
    rw [cthickening_ball h3.le (by positivity)] at h4
    have := h4 hx
    rw [Metric.mem_closedBall] at this
    linarith only [this]
  have hQ : Metric.ball y ((3 : ℝ) ^ m / 2) = shiftCube y (m : ℤ) := (ip_shiftCube_ball y m).symm
  refine ⟨?_, ?_⟩
  · rw [← hQ, Metric.mem_ball]
    linarith only [hxb, h1, h3]
  · rw [← hQ]
    have hne : (Metric.ball y ((3 : ℝ) ^ m / 2))ᶜ.Nonempty := by
      refine ⟨y + (fun _ => (3 : ℝ) ^ m), ?_⟩
      rw [Set.mem_compl_iff, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      intro hlt
      have i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
      have h5 := (pi_norm_lt_iff (by positivity)).1 hlt i0
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at h5
      have : (0 : ℝ) < 3 ^ m := by positivity
      linarith only [h5, this]
    refine lt_of_lt_of_le (show 2 * ((3 : ℝ) ^ m / 16) < (3 : ℝ) ^ m / 4 - 3 ^ l by
      linarith only [h1, h3]) ((Metric.le_infDist hne).2 fun w hw => ?_)
    rw [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hw
    have := dist_triangle w x y
    rw [dist_comm x w]
    linarith only [this, hw, hxb]


/-- An `H¹(V)` function with prescribed values on `V`. -/
noncomputable def ip_H1_congr {V : Set (Vec d)} (hV : MeasurableSet V) (g : H1Function V)
    (f : Vec d → ℝ) (h : ∀ x ∈ V, f x = g.toFun x) : H1Function V where
  toFun := f
  grad := g.grad
  memL2 := g.memL2.ae_eq ((ae_restrict_iff' hV).2 (Filter.Eventually.of_forall fun x hx => (h x hx).symm))
  gradMemL2 := g.gradMemL2
  hasWeakGradient := fun i => ia_weakDeriv_congr_on hV (g.hasWeakGradient i) (fun x hx => (h x hx).symm)

@[simp] theorem ip_H1_congr_toFun {V : Set (Vec d)} (hV : MeasurableSet V) (g : H1Function V)
    (f : Vec d → ℝ) (h : ∀ x ∈ V, f x = g.toFun x) : (ip_H1_congr hV g f h).toFun = f := rfl

/-- **Existence of the homogenized solution** with the mollified solution as boundary datum. -/
theorem ia_exists_uhom [NeZero d] {Q V : Set (Vec d)} (hQ : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : IsOpen V) (hVQ : V ⊆ Q) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {rc : ℝ} (hrc : 0 < rc)
    (hmarg : ∀ x ∈ Metric.cthickening h V, x ∈ Q ∧ 2 * rc < Metric.infDist x Qᶜ)
    (u : H1Function Q) {f : Vec d → ℝ} (hfm : Measurable f) {Fs : ℝ} (hfb : ∀ x ∈ V, |f x| ≤ Fs)
    {s : ℝ} (hs : 0 < s) :
    ∃ uhom : H1Function V, IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V uhom f (fun _ => 0) ∧
      MemH10 V (fun x => uhom.toFun x - l2a_moll d h η u.toFun x) := by
  have hVb : Bornology.IsBounded V := hQb.subset hVQ
  obtain ⟨ut, hut⟩ := ia_extension hQ hQb u hrc
  have hagree : ∀ x ∈ V, ∀ y, dist y x ≤ h → ut.toFun y = u.toFun y := by
    intro x hx y hy
    have hyT : y ∈ Metric.cthickening h V := Metric.mem_cthickening_of_dist_le y x h V hx hy
    exact (hut y (hmarg y hyT).1 (hmarg y hyT).2).1
  have hmoll : ∀ x ∈ V, l2a_moll d h η u.toFun x = l2a_moll d h η ut.toFun x := fun x hx =>
    l2a_moll_congr hh hηs fun y hy => (hagree x hx y hy).symm
  set g0 := l2a_mollH1 hV hVb hh hη hηs ut with hg0
  set g := ip_H1_congr hV.measurableSet g0 (l2a_moll d h η u.toFun) (fun x hx => hmoll x hx) with hg
  have hbd : IsBoundedDomain V := by
    obtain ⟨R, hR⟩ := hVb.subset_closedBall 0
    refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx i => ?_⟩
    have h1 := hR hx
    rw [mem_closedBall_zero_iff] at h1
    have h2 := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (h1.trans (le_max_left _ _))
  have hfL2 : MemScalarL2 V f := by
    have : IsFiniteMeasure (volumeMeasureOn V) := ⟨by
      simp only [volumeMeasureOn, Measure.restrict_apply_univ]
      exact hVb.measure_lt_top⟩
    refine MemLp.of_bound (C := |Fs|) hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    exact (hfb x hx).trans (le_abs_self _)
  have hEll : IsEllipticFieldOn s s V (fun _ => s • (1 : Mat d)) :=
    isEllipticFieldOn_constantCoeffField hV.measurableSet (isEllipticMatrix_scalarMatrix hs)
  obtain ⟨uh, hsol, hmem⟩ := w0_dirichlet_exists hV hbd hEll hfL2 g
  exact ⟨uh, hsol, hmem⟩


/-- The oscillation over the cube `z + □_{m-1}` against the oscillation over `y + □_m`. -/
theorem ip_osc_pred {y z : Vec d} {l m : ℕ} (hml : l + 5 ≤ m)
    (hz : dist z y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l) {v : Vec d → ℝ}
    (hv : MemLp v 2 (volume.restrict (h1_cube y m))) :
    h1_l2 (h1_cube z (m - 1)) v ≤ Real.sqrt ((3 : ℝ) ^ d) * h1_l2 (h1_cube y m) v := by
  have hsub : h1_cube z (m - 1) ⊆ h1_cube y m := ip_cube_sub_pred hml hz
  have h := h1_l2_le hsub hv (h1_vol_cube_ne_top y m) (h1_vol_cube_pos z (m - 1))
  rw [h1_volT_cube, h1_volT_cube] at h
  have e : ((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ (m - 1)) ^ d = (3 : ℝ) ^ d := by
    have : (3 : ℝ) ^ m = 3 * 3 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, mul_pow, mul_div_assoc, div_self (by positivity), mul_one]
  rwa [e] at h

theorem ip_flux_sup [NeZero d] {y : Vec d} {l m : ℕ} (hml : l + 5 ≤ m)
    {u : H1Function (shiftCube y (m : ℤ))} {nu σ' F Kd a1 a2 Clip : ℝ} (hnu : 0 < nu)
    (hσ' : 0 < σ') (hKd : 0 ≤ Kd) (ha1 : 0 ≤ a1)
    (G : Vec d → Vec d)
    (HFlux : ∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
      ∀ x ∈ l2b_cell (y + l2b_pt l j) l,
        ‖G x‖ ≤ Kd * (a1 * lipGradL2 (shiftCube (y + l2b_pt l j) ((l + 1 : ℕ) : ℤ)) u.grad + a2 * F))
    (HL : ∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
      Real.sqrt nu / Real.sqrt σ' * lipGradL2 (shiftCube (y + l2b_pt l j) ((l + 1 : ℕ) : ℤ)) u.grad ≤
        Clip * (((3 : ℝ) ^ (m - 1))⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) (m - 1)) u.toFun) +
          Clip * (σ'⁻¹ * (3 : ℝ) ^ (m - 1) * F))
    (hClip : 0 ≤ Clip) :
    ∀ x : Vec d, dist x y < (3 : ℝ) ^ m / 4 →
      ‖G x‖ ≤ Kd * (a1 * (Real.sqrt σ' / Real.sqrt nu *
        (Clip * (((3 : ℝ) ^ (m - 1))⁻¹ * (Real.sqrt ((3 : ℝ) ^ d) * h1_l2 (h1_cube y m) u.toFun)) +
          Clip * (σ'⁻¹ * (3 : ℝ) ^ (m - 1) * F))) + a2 * F) := by
  intro x hx
  obtain ⟨j, hj⟩ := ip_tiling y x l
  have hrel := ip_cell_center hx hj
  have h1 := HFlux j hrel x hj
  have h2 := HL j hrel
  set z := y + l2b_pt l j with hz
  set E := lipGradL2 (shiftCube z ((l + 1 : ℕ) : ℤ)) u.grad with hE
  have hsq : 0 < Real.sqrt σ' / Real.sqrt nu := by positivity
  have hsn : 0 < Real.sqrt nu / Real.sqrt σ' := by positivity
  have hOz := ip_osc_pred hml hrel (v := u.toFun) (by
    rw [← hr_shiftCube_eq]; exact u.memL2)
  have hE' : E ≤ Real.sqrt σ' / Real.sqrt nu *
      (Clip * (((3 : ℝ) ^ (m - 1))⁻¹ * (Real.sqrt ((3 : ℝ) ^ d) * h1_l2 (h1_cube y m) u.toFun)) +
        Clip * (σ'⁻¹ * (3 : ℝ) ^ (m - 1) * F)) := by
    have e : E = Real.sqrt σ' / Real.sqrt nu * (Real.sqrt nu / Real.sqrt σ' * E) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hsq.le
    refine h2.trans ?_
    have : ((3 : ℝ) ^ (m - 1))⁻¹ * h1_l2 (h1_cube z (m - 1)) u.toFun ≤
        ((3 : ℝ) ^ (m - 1))⁻¹ * (Real.sqrt ((3 : ℝ) ^ d) * h1_l2 (h1_cube y m) u.toFun) :=
      mul_le_mul_of_nonneg_left hOz (by positivity)
    nlinarith only [this, hClip]
  refine h1.trans ?_
  have := mul_le_mul_of_nonneg_left hE' ha1
  have := mul_le_mul_of_nonneg_left (add_le_add_left this (a2 * F)) hKd
  linarith only [this]


/-- An essential-supremum bound gives an almost-everywhere bound. -/
theorem ip_ae_of_eLpNorm {H : Set (Vec d)} {g : Vec d → ℝ} {S : ℝ} (h0 : 0 ≤ S)
    (h : eLpNorm g ⊤ (volume.restrict H) ≤ ENNReal.ofReal S) :
    ∀ᵐ x ∂(volume.restrict H), |g x| ≤ S := by
  have h2 := eLpNormEssSup_le_eLpNorm_top.trans h
  filter_upwards [enorm_ae_le_eLpNormEssSup g (volume.restrict H)] with x hx
  have := hx.trans h2
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff h0] at this

/-- **The mollification error from the De Giorgi estimate on the cells.** -/
theorem ip_moll_bound [NeZero d] (hd : 2 ≤ d) :
    ∃ CDG : ℝ, 0 < CDG ∧ ∀ {y : Vec d} {l m : ℕ}, l + 5 ≤ m →
      ∀ {a : CoeffField d} {nu Lam F T2 : ℝ}, 0 < nu → 0 ≤ F →
      IsEllipticFieldOn nu Lam (shiftCube y (m : ℤ)) a →
      ∀ (u : H1Function (shiftCube y (m : ℤ))) {f : Vec d → ℝ}, Measurable f → (∀ x, |f x| ≤ F) →
      IsWeakSolutionOn a (shiftCube y (m : ℤ)) u f (fun _ => 0) →
      (∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ m / 4 + 3 ^ l →
        h1_l2 (h1_cube (y + l2b_pt l j) (l + 3)) u.toFun ≤ T2) →
      ∀ {η : Vec d → ℝ}, Continuous η → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ {V : Set (Vec d)}, MeasurableSet V → V ⊆ Metric.ball y ((3 : ℝ) ^ m / 4) →
        ∀ᵐ x ∂(volume.restrict V),
          |u.toFun x - l2a_moll d ((3 : ℝ) ^ l) η u.toFun x| ≤
            2 * (CDG * (Lam / nu) ^ deGiorgiPower d *
              (T2 + (3 : ℝ) ^ (2 * (l + 3)) / nu * F)) := by
  obtain ⟨CDG, hCDG, H⟩ := ip_cell_dg hd
  refine ⟨CDG, hCDG, ?_⟩
  intro y l m hml a nu Lam F T2 hnu hF hEll u f hfm hfb hu hT2 η hηc hη0 hη1 hηs V hVm hV
  set S : ℝ := CDG * (Lam / nu) ^ deGiorgiPower d * (T2 + (3 : ℝ) ^ (2 * (l + 3)) / nu * F) with hS
  have h3l : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  have hcov : V ⊆ ⋃ j : Fin d → ℤ, (l2b_cell (y + l2b_pt l j) l ∩ V) := by
    intro x hx
    obtain ⟨j, hj⟩ := ip_tiling y x l
    exact Set.mem_iUnion.2 ⟨j, hj, hx⟩
  refine ip_ae_cover hcov (fun j => ?_)
  by_cases hne : (l2b_cell (y + l2b_pt l j) l ∩ V).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp
  obtain ⟨x0, hx0c, hx0V⟩ := hne
  have hrel := ip_cell_center (hV hx0V |> Metric.mem_ball.1) hx0c
  set z := y + l2b_pt l j with hz
  have hsub : shiftCube z ((l + 3 : ℕ) : ℤ) ⊆ shiftCube y (m : ℤ) := by
    rw [ip_shiftCube_ball, ip_shiftCube_ball]
    exact ip_cube_sub hml le_rfl hrel
  have hopen := rc_isOpen_shiftCube z ((l + 3 : ℕ) : ℤ)
  have hEll' : IsEllipticFieldOn nu Lam (shiftCube z ((l + 3 : ℕ) : ℤ)) a :=
    hEll.mono hopen.measurableSet hsub
  have hu' := hu.restrict' hopen hsub
  set c : ℝ := h1_avg (h1_cube z (l + 3)) u.toFun with hc
  have hDG := H z (l + 3) hEll' f (u.restrict hopen hsub) c hu'
  have hcube : shiftCube z ((l + 3 : ℕ) : ℤ) = h1_cube z (l + 3) := hr_shiftCube_eq z (l + 3)
  have hu2 : MemLp u.toFun 2 (volume.restrict (h1_cube z (l + 3))) := by
    rw [← hcube]
    exact u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hlp : lpBar (shiftCube z ((l + 3 : ℕ) : ℤ)) 2 (fun x => (u.restrict hopen hsub).toFun x - c) =
      ENNReal.ofReal (h1_l2 (h1_cube z (l + 3)) u.toFun) := by
    change lpBar (shiftCube z ((l + 3 : ℕ) : ℤ)) 2
      (fun x => u.toFun x - h1_avg (h1_cube z (l + 3)) u.toFun) = _
    rw [hcube]
    exact hr_lpBar_eq (h1_vol_cube_ne_top z (l + 3)) (h1_vol_cube_pos z (l + 3)) hu2
  have hfF : eLpNorm f ⊤ (volume.restrict (shiftCube z ((l + 3 : ℕ) : ℤ))) ≤ ENNReal.ofReal F := by
    rw [eLpNorm_exponent_top hfm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hfb x)
  have hK0 : 0 ≤ CDG * (Lam / nu) ^ deGiorgiPower d := by
    obtain ⟨-, hle, -, -⟩ := hEll.2 y (rc_mem_shiftCube_self y _)
    exact mul_nonneg hCDG.le (Real.rpow_nonneg (div_nonneg (hnu.le.trans hle) hnu.le) _)
  have hbd : eLpNorm (fun x => u.toFun x - c) ⊤ (volume.restrict (Metric.ball z ((3 : ℝ) ^ (l + 3) / 4)))
      ≤ ENNReal.ofReal S := by
    refine hDG.trans ?_
    rw [hlp]
    have hw0 : 0 ≤ (3 : ℝ) ^ (2 * (l + 3)) / nu := by positivity
    calc ENNReal.ofReal (CDG * (Lam / nu) ^ deGiorgiPower d) *
          (ENNReal.ofReal (h1_l2 (h1_cube z (l + 3)) u.toFun) +
            ENNReal.ofReal ((3 : ℝ) ^ (2 * (l + 3)) / nu) *
              eLpNorm f ⊤ (volume.restrict (shiftCube z ((l + 3 : ℕ) : ℤ))))
        ≤ ENNReal.ofReal (CDG * (Lam / nu) ^ deGiorgiPower d) *
          (ENNReal.ofReal (h1_l2 (h1_cube z (l + 3)) u.toFun) +
            ENNReal.ofReal ((3 : ℝ) ^ (2 * (l + 3)) / nu) * ENNReal.ofReal F) := by gcongr
      _ = ENNReal.ofReal (CDG * (Lam / nu) ^ deGiorgiPower d *
            (h1_l2 (h1_cube z (l + 3)) u.toFun + (3 : ℝ) ^ (2 * (l + 3)) / nu * F)) := by
          rw [← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add (show 0 ≤ h1_l2 (h1_cube z (l + 3)) u.toFun from Real.sqrt_nonneg _)
            (by positivity),
            ← ENNReal.ofReal_mul hK0]
      _ ≤ ENNReal.ofReal S := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hS]
          exact mul_le_mul_of_nonneg_left (by linarith only [hT2 j hrel]) hK0
  have hT2j := hT2 j hrel
  have hl20 : 0 ≤ h1_l2 (h1_cube z (l + 3)) u.toFun := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact mul_nonneg hK0 (add_nonneg (hl20.trans hT2j) (by positivity))
  have hae := ip_ae_of_eLpNorm hS0 hbd
  have hballQ : Metric.ball z ((3 : ℝ) ^ (l + 3) / 4) ⊆ shiftCube y (m : ℤ) := by
    refine Set.Subset.trans ?_ hsub
    rw [ip_shiftCube_ball]
    exact Metric.ball_subset_ball (by have : (0 : ℝ) < 3 ^ (l + 3) := by positivity
                                      linarith only [this])
  have hum : AEStronglyMeasurable u.toFun (volume.restrict (Metric.ball z ((3 : ℝ) ^ (l + 3) / 4))) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hballQ le_rfl)
  have hcellball : l2b_cell z l ∩ V ⊆ Metric.ball z ((3 : ℝ) ^ (l + 3) / 4) := by
    intro x hx
    rw [Metric.mem_ball]
    have h1 := ip_cell_dist hx.1
    have : (3 : ℝ) ^ (l + 3) = 27 * 3 ^ l := by rw [pow_add]; norm_num; ring
    rw [this]; linarith only [h1, h3l]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hcellball hae,
    ae_restrict_mem ((l2b_cell_measurable z l).inter (hVm))] with x hx hxm
  have hm := ip_moll_sub_le h3l hηc hη0 hη1 hηs Metric.isOpen_ball.measurableSet
    (ip_closedBall_sub hxm.1) hum hae
  have e : u.toFun x - l2a_moll d ((3 : ℝ) ^ l) η u.toFun x =
      (u.toFun x - c) - (l2a_moll d ((3 : ℝ) ^ l) η u.toFun x - c) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith only [hx, hm]

/-- The closed and the open translated cube differ by a null set. -/
theorem ip_restrict_cell (z : Vec d) (n : ℕ) :
    volume.restrict (l2b_cell z n) = volume.restrict (shiftCube z (n : ℤ)) := by
  have h1 := (measurePreserving_addRight_restrict_translateSet z (cubeSet (originCube d (n : ℤ)))).map_eq
  have h2 := (measurePreserving_addRight_restrict_translateSet z
    (openCubeSet (originCube d (n : ℤ)))).map_eq
  have e := volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d (n : ℤ))
  rw [ip_shiftCube_eq, ← h2, ← e, h1]
  rfl

/-- The cell average is the normalized norm on the translated cube. -/
theorem ip_avg_eq_lpBar {z : Vec d} {n : ℕ} {g : Vec d → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : AEStronglyMeasurable g (volume.restrict (shiftCube z (n : ℤ)))) :
    l2b_avg (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ)))) (l2b_cell z n)
        (fun x => ‖g x‖ₑ) r = lpBar (shiftCube z (n : ℤ)) (ENNReal.ofReal r) g := by
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hvol : volume (shiftCube z (n : ℤ)) = ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) := by
    have := congrArg (fun μ => μ Set.univ) (ip_restrict_cell z n)
    simp only [Measure.restrict_apply_univ] at this
    rw [← this]
    exact l2b_volume_cell' z n
  unfold l2b_avg lpBar
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top
    (hg.smul_measure ((volume (shiftCube z (n : ℤ)))⁻¹)), ENNReal.toReal_ofReal hr.le,
    lintegral_smul_measure, hvol, ip_restrict_cell]
  simp only [smul_eq_mul]

/-- A bounded function has small cell average. -/
theorem ip_avg_le {z : Vec d} {n : ℕ} {f : Vec d → ℝ} {F r : ℝ} (hr : 0 < r)
    (hf : ∀ x, |f x| ≤ F) :
    l2b_avg (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ)))) (l2b_cell z n)
        (fun x => ‖f x‖ₑ) r ≤ ENNReal.ofReal F := by
  unfold l2b_avg
  have hv0 : ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) ≠ 0 := by
    have := cubeVolume_pos (originCube d (n : ℤ))
    simpa using this
  have hvt : ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : ∫⁻ x in l2b_cell z n, ‖f x‖ₑ ^ r ≤
      ∫⁻ x in l2b_cell z n, ENNReal.ofReal F ^ r := by
    refine lintegral_mono fun x => ?_
    refine ENNReal.rpow_le_rpow ?_ hr.le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hf x)
  rw [lintegral_const, Measure.restrict_apply_univ, l2b_volume_cell'] at h1
  have h2 : (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ *
      ∫⁻ x in l2b_cell z n, ‖f x‖ₑ ^ r ≤ ENNReal.ofReal F ^ r := by
    calc (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ * ∫⁻ x in l2b_cell z n, ‖f x‖ₑ ^ r
        ≤ (ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ *
          (ENNReal.ofReal F ^ r * ENNReal.ofReal (cubeVolume (originCube d (n : ℤ)))) := by
          gcongr
      _ = ENNReal.ofReal F ^ r := by
          rw [mul_comm (ENNReal.ofReal F ^ r), ← mul_assoc, ENNReal.inv_mul_cancel hv0 hvt, one_mul]
  calc ((ENNReal.ofReal (cubeVolume (originCube d (n : ℤ))))⁻¹ *
        ∫⁻ x in l2b_cell z n, (fun x => ‖f x‖ₑ) x ^ r) ^ (1 / r)
      ≤ (ENNReal.ofReal F ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal F := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- The translated cube has positive finite volume. -/
theorem ip_volume_shiftCube_ne (z : Vec d) (n : ℕ) :
    volume (shiftCube z (n : ℤ)) ≠ 0 ∧ volume (shiftCube z (n : ℤ)) ≠ ⊤ := by
  rw [ip_shiftCube_ball]
  refine ⟨(Metric.isOpen_ball.measure_pos volume ⟨z, Metric.mem_ball_self (by positivity)⟩).ne',
    Metric.isBounded_ball.measure_lt_top.ne⟩

/-- **The cell bound of the mollified flux, in real form.** -/
theorem ip_flux_real {W : Set (Vec d)} {u : H1Function W} {z : Vec d} {n : ℕ}
    (hsub : shiftCube z ((n + 1 : ℕ) : ℤ) ⊆ W) {f : Vec d → ℝ} {F q : ℝ} (hq : 0 < q)
    (hf : ∀ x, |f x| ≤ F) {nm K a1 a2 : ℝ} (hK : 0 ≤ K) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (h : ENNReal.ofReal nm ≤ ENNReal.ofReal K *
      (ENNReal.ofReal a1 * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
          (l2b_cell z (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
        ENNReal.ofReal a2 * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
          (l2b_cell z (n + 1)) (fun x => ‖f x‖ₑ) q)) :
    nm ≤ K * (a1 * lipGradL2 (shiftCube z ((n + 1 : ℕ) : ℤ)) u.grad + a2 * F) := by
  have hF : 0 ≤ F := (abs_nonneg _).trans (hf 0)
  have hmem : MemLp (fun x => eucNorm (u.grad x)) 2 (volume.restrict (shiftCube z ((n + 1 : ℕ) : ℤ))) :=
    (memLp_eucNorm_grad u).mono_measure (Measure.restrict_mono hsub le_rfl)
  have e1 := ip_avg_eq_lpBar (z := z) (n := n + 1) (g := fun x => eucNorm (u.grad x)) (r := 2)
    (by norm_num) hmem.aestronglyMeasurable
  rw [ENNReal.ofReal_ofNat] at e1
  have hne : lpBar (shiftCube z ((n + 1 : ℕ) : ℤ)) 2 (fun x => eucNorm (u.grad x)) ≠ ⊤ :=
    lip_lpBar_ne_top (ip_volume_shiftCube_ne z (n + 1)).1 hmem
  have e2 : ENNReal.ofReal (lipGradL2 (shiftCube z ((n + 1 : ℕ) : ℤ)) u.grad) =
      lpBar (shiftCube z ((n + 1 : ℕ) : ℤ)) 2 (fun x => eucNorm (u.grad x)) :=
    ENNReal.ofReal_toReal hne
  have e3 := ip_avg_le (z := z) (n := n + 1) (f := f) (F := F) (r := q) hq hf
  rw [e1, ← e2] at h
  have h4 : ENNReal.ofReal nm ≤ ENNReal.ofReal K *
      (ENNReal.ofReal a1 * ENNReal.ofReal (lipGradL2 (shiftCube z ((n + 1 : ℕ) : ℤ)) u.grad) +
        ENNReal.ofReal a2 * ENNReal.ofReal F) := by
    refine h.trans ?_
    gcongr
  have hE0 : 0 ≤ lipGradL2 (shiftCube z ((n + 1 : ℕ) : ℤ)) u.grad := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_mul ha1, ← ENNReal.ofReal_mul ha2, ← ENNReal.ofReal_add (by positivity)
    (by positivity), ← ENNReal.ofReal_mul hK] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4

section
open scoped Matrix.Norms.L2Operator

/-- A continuous function bounded almost everywhere on an open set is bounded everywhere on it. -/
theorem ip_ae_cont_le {g : Vec d → ℝ} (hg : Continuous g) {U : Set (Vec d)} (hU : IsOpen U) {B : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict U), g x ≤ B) : ∀ x ∈ U, g x ≤ B := by
  intro x0 hx0
  by_contra hlt
  rw [not_le] at hlt
  have hO : IsOpen (U ∩ {x | B < g x}) := hU.inter (isOpen_lt continuous_const hg)
  have hpos : 0 < volume (U ∩ {x | B < g x}) := hO.measure_pos volume ⟨x0, hx0, hlt⟩
  have h0 : volume (U ∩ {x | B < g x}) = 0 := by
    have := (ae_restrict_iff' hU.measurableSet).1 h
    rw [ae_iff] at this
    refine measure_mono_null ?_ this
    intro x hx
    exact fun hh => absurd (hh hx.1) (not_le.2 hx.2)
  exact hpos.ne' h0

/-- **Ellipticity of a field `ν Id + c` with `c` skew, continuous, and bounded in operator norm.** -/
theorem ip_isElliptic [NeZero d] {nu B : ℝ} (hnu : 0 < nu) {c : Vec d → Mat d} (hc : Continuous c)
    (hsk : ∀ x, symmPart (nu • (1 : Mat d) + c x) = nu • (1 : Mat d)) {U : Set (Vec d)}
    (hU : IsOpen U)
    (hae : ∀ᵐ x ∂(volume.restrict U), Book.Ch02.matrixOperatorNorm (c x) ≤ B) :
    IsEllipticFieldOn nu (((d : ℝ) * d * (nu + B) ^ 2 + nu ^ 2) / nu) U
      (fun x => nu • (1 : Mat d) + c x) := by
  have hcont : Continuous fun x => Book.Ch02.matrixOperatorNorm (c x) := by
    have : (fun x => Book.Ch02.matrixOperatorNorm (c x)) = fun x => ‖c x‖ := by
      funext x; exact Book.Ch02.matrixOperatorNorm_eq_l2_opNorm _
    rw [this]; exact hc.norm
  have hall := ip_ae_cont_le hcont hU hae
  classical
  refine ⟨?_, fun x hx => ?_⟩
  · refine measurable_matrix_of_entries fun i j => Measurable.ite hU.measurableSet ?_ measurable_const
    have : Continuous fun x => (nu • (1 : Mat d) + c x) i j := by
      have h1 : Continuous fun x => (c x) i j :=
        (continuous_apply j).comp ((continuous_apply i).comp hc)
      simp only [Matrix.add_apply]
      exact continuous_const.add h1
    exact this.measurable
  · refine SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (hsk x) (fun i j => ?_)
    have h1 := Book.Ch02.abs_entry_le_matrixOperatorNorm (c x) i j
    have h2 : |(nu • (1 : Mat d)) i j| ≤ nu := by
      by_cases hij : i = j
      · subst hij; simp [abs_of_pos hnu]
      · simp [hij, hnu.le]
    simp only [Matrix.add_apply]
    calc |(nu • (1 : Mat d)) i j + (c x) i j| ≤ |(nu • (1 : Mat d)) i j| + |(c x) i j| := abs_add_le _ _
      _ ≤ nu + B := add_le_add h2 (h1.trans (hall x hx))

end


/-- A cell next to a relevant centre lies in the cube. -/
theorem ip_cell_sub {y z : Vec d} {l k : ℕ} (hlk : l + 5 ≤ k)
    (hz : dist z y ≤ (3 : ℝ) ^ k / 4 + 3 ^ l) :
    l2b_cell z (l + 1) ⊆ shiftCube y (k : ℤ) := by
  intro x hx
  have h1 := ip_cell_dist hx
  rw [ip_shiftCube_ball, Metric.mem_ball]
  have h2 := ip_pow_gap hlk
  have h3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  have h4 : (3 : ℝ) ^ (l + 1) = 3 * 3 ^ l := by ring
  calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    _ < _ := by rw [h4] at h1; linarith only [h1, hz, h2, h3]

/-- The lattice of the cell centres lies in the grid of the bottom scale. -/
theorem ip_center_mem_grid {N : ℝ} {n k l : ℕ} {A k1 : ℕ} {y : Vec d}
    (hy : y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A))) (hnl : nK N n ≤ l) (hlk : l < k)
    (hk : k ≤ n + k1) (z : Vec d) (j : Fin d → ℤ) (hz : z = y + l2b_pt l j)
    (hzd : dist z y ≤ (3 : ℝ) ^ k / 4 + 3 ^ l) :
    z ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + (A + k1 + 1))) := by
  have hR : (0 : ℝ) ≤ (3 : ℝ) ^ (n + A) := by positivity
  rw [mem_gridPts hR] at hy
  obtain ⟨κ, hκ, hyb⟩ := hy
  have hR' : (0 : ℝ) ≤ (3 : ℝ) ^ (n + (A + k1 + 1)) := by positivity
  rw [mem_gridPts hR']
  refine ⟨fun i => (κ i) + 3 ^ (l + 3 - nK N n) * j i, fun i => ?_, fun i => ?_⟩
  · rw [hz]
    simp only [Pi.add_apply, l2b_pt, hκ i]
    push_cast
    have : (3 : ℝ) ^ l = (3 : ℝ) ^ ((nK N n : ℤ) - 3) * 3 ^ (l + 3 - nK N n) := by
      have e : ((nK N n : ℤ) - 3) + ((l + 3 - nK N n : ℕ) : ℤ) = (l : ℤ) := by omega
      rw [← zpow_natCast, ← zpow_natCast (3 : ℝ) (l + 3 - nK N n), ← zpow_add₀ (by norm_num), e,
        zpow_natCast]
    rw [this]; ring
  · have hd1 : |z i - y i| ≤ (3 : ℝ) ^ k / 4 + 3 ^ l := by
      have := dist_le_pi_dist z y i
      rw [Real.dist_eq] at this
      exact this.trans hzd
    have h3k : (3 : ℝ) ^ k ≤ 3 ^ (n + k1) := pow_le_pow_right₀ (by norm_num) hk
    have h3l : (3 : ℝ) ^ l ≤ 3 ^ (n + k1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hyi := hyb i
    have e1 : (3 : ℝ) ^ (n + (A + k1 + 1)) = 3 * (3 ^ n * 3 ^ A * 3 ^ k1) := by ring
    have e2 : (3 : ℝ) ^ (n + A) = 3 ^ n * 3 ^ A := by ring
    have e3 : (3 : ℝ) ^ (n + k1) = 3 ^ n * 3 ^ k1 := by ring
    have hA1 : (1 : ℝ) ≤ 3 ^ A := one_le_pow₀ (by norm_num)
    have hk1 : (1 : ℝ) ≤ 3 ^ k1 := one_le_pow₀ (by norm_num)
    have hn0 : (0 : ℝ) < 3 ^ n := by positivity
    have habs : |z i| ≤ |y i| + |z i - y i| := by
      have := abs_add_le (y i) (z i - y i)
      simpa using this
    rw [e1]
    rw [e2] at hyi
    rw [e3] at h3k h3l
    have P1 : (3 : ℝ) ^ n * 3 ^ A ≤ 3 ^ n * 3 ^ A * 3 ^ k1 :=
      le_mul_of_one_le_right (by positivity) hk1
    have P2 : (3 : ℝ) ^ n * 3 ^ k1 ≤ 3 ^ n * 3 ^ A * 3 ^ k1 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hn0.le) (by positivity : (0 : ℝ) ≤ 3 ^ k1)
      linarith only [this]
    have P3 : 0 ≤ (3 : ℝ) ^ n * 3 ^ A * 3 ^ k1 := by positivity
    linarith only [habs, hd1, hyi, h3k, h3l, P1, P2, P3]

/-- A function of finite essential supremum has a measurable bounded representative. -/
theorem ip_fmod {W : Set (Vec d)} {f : Vec d → ℝ} (hf : eLpNorm f ⊤ (volume.restrict W) ≠ ⊤) :
    ∃ f' : Vec d → ℝ, Measurable f' ∧ (∀ x, |f' x| ≤ (eLpNorm f ⊤ (volume.restrict W)).toReal) ∧
      ∀ᵐ x ∂(volume.restrict W), f' x = f x := by
  set F : ℝ := (eLpNorm f ⊤ (volume.restrict W)).toReal with hF
  have hm : AEStronglyMeasurable f (volume.restrict W) := by
    by_contra hn
    exact hf (eLpNorm_of_not_aestronglyMeasurable hn)
  have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
  set f1 : Vec d → ℝ := hm.mk f with hf1
  have hf1m : Measurable f1 := hm.stronglyMeasurable_mk.measurable
  have hae1 : ∀ᵐ x ∂(volume.restrict W), f x = f1 x := hm.ae_eq_mk
  have hbd : ∀ᵐ x ∂(volume.restrict W), |f x| ≤ F := by
    have h := enorm_ae_le_eLpNormEssSup f (volume.restrict W)
    rw [← eLpNorm_exponent_top hm] at h
    filter_upwards [h] with x hx
    have := ENNReal.toReal_mono hf hx
    rwa [toReal_enorm, Real.norm_eq_abs] at this
  refine ⟨fun x => if |f1 x| ≤ F then f1 x else 0, ?_, fun x => ?_, ?_⟩
  · exact Measurable.ite (measurableSet_le hf1m.abs measurable_const) hf1m measurable_const
  · by_cases h : |f1 x| ≤ F
    · simp only [h, ite_true]
    · simp only [h, ite_false, abs_zero]; exact hF0
  · filter_upwards [hae1, hbd] with x h1 h2
    have : |f1 x| ≤ F := by rw [← h1]; exact h2
    simp only [this, ite_true, h1]

/-- Weak solutions only depend on the right-hand side almost everywhere. -/
theorem ip_sol_congr {a : CoeffField d} {W : Set (Vec d)} {u : H1Function W} {f f' : Vec d → ℝ}
    (h : ∀ᵐ x ∂(volume.restrict W), f' x = f x) (hu : IsWeakSolutionOn a W u f (fun _ => 0)) :
    IsWeakSolutionOn a W u f' (fun _ => 0) := by
  intro φ
  rw [hu φ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- A solution for the recentred field is a solution for the centred field. -/
theorem ip_centered_of_recentered {a b : CoeffField d} {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) {S : Mat d}
    (hS : matTranspose S = -S) (hab : ∀ x, b x = a x + S) {u : H1Function W} {f : Vec d → ℝ}
    (hu : IsWeakSolutionOn a W u f (fun _ => 0)) : IsWeakSolutionOn b W u f (fun _ => 0) := by
  have : IsFiniteMeasure (volumeMeasureOn W) :=
    ⟨by simp only [volumeMeasureOn, Measure.restrict_apply_univ]; exact hWb.measure_lt_top⟩
  exact (isWeakSolutionOn_congr_const_skew hW hS hab
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2)).2 hu

theorem ip_p_ge_one {d : ℕ} (hd : 2 ≤ d) : 1 ≤ deGiorgiPower d := by
  rcases Nat.eq_or_lt_of_le hd with h | h
  · subst h; rw [deGiorgiPower_two]; norm_num
  · rw [deGiorgiPower_of_three_le (by omega)]
    have : (3 : ℝ) ≤ d := by exact_mod_cast h
    linarith only [this]

theorem ip_conj_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Real.conjExponent (sobStar d) := by
  have hs : 1 < sobStar d := by linarith only [two_lt_sobStar hd]
  exact (Real.HolderConjugate.conjExponent hs).symm.pos

theorem ip_ceil_le {N M k : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) (hk : 1 ≤ k) :
    ((⌈N * Real.log k⌉₊ : ℕ) : ℤ) ≤ ⌈M * Real.log k⌉ := by
  have hl : 0 ≤ Real.log k := Real.log_nonneg hk
  rw [Int.natCast_ceil_eq_ceil (mul_nonneg hN hl)]
  exact Int.ceil_mono (mul_le_mul_of_nonneg_right hNM hl)

end SuperdiffusionCLT.Section7
