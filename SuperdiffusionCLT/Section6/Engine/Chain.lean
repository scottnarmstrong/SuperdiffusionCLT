/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.AffineSlopeB

/-!
# The chain from a top-scale corrected affine to a bottom-scale one: one step

The corrected-affine map `V j` is compared with `V l` for `l ≤ j ≤ l + Hb`: if
`w = V j r + R` with `R` small at scale `l`, there is `q` with the same best-affine slope
at scale `l` as `w`, `w - V l q` small at scale `l`, and `|q| ≈ |r|`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb5a_engCube_mono {m n : ℕ} (h : m ≤ n) : engCube d m ⊆ engCube d n := by
  intro y hy
  have hy' := mem_openCubeSet_originCube_iff.1 hy
  show y ∈ openCubeSet (originCube d (n : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := hy' i
  have hle : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) h
  constructor <;> linarith only [hi.1, hi.2, hle]

/-- A solution on a cube restricts to a solution on a smaller cube. -/
theorem eb5a_sol_restrict {a : CoeffField d} {m l : ℕ} {w : Vec d → ℝ} {g : Vec d → Vec d}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hlm : l ≤ m) (h : IsSolOn a (engCube d m) w g) : IsSolOn a (engCube d l) w g :=
  IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _) (eb5a_engCube_mono hlm)
    (volume_openCubeSet_lt_top _).ne (hell l) h

theorem eb5a_memLp {a : CoeffField d} {m l : ℕ} {w : Vec d → ℝ} {g : Vec d → Vec d}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hlm : l ≤ m) (h : IsSolOn a (engCube d m) w g) :
    MemLp w 2 (normalizedCubeMeasure (originCube d (l : ℤ))) :=
  (eb5a_sol_restrict hell hlm h).memLp.1

theorem eb5a_engNorm_neg (x : Vec d) : engNorm (-x) = engNorm x := by
  have h := engNorm_smul (-1 : ℝ) x
  simpa using h

theorem eb5a_engNorm_sub_le (x y : Vec d) : engNorm (x - y) ≤ engNorm x + engNorm y := by
  rw [sub_eq_add_neg]
  refine (engNorm_add_le _ _).trans ?_
  rw [eb5a_engNorm_neg]

theorem eb5a_engNorm_sub_comm (x y : Vec d) : engNorm (x - y) = engNorm (y - x) := by
  rw [← neg_sub, eb5a_engNorm_neg]

theorem eb5a_engNorm_le_sub_add (x y : Vec d) : engNorm x ≤ engNorm (x - y) + engNorm y := by
  have h := engNorm_add_le (x - y) y
  rwa [sub_add_cancel] at h

theorem eb5a_flat_sub_le [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeFlat n (fun x => f x - g x) ≤ cubeFlat n f + cubeFlat n g := by
  have hg' : MemLp (fun x => (-1 : ℝ) * g x) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
    simpa using hg.const_mul (-1 : ℝ)
  have h := cubeFlat_add_le hf hg'
  have h2 := cubeFlat_const_mul (d := d) n (-1 : ℝ) g
  simp only [abs_neg, abs_one, one_mul] at h2
  rw [h2] at h
  simpa only [neg_mul, one_mul, ← sub_eq_add_neg] using h

/-- The slope of the corrected affine `F e` at scale `l` is a linear map of `e`. -/
theorem eb5a_exists_slopeMap [NeZero d] (l : ℕ) (F : Vec d →ₗ[ℝ] (Vec d → ℝ))
    (hF : ∀ e : Vec d, MemLp (F e) 2 (normalizedCubeMeasure (originCube d (l : ℤ)))) :
    ∃ T : Vec d →ₗ[ℝ] Vec d, ∀ e, T e = affSlope l (F e) := by
  refine ⟨{ toFun := fun e => affSlope l (F e), map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro x y
    have h : F (x + y) = fun z => F x z + F y z := by
      rw [map_add]
      rfl
    show affSlope l (F (x + y)) = affSlope l (F x) + affSlope l (F y)
    rw [h]
    exact affSlope_add (hF x) (hF y)
  · intro c x
    have h : F (c • x) = fun z => c * F x z := by
      rw [map_smul]
      rfl
    show affSlope l (F (c • x)) = c • affSlope l (F x)
    rw [h, affSlope_const_mul]

theorem eb5a_sqrt3_le : 2 * Real.sqrt 3 ≤ 4 := by
  have : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  linarith only [this]

theorem eb5a_ratio_up {N Q P : ℝ} (hN0 : 0 ≤ N) (hN : N ≤ 1 / 64) (hP : 0 ≤ P)
    (h : Q ≤ P + N * Q + 7 * N * P) : Q ≤ (1 + 32 * N) * P := by
  by_contra hcon0
  have hcon := not_le.1 hcon0
  have h1 : 0 < 1 - N := by linarith only [hN]
  have h2 : 0 < Q - (1 + 32 * N) * P := by linarith only [hcon]
  nlinarith only [mul_pos h1 h2, mul_nonneg hN0 hP, mul_nonneg (mul_nonneg hN0 hN0) hP, hN, hN0,
    h, hP]

theorem eb5a_ratio_down {N Q P : ℝ} (hN0 : 0 ≤ N) (hN : N ≤ 1 / 64) (hQ : 0 ≤ Q)
    (h : P ≤ Q + N * Q + 7 * N * P) : P ≤ (1 + 32 * N) * Q := by
  by_contra hcon0
  have hcon := not_le.1 hcon0
  have h1 : 0 < 1 - 7 * N := by linarith only [hN]
  have h2 : 0 < P - (1 + 32 * N) * Q := by linarith only [hcon]
  nlinarith only [mul_pos h1 h2, mul_nonneg hN0 hQ, mul_nonneg (mul_nonneg hN0 hN0) hQ, hN, hN0,
    h, hQ]

/-- One step of the chain: if `w = V j r + R` with `R` flat at scale `l`, then some `q` has the
slope of `w` at scale `l`, `w - V l q` is flat of size `6 K δ_l |q|`, and `|q| ≈ |r|`. -/
theorem eb5a_step [NeZero d] (K : ℝ) (hK : 1 ≤ K) (δ : ℕ → ℝ) (Hb l j : ℕ)
    (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ))
    (hlj : l ≤ j) (hjl : j ≤ l + Hb) (hδl : 0 ≤ δ l) (hmono : δ j ≤ δ l)
    (hN : 64 * K * δ l * ((Hb : ℝ) + 1) ≤ 1)
    (hVl : ∀ e, MemLp (V l e) 2 (normalizedCubeMeasure (originCube d (l : ℤ))))
    (hVj : ∀ e, MemLp (V j e) 2 (normalizedCubeMeasure (originCube d (l : ℤ))))
    (hflat_lj : ∀ e : Vec d,
      cubeFlat l (fun x => V j e x - vecDot (affSlope l (V j e)) x) ≤ K * δ j * engNorm e ∧
        engNorm (affSlope l (V j e) - e) ≤ K * δ j * ((j : ℝ) - (l : ℝ) + 1) * engNorm e)
    (hflat_ll : ∀ e : Vec d,
      cubeFlat l (fun x => V l e x - vecDot (affSlope l (V l e)) x) ≤ K * δ l * engNorm e ∧
        engNorm (affSlope l (V l e) - e) ≤ K * δ l * ((l : ℝ) - (l : ℝ) + 1) * engNorm e)
    (w R : Vec d → ℝ) (r : Vec d) (hw : ∀ x, w x = V j r x + R x)
    (hRm : MemLp R 2 (normalizedCubeMeasure (originCube d (l : ℤ))))
    (hR : cubeFlat l R ≤ 3 / 2 * K * δ l * engNorm r) :
    ∃ q : Vec d, affSlope l (V l q) = affSlope l w ∧
      cubeFlat l (fun x => w x - V l q x) ≤ 6 * K * δ l * engNorm q ∧
      engNorm q ≤ (1 + 32 * (K * δ l * ((Hb : ℝ) + 1))) * engNorm r ∧
      engNorm r ≤ (1 + 32 * (K * δ l * ((Hb : ℝ) + 1))) * engNorm q := by
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hHb1 : (1 : ℝ) ≤ (Hb : ℝ) + 1 := by linarith only [(Nat.cast_nonneg Hb : (0 : ℝ) ≤ Hb)]
  have hKδ0 : 0 ≤ K * δ l := mul_nonneg hK0 hδl
  have hN0 : 0 ≤ K * δ l * ((Hb : ℝ) + 1) := mul_nonneg hKδ0 (by linarith only [hHb1])
  set N := K * δ l * ((Hb : ℝ) + 1) with hNdef
  have hN' : N ≤ 1 / 64 := by
    have : 64 * K * δ l * ((Hb : ℝ) + 1) = 64 * N := by rw [hNdef]; ring
    linarith only [hN, this]
  have hKδN : K * δ l ≤ N := by
    calc K * δ l = K * δ l * 1 := by ring
      _ ≤ K * δ l * ((Hb : ℝ) + 1) := mul_le_mul_of_nonneg_left hHb1 hKδ0
  have hKδjN : K * δ j * ((j : ℝ) - (l : ℝ) + 1) ≤ N := by
    have hj : (j : ℝ) ≤ (l : ℝ) + (Hb : ℝ) := by exact_mod_cast hjl
    have h1 : K * δ j ≤ K * δ l := mul_le_mul_of_nonneg_left hmono hK0
    have h2 : (j : ℝ) - (l : ℝ) + 1 ≤ (Hb : ℝ) + 1 := by linarith only [hj]
    have h3 : 0 ≤ (j : ℝ) - (l : ℝ) + 1 := by
      have : (l : ℝ) ≤ (j : ℝ) := by exact_mod_cast hlj
      linarith only [this]
    exact mul_le_mul h1 h2 h3 hKδ0
  obtain ⟨T, hT⟩ := eb5a_exists_slopeMap l (V l) hVl
  have hTc : ∀ e : Vec d, engNorm (T e - e) ≤ 1 / 2 * engNorm e := by
    intro e
    rw [hT e]
    have h := (hflat_ll e).2
    simp only [sub_self, zero_add, mul_one] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hKδN, hN']) (engNorm_nonneg e)
  obtain ⟨hbij, -⟩ := engNorm_bijective_of_close T hTc
  have hwfun : w = fun x => V j r x + R x := funext hw
  obtain ⟨q, hq⟩ := hbij.2 (affSlope l w)
  have hwm : MemLp w 2 (normalizedCubeMeasure (originCube d (l : ℤ))) := by
    rw [hwfun]
    exact (hVj r).add hRm
  set s := affSlope l (V j r) with hs
  set σ := affSlope l R with hσ
  have hws : affSlope l w = s + σ := by
    rw [hwfun]
    exact affSlope_add (hVj r) hRm
  have hTq : T q = s + σ := hq.trans hws
  have hq' : affSlope l (V l q) = affSlope l w := by rw [← hT q]; exact hq
  have e1 : engNorm (q - T q) ≤ N * engNorm q := by
    rw [eb5a_engNorm_sub_comm, hT q]
    refine (hflat_ll q).2.trans ?_
    simp only [sub_self, zero_add, mul_one]
    exact mul_le_mul_of_nonneg_right hKδN (engNorm_nonneg q)
  have e2 : engNorm (s - r) ≤ N * engNorm r :=
    (hflat_lj r).2.trans (mul_le_mul_of_nonneg_right hKδjN (engNorm_nonneg r))
  have e3 : engNorm σ ≤ 6 * N * engNorm r := by
    have h1 := engNorm_affSlope_le hRm
    have h2 := eb5a_sqrt3_le
    have hRn := cubeFlat_nonneg (d := d) l R
    have h4 : engNorm σ ≤ 4 * cubeFlat l R :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hRn)
    have h5 : 4 * cubeFlat l R ≤ 6 * (K * δ l) * engNorm r := by
      linarith only [hR]
    have h6 : 6 * (K * δ l) * engNorm r ≤ 6 * N * engNorm r :=
      mul_le_mul_of_nonneg_right (by linarith only [hKδN]) (engNorm_nonneg r)
    linarith only [h4, h5, h6]
  have hdiff : q - r = (q - T q) + (s - r) + σ := by rw [hTq]; abel
  have hdist : engNorm (q - r) ≤ N * engNorm q + 7 * N * engNorm r := by
    rw [hdiff]
    have a1 := engNorm_add_le ((q - T q) + (s - r)) σ
    have a2 := engNorm_add_le (q - T q) (s - r)
    linarith only [a1, a2, e1, e2, e3]
  have hQ0 := engNorm_nonneg q
  have hP0 := engNorm_nonneg r
  have hup : engNorm q ≤ (1 + 32 * N) * engNorm r := by
    have := eb5a_engNorm_le_sub_add q r
    exact eb5a_ratio_up hN0 hN' hP0 (by linarith only [this, hdist])
  have hdown : engNorm r ≤ (1 + 32 * N) * engNorm q := by
    have := eb5a_engNorm_le_sub_add r q
    rw [eb5a_engNorm_sub_comm] at this
    exact eb5a_ratio_down hN0 hN' hQ0 (by linarith only [this, hdist])
  refine ⟨q, hq', ?_, hup, hdown⟩
  -- flatness
  have hr2 : engNorm r ≤ 2 * engNorm q := by
    nlinarith only [hdown, hN', hQ0]
  have hlin : ∀ p : Vec d, MemLp (fun x => vecDot p x) 2
      (normalizedCubeMeasure (originCube d (l : ℤ))) := fun p => e0c_memLp l (e0c_continuous_vecDot p)
  have f1 : cubeFlat l (fun x => V l q x - vecDot (affSlope l w) x) ≤ K * δ l * engNorm q := by
    have := (hflat_ll q).1
    rwa [hq'] at this
  have f2 : cubeFlat l (fun x => w x - vecDot (affSlope l w) x) ≤
      K * δ j * engNorm r + cubeFlat l R := by
    refine (cubeFlat_sub_affSlope_le hwm s).trans ?_
    have hfun : (fun x => w x - vecDot s x) =
        fun x => (V j r x - vecDot s x) + R x := by
      funext x
      rw [hw x]
      ring
    rw [hfun]
    refine (cubeFlat_add_le ((hVj r).sub (hlin s)) hRm).trans ?_
    exact add_le_add_left (hflat_lj r).1 _
  have hfun : (fun x => w x - V l q x) =
      fun x => (w x - vecDot (affSlope l w) x) - (V l q x - vecDot (affSlope l w) x) := by
    funext x
    ring
  rw [hfun]
  have key := eb5a_flat_sub_le (f := fun x => w x - vecDot (affSlope l w) x)
    (g := fun x => V l q x - vecDot (affSlope l w) x) (hwm.sub (hlin _)) ((hVl q).sub (hlin _))
  refine key.trans ?_
  have g1 : K * δ j * engNorm r ≤ K * δ l * (2 * engNorm q) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hmono hK0) hr2 hP0 hKδ0
  have g2 : cubeFlat l R ≤ 3 / 2 * K * δ l * (2 * engNorm q) :=
    hR.trans (mul_le_mul_of_nonneg_left hr2 (by positivity))
  nlinarith only [f1, f2, g1, g2]

end SuperdiffusionCLT.Section6
