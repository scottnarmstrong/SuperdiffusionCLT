/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2BdryC
public import SuperdiffusionCLT.Section7.Root.InteriorApproxF
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryLocalizedC
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalD

/-!
# Boundary `L^∞`-`L²` estimate: De Giorgi on a bottom-scale cell
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem linfL2c_shiftCube_axis (z : Vec d) (n : ℕ) :
    shiftCube z (n : ℤ) = axisCube (fun i => z i - (3 : ℝ) ^ n / 2) ((3 : ℝ) ^ n) := by
  ext x
  rw [hr_shiftCube_eq, h1_mem_cube_iff]
  unfold axisCube
  rw [Set.mem_pi]
  refine forall_congr' fun i => ?_
  simp only [Set.mem_univ, true_implies, Set.mem_Ioo]
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]

theorem linfL2c_cube_sub_half (z : Vec d) (n : ℕ) :
    shiftCube z (n : ℤ) ⊆ halfCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)) := by
  intro x hx
  rw [hr_shiftCube_eq, h1_mem_cube_iff] at hx
  unfold halfCube axisCube
  rw [Set.mem_pi]
  intro i _
  have h := abs_lt.1 (hx i)
  have e : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by ring
  have hp : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  simp only [Pi.add_apply, Set.mem_Ioo]
  rw [e]
  constructor <;> linarith only [h.1, h.2, hp]

/-- **De Giorgi on a cell that meets the boundary** (localized zero trace). -/
theorem linfL2c_dg_cut (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {lam Lam : ℝ} {a : CoeffField d} {S V : Set (Vec d)}, IsOpen S →
      ∀ (z : Vec d) (n : ℕ), V = S ∩ shiftCube z ((n + 1 : ℕ) : ℤ) →
      IsEllipticFieldOn lam Lam V a → ∀ u : H1Function V,
        LocalizedZeroTraceFunctionOn V (shiftCube z ((n + 1 : ℕ) : ℤ)) u.toFun →
        IsWeakSolutionOn a V u (fun _ => 0) (fun _ => 0) →
        volume V ≠ ⊤ → 0 < (volume V).toReal →
        eLpNorm u.toFun ⊤ (volume.restrict (S ∩ shiftCube z (n : ℤ))) ≤
          ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d * linfL2b_nl2 V u.toFun) := by
  obtain ⟨C, hC, H⟩ := deGiorgi_boundary_localized_scaled hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a S V hS z n hV hEll u hz hw hfin hpos
  have hax := linfL2c_shiftCube_axis z (n + 1)
  rw [hax] at hV hz
  subst hV
  have hL : (0 : ℝ) < (3 : ℝ) ^ (n + 1) := by positivity
  have hnl : lpBar (S ∩ axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1))) 2
      u.toFun = ENNReal.ofReal (linfL2b_nl2 (S ∩ axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
        ((3 : ℝ) ^ (n + 1))) u.toFun) := linfL2b_lpBar_eq hfin hpos u.memL2
  have hR := H hS (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) hL hEll (fun _ => 0) u hz hw
    (ENNReal.ofReal (linfL2b_nl2 (S ∩ axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
        ((3 : ℝ) ^ (n + 1))) u.toFun / (3 : ℝ) ^ (n + 1))) (by
      rw [hnl, ← ENNReal.ofReal_mul hL.le]
      rw [mul_div_cancel₀ _ hL.ne'])
    (shiftCube z (n : ℤ)) (linfL2c_cube_sub_half z n)
  have e1 : eLpNorm (fun _ : Vec d => (0 : ℝ)) ⊤
      (volume.restrict (S ∩ axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)))) =
        0 := eLpNorm_zero
  rw [e1, mul_zero, add_zero, ← ENNReal.ofReal_mul hL.le, mul_div_cancel₀ _ hL.ne'] at hR
  have hnn := linfL2b_nl2_nonneg (S ∩ axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
        ((3 : ℝ) ^ (n + 1))) u.toFun
  rw [← ENNReal.ofReal_mul'] at hR
  · exact hR
  · exact hnn

/-- The normalised `L²` norm of the oscillation, from the unnormalised one on a cube. -/
theorem linfL2c_cube_norm {L : ℝ} (hL : 0 < L) {Q : Set (Vec d)} (hQ : (volume Q).toReal = L ^ d)
    {F : Vec d → ℝ} (hF : MemLp F 2 (volume.restrict Q)) :
    ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * eLpNorm F 2 (volume.restrict Q) =
      ENNReal.ofReal (Real.sqrt ((∫ x in Q, F x ^ 2) / (volume Q).toReal)) := by
  rw [linfL2b_eLpNorm_two_eq hF, ← ENNReal.ofReal_mul (by positivity), hQ]
  congr 1
  have hI : 0 ≤ ∫ x in Q, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hLd : (0 : ℝ) < L ^ d := by positivity
  have e1 : L ^ (-(d : ℝ) / 2) = (Real.sqrt (L ^ d))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_neg (by positivity)]
    congr 1
    ring
  rw [e1, Real.sqrt_div hI, div_eq_inv_mul]

/-- **De Giorgi on a cell inside the domain**, for the oscillation about the mean. -/
theorem linfL2c_dg_int (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {lam Lam : ℝ} {a : CoeffField d} {Q : Set (Vec d)} (z : Vec d) (n : ℕ),
      Q = shiftCube z ((n + 1 : ℕ) : ℤ) → IsEllipticFieldOn lam Lam Q a → ∀ u : H1Function Q,
        IsWeakSolutionOn a Q u (fun _ => 0) (fun _ => 0) →
        eLpNorm (fun x => u.toFun x - h1_avg Q u.toFun) ⊤ (volume.restrict (shiftCube z (n : ℤ))) ≤
          ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d * h1_l2 Q u.toFun) := by
  obtain ⟨C, hC, H⟩ := ip_dg_abs hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a Q z n hQ hEll u hw
  have hax := linfL2c_shiftCube_axis z (n + 1)
  rw [hax] at hQ
  subst hQ
  have hvol : (volume (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)))).toReal
      = ((3 : ℝ) ^ (n + 1)) ^ d := by
    rw [← hax, hr_shiftCube_eq]; exact h1_volT_cube z (n + 1)
  have hvpos : 0 < (volume (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)))).toReal := by
    rw [hvol]; positivity
  have hfin : volume (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1))) ≠ ⊤ := by
    rw [← hax]; exact linfL2c_vol_cube_ne_top z _
  have hL : (0 : ℝ) < (3 : ℝ) ^ (n + 1) := by positivity
  have hu2 := u.memL2
  have hF2 : MemLp (fun x => u.toFun x - h1_avg (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
      ((3 : ℝ) ^ (n + 1))) u.toFun) 2 (volume.restrict (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
      ((3 : ℝ) ^ (n + 1)))) := hu2.sub (memLp_const _)
  have hmono : eLpNorm (fun x => u.toFun x - h1_avg (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
      ((3 : ℝ) ^ (n + 1))) u.toFun) ⊤ (volume.restrict (shiftCube z (n : ℤ))) ≤
      eLpNorm (fun x => u.toFun x - h1_avg (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
      ((3 : ℝ) ^ (n + 1))) u.toFun) ⊤
        (volume.restrict (halfCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)))) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono (linfL2c_cube_sub_half z n) le_rfl)
  have h := H (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) hL hEll (fun _ => 0) u
    (h1_avg (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1))) u.toFun) hw
  have e1 : eLpNorm (fun _ : Vec d => (0 : ℝ)) ⊤
      (volume.restrict (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)))) =
        0 := eLpNorm_zero
  rw [e1, mul_zero, add_zero, linfL2c_cube_norm hL hvol hF2] at h
  refine hmono.trans (h.trans ?_)
  have hI : h1_l2 (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1))) u.toFun =
      Real.sqrt ((∫ x in axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)),
        (u.toFun x - h1_avg (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2) ((3 : ℝ) ^ (n + 1)))
          u.toFun) ^ 2) / (volume (axisCube (fun i => z i - (3 : ℝ) ^ (n + 1) / 2)
          ((3 : ℝ) ^ (n + 1)))).toReal) := rfl
  rw [hI, ← ENNReal.ofReal_mul' (Real.sqrt_nonneg _)]

/-- The chain bound with hypotheses only up to the length of the chain. -/
theorem linfL2c_chain_trunc {T : ℕ → Set (Vec d)} {u : Vec d → ℝ} {θ : ℕ → ℝ} {K : ℝ}
    (hK1 : 1 ≤ K) {N : ℕ} (hmono : ∀ t, t < N → T t ⊆ T (t + 1))
    (hfin : ∀ t, t ≤ N → volume (T t) ≠ ⊤) (hpos : ∀ t, t ≤ N → 0 < (volume (T t)).toReal)
    (hL2 : ∀ t, t ≤ N → MemLp u 2 (volume.restrict (T t)))
    (hK : ∀ t, t < N → (volume (T (t + 1))).toReal ≤ K * (volume (T t)).toReal)
    (hosc : ∀ t, t < N → h1_l2 (T (t + 1)) u ≤ θ t) :
    |h1_avg (T 0) u| ≤ Real.sqrt K * ∑ s ∈ Finset.range N, θ s + linfL2b_nl2 (T N) u := by
  have h := linfL2c_chain_mean (T := fun t => T (min t N)) (u := u) (θ := θ) (K := K) (N := N)
    (fun t => by
      by_cases ht : t < N
      · have h1 : min t N = t := min_eq_left ht.le
        have h2 : min (t + 1) N = t + 1 := min_eq_left ht
        simp only [h1, h2]; exact hmono t ht
      · have h1 : min t N = N := min_eq_right (not_lt.1 ht)
        have h2 : min (t + 1) N = N := min_eq_right (by omega)
        simp only [h1, h2]; exact subset_rfl)
    (fun t => hfin _ (min_le_right _ _)) (fun t => hpos _ (min_le_right _ _))
    (fun t => hL2 _ (min_le_right _ _))
    (fun t => by
      by_cases ht : t < N
      · have h1 : min t N = t := min_eq_left ht.le
        have h2 : min (t + 1) N = t + 1 := min_eq_left ht
        simp only [h1, h2]; exact hK t ht
      · have h1 : min t N = N := min_eq_right (not_lt.1 ht)
        have h2 : min (t + 1) N = N := min_eq_right (by omega)
        simp only [h1, h2]
        have := hpos N le_rfl
        nlinarith only [hK1, this])
    (fun t ht => by
      have h2 : min (t + 1) N = t + 1 := min_eq_left ht
      simp only [h2]; exact hosc t ht)
  simpa using h

/-- **The pointwise bound on a bottom-scale cell** from the chain of means, the oscillation
bounds of the boundary estimate, and the De Giorgi estimate. -/
theorem linfL2c_cell_bound (hd : 2 ≤ d) :
    ∃ CD : ℝ, 0 < CD ∧
      ∀ {lam Lam : ℝ} {a : CoeffField d} {S : Set (Vec d)} (hSo : IsOpen S) (u0 : H1Function S)
        (z : Vec d) (n' N m' : ℕ), n' + 1 + N + 1 = m' →
        ∀ {E1 K Y3 D Y : ℝ} (T : ℕ → Set (Vec d)), 0 < lam → lam ≤ Lam → 1 ≤ K → 0 ≤ E1 → 0 ≤ D → 0 ≤ Y →
        T 0 = shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S →
        IsEllipticFieldOn lam Lam (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) a →
        IsWeakSolutionOn a (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S)
          (u0.restrict ((rc_isOpen_shiftCube z _).inter hSo) Set.inter_subset_right)
          (fun _ => 0) (fun _ => 0) →
        (¬ shiftCube z ((n' + 1 : ℕ) : ℤ) ⊆ S →
          LocalizedZeroTraceFunctionOn (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S)
            (shiftCube z ((n' + 1 : ℕ) : ℤ)) u0.toFun) →
        (∀ t, t < N → T t ⊆ T (t + 1)) → (∀ t, t ≤ N → volume (T t) ≠ ⊤) →
        (∀ t, t ≤ N → 0 < (volume (T t)).toReal) →
        (∀ t, t ≤ N → MemLp u0.toFun 2 (volume.restrict (T t))) →
        (∀ t, t < N → (volume (T (t + 1))).toReal ≤ K * (volume (T t)).toReal) →
        (∀ t, t < N → h1_l2 (T (t + 1)) u0.toFun ≤
          E1 * ((3 : ℝ) ^ (n' + 1 + t + 1) / (3 : ℝ) ^ m') * (D + Y)) →
        linfL2b_nl2 (T N) u0.toFun ≤ Y3 →
        h1_l2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun ≤
          E1 * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') * (D + Y) →
        (¬ shiftCube z ((n' + 1 : ℕ) : ℤ) ⊆ S →
          linfL2b_nl2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun ≤
            E1 * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') * (D + Y)) →
        CD * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') ≤ 1 →
        ∀ᵐ x ∂volume.restrict (S ∩ shiftCube z (n' : ℤ)),
          |u0.toFun x| ≤ Real.sqrt K * (E1 * (D + Y) * (1 / 2)) + Y3 + E1 * (D + Y) := by
  obtain ⟨CDc, hCc, Hc⟩ := linfL2c_dg_cut hd
  obtain ⟨CDi, hCi, Hi⟩ := linfL2c_dg_int hd
  refine ⟨max CDc CDi, lt_max_of_lt_left hCc, ?_⟩
  intro lam Lam a S hSo u0 z n' N m' hm' E1 K Y3 D Y T hlam hLL hK1 hE1 hD hY hT0 hEll hw hzero hmono
    hfin hpos hL2 hK hosc hTN hosc0 hcut0 hAbs
  have hVo : IsOpen (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) := (rc_isOpen_shiftCube z _).inter hSo
  have hVfin : volume (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) ≠ ⊤ :=
    ne_top_of_le_ne_top (linfL2c_vol_cube_ne_top z _) (measure_mono Set.inter_subset_left)
  have hVpos : 0 < (volume (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S)).toReal := by
    have := hpos 0 (Nat.zero_le _); rwa [hT0] at this
  -- the mean
  have hchain := linfL2c_chain_trunc (θ := fun t => E1 * (D + Y) * ((3 : ℝ) ^ (n' + 1 + t + 1) / (3 : ℝ) ^ m'))
    hK1 hmono hfin hpos hL2 hK (fun t ht => by
      have := hosc t ht
      calc _ ≤ _ := this
        _ = _ := by ring)
  rw [hT0] at hchain
  have hgeom := linfL2c_geom_chain (n' + 1) N m' (by omega)
  have hsum : ∑ s ∈ Finset.range N, E1 * (D + Y) * ((3 : ℝ) ^ (n' + 1 + s + 1) / (3 : ℝ) ^ m') ≤
      E1 * (D + Y) * (1 / 2) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hmean : |h1_avg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun| ≤
      Real.sqrt K * (E1 * (D + Y) * (1 / 2)) + Y3 := by
    have h1 : Real.sqrt K * ∑ s ∈ Finset.range N,
        E1 * (D + Y) * ((3 : ℝ) ^ (n' + 1 + s + 1) / (3 : ℝ) ^ m') ≤
        Real.sqrt K * (E1 * (D + Y) * (1 / 2)) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    linarith only [hchain, h1, hTN]
  have hEDnn : 0 ≤ E1 * (D + Y) := by positivity
  have hrat : 0 ≤ (3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m' := by positivity
  have hratN : 0 ≤ (Lam / lam) ^ deGiorgiPower d :=
    Real.rpow_nonneg (div_nonneg (by linarith only [hlam, hLL]) hlam.le) _
  have hmeas : AEStronglyMeasurable u0.toFun (volume.restrict (S ∩ shiftCube z (n' : ℤ))) :=
    u0.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
  by_cases hcutQ : shiftCube z ((n' + 1 : ℕ) : ℤ) ⊆ S
  · -- the cell lies inside the domain
    have hVeq : shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S = shiftCube z ((n' + 1 : ℕ) : ℤ) :=
      Set.inter_eq_left.2 hcutQ
    have hsubS : shiftCube z (n' : ℤ) ⊆ S :=
      (linfL2c_cube_mono z (Nat.le_succ n')).trans hcutQ
    have hSeq : S ∩ shiftCube z (n' : ℤ) = shiftCube z (n' : ℤ) := Set.inter_eq_right.2 hsubS
    rw [hSeq]
    have hdg := Hi (lam := lam) (Lam := Lam) (a := a) (Q := shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) z n'
      hVeq hEll (u0.restrict hVo Set.inter_subset_right) hw
    have hmx : 0 ≤ CDi * (Lam / lam) ^ deGiorgiPower d * h1_l2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S)
        u0.toFun := by
      have : 0 ≤ h1_l2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun := Real.sqrt_nonneg _
      positivity
    have hae := decayEst_ae_le_of_eLpNorm_top
      (hmeas.sub aestronglyMeasurable_const |>.mono_measure (by rw [hSeq]))
      hmx hdg
    have hbd : CDi * (Lam / lam) ^ deGiorgiPower d *
        h1_l2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun ≤ E1 * (D + Y) := by
      have h1 : CDi * (Lam / lam) ^ deGiorgiPower d *
          h1_l2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun ≤
          CDi * (Lam / lam) ^ deGiorgiPower d *
            (E1 * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') * (D + Y)) :=
        mul_le_mul_of_nonneg_left hosc0 (by positivity)
      have h2 : CDi * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hratN) hrat) hAbs
      calc _ ≤ _ := h1
        _ = (CDi * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m')) *
            (E1 * (D + Y)) := by ring
        _ ≤ 1 * (E1 * (D + Y)) := mul_le_mul_of_nonneg_right h2 hEDnn
        _ = _ := one_mul _
    filter_upwards [hae] with x hx
    have h3 : |u0.toFun x| ≤ |u0.toFun x - h1_avg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun| +
        |h1_avg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun| := by
      have := abs_add_le (u0.toFun x - h1_avg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun)
        (h1_avg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun)
      simpa using this
    have hx' : |u0.toFun x - h1_avg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun| ≤
        E1 * (D + Y) := le_trans hx hbd
    linarith only [h3, hx', hmean]
  · have hzt := hzero hcutQ
    have hdg := Hc (lam := lam) (Lam := Lam) (a := a) (S := S)
      (V := shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) hSo z n' (Set.inter_comm _ _) hEll
      (u0.restrict hVo Set.inter_subset_right) hzt hw hVfin hVpos
    have hmx : 0 ≤ CDc * (Lam / lam) ^ deGiorgiPower d *
        linfL2b_nl2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun := by
      have := linfL2b_nl2_nonneg (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun
      positivity
    have hae := decayEst_ae_le_of_eLpNorm_top hmeas hmx hdg
    have hbd : CDc * (Lam / lam) ^ deGiorgiPower d *
        linfL2b_nl2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun ≤ E1 * (D + Y) := by
      have h1 : CDc * (Lam / lam) ^ deGiorgiPower d *
          linfL2b_nl2 (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ S) u0.toFun ≤
          CDc * (Lam / lam) ^ deGiorgiPower d *
            (E1 * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') * (D + Y)) :=
        mul_le_mul_of_nonneg_left (hcut0 hcutQ) (by positivity)
      have h2 : CDc * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hratN) hrat) hAbs
      calc _ ≤ _ := h1
        _ = (CDc * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m')) *
            (E1 * (D + Y)) := by ring
        _ ≤ 1 * (E1 * (D + Y)) := mul_le_mul_of_nonneg_right h2 hEDnn
        _ = _ := one_mul _
    filter_upwards [hae] with x hx
    have hnn1 : 0 ≤ Real.sqrt K * (E1 * (D + Y) * (1 / 2)) := by positivity
    have hY3 : 0 ≤ Y3 := le_trans (linfL2b_nl2_nonneg _ _) hTN
    linarith only [hx, hbd, hnn1, hY3]

/-- A chain of lattice points of increasing scale around a lattice point of the fine grid. -/
theorem linfL2c_chain_exists {R : ℝ} {sL e n' N : ℕ} {Mg : ℝ}
    (hcovS : ∀ i : ℕ, i + e + 2 ≤ n' + 1 + N → ∀ x ∈ euclidBall (d := d) R,
      ∃ w ∈ gridPts d (((i + e + 2 : ℕ) : ℤ) - (sL : ℤ)) Mg, w ∈ euclidBall (d := d) R ∧
        ‖x - w‖ ≤ (3 : ℝ) ^ i)
    (he : e + 2 ≤ n' + 1) {z : Vec d}
    (hz : z ∈ gridPts d (((n' + 1 : ℕ) : ℤ) - (sL : ℤ)) Mg) (hzS : z ∈ euclidBall (d := d) R) :
    ∃ zc : ℕ → Vec d, zc 0 = z ∧
      (∀ t, t ≤ N → zc t ∈ gridPts d (((n' + 1 + t : ℕ) : ℤ) - (sL : ℤ)) Mg ∧
        zc t ∈ euclidBall (d := d) R ∧ ‖z - zc t‖ ≤ (3 : ℝ) ^ (n' + 1 + t - (e + 2))) ∧
      (∀ t, t < N → ‖zc t - zc (t + 1)‖ ≤ (3 : ℝ) ^ (n' + 1 + t)) := by
  classical
  have hex : ∀ t : ℕ, ∃ w : Vec d, (t = 0 → w = z) ∧ (t ≤ N →
      w ∈ gridPts d (((n' + 1 + t : ℕ) : ℤ) - (sL : ℤ)) Mg ∧ w ∈ euclidBall (d := d) R ∧
        ‖z - w‖ ≤ (3 : ℝ) ^ (n' + 1 + t - (e + 2))) := by
    intro t
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨z, fun _ => rfl, fun _ => ⟨hz, hzS, ?_⟩⟩
      simp
    · by_cases htN : t ≤ N
      · obtain ⟨w, hw, hwS, hwd⟩ := hcovS (n' + 1 + t - (e + 2)) (by omega) z hzS
        have e1 : n' + 1 + t - (e + 2) + e + 2 = n' + 1 + t := by omega
        rw [e1] at hw
        exact ⟨w, fun h => absurd h ht0, fun _ => ⟨hw, hwS, hwd⟩⟩
      · exact ⟨z, fun h => absurd h ht0, fun h => absurd h htN⟩
  choose zc hzc0 hzc using hex
  refine ⟨zc, hzc0 0 rfl, fun t ht => hzc t ht, fun t ht => ?_⟩
  have h1 := (hzc t ht.le).2.2
  have h2 := (hzc (t + 1) ht).2.2
  have h3 : ‖zc t - zc (t + 1)‖ ≤ ‖z - zc t‖ + ‖z - zc (t + 1)‖ := by
    have : zc t - zc (t + 1) = (z - zc (t + 1)) - (z - zc t) := by abel
    rw [this]
    calc _ ≤ ‖z - zc (t + 1)‖ + ‖z - zc t‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have e1 : n' + 1 + (t + 1) - (e + 2) = (n' + 1 + t - (e + 2)) + 1 := by omega
  rw [e1] at h2
  have hp : (0 : ℝ) < (3 : ℝ) ^ (n' + 1 + t - (e + 2)) := by positivity
  have e2 : (3 : ℝ) ^ (n' + 1 + t) = (3 : ℝ) ^ (n' + 1 + t - (e + 2)) * (3 : ℝ) ^ (e + 2) := by
    rw [← pow_add]; congr 1; omega
  have hee : (9 : ℝ) ≤ (3 : ℝ) ^ (e + 2) := by
    have : (3 : ℝ) ^ 2 ≤ (3 : ℝ) ^ (e + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [this]
  have e3 : (3 : ℝ) ^ (n' + 1 + t - (e + 2) + 1) = 3 * (3 : ℝ) ^ (n' + 1 + t - (e + 2)) := by ring
  rw [e3] at h2
  rw [e2]
  nlinarith only [h1, h2, h3, hp, hee]

theorem linfL2c_cube_nest {w w' : Vec d} {j : ℕ} (h : ‖w - w'‖ ≤ (3 : ℝ) ^ j) :
    shiftCube w (j : ℤ) ⊆ shiftCube w' ((j + 1 : ℕ) : ℤ) := by
  intro y hy
  rw [hr_shiftCube_eq, h1_cube, Metric.mem_ball, dist_eq_norm] at hy
  rw [hr_shiftCube_eq, h1_cube, Metric.mem_ball, dist_eq_norm]
  have h1 : ‖y - w'‖ ≤ ‖y - w‖ + ‖w - w'‖ := by
    have : y - w' = (y - w) + (w - w') := by abel
    rw [this]; exact norm_add_le _ _
  have e : (3 : ℝ) ^ (j + 1) = 3 * (3 : ℝ) ^ j := by ring
  rw [e]
  linarith only [h1, hy, h]

/-- **The pointwise bound near a lattice point of the fine grid** (the chain of cells, the
oscillation bounds of the boundary estimate and De Giorgi on the bottom cell). -/
theorem linfL2c_point (hd : 2 ≤ d) [NeZero d] :
    ∃ CD : ℝ, 0 < CD ∧
      ∀ {lam Lam : ℝ} {a : CoeffField d} {R : ℝ} (u0 : H1Function (euclidBall (d := d) R))
        {sL e n' N m' : ℕ} {Mg E1 K cd V3 D Y : ℝ},
        n' + 1 + N + 1 = m' → e + 2 ≤ n' + 1 → 0 < lam → lam ≤ Lam → 1 ≤ K → 0 ≤ E1 → 0 ≤ D →
        0 ≤ Y → 0 < cd → 0 ≤ V3 → 0 < R → 0 ≤ Mg →
        (∀ i : ℕ, i + e + 2 ≤ m' → ∀ x ∈ euclidBall (d := d) R,
          ∃ w ∈ gridPts d (((i + e + 2 : ℕ) : ℤ) - (sL : ℤ)) Mg, w ∈ euclidBall (d := d) R ∧
            ‖x - w‖ ≤ (3 : ℝ) ^ i) →
        (∀ j : ℕ, j ≤ m' → ∀ w ∈ euclidBall (d := d) R,
          ENNReal.ofReal (cd * ((3 : ℝ) ^ j) ^ d) ≤
            volume (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R)) →
        (3 : ℝ) ^ d ≤ K * cd →
        Real.sqrt d * ((3 : ℝ) ^ m' + (3 : ℝ) ^ m' / 2) ≤ R / 12 →
        (volume (decayEst_ann (d := d) (R / 4) R)).toReal ≤
          V3 * (cd * ((3 : ℝ) ^ (n' + 1 + N)) ^ d) →
        IsEllipticFieldOn lam Lam (euclidBall (d := d) R) a →
        (∀ (V : Set (Vec d)) (hV : IsOpen V) (hVS : V ⊆ euclidBall (d := d) R),
          V ⊆ decayEst_ann (d := d) (R / 8) R →
          IsWeakSolutionOn a V (u0.restrict hV hVS) (fun _ => 0) (fun _ => 0)) →
        (∀ (w : Vec d) (j : ℕ), LocalizedZeroTraceFunctionOn
          (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) (shiftCube w (j : ℤ)) u0.toFun) →
        (∀ j : ℕ, n' + 1 ≤ j → j < m' → ∀ w ∈ gridPts d ((j : ℤ) - (sL : ℤ)) Mg,
          w ∈ euclidBall (d := d) R →
          (∃ x ∈ decayEst_ann (d := d) (R / 3) R, ‖x - w‖ ≤ (3 : ℝ) ^ m') →
          h1_l2 (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) u0.toFun ≤
              E1 * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') * (D + Y) ∧
            (¬ shiftCube w (j : ℤ) ⊆ euclidBall (d := d) R →
              linfL2b_nl2 (shiftCube w (j : ℤ) ∩ euclidBall (d := d) R) u0.toFun ≤
                E1 * ((3 : ℝ) ^ j / (3 : ℝ) ^ m') * (D + Y))) →
        CD * (Lam / lam) ^ deGiorgiPower d * ((3 : ℝ) ^ (n' + 1) / (3 : ℝ) ^ m') ≤ 1 →
        D = h1_l2 (decayEst_ann (d := d) (R / 4) R) u0.toFun →
        Y = linfL2b_nl2 (decayEst_ann (d := d) (R / 4) R) u0.toFun →
        ∀ z ∈ gridPts d (((n' + 1 : ℕ) : ℤ) - (sL : ℤ)) Mg, z ∈ euclidBall (d := d) R →
          (∃ x ∈ decayEst_ann (d := d) (R / 3) R, ‖x - z‖ ≤ (3 : ℝ) ^ (n' + 1 - (e + 2))) →
          ∀ᵐ x ∂volume.restrict (euclidBall (d := d) R ∩ shiftCube z (n' : ℤ)),
            |u0.toFun x| ≤ Real.sqrt K * (E1 * (D + Y) * (1 / 2)) + Real.sqrt V3 * Y +
              E1 * (D + Y) := by
  obtain ⟨CD, hCD, Hcell⟩ := linfL2c_cell_bound hd
  refine ⟨CD, hCD, ?_⟩
  intro lam Lam a R u0 sL e n' N m' Mg E1 K cd V3 D Y hm' he hlam hLL hK1 hE1 hD hY hcd hV3 hR hMg
    hcovS hdens hK3 hgeo hratio hell hwS hz0 hLC hAbs hDdef hYdef z hz hzS ⟨x, hxA, hxz⟩
  have hSo : IsOpen (euclidBall (d := d) R) := isOpen_euclidBall R
  obtain ⟨zc, hzc0, hzc, hzcd⟩ := linfL2c_chain_exists (R := R) (sL := sL) (e := e) (n' := n')
    (N := N) (Mg := Mg) (fun i hi => hcovS i (by omega)) he hz hzS
  -- the sets of the chain
  have hWafin : volume (decayEst_ann (d := d) (R / 4) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono (decayEst_ann_subset _ _))
  have hu2 := u0.memL2
  have hxd : ∀ t, t ≤ N → ‖x - zc t‖ ≤ (3 : ℝ) ^ m' := by
    intro t ht
    have h1 := (hzc t ht).2.2
    have h2 : ‖x - zc t‖ ≤ ‖x - z‖ + ‖z - zc t‖ := by
      have : x - zc t = (x - z) + (z - zc t) := by abel
      rw [this]; exact norm_add_le _ _
    have h3 : (3 : ℝ) ^ (n' + 1 - (e + 2)) ≤ (3 : ℝ) ^ (m' - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (3 : ℝ) ^ (n' + 1 + t - (e + 2)) ≤ (3 : ℝ) ^ (m' - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h5 : (3 : ℝ) ^ m' = 3 * (3 : ℝ) ^ (m' - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h6 : (0 : ℝ) < (3 : ℝ) ^ (m' - 1) := by positivity
    linarith only [h1, h2, h3, h4, h5, h6, hxz]
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → Set (Vec d), ∀ t,
      T t = shiftCube (zc t) ((n' + 1 + t : ℕ) : ℤ) ∩ euclidBall (d := d) R := ⟨_, fun _ => rfl⟩
  have hTS : ∀ t, T t ⊆ euclidBall (d := d) R := fun t => by
    rw [hTdef]; exact Set.inter_subset_right
  have hTfin : ∀ t, volume (T t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top (h1_vol_ball_ne_top hR) (measure_mono (hTS t))
  have hTvol : ∀ t, t ≤ N → cd * ((3 : ℝ) ^ (n' + 1 + t)) ^ d ≤ (volume (T t)).toReal := by
    intro t ht
    have h := hdens (n' + 1 + t) (by omega) (zc t) (hzc t ht).2.1
    rw [← hTdef] at h
    have := ENNReal.toReal_mono (hTfin t) h
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hTpos : ∀ t, t ≤ N → 0 < (volume (T t)).toReal := fun t ht =>
    lt_of_lt_of_le (by positivity) (hTvol t ht)
  have hTup : ∀ t, (volume (T t)).toReal ≤ ((3 : ℝ) ^ (n' + 1 + t)) ^ d := fun t => by
    have h := ENNReal.toReal_mono (linfL2c_vol_cube_ne_top (zc t) (n' + 1 + t)
      ) (measure_mono (show T t ⊆ shiftCube (zc t) ((n' + 1 + t : ℕ) : ℤ) by
        rw [hTdef]; exact Set.inter_subset_left))
    rw [hr_shiftCube_eq, h1_volT_cube] at h
    exact h
  have hVo : IsOpen (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ euclidBall (d := d) R) :=
    (rc_isOpen_shiftCube z _).inter hSo
  have hxR : R / 3 < eucNorm x := by
    have := (linfL2c_ann_iff (a := R / 3) (b := R) (by positivity) hR).1 hxA
    exact this.1
  -- the cell is inside the annulus
  have hVA : shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ euclidBall (d := d) R ⊆
      decayEst_ann (d := d) (R / 8) R := by
    intro y hy
    have h1 : y ∈ decayEst_ann (d := d) (R / 4) R := by
      refine linfL2c_cube_in_ann (j := n' + 1) (ρ := (3 : ℝ) ^ m') hR hxR ?_ ?_ hy.1 hy.2
      · have h2 : ‖x - z‖ ≤ (3 : ℝ) ^ (n' + 1 - (e + 2)) := hxz
        exact h2.trans (pow_le_pow_right₀ (by norm_num) (by omega))
      · refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)) hgeo
        have : (3 : ℝ) ^ (n' + 1) ≤ (3 : ℝ) ^ m' := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith only [this]
    rw [linfL2c_ann_iff (by positivity) hR] at h1 ⊢
    refine ⟨?_, h1.2⟩
    linarith only [h1.1, hR]
  have hw := hwS _ hVo Set.inter_subset_right hVA
  have hEll : IsEllipticFieldOn lam Lam (shiftCube z ((n' + 1 : ℕ) : ℤ) ∩ euclidBall (d := d) R) a :=
    wh2_isEllipticFieldOn_mono hVo.measurableSet Set.inter_subset_right hell
  -- the oscillation and the norm at the chain scales
  have hxnear : ∀ t, t ≤ N → ∃ x' ∈ decayEst_ann (d := d) (R / 3) R, ‖x' - zc t‖ ≤ (3 : ℝ) ^ m' :=
    fun t ht => ⟨x, hxA, hxd t ht⟩
  have hmono : ∀ t, t < N → T t ⊆ T (t + 1) := by
    intro t ht
    rw [hTdef, hTdef]
    exact Set.inter_subset_inter_left _ (linfL2c_cube_nest (hzcd t ht))
  have hTN : linfL2b_nl2 (T N) u0.toFun ≤ Real.sqrt V3 * Y := by
    have hTNW : T N ⊆ decayEst_ann (d := d) (R / 4) R := by
      intro y hy
      rw [hTdef] at hy
      refine linfL2c_cube_in_ann (j := n' + 1 + N) (ρ := (3 : ℝ) ^ m') hR hxR (hxd N le_rfl) ?_ hy.1 hy.2
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)) hgeo
      have : (3 : ℝ) ^ (n' + 1 + N) ≤ (3 : ℝ) ^ m' := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith only [this]
    have hm := linfL2b_nl2_mono hTNW hWafin (hTpos N le_rfl)
      (hu2.mono_measure (Measure.restrict_mono (decayEst_ann_subset _ _) le_rfl))
    rw [hYdef]
    refine hm.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (linfL2b_nl2_nonneg _ _))
    rw [div_le_iff₀ (hTpos N le_rfl)]
    have := hTvol N le_rfl
    have h3 : V3 * (cd * ((3 : ℝ) ^ (n' + 1 + N)) ^ d) ≤ V3 * (volume (T N)).toReal :=
      mul_le_mul_of_nonneg_left this hV3
    linarith only [hratio, h3]
  have hnb := hLC (n' + 1) le_rfl (by omega) z hz hzS ⟨x, hxA, hxz.trans
    (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  refine Hcell hSo u0 z n' N m' hm' T hlam hLL hK1 hE1 hD hY ?_ hEll hw (fun _ => hz0 z (n' + 1))
    hmono (fun t _ => hTfin t) hTpos (fun t _ => hu2.mono_measure (Measure.restrict_mono (hTS t) le_rfl))
    (fun t ht => ?_) (fun t ht => ?_) hTN hnb.1 hnb.2 hAbs
  · rw [hTdef, hzc0]
  · -- the ratio of the volumes
    calc (volume (T (t + 1))).toReal ≤ ((3 : ℝ) ^ (n' + 1 + (t + 1))) ^ d := hTup (t + 1)
      _ = (3 : ℝ) ^ d * ((3 : ℝ) ^ (n' + 1 + t)) ^ d := by
          rw [show n' + 1 + (t + 1) = (n' + 1 + t) + 1 by ring, pow_succ, mul_pow, mul_comm]
      _ ≤ (K * cd) * ((3 : ℝ) ^ (n' + 1 + t)) ^ d :=
          mul_le_mul_of_nonneg_right hK3 (by positivity)
      _ = K * (cd * ((3 : ℝ) ^ (n' + 1 + t)) ^ d) := by ring
      _ ≤ K * (volume (T t)).toReal :=
          mul_le_mul_of_nonneg_left (hTvol t ht.le) (by linarith only [hK1])
  · -- the oscillation
    have hh := hLC (n' + 1 + (t + 1)) (by omega) (by omega) (zc (t + 1))
      (hzc (t + 1) ht).1 (hzc (t + 1) ht).2.1 (hxnear (t + 1) ht)
    rw [hTdef]
    exact hh.1

end SuperdiffusionCLT.Section8
