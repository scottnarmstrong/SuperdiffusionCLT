/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryLayer
public import SuperdiffusionCLT.Section7.Lipschitz.WitnessBdry

/-!
# A local boundary-layer measure bound

For a uniformly `C^{1,1}` open set the part of the boundary layer of thickness `t` inside a ball of
radius `R` has measure at most `(8 (R + t) / r + 2)^d C t`, with `C` proportional to `r^{d-1}`
(`ca2_volume_layer_local_le`).  Applied with the chart radius reduced to the size of the ball this
gives `|layer ∩ cube| ≤ C t (size of the cube)^{d-1}`.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

/-- The piece constant of the local layer bound. -/
noncomputable def ca2_pieceConst (n : ℕ) (r M₁ : ℝ) : ℝ :=
  ((n : ℝ) + 1) * layerSlope n M₁ * (2 * ((1 + ((n : ℝ) + 1)) * r + layerSlope n M₁ * r)) ^ n

theorem ca2_volume_layer_local_le {n : ℕ} {U : Set (Vec (n + 1))} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (hF : (frontier U).Nonempty) (z : Vec (n + 1)) {R : ℝ}
    (hR : 0 ≤ R) {t : ℝ} (ht : 0 < t) (htr : t ≤ r / 2) :
    volume (boundaryLayer U t ∩ Metric.ball z R) ≤
      ENNReal.ofReal ((8 * (R + t) / r + 2) ^ (n + 1) * (ca2_pieceConst n r M₁ * t)) := by
  classical
  have hr : 0 < r := h.2.1
  set ρ : ℝ := r / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  let cell : Vec (n + 1) → (Fin (n + 1) → ℤ) := fun x i => ⌊x i / ρ⌋
  let Kfin : Finset (Fin (n + 1) → ℤ) := Fintype.piFinset fun i =>
    Finset.Icc ⌊(z i - (R + t)) / ρ⌋ ⌊(z i + (R + t)) / ρ⌋
  let K' : Finset (Fin (n + 1) → ℤ) := Kfin.filter fun k =>
    ∃ x ∈ frontier U, ‖x - z‖ ≤ R + t ∧ cell x = k
  have hex : ∀ k : Fin (n + 1) → ℤ, (∃ x ∈ frontier U, ‖x - z‖ ≤ R + t ∧ cell x = k) →
      ∃ x, x ∈ frontier U ∧ ‖x - z‖ ≤ R + t ∧ cell x = k := fun k hk => hk
  choose! p hp using hex
  have hcover : boundaryLayer U t ∩ Metric.ball z R ⊆ ⋃ k ∈ K',
      {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
        ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4} := by
    intro y hy
    obtain ⟨x', hx', hdx⟩ := (Metric.infDist_lt_iff hF).1 hy.1.2
    have hdist : ‖x' - z‖ ≤ R + t := by
      have h1 : ‖y - z‖ < R := by
        have := hy.2; rwa [Metric.mem_ball, dist_eq_norm] at this
      have h2 : ‖y - x'‖ < t := by rwa [dist_eq_norm] at hdx
      have h3 := norm_sub_le_norm_sub_add_norm_sub x' y z
      rw [norm_sub_rev x' y] at h3
      linarith only [h1, h2, h3]
    have hxk : ∃ x ∈ frontier U, ‖x - z‖ ≤ R + t ∧ cell x = cell x' := ⟨x', hx', hdist, rfl⟩
    obtain ⟨hpF, hpd, hpc⟩ := hp (cell x') hxk
    have hmemK : cell x' ∈ K' := by
      refine Finset.mem_filter.2 ⟨?_, hxk⟩
      have hdi : ∀ i, |x' i - z i| ≤ R + t := fun i => by
        have h2 := norm_le_pi_norm (x' - z) i
        rw [Pi.sub_apply, Real.norm_eq_abs] at h2
        exact h2.trans hdist
      refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
      · show ⌊(z i - (R + t)) / ρ⌋ ≤ ⌊x' i / ρ⌋
        refine Int.floor_le_floor ?_
        exact div_le_div_of_nonneg_right (by linarith only [(abs_le.1 (hdi i)).1]) hρ0.le
      · show ⌊x' i / ρ⌋ ≤ ⌊(z i + (R + t)) / ρ⌋
        refine Int.floor_le_floor ?_
        exact div_le_div_of_nonneg_right (by linarith only [(abs_le.1 (hdi i)).2]) hρ0.le
    refine Set.mem_iUnion₂.2 ⟨cell x', hmemK, hy.1, x', hx', ?_, ?_⟩
    · rwa [dist_eq_norm] at hdx
    · rw [norm_sub_rev, ← hρ]
      refine (pi_norm_lt_iff hρ0).2 fun i => ?_
      have hi : ⌊p (cell x') i / ρ⌋ = ⌊x' i / ρ⌋ := congrFun hpc i
      rw [Pi.sub_apply, Real.norm_eq_abs]
      rw [abs_sub_comm]
      exact abs_sub_lt_of_floor_eq hρ0 hi.symm
  have hRt : 0 ≤ R + t := by linarith only [hR, ht]
  have hcard : (K'.card : ℝ) ≤ (8 * (R + t) / r + 2) ^ (n + 1) := by
    have h1 : K'.card ≤ Kfin.card := Finset.card_filter_le _ _
    have h2 : Kfin.card = ∏ i : Fin (n + 1),
        (Finset.Icc ⌊(z i - (R + t)) / ρ⌋ ⌊(z i + (R + t)) / ρ⌋).card :=
      Fintype.card_piFinset _
    have h3 : ∀ i : Fin (n + 1),
        ((Finset.Icc ⌊(z i - (R + t)) / ρ⌋ ⌊(z i + (R + t)) / ρ⌋).card : ℝ)
          ≤ 8 * (R + t) / r + 2 := by
      intro i
      rw [Int.card_Icc]
      have hpos : 0 ≤ 8 * (R + t) / r + 2 := by positivity
      rcases le_or_gt (⌊(z i + (R + t)) / ρ⌋ + 1 - ⌊(z i - (R + t)) / ρ⌋) 0 with hz | hz
      · rw [Int.toNat_of_nonpos hz]; simpa using hpos
      · have e1 : (((⌊(z i + (R + t)) / ρ⌋ + 1 - ⌊(z i - (R + t)) / ρ⌋).toNat : ℕ) : ℝ)
            = ((⌊(z i + (R + t)) / ρ⌋ + 1 - ⌊(z i - (R + t)) / ρ⌋ : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hz.le
        rw [e1]
        push_cast
        have f1 := Int.floor_le ((z i + (R + t)) / ρ)
        have f2 := Int.lt_floor_add_one ((z i - (R + t)) / ρ)
        have f3 : (z i + (R + t)) / ρ - (z i - (R + t)) / ρ = 8 * (R + t) / r := by
          rw [hρ]; field_simp; ring
        linarith only [f1, f2, f3]
    calc (K'.card : ℝ) ≤ (Kfin.card : ℝ) := by exact_mod_cast h1
      _ = ∏ i : Fin (n + 1),
          ((Finset.Icc ⌊(z i - (R + t)) / ρ⌋ ⌊(z i + (R + t)) / ρ⌋).card : ℝ) := by
          rw [h2]; push_cast; rfl
      _ ≤ ∏ _i : Fin (n + 1), (8 * (R + t) / r + 2) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => h3 i)
      _ = _ := by simp
  have hpiece : ∀ k ∈ K', volume {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
      ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4}
      ≤ ENNReal.ofReal (ca2_pieceConst n r M₁ * t) := fun k hk =>
    volume_layerPiece_le h ht htr (hp k (Finset.mem_filter.1 hk).2).1
  have hVnn : 0 ≤ ca2_pieceConst n r M₁ * t := by
    have := layerSlope_pos n M₁
    unfold ca2_pieceConst
    positivity
  calc volume (boundaryLayer U t ∩ Metric.ball z R)
      ≤ volume (⋃ k ∈ K', {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
          ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4}) := measure_mono hcover
    _ ≤ ∑ k ∈ K', volume {y : Vec (n + 1) | y ∈ boundaryLayer U t ∧
          ∃ x' ∈ frontier U, ‖y - x'‖ < t ∧ ‖x' - p k‖ < r / 4} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ K', ENNReal.ofReal (ca2_pieceConst n r M₁ * t) := Finset.sum_le_sum hpiece
    _ = ENNReal.ofReal ((K'.card : ℝ) * (ca2_pieceConst n r M₁ * t)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hVnn)

theorem ca2_uniform_mono {d : ℕ} {U : Set (Vec d)} {r r' M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (hr' : 0 < r') (hrr : r' ≤ r) :
    IsUniformC11Domain U r' M₁ M₂ D :=
  ⟨h.1, hr', h.2.2.1, fun x hx => (h.2.2.2 x hx).mono hrr le_rfl le_rfl⟩

theorem ca2_pieceConst_mul (n : ℕ) (ℓ M₁ : ℝ) :
    ca2_pieceConst n ℓ M₁ = ℓ ^ n * ca2_pieceConst n 1 M₁ := by
  unfold ca2_pieceConst
  rw [show 2 * ((1 + ((n : ℝ) + 1)) * ℓ + layerSlope n M₁ * ℓ) =
    ℓ * (2 * ((1 + ((n : ℝ) + 1)) * 1 + layerSlope n M₁ * 1)) by ring, mul_pow]
  ring

end SuperdiffusionCLT.Section7
