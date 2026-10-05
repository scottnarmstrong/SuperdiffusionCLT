/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.CubeFormDomains
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareK
public import SuperdiffusionCLT.Section7.Prereq.DomainInvariance
public import SuperdiffusionCLT.Section7.Analytic.Geometry.WhitneyBall

/-!
# The boundary domains in cube form

`Section7.g1q_cube_form`: for a smooth bounded domain `U`, a dilate `t • U`, a scale `k` with
`3^k ≤ t` and a point `z ∈ t • U`, there is a domain `V` with
`(z + □_{k-a}) ∩ t • U ⊆ V ⊆ (z + □_k) ∩ t • U` for a number `a = a(U, d)` of scales independent of
`t`, `k`, `z` (the sup-norm balls `Metric.ball z (3^j / 2)` are the cubes `z + □_j`, see
`g1q_shiftCube_eq_ball`). `V` is uniformly `C^{1,1}` after rescaling by `3^{-k}`, its frontier agrees with the
frontier of `t • U` on the smaller cube, the smaller cube has distance at least `c 3^k` from the
artificial part of the frontier, and `V` carries the mean-value Poincare inequality with the
constant `CP 3^k`.

The two cases are not distinguished by the statement. If the cube of half-width `3^{k-a₀}/2` about `z`
lies in `t • U` (`g1q_interior_case`), `V` is a rounded cube of that half-width. Otherwise some
point `q` of the frontier lies within `3^{k-a₀}/2` of `z`, and `V` is the domain of the boundary family
`a10_boundary_family_poincare` at the scale `κ 3^k` centred at `q`; the scale loss `a₀` makes the cube
`(z + □_{k-a}) ` lie in the part of that family where the domain agrees with `t • U`. The loss is
`a = a₀ + 2` with `3^{a₀} ≥ 1 / (c₀ κ)`, `κ = min (r / c₂, 1 / (|M₂| + 1), 1 / (4 c₂))`, where
`(c₀, c₁, c₂)` are the constants of the boundary family and `(r, M₁, M₂)` the uniform `C^{1,1}`
data of `U`.
-/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A ball about a point of `Ω` that is not contained in `Ω` meets the frontier of `Ω`. -/
theorem g1q_ball_inter_frontier {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {z : Vec d} (hz : z ∈ Ω)
    {ρ : ℝ} (hρ : ¬ Metric.ball z ρ ⊆ Ω) :
    ∃ q ∈ frontier Ω, q ∈ Metric.ball z ρ := by
  by_contra hno
  push Not at hno
  have hpre : IsPreconnected (Metric.ball z ρ) := (convex_ball z ρ).isPreconnected
  have hcov : Metric.ball z ρ ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro x hx
    by_cases hxc : x ∈ closure Ω
    · left
      by_contra hxΩ
      exact hno x ⟨hxc, by rw [hΩ.interior_eq]; exact hxΩ⟩ hx
    · right; exact hxc
  rcases hpre.subset_or_subset hΩ isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left subset_closure) hcov with h | h
  · exact hρ h
  · obtain ⟨x, hx, -⟩ := Set.not_subset.1 hρ
    have hρ0 : 0 < ρ := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.1 hx)
    exact h (Metric.mem_ball_self hρ0) (subset_closure hz)

theorem g1q_rad_int (k a₀ : ℕ) :
    (3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2 = ((3 : ℝ) ^ k / 3 ^ a₀ / 2) / 9 := by
  rw [pow_add]
  field_simp
  norm_num

theorem g1q_rad_mono (k : ℕ) {a₀ a : ℕ} (h : a₀ ≤ a) :
    (3 : ℝ) ^ k / 3 ^ a / 2 ≤ (3 : ℝ) ^ k / 3 ^ a₀ / 2 := by
  have h1 : (3 : ℝ) ^ a₀ ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) h
  have h2 : (0 : ℝ) < 3 ^ a₀ := by positivity
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have : (3 : ℝ) ^ k / 3 ^ a ≤ 3 ^ k / 3 ^ a₀ := div_le_div_of_nonneg_left h3.le h2 h1
  linarith only [this]

/-- The interior case of the cube form: the rounded cube of half-width `3^k / (2 · 3^{a₀})`. -/
theorem g1q_interior_case [NeZero d] {rE M₁E M₂E DE : ℝ}
    (hE : IsUniformC11Domain (g1_superE d d) rE M₁E M₂E DE) {Ω : Set (Vec d)} {z : Vec d}
    {k a₀ : ℕ} (hint : Metric.ball z ((3 : ℝ) ^ k / 3 ^ a₀ / 2) ⊆ Ω) :
    Metric.ball z ((3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2) ⊆
        g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z ∧
      g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ Ω ∧
      IsUniformC11Domain ((fun y => ((3 : ℝ) ^ k)⁻¹ • (y - z)) ''
          g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z) (1 / 3 ^ a₀ / 2 * rE) M₁E
        (M₂E / (1 / 3 ^ a₀ / 2)) (1 / 3 ^ a₀ / 2 * DE) ∧
      frontier (g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z) ∩
        Metric.ball z ((3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2) = ∅ ∧
      (∀ y ∈ Metric.ball z ((3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2),
        ∀ q ∈ frontier (g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z),
          1 / (9 * 3 ^ a₀) * (3 : ℝ) ^ k ≤ dist y q) ∧
      ∀ u : H1Function (g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z),
        eLpNorm (fun x => u.toFun x - (∫ y in g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z, u.toFun y) /
            (volume (g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z)).toReal) 2
          (volume.restrict (g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z)) ≤
        ENNReal.ofReal (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + 6 ^ d)) * (3 : ℝ) ^ k) *
          eLpNorm (fun x => ‖u.grad x‖) 2
            (volume.restrict (g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z)) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hN : 1 ≤ d := hdpos
  have hd : d ≤ 9 ^ d := (Nat.lt_pow_self (n := d) (by norm_num : 1 < 9)).le
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have h3a : (1 : ℝ) ≤ 3 ^ a₀ := one_le_pow₀ (by norm_num)
  set l : ℝ := (3 : ℝ) ^ k / 3 ^ a₀ / 2 with hl
  have hl0 : 0 < l := by positivity
  have hlk : l ≤ (3 : ℝ) ^ k / 2 := by
    rw [hl]
    have : (3 : ℝ) ^ k / 3 ^ a₀ ≤ 3 ^ k := div_le_self h3k.le h3a
    linarith only [this]
  have hrad : (3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2 = l / 9 := g1q_rad_int k a₀
  rw [hrad]
  have hV1 : Metric.ball z (l / 9) ⊆ g1q_V d d l z :=
    (Metric.ball_subset_ball (by linarith only [hl0])).trans (g1q_ball_subset hN hd hl0 z)
  refine ⟨hV1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := g1q_subset_ball hN hl0 z hx
    exact ⟨Metric.ball_subset_ball hlk this, hint this⟩
  · have := g1q_uniform hE hl0 h3k z
    have e : l / (3 : ℝ) ^ k = 1 / 3 ^ a₀ / 2 := by rw [hl]; field_simp
    rwa [e] at this
  · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hxV := hV1 hx.2
    rw [(g1q_isOpen hl0 z).frontier_eq] at hx
    exact hx.1.2 hxV
  · intro y hy q hq
    have := g1q_buffer hN hd hl0 z hy hq
    have e : 1 / (9 * 3 ^ a₀) * (3 : ℝ) ^ k = l / 3 - l / 9 := by
      rw [hl]; field_simp; ring
    linarith only [this, e]
  · intro u
    refine (g1q_poincare hN hd hl0 z u).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have : (3 : ℝ) ^ k / 3 ^ a₀ ≤ 3 ^ k := div_le_self h3k.le h3a
    linarith only [this, hl]

theorem g1q_rescale_compose (W : Set (Vec d)) {κ s c : ℝ} (hκ : κ ≠ 0) (hs : s = κ * c) (hc : c ≠ 0)
    (z q : Vec d) :
    (fun y => c⁻¹ • (y - z)) '' W =
      (fun y => κ • y + c⁻¹ • (q - z)) '' ((fun y => s⁻¹ • (y - q)) '' W) := by
  rw [Set.image_image]
  refine Set.image_congr fun y _ => ?_
  simp only [smul_smul]
  have e : κ * s⁻¹ = c⁻¹ := by rw [hs]; field_simp
  rw [e, ← smul_add]
  congr 1
  abel

theorem g1q_dist_lt {y q z : Vec d} {ρ ρ0 R : ℝ} (hy : y ∈ Metric.ball z ρ)
    (hq : q ∈ Metric.ball z ρ0) (h : ρ + ρ0 ≤ R) : y ∈ Metric.ball q R := by
  rw [Metric.mem_ball] at *
  have := dist_triangle y z q
  rw [dist_comm z q] at this
  linarith only [this, hy, hq, h]

/-- **Cube form of the uniform boundary domains** (`l.Dirichlet.uniform.boundary.domains`), for the
dilates `t • U` of a smooth bounded domain, with a fixed loss `a(U, d)` of scales. For `z ∈ t • U`
and every `k` with `3^k ≤ t` there is a domain `V` between the cubes `z + □_{k-a}` and
`z + □_k` (intersected with `t • U`), uniformly `C^{1,1}` after the rescaling by `3^{-k}`, whose
frontier agrees with that of `t • U` on the smaller cube, with a buffer of size `c 3^k` between the
smaller cube and the artificial part of the frontier, and carrying the mean-value Poincare
inequality with the constant `CP 3^k`. No assumption is made on whether the cube meets the frontier. -/
theorem g1q_cube_form [NeZero d] {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) :
    ∃ (a : ℕ) (r' M₁' M₂' D' c CP : ℝ), 0 < r' ∧ 0 < c ∧ 0 ≤ CP ∧
      ∀ (t : ℝ) (k : ℕ), 0 < t → (3 : ℝ) ^ k ≤ t → ∀ z ∈ t • U,
        ∃ V : Set (Vec d),
          Metric.ball z ((3 : ℝ) ^ k / 3 ^ a / 2) ∩ t • U ⊆ V ∧
          V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ t • U ∧
          IsUniformC11Domain ((fun y => ((3 : ℝ) ^ k)⁻¹ • (y - z)) '' V) r' M₁' M₂' D' ∧
          frontier V ∩ Metric.ball z ((3 : ℝ) ^ k / 3 ^ a / 2) ⊆ frontier (t • U) ∧
          (∀ y ∈ t • U ∩ Metric.ball z ((3 : ℝ) ^ k / 3 ^ a / 2),
            ∀ q ∈ frontier V \ frontier (t • U), c * (3 : ℝ) ^ k ≤ dist y q) ∧
          ∀ u : H1Function V,
            eLpNorm (fun x => u.toFun x - (∫ y in V, u.toFun y) / (volume V).toReal) 2
                (volume.restrict V) ≤
              ENNReal.ofReal (CP * (3 : ℝ) ^ k) *
                eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict V) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hN : 1 ≤ d := hdpos
  obtain ⟨r, M₁, M₂, D, hUu⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  obtain ⟨rE, M₁E, M₂E, DE, hE⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain
    (g1_isSmoothBoundedDomain_superE (d := d) (N := d) hN)
  obtain ⟨c₀, c₁, c₂, cb, r'b, M₁'b, M₂'b, D'b, CPb, hc0, hc01, hc12, hcb, hr'b, hCPb, hfam⟩ :=
    a10_boundary_family_poincare (d := d) M₁
  have hr : 0 < r := hUu.2.1
  have hrE : 0 < rE := hE.2.1
  have hc2 : 0 < c₂ := by linarith only [hc0, hc01, hc12]
  have hM2 : 0 < |M₂| + 1 := by positivity
  set κ : ℝ := min (min (r / c₂) (1 / (|M₂| + 1))) (1 / (4 * c₂)) with hκ
  have hκ0 : 0 < κ := lt_min (lt_min (div_pos hr hc2) (by positivity)) (by positivity)
  have hκ1 : κ ≤ r / c₂ := (min_le_left _ _).trans (min_le_left _ _)
  have hκ2 : κ ≤ 1 / (|M₂| + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hκ3 : κ ≤ 1 / (4 * c₂) := min_le_right _ _
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (c₀ * κ)) (by norm_num : (1 : ℝ) < 3)
  set a₀ : ℕ := n + 1 with ha₀
  have ha₀1 : 1 / (c₀ * κ) ≤ (3 : ℝ) ^ a₀ := by
    refine hn.le.trans ?_
    rw [ha₀]
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
  have h3a : (3 : ℝ) ≤ 3 ^ a₀ := by
    rw [ha₀]
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3a0 : (0 : ℝ) < 3 ^ a₀ := by positivity
  set lam : ℝ := 1 / 3 ^ a₀ / 2 with hlam
  have hlam0 : 0 < lam := by positivity
  refine ⟨a₀ + 2, min (lam * rE) (κ * r'b), max M₁E M₁'b, max (M₂E / lam) (M₂'b / κ),
    max (lam * DE) (κ * D'b), min (1 / (9 * 3 ^ a₀)) (cb * κ),
    max (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + 6 ^ d))) (CPb * κ),
    lt_min (by positivity) (by positivity), lt_min (by positivity) (by positivity),
    (Real.sqrt_nonneg _).trans (le_max_left _ _), ?_⟩
  intro t k ht htk z hz
  have hΩ : IsUniformC11Domain (t • U) (t * r) M₁ (M₂ / t) (t * D) := hUu.smul ht
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  by_cases hint : Metric.ball z ((3 : ℝ) ^ k / 3 ^ a₀ / 2) ⊆ t • U
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g1q_interior_case hE hint
    refine ⟨g1q_V d d ((3 : ℝ) ^ k / 3 ^ a₀ / 2) z, ?_, h2, ?_, ?_, ?_, ?_⟩
    · exact fun x hx => h1 hx.1
    · refine g1q_uniform_mono h3 (lt_min (by positivity) (by positivity)) (min_le_left _ _)
        (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
    · rw [h4]; exact Set.empty_subset _
    · intro y hy q hq
      refine le_trans ?_ (h5 y hy.2 q hq.1)
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) h3k.le
    · intro u
      refine (h6 u).trans ?_
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) h3k.le)) le_rfl
  · obtain ⟨q, hqf, hqz⟩ := g1q_ball_inter_frontier hΩ.1 hz hint
    set s : ℝ := κ * 3 ^ k with hs
    have hs0 : 0 < s := by positivity
    have hs1 : c₂ * s ≤ t * r := by
      have h1 : c₂ * κ ≤ r := by
        have := mul_le_mul_of_nonneg_left hκ1 hc2.le
        rwa [mul_div_cancel₀ _ hc2.ne'] at this
      calc c₂ * s = (c₂ * κ) * 3 ^ k := by rw [hs]; ring
        _ ≤ r * t := mul_le_mul h1 htk h3k.le hr.le
        _ = t * r := by ring
    have hs2 : M₂ / t * s ≤ 1 := by
      have h1 : (3 : ℝ) ^ k / t ≤ 1 := (div_le_one ht).2 htk
      have h2 : κ * (|M₂|) ≤ 1 := by
        calc κ * |M₂| ≤ 1 / (|M₂| + 1) * |M₂| := mul_le_mul_of_nonneg_right hκ2 (abs_nonneg M₂)
          _ ≤ 1 := by
              rw [one_div, inv_mul_le_iff₀ hM2]
              linarith only
      calc M₂ / t * s = M₂ * κ * (3 ^ k / t) := by rw [hs]; ring
        _ ≤ |M₂| * κ * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self M₂) hκ0.le) h1
              (by positivity) (by positivity)
        _ ≤ 1 := by linarith only [h2, mul_comm κ |M₂|]
    obtain ⟨W, hW1, -, hW3, hW4, hW5, hW6, hW7⟩ :=
      hfam (t • U) (t * r) (M₂ / t) (t * D) hΩ q hqf s hs0 hs1 hs2
    set ρ0 : ℝ := (3 : ℝ) ^ k / 3 ^ a₀ / 2 with hρ0
    have hin : (3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2 ≤ ρ0 := g1q_rad_mono k (Nat.le_add_right a₀ 2)
    have hbig : (3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2 + ρ0 ≤ c₀ * s := by
      have h1 : 1 / (3 : ℝ) ^ a₀ ≤ c₀ * κ := by
        rw [div_le_iff₀ h3a0]
        rw [div_le_iff₀ (by positivity)] at ha₀1
        linarith only [ha₀1]
      calc (3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2 + ρ0 ≤ ρ0 + ρ0 := by linarith only [hin]
        _ = 1 / 3 ^ a₀ * 3 ^ k := by rw [hρ0]; field_simp; ring
        _ ≤ c₀ * κ * 3 ^ k := mul_le_mul_of_nonneg_right h1 h3k.le
        _ = c₀ * s := by rw [hs]; ring
    have hc0ball : ∀ y ∈ Metric.ball z ((3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2),
        y ∈ Metric.ball q (c₀ * s) := fun y hy => g1q_dist_lt hy hqz hbig
    have hc1ball : ∀ y ∈ Metric.ball z ((3 : ℝ) ^ k / 3 ^ (a₀ + 2) / 2),
        y ∈ Metric.ball q (c₁ * s) := fun y hy =>
      Metric.ball_subset_ball (mul_le_mul_of_nonneg_right hc01.le hs0.le) (hc0ball y hy)
    refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxq : x ∈ t • U ∩ Metric.ball q (c₁ * s) := ⟨hx.2, hc1ball x hx.1⟩
      rw [hW3] at hxq
      exact hxq.1
    · intro x hx
      have h1 := hW4 hx
      refine ⟨?_, h1.1⟩
      have hzq : z ∈ Metric.ball q ρ0 := by
        rw [Metric.mem_ball, dist_comm]; exact Metric.mem_ball.1 hqz
      have := g1q_dist_lt h1.2 hzq (le_refl _)
      refine Metric.ball_subset_ball ?_ this
      have h2 : c₂ * κ ≤ 1 / 4 := by
        have := mul_le_mul_of_nonneg_left hκ3 hc2.le
        calc c₂ * κ ≤ c₂ * (1 / (4 * c₂)) := this
          _ = 1 / 4 := by field_simp
      have h3 : ρ0 ≤ 3 ^ k / 6 := by
        rw [hρ0]
        have : (3 : ℝ) ^ k / 3 ^ a₀ ≤ 3 ^ k / 3 := div_le_div_of_nonneg_left h3k.le (by norm_num) h3a
        linarith only [this]
      calc c₂ * s + ρ0 ≤ 1 / 4 * 3 ^ k + 3 ^ k / 6 := by
            have : c₂ * s = c₂ * κ * 3 ^ k := by rw [hs]; ring
            rw [this]
            have := mul_le_mul_of_nonneg_right h2 h3k.le
            linarith only [this, h3]
        _ ≤ 3 ^ k / 2 := by linarith only [h3k]
    · have hc : (3 : ℝ) ^ k ≠ 0 := h3k.ne'
      rw [g1q_rescale_compose W hκ0.ne' hs hc z q]
      refine g1q_uniform_mono (hW1.affineImage hκ0 _) (lt_min (by positivity) (by positivity))
        (min_le_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    · intro x hx
      exact hW5 ⟨hx.1, hc1ball x hx.2⟩
    · intro y hy q' hq'
      have := hW6 y ⟨hy.1, hc0ball y hy.2⟩ q' hq'
      refine le_trans ?_ this
      calc min (1 / (9 * 3 ^ a₀)) (cb * κ) * 3 ^ k ≤ cb * κ * 3 ^ k :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h3k.le
        _ = cb * s := by rw [hs]; ring
    · intro u
      refine (hW7 u).trans ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      calc CPb * s = CPb * κ * 3 ^ k := by rw [hs]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) h3k.le

/-- The open cube `z + □_j` is the sup-norm ball of radius `3^j / 2` about `z`. -/
theorem g1q_shiftCube_eq_ball (z : Vec d) (j : ℤ) :
    wpd_shiftCube z j = Metric.ball z ((3 : ℝ) ^ j / 2) := by
  ext x
  rw [wpd_mem_shiftCube, mem_ball_iff_norm, pi_norm_lt_iff (by positivity)]
  refine forall_congr' fun i => ?_
  rw [Real.norm_eq_abs]
  rfl

end SuperdiffusionCLT.Section7
