/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Regularity

/-!
# Large-scale `C^{1,γ}` regularity: scale-by-scale estimates

Flatness of `u - Φ e₀` at all scales below `m`, and the Caccioppoli bound on the gradient of
`Φ e₀` on a cube above `m`.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb8b_sqrt_le (d : ℕ) : Real.sqrt d ≤ (3 : ℝ) ^ d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    simp
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 h
  have h1 : (d : ℝ) < (3 : ℝ) ^ d := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith only [h1, hd]

theorem eb8b_entire_cube [NeZero d] {a : CoeffField d} {φ : Vec d → ℝ} {gφ : Vec d → Vec d}
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (h : IsEntireSolution a φ gφ) (n : ℕ) : IsSolOn a (engCube d n) φ gφ := by
  have hs : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
  have hR : 0 < Real.sqrt d * (3 : ℝ) ^ n := by positivity
  exact IsSolOn.cube_of_ball (hell n) (by linarith only [hR]) (h _ hR)

theorem eb8b_s_iter {s : ℕ → ℝ} {mstar : ℕ}
    (hs : ∀ j : ℕ, mstar ≤ j → 0 < s j ∧ s (j + 1) ≤ 2 * s j) {m : ℕ} (hm : mstar ≤ m)
    (t : ℕ) : s (m + t) ≤ 2 ^ t * s m := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := (hs (m + t) (by omega)).2
    calc s (m + (t + 1)) = s (m + t + 1) := rfl
      _ ≤ 2 * s (m + t) := h
      _ ≤ 2 * (2 ^ t * s m) := by gcongr
      _ = 2 ^ (t + 1) * s m := by ring

theorem eb8b_flat_u [NeZero d] {Cf Cl η κ : ℝ} (hCf : 1 ≤ Cf) (hCl : 1 ≤ Cl) (hκ : 0 ≤ κ)
    {a : CoeffField d} {δ : ℕ → ℝ} {mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {GΦ : Vec d → Vec d → Vec d}
    (hδ1 : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ 1)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hfirst : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ e : Vec d,
      ∃ q : Vec d, affSlope k (V k q) = affSlope k (V m e))
    (hfin : ∀ m k0 : ℕ, mstar ≤ k0 → k0 ≤ m →
      ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
        ∃ e : Vec d, engNorm e ≤ Cf * cubeFlat m w ∧
          ∀ k : ℕ, k0 ≤ k → k ≤ m →
            cubeFlat k (fun x => w x - V m e x) ≤
              Cf * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w)
    (hΦsol : ∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0))
    (hΦlim : ∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
      ∀ k : ℕ, mstar ≤ k → k ≤ m →
        cubeFlat k (fun x => Φ e0 x - V m e x) ≤
          Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e)
    {m : ℕ} (hm : mstar ≤ m) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : IsSolOn a (engCube d m) u g) :
    ∃ e0 e : Vec d, engNorm e ≤ Cf * cubeFlat m u ∧
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) ∧
      ∀ k : ℕ, mstar ≤ k → k ≤ m →
        cubeFlat k (fun x => u x - Φ e0 x) ≤
          (Cf + Cl * Cf) * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m u := by
  obtain ⟨e, hen, hef⟩ := hfin m mstar le_rfl hm u ⟨g, hu⟩
  obtain ⟨e0, he0⟩ := hfirst m mstar le_rfl hm e
  refine ⟨e0, e, hen, he0.symm, fun k hk hkm => ?_⟩
  have h2 := hΦlim e0 m e hm he0.symm k hk hkm
  have hδm := hδ1 m hm
  refine eb8b_flat_close (eb5a_memLp hell hkm hu) ?_ ?_ hCf hCl hδm.1 hδm.2
    (cubeFlat_nonneg _ _) (by simpa only [sub_nonneg] using Nat.cast_le.2 hkm) hκ
    (hef k hk hkm) h2 hen
  · exact eb5a_memLp hell hkm (hVsol m hm e).choose_spec
  · exact (eb8b_entire_cube hell (hΦsol e0) k).memLp.1

theorem eb8b_phi_grad [NeZero d] {Cin Cz Cl η κ : ℝ} (hCin : 1 ≤ Cin) (hCz : 1 ≤ Cz)
    (hCl : 1 ≤ Cl) {a : CoeffField d} {δ s : ℕ → ℝ} {mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} {Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {GΦ : Vec d → Vec d → Vec d}
    (hδ1 : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ 1)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hVtop : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d, cubeFlat j (V j e) ≤ Cin * engNorm e)
    (hHC : ∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      IsSolOn a (engCube d k) u g →
        cubeGradL2 (k - 2) g ≤ Cin * Real.sqrt (s k) * cubeFlat k u)
    (hfirst : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ e : Vec d,
      ∃ q : Vec d, affSlope k (V k q) = affSlope k (V m e))
    (hsurj : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ q : Vec d,
      ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q))
    (hcons : ∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
      affSlope n (V (m + 1) e') = affSlope n (V m e) →
      engNorm (e' - e) ≤ Cz * δ m * engNorm e)
    (hΦsol : ∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0))
    (hΦlim : ∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
      affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
      ∀ k : ℕ, mstar ≤ k → k ≤ m →
        cubeFlat k (fun x => Φ e0 x - V m e x) ≤
          Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e)
    {m : ℕ} (hm : mstar ≤ m) (t : ℕ) {e0 e : Vec d}
    (he : affSlope mstar (V m e) = affSlope mstar (V mstar e0)) :
    cubeGradL2 (m + t) (GΦ e0) ≤
      Cin * Real.sqrt (s (m + t + 2)) * ((Cin + Cl) * (1 + Cz) ^ (t + 2) * engNorm e) := by
  obtain ⟨e', hs', hn'⟩ := eb8b_iter (c9 := 1) (by linarith only [hCz]) zero_le_one hδ1 hfirst
    hsurj hcons (t + 2) m hm e
  have hM : m + (t + 2) = m + t + 2 := by omega
  rw [hM] at hs'
  have hMm : mstar ≤ m + t + 2 := by omega
  have h1 := hΦlim e0 (m + t + 2) e' hMm (hs'.trans he) (m + t + 2) hMm le_rfl
  simp only [sub_self, mul_zero, neg_zero, Real.rpow_zero, mul_one] at h1
  have h2 := hVtop (m + t + 2) hMm e'
  have hφM := (eb8b_entire_cube hell (hΦsol e0) (m + t + 2))
  have hVM : MemLp (V (m + t + 2) e') 2
      (normalizedCubeMeasure (originCube d ((m + t + 2 : ℕ) : ℤ))) :=
    (hVsol (m + t + 2) hMm e').choose_spec.memLp.1
  have hsum := cubeFlat_add_le (hφM.memLp.1.sub hVM) hVM
  have hfun : (fun x => (Φ e0 x - V (m + t + 2) e' x) + V (m + t + 2) e' x) = Φ e0 := by
    funext x
    ring
  simp only [Pi.sub_apply, hfun] at hsum
  have hsum' : cubeFlat (m + t + 2) (Φ e0) ≤
      cubeFlat (m + t + 2) (fun x => Φ e0 x - V (m + t + 2) e' x) +
        cubeFlat (m + t + 2) (V (m + t + 2) e') := hsum
  have hδM := hδ1 (m + t + 2) hMm
  have hn0 := engNorm_nonneg e'
  have hflat : cubeFlat (m + t + 2) (Φ e0) ≤ (Cin + Cl) * engNorm e' := by
    have h3 : Cl * δ (m + t + 2) * engNorm e' ≤ Cl * engNorm e' := by
      have : Cl * δ (m + t + 2) ≤ Cl * 1 := mul_le_mul_of_nonneg_left hδM.2 (by linarith only [hCl])
      nlinarith only [this, hn0]
    linarith only [hsum', h1, h2, h3]
  have hHCM := hHC (m + t + 2) hMm (Φ e0) (GΦ e0) hφM
  have hsub : m + t + 2 - 2 = m + t := by omega
  rw [hsub] at hHCM
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hsq := Real.sqrt_nonneg (s (m + t + 2))
  have hn'' : engNorm e' ≤ (1 + Cz) ^ (t + 2) * engNorm e := by
    simpa only [mul_one] using hn'
  calc cubeGradL2 (m + t) (GΦ e0)
      ≤ Cin * Real.sqrt (s (m + t + 2)) * cubeFlat (m + t + 2) (Φ e0) := hHCM
    _ ≤ Cin * Real.sqrt (s (m + t + 2)) * ((Cin + Cl) * engNorm e') := by gcongr
    _ ≤ Cin * Real.sqrt (s (m + t + 2)) * ((Cin + Cl) * ((1 + Cz) ^ (t + 2) * engNorm e)) := by
        gcongr
    _ = _ := by ring

theorem eb8b_grad_aesm [NeZero d] {a : CoeffField d} {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : IsBallSolution a R u g) :
    AEStronglyMeasurable g (ballMeasure r) := by
  obtain ⟨v, -, hv2⟩ := h
  have hvec : MemLp v.toH1.grad 2 (volume.restrict (euclidBall R)) :=
    MeasureTheory.MemLp.of_eval fun i => v.toH1.gradMemL2 i
  have h1 : AEStronglyMeasurable g (volume.restrict (euclidBall R)) :=
    hvec.aestronglyMeasurable.congr hv2
  have h2 : AEStronglyMeasurable g (volume.restrict (euclidBall (d := d) r)) :=
    h1.mono_measure (Measure.restrict_mono (euclidBall_mono hr.le hrR) le_rfl)
  unfold ballMeasure ProbabilityTheory.cond
  exact h2.smul_measure _

theorem eb8b_ballGrad_sub {r : ℝ} {F G : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (ballMeasure r)) (hG : AEStronglyMeasurable G (ballMeasure r)) :
    ballGradL2 r (fun x => F x - G x) ≤ ballGradL2 r F + ballGradL2 r G := by
  have hcont : Continuous (fun e : Vec d => engNorm e) :=
    Real.continuous_sqrt.comp continuous_vecNormSq
  have hm : AEStronglyMeasurable (fun x => engNorm (F x - G x)) (ballMeasure r) :=
    hcont.comp_aestronglyMeasurable (hF.sub hG)
  unfold ballGradL2
  refine le_trans (eLpNorm_mono (g := fun x => engNorm (F x) + engNorm (G x)) hm ?_) ?_
  · intro x
    show ‖engNorm (F x - G x)‖ ≤ ‖engNorm (F x) + engNorm (G x)‖
    rw [Real.norm_of_nonneg (engNorm_nonneg _),
      Real.norm_of_nonneg (add_nonneg (engNorm_nonneg _) (engNorm_nonneg _))]
    exact eb5a_engNorm_sub_le (F x) (G x)
  · exact eLpNorm_add_le (f := fun x => engNorm (F x)) (g := fun x => engNorm (G x)) one_le_two

theorem eb8b_small_final {Cd1 Cd2 C2 Λ E X Y Gh qγ : ℝ} {A B : ℝ≥0∞}
    (hB : B = ENNReal.ofReal Y) (hY : 0 ≤ Y) (hCd1 : 0 ≤ Cd1) (hCd2 : 0 ≤ Cd2) (hC2 : 0 ≤ C2)
    (hΛ : 0 ≤ Λ) (hq : 0 ≤ qγ) (hE0 : 0 ≤ E) (hX : X ≤ Cd2 * Y) (hGh : Gh ≤ C2 * E * X)
    (hE : E ≤ Λ * qγ) (hA : A ≤ ENNReal.ofReal (Cd1 * Gh)) :
    A ≤ ENNReal.ofReal (Cd1 * C2 * Cd2 * Λ * qγ) * B := by
  rw [hB, ← ENNReal.ofReal_mul (by positivity)]
  refine hA.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : C2 * E * X ≤ C2 * E * (Cd2 * Y) := mul_le_mul_of_nonneg_left hX (by positivity)
  have h2 : C2 * E * (Cd2 * Y) ≤ C2 * (Λ * qγ) * (Cd2 * Y) := by gcongr
  calc Cd1 * Gh ≤ Cd1 * (C2 * (Λ * qγ) * (Cd2 * Y)) :=
        mul_le_mul_of_nonneg_left (hGh.trans (h1.trans h2)) hCd1
    _ = _ := by ring

/-- **E-B8b (large-scale `C^{1,γ}`)**, Step 8, second half. The radius threshold is
`3^{mstar + C0}`. -/
theorem eng_regularity (d : ℕ) [NeZero d] (Cin Cc Cf Cz Cl Cs : ℝ) (hCin : 1 ≤ Cin)
    (hCc : 1 ≤ Cc) (hCf : 1 ≤ Cf) (hCz : 1 ≤ Cz) (hCl : 1 ≤ Cl) (hCs : 1 ≤ Cs) :
    ∃ (C c9 : ℝ) (C0 : ℕ), 1 ≤ C ∧ 0 < c9 ∧
      ∀ η κ γ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 / 24 → 0 < γ → γ + 7 * κ ≤ η →
        ∀ (a : CoeffField d) (δ s : ℕ → ℝ) (mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ))
          (Φ : Vec d →ₗ[ℝ] (Vec d → ℝ)) (GΦ : Vec d → Vec d → Vec d),
          3 ≤ mstar →
          (∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ c9) →
          GrowthElliptic a →
          -- hell
          (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
          -- hs
          (∀ k m : ℕ, mstar ≤ k → k ≤ m →
            0 < s m ∧ s (m + 1) ≤ 2 * s m ∧
              s k ≤ Cs * (9 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * s m) →
          -- hVsol
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
          -- hVtop
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d, cubeFlat j (V j e) ≤ Cin * engNorm e) →
          -- hHC (Caccioppoli, two scales down)
          (∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
            IsSolOn a (engCube d k) u g →
              cubeGradL2 (k - 2) g ≤ Cin * Real.sqrt (s k) * cubeFlat k u) →
          -- hHP (Poincaré)
          (∀ k : ℕ, mstar ≤ k → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
            IsSolOn a (engCube d k) u g →
              Real.sqrt (s k) * cubeFlat k u ≤ Cin * cubeGradL2 k g) →
          -- hchain Cc κ
          (∀ m k : ℕ, mstar ≤ k → k ≤ m →
            (∀ e : Vec d, ∃ q : Vec d,
              affSlope k (V k q) = affSlope k (V m e) ∧
                cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
                engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
                engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
              ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q)) →
          -- hfin Cf (η - 3κ)
          (∀ m k0 : ℕ, mstar ≤ k0 → k0 ≤ m →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) →
              ∃ e : Vec d, engNorm e ≤ Cf * cubeFlat m w ∧
                ∀ k : ℕ, k0 ≤ k → k ≤ m →
                  cubeFlat k (fun x => w x - V m e x) ≤
                    Cf * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) →
          -- hcons Cz (slope part)
          (∀ n m : ℕ, mstar ≤ n → n ≤ m → ∀ e e' : Vec d,
            affSlope n (V (m + 1) e') = affSlope n (V m e) →
            engNorm (e' - e) ≤ Cz * δ m * engNorm e) →
          -- hΦsol
          (∀ e0 : Vec d, IsEntireSolution a (Φ e0) (GΦ e0)) →
          -- hΦlim Cl (η - 6κ), anchored at `n = mstar`
          (∀ (e0 : Vec d) (m : ℕ) (e : Vec d), mstar ≤ m →
            affSlope mstar (V m e) = affSlope mstar (V mstar e0) →
            ∀ k : ℕ, mstar ≤ k → k ≤ m →
              cubeFlat k (fun x => Φ e0 x - V m e x) ≤
                Cl * δ m * (3 : ℝ) ^ (-((η - 6 * κ) * ((m : ℝ) - (k : ℝ)))) * engNorm e) →
          -- hΦmem (second conclusion of `eng_liouville`, with `c = 0`)
          (∀ e0 : Vec d, ∃ hm : AEStronglyMeasurable (fun x => (0 : ℝ) + Φ e0 x) volume,
            AEEqFun.mk (fun x => (0 : ℝ) + Φ e0 x) hm ∈ growthSpace a γ) →
          -- conclusion
          ∀ R : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ R →
            ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsBallSolution a R u g →
              ∃ φ ∈ growthSpace a γ, ∃ gφ : Vec d → Vec d,
                IsEntireSolution a φ gφ ∧
                  ∀ r : ℝ, (3 : ℝ) ^ (mstar + C0) ≤ r → r < R →
                    ballGradL2 r (fun x => g x - gφ x) ≤
                      ENNReal.ofReal (C * (r / R) ^ γ) * ballGradL2 R g := by
  have _ := hCc
  obtain ⟨Cd1, hCd1, hball_cube⟩ := ballGradL2_le_cubeGradL2 d
  obtain ⟨Cd2, hCd2, hcube_ball⟩ := cubeGradL2_le_ballGradL2 d
  have hdR : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hs1 : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hdR
  have hspos : 0 < Real.sqrt d := by linarith only [hs1]
  set Λ : ℝ := (3 : ℝ) ^ (d + 4) with hΛdef
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by norm_num)
  set Cb : ℝ := (Real.sqrt d * Λ) ^ d with hCbdef
  have hCb1 : 1 ≤ Cb := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hs1 hΛ1)
  set C2 : ℝ := Cin * Cin * Real.sqrt Cs * (Cf + Cl * Cf) with hC2def
  set Cφ : ℝ := Cin * Real.sqrt ((2 : ℝ) ^ (d + 3)) * ((Cin + Cl) * (1 + Cz) ^ (d + 3)) * Cf * Cin
    with hCφdef
  set Csm : ℝ := Cd1 * C2 * Cd2 * (81 * Real.sqrt d) with hCsmdef
  set Clg : ℝ := Cb + Cb * (Cd1 * Cφ * Cd2) with hClgdef
  have hCs0 : 0 ≤ Real.sqrt Cs := Real.sqrt_nonneg _
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCf0 : 0 ≤ Cf := by linarith only [hCf]
  have hCl0 : 0 ≤ Cl := by linarith only [hCl]
  have hCd1' : 0 ≤ Cd1 := by linarith only [hCd1]
  have hCd2' : 0 ≤ Cd2 := by linarith only [hCd2]
  have hCb0 : 0 ≤ Cb := by linarith only [hCb1]
  have hKpos : 0 ≤ (Cin + Cl) * (1 + Cz) ^ (d + 3) :=
    mul_nonneg (add_nonneg hCin0 hCl0) (pow_nonneg (by linarith only [hCz]) _)
  have hC20 : 0 ≤ C2 := by
    rw [hC2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCin0 hCin0) hCs0)
      (add_nonneg hCf0 (mul_nonneg hCl0 hCf0))
  have hCφ0 : 0 ≤ Cφ := by
    rw [hCφdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCin0 (Real.sqrt_nonneg _)) hKpos)
      hCf0) hCin0
  have h81 : 0 ≤ 81 * Real.sqrt d := mul_nonneg (by norm_num) hspos.le
  have hCsm0 : 0 ≤ Csm := by
    rw [hCsmdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCd1' hC20) hCd2') h81
  have hClg0 : 0 ≤ Clg := by
    rw [hClgdef]
    exact add_nonneg hCb0 (mul_nonneg hCb0 (mul_nonneg (mul_nonneg hCd1' hCφ0) hCd2'))
  refine ⟨1 + Csm + 81 * Real.sqrt d * Clg, 1, d + 4, ?_, one_pos, ?_⟩
  · have : 0 ≤ 81 * Real.sqrt d * Clg := mul_nonneg h81 hClg0
    linarith only [hCsm0, this]
  intro η κ γ hη1 hη2 hκ hκ' hγ hγη a δ s mstar V Φ GΦ hms hδ hGE hell hs hVsol hVtop hHC hHP
    hchain hfin hcons hΦsol hΦlim hΦmem R hR u g hu
  have hδ1 : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j ≤ 1 := hδ
  have hfirst : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ e : Vec d,
      ∃ q : Vec d, affSlope k (V k q) = affSlope k (V m e) := by
    intro m k hk hkm e
    obtain ⟨q, hq, -⟩ := (hchain m k hk hkm).1 e
    exact ⟨q, hq⟩
  have hsurj : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ q : Vec d,
      ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q) :=
    fun m k hk hkm => (hchain m k hk hkm).2
  -- the scale `m`
  have hR3 : (3 : ℝ) ^ (mstar + (d + 4)) = 81 * (3 : ℝ) ^ (mstar + d) := by
    rw [show mstar + (d + 4) = (mstar + d) + 4 by ring, pow_add]
    norm_num
    ring
  have hsd : Real.sqrt d ≤ (3 : ℝ) ^ d := eb8b_sqrt_le d
  have h3d : (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (mstar + d) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hRpos : 0 < R := by
    have : (0 : ℝ) < (3 : ℝ) ^ (mstar + (d + 4)) := pow_pos three_pos _
    linarith only [this, hR]
  have hsd2 : Real.sqrt d ≤ 2 * R := by
    have : (0 : ℝ) < (3 : ℝ) ^ (mstar + d) := pow_pos three_pos _
    linarith only [hsd, h3d, hR, hR3, this]
  obtain ⟨m, hm1, hm2⟩ := eb8b_exists_m d hsd2
  have hm3 : mstar + 3 ≤ m := by
    by_contra hcon
    have hle : (3 : ℝ) ^ (m + 1) ≤ (3 : ℝ) ^ (mstar + 3) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : Real.sqrt d * (3 : ℝ) ^ (m + 1) ≤ (3 : ℝ) ^ d * (3 : ℝ) ^ (mstar + 3) :=
      mul_le_mul hsd hle (pow_pos three_pos _).le (pow_pos three_pos _).le
    have h2 : (3 : ℝ) ^ d * (3 : ℝ) ^ (mstar + 3) = 27 * (3 : ℝ) ^ (mstar + d) := by
      rw [show mstar + 3 = mstar + 3 from rfl, pow_add, pow_add]
      norm_num
      ring
    have : (0 : ℝ) < (3 : ℝ) ^ (mstar + d) := pow_pos three_pos _
    linarith only [hm2, h1, h2, hR, hR3, this]
  have hmm : mstar ≤ m := by omega
  have hm3' : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by rw [pow_succ]; ring
  have hm0 : (0 : ℝ) < (3 : ℝ) ^ m := pow_pos three_pos _
  have hmR1 : 2 * R < 3 * Real.sqrt d * (3 : ℝ) ^ m := by
    rw [hm3'] at hm2
    linarith only [hm2]
  have hsd_d : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (Nat.cast_nonneg d)]
    nlinarith only [hdR]
  have hRle : R ≤ (d : ℝ) * (3 : ℝ) ^ (m + 2) := by
    have h9 : (3 : ℝ) ^ (m + 2) = 9 * (3 : ℝ) ^ m := by rw [pow_add]; ring
    rw [h9]
    nlinarith only [hmR1, hsd_d, hm0, hdR]
  have hu' : IsSolOn a (engCube d m) u g := IsSolOn.cube_of_ball (hell m) hm1 hu
  obtain ⟨e0, e, hen, hslope, hflat⟩ :=
    eb8b_flat_u hCf hCl hκ.le hδ1 hell hVsol hfirst hfin hΦsol hΦlim hmm hu'
  have hHPm := hHP m hmm u g hu'
  have hsm : 0 < s m := (hs m m hmm le_rfl).1
  have hBfin : ballGradL2 R g ≠ ⊤ := (eb8b_gradMemLp_ball hRpos hu).eLpNorm_ne_top
  have hB : ballGradL2 R g = ENNReal.ofReal (ballGradL2 R g).toReal :=
    (ENNReal.ofReal_toReal hBfin).symm
  have hY0 : 0 ≤ (ballGradL2 R g).toReal := ENNReal.toReal_nonneg
  have hXY : cubeGradL2 m g ≤ Cd2 * (ballGradL2 R g).toReal :=
    hcube_ball R m hm1 hRle g (eb8b_gradMemLp_ball hRpos hu)
  obtain ⟨hmeas, hmemφ⟩ := hΦmem e0
  refine ⟨AEEqFun.mk (fun x => (0 : ℝ) + Φ e0 x) hmeas, hmemφ, GΦ e0, ?_, ?_⟩
  · apply eb8b_entire_congr (hΦsol e0)
    filter_upwards [AEEqFun.coeFn_mk (fun x => (0 : ℝ) + Φ e0 x) hmeas] with x hx
    rw [hx]
    simp
  intro r hr1 hrR
  have hr3 : (1 : ℝ) ≤ (3 : ℝ) ^ (mstar + (d + 4)) := one_le_pow₀ (by norm_num)
  have hr0 : 0 < r := by linarith only [hr3, hr1]
  have hq0 : 0 < r / R := div_pos hr0 hRpos
  have hq1 : r / R ≤ 1 := by rw [div_le_one hRpos]; exact hrR.le
  have hγ1 : γ ≤ 1 := by linarith only [hγη, hη2, hκ]
  have hqγ : 0 ≤ (r / R) ^ γ := Real.rpow_nonneg hq0.le _
  rcases le_or_gt (54 * r) ((3 : ℝ) ^ m) with hsmall | hlarge
  · -- small radius: Caccioppoli on a cube two scales below the flatness scale
    have hr1' : (1 : ℝ) ≤ 2 * r := by linarith only [hr3, hr1]
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hr1' (by norm_num : (1 : ℝ) < 3)
    have hnm : n + 3 ≤ m := by
      by_contra hcon
      have h1 : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h9 : (3 : ℝ) ^ (n + 2) = 9 * (3 : ℝ) ^ n := by rw [pow_add]; ring
      linarith only [h1, h9, hn1, hsmall, hr0]
    have hmn : mstar ≤ n + 3 := by
      by_contra hcon
      have h1 : (3 : ℝ) ^ (n + 1) ≤ (3 : ℝ) ^ (mstar + (d + 4)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith only [h1, hn2, hr1, hr0]
    obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = n + 3 := ⟨_, rfl⟩
    have hkm : k ≤ m := by omega
    have hk : mstar ≤ k := by omega
    have hk2 : k - 2 = n + 1 := by omega
    have hΦk := eb8b_entire_cube hell (hΦsol e0) k
    have hwk : IsSolOn a (engCube d k) (fun x => u x - Φ e0 x) (fun x => g x - GΦ e0 x) :=
      IsSolOn.sub (hell k) (eb5a_sol_restrict hell hkm hu') hΦk
    have hHCk := hHC k hk _ _ hwk
    have hs' := (hs k m hk hkm).2.2
    have hfk := hflat k hk hkm
    have hcomb := eb8b_combine (A := Cf + Cl * Cf) hCin hCs
      (add_nonneg hCf0 (mul_nonneg hCl0 hCf0)) hsm
      (cubeFlat_nonneg _ _) hHCk hfk hHPm hs'
    rw [hk2] at hcomb
    have hmemG : MemLp (fun x => engNorm (g x - GΦ e0 x)) 2
        (normalizedCubeMeasure (originCube d ((n + 1 : ℕ) : ℤ))) :=
      (eb5a_sol_restrict hell (by omega : n + 1 ≤ k) hwk).memLp.2
    have hn3 : (3 : ℝ) ^ (n + 1) ≤ 54 * r := by
      have : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by rw [pow_succ]; ring
      linarith only [this, hn1, hr0]
    have hball := hball_cube r (n + 1) hr0 hn2.le hn3 _ hmemG
    -- the exponent
    have hpow : (3 : ℝ) ^ (-((m : ℝ) - (k : ℝ))) = (3 : ℝ) ^ k / (3 : ℝ) ^ m := by
      rw [neg_sub, Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    have hk3 : (3 : ℝ) ^ k ≤ 54 * r := by
      have : (3 : ℝ) ^ k = 27 * (3 : ℝ) ^ n := by rw [hkdef, pow_add]; norm_num; ring
      linarith only [this, hn1, hr0]
    have hqx : (3 : ℝ) ^ (-((m : ℝ) - (k : ℝ))) ≤ (81 * Real.sqrt d) * (r / R) := by
      rw [hpow, div_le_iff₀ hm0, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hRpos]
      have h1 : (3 : ℝ) ^ k * R ≤ 54 * r * (3 / 2 * Real.sqrt d * (3 : ℝ) ^ m) := by
        have hR' : R ≤ 3 / 2 * Real.sqrt d * (3 : ℝ) ^ m := by linarith only [hmR1]
        calc (3 : ℝ) ^ k * R ≤ 54 * r * R := mul_le_mul_of_nonneg_right hk3 hRpos.le
          _ ≤ _ := mul_le_mul_of_nonneg_left hR' (mul_nonneg (by norm_num) hr0.le)
      nlinarith only [h1]
    have hE := eb8b_exp hη2 hκ hγ hγη hq0 hq1 (Λ := 81 * Real.sqrt d)
      (by linarith only [hs1]) hqx
    have hfin := eb8b_small_final (A := ballGradL2 r (fun x => g x - GΦ e0 x))
      (B := ballGradL2 R g) hB hY0 hCd1' hCd2' hC20 h81 hqγ
      (Real.rpow_nonneg (by norm_num) _) hXY hcomb hE hball
    have hle : Cd1 * C2 * Cd2 * (81 * Real.sqrt d) ≤ 1 + Csm + 81 * Real.sqrt d * Clg := by
      have : 0 ≤ 81 * Real.sqrt d * Clg := mul_nonneg h81 hClg0
      have e1 : Cd1 * C2 * Cd2 * (81 * Real.sqrt d) = Csm := hCsmdef.symm
      linarith only [e1, this]
    exact hfin.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle hqγ)) zero_le)
  · -- large radius: compare with a ball and a cube above the flatness scale
    set ρ : ℝ := (3 : ℝ) ^ (m + d + 1) / 2 with hρdef
    have hρpos : 0 < ρ := div_pos (pow_pos three_pos _) two_pos
    have hρ' : ρ = 3 / 2 * (3 : ℝ) ^ d * (3 : ℝ) ^ m := by
      rw [hρdef, pow_succ, pow_add]
      ring
    have hΛ81 : Λ = 81 * (3 : ℝ) ^ d := by
      rw [hΛdef, pow_add]
      norm_num
      ring
    have h3d0 : (0 : ℝ) < (3 : ℝ) ^ d := pow_pos three_pos _
    have hRρ : R ≤ ρ := by
      have h1 : R ≤ 3 / 2 * Real.sqrt d * (3 : ℝ) ^ m := by linarith only [hmR1]
      have h2 : Real.sqrt d * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ d * (3 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hsd hm0.le
      rw [hρ']
      linarith only [h1, h2]
    have hρΛ : ρ ≤ Λ * r := by
      rw [hρ', hΛ81]
      calc 3 / 2 * (3 : ℝ) ^ d * (3 : ℝ) ^ m ≤ 3 / 2 * (3 : ℝ) ^ d * (54 * r) :=
            mul_le_mul_of_nonneg_left hlarge.le (mul_nonneg (by norm_num) h3d0.le)
        _ = _ := by ring
    have hrR' : r ≤ R := hrR.le
    have hrρ : r ≤ ρ := hrR'.trans hRρ
    have hRΛ : R ≤ Λ * r := hRρ.trans hρΛ
    have hg1 : ballGradL2 r g ≤ ENNReal.ofReal Cb * ballGradL2 R g :=
      eb8b_ball_mono d hΛ1 hr0 hrR' hRΛ (eb8b_gradMemLp_ball hRpos hu).aestronglyMeasurable
    have hΦρ := hΦsol e0 ρ hρpos
    have hG1 : ballGradL2 r (GΦ e0) ≤ ENNReal.ofReal Cb * ballGradL2 ρ (GΦ e0) :=
      eb8b_ball_mono d hΛ1 hr0 hrρ hρΛ (eb8b_gradMemLp_ball hρpos hΦρ).aestronglyMeasurable
    have h2ρ : 2 * ρ ≤ (3 : ℝ) ^ (m + d + 1) := by linarith only [hρdef]
    have h54ρ : (3 : ℝ) ^ (m + d + 1) ≤ 54 * ρ := by
      have : (0 : ℝ) < (3 : ℝ) ^ (m + d + 1) := pow_pos three_pos _
      linarith only [this, hρdef]
    have hG2 : ballGradL2 ρ (GΦ e0) ≤ ENNReal.ofReal (Cd1 * cubeGradL2 (m + d + 1) (GΦ e0)) :=
      hball_cube ρ (m + d + 1) hρpos h2ρ h54ρ (GΦ e0)
        (eb8b_entire_cube hell (hΦsol e0) (m + d + 1)).memLp.2
    have hG3 := eb8b_phi_grad hCin hCz hCl hδ1 hell hVsol hVtop hHC hfirst hsurj hcons hΦsol
      hΦlim hmm (d + 1) hslope
    have e3 : d + 1 + 2 = d + 3 := rfl
    rw [e3] at hG3
    have hsi : s (m + (d + 1) + 2) ≤ 2 ^ (d + 3) * s m :=
      eb8b_s_iter (fun j hj => ⟨(hs j j hj le_rfl).1, (hs j j hj le_rfl).2.1⟩) hmm (d + 3)
    have hsq : Real.sqrt (s (m + (d + 1) + 2)) ≤ Real.sqrt ((2 : ℝ) ^ (d + 3)) * Real.sqrt (s m) := by
      refine (Real.sqrt_le_sqrt hsi).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (pow_nonneg zero_le_two _)]
    have hΩ0 := cubeFlat_nonneg m u
    have hG4 : cubeGradL2 (m + d + 1) (GΦ e0) ≤ Cφ * cubeGradL2 m g := by
      have hKe : 0 ≤ (Cin + Cl) * (1 + Cz) ^ (d + 3) * engNorm e :=
        mul_nonneg hKpos (engNorm_nonneg e)
      calc cubeGradL2 (m + d + 1) (GΦ e0)
          ≤ Cin * Real.sqrt (s (m + (d + 1) + 2)) *
              ((Cin + Cl) * (1 + Cz) ^ (d + 3) * engNorm e) := hG3
        _ ≤ Cin * (Real.sqrt ((2 : ℝ) ^ (d + 3)) * Real.sqrt (s m)) *
              ((Cin + Cl) * (1 + Cz) ^ (d + 3) * (Cf * cubeFlat m u)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq hCin0)
            (mul_le_mul_of_nonneg_left hen hKpos) hKe
            (mul_nonneg hCin0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
        _ = (Cin * Real.sqrt ((2 : ℝ) ^ (d + 3)) * ((Cin + Cl) * (1 + Cz) ^ (d + 3)) * Cf) *
              (Real.sqrt (s m) * cubeFlat m u) := by ring
        _ ≤ (Cin * Real.sqrt ((2 : ℝ) ^ (d + 3)) * ((Cin + Cl) * (1 + Cz) ^ (d + 3)) * Cf) *
              (Cin * cubeGradL2 m g) :=
          mul_le_mul_of_nonneg_left hHPm (mul_nonneg (mul_nonneg (mul_nonneg
            hCin0 (Real.sqrt_nonneg _)) hKpos) hCf0)
        _ = Cφ * cubeGradL2 m g := by rw [hCφdef]; ring
    have hsub := eb8b_ballGrad_sub (eb8b_grad_aesm hr0 hrR' hu) (eb8b_grad_aesm hr0 hrρ hΦρ)
    have hcub : ballGradL2 ρ (GΦ e0) ≤
        ENNReal.ofReal (Cd1 * Cφ * Cd2) * ballGradL2 R g := by
      refine hG2.trans ?_
      rw [hB, ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCd1' hCφ0) hCd2')]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : Cd1 * cubeGradL2 (m + d + 1) (GΦ e0) ≤ Cd1 * (Cφ * cubeGradL2 m g) :=
        mul_le_mul_of_nonneg_left hG4 hCd1'
      have h2 : Cd1 * (Cφ * cubeGradL2 m g) ≤ Cd1 * (Cφ * (Cd2 * (ballGradL2 R g).toReal)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXY hCφ0) hCd1'
      calc Cd1 * cubeGradL2 (m + d + 1) (GΦ e0) ≤ _ := h1.trans h2
        _ = _ := by ring
    have hbig : ballGradL2 r (fun x => g x - GΦ e0 x) ≤
        ENNReal.ofReal Clg * ballGradL2 R g := by
      refine hsub.trans ?_
      refine (add_le_add hg1 (hG1.trans (mul_le_mul_right (hcub) _))).trans (le_of_eq ?_)
      rw [hClgdef, ENNReal.ofReal_add hCb0
        (mul_nonneg hCb0 (mul_nonneg (mul_nonneg hCd1' hCφ0) hCd2')),
        ENNReal.ofReal_mul (p := Cb) (q := Cd1 * Cφ * Cd2) hCb0]
      ring
    have hqlow : 1 ≤ 81 * Real.sqrt d * (r / R) ^ γ := by
      have hR81 : R ≤ 81 * Real.sqrt d * r := by
        have h1 : R ≤ 3 / 2 * Real.sqrt d * (3 : ℝ) ^ m := by linarith only [hmR1]
        calc R ≤ 3 / 2 * Real.sqrt d * (3 : ℝ) ^ m := h1
          _ ≤ 3 / 2 * Real.sqrt d * (54 * r) :=
            mul_le_mul_of_nonneg_left hlarge.le (mul_nonneg (by norm_num) hspos.le)
          _ = 81 * Real.sqrt d * r := by ring
      have h1 : 1 ≤ 81 * Real.sqrt d * (r / R) := by
        rw [show 81 * Real.sqrt d * (r / R) = (81 * Real.sqrt d * r) / R by ring,
          le_div_iff₀ hRpos]
        linarith only [hR81]
      have h2 : r / R ≤ (r / R) ^ γ := by
        have := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hγ1
        rwa [Real.rpow_one] at this
      calc (1 : ℝ) ≤ 81 * Real.sqrt d * (r / R) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 h81
    refine hbig.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
    have h0 : 0 ≤ (1 + Csm) * (r / R) ^ γ := mul_nonneg (by linarith only [hCsm0]) hqγ
    have e : (1 + Csm + 81 * Real.sqrt d * Clg) * (r / R) ^ γ =
        (1 + Csm) * (r / R) ^ γ + Clg * (81 * Real.sqrt d * (r / R) ^ γ) := by ring
    have h1 : Clg ≤ Clg * (81 * Real.sqrt d * (r / R) ^ γ) := by
      calc Clg = Clg * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hqlow hClg0
    linarith only [e, h0, h1]

/-- Witness for the numerical hypotheses: `δ = 0`, `s = 1`, `Cs = 1`, and admissible exponents. -/
example : ∃ (η κ γ : ℝ) (mstar : ℕ), 1 / 2 ≤ η ∧ η < 1 ∧ 0 < κ ∧ κ ≤ 1 / 24 ∧ 0 < γ ∧
    γ + 7 * κ ≤ η ∧ 3 ≤ mstar ∧
    (∀ j : ℕ, mstar ≤ j → 0 ≤ (fun _ : ℕ => (0 : ℝ)) j ∧ (fun _ : ℕ => (0 : ℝ)) j ≤ 1) ∧
    (∀ k m : ℕ, mstar ≤ k → k ≤ m →
      0 < (fun _ : ℕ => (1 : ℝ)) m ∧
        (fun _ : ℕ => (1 : ℝ)) (m + 1) ≤ 2 * (fun _ : ℕ => (1 : ℝ)) m ∧
        (fun _ : ℕ => (1 : ℝ)) k ≤
          1 * (9 : ℝ) ^ ((1 / 24 : ℝ) * ((m : ℝ) - (k : ℝ))) * (fun _ : ℕ => (1 : ℝ)) m) := by
  refine ⟨9 / 10, 1 / 24, 1 / 2, 3, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, le_rfl, fun _ _ => ⟨le_rfl, by norm_num⟩, ?_⟩
  intro k m _ hkm
  refine ⟨one_pos, by norm_num, ?_⟩
  have h : (1 : ℝ) ≤ (9 : ℝ) ^ ((1 / 24 : ℝ) * ((m : ℝ) - (k : ℝ))) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) (sub_nonneg.2 (Nat.cast_le.2 hkm)))
  simpa using h

end SuperdiffusionCLT.Section6
