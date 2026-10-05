/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Elementary

/-!
# The pinned excess iteration (abstract)
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Finset

/-- Near-minimizing slopes along the scales `[n, M]`, ending at `pM`, whose lengths are controlled
by the telescoping slope comparison. -/
theorem lip_iteration_chain {P : Type} (size : P → ℝ) (Cs : ℝ) (hCs : 0 ≤ Cs) (n M : ℕ)
    (Φ : ℕ → P → ℝ) (pM : P) (e : ℕ → ℝ) (hΦ : ∀ j p, 0 ≤ Φ j p)
    (he : ∀ j, n ≤ j → j < M → e j = ⨅ p, Φ j p) (heM : e M = Φ M pM)
    (hslope : ∀ j, n ≤ j → j + 1 ≤ M → ∀ p q, size p ≤ size q + Cs * (Φ j p + Φ (j + 1) q))
    (hnM : n ≤ M) (η : ℝ) (hη : 0 < η) :
    ∃ q : ℕ → P, (∀ i, n ≤ i → i ≤ M → Φ i (q i) ≤ e i + η) ∧
      ∀ i, n ≤ i → i ≤ M →
        size (q i) ≤ size pM + 2 * Cs * ∑ l ∈ Ico i (M + 1), Φ l (q l) := by
  have : Nonempty P := ⟨pM⟩
  have hex : ∀ j, ∃ p : P, n ≤ j → j < M → Φ j p ≤ e j + η := by
    intro j
    by_cases hj : n ≤ j ∧ j < M
    · have hbdd : BddBelow (Set.range fun p => Φ j p) := ⟨0, by rintro _ ⟨p, rfl⟩; exact hΦ j p⟩
      have hlt : (⨅ p, Φ j p) < (⨅ p, Φ j p) + η := by linarith only [hη]
      obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt (f := fun p => Φ j p) hlt
      exact ⟨p, fun _ _ => by rw [he j hj.1 hj.2]; exact hp.le⟩
    · exact ⟨pM, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose r hr using hex
  let q : ℕ → P := fun j => if j = M then pM else r j
  have hqM : q M = pM := by simp [q]
  have hq1 : ∀ i, n ≤ i → i ≤ M → Φ i (q i) ≤ e i + η := by
    intro i hi1 hi2
    rcases hi2.lt_or_eq with h | h
    · have : q i = r i := by simp [q, h.ne]
      rw [this]; exact hr i hi1 h
    · subst h; rw [hqM, heM]; linarith only [hη]
  refine ⟨q, hq1, ?_⟩
  have key : ∀ d i, i + d = M → n ≤ i →
      size (q i) ≤ size pM + Cs * Φ i (q i) + 2 * Cs * ∑ l ∈ Ico (i + 1) (M + 1), Φ l (q l) := by
    intro d
    induction d with
    | zero =>
      intro i hi _
      have hiM : i = M := by omega
      subst hiM
      rw [Finset.Ico_self, Finset.sum_empty, hqM]
      have := mul_nonneg hCs (hΦ i pM)
      linarith only [this]
    | succ d ih =>
      intro i hi hni
      have h1 := ih (i + 1) (by omega) (by omega)
      have h2 := hslope i hni (by omega) (q i) (q (i + 1))
      have h3 : ∑ l ∈ Ico (i + 1) (M + 1), Φ l (q l) =
          Φ (i + 1) (q (i + 1)) + ∑ l ∈ Ico (i + 1 + 1) (M + 1), Φ l (q l) :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [h3]
      linarith only [h1, h2]
  intro i hi1 hi2
  have h1 := key (M - i) i (by omega) hi1
  have h3 : ∑ l ∈ Ico i (M + 1), Φ l (q l) =
      Φ i (q i) + ∑ l ∈ Ico (i + 1) (M + 1), Φ l (q l) :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  rw [h3]
  have h4 : 0 ≤ Cs * Φ i (q i) := mul_nonneg hCs (hΦ i _)
  linarith only [h1, h4]

theorem lip_iteration_restr {P : Type} (Cr : ℝ) (hCr : 1 ≤ Cr) (n M : ℕ) (Φ : ℕ → P → ℝ)
    (hr : ∀ j, n ≤ j → j + 1 ≤ M → ∀ p, Φ j p ≤ Cr * Φ (j + 1) p)
    (p : P) : ∀ d i, i + d = M → n ≤ i → Φ i p ≤ Cr ^ d * Φ M p := by
  intro d
  induction d with
  | zero => intro i hi _; have : i = M := by omega
            subst this; simp
  | succ d ih =>
    intro i hi hni
    have h1 := ih (i + 1) (by omega) (by omega)
    have h2 := hr i hni (by omega) p
    calc Φ i p ≤ Cr * Φ (i + 1) p := h2
      _ ≤ Cr * (Cr ^ d * Φ M p) := mul_le_mul_of_nonneg_left h1 (by linarith only [hCr])
      _ = Cr ^ (d + 1) * Φ M p := by ring


/-- The one-step inequality for the minimal flatness `e`, with the error `η` of a near-minimizing
chain. -/
theorem lip_iteration_step {P : Type} (size : P → ℝ) (Cs : ℝ) (hCs : 0 ≤ Cs) (k₀ n M : ℕ)
    (Φ : ℕ → P → ℝ) (a b : ℕ → ℝ) (pM : P) (e : ℕ → ℝ) (hΦ : ∀ j p, 0 ≤ Φ j p)
    (he0 : ∀ j, 0 ≤ e j) (hb : ∀ k, 0 ≤ b k)
    (he : ∀ j, n ≤ j → j < M → e j = ⨅ p, Φ j p) (heM : e M = Φ M pM)
    (hone : ∀ k, n + k₀ ≤ k → k + 1 ≤ M → ∀ p, ∃ p',
      Φ (k - k₀) p' ≤ 1 / 2 * Φ (k + 1) p + b k * size p + a k)
    (hslope : ∀ j, n ≤ j → j + 1 ≤ M → ∀ p q, size p ≤ size q + Cs * (Φ j p + Φ (j + 1) q))
    (η : ℝ) (hη : 0 < η) (k : ℕ) (hk : n + k₀ ≤ k) (hkM : k + 1 ≤ M) :
    e (k - k₀) ≤ 1 / 2 * e (k + 1) +
      (a k + b k * (size pM + 2 * Cs * e M) + η * (1 + 2 * Cs * b k * (M + 1))) +
        2 * Cs * b k * ∑ l ∈ Ico k M, e l := by
  obtain ⟨q, hq1, hq2⟩ := lip_iteration_chain size Cs hCs n M Φ pM e hΦ he heM hslope
    (by omega) η hη
  obtain ⟨p', hp'⟩ := hone k hk hkM (q (k + 1))
  have h1 : e (k - k₀) ≤ Φ (k - k₀) p' := by
    rw [he (k - k₀) (by omega) (by omega)]
    exact ciInf_le ⟨0, by rintro _ ⟨p, rfl⟩; exact hΦ _ p⟩ p'
  have h2 := hq1 (k + 1) (by omega) hkM
  have h3 := hq2 (k + 1) (by omega) hkM
  have h4 : ∑ l ∈ Ico (k + 1) (M + 1), Φ l (q l) ≤ ∑ l ∈ Ico (k + 1) (M + 1), (e l + η) := by
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_Ico] at hl
    exact hq1 l (by omega) (by omega)
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h4
  have h5 : ∑ l ∈ Ico (k + 1) (M + 1), e l = ∑ l ∈ Ico (k + 1) M, e l + e M :=
    Finset.sum_Ico_succ_top (by omega) _
  have h6 : ∑ l ∈ Ico (k + 1) M, e l ≤ ∑ l ∈ Ico k M, e l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (by omega))
      (fun i _ _ => he0 i)
  have h7 : ((M + 1 - (k + 1) : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
    have : M + 1 - (k + 1) ≤ M + 1 := Nat.sub_le _ _
    exact_mod_cast this
  have h8 : ((M + 1 - (k + 1) : ℕ) : ℝ) * η ≤ ((M : ℝ) + 1) * η :=
    mul_le_mul_of_nonneg_right h7 hη.le
  have h9 : size (q (k + 1)) ≤ size pM + 2 * Cs * (∑ l ∈ Ico k M, e l + e M + ((M : ℝ) + 1) * η) := by
    have : 2 * Cs * ∑ l ∈ Ico (k + 1) (M + 1), Φ l (q l) ≤
        2 * Cs * (∑ l ∈ Ico k M, e l + e M + ((M : ℝ) + 1) * η) :=
      mul_le_mul_of_nonneg_left (by linarith only [h4, h5, h6, h8]) (by linarith only [hCs])
    linarith only [h3, this]
  have h10 := mul_le_mul_of_nonneg_left h9 (hb k)
  linarith only [h1, hp', h2, h10, hη]


theorem lip_iteration_sum_int_nat (x y : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc (x : ℤ) (y : ℤ), f j.toNat = ∑ j ∈ Finset.Icc x y, f j := by
  refine Finset.sum_nbij' Int.toNat (fun j : ℕ => (j : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro j hj; rw [Finset.mem_Icc] at hj ⊢; omega
  · intro j hj; rw [Finset.mem_Icc] at hj ⊢; omega
  · intro j hj; rw [Finset.mem_Icc] at hj; omega
  · intro j _; simp
  · intro j _; rfl

theorem lip_iteration_limit (X Y c : ℝ) (hc : 0 ≤ c) (h : ∀ η : ℝ, 0 < η → X ≤ Y + η * c) :
    X ≤ Y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : 0 < c + 1 := by linarith only [hc]
  have h1 := h (ε / (c + 1)) (div_pos hε hpos)
  have h2 : ε / (c + 1) * (c + 1) = ε := div_mul_cancel₀ _ hpos.ne'
  have h3 : 0 ≤ ε / (c + 1) := (div_pos hε hpos).le
  have h4 : ε / (c + 1) * c ≤ ε / (c + 1) * (c + 1) :=
    mul_le_mul_of_nonneg_left (by linarith only) h3
  linarith only [h1, h2, h4]


/-- The sum of the minimal flatnesses over `[n, M]`. -/
theorem lip_iteration_sum_bound {P : Type} (size : P → ℝ) (Cs Cr : ℝ) (hCs : 0 ≤ Cs)
    (hCr : 1 ≤ Cr) (k₀ n M : ℕ) (Φ : ℕ → P → ℝ) (a b : ℕ → ℝ) (pM : P) (e : ℕ → ℝ)
    (hΦ : ∀ j p, 0 ≤ Φ j p) (he0 : ∀ j, 0 ≤ e j) (hb : ∀ k, 0 ≤ b k)
    (he : ∀ j, n ≤ j → j < M → e j = ⨅ p, Φ j p) (heM : e M = Φ M pM)
    (hlow : ∀ j, j < n → e j = 0)
    (hone : ∀ k, n + k₀ ≤ k → k + 1 ≤ M → ∀ p, ∃ p',
      Φ (k - k₀) p' ≤ 1 / 2 * Φ (k + 1) p + b k * size p + a k)
    (hslope : ∀ j, n ≤ j → j + 1 ≤ M → ∀ p q, size p ≤ size q + Cs * (Φ j p + Φ (j + 1) q))
    (hr : ∀ j, n ≤ j → j + 1 ≤ M → ∀ p, Φ j p ≤ Cr * Φ (j + 1) p)
    (hsmall : (∑ k ∈ Icc (n + k₀) (M - 1), b k) * (8 * (Cs + 1)) ≤ 1)
    (hM : n + k₀ + 1 ≤ M) :
    ∑ l ∈ Icc n M, e l ≤ 4 * (∑ k ∈ Icc (n + k₀) (M - 1), a k +
      (∑ k ∈ Icc (n + k₀) (M - 1), b k) * (size pM + 2 * Cs * Φ M pM) +
        (k₀ + 1) * (Cr ^ k₀ * Φ M pM)) := by
  have hCr0 : 0 ≤ Cr := by linarith only [hCr]
  have hR0 := hΦ M pM
  have hIcc : ∀ x : ℕ, Icc x (M - 1) = Ico x M := by
    intro x; ext l; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  -- the top excesses
  have htop : ∀ j : ℤ, (M : ℤ) - k₀ ≤ j → j ≤ M → e j.toNat ≤ Cr ^ k₀ * Φ M pM := by
    intro j h1 h2
    have hpow : 1 ≤ Cr ^ k₀ := one_le_pow₀ hCr
    by_cases hjn : n ≤ j.toNat ∧ j.toNat < M
    · rw [he _ hjn.1 hjn.2]
      refine le_trans (ciInf_le ⟨0, by rintro _ ⟨p, rfl⟩; exact hΦ _ p⟩ pM) ?_
      refine le_trans (lip_iteration_restr Cr hCr n M Φ hr pM (M - j.toNat) j.toNat (by omega)
        hjn.1) ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCr (by omega)) hR0
    · by_cases hjM : j.toNat = M
      · rw [hjM, heM]
        calc Φ M pM = 1 * Φ M pM := (one_mul _).symm
          _ ≤ Cr ^ k₀ * Φ M pM := mul_le_mul_of_nonneg_right hpow hR0
      · rw [hlow j.toNat (by omega)]
        exact mul_nonneg (pow_nonneg hCr0 _) hR0
  have hnm : ((n + k₀ : ℕ) : ℤ) ≤ ((M - 1 : ℕ) : ℤ) := by omega
  have hbs : ∑ k ∈ Icc (n + k₀) (M - 1), b k ≤ 1 / 8 := by
    have h0 : 0 ≤ ∑ k ∈ Icc (n + k₀) (M - 1), b k := Finset.sum_nonneg fun k _ => hb k
    have : (∑ k ∈ Icc (n + k₀) (M - 1), b k) * 8 ≤
        (∑ k ∈ Icc (n + k₀) (M - 1), b k) * (8 * (Cs + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hCs]) h0
    linarith only [this, hsmall]
  have hsm : ∑ k ∈ Icc ((n + k₀ : ℕ) : ℤ) ((M - 1 : ℕ) : ℤ), 2 * Cs * b k.toNat ≤ 1 / 4 := by
    rw [lip_iteration_sum_int_nat (n + k₀) (M - 1) (fun k => 2 * Cs * b k), ← Finset.mul_sum]
    have h0 : 0 ≤ ∑ k ∈ Icc (n + k₀) (M - 1), b k := Finset.sum_nonneg fun k _ => hb k
    linarith only [h0, hsmall]
  have hkey : ∀ η : ℝ, 0 < η → ∑ l ∈ Icc n M, e l ≤ 4 * (∑ k ∈ Icc (n + k₀) (M - 1), a k +
      (∑ k ∈ Icc (n + k₀) (M - 1), b k) * (size pM + 2 * Cs * Φ M pM) +
        (k₀ + 1) * (Cr ^ k₀ * Φ M pM)) +
      η * (4 * ∑ k ∈ Icc (n + k₀) (M - 1), (1 + 2 * Cs * b k * (M + 1))) := by
    intro η hη
    have hit : ∀ k ∈ Icc ((n + k₀ : ℕ) : ℤ) ((M - 1 : ℕ) : ℤ),
        e (k - k₀).toNat ≤ 1 / 2 * e (k + 1).toNat +
          (a k.toNat + b k.toNat * (size pM + 2 * Cs * e M) +
            η * (1 + 2 * Cs * b k.toNat * (M + 1))) +
          2 * Cs * b k.toNat * ∑ j ∈ Icc k ((M - 1 : ℕ) : ℤ), e j.toNat := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      lift k to ℕ using (by omega)
      have hst := lip_iteration_step size Cs hCs k₀ n M Φ a b pM e hΦ he0 hb he heM hone hslope
        η hη k (by omega) (by omega)
      have e1 : ((k : ℤ) - (k₀ : ℤ)).toNat = k - k₀ := by omega
      have e2 : ((k : ℤ) + 1).toNat = k + 1 := by omega
      have e3 : ∑ j ∈ Icc (k : ℤ) ((M - 1 : ℕ) : ℤ), e j.toNat = ∑ l ∈ Ico k M, e l := by
        rw [lip_iteration_sum_int_nat k (M - 1) e, hIcc]
      rw [e1, e2, e3, Int.toNat_natCast]
      exact hst
    have hmain := excess_iteration_sum k₀ ((n + k₀ : ℕ) : ℤ) ((M - 1 : ℕ) : ℤ) hnm
      (fun j => e j.toNat)
      (fun k => a k.toNat + b k.toNat * (size pM + 2 * Cs * e M) +
        η * (1 + 2 * Cs * b k.toNat * (M + 1)))
      (fun k => 2 * Cs * b k.toNat) (fun j => he0 _)
      (fun k => mul_nonneg (mul_nonneg (by norm_num) hCs) (hb _)) hit hsm
    have hl1 : ((n + k₀ : ℕ) : ℤ) - (k₀ : ℤ) = (n : ℤ) := by omega
    have hl2 : ((M - 1 : ℕ) : ℤ) + 1 = (M : ℤ) := by omega
    have hl3 : ((M - 1 : ℕ) : ℤ) - (k₀ : ℤ) + 1 = (M : ℤ) - (k₀ : ℤ) := by omega
    rw [hl1, hl2, hl3, lip_iteration_sum_int_nat n M e] at hmain
    have hA : ∑ k ∈ Icc ((n + k₀ : ℕ) : ℤ) ((M - 1 : ℕ) : ℤ),
        (a k.toNat + b k.toNat * (size pM + 2 * Cs * e M) +
          η * (1 + 2 * Cs * b k.toNat * (M + 1))) =
        ∑ k ∈ Icc (n + k₀) (M - 1), (a k + b k * (size pM + 2 * Cs * e M) +
          η * (1 + 2 * Cs * b k * (M + 1))) :=
      lip_iteration_sum_int_nat (n + k₀) (M - 1)
        (fun k => a k + b k * (size pM + 2 * Cs * e M) + η * (1 + 2 * Cs * b k * (M + 1)))
    have hA2 : ∑ k ∈ Icc (n + k₀) (M - 1), (a k + b k * (size pM + 2 * Cs * e M) +
          η * (1 + 2 * Cs * b k * (M + 1))) =
        ∑ k ∈ Icc (n + k₀) (M - 1), a k + (∑ k ∈ Icc (n + k₀) (M - 1), b k) *
          (size pM + 2 * Cs * e M) +
        η * ∑ k ∈ Icc (n + k₀) (M - 1), (1 + 2 * Cs * b k * (M + 1)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    have hT : ∑ j ∈ Icc ((M : ℤ) - k₀) (M : ℤ), e j.toNat ≤
        (k₀ + 1) * (Cr ^ k₀ * Φ M pM) := by
      have hc : ((Icc ((M : ℤ) - k₀) (M : ℤ)).card : ℝ) = k₀ + 1 := by
        rw [Int.card_Icc]
        have : ((M : ℤ) + 1 - ((M : ℤ) - k₀)).toNat = k₀ + 1 := by omega
        rw [this]; push_cast; ring
      calc ∑ j ∈ Icc ((M : ℤ) - k₀) (M : ℤ), e j.toNat
          ≤ ∑ _j ∈ Icc ((M : ℤ) - k₀) (M : ℤ), (Cr ^ k₀ * Φ M pM) :=
            Finset.sum_le_sum fun j hj => by
              rw [Finset.mem_Icc] at hj; exact htop j hj.1 hj.2
        _ = (k₀ + 1) * (Cr ^ k₀ * Φ M pM) := by
            rw [Finset.sum_const, nsmul_eq_mul, hc]
    rw [hA, hA2, heM] at hmain
    linarith only [hmain, hT]
  exact lip_iteration_limit _ _ _ (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun k _ => by
      have := hb k
      have : 0 ≤ 2 * Cs * b k * ((M : ℝ) + 1) := by positivity
      linarith only [this])) hkey


/-- **L1 — the pinned excess iteration.**  `Φ j p` is a flatness of the solution at the scale `j`
relative to the slope `p`; `size p` is the length of the slope.  From the one-step inequality, the
slope comparison between consecutive scales and the restriction bound, the quantity `osc j` is
bounded at every scale by the top flatness and the sum of the errors.  The smallness of `∑ b` is
explicit and does not involve `k₀`, `Ca`, `Cr`. -/
theorem lip_iteration (Cs Ca Cr : ℝ) (hCs : 0 ≤ Cs) (hCa : 0 ≤ Ca) (hCr : 1 ≤ Cr) (k₀ : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {P : Type} (size : P → ℝ) (n M : ℕ) (Φ : ℕ → P → ℝ) (osc a b : ℕ → ℝ) (pM : P),
        n ≤ M →
        (∀ j p, 0 ≤ Φ j p) → (∀ p, 0 ≤ size p) → (∀ k, 0 ≤ a k) → (∀ k, 0 ≤ b k) →
        (∀ k, n + k₀ ≤ k → k + 1 ≤ M → ∀ p, ∃ p',
          Φ (k - k₀) p' ≤ 1 / 2 * Φ (k + 1) p + b k * size p + a k) →
        (∀ j, n ≤ j → j + 1 ≤ M → ∀ p q, size p ≤ size q + Cs * (Φ j p + Φ (j + 1) q)) →
        (∀ j, n ≤ j → j + 1 ≤ M → ∀ p, Φ j p ≤ Cr * Φ (j + 1) p) →
        (∀ j, n ≤ j → j ≤ M → ∀ p, osc j ≤ Φ j p + Ca * size p) →
        (∑ k ∈ Finset.Icc (n + k₀) (M - 1), b k) * (8 * (Cs + 1)) ≤ 1 →
        ∀ j, n ≤ j → j ≤ M →
          osc j ≤ C * (Φ M pM + size pM + ∑ k ∈ Finset.Icc (n + k₀) (M - 1), a k) := by
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = 4 * (1 + 2 * Ca * Cs) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * Cs + (k₀ + 1) * Cr ^ k₀ := ⟨_, rfl⟩
  have hCr0 : 0 ≤ Cr := by linarith only [hCr]
  have hpow : 1 ≤ Cr ^ k₀ := one_le_pow₀ hCr
  have hK1a : 1 ≤ K1 := by
    have : 0 ≤ Ca * Cs := mul_nonneg hCa hCs
    rw [hK1]; linarith only [this]
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ((k₀ : ℝ) + 1) * Cr ^ k₀ := by positivity
    rw [hc]; linarith only [this, hCs]
  refine ⟨1 + K1 * (1 + c) + Ca + Cr ^ k₀, ?_, ?_⟩
  · have : 0 ≤ K1 * (1 + c) := mul_nonneg (by linarith only [hK1a]) (by linarith only [hc0])
    linarith only [this, hCa, hpow]
  intro P size n M Φ osc a b pM hnM hΦ hs0 ha hb hone hsl hrs hosc hsmall j hj1 hj2
  have hR0 := hΦ M pM
  have hS0 := hs0 pM
  have hA0 : 0 ≤ ∑ k ∈ Finset.Icc (n + k₀) (M - 1), a k := Finset.sum_nonneg fun k _ => ha k
  have hCrC : Cr ^ k₀ ≤ 1 + K1 * (1 + c) + Ca + Cr ^ k₀ := by
    have : 0 ≤ K1 * (1 + c) := mul_nonneg (by linarith only [hK1a]) (by linarith only [hc0])
    linarith only [this, hCa]
  have hCaC : Ca ≤ 1 + K1 * (1 + c) + Ca + Cr ^ k₀ := by
    have : 0 ≤ K1 * (1 + c) := mul_nonneg (by linarith only [hK1a]) (by linarith only [hc0])
    linarith only [this, hpow]
  have hC0 : 0 ≤ 1 + K1 * (1 + c) + Ca + Cr ^ k₀ := by linarith only [hCaC, hCa]
  have hK1C : K1 ≤ 1 + K1 * (1 + c) + Ca + Cr ^ k₀ := by
    have : K1 * 1 ≤ K1 * (1 + c) :=
      mul_le_mul_of_nonneg_left (by linarith only [hc0]) (by linarith only [hK1a])
    linarith only [this, hCa, hpow]
  have hK1Ca : K1 + Ca ≤ 1 + K1 * (1 + c) + Ca + Cr ^ k₀ := by
    have : K1 * 1 ≤ K1 * (1 + c) :=
      mul_le_mul_of_nonneg_left (by linarith only [hc0]) (by linarith only [hK1a])
    linarith only [this, hpow]
  have hK1c : K1 * c ≤ 1 + K1 * (1 + c) + Ca + Cr ^ k₀ := by
    have : K1 * c ≤ K1 * (1 + c) :=
      mul_le_mul_of_nonneg_left (by linarith only) (by linarith only [hK1a])
    linarith only [this, hCa, hpow]
  by_cases hM : n + k₀ + 1 ≤ M
  · -- the iteration
    obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun j =>
        if n ≤ j ∧ j < M then ⨅ p, Φ j p else if j = M then Φ M pM else 0 := ⟨_, rfl⟩
    have he0 : ∀ j, 0 ≤ e j := by
      intro j
      rw [he]
      dsimp only
      split_ifs
      · exact Real.iInf_nonneg fun p => hΦ j p
      · exact hR0
      · exact le_refl _
    have heq : ∀ j, n ≤ j → j < M → e j = ⨅ p, Φ j p := by
      intro j h1 h2; rw [he]; simp [h1, h2]
    have heM : e M = Φ M pM := by rw [he]; simp
    have hlow : ∀ j, j < n → e j = 0 := by
      intro j h
      have h1 : ¬(n ≤ j ∧ j < M) := by omega
      have h2 : j ≠ M := by omega
      rw [he]; simp [h1, h2]
    have hS := lip_iteration_sum_bound size Cs Cr hCs hCr k₀ n M Φ a b pM e hΦ he0 hb heq heM
      hlow hone hsl hrs hsmall hM
    obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = ∑ k ∈ Finset.Icc (n + k₀) (M - 1), b k := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ k ∈ Finset.Icc (n + k₀) (M - 1), a k := ⟨_, rfl⟩
    obtain ⟨Se, hSe⟩ : ∃ Se : ℝ, Se = ∑ l ∈ Finset.Icc n M, e l := ⟨_, rfl⟩
    rw [← hBs, ← hA, ← hSe] at hS
    rw [← hBs] at hsmall
    rw [← hA]
    have hA0' : 0 ≤ A := by rw [hA]; exact hA0
    have hB0 : 0 ≤ Bs := by rw [hBs]; exact Finset.sum_nonneg fun k _ => hb k
    have hB1 : Bs ≤ 1 := by linarith only [hsmall, hB0, mul_nonneg hB0 hCs]
    -- the bound on `osc j`
    have hosc2 : osc j ≤ (1 + 2 * Ca * Cs) * Se + Ca * size pM := by
      refine lip_iteration_limit _ _ (1 + 2 * Ca * Cs * ((M : ℝ) + 1)) (by positivity) ?_
      intro η hη
      obtain ⟨q, hq1, hq2⟩ := lip_iteration_chain size Cs hCs n M Φ pM e hΦ heq heM hsl hnM η hη
      have h1 := hosc j hj1 hj2 (q j)
      have h2 := hq1 j hj1 hj2
      have h3 := hq2 j hj1 hj2
      have h4 : ∑ l ∈ Finset.Ico j (M + 1), Φ l (q l) ≤ ∑ l ∈ Finset.Ico j (M + 1), (e l + η) := by
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_Ico] at hl
        exact hq1 l (by omega) (by omega)
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h4
      have h5 : ∑ l ∈ Finset.Ico j (M + 1), e l ≤ Se := by
        rw [hSe]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => he0 i)
        intro l hl; rw [Finset.mem_Ico] at hl; rw [Finset.mem_Icc]; omega
      have h6 : ((M + 1 - j : ℕ) : ℝ) * η ≤ ((M : ℝ) + 1) * η := by
        refine mul_le_mul_of_nonneg_right ?_ hη.le
        have : M + 1 - j ≤ M + 1 := Nat.sub_le _ _
        exact_mod_cast this
      have h7 : e j ≤ Se := by
        rw [hSe]
        exact Finset.single_le_sum (f := e) (fun i _ => he0 i) (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
      have h8 : Ca * size (q j) ≤ Ca * (size pM + 2 * Cs * (Se + ((M : ℝ) + 1) * η)) :=
        mul_le_mul_of_nonneg_left (by
          have : 2 * Cs * ∑ l ∈ Finset.Ico j (M + 1), Φ l (q l) ≤
              2 * Cs * (Se + ((M : ℝ) + 1) * η) :=
            mul_le_mul_of_nonneg_left (by linarith only [h4, h5, h6]) (by linarith only [hCs])
          linarith only [h3, this]) hCa
      linarith only [h1, h2, h7, h8]
    have hX : Se ≤ 4 * (A + size pM + c * Φ M pM) := by
      have h1 : Bs * (size pM + 2 * Cs * Φ M pM) ≤ size pM + 2 * Cs * Φ M pM :=
        mul_le_of_le_one_left (by positivity) hB1
      rw [hc]
      linarith only [hS, h1]
    have hosc3 : osc j ≤ (1 + 2 * Ca * Cs) * (4 * (A + size pM +
        c * Φ M pM)) + Ca * size pM := by
      have := mul_le_mul_of_nonneg_left hX (show 0 ≤ 1 + 2 * Ca * Cs by positivity)
      linarith only [hosc2, this]
    have hfin : (1 + 2 * Ca * Cs) * (4 * (A + size pM + c * Φ M pM)) + Ca * size pM =
        K1 * A + (K1 + Ca) * size pM + (K1 * c) * Φ M pM := by
      rw [hK1]; ring
    have p1 := mul_le_mul_of_nonneg_right hK1C hA0'
    have p2 := mul_le_mul_of_nonneg_right hK1Ca hS0
    have p3 := mul_le_mul_of_nonneg_right hK1c hR0
    linarith only [hosc3, hfin, p1, p2, p3]
  · have hjM : M - j ≤ k₀ := by omega
    have h1 := lip_iteration_restr Cr hCr n M Φ hrs pM (M - j) j (by omega) hj1
    have h2 : Cr ^ (M - j) * Φ M pM ≤ Cr ^ k₀ * Φ M pM :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCr hjM) hR0
    have h3 := hosc j hj1 hj2 pM
    have p1 := mul_nonneg hC0 hA0
    have p3 := mul_le_mul_of_nonneg_right hCrC hR0
    have p4 := mul_le_mul_of_nonneg_right hCaC hS0
    linarith only [h1, h2, h3, p3, p4, p1]

/-- Witness: constant sequences (`Φ ≡ 1`, `a ≡ 1/2`, `b ≡ 0`, trivial slopes) satisfy every
hypothesis of `lip_iteration`, with `k₀ = 1`, `n = 0`, `M = 3`. -/
example : ∃ C : ℝ, 1 ≤ C ∧ ((fun _ : ℕ => (1 : ℝ)) 1 ≤ C * (1 + 0 + ∑ k ∈ Finset.Icc (0 + 1) (3 - 1),
    (fun _ : ℕ => (1 / 2 : ℝ)) k)) := by
  obtain ⟨C, hC, h⟩ := lip_iteration 0 0 1 (by norm_num) (by norm_num) (by norm_num) 1
  refine ⟨C, hC, ?_⟩
  exact h (P := Unit) (fun _ => 0) 0 3 (fun _ _ => 1) (fun _ => 1) (fun _ => 1 / 2) (fun _ => 0)
    () (by norm_num) (fun _ _ => zero_le_one) (fun _ => le_refl _) (fun _ => by norm_num)
    (fun _ => le_refl _)
    (fun k _ _ _ => ⟨(), by simp; norm_num⟩)
    (fun j _ _ p q => by simp)
    (fun j _ _ p => by simp)
    (fun j _ _ p => by simp)
    (by simp) 1 (by norm_num) (by norm_num)

end SuperdiffusionCLT.Section7
