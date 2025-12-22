import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.PowModTotient
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum.Prime

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Classical

namespace Putnam2025B3

lemma round1_h_main_lemma (p k : ℕ)
  (hk : Nat.Prime p)
  (n : ℕ)
  (hn : n ≠ 0)
  (h : p ^ k ∣ n):
  k ≤ padicValNat p n := by
  have h1 : k ≤ n.factorization p := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization hk hn] at h
    exact h
  have h2 : padicValNat p n = n.factorization p := by
    exact Eq.symm (Nat.factorization_def n hk)
  rw [h2]
  exact h1

theorem round1_lemma1 :
  ∀ (n : ℕ), n ≥ 1 → ∃ a b m : ℕ, n = 3^a * 5^b * m ∧ Nat.Coprime m 15 := by
  intro n hn
  have h_npos : 0 < n := by linarith
  set a : ℕ := padicValNat 3 n with ha
  have h1 : 3 ^ a ∣ n := by
    apply pow_padicValNat_dvd
  set k : ℕ := n / (3 ^ a) with hk
  have h2 : n = 3 ^ a * k := by
    have h21 : 3 ^ a ∣ n := h1
    have h22 : n = (3 ^ a) * (n / (3 ^ a)) := by
      rw [Nat.mul_div_cancel' h21]
    simpa [hk] using h22
  have h_pos_k : 0 < k := by
    have h12 : 0 < 3 ^ a := by positivity
    have h13 : n = 3 ^ a * k := h2
    have h14 : 0 < n := h_npos
    nlinarith
  set b : ℕ := padicValNat 5 k with hb
  have h3 : 5 ^ b ∣ k := by
    apply pow_padicValNat_dvd
  set m : ℕ := k / (5 ^ b) with hm
  have h4 : k = 5 ^ b * m := by
    have h41 : 5 ^ b ∣ k := h3
    have h42 : k = (5 ^ b) * (k / (5 ^ b)) := by
      rw [Nat.mul_div_cancel' h41]
    simpa [hm] using h42
  have h5 : n = 3 ^ a * 5 ^ b * m := by
    calc
      n = 3 ^ a * k := h2
      _ = 3 ^ a * (5 ^ b * m) := by rw [h4]
      _ = 3 ^ a * 5 ^ b * m := by ring
  have h6 : ¬ (3 ∣ m) := by
    by_contra h
    have h7 : 3 ∣ k := by
      rw [h4]
      exact dvd_mul_of_dvd_right h (5 ^ b)
    rcases h7 with ⟨t, ht⟩
    have h8 : n = 3 ^ (a + 1) * t := by
      calc
        n = 3 ^ a * k := h2
        _ = 3 ^ a * (3 * t) := by rw [ht]
        _ = 3 ^ (a + 1) * t := by ring
    have h9 : 3 ^ (a + 1) ∣ n := ⟨t, h8⟩
    have h10 : a + 1 ≤ a := round1_h_main_lemma 3 (a + 1) (by norm_num) n (by linarith) h9
    omega
  have h7 : ¬ (5 ∣ m) := by
    by_contra h
    rcases h with ⟨t, ht⟩
    have h_eq : m = 5 * t := by exact ht
    have h10 : k = 5 ^ (b + 1) * t := by
      calc
        k = 5 ^ b * m := h4
        _ = 5 ^ b * (5 * t) := by rw [h_eq]
        _ = 5 ^ (b + 1) * t := by ring
    have h11 : 5 ^ (b + 1) ∣ k := ⟨t, h10⟩
    have h12 : b + 1 ≤ b := round1_h_main_lemma 5 (b + 1) (by norm_num) k (by linarith) h11
    omega
  have h_coprime3 : Nat.Coprime m 3 := by
    have h11 : Nat.Prime 3 := by norm_num
    have h12 : ¬ (3 ∣ m) := h6
    have h13 : Nat.Coprime 3 m := Nat.Prime.coprime_iff_not_dvd h11 |>.mpr h12
    exact Nat.Coprime.symm h13
  have h_coprime5 : Nat.Coprime m 5 := by
    have h13 : Nat.Prime 5 := by norm_num
    have h14 : ¬ (5 ∣ m) := h7
    have h15 : Nat.Coprime 5 m := Nat.Prime.coprime_iff_not_dvd h13 |>.mpr h14
    exact Nat.Coprime.symm h15
  have h_main : Nat.Coprime m 15 := by
    have h15 : 15 = 3 * 5 := by norm_num
    rw [h15]
    exact Nat.Coprime.mul_right h_coprime3 h_coprime5
  exact ⟨a, b, m, ⟨h5, h_main⟩⟩

lemma round1_h1a :
  ∀ (k : ℕ), k ≥ 1 → Nat.totient (3 ^ k) = 2 * 3 ^ (k - 1) := by
  intro k hk
  have h₁ : Nat.Prime 3 := by norm_num
  have h₂ : ∃ n : ℕ, k = n + 1 := by
    refine' ⟨k - 1, _⟩
    omega
  rcases h₂ with ⟨n, rfl⟩
  have h₃ : Nat.totient (3 ^ (n + 1)) = 3 ^ n * (3 - 1) := by
    apply Nat.totient_prime_pow_succ h₁
  have h₄ : Nat.totient (3 ^ (n + 1)) = 2 * 3 ^ n := by
    rw [h₃]
    ring
  simpa using h₄

lemma round1_h1b :
  ∀ (k : ℕ), k ≥ 1 → 2 * 3 ^ (k - 1) ≥ k := by
  intro k hk
  induction k with
  | zero =>
    exfalso
    linarith
  | succ k ih =>
    cases k with
    | zero =>
      norm_num
    | succ k' =>
      simp [pow_succ] at ih ⊢
      ring_nf at * ; omega

lemma round1_h1 :
  ∀ (a : ℕ), Nat.totient (3 ^ a) ≥ a := by
  intro a
  by_cases h : a = 0
  ·
    subst h
    norm_num
  ·
    have ha : a ≥ 1 := by omega
    have h₃ : Nat.totient (3 ^ a) = 2 * 3 ^ (a - 1) := round1_h1a a ha
    have h₄ : 2 * 3 ^ (a - 1) ≥ a := round1_h1b a ha
    rw [h₃]
    exact h₄

lemma round1_h2 :
  ∀ (b : ℕ), Nat.totient (5 ^ b) ≥ 1 := by
  intro b
  have h₁ : 5 ^ b ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  have h₂ : Nat.totient (5 ^ b) ≥ 1 := Nat.totient_pos.mpr (by positivity)
  exact h₂

lemma round1_h3a :
  ∀ (k : ℕ), k ≥ 1 → Nat.totient (5 ^ k) = 4 * 5 ^ (k - 1) := by
  intro k hk
  have h₁ : Nat.Prime 5 := by norm_num
  have h₂ : ∃ n : ℕ, k = n + 1 := by
    refine' ⟨k - 1, _⟩
    omega
  rcases h₂ with ⟨n, rfl⟩
  have h₃ : Nat.totient (5 ^ (n + 1)) = 5 ^ n * (5 - 1) := by
    apply Nat.totient_prime_pow_succ h₁
  have h₄ : Nat.totient (5 ^ (n + 1)) = 4 * 5 ^ n := by
    rw [h₃]
    ring
  simpa using h₄

lemma round1_h3b :
  ∀ (k : ℕ), k ≥ 1 → 4 * 5 ^ (k - 1) ≥ k := by
  intro k hk
  induction k with
  | zero =>
    exfalso
    linarith
  | succ k ih =>
    cases k with
    | zero =>
      norm_num
    | succ k' =>
      simp [pow_succ] at ih ⊢
      ring_nf at * ; omega

lemma round1_h3 :
  ∀ (b : ℕ), Nat.totient (5 ^ b) ≥ b := by
  intro b
  by_cases h : b = 0
  ·
    subst h
    norm_num
  ·
    have hb : b ≥ 1 := by omega
    have h₃ : Nat.totient (5 ^ b) = 4 * 5 ^ (b - 1) := round1_h3a b hb
    have h₄ : 4 * 5 ^ (b - 1) ≥ b := round1_h3b b hb
    rw [h₃]
    exact h₄

lemma round1_h4' :
  ∀ (a : ℕ), Nat.totient (3 ^ a) ≥ 1 := by
  intro a
  have h₁ : 3 ^ a ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  have h₂ : Nat.totient (3 ^ a) ≥ 1 := Nat.totient_pos.mpr (by positivity)
  exact h₂

theorem round1_lemma2 :
  ∀ (a b m : ℕ), m ≥ 1 → (Nat.totient (3^a) * Nat.totient (5^b) * Nat.totient m ≥ a) ∧
  (Nat.totient (3^a) * Nat.totient (5^b) * Nat.totient m ≥ b) := by
  have h1 : ∀ (a : ℕ), Nat.totient (3 ^ a) ≥ a := round1_h1
  have h2 : ∀ (b : ℕ), Nat.totient (5 ^ b) ≥ 1 := round1_h2
  have h3 : ∀ (b : ℕ), Nat.totient (5 ^ b) ≥ b := round1_h3
  have h4' : ∀ (a : ℕ), Nat.totient (3 ^ a) ≥ 1 := round1_h4'
  intro a b m hm
  have h4 : Nat.totient m ≥ 1 := Nat.totient_pos.mpr (by positivity)
  have h5 : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m ≥ a := by
    have h5₁ : Nat.totient m ≥ 1 := h4
    have h5₂ : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m ≥ Nat.totient (3 ^ a) * Nat.totient (5 ^ b) := by
      have h5₃ : Nat.totient m ≥ 1 := h5₁
      exact le_mul_of_one_le_right (by positivity) h5₃
    have h5₄ : Nat.totient (5 ^ b) ≥ 1 := h2 b
    have h5₅ : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) ≥ Nat.totient (3 ^ a) := by
      calc
        Nat.totient (3 ^ a) * Nat.totient (5 ^ b)
          ≥ Nat.totient (3 ^ a) * 1 := by gcongr
        _ = Nat.totient (3 ^ a) := by ring
    have h5₆ : Nat.totient (3 ^ a) ≥ a := h1 a
    calc
      Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m
        ≥ Nat.totient (3 ^ a) * Nat.totient (5 ^ b) := h5₂
      _ ≥ Nat.totient (3 ^ a) := h5₅
      _ ≥ a := h5₆
  have h6 : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m ≥ b := by
    have h6₁ : Nat.totient m ≥ 1 := h4
    have h6₂ : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m ≥ Nat.totient (3 ^ a) * Nat.totient (5 ^ b) := by
      have h6₃ : Nat.totient m ≥ 1 := h6₁
      exact le_mul_of_one_le_right (by positivity) h6₃
    have h6₄ : Nat.totient (3 ^ a) ≥ 1 := h4' a
    have h6₅ : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) ≥ Nat.totient (5 ^ b) := by
      calc
        Nat.totient (3 ^ a) * Nat.totient (5 ^ b)
          ≥ 1 * Nat.totient (5 ^ b) := by gcongr
        _ = Nat.totient (5 ^ b) := by ring
    have h6₆ : Nat.totient (5 ^ b) ≥ b := h3 b
    calc
      Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m
        ≥ Nat.totient (3 ^ a) * Nat.totient (5 ^ b) := h6₂
      _ ≥ Nat.totient (5 ^ b) := h6₅
      _ ≥ b := h6₆
  exact ⟨h5, h6⟩

lemma round1_h_main (x1 x2 x3 y1 y2 y3 : ℕ)
  (h1 : x1 ≤ y1)
  (h2 : x2 ≤ y2)
  (h3 : x3 ≤ y3)
  (h4 : x1 * x2 * x3 = y1 * y2 * y3)
  (hy1_pos : 0 < y1)
  (hy2_pos : 0 < y2)
  (hy3_pos : 0 < y3):
  x1 = y1 ∧ x2 = y2 ∧ x3 = y3 := by
  have h_y1y2_pos : 0 < y1 * y2 := mul_pos hy1_pos hy2_pos
  have h5 : x1 * x2 ≤ y1 * y2 := by exact mul_le_mul' h1 h2
  have h6 : (x1 * x2) * x3 ≤ (y1 * y2) * x3 := by exact mul_le_mul_of_nonneg_right h5 (by positivity)
  have h7 : (y1 * y2) * x3 ≤ (y1 * y2) * y3 := by exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h8 : (y1 * y2) * y3 ≤ (y1 * y2) * x3 := by
    have h9 : (x1 * x2) * x3 = (y1 * y2) * y3 := h4
    linarith
  have h_eq1' : (y1 * y2) * x3 = (y1 * y2) * y3 := by
    exact le_antisymm h7 h8
  have h_x3_eq_y3 : x3 = y3 := by
    apply mul_left_cancel₀ (show (y1 * y2 : ℕ) ≠ 0 by positivity)
    exact h_eq1'
  have h_eq2 : x1 * x2 * y3 = y1 * y2 * y3 := by
    rw [h_x3_eq_y3] at h4
    exact h4
  have h_eq3 : x1 * x2 = y1 * y2 := by
    apply mul_right_cancel₀ (show (y3 : ℕ) ≠ 0 by positivity)
    simpa [mul_assoc] using h_eq2
  have h_x1_eq_y1 : x1 = y1 := by
    by_contra h
    have h5 : x1 < y1 := by omega
    have h6 : x1 * x2 < y1 * y2 := by
      have h7 : x1 ≤ y1 - 1 := by omega
      have h8 : x2 ≤ y2 := h2
      nlinarith
    rw [h_eq3] at h6
    omega
  have h_x2_eq_y2 : x2 = y2 := by
    have h9 : y1 * x2 = y1 * y2 := by
      rw [h_x1_eq_y1] at h_eq3
      simpa using h_eq3
    have h10 : x2 = y2 := by
      apply mul_left_cancel₀ (show (y1 : ℕ) ≠ 0 by positivity)
      simpa using h9
    exact h10
  exact ⟨h_x1_eq_y1, h_x2_eq_y2, h_x3_eq_y3⟩

theorem round1_lemma3 :
  ∀ (a b m n : ℕ), n = 3^a * 5^b * m → n ≥ 2 → m ≥ 1 →
  (Nat.totient (3^a) * Nat.totient (5^b) * Nat.totient m) < n := by
  intro a b m n h_eq h_n_ge_2 h_m_ge_1
  have h_y1_pos : 0 < (3 ^ a : ℕ) := by positivity
  have h_y2_pos : 0 < (5 ^ b : ℕ) := by positivity
  have h_y3_pos : 0 < m := by linarith
  have h1 : Nat.totient (3 ^ a) ≤ (3 ^ a : ℕ) := Nat.totient_le (3 ^ a)
  have h2 : Nat.totient (5 ^ b) ≤ (5 ^ b : ℕ) := Nat.totient_le (5 ^ b)
  have h3 : Nat.totient m ≤ m := Nat.totient_le m
  by_cases h : (Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m) = n
  ·
    have h4 : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m = (3 ^ a : ℕ) * (5 ^ b : ℕ) * m := by
      rw [h, h_eq]
    have h_main : Nat.totient (3 ^ a) = (3 ^ a : ℕ) ∧ Nat.totient (5 ^ b) = (5 ^ b : ℕ) ∧ Nat.totient m = m := by
      exact round1_h_main (Nat.totient (3 ^ a)) (Nat.totient (5 ^ b)) (Nat.totient m) (3 ^ a) (5 ^ b) m h1 h2 h3 h4 h_y1_pos h_y2_pos h_y3_pos
    have h5 : Nat.totient (3 ^ a) = (3 ^ a : ℕ) := h_main.1
    have h6 : Nat.totient (5 ^ b) = (5 ^ b : ℕ) := h_main.2.1
    have h7 : Nat.totient m = m := h_main.2.2
    have h8 : (3 ^ a : ℕ) = 1 := by
      by_contra h9
      have h10 : 1 < (3 ^ a : ℕ) := by
        omega
      have h11 : Nat.totient (3 ^ a) < (3 ^ a : ℕ) := Nat.totient_lt (3 ^ a) h10
      rw [h5] at h11
      omega
    have h10 : (5 ^ b : ℕ) = 1 := by
      by_contra h11
      have h12 : 1 < (5 ^ b : ℕ) := by omega
      have h13 : Nat.totient (5 ^ b) < (5 ^ b : ℕ) := Nat.totient_lt (5 ^ b) h12
      rw [h6] at h13
      omega
    have h11 : a = 0 := by
      have h12 : (3 ^ a : ℕ) = 1 := h8
      by_contra h13
      have h14 : a ≥ 1 := by omega
      have h15 : (3 ^ a : ℕ) ≥ 3 := by
        have h16 : a ≥ 1 := h14
        have h17 : (3 ^ a : ℕ) ≥ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h16
        norm_num at h17 ⊢ ; omega
      omega
    have h12 : b = 0 := by
      have h13 : (5 ^ b : ℕ) = 1 := h10
      by_contra h14
      have h15 : b ≥ 1 := by omega
      have h16 : (5 ^ b : ℕ) ≥ 5 := by
        have h17 : b ≥ 1 := h15
        have h18 : (5 ^ b : ℕ) ≥ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) h17
        norm_num at h18 ⊢ ; omega
      omega
    have h13 : m = 1 := by
      by_contra h14
      have h15 : 1 < m := by omega
      have h16 : Nat.totient m < m := Nat.totient_lt m h15
      rw [h7] at h16
      omega
    have h14 : n = 1 := by
      rw [h_eq, h11, h12, h13] ; norm_num
    omega
  ·
    have h' : (Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m) ≤ n := by
      have h5 : (Nat.totient (3 ^ a)) * (Nat.totient (5 ^ b)) ≤ (3 ^ a) * (5 ^ b) := by
        apply mul_le_mul
        · exact h1
        · exact h2
        · positivity
        · positivity
      have h6 : ((Nat.totient (3 ^ a)) * (Nat.totient (5 ^ b))) * (Nat.totient m) ≤ ((3 ^ a) * (5 ^ b)) * m := by
        exact mul_le_mul h5 h3 (by positivity) (by positivity)
      simpa [h_eq, mul_assoc] using h6
    omega

lemma round1_h_coprime135 (a b m : ℕ)
  (h2 : Nat.Coprime m 15):
  Nat.Coprime m 135 := by
  have h3 : Nat.Coprime m 3 := by
    have h4 : (3 : ℕ) ∣ 15 := by norm_num
    exact Nat.Coprime.of_dvd_right h4 h2
  have h5 : Nat.Coprime m 5 := by
    have h6 : (5 : ℕ) ∣ 15 := by norm_num
    exact Nat.Coprime.of_dvd_right h6 h2
  have h7 : Nat.Coprime m (3 ^ 3) := Nat.Coprime.pow_right 3 h3
  have h8 : Nat.Coprime m ( (3 ^ 3) * 5 ) := Nat.Coprime.mul_right h7 h5
  norm_num at h8 ⊢
  exact h8

theorem round1_lemma4 :
  ∀ (a b m : ℕ), m ≥ 1 → Nat.Coprime m 15 →
  m ∣ 135 ^ (Nat.totient (3^a) * Nat.totient (5^b) * Nat.totient m) - 1 := by
  intro a b m h1 h2
  have h_coprime135 : Nat.Coprime m 135 := round1_h_coprime135 a b m h2
  have h_main1 : m ∣ 135 ^ Nat.totient m - 1 := by
    by_cases h : m = 1
    · subst h
      norm_num
    · have h' : 1 < m := by omega
      have h_coprime135' : Nat.Coprime 135 m := Nat.Coprime.symm h_coprime135
      have h4 : 135 ^ Nat.totient m % m = 1 := by
        exact Nat.pow_totient_mod_eq_one h' h_coprime135'
      let x := 135 ^ Nat.totient m
      have hx_pos : x ≥ 1 := by
        apply Nat.one_le_pow
        norm_num
      have h5 : x % m = 1 := h4
      have h6 : m * (x / m) + x % m = x := Nat.div_add_mod x m
      have h7 : m * (x / m) + 1 = x := by
        rw [h5] at h6
        exact h6
      have h8 : x - 1 = m * (x / m) := by
        omega
      have h9 : m ∣ x - 1 := by
        rw [h8]
        exact dvd_mul_right m (x / m)
      simpa [x] using h9
  let K := Nat.totient (3 ^ a) * Nat.totient (5 ^ b)
  have h_main2 : m ∣ 135 ^ (Nat.totient m * K) - 1 := by
    have h10 : 135 ^ Nat.totient m - 1 ∣ 135 ^ (Nat.totient m * K) - 1 := by
      exact nat_pow_one_sub_dvd_pow_mul_sub_one 135 m.totient K
    exact dvd_trans h_main1 h10
  have h_final : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m = Nat.totient m * K := by
    ring
  rw [h_final]
  exact h_main2

lemma round1_h_main_eq (a b m t n : ℕ):
  2025^t - 15^t = 15^t * (135^t - 1) := by
  have h₁ : 2025 = 135 * 15 := by norm_num
  have h₂ : (2025 : ℕ)^t = (135 * 15 : ℕ)^t := by rw [h₁]
  have h₃ : (135 * 15 : ℕ)^t = 135^t * 15^t := by
    rw [mul_pow]
  have h₄ : (2025 : ℕ)^t = 135^t * 15^t := by
    rw [h₂, h₃]
  have h₅ : 135^t ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  have h₆ : 15^t > 0 := by positivity
  rw [h₄]
  have h₇ : 135^t * 15^t - 15^t = 15^t * (135^t - 1) := by
    have h₈ : 135^t * 15^t = 15^t * 135^t := by ring
    rw [h₈]
    have h₉ : 15^t * 135^t - 15^t = 15^t * (135^t - 1) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    exact h₉
  exact h₇

lemma round1_h_main_17f452 (a b m t n : ℕ)
  (h₂ : t ≥ a)
  (h₃ : t ≥ b)
  (h₄ : Nat.Coprime m 15)
  (h₅ : m ∣ 135^t - 1):
  3^a * 5^b * m ∣ 15^t * (135^t - 1) := by
  have h₆ : 3 ^ a ∣ 3 ^ t := by
    apply Nat.pow_dvd_pow
    omega
  have h₇ : 5 ^ b ∣ 5 ^ t := by
    apply Nat.pow_dvd_pow
    omega
  have h₈₁ : 15 ^ t = 3 ^ t * 5 ^ t := by
    have h₈₂ : ∀ t : ℕ, 15 ^ t = 3 ^ t * 5 ^ t := by
      intro t
      induction t with
      | zero => norm_num
      | succ t ih =>
        simp [pow_succ, ih, mul_assoc, mul_comm]
        ring
    exact h₈₂ t
  have h₈ : 3 ^ a ∣ 15 ^ t := by
    rw [h₈₁]
    exact dvd_mul_of_dvd_left h₆ (5 ^ t)
  have h₉ : 3 ^ a ∣ 15^t * (135^t - 1) := by
    exact dvd_mul_of_dvd_left h₈ (135^t - 1)
  have h₁₀ : 5 ^ b ∣ 15 ^ t := by
    rw [h₈₁]
    exact dvd_mul_of_dvd_right h₇ (3 ^ t)
  have h₁₁ : 5 ^ b ∣ 15^t * (135^t - 1) := by
    exact dvd_mul_of_dvd_left h₁₀ (135^t - 1)
  have h₁₂ : m ∣ 15^t * (135^t - 1) := by
    exact dvd_mul_of_dvd_right h₅ (15 ^ t)
  have h₁₃ : Nat.Coprime m 3 := by
    have h₁₄ : Nat.Coprime m 15 := h₄
    have h₁₅ : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h₁₅] at h₁₄
    exact Nat.Coprime.coprime_mul_right_right h₁₄
  have h₁₄ : Nat.Coprime m 5 := by
    have h₁₅ : Nat.Coprime m 15 := h₄
    have h₁₆ : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h₁₆] at h₁₅
    exact Nat.Coprime.coprime_mul_left_right h₁₅
  have h₁₅ : Nat.Coprime m (3 ^ a) := by
    apply Nat.Coprime.pow_right
    exact h₁₃
  have h₁₆ : Nat.Coprime m (5 ^ b) := by
    apply Nat.Coprime.pow_right
    exact h₁₄
  have h₁₇ : Nat.Coprime (3 ^ a) (5 ^ b) := by
    apply Nat.Coprime.pow
    norm_num
  have h₁₈ : Nat.Coprime m ((3 ^ a) * (5 ^ b)) := by
    exact Nat.Coprime.mul_right h₁₅ h₁₆
  have h₁₈' : Nat.Coprime ((3 ^ a) * (5 ^ b)) m := by
    exact h₁₈.symm
  have h₁₉ : (3 ^ a * 5 ^ b) ∣ 15^t * (135^t - 1) := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd h₁₇ h₉ h₁₁
  have h₂₀ : ((3 ^ a * 5 ^ b) * m) ∣ 15^t * (135^t - 1) := by
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h₁₈' h₁₉ h₁₂
  simpa [mul_assoc] using h₂₀

theorem round1_lemma5 :
  ∀ (a b m t n : ℕ), n = 3^a * 5^b * m → t ≥ a → t ≥ b → Nat.Coprime m 15 →
  m ∣ 135^t - 1 → n ∣ 2025^t - 15^t := by
  intro a b m t n h₁ h₂ h₃ h₄ h₅
  have h_main_eq : 2025^t - 15^t = 15^t * (135^t - 1) := round1_h_main_eq a b m t n
  have h_main : 3^a * 5^b * m ∣ 15^t * (135^t - 1) := round1_h_main_17f452 a b m t n h₂ h₃ h₄ h₅
  have h₆ : n ∣ 15^t * (135^t - 1) := by
    rw [h₁]
    exact h_main
  rw [h_main_eq]
  exact h₆

lemma round1_h_main_f1374c :
  ∀ (n : ℕ), n ≥ 1 → Nat.totient n ≥ 1 := by
  intro n hn
  have h₁ : 0 < n := by linarith
  have h₂ : 0 < Nat.totient n := Nat.totient_pos.mpr h₁
  linarith

lemma round1_h1_c40395 (a : ℕ):
  3 ^ a ≥ 1 := by
  have h : 3 ^ a ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  exact h

lemma round1_h2_967276 (b : ℕ):
  5 ^ b ≥ 1 := by
  have h : 5 ^ b ≥ 1 := by
    apply Nat.one_le_pow
    norm_num
  exact h

theorem round1_lemma6 :
  ∀ (a b m : ℕ), m ≥ 1 →
  (Nat.totient (3^a) * Nat.totient (5^b) * Nat.totient m) ≥ 1 := by
  intro a b m h
  have h11 : Nat.totient (3 ^ a) ≥ 1 := round1_h_main_f1374c (3 ^ a) (round1_h1_c40395 a)
  have h12 : Nat.totient (5 ^ b) ≥ 1 := round1_h_main_f1374c (5 ^ b) (round1_h2_967276 b)
  have h13 : Nat.totient m ≥ 1 := round1_h_main_f1374c m h
  have h_main : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) * Nat.totient m ≥ 1 := by
    have h4 : Nat.totient (3 ^ a) * Nat.totient (5 ^ b) ≥ 1 := by
      nlinarith
    nlinarith
  exact h_main

theorem putnam_2025_b3 (S : Set ℕ)
  (hS : S.Nonempty)
  (h0 : ∀ n ∈ S, 0 < n)
  (h : ∀ n ∈ S, ∀ d : ℕ, 0 < d → d ∣ 2025 ^ n - 15 ^ n → d ∈ S)
  (n : ℕ)
  (hn : 0 < n):
  n ∈ S := by
      have h1 : (1 : ℕ) ∈ S := by
        rcases hS with ⟨s, hs⟩
        have h_s_pos : 0 < s := h0 s hs
        have h15_le_2025 : 15 ^ s ≤ 2025 ^ s := by
          apply Nat.pow_le_pow_left
          norm_num
        have h1_div : (1 : ℕ) ∣ (2025 ^ s - 15 ^ s) := by
          norm_num
        have h1_in_S : (1 : ℕ) ∈ S := h s hs 1 (by norm_num) h1_div
        tauto
      have h5 : ∀ n : ℕ, 0 < n → n ∈ S := by
        intro n hn_pos
        induction n using Nat.strong_induction_on with
        | h n ih =>
          by_cases h_n_eq_1 : n = 1
          ·
            rw [h_n_eq_1]
            tauto
          ·
            have h_n_ge_2 : n ≥ 2 := by
              omega
            rcases round1_lemma1 n (by linarith) with ⟨a, b, m, h_n_eq, h_coprime_m_15⟩
            have h_m_ge_1 : m ≥ 1 := by
              by_contra h_m_lt_1
              have h_m_eq_0 : m = 0 := by omega
              rw [h_m_eq_0] at h_n_eq
              simp at h_n_eq ; omega
            set t := Nat.totient (3^a) * Nat.totient (5^b) * Nat.totient m with ht_def
            have h21 : t ≥ a ∧ t ≥ b := by
              have h211 := round1_lemma2 a b m h_m_ge_1
              tauto
            have h211 : t ≥ a := h21.left
            have h212 : t ≥ b := h21.right
            have h3 : t < n := by
              exact round1_lemma3 a b m n h_n_eq (by linarith) h_m_ge_1
            have h4 : m ∣ 135 ^ t - 1 := by
              exact round1_lemma4 a b m h_m_ge_1 h_coprime_m_15
            have h51 : n ∣ 2025 ^ t - 15 ^ t := by
              exact round1_lemma5 a b m t n h_n_eq h211 h212 h_coprime_m_15 h4
            have h_t_ge_1 : t ≥ 1 := by
              exact round1_lemma6 a b m h_m_ge_1
            have h_t_pos : 0 < t := by linarith
            have h_t_in_S : t ∈ S := by
              apply ih t (by linarith) (by linarith)
            have h_n_in_S : n ∈ S := h t h_t_in_S n (by linarith) h51
            exact h_n_in_S
      exact h5 n hn

end Putnam2025B3
