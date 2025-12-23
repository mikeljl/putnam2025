import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Bound

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Classical

namespace Putnam2025A1

lemma round1_h1 (x : ℕ):
  (2 * x + 1) % 2 = 1 := by
  simp [Nat.add_mod]

lemma round1_h2 (a b : ℕ)
  (ha : a % 2 = 1)
  (hga : Nat.gcd a b ∣ a):
  (Nat.gcd a b) % 2 = 1 := by
  have h₃ : Nat.gcd a b ∣ a := hga
  by_cases h : (Nat.gcd a b) % 2 = 0
  ·
    have h₄ : 2 ∣ Nat.gcd a b := by
      omega
    have h₅ : 2 ∣ a := dvd_trans h₄ h₃
    have h₆ : a % 2 = 0 := by
      omega
    omega
  ·
    omega

theorem round1_gcd_is_odd (m n : ℕ → ℕ)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
  ∀ k : ℕ, (Nat.gcd (2 * m k + 1) (2 * n k + 1)) % 2 = 1 := by
  intro k
  let a : ℕ := 2 * m k + 1
  let b : ℕ := 2 * n k + 1
  have ha : a % 2 = 1 := round1_h1 (m k)
  have h_main : (Nat.gcd a b) % 2 = 1 := round1_h2 a b ha (Nat.gcd_dvd_left a b)
  exact h_main

lemma round1_h_main (r : ℚ):
  Nat.Coprime (r.num.natAbs) (r.den) := by
  have h₁ : ∀ (r : ℚ), Nat.Coprime (r.num.natAbs) (r.den) := by
    intro r
    exact r.reduced
  exact h₁ r

theorem round1_h_coprime (m n : ℕ → ℕ)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
  ∀ k : ℕ, Nat.gcd (m (k + 1)) (n (k + 1)) = 1 := by
  intro k
  let r : ℚ := (2 * m k + 1) / (2 * n k + 1)
  have h_eq1 : (↑(m (k + 1)) : ℤ) = (r.num) := by
    simpa [r] using hm k
  have h_eq2 : n (k + 1) = r.den := by
    simpa [r] using hn k
  have h_nonneg : 0 ≤ r.num := by
    have h1 : 0 ≤ (m (k + 1) : ℤ) := by positivity
    linarith [h_eq1]
  have h4 : Int.natAbs (r.num) = m (k + 1) := by
    have h5 : Int.natAbs (r.num) = Int.natAbs ((m (k + 1) : ℤ)) := by rw [h_eq1]
    simpa using h5
  have h5 : Nat.Coprime (r.num.natAbs) (r.den) := round1_h_main r
  have h6 : Nat.Coprime (m (k + 1)) (n (k + 1)) := by
    simpa [h4, h_eq2] using h5
  have h7 : Nat.gcd (m (k + 1)) (n (k + 1)) = 1 := by
    exact h6
  exact h7

theorem round1_cross_prod_eq (m n : ℕ → ℕ)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
  ∀ k : ℕ, (2 * m k + 1) * n (k + 1) = (2 * n k + 1) * m (k + 1) := by
  intro k
  let q : ℚ := ((2 * m k + 1) / (2 * n k + 1) : ℚ)
  have h1 : m (k + 1) = q.num := hm k
  have h2 : n (k + 1) = q.den := hn k
  have hq_pos : 0 < q.den := Rat.den_pos q
  have h_pos : 0 < n (k + 1) := by
    rw [h2]
    exact hq_pos
  have h_main : (q : ℚ) = ( (q.num : ℚ) / (q.den : ℚ) ) := by
    exact Eq.symm (Rat.num_div_den q)
  have h_num_eq : (q.num : ℚ) = (m (k + 1) : ℚ) := by
    exact_mod_cast h1.symm
  have h_den_eq : (q.den : ℚ) = (n (k + 1) : ℚ) := by
    exact_mod_cast h2.symm
  have h_eq1 : (q : ℚ) = ( (m (k + 1) : ℚ) / (n (k + 1) : ℚ) ) := by
    rw [h_main, h_num_eq, h_den_eq]
  have h_eq2 : ( (2 * m k + 1 : ℚ) / (2 * n k + 1 : ℚ) ) = ( (m (k + 1) : ℚ) / (n (k + 1) : ℚ) ) := by
    simpa [q] using h_eq1
  have h_ne_zero : (n (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (show (n (k + 1) ≠ 0) from Nat.ne_of_gt h_pos)
  have h_final : (2 * m k + 1 : ℚ) * (n (k + 1) : ℚ) = (2 * n k + 1 : ℚ) * (m (k + 1) : ℚ) := by
    field_simp [h_ne_zero] at h_eq2 ⊢
    ring_nf at h_eq2 ⊢ ; exact h_eq2
  exact_mod_cast h_final

lemma round1_main_lemma (a b x y : ℕ)
  (ha_pos : 0 < a)
  (hb_pos : 0 < b)
  (h_eq : a * y = b * x)
  (h_gcd_xy : Nat.gcd x y = 1):
  let d := Nat.gcd a b;
       a = d * x ∧ b = d * y := by
  let d := Nat.gcd a b
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left b ha_pos
  have h1 : d ∣ a := Nat.gcd_dvd_left a b
  have h2 : d ∣ b := Nat.gcd_dvd_right a b
  rcases h1 with ⟨a', ha⟩
  rcases h2 with ⟨b', hb⟩
  have ha' : a = d * a' := by linarith
  have hb' : b = d * b' := by linarith
  have h_eq2 : a' * y = b' * x := by
    have h : (d * a') * y = (d * b') * x := by
      rw [← ha', ← hb']
      exact h_eq
    have h' : d * (a' * y) = d * (b' * x) := by
      ring_nf at h ⊢ ; exact h
    exact mul_left_cancel₀ (show (d : ℕ) ≠ 0 from by linarith) h'
  have h3 : Nat.gcd a' b' = 1 := by
    have h4 : Nat.gcd (d * a') (d * b') = d * Nat.gcd a' b' := by
      rw [Nat.gcd_mul_left]
    have h5 : Nat.gcd a b = Nat.gcd (d * a') (d * b') := by
      rw [ha', hb']
    have h6 : Nat.gcd a b = d * Nat.gcd a' b' := by
      rw [h5, h4]
    have h7 : d = Nat.gcd a b := by rfl
    rw [h7] at h6
    nlinarith
  have h4 : b' ∣ y := by
    have h5 : b' ∣ a' * y := by
      rw [h_eq2]
      use x
    have h6 : Nat.Coprime a' b' := by
      exact h3
    have h7 : Nat.Coprime b' a' := Nat.Coprime.symm h6
    exact Nat.Coprime.dvd_of_dvd_mul_left h7 h5
  rcases h4 with ⟨t, ht⟩
  have hy : y = b' * t := by linarith
  have h7 : x = a' * t := by
    have h_eq3 : a' * y = b' * x := h_eq2
    rw [hy] at h_eq3
    have h9 : a' * (b' * t) = b' * x := h_eq3
    have h10 : b' * (a' * t) = b' * x := by
      ring_nf at h9 ⊢ ; linarith
    have hb'_pos : 0 < b' := by
      by_contra h
      have h11 : b' = 0 := by omega
      rw [h11] at hb' ; omega
    apply mul_left_cancel₀ (show (b' : ℕ) ≠ 0 from by linarith)
    linarith
  have h8 : Nat.gcd x y = t := by
    have h9 : Nat.gcd x y = Nat.gcd (a' * t) (b' * t) := by
      rw [show x = a' * t from h7, show y = b' * t from hy]
    rw [h9]
    have h10 : Nat.gcd (a' * t) (b' * t) = t * Nat.gcd a' b' := by
      rw [Nat.gcd_mul_right] ; ring
    rw [h10, h3] ; ring
  have ht1 : t = 1 := by
    have h11 : Nat.gcd x y = 1 := h_gcd_xy
    rw [h8] at h11 ; omega
  have h9 : x = a' := by
    have h10 : x = a' * t := h7
    rw [ht1] at h10 ; linarith
  have h10 : y = b' := by
    have h11 : y = b' * t := hy
    rw [ht1] at h11 ; linarith
  have h11 : a = d * x := by
    have h12 : a = d * a' := ha'
    rw [h12, h9]
  have h12 : b = d * y := by
    have h13 : b = d * b' := hb'
    rw [h13, h10]
  exact ⟨h11, h12⟩

theorem round1_h1_f6c547 (m n : ℕ → ℕ)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den)
  (h_coprime : ∀ k : ℕ, Nat.gcd (m (k + 1)) (n (k + 1)) = 1)
  (cross_prod_eq : ∀ k : ℕ, (2 * m k + 1) * n (k + 1) = (2 * n k + 1) * m (k + 1)):
  ∀ k : ℕ, 2 * m k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * m (k + 1) ∧ 2 * n k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * n (k + 1) := by
  intro k
  let a := 2 * m k + 1
  let b := 2 * n k + 1
  let x := m (k + 1)
  let y := n (k + 1)
  have ha_pos : 0 < a := by
    dsimp [a] ; omega
  have hb_pos : 0 < b := by
    dsimp [b] ; omega
  have h_eq : a * y = b * x := by
    simpa [a, b, x, y] using cross_prod_eq k
  have h_gcd_xy : Nat.gcd x y = 1 := by
    simpa [x, y] using h_coprime k
  have h_main : (let d := Nat.gcd a b; a = d * x ∧ b = d * y) :=
    round1_main_lemma a b x y ha_pos hb_pos h_eq h_gcd_xy
  exact_mod_cast h_main

lemma round1_g_pos (m n : ℕ → ℕ)
  (k : ℕ):
  0 < Nat.gcd (2 * m k + 1) (2 * n k + 1) := by
  have h_pos1 : 0 < 2 * m k + 1 := by
    omega
  apply Nat.pos_of_dvd_of_pos _ h_pos1
  exact Nat.gcd_dvd_left (2 * m k + 1) (2 * n k + 1)

lemma round1_natAbs_sub (a b : ℕ):
  Int.natAbs ((a : ℤ) - (b : ℤ)) = if a ≥ b then a - b else b - a := by
  by_cases h : a ≥ b
  ·
    have h₁ : ∃ (d : ℕ), a = b + d := by
      refine' ⟨a - b, _⟩
      omega
    rcases h₁ with ⟨d, rfl⟩
    simp
  ·
    have h' : a < b := by omega
    have h₂ : ∃ (d : ℕ), b = a + d := by
      refine' ⟨b - a, _⟩
      omega
    rcases h₂ with ⟨d, rfl⟩
    simp

theorem round1_h_key_relation (m n : ℕ → ℕ)
  (h1 : ∀ k : ℕ, 2 * m k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * m (k + 1) ∧ 2 * n k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * n (k + 1)):
  ∀ k : ℕ, Nat.gcd (2 * m k + 1) (2 * n k + 1) * (if m (k + 1) ≥ n (k + 1) then m (k + 1) - n (k + 1) else n (k + 1) - m (k + 1)) = 2 * (if m k ≥ n k then m k - n k else n k - m k) := by
  intro k
  let g := Nat.gcd (2 * m k + 1) (2 * n k + 1)
  have hg_pos : 0 < g := round1_g_pos m n k
  have h2 : (2 * m k + 1 : ℤ) = (g : ℤ) * (m (k + 1) : ℤ) := by
    exact_mod_cast (h1 k).1
  have h3 : (2 * n k + 1 : ℤ) = (g : ℤ) * (n (k + 1) : ℤ) := by
    exact_mod_cast (h1 k).2
  set x : ℤ := (m (k + 1) : ℤ) - (n (k + 1) : ℤ) with hx_def
  set y : ℤ := (m k : ℤ) - (n k : ℤ) with hy_def
  have h_eq1 : (g : ℤ) * x = 2 * y := by
    rw [hx_def, hy_def]
    linarith
  have h_main : (g : ℤ) * Int.natAbs x = 2 * Int.natAbs y := by
    have h1 : |(g : ℤ) * x| = |(2 * y)| := by rw [h_eq1]
    have h2 : |(g : ℤ) * x| = (g : ℤ) * Int.natAbs x := by
      simp [abs_mul, abs_of_pos (show (0 : ℤ) < (g : ℤ) from by exact_mod_cast hg_pos)]
    have h3 : |(2 * y)| = 2 * Int.natAbs y := by
      simp [abs_mul]
    rw [h2, h3] at h1
    exact h1
  have h4 : (if m (k + 1) ≥ n (k + 1) then m (k + 1) - n (k + 1) else n (k + 1) - m (k + 1)) = Int.natAbs x := by
    have h_eq : Int.natAbs x = (if m (k + 1) ≥ n (k + 1) then m (k + 1) - n (k + 1) else n (k + 1) - m (k + 1)) := by
      simpa [x, hx_def] using round1_natAbs_sub (m (k + 1)) (n (k + 1))
    exact h_eq.symm
  have h5 : (if m k ≥ n k then m k - n k else n k - m k) = Int.natAbs y := by
    have h_eq : Int.natAbs y = (if m k ≥ n k then m k - n k else n k - m k) := by
      simpa [y, hy_def] using round1_natAbs_sub (m k) (n k)
    exact h_eq.symm
  rw [h4, h5] at *
  exact_mod_cast h_main

theorem round1_h_eq (m n : ℕ → ℕ)
  (h1 : ∀ k : ℕ, 2 * m k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * m (k + 1) ∧ 2 * n k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * n (k + 1))
  (h_key_relation : ∀ k : ℕ, Nat.gcd (2 * m k + 1) (2 * n k + 1) * (if m (k + 1) ≥ n (k + 1) then m (k + 1) - n (k + 1) else n (k + 1) - m (k + 1)) = 2 * (if m k ≥ n k then m k - n k else n k - m k)):
  ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * (if m k ≥ n k then m k - n k else n k - m k) = (2 ^ k) * (if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0) := by
  let d : ℕ → ℕ := fun k => if m k ≥ n k then m k - n k else n k - m k
  have h_main : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * d k = (2 ^ k) * d 0 := by
    intro k
    induction k with
    | zero =>
      simp [d]
    | succ k ih =>
      have h2 : Nat.gcd (2 * m k + 1) (2 * n k + 1) * d (k + 1) = 2 * d k := by
        simpa [d] using h_key_relation k
      have h3 : (∏ j ∈ Finset.range (k + 1), Nat.gcd (2 * m j + 1) (2 * n j + 1)) = (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * Nat.gcd (2 * m k + 1) (2 * n k + 1) := by
        rw [Finset.prod_range_succ]
      rw [h3]
      calc
        ((∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * Nat.gcd (2 * m k + 1) (2 * n k + 1)) * d (k + 1)
          = (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * (Nat.gcd (2 * m k + 1) (2 * n k + 1) * d (k + 1)) := by ring
        _ = (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * (2 * d k) := by rw [h2]
        _ = 2 * ((∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * d k) := by ring
        _ = 2 * ((2 ^ k) * d 0) := by rw [ih]
        _ = (2 ^ (k + 1)) * d 0 := by
          simp [pow_succ]
          ring
  exact h_main

lemma round1_h_main_8baa92 (m n : ℕ → ℕ)
  (h_gcd_odd : ∀ k : ℕ, (Nat.gcd (2 * m k + 1) (2 * n k + 1)) % 2 = 1):
  ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) % 2 = 1 := by
  intro k
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have h1 : (Nat.gcd (2 * m k + 1) (2 * n k + 1)) % 2 = 1 := h_gcd_odd k
    simp [ih, h1, Nat.mul_mod]

theorem round1_h_prod_odd (m n : ℕ → ℕ)
  (h_gcd_odd : ∀ k : ℕ, (Nat.gcd (2 * m k + 1) (2 * n k + 1)) % 2 = 1):
  ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) % 2 = 1 := by
  have h_main : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) % 2 = 1 :=
    round1_h_main_8baa92 m n h_gcd_odd
  exact h_main

lemma round1_h_coprime_30af95 (k : ℕ)
  (m n : ℕ → ℕ)
  (h_prod_odd : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) % 2 = 1):
  Nat.Coprime (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) 2 := by
  set P_k := ∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1) with hP_k
  have h1 : P_k % 2 = 1 := h_prod_odd k
  set d := Nat.gcd P_k 2 with hd
  have h2 : d ∣ P_k := Nat.gcd_dvd_left P_k 2
  have h3 : d ∣ 2 := Nat.gcd_dvd_right P_k 2
  have h4 : ¬ (2 ∣ d) := by
    by_contra h
    have h5 : 2 ∣ d := h
    have h6 : 2 ∣ P_k := Nat.dvd_trans h5 h2
    have h7 : P_k % 2 = 0 := Nat.mod_eq_zero_of_dvd h6
    omega
  have h8 : d ∣ 2 := h3
  have h9 : d = 1 ∨ d = 2 := by
    have h10 : d ≤ 2 := Nat.le_of_dvd (by norm_num) h8
    interval_cases d <;> tauto
  rcases h9 with (h9 | h9)
  ·
    have h10 : Nat.gcd P_k 2 = 1 := by
      exact h9
    exact h10
  ·
    have h11 : 2 ∣ d := by
      rw [h9]
    exact False.elim (h4 h11)

theorem round1_h_div (m n : ℕ → ℕ)
  (h_eq : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * (if m k ≥ n k then m k - n k else n k - m k) = (2 ^ k) * (if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0))
  (h_prod_odd : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) % 2 = 1):
  ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ (if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0) := by
  intro k
  set P_k := ∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1) with hP_k
  set C := (if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0) with hC
  have h_eq_k := h_eq k
  have hdiv : P_k ∣ (2 ^ k) * C := by
    refine' ⟨(if m k ≥ n k then m k - n k else n k - m k), _⟩
    exact (h_eq_k).symm
  have hdiv' : P_k ∣ C * (2 ^ k) := by
    have h_comm : C * (2 ^ k) = (2 ^ k) * C := by apply mul_comm
    rw [h_comm]
    exact hdiv
  have h_coprime1 : Nat.Coprime P_k 2 := round1_h_coprime_30af95 k m n h_prod_odd
  have h_coprime2 : Nat.Coprime P_k (2 ^ k) := by
    exact Nat.gcd_pow_right_of_gcd_eq_one h_coprime1
  have h_main : P_k ∣ C := Nat.Coprime.dvd_of_dvd_mul_right h_coprime2 hdiv'
  simpa [hP_k, hC] using h_main

lemma round1_h1_7de768 (S : Set ℕ)
  (hS : Set.Infinite S)
  (x : ℕ)
  (hx : x ∈ S):
  ∃ y ∈ S, x < y := by
  by_contra h
  push_neg at h
  have h2 : ∀ (y : ℕ), y ∈ S → y ≤ x := by simpa using h
  have h3 : S ⊆ Set.Iic x := by
    intro y hy
    simpa [Set.mem_Iic] using h2 y hy
  have h4 : Set.Finite S := Set.Finite.subset (Set.finite_Iic x) h3
  exact Set.not_infinite.mpr h4 hS

theorem round1_infinite_set_has_strictly_increasing_subsequence (S : Set ℕ)
  (hS : Set.Infinite S):
  ∃ f : ℕ → ℕ, (∀ i, f i ∈ S) ∧ (∀ i, f i < f (i + 1)) := by
  have h_nonempty : Set.Nonempty S := Set.Infinite.nonempty hS
  classical
  let choose_next (x : ℕ) (hx : x ∈ S) : ℕ := Classical.choose (round1_h1_7de768 S hS x hx)
  have h_choose_spec (x : ℕ) (hx : x ∈ S) : choose_next x hx ∈ S ∧ x < choose_next x hx := by
    exact Classical.choose_spec (round1_h1_7de768 S hS x hx)
  let P : Type := {x : ℕ // x ∈ S}
  let g : P → P := fun x : P ↦
    ⟨choose_next x.val x.property, (h_choose_spec x.val x.property).1⟩
  obtain ⟨x₀, hx₀⟩ := h_nonempty
  let x₀' : P := ⟨x₀, hx₀⟩
  let step : ℕ → P → P := fun _ h ↦ g h
  let f' : ℕ → P := fun n ↦ Nat.recOn n x₀' step
  let f : ℕ → ℕ := fun n ↦ (f' n).val
  have h1 : ∀ n : ℕ, f n ∈ S := by
    intro n
    have h_prop : (f' n).val ∈ S := (f' n).property
    simp [f]
  have h2 : ∀ n : ℕ, f n < f (n + 1) := by
    intro n
    have h4 : f (n + 1) = (f' (n + 1)).val := by rfl
    have h5 : f' (n + 1) = g (f' n) := by
      simp [f', step]
    rw [h4, h5]
    simp [g, h_choose_spec, f]
  exact ⟨f, h1, h2⟩

lemma round1_h_all_gcd_div_C (m n : ℕ → ℕ)
  (f : ℕ → ℕ)
  (C : ℕ)
  (h_divides : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ C):
  ∀ j : ℕ, Nat.gcd (2 * m j + 1) (2 * n j + 1) ∣ C := by
  intro j
  have h₁ : (∏ j' ∈ Finset.range (j + 1), Nat.gcd (2 * m j' + 1) (2 * n j' + 1)) ∣ C := h_divides (j + 1)
  have h₂ : Nat.gcd (2 * m j + 1) (2 * n j + 1) ∣ (∏ j' ∈ Finset.range (j + 1), Nat.gcd (2 * m j' + 1) (2 * n j' + 1)) := by
    apply Finset.dvd_prod_of_mem
    simp
  exact dvd_trans h₂ h₁

lemma round1_h_g_pos (m n : ℕ → ℕ)
  (f : ℕ → ℕ)
  (C : ℕ)
  (g : ℕ → ℕ)
  (hg : ∀ j : ℕ, g j = Nat.gcd (2 * m j + 1) (2 * n j + 1)):
  ∀ j : ℕ, g j > 0 := by
  intro j
  have h1 : g j = Nat.gcd (2 * m j + 1) (2 * n j + 1) := hg j
  rw [h1]
  apply Nat.pos_of_dvd_of_pos
  · exact Nat.gcd_dvd_left (2 * m j + 1) (2 * n j + 1)
  · omega

lemma round1_hP_pos (m n : ℕ → ℕ)
  (f : ℕ → ℕ)
  (C : ℕ)
  (g : ℕ → ℕ)
  (P : ℕ → ℕ)
  (hg : ∀ j : ℕ, g j = Nat.gcd (2 * m j + 1) (2 * n j + 1))
  (hP : ∀ k : ℕ, P k = ∏ j ∈ Finset.range k, g j)
  (h_g_pos : ∀ j : ℕ, g j > 0):
  ∀ k : ℕ, P k > 0 := by
  intro k
  induction k with
  | zero =>
    simp [hP]
  | succ k ih =>
    have h4 : P (k + 1) = P k * g k := by
      rw [hP (k + 1), hP k, Finset.prod_range_succ]
    rw [h4]
    have h5 : g k > 0 := h_g_pos k
    have h6 : P k > 0 := ih
    positivity

lemma round1_h_P_strict_mono (m n : ℕ → ℕ)
  (f : ℕ → ℕ)
  (C : ℕ)
  (g : ℕ → ℕ)
  (P : ℕ → ℕ)
  (hg : ∀ j : ℕ, g j = Nat.gcd (2 * m j + 1) (2 * n j + 1))
  (hP : ∀ k : ℕ, P k = ∏ j ∈ Finset.range k, g j)
  (h_g_pos : ∀ j : ℕ, g j > 0)
  (h_gcd_ge_3' : ∀ i : ℕ, g (f i) ≥ 3)
  (h_f_incr : ∀ i : ℕ, f i < f (i + 1)):
  ∀ i : ℕ, P (f (i + 1)) > P (f i) := by
  have hP_pos : ∀ k : ℕ, P k > 0 := round1_hP_pos m n f C g P hg hP h_g_pos
  intro i
  set k := f i
  set l := f (i + 1)
  have h_lt : k < l := h_f_incr i
  have h_main1 : P l = P k * ∏ j ∈ Finset.Ico k l, g j := by
    have h1 : Finset.range l = Finset.range k ∪ Finset.Ico k l := by
      ext x
      simp [Nat.lt_iff_le_and_ne]
      omega
    have h2 : Disjoint (Finset.range k) (Finset.Ico k l) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_range] at hx1
      simp only [Finset.mem_Ico] at hx2
      omega
    have h_eq : ∏ j ∈ Finset.range l, g j = (∏ j ∈ Finset.range k, g j) * (∏ j ∈ Finset.Ico k l, g j) := by
      rw [h1, Finset.prod_union h2]
    simpa [hP] using h_eq
  have h_prod_pos : (∏ j ∈ Finset.Ico k l, g j) > 0 := by
    apply Finset.prod_pos
    intro j _
    exact h_g_pos j
  have h_prod_ge : (∏ j ∈ Finset.Ico k l, g j) ≥ g k := by
    have h1 : k ∈ Finset.Ico k l := by
      simp [h_lt]
    have h2 : g k ∣ ∏ j ∈ Finset.Ico k l, g j := by
      apply Finset.dvd_prod_of_mem
      exact h1
    exact Nat.le_of_dvd h_prod_pos h2
  have h4 : g k ≥ 3 := h_gcd_ge_3' i
  have h5 : (∏ j ∈ Finset.Ico k l, g j) ≥ 3 := by linarith
  have hP_pos_k : P k > 0 := hP_pos k
  rw [h_main1]
  nlinarith

lemma round1_h_b_strict_mono (m n : ℕ → ℕ)
  (f : ℕ → ℕ)
  (C : ℕ)
  (g : ℕ → ℕ)
  (P : ℕ → ℕ)
  (h_b_increasing : ∀ i : ℕ, P (f (i + 1)) > P (f i)):
  ∀ (i j : ℕ), i < j → P (f j) > P (f i) := by
  intro i j h_ij
  induction j with
  | zero =>
    exfalso
    linarith
  | succ j ih =>
    by_cases h : i < j
    · have h1 : P (f j) > P (f i) := ih h
      have h2 : P (f (j + 1)) > P (f j) := h_b_increasing j
      linarith
    · have h3 : i = j := by omega
      rw [h3]
      simpa using h_b_increasing j

theorem round1_strictly_increasing_subsequence_gcd_ge_3_divides_constant_is_contradiction (m n : ℕ → ℕ)
  (f : ℕ → ℕ)
  (C : ℕ)
  (h_C_pos : C > 0)
  (h_f_incr : ∀ i : ℕ, f i < f (i + 1))
  (h_gcd_ge_3 : ∀ i : ℕ, Nat.gcd (2 * m (f i) + 1) (2 * n (f i) + 1) ≥ 3)
  (h_divides : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ C):
  False := by
  let g : ℕ → ℕ := fun j => Nat.gcd (2 * m j + 1) (2 * n j + 1)
  let P : ℕ → ℕ := fun k => ∏ j ∈ Finset.range k, g j
  have h_all_gcd_div_C : ∀ j : ℕ, g j ∣ C := round1_h_all_gcd_div_C m n f C h_divides
  have h_g_pos : ∀ j : ℕ, g j > 0 := round1_h_g_pos m n f C g (by simp [g])
  have h_gcd_ge_3' : ∀ i : ℕ, g (f i) ≥ 3 := by
    intro i
    simpa [g] using h_gcd_ge_3 i
  have h_P_strict_mono : ∀ i : ℕ, P (f (i + 1)) > P (f i) :=
    round1_h_P_strict_mono m n f C g P (by simp [g]) (by simp [P]) h_g_pos h_gcd_ge_3' h_f_incr
  let b : ℕ → ℕ := fun i => P (f i)
  have h_b_increasing : ∀ i : ℕ, b (i + 1) > b i := by
    intro i
    simpa [b] using h_P_strict_mono i
  have h_b_strict_mono : ∀ (i j : ℕ), i < j → b j > b i :=
    round1_h_b_strict_mono m n f C g P h_b_increasing
  have h_b_inj : Function.Injective b := by
    intro i j h_eq
    by_contra hne
    have h_lt : i < j := by
      by_contra h
      have h' : j < i := by omega
      have h1 := h_b_strict_mono j i h'
      linarith
    have h2 : b j > b i := h_b_strict_mono i j h_lt
    linarith
  have h_b_div_C : ∀ i : ℕ, b i ∣ C := by
    intro i
    simpa [b, P] using h_divides (f i)
  let S : Finset ℕ := Nat.divisors C
  have hS_finite : Set.Finite (S : Set ℕ) := by exact Finset.finite_toSet S
  have h_b_image : ∀ i : ℕ, b i ∈ (S : Set ℕ) := by
    intro i
    have h9 : b i ∣ C := h_b_div_C i
    have h10 : 0 < C := h_C_pos
    simp only [S] at *
    aesop
  let h : ℕ → (S : Set ℕ) := fun i => ⟨b i, h_b_image i⟩
  have h_inj : Function.Injective h := by
    intro i j h
    simp only [Subtype.ext_iff] at h
    exact h_b_inj h
  have h_univ_finite : Set.Finite (Set.univ : Set (S)) := by
    exact Set.finite_univ
  have h_range_infinite : Set.Infinite (Set.range h) := Set.infinite_range_of_injective h_inj
  have h_range_finite : Set.Finite (Set.range h) := Set.Finite.subset h_univ_finite (Set.subset_univ (Set.range h))
  exact h_range_finite.not_infinite h_range_infinite

theorem round1_product_divides_constant (m n : ℕ → ℕ)
  (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den)
  (h_gcd_odd : ∀ k : ℕ, (Nat.gcd (2 * m k + 1) (2 * n k + 1)) % 2 = 1):
  ∃ C : ℕ, C > 0 ∧ ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ C := by
  have h_coprime : ∀ k : ℕ, Nat.gcd (m (k + 1)) (n (k + 1)) = 1 := by
    exact round1_h_coprime m n hm hn
  have cross_prod_eq : ∀ k : ℕ, (2 * m k + 1) * n (k + 1) = (2 * n k + 1) * m (k + 1) := by
    exact round1_cross_prod_eq m n hm hn
  have h1 : ∀ k : ℕ, 2 * m k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * m (k + 1) ∧ 2 * n k + 1 = (Nat.gcd (2 * m k + 1) (2 * n k + 1)) * n (k + 1) := by
    exact round1_h1_f6c547 m n hm hn h_coprime cross_prod_eq
  have h_key_relation : ∀ k : ℕ, Nat.gcd (2 * m k + 1) (2 * n k + 1) * (if m (k + 1) ≥ n (k + 1) then m (k + 1) - n (k + 1) else n (k + 1) - m (k + 1)) = 2 * (if m k ≥ n k then m k - n k else n k - m k) := by
    exact round1_h_key_relation m n h1
  have h_eq : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) * (if m k ≥ n k then m k - n k else n k - m k) = (2 ^ k) * (if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0) := by
    exact round1_h_eq m n h1 h_key_relation
  have h_prod_odd : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) % 2 = 1 := by
    exact round1_h_prod_odd m n h_gcd_odd
  have h_div : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ (if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0) := by
    exact round1_h_div m n h_eq h_prod_odd
  set C : ℕ := if m 0 ≥ n 0 then m 0 - n 0 else n 0 - m 0 with hC_def
  have hC_pos : C > 0 := by
    by_cases h : m 0 ≥ n 0
    ·
      have h11 : m 0 > n 0 := by
        by_contra h12
        have h13 : m 0 ≤ n 0 := by linarith
        have h14 : m 0 = n 0 := by linarith
        tauto
      have h15 : C = m 0 - n 0 := by
        rw [hC_def]
        simp [h]
      have h16 : m 0 - n 0 > 0 := by
        omega
      linarith
    ·
      have h11 : n 0 > m 0 := by omega
      have h12 : C = n 0 - m 0 := by
        rw [hC_def]
        simp [h]
      have h13 : n 0 - m 0 > 0 := by bound
      linarith
  have h_div_C : ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ C := by
    intro k
    have h10 := h_div k
    simpa [hC_def] using h10
  exact ⟨C, hC_pos, h_div_C⟩

theorem putnam_2025_a1 (m n : ℕ → ℕ)
  (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
  {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite := by
      have h_gcd_odd : ∀ k : ℕ, (Nat.gcd (2 * m k + 1) (2 * n k + 1)) % 2 = 1 := by
        exact round1_gcd_is_odd m n hm hn
      have h2 : ∃ C : ℕ, C > 0 ∧ ∀ k : ℕ, (∏ j ∈ Finset.range k, Nat.gcd (2 * m j + 1) (2 * n j + 1)) ∣ C := by
        exact round1_product_divides_constant m n h0 hm hn h_gcd_odd
      rcases h2 with ⟨C, h_C_pos, h_divides⟩
      by_cases h5 : Set.Infinite ({k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)} : Set ℕ)
      ·
        have h6 : ∃ f : ℕ → ℕ, (∀ i, f i ∈ ({k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)} : Set ℕ)) ∧ (∀ i, f i < f (i + 1)) := by
          exact round1_infinite_set_has_strictly_increasing_subsequence ({k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)} : Set ℕ) h5
        rcases h6 with ⟨f, h_f_in_S, h_f_incr⟩
        have h_gcd_ge_3 : ∀ i : ℕ, Nat.gcd (2 * m (f i) + 1) (2 * n (f i) + 1) ≥ 3 := by
          intro i
          have h1 : (Nat.gcd (2 * m (f i) + 1) (2 * n (f i) + 1)) % 2 = 1 := by
            specialize h_gcd_odd (f i)
            simpa using h_gcd_odd
          have h21 : ¬ ( (2 * m (f i) + 1).Coprime (2 * n (f i) + 1) ) := h_f_in_S i
          have h22 : Nat.gcd (2 * m (f i) + 1) (2 * n (f i) + 1) ≠ 1 := by
            by_contra h221
            have h222 : ( (2 * m (f i) + 1).Coprime (2 * n (f i) + 1) ) := by
              simp [Nat.coprime_iff_gcd_eq_one, h221]
            tauto
          by_contra h3
          have h31 : Nat.gcd (2 * m (f i) + 1) (2 * n (f i) + 1) < 3 := by linarith
          have h32 : Nat.gcd (2 * m (f i) + 1) (2 * n (f i) + 1) = 1 := by
            omega
          tauto
        have h_contra : False := by
          exact round1_strictly_increasing_subsequence_gcd_ge_3_divides_constant_is_contradiction m n f C h_C_pos h_f_incr h_gcd_ge_3 h_divides
        exact False.elim h_contra
      ·
        have h6 : Set.Finite ({k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)} : Set ℕ) := by
          simpa [Set.Infinite] using h5
        exact h6

end Putnam2025A1
