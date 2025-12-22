import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum.Prime

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Classical

namespace Putnam2025A6

lemma round1_h_m_ne_zero (k : ℕ)
  (m : ℤ)
  (h2 : ¬ ((2 ^ (k + 2) : ℤ) ∣ m)):
  m ≠ 0 := by
  by_contra h
  have h4 : (2 ^ (k + 2) : ℤ) ∣ m := by
    rw [h]
    simp
  contradiction

theorem round1_padicValInt_lemma (k : ℕ)
  (m : ℤ)
  (h1 : (2 ^ (k + 1) : ℤ) ∣ m)
  (h2 : ¬ ((2 ^ (k + 2) : ℤ) ∣ m)):
  padicValInt 2 m = k + 1 := by
  have h_m_ne_zero : m ≠ 0 := round1_h_m_ne_zero k m h2
  have h_main₁ : (2 ^ (k + 1) : ℕ) ∣ Int.natAbs m := by
    let n : ℕ := 2 ^ (k + 1)
    have h₁' : (n : ℤ) ∣ m := by
      simpa [n] using h1
    have h₃ : n ∣ Int.natAbs m := by
      have h₄ : (n : ℤ) ∣ m := h₁'
      have h₅ : (n : ℤ) ∣ m := h₄
      have h₆ : n ∣ Int.natAbs m := by
        exact Int.ofNat_dvd_left.mp h₁'
      exact h₆
    simpa [n] using h₃
  have h_main₂ : ¬ ( (2 ^ (k + 2) : ℕ) ∣ Int.natAbs m) := by
    let n : ℕ := 2 ^ (k + 2)
    intro h_contra
    have h₃ : n ∣ Int.natAbs m := by simpa [n] using h_contra
    have h₄ : (n : ℤ) ∣ m := by
      exact Int.ofNat_dvd_left.mpr h_contra
    have h₅ : (2 ^ (k + 2) : ℤ) ∣ m := by simpa [n] using h₄
    exact h2 h₅
  have h_main₃ : k + 1 ≤ padicValNat 2 (Int.natAbs m) := by
    have h₄ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h₅ : (2 ^ (k + 1) : ℕ) ∣ Int.natAbs m := h_main₁
    have h₆ : (k + 1) ≤ padicValNat 2 (Int.natAbs m) := by
      have h₇ : (2 ^ (k + 1) : ℕ) ∣ Int.natAbs m := h₅
      have h₈ : (k + 1) ≤ padicValNat 2 (Int.natAbs m) := by
        apply (padicValNat_dvd_iff_le (show Int.natAbs m ≠ 0 from by simp [h_m_ne_zero])).mp h₇
      exact h₈
    exact h₆
  have h_main₄ : padicValNat 2 (Int.natAbs m) ≤ k + 1 := by
    have h₄ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_contra h
    have h₅ : k + 2 ≤ padicValNat 2 (Int.natAbs m) := by linarith
    have h₆ : (2 ^ (k + 2) : ℕ) ∣ Int.natAbs m := by
      apply (padicValNat_dvd_iff_le (show Int.natAbs m ≠ 0 from by simp [h_m_ne_zero])).mpr h₅
    exact h_main₂ h₆
  have h_main₅ : padicValNat 2 (Int.natAbs m) = k + 1 := by omega
  have h_final : padicValInt 2 m = padicValNat 2 (Int.natAbs m) := by rfl
  rw [h_final]
  exact h_main₅

lemma round1_h_step (b : ℕ → ℤ)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1):
  ∀ (m1 m2 : ℕ), b (m1 + 1) - b (m2 + 1) = (b m1 - b m2) * (2 * (b m1 + b m2) + 1) := by
  intro m1 m2
  have h1 : b (m1 + 1) = 2 * (b m1) ^ 2 + (b m1) + 1 := hb m1
  have h2 : b (m2 + 1) = 2 * (b m2) ^ 2 + (b m2) + 1 := hb m2
  rw [h1, h2]
  ring

theorem round1_lemma_product_formula (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1):
  ∀ (n r : ℕ), b (n + r) - b n = b r * (∏ i ∈ Finset.range n, (2 * (b (r + i) + b i) + 1)) := by
  have h_step : ∀ (m1 m2 : ℕ), b (m1 + 1) - b (m2 + 1) = (b m1 - b m2) * (2 * (b m1 + b m2) + 1) :=
    round1_h_step b hb
  have h_main : ∀ (n : ℕ), ∀ (r : ℕ), b (n + r) - b n = b r * (∏ i ∈ Finset.range n, (2 * (b (r + i) + b i) + 1)) := by
    intro n
    induction n with
    | zero =>
      intro r
      simp [hb0]
    | succ n ih =>
      intro r
      have h1 : b ((n + 1) + r) - b (n + 1) = (b (n + r) - b n) * (2 * (b (n + r) + b n) + 1) := by
        have h2 := h_step (n + r) n
        simpa [add_assoc, add_comm, add_left_comm] using h2
      have h3 : (∏ i ∈ Finset.range (n + 1), (2 * (b (r + i) + b i) + 1)) = (∏ i ∈ Finset.range n, (2 * (b (r + i) + b i) + 1)) * (2 * (b (r + n) + b n) + 1) := by
        rw [Finset.prod_range_succ]
      rw [h1, h3]
      have h4 := ih r
      rw [h4]
      ring_nf
  exact h_main

lemma round1_h_main (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1):
  ∀ (m : ℕ) (t : ℤ), ∀ (n : ℕ), g (n + m) t = g n (g m t) := by
  intro m t
  intro n
  induction n with
  | zero =>
    simp [hg1]
  | succ n ih =>
    have h1 : g ((n + 1) + m) t = g (n + m + 1) t := by ring_nf
    rw [h1]
    have h2 : g (n + m + 1) t = 2 * (g (n + m) t) ^ 2 + (g (n + m) t) + 1 := by
      apply hg2
    rw [h2]
    rw [ih]
    have h3 : g (n + 1) (g m t) = 2 * (g n (g m t)) ^ 2 + (g n (g m t)) + 1 := by
      apply hg2
    rw [h3]

theorem round1_lemma1 (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1):
  ∀ (n m : ℕ) (t : ℤ), g (n + m) t = g n (g m t) := by
  have h_main : ∀ (m : ℕ) (t : ℤ), ∀ (n : ℕ), g (n + m) t = g n (g m t) :=
    round1_h_main g hg1 hg2
  intro n m t
  exact h_main m t n

lemma round1_h_main_e082c3 (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1):
  ∀ (n : ℕ) (s h : ℤ), h % 2 = 0 → ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q := by
  intro n
  induction n with
  | zero =>
    intro s h h_h
    refine' ⟨1, by decide, by decide, _⟩
    simp [hg1]
  | succ n ih =>
    intro s h h_h
    have h1 : ∃ (q : ℤ), q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q := ih s h h_h
    rcases h1 with ⟨q, hq1, hq2, h_eq⟩
    set x := g n s with hx
    set y := g n (s + h) with hy
    have h_eq2 : y - x = h * q := h_eq
    have h_main : g (n + 1) (s + h) - g (n + 1) s = h * (q * (2 * (x + y) + 1)) := by
      have h3 : g (n + 1) (s + h) = 2 * (g n (s + h)) ^ 2 + (g n (s + h)) + 1 := hg2 n (s + h)
      have h4 : g (n + 1) s = 2 * (g n s) ^ 2 + (g n s) + 1 := hg2 n s
      rw [h3, h4]
      have h5 : (2 * (y : ℤ) ^ 2 + (y : ℤ) + 1) - (2 * (x : ℤ) ^ 2 + (x : ℤ) + 1) = (y - x) * (2 * (x + y) + 1) := by
        ring
      rw [h5]
      rw [h_eq2] ; ring
    have h4 : (2 * (x + y) + 1) % 4 = 1 := by
      have h5 : h % 2 = 0 := h_h
      have h6 : ∃ (k : ℤ), h = 2 * k := by
        refine' ⟨h / 2, _⟩
        omega
      rcases h6 with ⟨k, hk⟩
      have h7 : y = x + h * q := by linarith
      rw [h7]
      rw [hk]
      ring_nf
      omega
    have h41 : (2 * (x + y) + 1) % 2 = 1 := by
      have h42 : (2 * (x + y) + 1) % 4 = 1 := h4
      omega
    have h6 : (q * (2 * (x + y) + 1)) % 2 = 1 := by
      have hq1' : q % 2 = 1 := hq1
      have h43 : (2 * (x + y) + 1) % 2 = 1 := h41
      simp [Int.mul_emod, hq1', h43]
    have h7 : (q * (2 * (x + y) + 1)) % 4 = 1 := by
      have hq2' : q % 4 = 1 := hq2
      have h44 : (2 * (x + y) + 1) % 4 = 1 := h4
      simp [Int.mul_emod, hq2', h44]
    refine' ⟨q * (2 * (x + y) + 1), h6, h7, h_main⟩

theorem round1_lemma2 (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1)
  (h_add : ∀ (n m : ℕ) (t : ℤ), g (n + m) t = g n (g m t)):
  ∀ (n : ℕ) (s h : ℤ), h % 2 = 0 → ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q := by
  have h_main : ∀ (n : ℕ) (s h : ℤ), h % 2 = 0 → ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q := by
    exact round1_h_main_e082c3 g hg1 hg2
  exact h_main

lemma round1_h_main_96b675 (t : ℤ):
  ∃ (b : ℤ), 8 * t ^ 4 + 8 * t ^ 3 + 12 * t ^ 2 + 4 * t = 8 * b := by
  have h1 : (t ^ 2 * 3 + t) % 2 = 0 := by
    have h2 : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases h2 with (h2 | h2)
    · simp [h2, pow_two, Int.add_emod, Int.mul_emod]
    · simp [h2, pow_two, Int.add_emod, Int.mul_emod]
  have h2 : ∃ (m : ℤ), 3 * t ^ 2 + t = 2 * m := by
    refine' ⟨(3 * t ^ 2 + t) / 2, _⟩
    omega
  rcases h2 with ⟨m, hm⟩
  refine' ⟨t ^ 4 + t ^ 3 + m, _⟩
  have h3 : 8 * t ^ 4 + 8 * t ^ 3 + 12 * t ^ 2 + 4 * t = 8 * (t ^ 4 + t ^ 3 + m) := by
    have h4 : 12 * t ^ 2 + 4 * t = 8 * m := by
      linarith
    linarith
  exact h3

theorem round1_lemma3 (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1):
  ∀ (t : ℤ), ∃ b : ℤ, g 2 t = t + 4 + 8 * b := by
  intro t
  have h_g1 : g 1 t = 2 * t ^ 2 + t + 1 := by
    rw [hg2 0 t, hg1 t]
  have h_g2 : g 2 t = 2 * (g 1 t) ^ 2 + (g 1 t) + 1 := by
    rw [hg2 1 t]
  have h3 : g 2 t = 8 * t ^ 4 + 8 * t ^ 3 + 12 * t ^ 2 + 5 * t + 4 := by
    rw [h_g2, h_g1]
    ring
  have h_main : ∃ (b : ℤ), 8 * t ^ 4 + 8 * t ^ 3 + 12 * t ^ 2 + 4 * t = 8 * b := round1_h_main_96b675 t
  rcases h_main with ⟨b, hb⟩
  refine' ⟨b, _⟩
  have h4 : g 2 t = t + 4 + 8 * b := by
    linarith [h3, hb]
  exact h4

lemma round1_main_step (g : ℕ → ℤ → ℤ)
  (h_lemma_A : ∀ (n : ℕ) (s h : ℤ), h % 2 = 0 → ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q)
  (m : ℕ)
  (h : ∀ (t : ℤ), ∃ b : ℤ, g (2 ^ m) t = t + (2 ^ (m + 1)) + (2 ^ (m + 2)) * b)
  (h_add : ∀ (n m : ℕ) (t : ℤ), g (n + m) t = g n (g m t)):
  ∀ (t : ℤ), ∃ c : ℤ, g (2 ^ (m + 1)) t = t + (2 ^ (m + 2)) + (2 ^ (m + 3)) * c := by
  intro t
  have h1 : ∃ b : ℤ, g (2 ^ m) t = t + (2 ^ (m + 1)) + (2 ^ (m + 2)) * b := h t
  rcases h1 with ⟨b, hb⟩
  let s := g (2 ^ m) t
  have h2 : s = t + (2 ^ (m + 1)) + (2 ^ (m + 2)) * b := hb
  let h_val : ℤ := s - t
  have h3 : h_val = (2 ^ (m + 1) : ℤ) + (2 ^ (m + 2) : ℤ) * b := by
    simp [h_val, h2]
    ring
  have h4 : h_val % 2 = 0 := by
    rw [h3]
    simp [pow_succ]
    ring_nf
    omega
  have h5 : ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g (2 ^ m) (t + h_val) - g (2 ^ m) t = h_val * q := by
    exact h_lemma_A (2 ^ m) t h_val h4
  rcases h5 with ⟨q, hq1, hq2, h_eq⟩
  have h6 : q % 4 = 1 := hq2
  have h7 : ∃ (j : ℤ), q = 4 * j + 1 := by
    refine' ⟨(q - 1) / 4, _⟩
    omega
  rcases h7 with ⟨j, hj⟩
  have h_main_goal : g (2 ^ (m + 1)) t = t + (2 ^ (m + 2)) + (2 ^ (m + 3)) * (j + b * (2 * j + 1)) := by
    have h8 : 2 ^ (m + 1) = 2 * 2 ^ m := by
      simp [pow_succ]
      ring
    have h9 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
      simp [pow_succ]
      ring
    have h10 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by
      simp [pow_succ]
      ring
    have h11 : g (2 ^ (m + 1)) t = g (2 ^ m) (g (2 ^ m) t) := by
      have h12 : (2 ^ (m + 1) : ℕ) = (2 ^ m) + (2 ^ m) := by
        simp [pow_succ]
        ring
      rw [h12]
      exact h_add (2 ^ m) (2 ^ m) t
    rw [h11]
    have h13 : t + h_val = s := by
      dsimp [h_val]
      abel
    rw [h13] at h_eq
    have h14 : g (2 ^ m) s - g (2 ^ m) t = h_val * q := h_eq
    have h15 : g (2 ^ m) s = g (2 ^ m) t + h_val * q := by linarith
    rw [h15]
    have h16 : g (2 ^ m) t = t + (2 ^ (m + 1)) + (2 ^ (m + 2)) * b := h2
    rw [h16]
    rw [hj]
    simp [h_val, h3]
    ring_nf
  refine' ⟨j + b * (2 * j + 1), _⟩
  exact h_main_goal

theorem round1_lemma4 (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1)
  (h_add : ∀ (n m : ℕ) (t : ℤ), g (n + m) t = g n (g m t))
  (h_lemma_A : ∀ (n : ℕ) (s h : ℤ), h % 2 = 0 → ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q):
  ∀ (m : ℕ), m ≥ 1 →
  (∀ (t : ℤ), ∃ b : ℤ, g (2 ^ m) t = t + (2 ^ (m + 1)) + (2 ^ (m + 2)) * b) →
  (∀ (t : ℤ), ∃ c : ℤ, g (2 ^ (m + 1)) t = t + (2 ^ (m + 2)) + (2 ^ (m + 3)) * c) := by
  intro m hm h
  exact round1_main_step g h_lemma_A m h h_add

lemma round1_h_main_beccd7 (u : ℕ → ℤ)
  (x : ℤ)
  (h_u0 : u 0 = x)
  (h_u : ∀ n, u (n + 1) = 2 * (u n) ^ 2 + u n + 1)
  (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1):
  ∀ (n : ℕ), u n = g n x := by
  intro n
  induction n with
  | zero =>
    have h1 : u 0 = x := h_u0
    have h2 : g 0 x = x := by simpa using hg1 x
    rw [h1, h2]
  | succ n ih =>
    have h3 : u (n + 1) = 2 * (u n) ^ 2 + u n + 1 := h_u n
    have h4 : g (n + 1) x = 2 * (g n x) ^ 2 + (g n x) + 1 := hg2 n x
    rw [h3, h4]
    rw [ih]

theorem round1_lemma5 (u : ℕ → ℤ)
  (x : ℤ)
  (h_u0 : u 0 = x)
  (h_u : ∀ n, u (n + 1) = 2 * (u n) ^ 2 + u n + 1)
  (g : ℕ → ℤ → ℤ)
  (hg1 : ∀ (t : ℤ), g 0 t = t)
  (hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1):
  ∀ (n : ℕ), u n = g n x := by
  have h_main : ∀ (n : ℕ), u n = g n x := by
    exact round1_h_main_beccd7 u x h_u0 h_u g hg1 hg2
  exact h_main

lemma pow_two_gt_one (n : ℕ)
  (hn : n ≥ 1):
  (2 : ℤ) ^ n > 1 := by
  have h : (2 : ℤ) ^ n ≥ (2 : ℤ) ^ 1 := by
    have h' : n ≥ 1 := hn
    have h'' : (2 : ℕ) ^ n ≥ (2 : ℕ) ^ 1 := Nat.pow_le_pow_right (by norm_num) h'
    exact_mod_cast h''
  norm_num at h ⊢
  omega

lemma round1_h_main_00f618 (k : ℕ)
  (x : ℤ)
  (hk : k ≥ 1)
  (hx : x % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2))):
  ∃ (m : ℤ), x - 1 = (2 : ℤ) ^ (k + 1) * m ∧ m % 2 = 1 := by
  have h2 : (1 + (2 : ℤ) ^ (k + 1)) < (2 : ℤ) ^ (k + 2) := by
    have h21 : k + 1 ≥ 1 := by omega
    have h22 : (2 : ℤ) ^ (k + 1) > 1 := pow_two_gt_one (k + 1) h21
    have h25 : (2 : ℤ) ^ (k + 2) = 2 * (2 : ℤ) ^ (k + 1) := by
      ring
    rw [h25]
    linarith
  have h1 : (1 + (2 : ℤ) ^ (k + 1)) % (2 : ℤ) ^ (k + 2) = (1 + (2 : ℤ) ^ (k + 1)) := by
    have h4 : (1 + (2 : ℤ) ^ (k + 1)) ≥ 0 := by positivity
    rw [Int.emod_eq_of_lt] <;> omega
  rw [h1] at hx
  have h5 : ∃ (q : ℤ), x = q * (2 ^ (k + 2) : ℤ) + (1 + 2 ^ (k + 1) : ℤ) := by
    refine' ⟨(x / (2 ^ (k + 2) : ℤ)), _⟩
    rw [Int.emod_def] at hx
    linarith
  rcases h5 with ⟨q, hq⟩
  use (2 * q + 1)
  constructor
  ·
    have h6 : (x - 1 : ℤ) = (2 * q + 1) * (2 : ℤ) ^ (k + 1) := by
      rw [hq]
      ring_nf
    linarith
  ·
    omega

theorem round1_helper_congruence_to_odd (k : ℕ)
  (x : ℤ)
  (hk : k ≥ 1)
  (hx : x % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2))):
  ∃ m : ℤ, x - 1 = (2 : ℤ) ^ (k + 1) * m ∧ m % 2 = 1 := by
  exact round1_h_main_00f618 k x hk hx

lemma round1_h_main_2647bd (b : ℕ → ℤ)
  (lemma5_mod_powers_of_2 : ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (b (n + 2 ^ s) - b n) % (2 ^ (s + 1)) = 0)
  (k : ℕ)
  (hk : k ≥ 1):
  ∀ (i : ℕ), (4 * b (i + 2 ^ k) + 1) % (2 ^ (k + 3)) = (4 * b i + 1) % (2 ^ (k + 3)) := by
  intro i
  have h1 : (b (i + 2 ^ k) - b i) % (2 ^ (k + 1)) = 0 := lemma5_mod_powers_of_2 k hk i
  have h2 : (2 ^ (k + 1) : ℤ) ∣ (b (i + 2 ^ k) - b i) := by
    simpa [Int.emod_eq_zero_of_dvd] using h1
  have h4 : ∃ (m : ℤ), (b (i + 2 ^ k) - b i) = m * (2 ^ (k + 1)) := by
    exact exists_eq_mul_left_of_dvd h2
  rcases h4 with ⟨m, hm⟩
  have h3 : (2 ^ (k + 3) : ℤ) ∣ (4 * (b (i + 2 ^ k) - b i)) := by
    have h5 : 4 * (b (i + 2 ^ k) - b i) = m * (2 ^ (k + 3)) := by
      calc
        4 * (b (i + 2 ^ k) - b i)
          = 4 * (m * (2 ^ (k + 1))) := by rw [hm]
        _ = m * (4 * (2 ^ (k + 1))) := by ring
        _ = m * (2 ^ (k + 3)) := by
          have h6 : (4 : ℤ) * (2 ^ (k + 1)) = (2 ^ (k + 3)) := by
            ring_nf
          rw [h6]
    rw [h5]
    exact ⟨m, by ring⟩
  have h5 : (4 * b (i + 2 ^ k) + 1) - (4 * b i + 1) = 4 * (b (i + 2 ^ k) - b i) := by ring
  have h6 : (2 ^ (k + 3) : ℤ) ∣ ((4 * b (i + 2 ^ k) + 1) - (4 * b i + 1)) := by
    rw [h5]
    exact h3
  have h7 : ((4 * b (i + 2 ^ k) + 1) % (2 ^ (k + 3))) = ((4 * b i + 1) % (2 ^ (k + 3))) := by
    simpa [Int.emod_eq_emod_iff_emod_sub_eq_zero] using h6
  exact h7

lemma round1_h_step2 (k : ℕ)
  (hk : k ≥ 1):
  ((1 + 2 ^ (k + 1) : ℤ) * (1 + 2 ^ (k + 1) : ℤ)) % (2 ^ (k + 3) : ℤ) = (1 + 2 ^ (k + 2) : ℤ) % (2 ^ (k + 3) : ℤ) := by
  have h1 : k ≥ 1 := hk
  have h2 : 2 * (k + 1) ≥ k + 3 := by omega
  have h3 : (2 ^ (k + 3) : ℤ) ∣ (2 ^ (2 * (k + 1)) : ℤ) := by
    have h4 : (k + 3) ≤ 2 * (k + 1) := by omega
    have h5 : (2 ^ (k + 3) : ℤ) ∣ (2 ^ (2 * (k + 1)) : ℤ) := by
      apply pow_dvd_pow
      omega
    exact h5
  have h_main : ((1 + 2 ^ (k + 1) : ℤ) * (1 + 2 ^ (k + 1) : ℤ)) = (1 + 2 ^ (k + 2) : ℤ) + (2 ^ (2 * (k + 1)) : ℤ) := by
    ring_nf
  rw [h_main]
  have h6 : (((1 + 2 ^ (k + 2) : ℤ) + (2 ^ (2 * (k + 1)) : ℤ)) % (2 ^ (k + 3) : ℤ)) = ((1 + 2 ^ (k + 2) : ℤ) % (2 ^ (k + 3) : ℤ)) := by
    have h7 : ∀ (a b : ℤ), (2 ^ (k + 3) : ℤ) ∣ b → ((a + b) % (2 ^ (k + 3) : ℤ)) = (a % (2 ^ (k + 3) : ℤ)) := by
      intro a b hb
      rcases hb with ⟨c, hc⟩
      simp [hc, Int.add_emod]
    exact h7 (1 + 2 ^ (k + 2) : ℤ) (2 ^ (2 * (k + 1)) : ℤ) h3
  rw [h6]

lemma round1_h_missing (k : ℕ)
  (hk : k ≥ 1)
  (x : ℤ)
  (h : x % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2))):
  (x ^ 2) % (2 ^ (k + 3)) = (1 + 2 ^ (k + 2)) % (2 ^ (k + 3)) := by
  have h1 : ∃ (t : ℤ), x = (1 + 2 ^ (k + 1)) + t * (2 ^ (k + 2)) := by
    have h2 : x % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2)) := h
    have h3 : (2 ^ (k + 2) : ℤ) ∣ (x - (1 + 2 ^ (k + 1))) := by
      simpa [Int.emod_eq_emod_iff_emod_sub_eq_zero] using h2
    rcases h3 with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    linarith
  rcases h1 with ⟨t, ht⟩
  have h_eq : x ^ 2 = (1 + 2 ^ (k + 1)) ^ 2 + (t * (1 + 2 ^ (k + 1))) * (2 ^ (k + 3)) + t ^ 2 * (2 ^ (2 * (k + 2))) := by
    calc
      x ^ 2 = ((1 + 2 ^ (k + 1)) + t * (2 ^ (k + 2))) ^ 2 := by rw [ht]
      _ = (1 + 2 ^ (k + 1)) ^ 2 + 2 * (1 + 2 ^ (k + 1)) * (t * (2 ^ (k + 2))) + (t * (2 ^ (k + 2))) ^ 2 := by ring
      _ = (1 + 2 ^ (k + 1)) ^ 2 + (t * (1 + 2 ^ (k + 1))) * (2 ^ (k + 3)) + t ^ 2 * (2 ^ (2 * (k + 2))) := by
        have h4 : 2 * (1 + 2 ^ (k + 1)) * (t * (2 ^ (k + 2))) = (t * (1 + 2 ^ (k + 1))) * (2 ^ (k + 3)) := by
          ring_nf
        have h5 : (t * (2 ^ (k + 2))) ^ 2 = t ^ 2 * (2 ^ (2 * (k + 2))) := by ring
        rw [h4, h5]
  have h6 : k ≥ 1 := hk
  have h7 : 2 * (k + 2) ≥ k + 3 := by omega
  have h8 : (2 ^ (k + 3) : ℤ) ∣ ((t * (1 + 2 ^ (k + 1))) * (2 ^ (k + 3)) + t ^ 2 * (2 ^ (2 * (k + 2)))) := by
    have h9 : (2 ^ (k + 3) : ℤ) ∣ ((t * (1 + 2 ^ (k + 1))) * (2 ^ (k + 3))) := by
      use t * (1 + 2 ^ (k + 1))
      ring
    have h10 : (2 ^ (k + 3) : ℤ) ∣ (t ^ 2 * (2 ^ (2 * (k + 2)))) := by
      have h11 : (k + 3) ≤ 2 * (k + 2) := by omega
      have h12 : (2 ^ (k + 3) : ℤ) ∣ (2 ^ (2 * (k + 2)) : ℤ) := by
        apply pow_dvd_pow
        omega
      exact dvd_mul_of_dvd_right h12 (t ^ 2)
    exact dvd_add h9 h10
  have h13 : (x ^ 2 - (1 + 2 ^ (k + 1)) ^ 2) % (2 ^ (k + 3)) = 0 := by
    have h14 : x ^ 2 - (1 + 2 ^ (k + 1)) ^ 2 = (t * (1 + 2 ^ (k + 1))) * (2 ^ (k + 3)) + t ^ 2 * (2 ^ (2 * (k + 2))) := by
      linarith [h_eq]
    rw [h14]
    simpa [Int.emod_eq_zero_of_dvd] using h8
  have h15 : (x ^ 2) % (2 ^ (k + 3)) = ((1 + 2 ^ (k + 1)) ^ 2) % (2 ^ (k + 3)) := by
    simpa [Int.emod_eq_emod_iff_emod_sub_eq_zero] using h13
  have h21 : ((1 + 2 ^ (k + 1) : ℤ) ^ 2) = ((1 + 2 ^ (k + 1) : ℤ)) * (1 + 2 ^ (k + 1) : ℤ) := by
    ring
  have h19 : (((1 + 2 ^ (k + 1) : ℤ)) * (1 + 2 ^ (k + 1) : ℤ)) % (2 ^ (k + 3)) = ((1 + 2 ^ (k + 2) : ℤ) % (2 ^ (k + 3))) := round1_h_step2 k hk
  have h20 : (((1 + 2 ^ (k + 1) : ℤ) ^ 2) % (2 ^ (k + 3))) = ((1 + 2 ^ (k + 2) : ℤ) % (2 ^ (k + 3))) := by
    have h22 : ((1 + 2 ^ (k + 1) : ℤ) ^ 2) = ((1 + 2 ^ (k + 1) : ℤ)) * (1 + 2 ^ (k + 1) : ℤ) := h21
    simpa [h22] using h19
  simpa [h15] using h20

theorem round1_lemma6_product_T_congruence (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (lemma5_mod_powers_of_2 : ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (b (n + 2 ^ s) - b n) % (2 ^ (s + 1)) = 0):
  ∀ (k : ℕ), k ≥ 1 → (∏ i ∈ Finset.range (2 ^ k), (4 * b i + 1)) % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2)) := by
  let f : ℕ → ℤ := fun i => 4 * b i + 1
  have h_main : ∀ (k : ℕ), (k ≥ 1 → (∏ i ∈ Finset.range (2 ^ k), f i) % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2))) := by
    intro k
    induction k with
    | zero =>
      intro h
      exfalso
      linarith
    | succ k ih =>
      intro h
      by_cases h_k : k = 0
      ·
        subst h_k
        norm_num [f, Finset.prod_range_succ, hb0, hb]
      ·
        have h_k_ge_1 : k ≥ 1 := by omega
        have h_ih' : (∏ i ∈ Finset.range (2 ^ k), f i) % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2)) := ih h_k_ge_1
        let m := 2 ^ k
        let N := (2 ^ (k + 3) : ℤ)
        let P₁ := ∏ i ∈ Finset.range m, f i
        let P₂ := ∏ i ∈ Finset.range m, f (m + i)
        have h_prod : (∏ i ∈ Finset.range (2 ^ (k + 1)), f i) = P₁ * P₂ := by
          have h1 : 2 ^ (k + 1) = m + m := by
            simp [m]
            ring
          rw [h1]
          have h2 : (∏ i ∈ Finset.range (m + m), f i) = (∏ i ∈ Finset.range m, f i) * (∏ i ∈ Finset.range m, f (m + i)) := by
            rw [Finset.prod_range_add]
          simpa [P₁, P₂] using h2
        have h2 : ∀ (i : ℕ), (f (m + i)) % N = (f i) % N := by
          intro i
          have h3 : m = 2 ^ k := by rfl
          have h4 : m + i = i + 2 ^ k := by
            rw [h3]
            omega
          rw [h4]
          have h5 := round1_h_main_2647bd b lemma5_mod_powers_of_2 k h_k_ge_1 i
          simpa [f, N, h3] using h5
        let x : ℤ := P₁ % N
        have h3 : (P₂ % N) = x := by
          have h4 : (P₂ % N) = (∏ i ∈ Finset.range m, f (m + i)) % N := by simp [P₂]
          rw [h4]
          have h5 : (∏ i ∈ Finset.range m, f (m + i)) % N = (∏ i ∈ Finset.range m, (f (m + i) % N)) % N := by
            rw [Finset.prod_int_mod]
          rw [h5]
          have h6 : (∏ i ∈ Finset.range m, (f (m + i) % N)) = ∏ i ∈ Finset.range m, (f i % N) := by
            apply Finset.prod_congr rfl
            intro i _
            exact h2 i
          rw [h6]
          have h7 : (∏ i ∈ Finset.range m, (f i % N)) % N = (∏ i ∈ Finset.range m, f i) % N := by
            have h8 : (∏ i ∈ Finset.range m, (f i % N)) % N = (∏ i ∈ Finset.range m, f i) % N := by
              simp [Finset.prod_int_mod]
            exact h8
          rw [h7]
        have hdiv : (2 ^ (k + 2) : ℤ) ∣ N := by
          use (2 : ℤ)
          simp [N]
          ring_nf
        have h41 : (x % (2 ^ (k + 2) : ℤ)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2) : ℤ) := by
          have h51 : (x % (2 ^ (k + 2) : ℤ)) = ((P₁ % N) % (2 ^ (k + 2) : ℤ)) := by simp [x]
          rw [h51]
          have h52 : ((P₁ % N) % (2 ^ (k + 2) : ℤ)) = (P₁ % (2 ^ (k + 2) : ℤ)) := by
            exact Int.emod_emod_of_dvd P₁ hdiv
          rw [h52] ; exact h_ih'
        have h5 : (x ^ 2) % N = (1 + 2 ^ (k + 2)) % N := by
          have hN : N = (2 ^ (k + 3)) := by
            simp [N]
          rw [hN]
          exact round1_h_missing k h_k_ge_1 x h41
        have h61 : ((P₁ * P₂) % N) = (x ^ 2) % N := by
          have h71 : ((P₁ * P₂) % N) = ((P₁ % N) * (P₂ % N)) % N := by
            simp [Int.mul_emod]
          rw [h71]
          have h72 : (P₂ % N) = x := h3
          rw [h72]
          simp [x] ; ring_nf
        have h9 : ((P₁ * P₂) % N) = (1 + 2 ^ (k + 2)) % N := by
          rw [h61] ; exact h5
        simpa [h_prod, N] using h9
  exact h_main

lemma round1_h_main_0e3a9e (b : ℕ → ℤ)
  (lemma5_mod_powers_of_2 : ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (b (n + 2 ^ s) - b n) % (2 ^ (s + 1)) = 0):
  ∀ (k : ℕ), k ≥ 1 → ∀ (i : ℕ), (2 * (b (2 ^ k + i) - b i)) % (2 ^ (k + 2)) = 0 := by
  intro k hk i
  have h2 : (b (i + 2 ^ k) - b i) % (2 ^ (k + 1)) = 0 := lemma5_mod_powers_of_2 k hk i
  have h3 : (2 ^ (k + 1) : ℤ) ∣ (b (i + 2 ^ k) - b i) := by
    have h31 : (b (i + 2 ^ k) - b i) % (2 ^ (k + 1)) = 0 := h2
    exact Int.dvd_of_emod_eq_zero (lemma5_mod_powers_of_2 k hk i)
  rcases h3 with ⟨m, hm⟩
  have h41 : b (i + 2 ^ k) - b i = (2 ^ (k + 1) : ℤ) * m := hm
  have h4 : 2 * (b (i + 2 ^ k) - b i) = m * (2 ^ (k + 2) : ℤ) := by
    calc
      2 * (b (i + 2 ^ k) - b i) = 2 * ((2 ^ (k + 1) : ℤ) * m) := by rw [h41]
      _ = (2 ^ (k + 1) : ℤ) * (2 * m) := by ring
      _ = m * (2 ^ (k + 2) : ℤ) := by
        have h5 : (2 ^ (k + 1) : ℤ) * (2 * m) = m * (2 ^ (k + 2) : ℤ) := by
          ring_nf
        exact h5
  have h5 : (2 * (b (i + 2 ^ k) - b i)) % (2 ^ (k + 2) : ℤ) = 0 := by
    rw [h4]
    simp
  simpa [add_comm (2 ^ k) i] using h5

lemma round1_h_term_congr (b : ℕ → ℤ)
  (h_main : ∀ (k : ℕ), k ≥ 1 → ∀ (i : ℕ), (2 * (b (2 ^ k + i) - b i)) % (2 ^ (k + 2)) = 0):
  ∀ (k : ℕ), k ≥ 1 → ∀ (i : ℕ), (2 * (b (2 ^ k + i) + b i) + 1) % (2 ^ (k + 2)) = (4 * b i + 1) % (2 ^ (k + 2)) := by
  intro k hk i
  have h6 : (2 * (b (2 ^ k + i) - b i)) % (2 ^ (k + 2) : ℤ) = 0 := h_main k hk i
  have h7 : (2 * (b (2 ^ k + i) + b i) + 1 : ℤ) - (4 * b i + 1 : ℤ) = 2 * (b (2 ^ k + i) - b i) := by
    ring
  have h8 : ((2 * (b (2 ^ k + i) + b i) + 1 : ℤ) - (4 * b i + 1 : ℤ)) % (2 ^ (k + 2) : ℤ) = 0 := by
    rw [h7]
    exact h6
  have h9 : (2 * (b (2 ^ k + i) + b i) + 1 : ℤ) % (2 ^ (k + 2) : ℤ) = (4 * b i + 1 : ℤ) % (2 ^ (k + 2) : ℤ) := by
    simpa [Int.emod_eq_emod_iff_emod_sub_eq_zero] using h8
  exact_mod_cast h9

theorem round1_lemma7_product_Q_congruence (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (lemma5_mod_powers_of_2 : ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (b (n + 2 ^ s) - b n) % (2 ^ (s + 1)) = 0)
  (lemma6_prod_T_cong : ∀ (k : ℕ), k ≥ 1 → (∏ i ∈ Finset.range (2 ^ k), (4 * b i + 1)) % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2))):
  ∀ (k : ℕ), k ≥ 1 → (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2)) := by
  have h_main : ∀ (k : ℕ), k ≥ 1 → ∀ (i : ℕ), (2 * (b (2 ^ k + i) - b i)) % (2 ^ (k + 2)) = 0 :=
    round1_h_main_0e3a9e b lemma5_mod_powers_of_2
  have h_term_congr : ∀ (k : ℕ), k ≥ 1 → ∀ (i : ℕ), (2 * (b (2 ^ k + i) + b i) + 1) % (2 ^ (k + 2)) = (4 * b i + 1) % (2 ^ (k + 2)) :=
    round1_h_term_congr b h_main
  intro k hk
  have h11 : ∀ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1) % (2 ^ (k + 2)) = (4 * b i + 1) % (2 ^ (k + 2)) := by
    intro i _
    exact h_term_congr k hk i
  have h12 : (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) % (2 ^ (k + 2)) = (∏ i ∈ Finset.range (2 ^ k), ((2 * (b (2 ^ k + i) + b i) + 1) % (2 ^ (k + 2)))) % (2 ^ (k + 2)) := by
    rw [Finset.prod_int_mod]
  have h14 : (∏ i ∈ Finset.range (2 ^ k), ((2 * (b (2 ^ k + i) + b i) + 1) % (2 ^ (k + 2)))) = ∏ i ∈ Finset.range (2 ^ k), ((4 * b i + 1) % (2 ^ (k + 2))) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact h11 i hi
  have h15 : (∏ i ∈ Finset.range (2 ^ k), ((2 * (b (2 ^ k + i) + b i) + 1) % (2 ^ (k + 2)))) % (2 ^ (k + 2)) = (∏ i ∈ Finset.range (2 ^ k), ((4 * b i + 1) % (2 ^ (k + 2)))) % (2 ^ (k + 2)) := by
    rw [h14]
  have h16 : (∏ i ∈ Finset.range (2 ^ k), (4 * b i + 1)) % (2 ^ (k + 2)) = (∏ i ∈ Finset.range (2 ^ k), ((4 * b i + 1) % (2 ^ (k + 2)))) % (2 ^ (k + 2)) := by
    rw [Finset.prod_int_mod]
  have h_final : (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) % (2 ^ (k + 2)) = (∏ i ∈ Finset.range (2 ^ k), (4 * b i + 1)) % (2 ^ (k + 2)) := by
    rw [h12, h15, h16]
  rw [h_final]
  exact lemma6_prod_T_cong k hk

lemma round1_h2 (b : ℕ → ℤ)
  (k : ℕ)
  (m : ℤ)
  (hm_odd : m % 2 = 1):
  padicValInt 2 m = 0 := by
  have h21 : ¬ (2 : ℤ) ∣ m := by
    intro h
    have h22 : (m % 2) = 0 := by
      omega
    omega
  exact padicValInt.eq_zero_of_not_dvd (p := 2) (h := h21)

lemma round1_h3_aux2 (x : ℤ)
  (hx : x ≠ 0):
  ∀ (n : ℕ), padicValInt 2 (x ^ n) = n * padicValInt 2 x := by
  have h2prime : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h4 : x ^ (n + 1) = x ^ n * x := by ring
    rw [h4]
    have h5 : padicValInt 2 (x ^ n * x) = padicValInt 2 (x ^ n) + padicValInt 2 x := by
      apply padicValInt.mul (p := 2)
      <;> positivity
    rw [h5, ih]
    ring

lemma round1_h3_85b877 (b : ℕ → ℤ)
  (k : ℕ)
  (m : ℤ):
  padicValInt 2 ((2 : ℤ) ^ (k + 1)) = k + 1 := by
  have h31 : padicValInt 2 (2 : ℤ) = 1 := by
    dsimp [padicValInt]
    norm_num
  have h32 : ∀ (n : ℕ), padicValInt 2 ((2 : ℤ) ^ n) = n * padicValInt 2 (2 : ℤ) :=
    round1_h3_aux2 (x := (2 : ℤ)) (by norm_num)
  have h33 := h32 (k + 1)
  rw [h33, h31]
  ring

lemma round1_h5 (b : ℕ → ℤ)
  (k : ℕ)
  (hk : k ≥ 1)
  (h1 : ∀ k : ℕ, k ≥ 1 → padicValInt 2 (b (2 ^ k)) = k + 1):
  b (2 ^ k) ≠ 0 := by
  by_contra h
  have h6 : padicValInt 2 (b (2 ^ k)) = 0 := by
    rw [h]
    simp
  have h7 : padicValInt 2 (b (2 ^ k)) = k + 1 := h1 k hk
  rw [h7] at h6
  omega

lemma round1_hm_ne_zero (m : ℤ)
  (hm_odd : m % 2 = 1):
  m ≠ 0 := by
  intro h
  rw [h] at hm_odd
  norm_num at hm_odd

theorem round1_final_step (b : ℕ → ℤ)
  (k : ℕ)
  (hk : k ≥ 1)
  (h1 : ∀ k : ℕ, k ≥ 1 → padicValInt 2 (b (2 ^ k)) = k + 1)
  (m : ℤ)
  (hm_odd : m % 2 = 1)
  (h_eq : b (2 ^ (k + 1)) - 2 * b (2 ^ k) = (2 : ℤ) ^ (k + 1) * b (2 ^ k) * m):
  padicValInt 2 (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) = 2 * k + 2 := by
  have h2 : padicValInt 2 m = 0 := round1_h2 b k m hm_odd
  have h3 : padicValInt 2 ((2 : ℤ) ^ (k + 1)) = k + 1 := round1_h3_85b877 b k m
  have h4 : padicValInt 2 (b (2 ^ k)) = k + 1 := h1 k hk
  have h5 : b (2 ^ k) ≠ 0 := round1_h5 b k hk h1
  have hm_ne_zero : m ≠ 0 := round1_hm_ne_zero m hm_odd
  have h_main : padicValInt 2 (((2 : ℤ) ^ (k + 1)) * (b (2 ^ k)) * m) =
      padicValInt 2 ((2 : ℤ) ^ (k + 1)) + padicValInt 2 (b (2 ^ k)) + padicValInt 2 m := by
    have h2prime : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    have h_mul1 : padicValInt 2 (((2 : ℤ) ^ (k + 1)) * (b (2 ^ k))) =
        padicValInt 2 ((2 : ℤ) ^ (k + 1)) + padicValInt 2 (b (2 ^ k)) := by
      apply padicValInt.mul (p := 2)
      <;> positivity
    have h_mul2 : padicValInt 2 ((((2 : ℤ) ^ (k + 1)) * (b (2 ^ k))) * m) =
        padicValInt 2 (((2 : ℤ) ^ (k + 1)) * (b (2 ^ k))) + padicValInt 2 m := by
      apply padicValInt.mul (p := 2)
      <;> positivity
    rw [h_mul2, h_mul1]
  have h_final : padicValInt 2 (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) =
      padicValInt 2 (((2 : ℤ) ^ (k + 1)) * (b (2 ^ k)) * m) := by
    rw [h_eq]
  rw [h_final, h_main, h3, h4, h2]
  ring

theorem round1_lemma5_general (u : ℕ → ℤ)
  (x : ℤ)
  (h_u0 : u 0 = x)
  (h_u : ∀ n, u (n + 1) = 2 * (u n) ^ 2 + u n + 1)
  (k : ℕ)
  (hk : k ≥ 1):
  (2 ^ (k + 2) : ℤ) ∣ (u (2 ^ k) - (x + 2 ^ (k + 1))) := by
  set g : ℕ → ℤ → ℤ := fun (n : ℕ) (t : ℤ) =>
    Nat.rec (fun (t : ℤ) => t) (fun (n : ℕ) (fn : ℤ → ℤ) (t : ℤ) => 2 * (fn t) ^ 2 + (fn t) + 1) n t with hg_def
  have hg1 : ∀ (t : ℤ), g 0 t = t := by
    intro t
    simp [hg_def]
  have hg2 : ∀ (n : ℕ) (t : ℤ), g (n + 1) t = 2 * (g n t) ^ 2 + (g n t) + 1 := by
    intro n t
    simp [hg_def]
  have h_add : ∀ (n m : ℕ) (t : ℤ), g (n + m) t = g n (g m t) := by
    exact round1_lemma1 g hg1 hg2
  have h_lemma_A : ∀ (n : ℕ) (s h : ℤ), h % 2 = 0 → ∃ q : ℤ, q % 2 = 1 ∧ q % 4 = 1 ∧ g n (s + h) - g n s = h * q := by
    exact round1_lemma2 g hg1 hg2 h_add
  have h_base : ∀ (t : ℤ), ∃ b : ℤ, g 2 t = t + 4 + 8 * b := by
    exact round1_lemma3 g hg1 hg2
  have h_step : ∀ (m : ℕ), m ≥ 1 → (∀ (t : ℤ), ∃ b : ℤ, g (2 ^ m) t = t + (2 ^ (m + 1)) + (2 ^ (m + 2)) * b) → (∀ (t : ℤ), ∃ c : ℤ, g (2 ^ (m + 1)) t = t + (2 ^ (m + 2)) + (2 ^ (m + 3)) * c) := by
    exact round1_lemma4 g hg1 hg2 h_add h_lemma_A
  have h_induction : ∀ (k : ℕ), k ≥ 1 → ∀ (t : ℤ), ∃ b : ℤ, g (2 ^ k) t = t + (2 ^ (k + 1)) + (2 ^ (k + 2)) * b := by
    intro k hk1
    induction k with
    | zero =>
      exfalso
      linarith
    | succ k ih =>
      by_cases h : k = 0
      ·
        subst h
        intro t
        have h_base1 := h_base t
        rcases h_base1 with ⟨b, hb⟩
        refine' ⟨b, _⟩
        norm_num at *
        ring_nf at * ; norm_num at * ; linarith
      ·
        have hk2 : k ≥ 1 := by
          omega
        have ih1 := ih hk2
        have h_step1 := h_step k hk2 ih1
        intro t
        have h5 := h_step1 t
        rcases h5 with ⟨c, hc⟩
        refine' ⟨c, _⟩
        simp [pow_succ] at *
        ring_nf at *
        norm_num at *
        linarith
  have h51 : ∃ b : ℤ, g (2 ^ k) x = x + (2 ^ (k + 1)) + (2 ^ (k + 2)) * b := by
    have h511 := h_induction k hk
    exact h511 x
  have h52 : ∀ (n : ℕ), u n = g n x := by
    exact round1_lemma5 u x h_u0 h_u g hg1 hg2
  rcases h51 with ⟨b, h511⟩
  have h53 : u (2 ^ k) = g (2 ^ k) x := by
    have h531 := h52 (2 ^ k)
    simpa using h531
  have h54 : u (2 ^ k) = x + (2 ^ (k + 1)) + (2 ^ (k + 2)) * b := by
    linarith [h53, h511]
  have h_final : (u (2 ^ k) - (x + 2 ^ (k + 1))) = (2 ^ (k + 2)) * b := by
    linarith [h54]
  use b

lemma round1_h_main_8fd445 (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (h_prod_formula : ∀ (n r : ℕ), b (n + r) - b n = b r * (∏ i ∈ Finset.range n, (2 * (b (r + i) + b i) + 1)))
  (h_lemma2 : ∀ k : ℕ, k ≥ 1 → padicValInt 2 (b (2 ^ k)) = k + 1):
  ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (2 ^ (s + 1) : ℤ) ∣ (b (n + 2 ^ s) - b n) := by
  intro s hs n
  have h1 : padicValInt 2 (b (2 ^ s)) = s + 1 := h_lemma2 s hs
  have h2 : (2 : ℤ) ^ (s + 1) ∣ b (2 ^ s) := by
    have h21 : (2 : ℤ) ^ (s + 1) ∣ b (2 ^ s) := by
      apply (padicValInt_dvd_iff (s + 1) (b (2 ^ s))).mpr
      right
      rw [h1]
    exact h21
  have h3 : b (n + 2 ^ s) - b n = b (2 ^ s) * (∏ i ∈ Finset.range n, (2 * (b (2 ^ s + i) + b i) + 1)) := by
    apply h_prod_formula n (2 ^ s)
  rw [h3]
  exact dvd_mul_of_dvd_left h2 _

theorem round1_lemma5_mod_powers_of_2_from_product_formula_and_lemma2 (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (h_prod_formula : ∀ (n r : ℕ), b (n + r) - b n = b r * (∏ i ∈ Finset.range n, (2 * (b (r + i) + b i) + 1)))
  (h_lemma2 : ∀ k : ℕ, k ≥ 1 → padicValInt 2 (b (2 ^ k)) = k + 1):
  ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (b (n + 2 ^ s) - b n) % (2 ^ (s + 1)) = 0 := by
  have h_main : ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (2 ^ (s + 1) : ℤ) ∣ (b (n + 2 ^ s) - b n) :=
    round1_h_main_8fd445 b hb0 hb h_prod_formula h_lemma2
  intro s hs n
  have h4 : (2 ^ (s + 1) : ℤ) ∣ (b (n + 2 ^ s) - b n) := h_main s hs n
  simpa [Int.emod_eq_zero_of_dvd] using h4

theorem round1_lemma2_191c1c (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1):
  ∀ k : ℕ, k ≥ 1 → padicValInt 2 (b (2 ^ k)) = k + 1 := by
  intro k hk
  have h1 : (2 ^ (k + 2) : ℤ) ∣ (b (2 ^ k) - (0 + 2 ^ (k + 1))) := by
    exact round1_lemma5_general b 0 hb0 hb k hk
  have h11 : (2 ^ (k + 2) : ℤ) ∣ (b (2 ^ k) - (2 ^ (k + 1))) := by simpa using h1
  have h12 : (2 ^ (k + 1) : ℤ) ∣ b (2 ^ k) := by
    have h121 : (2 ^ (k + 1) : ℤ) ∣ (2 ^ (k + 2) : ℤ) := by
      use 2
      ring_nf
    have h122 : (2 ^ (k + 1) : ℤ) ∣ (b (2 ^ k) - (2 ^ (k + 1))) := dvd_trans h121 h11
    have h123 : (2 ^ (k + 1) : ℤ) ∣ (2 ^ (k + 1) : ℤ) := by
      exact dvd_refl _
    have h124 : (2 ^ (k + 1) : ℤ) ∣ (b (2 ^ k) - (2 ^ (k + 1))) + (2 ^ (k + 1) : ℤ) := by
      apply Int.dvd_add h122 h123
    have h125 : (b (2 ^ k) - (2 ^ (k + 1))) + (2 ^ (k + 1) : ℤ) = b (2 ^ k) := by ring
    rw [h125] at h124
    exact h124
  have h13 : ¬((2 ^ (k + 2) : ℤ) ∣ b (2 ^ k)) := by
    by_contra h131
    have h132 : (2 ^ (k + 2) : ℤ) ∣ (b (2 ^ k) - (2 ^ (k + 1))) := h11
    have h133 : (2 ^ (k + 2) : ℤ) ∣ b (2 ^ k) := h131
    have h134 : (2 ^ (k + 2) : ℤ) ∣ (b (2 ^ k)) - (b (2 ^ k) - (2 ^ (k + 1))) := by
      apply Int.dvd_sub h133 h132
    have h135 : (b (2 ^ k)) - (b (2 ^ k) - (2 ^ (k + 1))) = (2 ^ (k + 1) : ℤ) := by ring
    rw [h135] at h134
    have h136 : (2 ^ (k + 2) : ℤ) ∣ (2 ^ (k + 1) : ℤ) := h134
    have h137 : (2 ^ (k + 2) : ℤ) > (2 ^ (k + 1) : ℤ) := by
      have h1371 : k ≥ 0 := by linarith
      have h1372 : (2 ^ (k + 2) : ℤ) = 2 * (2 ^ (k + 1)) := by
        ring_nf
      rw [h1372]
      have h1373 : (2 ^ (k + 1) : ℤ) > 0 := by positivity
      linarith
    have h138 : (2 ^ (k + 2) : ℤ) ≤ (2 ^ (k + 1) : ℤ) := by
      apply Int.le_of_dvd (by positivity) h136
    linarith
  have h14 := round1_padicValInt_lemma k (b (2 ^ k)) h12 h13
  exact h14

theorem round1_exists_m (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1):
  ∀ k : ℕ, k ≥ 1 → ∃ m : ℤ, m % 2 = 1 ∧ b (2 ^ (k + 1)) - 2 * b (2 ^ k) = (2 : ℤ) ^ (k + 1) * b (2 ^ k) * m := by
  have h_prod_formula : ∀ (n r : ℕ), b (n + r) - b n = b r * (∏ i ∈ Finset.range n, (2 * (b (r + i) + b i) + 1)) := by
    exact round1_lemma_product_formula b hb0 hb
  have h_lemma5 : ∀ (s : ℕ), s ≥ 1 → ∀ (n : ℕ), (b (n + 2 ^ s) - b n) % (2 ^ (s + 1)) = 0 := by
    exact round1_lemma5_mod_powers_of_2_from_product_formula_and_lemma2 b hb0 hb h_prod_formula (round1_lemma2_191c1c b hb0 hb)
  have h_lemma6 : ∀ (k1 : ℕ), k1 ≥ 1 → (∏ i ∈ Finset.range (2 ^ k1), (4 * b i + 1)) % (2 ^ (k1 + 2)) = (1 + 2 ^ (k1 + 1)) % (2 ^ (k1 + 2)) := by
    exact round1_lemma6_product_T_congruence b hb0 hb h_lemma5
  have h_lemma7 : ∀ (k1 : ℕ), k1 ≥ 1 → (∏ i ∈ Finset.range (2 ^ k1), (2 * (b (2 ^ k1 + i) + b i) + 1)) % (2 ^ (k1 + 2)) = (1 + 2 ^ (k1 + 1)) % (2 ^ (k1 + 2)) := by
    exact round1_lemma7_product_Q_congruence b hb0 hb h_lemma5 h_lemma6
  intro k hk
  have h71 : (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) % (2 ^ (k + 2)) = (1 + 2 ^ (k + 1)) % (2 ^ (k + 2)) := h_lemma7 k hk
  have h91 : ∃ m : ℤ, (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) - 1 = (2 : ℤ) ^ (k + 1) * m ∧ m % 2 = 1 := by
    exact round1_helper_congruence_to_odd k (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) hk h71
  rcases h91 with ⟨m, h911, h912⟩
  have h92 : b (2 ^ (k + 1)) - b (2 ^ k) = b (2 ^ k) * (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) := by
    have h101 := h_prod_formula (2 ^ k) (2 ^ k)
    have h102 : (2 ^ k + 2 ^ k) = 2 ^ (k + 1) := by
      ring_nf
    rw [h102] at h101
    exact h101
  have h93 : (∏ i ∈ Finset.range (2 ^ k), (2 * (b (2 ^ k + i) + b i) + 1)) = (2 : ℤ) ^ (k + 1) * m + 1 := by
    linarith
  have h94 : b (2 ^ (k + 1)) - b (2 ^ k) = b (2 ^ k) * ((2 : ℤ) ^ (k + 1) * m + 1) := by
    rw [h92, h93]
  have h95 : b (2 ^ (k + 1)) - b (2 ^ k) = (2 : ℤ) ^ (k + 1) * b (2 ^ k) * m + b (2 ^ k) := by
    calc
      b (2 ^ (k + 1)) - b (2 ^ k) = b (2 ^ k) * ((2 : ℤ) ^ (k + 1) * m + 1) := h94
      _ = b (2 ^ k) * ((2 : ℤ) ^ (k + 1) * m) + b (2 ^ k) * 1 := by ring
      _ = (2 : ℤ) ^ (k + 1) * b (2 ^ k) * m + b (2 ^ k) := by ring
  have h96 : b (2 ^ (k + 1)) - 2 * b (2 ^ k) = (2 : ℤ) ^ (k + 1) * b (2 ^ k) * m := by
    linarith
  exact ⟨m, h912, h96⟩

theorem putnam_2025_a6 (b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hb : ∀ n, b (n + 1) = 2 * b n ^ 2 + b n + 1)
  (k : ℕ)
  (hk : k ≥ 1):
  padicValInt 2 (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) = 2 * k + 2 := by
      have h1 := round1_lemma2_191c1c b hb0 hb
      have h2 := round1_exists_m b hb0 hb
      rcases h2 k hk with ⟨m, hm_odd, h_eq⟩
      have h4 := round1_final_step b k hk h1 m hm_odd h_eq
      exact h4

end Putnam2025A6
