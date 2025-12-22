import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered

set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open BigOperators Real Nat Topology Rat

namespace Putnam2025B6

theorem rpow_fourth_root_of_fourth_power (x : ℝ)
  (hx : x ≥ 0):
  (x ^ 4) ^ (1 / 4 : ℝ) = x := by
  have h1 : (x ^ 4 : ℝ) = x ^ (4 : ℝ) := by
    norm_cast
  rw [h1]
  have h2 : x ^ (4 * (1 / 4 : ℝ)) = (x ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_mul hx (4 : ℝ) (1 / 4 : ℝ)
  have h3 : (4 : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
  have h4 : x ^ (4 * (1 / 4 : ℝ)) = x := by
    rw [h3]
    simp [Real.rpow_one]
  rw [← h2, h4]

theorem diff_of_squares_is_twice_n_plus_one (g : ℕ+ → ℕ+)
  (hg : ∀ (n : ℕ+), (g n : ℕ) = (n : ℕ) ^ 2)
  (n : ℕ+):
  (g (n + 1) : ℝ) - (g n : ℝ) = 2 * (n : ℝ) + 1 := by
  let m := (n : ℕ)
  have h1 : (g (n + 1) : ℕ) = (m + 1)^2 := by
    simpa [m] using hg (n + 1)
  have h2 : (g n : ℕ) = m^2 := by
    simpa [m] using hg n
  have h3 : ((g (n + 1) : ℝ)) = (( (m + 1 : ℕ)^2 : ℝ)) := by
    exact_mod_cast h1
  have h4 : ((g n : ℝ)) = (( (m : ℕ)^2 : ℝ)) := by
    exact_mod_cast h2
  rw [h3, h4]
  simp [pow_two]
  ring_nf
  norm_cast

theorem square_of_square_is_fourth_power (g : ℕ+ → ℕ+)
  (hg : ∀ (n : ℕ+), (g n : ℕ) = (n : ℕ) ^ 2)
  (n : ℕ+):
  (g (g n) : ℝ) = (n : ℝ) ^ 4 := by
  have h1 : (g n : ℕ) = (n : ℕ) ^ 2 := hg n
  have h2 : (g (g n) : ℕ) = ((g n : ℕ) ^ 2) := by
    exact hg (g n)
  have h3 : (g (g n) : ℕ) = ((n : ℕ) ^ 2) ^ 2 := by
    rw [h2, h1]
  have h4 : (g (g n) : ℕ) = (n : ℕ) ^ 4 := by
    rw [h3]
    ring
  have h5 : (g (g n) : ℝ) = ((n : ℝ) ^ 4) := by
    exact_mod_cast h4
  exact h5

theorem exists_pnat_to_pnat_square_function :
  ∃ g : ℕ+ → ℕ+, ∀ (n : ℕ+), (g n : ℕ) = (n : ℕ) ^ 2 := by
  let g : ℕ+ → ℕ+ := fun n =>
    ⟨(n : ℕ) ^ 2, by
      have h : (0 : ℕ) < (n : ℕ) := n.pos
      positivity⟩
  have h_main : ∀ (n : ℕ+), (g n : ℕ) = (n : ℕ) ^ 2 := by
    intro n
    simp [g]
  exact ⟨g, h_main⟩

lemma round1_h_main (n : ℕ+):
  (n : ℝ) ≥ 1 := by
  exact_mod_cast n.pos

theorem twice_n_plus_one_ge_n_for_pnat (n : ℕ+):
  2 * (n : ℝ) + 1 ≥ (n : ℝ) := by
  have h1 : (n : ℝ) ≥ 1 := round1_h_main n
  linarith

theorem pnat_coe_real_nonneg (n : ℕ+):
  (n : ℝ) ≥ 0 := by
  have h₁ : (n : ℝ) ≥ 0 := by
    exact_mod_cast Nat.zero_le (n.val)
  exact h₁

theorem g_ge_n (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r):
  ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ) := by
  have h_main : ∀ (k : ℕ), (hpos : 0 < k) → (g ⟨k, hpos⟩ : ℕ) ≥ k := by
    intro k
    induction k with
    | zero =>
      intro hpos
      exfalso
      linarith
    | succ k ih =>
      intro h
      by_cases h_k : k = 0
      ·
        subst h_k
        have h₁ : 0 < 1 := by norm_num
        have h₂ : (g (⟨1, h₁⟩) : ℕ) ≥ 1 := (g (⟨1, h₁⟩)).pos
        simpa using h₂
      ·
        have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k
        have ih' : (g ⟨k, h_k_pos⟩ : ℕ) ≥ k := ih h_k_pos
        by_contra h_contra
        have h₁ : (g ⟨k + 1, h⟩ : ℕ) < k + 1 := by exact Nat.lt_of_not_ge h_contra
        have h₂ : (g ⟨k + 1, h⟩ : ℝ) < ((k : ℝ) + 1) := by exact_mod_cast h₁
        have h₃ : (g ⟨k, h_k_pos⟩ : ℝ) ≥ (k : ℝ) := by exact_mod_cast ih'
        have h₄ : (g ⟨k + 1, h⟩ : ℝ) - (g ⟨k, h_k_pos⟩ : ℝ) < 1 := by linarith
        have h₅ : (g ⟨k + 1, h⟩ : ℝ) - (g ⟨k, h_k_pos⟩ : ℝ) ≥ (g (g ⟨k, h_k_pos⟩) : ℝ) ^ r := h_ineq ⟨k, h_k_pos⟩
        have h₆ : (g (g ⟨k, h_k_pos⟩) : ℝ) ^ r < 1 := by linarith
        have h₇ : (0 : ℝ) < r := by linarith
        have h₈ : (g (g ⟨k, h_k_pos⟩) : ℝ) ≥ 1 := by
          exact_mod_cast (g (g ⟨k, h_k_pos⟩)).pos
        have h₉ : (g (g ⟨k, h_k_pos⟩) : ℝ) ^ r ≥ 1 := by
          apply one_le_rpow
          <;> linarith
        linarith
  intro n
  have h₁ : 0 < (n : ℕ) := n.pos
  exact h_main (n : ℕ) h₁

theorem exists_sequence_with_recurrence (r : ℝ):
  ∃ (e : ℕ → ℝ), e 0 = 1 ∧ (∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1) := by
  let e : ℕ → ℝ := fun n => Nat.recOn n 1 (fun m ih => r * (ih)^2 + 1)
  have h1 : e 0 = 1 := by
    simp [e]
  have h2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1 := by
    intro m
    simp [e]
  exact ⟨e, ⟨h1, h2⟩⟩

theorem exists_natural_number_for_arithmetic_progression_exceeds (δ : ℝ)
  (h_δ_pos : δ > 0)
  (k : ℝ):
  ∃ (M : ℕ), (1 : ℝ) + (M : ℝ) * δ > k := by
  have h1 : ∃ (M : ℕ), (M : ℝ) > (k - 1) / δ := by
    exact exists_nat_gt ((k - 1) / δ)
  rcases h1 with ⟨M, hM⟩
  use M
  have h2 : (M : ℝ) * δ > ((k - 1) / δ) * δ := by
    exact mul_lt_mul_of_pos_right hM h_δ_pos
  have h3 : ((k - 1) / δ) * δ = k - 1 := by
    field_simp [h_δ_pos.ne']
  rw [h3] at h2
  linarith

lemma round1_h_main_f0503c (r : ℝ)
  (hr : r > 1/4)
  (e : ℕ → ℝ)
  (he1 : e 0 = 1)
  (he2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1):
  ∀ (m : ℕ), e m ≥ 1 := by
  intro m
  induction m with
  | zero =>
    norm_num [he1]
  | succ m ih =>
    have h1 : (e m)^2 ≥ 1 := by
      have h11 : e m ≥ 1 := ih
      nlinarith
    have h2 : r * (e m)^2 ≥ r := by
      have h21 : r > 0 := by linarith
      nlinarith
    have h3 : r * (e m)^2 + 1 ≥ 1 := by
      linarith
    have h4 : e (m + 1) = r * (e m)^2 + 1 := he2 m
    linarith [h4, h3]

theorem lemma_e_m_ge_one (r : ℝ)
  (hr : r > 1/4)
  (e : ℕ → ℝ)
  (he1 : e 0 = 1)
  (he2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1):
  ∀ (m : ℕ), e m ≥ 1 := by
  exact round1_h_main_f0503c r hr e he1 he2

lemma round1_main (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (e : ℕ → ℝ)
  (he1 : e 0 = 1):
  ∃ (N₀ : ℕ) (C₀ : ℝ), C₀ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C₀ * (n : ℝ) ^ (e 0) := by
  use 0, (1 : ℝ)
  constructor
  ·
    norm_num
  ·
    intro n _
    have h1 : (g n : ℝ) ≥ (n : ℝ) := by
      exact_mod_cast h_g_ge_n n
    have h2 : (1 : ℝ) * (n : ℝ) ^ (e 0) = (n : ℝ) := by
      rw [he1]
      norm_num
    rw [h2]
    exact h1

theorem lemma_base_case_m_eq_0 (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (e : ℕ → ℝ)
  (he1 : e 0 = 1):
  ∃ (N₀ : ℕ) (C₀ : ℝ), C₀ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C₀ * (n : ℝ) ^ (e 0) := by
  exact round1_main r hr g h_g_ge_n e he1

theorem real_power_decomposition_by_exponent_diff (k : ℕ)
  (α : ℝ)
  (h_α_gt_k : α > (k : ℝ))
  (n : ℕ+):
  (n : ℝ) ^ α = (n : ℝ) ^ (α - (k : ℝ)) * (n : ℝ) ^ (k : ℝ) := by
  have h₁ : (n : ℝ) > 0 := by exact_mod_cast PNat.pos n
  have h_main : (n : ℝ) ^ (α - (k : ℝ)) * (n : ℝ) ^ ((k : ℝ)) = (n : ℝ) ^ (α) := by
    rw [← Real.rpow_add h₁]
    ring_nf
  exact h_main.symm

theorem inequality_with_positive_factor (C x y : ℝ)
  (h1 : C * x ≥ 1)
  (h2 : y > 0):
  C * x * y ≥ y := by
  have h3 : (C * x) * y ≥ 1 * y := by
    exact mul_le_mul_of_nonneg_right h1 (show 0 ≤ y by linarith)
  have h4 : (1 : ℝ) * y = y := by ring
  rw [h4] at h3
  linarith

lemma round1_h1 (n : ℕ+)
  (k : ℕ)
  (g : ℕ+):
  ((n : ℝ) ^ (k : ℝ)) = (( (n : ℕ) ^ k : ℝ)) := by
  norm_cast

theorem real_power_to_nat_inequality (n : ℕ+)
  (k : ℕ)
  (g : ℕ+)
  (h : (g : ℝ) ≥ (n : ℝ) ^ (k : ℝ)):
  (g : ℕ) ≥ (n : ℕ) ^ k := by
  have h1 : ((n : ℝ) ^ (k : ℝ)) = (( (n : ℕ) ^ k : ℝ)) := by
    exact round1_h1 n k g
  have h2 : (g : ℝ) ≥ (( (n : ℕ) ^ k : ℝ)) := by
    rw [h1] at h
    exact h
  exact_mod_cast h2

theorem g_g_n_pow_r_ge_one (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r):
  ∀ (n : ℕ+), (g (g n) : ℝ) ^ r ≥ 1 := by
  intro n
  have h1 : (g (g n) : ℝ) ≥ 1 := by
    have h2 : (g (g n) : ℕ) ≥ 1 := by exact_mod_cast (g (g n)).pos
    exact_mod_cast h2
  have h3 : r > 0 := by linarith
  have h4 : (g (g n) : ℝ) ^ r ≥ (1 : ℝ) ^ r := by
    apply Real.rpow_le_rpow
    · linarith
    · linarith
    · linarith
  have h5 : (1 : ℝ) ^ r = 1 := by
    simp
  rw [h5] at h4
  exact h4

theorem g_is_strictly_increasing (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h1 : ∀ (n : ℕ+), (g (g n) : ℝ) ^ r ≥ 1):
  ∀ (n : ℕ+), g (n + 1) > g n := by
  intro n
  have h2 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r := h_ineq n
  have h3 : (g (g n) : ℝ) ^ r ≥ 1 := h1 n
  have h4 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ 1 := by linarith
  have h5 : (g (n + 1) : ℝ) > (g n : ℝ) := by linarith
  exact_mod_cast h5

theorem g_n_ge_n_from_strictly_increasing (g : ℕ+ → ℕ+)
  (h_incr : ∀ (n : ℕ+), g (n + 1) > g n):
  ∀ (n : ℕ+), (g n : ℕ) ≥ n := by
  intro n
  induction n using PNat.recOn with
  | one =>
    norm_num
    exact_mod_cast (show (g 1 : ℕ) ≥ 1 from by exact_mod_cast (g 1).pos)
  | succ n ih =>
    have h1 : (g (n + 1) : ℕ) > (g n : ℕ) := by exact_mod_cast h_incr n
    have h2 : (g n : ℕ) ≥ (n : ℕ) := ih
    have h3 : (g (n + 1) : ℕ) ≥ ((n : ℕ) + 1) := by
      omega
    simpa [show ((n + 1 : ℕ+) : ℕ) = (n : ℕ) + 1 by simp] using h3

theorem lemma1 (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_super : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g n : ℕ) ≥ (n : ℕ) ^ k)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n)):
  ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (g n) : ℕ) ≥ (g n : ℕ) ^ k := by
  intro k
  have h₁ : ∃ (N₁ : ℕ), ∀ (m : ℕ+), (m : ℕ) ≥ N₁ → (g m : ℕ) ≥ (m : ℕ) ^ k := h_super k
  rcases h₁ with ⟨N₁, hN₁⟩
  refine' ⟨N₁, _⟩
  intro n hn
  have h₂ : (n : ℕ) ≥ N₁ := hn
  have h₃ : (g n : ℕ) ≥ (n : ℕ) := h_g_prop.2 n
  have h₄ : (g n : ℕ) ≥ N₁ := by linarith
  have h₅ : (g (g n) : ℕ) ≥ ((g n : ℕ) : ℕ) ^ k := hN₁ (g n) h₄
  simpa using h₅

lemma round1_main_7edb38 (r : ℝ)
  (hr : r > 1/4)
  (M : ℝ)
  (hM : M > 0):
  ∃ (k : ℕ), (k : ℝ) * r ≥ M := by
  have hr_pos : 0 < r := by linarith
  have h1 : ∃ (k : ℕ), (k : ℝ) > M / r := by
    exact exists_nat_gt (M / r)
  rcases h1 with ⟨k, hk⟩
  have h2 : (k : ℝ) * r > M := by
    have h3 : (k : ℝ) > M / r := hk
    have h4 : (k : ℝ) * r > (M / r) * r := by gcongr
    have h5 : (M / r) * r = M := by
      field_simp [hr_pos.ne']
    rw [h5] at h4
    linarith
  have h6 : (k : ℝ) * r ≥ M := by linarith
  exact ⟨k, h6⟩

theorem lemma2 (r : ℝ)
  (hr : r > 1/4)
  (M : ℝ)
  (hM : M > 0):
  ∃ (k : ℕ), (k : ℝ) * r ≥ M := by
  exact round1_main_7edb38 r hr M hM

theorem lemma4 (x : ℝ)
  (hx : x > 1)
  (y z : ℝ)
  (h_y_ge_z : y ≥ z)
  (hz : z > 0):
  x ^ y ≥ x ^ z := by
  have h1 : 1 ≤ x := by linarith
  have h_main : Monotone (fun (t : ℝ) => x ^ t) := monotone_rpow_of_base_ge_one h1
  have h2 : x ^ y ≥ x ^ z := h_main h_y_ge_z
  exact h2

lemma round1_h_main_641cf1 (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n)):
  ∀ (n : ℕ+), (n : ℕ) ≥ 2 → (g n : ℝ) > 1 := by
  have h₂ : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ) := h_g_prop.2
  intro n hn
  have h₃ : (g n : ℕ) ≥ (n : ℕ) := h₂ n
  have h₄ : (n : ℕ) ≥ 2 := hn
  have h₅ : (g n : ℕ) ≥ 2 := by linarith
  have h₆ : (g n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h₅
  have h₇ : (g n : ℝ) > 1 := by linarith
  exact h₇

theorem lemma5 (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n)):
  ∀ (n : ℕ+), (n : ℕ) ≥ 2 → (g n : ℝ) > 1 := by
  have h_main : ∀ (n : ℕ+), (n : ℕ) ≥ 2 → (g n : ℝ) > 1 := round1_h_main_641cf1 g h_g_prop
  exact h_main

lemma round1_h_main_93cf1b (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n)):
  ∀ (y : ℕ+) (k : ℕ), g (⟨y.val + k, by positivity⟩ : ℕ+) ≥ g y := by
  intro y k
  induction k with
  | zero =>
    have h_eq : (⟨y.val + 0, by positivity⟩ : ℕ+) = y := by
      apply PNat.eq
      simp
    rw [h_eq]
  | succ k ih =>
    let z : ℕ+ := ⟨y.val + k, by positivity⟩
    have h_step : g (z + 1) > g z := h_g_prop.1 z
    have h_goal : g (z + 1) ≥ g z := le_of_lt h_step
    have h_final : g (⟨y.val + (k + 1), by positivity⟩ : ℕ+) = g (z + 1) := by
      apply congr_arg g
      apply PNat.eq
      simp [z]
      ring
    rw [h_final]
    exact le_trans ih h_goal

theorem lemma2_g_g_n_ge_g_n_plus_2 (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (n : ℕ+)
  (h : (g n : ℕ) ≥ n + 2):
  (g (g n) : ℝ) ≥ (g (n + 2) : ℝ) := by
  have h_main : ∀ (y : ℕ+) (k : ℕ), g (⟨y.val + k, by positivity⟩ : ℕ+) ≥ g y :=
    round1_h_main_93cf1b g h_g_prop
  let b : ℕ+ := n + 2
  have h_b_val : (b.val : ℕ) = (n : ℕ) + 2 := by
    simp [b]
  have h_exists_k : ∃ (k : ℕ), (g n : ℕ) = (n : ℕ) + 2 + k := by
    refine' ⟨(g n : ℕ) - ((n : ℕ) + 2), _⟩
    omega
  rcases h_exists_k with ⟨k, hk⟩
  have h_eq : (g n : ℕ) = b.val + k := by
    simp [h_b_val, hk]
  have h3 : g (g n) ≥ g (b) := by
    have h4 : g (g n) = g (⟨(g n : ℕ), by positivity⟩ : ℕ+) := by
      rfl
    rw [h4]
    have h5 : (g (⟨(g n : ℕ), by positivity⟩ : ℕ+)) ≥ g (b) := by
      simpa [h_eq] using h_main b k
    exact h5
  have h4 : (g (g n) : ℝ) ≥ (g (n + 2) : ℝ) := by
    simpa [show (n + 2 : ℕ+) = b from by
      simp [b]] using h3
  exact h4

theorem lemma3_exists_N5_g_n_plus_2_ge_g_n_plus_1_pow_5 (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (h_exp_growth : ∀ (M : ℝ), M > 0 → ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M):
  ∃ (N5 : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N5 → (g (n + 2) : ℝ) ≥ (g (n + 1) : ℝ) ^ 5 := by
  have h_main : ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ (5 : ℝ) := by
    exact h_exp_growth (5 : ℝ) (by norm_num)
  rcases h_main with ⟨N, hN⟩
  refine' ⟨N, _⟩
  intro n hn
  have h1 : ((n + 1 : ℕ+) : ℕ) ≥ N := by
    simp
    omega
  have h2 := hN (n + 1) h1
  simpa [add_assoc] using h2

lemma round1_h_main_78281e (x k : ℝ)
  (hx : x > 1)
  (h_ineq : x > x ^ k):
  k < 1 := by
  by_contra h
  have h' : k ≥ 1 := by linarith
  have h1 : x ^ k ≥ x := by
    have h2 : x > 0 := by linarith
    have h3 : x ^ k ≥ x ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      <;> linarith
    have h4 : x ^ (1 : ℝ) = x := by
      simp
    rw [h4] at h3
    exact h3
  linarith

theorem lemma4_x_gt_x_pow_k_implies_k_lt_1 (x k : ℝ)
  (hx : x > 1)
  (h_ineq : x > x ^ k):
  k < 1 := by
  exact round1_h_main_78281e x k hx h_ineq

theorem lemma7_g_n_plus_1_gt_1 (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (n : ℕ+)
  (N2 : ℕ)
  (h_n_ge_N2 : (n : ℕ) ≥ N2)
  (h_N2_prop : ∀ (k : ℕ+), (k : ℕ) ≥ N2 → (g k : ℕ) ≥ k + 2):
  (g (n + 1) : ℝ) > 1 := by
  have h1 : (g n : ℕ) ≥ (n : ℕ) + 2 := h_N2_prop n h_n_ge_N2
  have h2 : (n : ℕ) ≥ 1 := by exact_mod_cast n.pos
  have h3 : (g n : ℕ) > 1 := by linarith
  have h4 : g (n + 1) > g n := h_g_prop.1 n
  have h5 : (g (n + 1) : ℕ) > (g n : ℕ) := by exact_mod_cast h4
  have h6 : (g (n + 1) : ℕ) > 1 := by linarith
  exact_mod_cast h6

theorem delta_is_positive (r : ℝ)
  (hr : r > 1/4):
  (1 : ℝ) - 1 / (4 * r) > 0 := by
  have h1 : r > 0 := by linarith
  have h2 : 4 * r > 1 := by linarith
  have h3 : 1 / (4 * r) < 1 := by
    apply (div_lt_one (by linarith)).mpr
    linarith
  linarith

lemma round1_h_main_92a38c (r : ℝ)
  (hr : r > 1/4)
  (x : ℝ):
  r * x^2 + 1 - x = r * (x - 1 / (2 * r))^2 + (1 - 1 / (4 * r)) := by
  have hr_pos : 0 < r := by linarith
  have hr_ne_zero : r ≠ 0 := by linarith
  field_simp [hr_ne_zero]
  ring

theorem quadratic_completion (r : ℝ)
  (hr : r > 1/4)
  (x : ℝ):
  r * x^2 + 1 - x = r * (x - 1 / (2 * r))^2 + (1 - 1 / (4 * r)) := by
  exact round1_h_main_92a38c r hr x

lemma round1_h_main_7e6868 (r : ℝ)
  (hr : r > 1/4)
  (x : ℝ):
  r * (x - 1 / (2 * r))^2 + (1 - 1 / (4 * r)) ≥ (1 - 1 / (4 * r)) := by
  have h₁ : 0 < r := by linarith
  have h₂ : 0 ≤ r * (x - 1 / (2 * r)) ^ 2 := by
    apply mul_nonneg
    · linarith
    · exact sq_nonneg (x - 1 / (2 * r))
  linarith

theorem lower_bound_from_nonnegative_square (r : ℝ)
  (hr : r > 1/4)
  (x : ℝ):
  r * (x - 1 / (2 * r))^2 + (1 - 1 / (4 * r)) ≥ (1 - 1 / (4 * r)) := by
  exact round1_h_main_7e6868 r hr x

theorem e_succ_ge_e_add_delta (r : ℝ)
  (e : ℕ → ℝ)
  (δ : ℝ)
  (h_e_rec : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1)
  (h_ineq : ∀ (x : ℝ), r * x^2 + 1 - x ≥ δ):
  ∀ (m : ℕ), e (m + 1) ≥ e m + δ := by
  intro m
  have h1 : r * (e m)^2 + 1 - e m ≥ δ := h_ineq (e m)
  have h2 : e (m + 1) = r * (e m)^2 + 1 := h_e_rec m
  linarith

theorem base_case_n_zero (e : ℕ → ℝ)
  (δ : ℝ)
  (h_e0 : e 0 = 1):
  e 0 ≥ 1 + (0 : ℝ) * δ := by
  have h1 : (0 : ℝ) * δ = 0 := by ring
  have h2 : (1 : ℝ) + (0 : ℝ) * δ = 1 := by
    rw [h1]
    norm_num
  have h3 : e 0 ≥ 1 := by
    linarith [h_e0]
  rw [h2]
  linarith

theorem inductive_step_property (e : ℕ → ℝ)
  (δ : ℝ)
  (k : ℕ)
  (h1 : e k ≥ 1 + (k : ℝ) * δ)
  (h2 : e (k + 1) ≥ e k + δ):
  e (k + 1) ≥ 1 + ((k : ℝ) + 1) * δ := by
  have h_main : e (k + 1) ≥ 1 + ((k : ℝ) + 1) * δ := by
    calc
      e (k + 1) ≥ e k + δ := h2
      _ ≥ (1 + (k : ℝ) * δ) + δ := by gcongr
      _ = 1 + ((k : ℝ) + 1) * δ := by ring
  exact h_main

theorem lemma_monotonicity_of_rpow (x y r : ℝ)
  (h1 : x ≥ y)
  (h2 : y ≥ 0)
  (h3 : r > 0):
  x ^ r ≥ y ^ r := by
  have h_main : x ^ r ≥ y ^ r := by
    have h4 : 0 ≤ r := by linarith
    have h5 : x ≥ 0 := by linarith
    have h6 : y ∈ Set.Ici (0 : ℝ) := by exact Set.mem_Ici.mpr h2
    have h7 : x ∈ Set.Ici (0 : ℝ) := by exact Set.mem_Ici.mpr h5
    have h9 : y ≤ x := by linarith
    have h10 : (x ^ r) ≥ (y ^ r) := monotoneOn_rpow_Ici_of_exponent_nonneg h4 h6 h7 h9
    exact h10
  exact h_main

lemma round1_h_main_78874b (C n r α : ℝ)
  (hC_pos : C > 0)
  (hn_pos : n > 0):
  (C ^ (α + 1) * n ^ (α ^ 2)) ^ r = C ^ (r * (α + 1)) * n ^ (r * (α ^ 2)) := by
  have h1 : 0 < C ^ (α + 1) := by positivity
  have h2 : 0 < n ^ (α ^ 2) := by positivity
  have h3 : (C ^ (α + 1) * n ^ (α ^ 2)) ^ r = (C ^ (α + 1)) ^ r * (n ^ (α ^ 2)) ^ r := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
  have h4 : (C ^ (α + 1)) ^ r = C ^ (r * (α + 1)) := by
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
  have h5 : (n ^ (α ^ 2)) ^ r = n ^ (r * (α ^ 2)) := by
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
  rw [h3, h4, h5]

theorem lemma_rpow_of_product_and_power (C n r α : ℝ)
  (hC_pos : C > 0)
  (hn_pos : n > 0):
  (C ^ (α + 1) * n ^ (α ^ 2)) ^ r = C ^ (r * (α + 1)) * n ^ (r * (α ^ 2)) := by
  exact round1_h_main_78874b C n r α hC_pos hn_pos

theorem lemma_positivity_of_K (C : ℝ)
  (r : ℝ)
  (α : ℝ)
  (hC_pos : C > 0)
  (hr_pos : r > 0)
  (hα : α ≥ 1):
  C ^ (r * (α + 1)) > 0 := by
  have h_main : C ^ (r * (α + 1)) > 0 := by
    apply Real.rpow_pos_of_pos
    exact hC_pos
  exact h_main

lemma round1_h_main_bf2d79 (n : ℕ+):
  (n : ℝ) > 0 := by
  have h : (n : ℕ) > 0 := n.pos
  exact_mod_cast h

theorem lemma_pnat_cast_real_positive (n : ℕ+):
  (n : ℝ) > 0 := by
  exact round1_h_main_bf2d79 n

lemma round1_h1_3efe0a (C n α : ℝ)
  (hC_pos : C > 0):
  C ^ (α + 1) > 0 := by
  apply Real.rpow_pos_of_pos
  exact hC_pos

lemma round1_h2 (C n α : ℝ)
  (hn_pos : n > 0):
  n ^ (α ^ 2) > 0 := by
  apply Real.rpow_pos_of_pos
  exact hn_pos

theorem lemma_nonnegativity_of_intermediate_expression (C n α : ℝ)
  (hC_pos : C > 0)
  (hn_pos : n > 0):
  C ^ (α + 1) * n ^ (α ^ 2) ≥ 0 := by
  have h1 : C ^ (α + 1) > 0 := by
    exact round1_h1_3efe0a C n α hC_pos
  have h2 : n ^ (α ^ 2) > 0 := by
    exact round1_h2 C n α hn_pos
  have h3 : C ^ (α + 1) * n ^ (α ^ 2) > 0 := mul_pos h1 h2
  have h4 : C ^ (α + 1) * n ^ (α ^ 2) ≥ 0 := by
    linarith
  exact h4

theorem nat_ge_one_implies_pos (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  0 < M := by
  linarith

theorem nat_n_ge_M_plus_one_and_M_ge_one_implies_n_pos (M n : ℕ)
  (hM_ge_1 : M ≥ 1)
  (hn_ge_M_plus_1 : n ≥ M + 1):
  0 < n := by
  have h1 : M + 1 ≥ 2 := by
    omega
  have h2 : n ≥ 2 := by
    omega
  have h3 : 0 < n := by
    omega
  exact h3

theorem g_M_is_positive_real (g : ℕ+ → ℕ+)
  (M : ℕ)
  (hM_pos : 0 < M):
  (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) > 0 := by
  have h1 : (g (⟨M, hM_pos⟩ : ℕ+) : ℕ) > 0 := by
    exact_mod_cast (g (⟨M, hM_pos⟩ : ℕ+)).pos
  have h2 : ((g (⟨M, hM_pos⟩ : ℕ+) : ℝ)) > 0 := by
    exact_mod_cast h1
  exact h2

theorem max_of_two_naturals_ge_each (a b : ℕ):
  max a b ≥ a ∧ max a b ≥ b := by
  by_cases h : a ≤ b
  ·
    have h1 : max a b = b := by
      rw [max_eq_right h]
    rw [h1]
    omega
  ·
    have h2 : b ≤ a := by omega
    have h3 : max a b = a := by
      rw [max_eq_left h2]
    rw [h3]
    omega

theorem K_mul_sum_ge_K_mul_C_sum_times_n_pow (M N_sum : ℕ)
  (C_sum K : ℝ)
  (β : ℝ)
  (hK_pos : K > 0)
  (hC_sum_pos : C_sum > 0)
  (n : ℕ)
  (hn_ge_N_sum : n ≥ N_sum)
  (h_sum_ineq : ∀ (n : ℕ), n ≥ N_sum → (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ C_sum * (n : ℝ) ^ (β + 1)):
  K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ K * C_sum * (n : ℝ) ^ (β + 1) := by
  have h1 : (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ C_sum * (n : ℝ) ^ (β + 1) := h_sum_ineq n hn_ge_N_sum
  have h2 : K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ K * (C_sum * (n : ℝ) ^ (β + 1)) := by
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : K * (C_sum * (n : ℝ) ^ (β + 1)) = K * C_sum * (n : ℝ) ^ (β + 1) := by ring
  rw [h3] at h2
  exact h2

theorem real_ge_add_and_nonneg_left_factor_implies_ge (x y z : ℝ)
  (h1 : x ≥ y + z)
  (h2 : y ≥ 0):
  x ≥ z := by
  have h_main : x ≥ z := by
    linarith
  exact h_main

theorem lemma_apply_h_growth_step_to_get_intermediate_bound (r : ℝ)
  (g : ℕ+ → ℕ+)
  (e : ℕ → ℝ)
  (m : ℕ)
  (N_m : ℕ)
  (C_m : ℝ)
  (h_e_m_ge_1 : e m ≥ 1)
  (hC_m_pos : C_m > 0)
  (h_hyp_m : ∀ (n : ℕ+), (n : ℕ) ≥ N_m → (g n : ℝ) ≥ C_m * (n : ℝ) ^ (e m))
  (h_growth_step : ∀ (α : ℝ)
    (hα : α ≥ 1)
    (N₀ : ℕ)
    (C : ℝ)
    (hC_pos : C > 0)
    (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α),
    ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * α^2 + 1)):
  ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * (e m)^2 + 1) := by
  exact h_growth_step (e m) h_e_m_ge_1 N_m C_m hC_m_pos h_hyp_m

lemma round1_h_main_221f08 (r : ℝ)
  (e : ℕ → ℝ)
  (m : ℕ)
  (he2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1):
  r * (e m)^2 + 1 = e (m + 1) := by
  have h : e (m + 1) = r * (e m)^2 + 1 := he2 m
  exact h.symm

theorem lemma_exponent_value_from_recurrence (r : ℝ)
  (e : ℕ → ℝ)
  (m : ℕ)
  (he2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1):
  r * (e m)^2 + 1 = e (m + 1) := by
  exact round1_h_main_221f08 r e m he2

lemma round1_h_main_5be531 (C : ℝ)
  (t : ℝ)
  (x y : ℝ)
  (ht_pos : t > 0)
  (h_exp_eq : x = y):
  C * t ^ x = C * t ^ y := by
  rw [h_exp_eq]

theorem lemma_equal_exponents_give_equal_power_expression (C : ℝ)
  (t : ℝ)
  (x y : ℝ)
  (ht_pos : t > 0)
  (h_exp_eq : x = y):
  C * t ^ x = C * t ^ y := by
  exact round1_h_main_5be531 C t x y ht_pos h_exp_eq

lemma round1_h_main_90762e (a b c : ℝ)
  (h_ineq : a ≥ b)
  (h_eq : b = c):
  a ≥ c := by
  have h1 : a ≥ c := by
    rw [h_eq] at h_ineq
    exact h_ineq
  exact h1

theorem lemma_inequality_and_equality_transitivity (a b c : ℝ)
  (h_ineq : a ≥ b)
  (h_eq : b = c):
  a ≥ c := by
  exact round1_h_main_90762e a b c h_ineq h_eq

theorem real_ge_implies_C_mul_pow_ge_one (C : ℝ)
  (hC_pos : C > 0)
  (δ : ℝ)
  (hδ_pos : δ > 0)
  (B : ℝ)
  (hB_def : B = (1 / C) ^ (1 / δ))
  (n : ℕ+)
  (h_n_ge_B : (n : ℝ) ≥ B):
  C * (n : ℝ) ^ δ ≥ 1 := by
  have h1 : (1 / C : ℝ) > 0 := by positivity
  have h2 : (n : ℝ) ≥ (1 / C : ℝ) ^ (1 / δ) := by
    rw [hB_def] at h_n_ge_B
    exact h_n_ge_B
  have h3 : ((n : ℝ) ^ δ) ≥ (((1 / C : ℝ) ^ (1 / δ)) ^ δ) := by
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · linarith
  have h4 : (((1 / C : ℝ) ^ (1 / δ)) ^ δ) = (1 / C : ℝ) := by
    have h5 : (((1 / C : ℝ) ^ (1 / δ)) ^ δ) = ((1 / C : ℝ) ^ ((1 / δ) * δ)) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h5]
    have h6 : (1 / δ : ℝ) * δ = 1 := by field_simp [hδ_pos.ne']
    rw [h6]
    simp
  rw [h4] at h3
  have h7 : (n : ℝ) ^ δ ≥ (1 / C : ℝ) := h3
  have h8 : C * ((n : ℝ) ^ δ) ≥ C * (1 / C : ℝ) := by
    exact mul_le_mul_of_nonneg_left h7 (by linarith)
  have h9 : C * (1 / C : ℝ) = 1 := by field_simp [hC_pos.ne']
  linarith

theorem exists_nat_ge_real (x : ℝ):
  ∃ (N₁ : ℕ), (N₁ : ℝ) ≥ x := by
  have h₁ : ∃ (N₁ : ℕ), (N₁ : ℝ) > x := exists_nat_gt x
  rcases h₁ with ⟨N₁, hN₁⟩
  refine' ⟨N₁, _⟩
  linarith

theorem pnat_coe_ge_of_nat_coe_ge (N₁ : ℕ)
  (n : ℕ+)
  (h : (n : ℕ) ≥ N₁):
  (n : ℝ) ≥ (N₁ : ℝ) := by
  have h₁ : ((n : ℕ) : ℝ) ≥ (N₁ : ℝ) := by exact_mod_cast h
  simpa using h₁

lemma round1_h1_bfc38f (a : ℝ)
  (k : ℕ)
  (r : ℝ)
  (ha_nonneg : a ≥ 0):
  ( (a ^ k : ℝ) ) ^ r = a ^ ((k : ℝ) * r) := by
  have h11 : ((a ^ k : ℝ)) = a ^ ((k : ℝ)) := by
    norm_cast
  rw [h11]
  have h12 : (a ^ ((k : ℝ)) : ℝ) ^ r = a ^ (((k : ℝ)) * r) := by
    rw [← Real.rpow_mul ha_nonneg]
  simpa using h12

theorem real_rpow_inequality_from_base_inequality (a b : ℝ)
  (k : ℕ)
  (r : ℝ)
  (ha_nonneg : a ≥ 0)
  (hb_nonneg : b ≥ 0)
  (hr_pos : r > 0)
  (h_ineq : b ≥ a ^ k):
  b ^ r ≥ a ^ ((k : ℝ) * r) := by
  have h2 : (0 : ℝ) ≤ (a ^ k : ℝ) := by positivity
  have h3 : b ≥ (a ^ k : ℝ) := by exact_mod_cast h_ineq
  have h4 : b ^ r ≥ ((a ^ k : ℝ) ^ r) := by
    apply Real.rpow_le_rpow
    <;> linarith
  have h5 : ((a ^ k : ℝ) ^ r) = a ^ ((k : ℝ) * r) := round1_h1_bfc38f a k r ha_nonneg
  rw [h5] at h4
  exact h4

theorem convert_nat_inequality_to_real_power_inequality (g : ℕ+ → ℕ+)
  (n : ℕ+)
  (k : ℕ)
  (h : (g (g n) : ℕ) ≥ (g n : ℕ) ^ k):
  (g (g n) : ℝ) ≥ (g n : ℝ) ^ k := by
  have h₁ : (g (g n) : ℕ) ≥ (g n : ℕ) ^ k := h
  exact_mod_cast h₁

theorem pnat_function_values_are_nonnegative (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (n : ℕ+):
  (g n : ℝ) ≥ 0 ∧ (g (g n) : ℝ) ≥ 0 := by
  have h1 : (g n : ℝ) > 0 := by
    exact_mod_cast (g n).pos
  have h2 : (g (g n) : ℝ) > 0 := by
    exact_mod_cast (g (g n)).pos
  exact ⟨by linarith, by linarith⟩

theorem get_lower_bound_on_difference_of_consecutive_terms (r : ℝ)
  (g : ℕ+ → ℕ+)
  (k : ℕ)
  (h_ineq : ∀ (n : ℕ+), (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (n : ℕ+)
  (h : (g (g n) : ℝ) ^ r ≥ (g n : ℝ) ^ ((k : ℝ) * r)):
  (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g n : ℝ) ^ ((k : ℝ) * r) := by
  have h1 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r := h_ineq n
  have h2 : (g (g n) : ℝ) ^ r ≥ (g n : ℝ) ^ ((k : ℝ) * r) := h
  exact ge_trans h1 h2

theorem sub_ge_implication_for_reals (a b c : ℝ)
  (h : a - b ≥ c):
  a ≥ b + c := by
  linarith

theorem adding_positive_is_strictly_greater (x y : ℝ)
  (hx : x > 0):
  x + y > y := by
  linarith

theorem pnat_function_is_strictly_positive (g : ℕ+ → ℕ+)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (n : ℕ+):
  (g n : ℝ) > 0 := by
  have h2 : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ) := h_g_prop.2
  have h3 : (g n : ℕ) ≥ (n : ℕ) := h2 n
  have h4 : (n : ℕ) > 0 := n.pos
  have h5 : (g n : ℕ) > 0 := by linarith
  exact_mod_cast h5

lemma round1_h_main_494b28 :
  ∀ (m : ℕ), m ≥ 3 → m ^ 2 ≥ m + 3 := by
  intro m hm
  induction' hm with m hm ih
  ·
    norm_num
  ·
    cases m with
    | zero => contradiction
    | succ m' =>
      simp [pow_two, Nat.succ_eq_add_one] at *
      ring_nf at * ; omega

theorem lemma_nat_inequality_n_minus_1_sq_ge_n_plus_2 :
  ∀ (n : ℕ), n ≥ 4 → (n - 1) ^ 2 ≥ n + 2 := by
  intro n hn
  have h1 : n - 1 ≥ 3 := by omega
  have h2 : (n - 1) ^ 2 ≥ (n - 1) + 3 := round1_h_main_494b28 (n - 1) h1
  have h3 : (n - 1) + 3 = n + 2 := by omega
  rw [h3] at h2
  exact h2

theorem lemma_exists_N0_for_g_k_plus_1_ge_g_k_sq (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (h_exp_growth : ∀ (M : ℝ), M > 0 → ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M):
  ∃ (N0 : ℕ), ∀ (k : ℕ+), (k : ℕ) ≥ N0 → (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) > 0 := by norm_num
  have h_main : ∃ (N0 : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N0 → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ (2 : ℝ) := h_exp_growth (2 : ℝ) h2
  rcases h_main with ⟨N0, hN0⟩
  refine ⟨N0, fun k hk => ?_⟩
  have h3 : (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ (2 : ℝ) := hN0 k hk
  have h4 : (g k : ℝ) ^ (2 : ℕ) = (g k : ℝ) ^ (2 : ℝ) := by
    norm_cast
  rw [h4]
  exact h3

theorem lemma_g_n_is_positive_from_ge_n_plus_2 (g : ℕ+ → ℕ+)
  (n : ℕ+)
  (h : (g n : ℕ) ≥ n + 2):
  (g n : ℝ) > 0 := by
  have h₁ : (0 : ℕ) < (g n : ℕ) := (g n).pos
  exact_mod_cast h₁

lemma round1_h_main_383714 (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (n : ℕ+):
  (g (n + 1) : ℝ) ≥ (g n : ℝ) + (g (g n) : ℝ) ^ r := by
  have h1 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r := h_ineq n
  linarith

theorem lemma_ineq_from_h_ineq_rearranged (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (n : ℕ+):
  (g (n + 1) : ℝ) ≥ (g n : ℝ) + (g (g n) : ℝ) ^ r := by
  exact round1_h_main_383714 r g h_ineq n

lemma round1_lemma_add_positive_gt_self (a b : ℝ)
  (ha : a > 0):
  a + b > b := by
  linarith

theorem lemma_add_positive_gt_self (a b : ℝ)
  (ha : a > 0):
  a + b > b := by
  exact round1_lemma_add_positive_gt_self a b ha

lemma round1_h_main_94d5cf (x y z : ℝ)
  (h2 : y ≥ z)
  (h3 : z ≥ x ^ 5):
  y ≥ x ^ 5 := by
  linarith

theorem lemma1_ge_transitivity (x y z : ℝ)
  (h2 : y ≥ z)
  (h3 : z ≥ x ^ 5):
  y ≥ x ^ 5 := by
  exact round1_h_main_94d5cf x y z h2 h3

lemma h_main_rpow (x y r : ℝ)
  (hx_pos : x > 0)
  (hr_pos : r > 0)
  (h_ineq : y ≥ x ^ 5):
  y ^ r ≥ x ^ (5 * r) := by
  have h1 : 0 < x ^ 5 := by positivity
  have h2 : 0 < y := by linarith
  have h3 : y ^ r ≥ (x ^ 5) ^ r := by
    apply Real.rpow_le_rpow
    <;> linarith
  have h4 : (x ^ 5) ^ r = x ^ (5 * r) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
  rw [h4] at h3
  exact h3

theorem lemma2_rpow_monotone (x y r : ℝ)
  (hx_pos : x > 0)
  (hr_pos : r > 0)
  (h_ineq : y ≥ x ^ 5):
  y ^ r ≥ x ^ (5 * r) := by
  exact h_main_rpow x y r hx_pos hr_pos h_ineq

lemma round1_h_main_0a53d1 (a b c : ℝ)
  (h11 : a > b)
  (h12 : b ≥ c):
  a > c := by
  linarith

theorem lemma3_transitivity_inequality (a b c : ℝ)
  (h11 : a > b)
  (h12 : b ≥ c):
  a > c := by
  have h_main : a > c := round1_h_main_0a53d1 a b c h11 h12
  exact h_main

lemma round1_h_main_718202 (g : ℕ+ → ℕ+)
  (α : ℝ)
  (N₀ : ℕ)
  (C : ℝ)
  (n : ℕ+)
  (hn : (n : ℕ) ≥ max 1 N₀)
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α):
  (g n : ℝ) ≥ C * (n : ℝ) ^ α := by
  have h1 : (n : ℕ) ≥ N₀ := by
    have h2 : max 1 N₀ ≥ N₀ := by
      exact le_max_right 1 N₀
    linarith
  exact h_hyp n h1

theorem first_g_lower_bound (g : ℕ+ → ℕ+)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (α : ℝ)
  (hα : α ≥ 1)
  (N₀ : ℕ)
  (C : ℝ)
  (hC_pos : C > 0)
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α)
  (n : ℕ+)
  (hn : (n : ℕ) ≥ max 1 N₀):
  (g n : ℝ) ≥ C * (n : ℝ) ^ α := by
  exact round1_h_main_718202 g α N₀ C n hn h_hyp

theorem g_n_nat_ge_N0 (g : ℕ+ → ℕ+)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (N₀ : ℕ)
  (n : ℕ+)
  (hn : (n : ℕ) ≥ max 1 N₀):
  (g n : ℕ) ≥ N₀ := by
  have h1 : (g n : ℕ) ≥ (n : ℕ) := h_g_ge_n n
  have h2 : (n : ℕ) ≥ max 1 N₀ := hn
  have h3 : max 1 N₀ ≥ N₀ := by
    apply Nat.le_max_right
  have h4 : (n : ℕ) ≥ N₀ := by
    exact le_trans h3 h2
  exact le_trans h4 h1

theorem second_application_of_hyp (g : ℕ+ → ℕ+)
  (α : ℝ)
  (hα : α ≥ 1)
  (N₀ : ℕ)
  (C : ℝ)
  (hC_pos : C > 0)
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α)
  (n : ℕ+)
  (h_gn_ge_N₀ : (g n : ℕ) ≥ N₀):
  (g (g n) : ℝ) ≥ C * (g n : ℝ) ^ α := by
  have h₁ : (g n : ℕ) ≥ N₀ := h_gn_ge_N₀
  have h_main : (g (g n) : ℝ) ≥ C * (g n : ℝ) ^ α := h_hyp (g n) h₁
  exact h_main

theorem power_inequality_step (α : ℝ)
  (hα : α ≥ 1)
  (C : ℝ)
  (hC_pos : C > 0)
  (N₀ : ℕ)
  (n : ℕ+)
  (g : ℕ+ → ℕ+)
  (hn : (n : ℕ) ≥ max 1 N₀)
  (h_gn_lower : (g n : ℝ) ≥ C * (n : ℝ) ^ α):
  C * (g n : ℝ) ^ α ≥ C ^ (α + 1) * (n : ℝ) ^ (α ^ 2) := by
  have h1 : (n : ℝ) ≥ 0 := by positivity
  have h2 : (C * (n : ℝ) ^ α) ≥ 0 := by positivity
  have h3 : (g n : ℝ) ≥ 0 := by linarith
  have hα0 : 0 ≤ α := by linarith
  have h4 : (g n : ℝ) ^ α ≥ (C * (n : ℝ) ^ α) ^ α := by
    apply Real.rpow_le_rpow
    · linarith
    · linarith
    · exact hα0
  have h5 : (C * (n : ℝ) ^ α) ^ α = C ^ α * ((n : ℝ) ^ α) ^ α := by
    rw [mul_rpow (by positivity) (by positivity)]
  have h6 : ((n : ℝ) ^ α) ^ α = (n : ℝ) ^ (α ^ 2) := by
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
  have h7 : (C * (n : ℝ) ^ α) ^ α = C ^ α * (n : ℝ) ^ (α ^ 2) := by
    rw [h5, h6]
  have h8 : (g n : ℝ) ^ α ≥ C ^ α * (n : ℝ) ^ (α ^ 2) := by
    linarith
  have h9 : C * (g n : ℝ) ^ α ≥ C * (C ^ α * (n : ℝ) ^ (α ^ 2)) := by
    exact mul_le_mul_of_nonneg_left h8 (by linarith)
  have h11 : C * (C ^ α) = C ^ (α + 1) := by
    have h12 : C ^ (α + 1 : ℝ) = C ^ α * C ^ (1 : ℝ) := by
      rw [Real.rpow_add (by linarith)]
    have h13 : C ^ (1 : ℝ) = C := by
      norm_num
    rw [h12, h13]
    ring
  have h10 : C * (C ^ α * (n : ℝ) ^ (α ^ 2)) = C ^ (α + 1) * (n : ℝ) ^ (α ^ 2) := by
    calc
      C * (C ^ α * (n : ℝ) ^ (α ^ 2))
        = (C * (C ^ α)) * (n : ℝ) ^ (α ^ 2) := by ring
      _ = (C ^ (α + 1)) * (n : ℝ) ^ (α ^ 2) := by rw [h11]
  rw [h10] at h9
  exact h9

lemma round1_h_main_1522d7 (β : ℝ)
  (hβ_pos : β > 0)
  (k : ℕ)
  (hk_ge_1 : k ≥ 1):
  ∀ (x : ℝ), x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ) → x ^ β ≤ (k : ℝ) ^ β := by
  intro x hx
  have h₁ : (k : ℝ) - 1 ≤ x := hx.1
  have h₂ : x ≤ (k : ℝ) := hx.2
  have h₃ : 0 ≤ x := by
    have h₄ : (k : ℝ) ≥ 1 := by exact_mod_cast hk_ge_1
    linarith
  have h₅ : x ≤ (k : ℝ) := h₂
  have h₆ : x ^ β ≤ (k : ℝ) ^ β := by
    apply Real.rpow_le_rpow
    <;> linarith
  exact h₆

theorem integral_le_pow_at_right_endpoint (β : ℝ)
  (hβ_pos : β > 0)
  (k : ℕ)
  (hk_ge_1 : k ≥ 1):
  ∫ (x : ℝ) in ((k : ℝ) - 1)..(k : ℝ), x ^ β ≤ (k : ℝ) ^ β := by
  have h_main : ∀ (x : ℝ), x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ) → x ^ β ≤ (k : ℝ) ^ β :=
    round1_h_main_1522d7 β hβ_pos k hk_ge_1
  have h_k_nonneg : 0 ≤ (k : ℝ) - 1 := by
    have h₃ : (k : ℝ) ≥ 1 := by exact_mod_cast hk_ge_1
    linarith
  have h1a : (k : ℝ) - 1 ≤ (k : ℝ) := by
    have h₃ : (k : ℝ) ≥ 1 := by exact_mod_cast hk_ge_1
    linarith
  have h_cont1 : ContinuousOn (fun x : ℝ ↦ x ^ β) (Set.uIcc ((k : ℝ) - 1) (k : ℝ)) := by
    have h_eq : Set.uIcc ((k : ℝ) - 1) (k : ℝ) = Set.Icc ((k : ℝ) - 1) (k : ℝ) := by
      rw [Set.uIcc_of_le h1a]
    rw [h_eq]
    apply ContinuousOn.rpow
    · exact continuousOn_id
    · exact continuousOn_const
    · intro x hx
      exact Or.inr hβ_pos
  have h_int1 : IntervalIntegrable (fun x : ℝ ↦ x ^ β) MeasureTheory.volume ((k : ℝ) - 1) (k : ℝ) := by
    apply ContinuousOn.intervalIntegrable h_cont1
  have h_int2 : IntervalIntegrable (fun x : ℝ ↦ (k : ℝ) ^ β) MeasureTheory.volume ((k : ℝ) - 1) (k : ℝ) := by
    apply intervalIntegrable_const
    simp
  have h_mono : (∀ x ∈ Set.uIcc ((k : ℝ) - 1) (k : ℝ), (x ^ β : ℝ) ≤ ((k : ℝ) ^ β : ℝ)) := by
    intro x hx
    have h_mem : x ∈ Set.Icc ((k : ℝ) - 1) (k : ℝ) := by
      have h_eq : Set.uIcc ((k : ℝ) - 1) (k : ℝ) = Set.Icc ((k : ℝ) - 1) (k : ℝ) := by
        rw [Set.uIcc_of_le h1a]
      rw [h_eq] at hx
      exact hx
    exact h_main x h_mem
  have h1 : ∫ (x : ℝ) in ((k : ℝ) - 1)..(k : ℝ), x ^ β ≤ ∫ (x : ℝ) in ((k : ℝ) - 1)..(k : ℝ), (k : ℝ) ^ β := by
    exact intervalIntegral.integral_mono_on h1a h_int1 h_int2 h_main
  have h2 : ∫ (x : ℝ) in ((k : ℝ) - 1)..(k : ℝ), (k : ℝ) ^ β = (k : ℝ) ^ β := by
    simp
  rw [h2] at h1
  exact h1

lemma round1_h_main_0e8a4c (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  ∀ (k : ℕ), (k ≥ M → (∑ i ∈ Finset.Ico M k, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) = ∫ (x : ℝ) in ((M : ℝ) - 1)..((k : ℝ) - 1), x ^ β) := by
  intro k
  induction k with
  | zero =>
    intro h1
    exfalso
    linarith [hM_ge_1]
  | succ k ih =>
    intro h2
    by_cases h3 : k ≥ M
    ·
      have h4 : (∑ i ∈ Finset.Ico M (k + 1), (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) = (∑ i ∈ Finset.Ico M k, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) + (∫ (x : ℝ) in ((k : ℝ) - 1)..(k : ℝ), x ^ β) := by
        rw [Finset.sum_Ico_succ_top h3]
      have h5 : (∑ i ∈ Finset.Ico M k, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) = ∫ (x : ℝ) in ((M : ℝ) - 1)..((k : ℝ) - 1), x ^ β := ih h3
      rw [h4, h5]
      have h_k_ge_1 : (k : ℝ) ≥ 1 := by
        have hM1 : (M : ℝ) ≥ 1 := by exact_mod_cast hM_ge_1
        have h_k_ge_M : (k : ℝ) ≥ (M : ℝ) := by exact_mod_cast h3
        linarith
      have h_k_minus_1_nonneg : (k : ℝ) - 1 ≥ 0 := by linarith
      have h_M_minus_1_nonneg : (M : ℝ) - 1 ≥ 0 := by
        have hM1 : (M : ℝ) ≥ 1 := by exact_mod_cast hM_ge_1
        linarith
      have h61 : IntervalIntegrable (fun (x : ℝ) => x ^ β) MeasureTheory.volume ((M : ℝ) - 1) ((k : ℝ) - 1) := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.rpow
        · fun_prop
        · fun_prop
        · intro x hx
          right
          exact hβ_pos
      have h62 : IntervalIntegrable (fun (x : ℝ) => x ^ β) MeasureTheory.volume ((k : ℝ) - 1) (k : ℝ) := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.rpow
        · fun_prop
        · fun_prop
        · intro x hx
          right
          exact hβ_pos
      have h6 : (∫ (x : ℝ) in ((M : ℝ) - 1)..((k : ℝ) - 1), x ^ β) + (∫ (x : ℝ) in ((k : ℝ) - 1)..(k : ℝ), x ^ β) = (∫ (x : ℝ) in ((M : ℝ) - 1)..(k : ℝ), x ^ β) := by
        rw [intervalIntegral.integral_add_adjacent_intervals h61 h62]
      have h7 : (( (k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by
        simp
      have h_goal : ∫ (x : ℝ) in ((M : ℝ) - 1)..(( (k + 1 : ℕ) : ℝ) - 1), x ^ β = ∫ (x : ℝ) in ((M : ℝ) - 1)..(k : ℝ), x ^ β := by
        rw [h7]
      rw [h_goal]
      exact h6
    ·
      have h4 : k + 1 = M := by omega
      rw [h4]
      norm_num

theorem sum_of_integrals_eq_integral (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (n : ℕ)
  (hn_gt_M : n > M):
  (∑ i ∈ Finset.Ico M n, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) =
    ∫ (x : ℝ) in ((M : ℝ) - 1)..((n : ℝ) - 1), x ^ β := by
  have h_main : ∀ (k : ℕ), (k ≥ M → (∑ i ∈ Finset.Ico M k, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) = ∫ (x : ℝ) in ((M : ℝ) - 1)..((k : ℝ) - 1), x ^ β) :=
    round1_h_main_0e8a4c β hβ_pos M hM_ge_1
  have h_n_ge_M : n ≥ M := by linarith
  exact h_main n h_n_ge_M

theorem integral_power_eval (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (n : ℕ)
  (hn_gt_M : n > M):
  ∫ (x : ℝ) in ((M : ℝ) - 1)..((n : ℝ) - 1), x ^ β =
    (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) := by
  have h1 : -1 < β := by linarith
  have h_main : ∫ (x : ℝ) in ((M : ℝ) - 1)..((n : ℝ) - 1), x ^ β =
    (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) := by
    apply integral_rpow
    left
    exact h1
  exact h_main

lemma round1_h1_cf102d (β : ℝ)
  (M : ℕ)
  (n : ℕ)
  (hn : n ≥ 1):
  (1 - 1 / (n : ℝ)) ^ (β + 1) = (((n : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) := by
  have h_pos : (n : ℝ) > 0 := by
    have h₁ : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    linarith
  have h4 : (n : ℝ) - 1 ≥ 0 := by
    have h₁ : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    linarith
  have h2 : 1 - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) := by
    field_simp [h_pos.ne']
  rw [h2]
  have h3 : (((n : ℝ) - 1) / (n : ℝ)) ^ (β + 1) = (((n : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) := by
    rw [Real.div_rpow h4 h_pos.le]
  exact h3

theorem algebraic_rewriting_of_sequence_a (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (n : ℕ)
  (hn : n ≥ 1):
  ((((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) / ((n : ℝ) ^ (β + 1)) =
  (1 / (β + 1)) * ((1 - 1 / (n : ℝ)) ^ (β + 1)) - (1 / (β + 1)) * ((((M : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1))) := by
  have h1 : (1 - 1 / (n : ℝ)) ^ (β + 1) = (((n : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) := by
    exact round1_h1_cf102d β M n hn
  rw [h1]
  have h_pos : (n : ℝ) > 0 := by
    have h₁ : (n : ℝ) ≥ 1 := by exact_mod_cast hn
    linarith
  field_simp [h_pos.ne']

lemma round1_main_argument (β : ℝ)
  (hβ_pos : β > 0)
  (ε : ℝ)
  (hε : ε > 0):
  ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → |(1 - 1 / (n : ℝ)) ^ (β + 1) - 1| < ε := by
  have h1 : ContinuousAt (fun (x : ℝ) => x ^ (β + 1)) 1 := by
    apply continuousAt_rpow_const
    norm_num
  have h2 : ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ), |x - 1| < δ → |x ^ (β + 1) - (1 : ℝ) ^ (β + 1)| < ε := by
    exact Metric.continuousAt_iff.mp h1
  have h3 : ∃ δ > 0, ∀ (x : ℝ), |x - 1| < δ → |x ^ (β + 1) - 1| < ε := by
    have h4 := h2 ε hε
    simpa [show (1 : ℝ) ^ (β + 1) = 1 by simp] using h4
  rcases h3 with ⟨δ, hδ_pos, h4⟩
  have hδ_pos' : 0 < 1 / δ := by positivity
  have h5 : ∃ (N₁ : ℕ), (N₁ : ℝ) > 1 / δ := by
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
    exact ⟨K, by simpa using hK⟩
  rcases h5 with ⟨N₁, hN₁⟩
  have hN₁_pos : 0 < N₁ := by
    by_contra h
    have h' : N₁ = 0 := by omega
    rw [h'] at hN₁
    norm_num at hN₁
    linarith
  refine' ⟨N₁, _⟩
  intro n hn
  have h6 : n ≥ N₁ := hn
  have h7 : 0 < n := by
    have h8 : N₁ > 0 := hN₁_pos
    omega
  have h9 : (n : ℝ) > 0 := by exact_mod_cast h7
  have h10 : (n : ℝ) ≥ (N₁ : ℝ) := by exact_mod_cast h6
  have h11 : (n : ℝ) > 1 / δ := by linarith
  have h12 : 1 / (n : ℝ) < δ := by
    have h13 : (n : ℝ) > 1 / δ := h11
    have h14 : 1 / (n : ℝ) < δ := by
      calc
        1 / (n : ℝ) < 1 / (1 / δ) := by
          apply one_div_lt_one_div_of_lt (by positivity) h13
        _ = δ := by
          field_simp [hδ_pos.ne']
    exact h14
  have h15 : |(1 - 1 / (n : ℝ)) - 1| < δ := by
    have h16 : |(1 - 1 / (n : ℝ)) - 1| = 1 / (n : ℝ) := by
      have h17 : (1 - 1 / (n : ℝ)) - 1 = - (1 / (n : ℝ)) := by ring
      rw [h17]
      have h18 : |(- (1 / (n : ℝ)))| = 1 / (n : ℝ) := by
        rw [abs_neg, abs_of_pos (show (0 : ℝ) < 1 / (n : ℝ) by positivity)]
      exact h18
    rw [h16]
    exact h12
  have h19 : |(1 - 1 / (n : ℝ)) ^ (β + 1) - 1| < ε := h4 (1 - 1 / (n : ℝ)) h15
  exact h19

theorem limit_of_one_minus_one_over_n_power_converges_to_one (β : ℝ)
  (hβ_pos : β > 0):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → |(1 - 1 / (n : ℝ)) ^ (β + 1) - 1| < ε := by
  intro ε hε
  exact round1_main_argument β hβ_pos ε hε

lemma round1_h_main_3b4221 (β : ℝ)
  (hβ_pos : β > 0)
  (x : ℕ → ℝ)
  (hx_converges_to_one : ∀ (ε : ℝ), ε > 0 → ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → |x n - 1| < ε)
  (ε : ℝ)
  (hε_pos : ε > 0):
  ∃ (N₄ : ℕ), ∀ (n : ℕ), n ≥ N₄ → |(1 / (β + 1)) * x n - (1 / (β + 1))| < ε := by
  have h1 : β + 1 > 0 := by linarith
  set ε' := ε * (β + 1) with hε'_def
  have hε'_pos : ε' > 0 := by
    positivity
  have h2 : ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → |x n - 1| < ε' := hx_converges_to_one ε' hε'_pos
  rcases h2 with ⟨N₁, hN₁⟩
  use N₁
  intro n hn
  have h3 : |x n - 1| < ε' := hN₁ n hn
  have h4 : |(1 / (β + 1)) * x n - (1 / (β + 1))| = (1 / (β + 1)) * |x n - 1| := by
    have h5 : |(1 / (β + 1)) * x n - (1 / (β + 1))| = |(1 / (β + 1)) * (x n - 1)| := by
      ring_nf
    rw [h5]
    rw [abs_mul]
    have h6 : |(1 / (β + 1))| = 1 / (β + 1) := by
      rw [abs_of_pos]
      positivity
    rw [h6]
  rw [h4]
  have h7 : (1 / (β + 1)) * |x n - 1| < ε := by
    calc
      (1 / (β + 1)) * |x n - 1| < (1 / (β + 1)) * ε' := by gcongr
      _ = (1 / (β + 1)) * (ε * (β + 1)) := by rw [hε'_def]
      _ = ε := by
        field_simp [h1.ne']
  exact h7

theorem sequence_converging_to_one_scaled_converges_to_scaled_value (β : ℝ)
  (hβ_pos : β > 0)
  (x : ℕ → ℝ)
  (hx_converges_to_one : ∀ (ε : ℝ), ε > 0 → ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → |x n - 1| < ε):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₄ : ℕ), ∀ (n : ℕ), n ≥ N₄ → |(1 / (β + 1)) * x n - (1 / (β + 1))| < ε := by
  intro ε hε_pos
  exact round1_h_main_3b4221 β hβ_pos x hx_converges_to_one ε hε_pos

theorem sequence_converging_to_zero_scaled_converges_to_zero (β : ℝ)
  (hβ_pos : β > 0)
  (y : ℕ → ℝ)
  (hy_converges_to_zero : ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |y n - 0| < ε):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₅ : ℕ), ∀ (n : ℕ), n ≥ N₅ → |(1 / (β + 1)) * y n - 0| < ε := by
  intro ε hε_pos
  have h1 : β + 1 > 0 := by linarith
  set ε' : ℝ := ε * (β + 1) with hε'_def
  have hε'_pos : ε' > 0 := by
    apply mul_pos hε_pos h1
  have h_main : ∃ (N₅ : ℕ), ∀ (n : ℕ), n ≥ N₅ → |y n - 0| < ε' := hy_converges_to_zero ε' hε'_pos
  rcases h_main with ⟨N₅, hN₅⟩
  refine' ⟨N₅, _⟩
  intro n hn
  have h2 : |y n - 0| < ε' := hN₅ n hn
  have h3 : |(1 / (β + 1)) * y n - 0| = |(1 / (β + 1))| * |y n - 0| := by
    rw [show (1 / (β + 1)) * y n - 0 = (1 / (β + 1)) * (y n - 0) by ring]
    rw [abs_mul]
  rw [h3]
  have h4 : |(1 / (β + 1))| = 1 / (β + 1) := by
    rw [abs_of_pos (show (1 / (β + 1) : ℝ) > 0 by positivity)]
  rw [h4]
  have h5 : (1 / (β + 1 : ℝ)) * |y n - 0| < (1 / (β + 1 : ℝ)) * ε' := by
    apply mul_lt_mul_of_pos_left h2
    positivity
  have h6 : (1 / (β + 1 : ℝ)) * ε' = ε := by
    rw [hε'_def]
    field_simp [h1.ne']
  rw [h6] at h5
  exact h5

theorem difference_of_two_convergent_sequences_converges_to_difference_of_limits (u : ℕ → ℝ)
  (v : ℕ → ℝ)
  (L₁ : ℝ)
  (L₂ : ℝ)
  (hu_converges_to_L₁ : ∀ (ε : ℝ), ε > 0 → ∃ (N₄ : ℕ), ∀ (n : ℕ), n ≥ N₄ → |u n - L₁| < ε)
  (hv_converges_to_L₂ : ∀ (ε : ℝ), ε > 0 → ∃ (N₅ : ℕ), ∀ (n : ℕ), n ≥ N₅ → |v n - L₂| < ε):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₆ : ℕ), ∀ (n : ℕ), n ≥ N₆ → |(u n - v n) - (L₁ - L₂)| < ε := by
  intro ε hε
  have hε2 : ε / 2 > 0 := by linarith
  have h1 : ∃ (N₄ : ℕ), ∀ (n : ℕ), n ≥ N₄ → |u n - L₁| < ε / 2 := hu_converges_to_L₁ (ε / 2) hε2
  have h2 : ∃ (N₅ : ℕ), ∀ (n : ℕ), n ≥ N₅ → |v n - L₂| < ε / 2 := hv_converges_to_L₂ (ε / 2) hε2
  rcases h1 with ⟨N₄, hN₄⟩
  rcases h2 with ⟨N₅, hN₅⟩
  use max N₄ N₅
  intro n hn
  have h3 : n ≥ N₄ := by
    exact le_trans (le_max_left N₄ N₅) hn
  have h4 : n ≥ N₅ := by
    exact le_trans (le_max_right N₄ N₅) hn
  have h5 : |u n - L₁| < ε / 2 := hN₄ n h3
  have h6 : |v n - L₂| < ε / 2 := hN₅ n h4
  have h7 : |(u n - v n) - (L₁ - L₂)| = |(u n - L₁) - (v n - L₂)| := by ring_nf
  rw [h7]
  have h8 : |(u n - L₁) - (v n - L₂)| ≤ |u n - L₁| + |v n - L₂| := by apply abs_sub
  have h9 : |u n - L₁| + |v n - L₂| < ε := by linarith
  linarith

lemma round1_h1_c9e83c (x L C : ℝ)
  (h_L_gt_C : L > C)
  (h : |x - L| < L - C):
  C < x := by
  have h1 : -(L - C) < x - L := (abs_lt.mp h).1
  linarith

theorem real_abs_ineq_implies_gt (x L C : ℝ)
  (h_L_gt_C : L > C)
  (h : |x - L| < L - C):
  x > C := by
  have h_main : C < x := round1_h1_c9e83c x L C h_L_gt_C h
  exact h_main

theorem exists_N0_for_L_minus_C_bound (a : ℕ → ℝ)
  (L : ℝ)
  (C : ℝ)
  (hL_pos : L > 0)
  (hC_pos : C > 0)
  (hC_lt_L : C < L)
  (h_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - L| < ε):
  ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - L| < L - C := by
  have h1 : L - C > 0 := by linarith
  have h_main : ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - L| < L - C := h_converges (L - C) h1
  exact h_main

theorem apply_real_ineq_to_sequence (a : ℕ → ℝ)
  (L C : ℝ)
  (N₀ : ℕ)
  (h_L_gt_C : L > C)
  (h_abs_bound : ∀ (n : ℕ), n ≥ N₀ → |a n - L| < L - C)
  (h_ineq_lemma : ∀ (x L C : ℝ), L > C → |x - L| < L - C → x > C):
  ∀ (n : ℕ), n ≥ N₀ → a n > C := by
  intro n hn
  have h1 : |a n - L| < L - C := h_abs_bound n hn
  have h2 : a n > C := h_ineq_lemma (a n) L C h_L_gt_C h1
  exact h2

theorem beta_plus_one_is_positive (β : ℝ)
  (hβ_pos : β > 0):
  β + 1 > 0 := by
  linarith

theorem n_rpow_is_positive (β : ℝ)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (n : ℕ)
  (hn : n ≥ M + 1)
  (h_beta_plus_one_pos : β + 1 > 0):
  (n : ℝ) ^ (β + 1) > 0 := by
  have h1 : n > 0 := by
    omega
  have h2 : (n : ℝ) > 0 := by exact_mod_cast h1
  have h3 : (n : ℝ) ^ (β + 1) > 0 := by
    apply Real.rpow_pos_of_pos
    exact h2
  exact h3

theorem div_inequality_to_mul_inequality (x y z : ℝ)
  (hy_pos : y > 0)
  (h_ineq : x / y > z):
  x > z * y := by
  have h1 : x / y > z := h_ineq
  have h2 : y > 0 := hy_pos
  have h3 : (x / y) * y > z * y := mul_lt_mul_of_pos_right h1 h2
  have h4 : (x / y) * y = x := by
    field_simp [h2.ne']
  rw [h4] at h3
  exact h3

theorem exists_real_valued_function_from_N_to_g (g : ℕ+ → ℕ+):
  ∃ (f : ℕ → ℝ), ∀ (k : ℕ) (h_k : 0 < k), f k = (g (⟨k, h_k⟩ : ℕ+) : ℝ) := by
  use fun k : ℕ => if h_k' : 0 < k then (g (⟨k, h_k'⟩ : ℕ+) : ℝ) else 0
  intro k h_k
  simp [h_k]

lemma round1_h_main_c1d9ee (f : ℕ → ℝ)
  (M : ℕ):
  ∀ n : ℕ, M ≤ n → (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) = f n - f M := by
  intro n
  induction n with
  | zero =>
    intro h₁
    have h₂ : M ≤ 0 := h₁
    have h₃ : M = 0 := by linarith
    simp [h₃]
  | succ n ih =>
    intro h₂
    by_cases h₃ : M ≤ n
    ·
      have h₄ : M ≤ n + 1 := by linarith
      have h₅ : (∑ i ∈ Finset.Ico M (n + 1), (f (i + 1) - f i)) = (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) + (f (n + 1) - f n) := by
        rw [Finset.sum_Ico_succ_top h₃]
      rw [h₅]
      have h₆ := ih h₃
      rw [h₆]
      ring
    ·
      have h₄ : ¬M ≤ n := h₃
      have h₅ : M > n := by omega
      have h₆ : M = n + 1 := by omega
      rw [h₆]
      simp

theorem telescoping_sum_formula (f : ℕ → ℝ)
  (M n : ℕ)
  (h : M ≤ n):
  (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) = f n - f M := by
  have h_main : ∀ (n : ℕ), M ≤ n → (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) = f n - f M := by
    exact round1_h_main_c1d9ee f M
  exact h_main n h

lemma round1_h_main_df82ca (g : ℕ+ → ℕ+)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (β : ℝ)
  (K : ℝ)
  (hK_pos : K > 0)
  (h_diff_ineq : ∀ (n : ℕ+), (n : ℕ) ≥ M → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β)
  (n : ℕ)
  (hn_ge_M_plus_1 : n ≥ M + 1)
  (hM_pos : 0 < M)
  (hn_pos : 0 < n)
  (f : ℕ → ℝ)
  (hf : ∀ (k : ℕ) (h_k : 0 < k), f k = (g (⟨k, h_k⟩ : ℕ+) : ℝ)):
  ∀ i ∈ Finset.Ico M n, f (i + 1) - f i ≥ K * (i : ℝ) ^ β := by
  intro i hi
  have h1 : M ≤ i := (Finset.mem_Ico.mp hi).1
  have h2 : 0 < i := by
    linarith
  set i_pos : 0 < i := h2
  let n' : ℕ+ := ⟨i, i_pos⟩
  have h3 : (n' : ℕ) ≥ M := by
    exact_mod_cast h1
  have h4 : (g (n' + 1) : ℝ) - (g n' : ℝ) ≥ K * (n' : ℝ) ^ β := h_diff_ineq n' h3
  have h5 : (n' : ℝ) = (i : ℝ) := by
    simp [n']
  have h6 : (g (n' + 1) : ℝ) - (g n' : ℝ) ≥ K * (i : ℝ) ^ β := by
    rw [h5] at h4
    exact h4
  have h7 : n' + 1 = (⟨i + 1, by linarith⟩ : ℕ+) := by
    apply PNat.eq
    simp [n']
  have h8 : (g (n' + 1) : ℝ) = (g ( (⟨i + 1, by linarith⟩ : ℕ+) ) : ℝ) := by
    rw [h7]
  have h9 : (g n' : ℝ) = (g ( (⟨i, i_pos⟩ : ℕ+) ) : ℝ) := by
    rfl
  rw [h8, h9] at h6
  have h10 : f (i + 1) = (g ( (⟨i + 1, by linarith⟩ : ℕ+) ) : ℝ) := by
    apply hf
  have h11 : f i = (g ( (⟨i, i_pos⟩ : ℕ+) ) : ℝ) := by
    apply hf
  rw [h10, h11]
  exact h6

theorem pointwise_inequality_for_f (g : ℕ+ → ℕ+)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (β : ℝ)
  (K : ℝ)
  (hK_pos : K > 0)
  (h_diff_ineq : ∀ (n : ℕ+), (n : ℕ) ≥ M → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β)
  (n : ℕ)
  (hn_ge_M_plus_1 : n ≥ M + 1)
  (hM_pos : 0 < M)
  (hn_pos : 0 < n)
  (f : ℕ → ℝ)
  (hf : ∀ (k : ℕ) (h_k : 0 < k), f k = (g (⟨k, h_k⟩ : ℕ+) : ℝ)):
  ∀ i ∈ Finset.Ico M n, f (i + 1) - f i ≥ K * (i : ℝ) ^ β := by
  have h_main : ∀ i ∈ Finset.Ico M n, f (i + 1) - f i ≥ K * (i : ℝ) ^ β := by
    exact round1_h_main_df82ca g M hM_ge_1 β K hK_pos h_diff_ineq n hn_ge_M_plus_1 hM_pos hn_pos f hf
  exact h_main

theorem f_values_at_M_and_n (g : ℕ+ → ℕ+)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (n : ℕ)
  (hn_ge_M_plus_1 : n ≥ M + 1)
  (hM_pos : 0 < M)
  (hn_pos : 0 < n)
  (f : ℕ → ℝ)
  (hf : ∀ (k : ℕ) (h_k : 0 < k), f k = (g (⟨k, h_k⟩ : ℕ+) : ℝ)):
  f n = (g (⟨n, hn_pos⟩ : ℕ+) : ℝ) ∧ f M = (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) := by
  have h1 : f n = (g (⟨n, hn_pos⟩ : ℕ+) : ℝ) := by
    exact hf n hn_pos
  have h2 : f M = (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) := by
    exact hf M hM_pos
  exact ⟨h1, h2⟩

theorem sum_inequality_from_pointwise_inequality (f : ℕ → ℝ)
  (M n : ℕ)
  (K : ℝ)
  (β : ℝ)
  (hn_ge_M_plus_1 : n ≥ M + 1)
  (hM_pos : 0 < M)
  (hn_pos : 0 < n)
  (h_ineq : ∀ i ∈ Finset.Ico M n, f (i + 1) - f i ≥ K * (i : ℝ) ^ β):
  (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) ≥ K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) := by
  have h_main : (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) ≥ (∑ i ∈ Finset.Ico M n, (K * (i : ℝ) ^ β)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h_ineq i hi
  have h_factor : (∑ i ∈ Finset.Ico M n, (K * (i : ℝ) ^ β)) = K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) := by
    rw [Finset.mul_sum]
  rw [h_factor] at h_main
  exact h_main

lemma round1_h_main_5c1c2b (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (N0 : ℕ)
  (h_N0 : ∀ (k : ℕ+), (k : ℕ) ≥ N0 → (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ 2)
  (k : ℕ+)
  (hk : (k : ℕ) ≥ N0):
  (g (k + 1) : ℕ) ≥ (k : ℕ) ^ 2 := by
  have h1 : (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ 2 := h_N0 k hk
  have h2 : (g k : ℕ) ≥ (k : ℕ) := h_g_prop.2 k
  have h3 : (g k : ℝ) ≥ (k : ℝ) := by exact_mod_cast h2
  have h4 : (g k : ℝ) ^ 2 ≥ (k : ℝ) ^ 2 := by
    gcongr
  have h5 : (g (k + 1) : ℝ) ≥ (k : ℝ) ^ 2 := by linarith
  have h6 : (g (k + 1) : ℕ) ≥ (k : ℕ) ^ 2 := by
    exact_mod_cast h5
  exact h6

theorem lemma1_g_k_plus_one_ge_k_sq (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (N0 : ℕ)
  (h_N0 : ∀ (k : ℕ+), (k : ℕ) ≥ N0 → (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ 2)
  (k : ℕ+)
  (hk : (k : ℕ) ≥ N0):
  (g (k + 1) : ℕ) ≥ (k : ℕ) ^ 2 := by
  exact round1_h_main_5c1c2b r g h_ineq h_g_prop N0 h_N0 k hk

lemma round1_h3 (N0 : ℕ)
  (n : ℕ+)
  (h2 : (n : ℕ) ≥ 4):
  (n : ℕ) - 1 > 0 := by
  have h₃₁ : (n : ℕ) ≥ 4 := h2
  omega

theorem lemma2_exists_pos_nat_k_eq_n_minus_one (N0 : ℕ)
  (n : ℕ+)
  (h1 : (n : ℕ) ≥ N0 + 1)
  (h2 : (n : ℕ) ≥ 4):
  ∃ (k : ℕ+), (k : ℕ) = (n : ℕ) - 1 := by
  have h3 : (n : ℕ) - 1 > 0 := round1_h3 N0 n h2
  refine' ⟨⟨(n : ℕ) - 1, h3⟩, by simp⟩

lemma round1_h_main_bd8a99 (g : ℕ+ → ℕ+)
  (k : ℕ+)
  (n : ℕ+)
  (h_eq : (k : ℕ) + 1 = (n : ℕ)):
  k + 1 = n := by
  apply PNat.eq
  simpa using h_eq

theorem lemma3_g_k_plus_one_eq_g_n_when_k_plus_one_eq_n (g : ℕ+ → ℕ+)
  (k : ℕ+)
  (n : ℕ+)
  (h_eq : (k : ℕ) + 1 = (n : ℕ)):
  (g (k + 1) : ℕ) = (g n : ℕ) := by
  have h1 : k + 1 = n := by
    exact round1_h_main_bd8a99 g k n h_eq
  rw [h1]

lemma round1_h_main_921b43 (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  ((M : ℝ) - 1 = 0) ∨ ((M : ℝ) - 1 > 0) := by
  by_cases h : M = 1
  ·
    left
    rw [h]
    norm_num
  ·
    right
    have hM_gt_1 : M > 1 := by
      omega
    have h' : (M : ℝ) > (1 : ℝ) := by exact_mod_cast hM_gt_1
    linarith

theorem M_value_dichotomy_lemma (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  ((M : ℝ) - 1 = 0) ∨ ((M : ℝ) - 1 > 0) := by
  exact round1_h_main_921b43 M hM_ge_1

theorem zero_power_lemma (x p : ℝ)
  (hx : x = 0)
  (hp : p > 0):
  x ^ p = 0 := by
  have h₁ : p ≠ 0 := by
    linarith
  have h₂ : (0 : ℝ) ^ p = 0 := by
    apply zero_rpow
    exact h₁
  rw [hx]
  exact h₂

theorem positive_power_lemma (x p : ℝ)
  (hx : x > 0)
  (hp : p > 0):
  x ^ p > 0 := by
  apply rpow_pos_of_pos
  exact hx

lemma round1_zero_numerator_lemma (num p : ℝ)
  (h_num_zero : num = 0)
  (h_p_pos : p > 0):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |num / (n : ℝ) ^ p| < ε := by
  intro ε hε_pos
  use 0
  intro n hn
  have h1 : num / (n : ℝ) ^ p = 0 := by
    rw [h_num_zero]
    simp
  rw [h1]
  simp [hε_pos]

theorem zero_numerator_lemma (num p : ℝ)
  (h_num_zero : num = 0)
  (h_p_pos : p > 0):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |num / (n : ℝ) ^ p| < ε := by
  exact round1_zero_numerator_lemma num p h_num_zero h_p_pos

lemma round1_main_goal (num p : ℝ)
  (h_num_pos : num > 0)
  (h_p_pos : p > 0):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |num / (n : ℝ) ^ p| < ε := by
  intro ε hε
  have h₁ : 0 < num / ε := by positivity
  have h₂ : 0 < 1 / p := by positivity
  set x : ℝ := (num / ε) ^ (1 / p) with hx_def
  have h₃ : 0 < x := by
    positivity
  have h₄ : ∃ (N₂ : ℕ), (N₂ : ℝ) > x := by
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt x
    exact ⟨N₂, by simpa using hN₂⟩
  rcases h₄ with ⟨N₂, hN₂⟩
  use N₂
  intro n hn
  have h₅ : (n : ℝ) ≥ (N₂ : ℝ) := by exact_mod_cast hn
  have h₆ : (n : ℝ) > x := by linarith
  have h₇ : (n : ℝ) > 0 := by linarith
  have h₈ : ((n : ℝ) ^ p) > x ^ p := by
    apply Real.rpow_lt_rpow
    <;> linarith
  have h₉ : x ^ p = num / ε := by
    rw [hx_def]
    have h₁₀ : ((num / ε) ^ (1 / p)) ^ p = (num / ε) ^ ((1 / p) * p) := by
      rw [← Real.rpow_mul (by positivity)]
    rw [h₁₀]
    have h₁₁ : (1 / p) * p = 1 := by
      field_simp [h_p_pos.ne']
    rw [h₁₁]
    simp
  have h₁₁ : (n : ℝ) ^ p > num / ε := by
    rw [h₉] at h₈
    exact h₈
  have h₁₂ : 0 < (n : ℝ) ^ p := by positivity
  have h₁₃ : num / (n : ℝ) ^ p < ε := by
    calc
      num / (n : ℝ) ^ p < num / (num / ε) := by gcongr
      _ = ε := by
        field_simp [hε.ne']
  have h₁₄ : 0 < num / (n : ℝ) ^ p := by positivity
  have h₁₅ : |num / (n : ℝ) ^ p| = num / (n : ℝ) ^ p := by
    rw [abs_of_pos] ; positivity
  rw [h₁₅]
  exact h₁₃

theorem positive_numerator_lemma (num p : ℝ)
  (h_num_pos : num > 0)
  (h_p_pos : p > 0):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |num / (n : ℝ) ^ p| < ε := by
  exact round1_main_goal num p h_num_pos h_p_pos

theorem one_fourth_is_in_the_set :
  (1/4 : ℝ) ∈ {r : ℝ | ∃ g : ℕ+ → ℕ+, ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r} := by
  rcases exists_pnat_to_pnat_square_function with ⟨g, hg⟩
  have h : ∀ (n : ℕ+), (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ (1 / 4 : ℝ) := by
    intro n
    have h1 : (n : ℝ) ≥ 0 := pnat_coe_real_nonneg n
    have h2 : ((n : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (n : ℝ) := rpow_fourth_root_of_fourth_power (n : ℝ) h1
    have h3 : (g (g n) : ℝ) = (n : ℝ) ^ 4 := square_of_square_is_fourth_power g hg n
    have h4 : (g (g n) : ℝ) ^ (1 / 4 : ℝ) = ((n : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
      rw [h3]
    have h5 : (g (g n) : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) := by
      rw [h4]
      exact h2
    have h6 : (g (n + 1) : ℝ) - (g n : ℝ) = 2 * (n : ℝ) + 1 := diff_of_squares_is_twice_n_plus_one g hg n
    have h7 : 2 * (n : ℝ) + 1 ≥ (n : ℝ) := twice_n_plus_one_ge_n_for_pnat n
    have h8 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ (n : ℝ) := by
      linarith [h6, h7]
    linarith [h5, h8]
  exact ⟨g, h⟩

theorem g_is_strictly_increasing_and_ge_n (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r):
  (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n) := by
  have h1 : ∀ (n : ℕ+), (g (g n) : ℝ) ^ r ≥ 1 := by
    exact g_g_n_pow_r_ge_one r hr g h_ineq
  have h2 : ∀ (n : ℕ+), g (n + 1) > g n := by
    exact g_is_strictly_increasing r g h_ineq h1
  have h3 : ∀ (n : ℕ+), (g n : ℕ) ≥ n := by
    exact g_n_ge_n_from_strictly_increasing g h2
  exact ⟨h2, h3⟩

theorem exists_positive_delta_for_lower_bound (r : ℝ)
  (hr : r > 1/4):
  ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), r * x^2 + 1 - x ≥ δ := by
  set δ : ℝ := 1 - 1 / (4 * r) with hδ_def
  have h1 : δ > 0 := by
    exact delta_is_positive r hr
  have h2 : ∀ (x : ℝ), r * x^2 + 1 - x ≥ δ := by
    intro x
    have h21 : r * x^2 + 1 - x = r * (x - 1 / (2 * r))^2 + (1 - 1 / (4 * r)) := by
      exact quadratic_completion r hr x
    have h22 : r * (x - 1 / (2 * r))^2 + (1 - 1 / (4 * r)) ≥ (1 - 1 / (4 * r)) := by
      exact lower_bound_from_nonnegative_square r hr x
    linarith
  exact ⟨δ, h1, h2⟩

theorem sequence_has_linear_lower_bound (r : ℝ)
  (e : ℕ → ℝ)
  (δ : ℝ)
  (hr : r > 1/4)
  (h_e0 : e 0 = 1)
  (h_e_rec : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1)
  (h_δ_pos : δ > 0)
  (h_ineq : ∀ (x : ℝ), r * x^2 + 1 - x ≥ δ):
  ∀ (n : ℕ), e n ≥ 1 + (n : ℝ) * δ := by
  have h_lemma1 : ∀ (m : ℕ), e (m + 1) ≥ e m + δ := by
    exact e_succ_ge_e_add_delta r e δ h_e_rec h_ineq
  have h_base : e 0 ≥ 1 + (0 : ℝ) * δ := by
    exact base_case_n_zero e δ h_e0
  have h_inductive_step : ∀ (k : ℕ), (e k ≥ 1 + (k : ℝ) * δ) → (e (k + 1) ≥ e k + δ) → (e (k + 1) ≥ 1 + ((k : ℝ) + 1) * δ) := by
    intro k h1 h2
    exact inductive_step_property e δ k h1 h2
  intro n
  induction n with
  | zero =>
    simpa using h_base
  | succ n ih =>
    have h21 : e (n + 1) ≥ e n + δ := h_lemma1 n
    have h22 : e (n + 1) ≥ 1 + ((n : ℝ) + 1) * δ := by
      exact h_inductive_step n ih h21
    simpa [add_assoc, mul_add, add_mul] using h22

theorem lemma_inductive_step (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (e : ℕ → ℝ)
  (he1 : e 0 = 1)
  (he2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1)
  (h_growth_step : ∀ (α : ℝ)
    (hα : α ≥ 1)
    (N₀ : ℕ)
    (C : ℝ)
    (hC_pos : C > 0)
    (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α),
    ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * α^2 + 1))
  (m : ℕ)
  (N_m : ℕ)
  (C_m : ℝ)
  (hC_m_pos : C_m > 0)
  (h_hyp_m : ∀ (n : ℕ+), (n : ℕ) ≥ N_m → (g n : ℝ) ≥ C_m * (n : ℝ) ^ (e m))
  (h_e_m_ge_1 : e m ≥ 1):
  ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (e (m + 1)) := by
  have h1 : ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * (e m)^2 + 1) := by
    exact lemma_apply_h_growth_step_to_get_intermediate_bound r g e m N_m C_m h_e_m_ge_1 hC_m_pos h_hyp_m h_growth_step
  rcases h1 with ⟨N₁, C₁, hC₁_pos, h_bound_intermediate⟩
  have h_exponent_eq : r * (e m)^2 + 1 = e (m + 1) := by
    exact lemma_exponent_value_from_recurrence r e m he2
  have h_final_bound : ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (e (m + 1)) := by
    intro n hn
    have h_bound1 : (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * (e m)^2 + 1) := h_bound_intermediate n hn
    have h_n_pos : (n : ℝ) > 0 := lemma_pnat_cast_real_positive n
    have h_power_eq : C₁ * (n : ℝ) ^ (r * (e m)^2 + 1) = C₁ * (n : ℝ) ^ (e (m + 1)) := by
      exact lemma_equal_exponents_give_equal_power_expression C₁ (n : ℝ) (r * (e m)^2 + 1) (e (m + 1)) h_n_pos (by rw [h_exponent_eq])
    exact lemma_inequality_and_equality_transitivity (g n : ℝ) (C₁ * (n : ℝ) ^ (r * (e m)^2 + 1)) (C₁ * (n : ℝ) ^ (e (m + 1))) h_bound1 h_power_eq
  exact ⟨N₁, C₁, hC₁_pos, h_final_bound⟩

theorem exists_N1_for_coeff_domination (C : ℝ)
  (hC_pos : C > 0)
  (δ : ℝ)
  (hδ_pos : δ > 0):
  ∃ (N₁ : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (C : ℝ) * (n : ℝ) ^ δ ≥ 1 := by
  set B : ℝ := (1 / C) ^ (1 / δ) with hB_def
  have h1 : ∃ (N₁ : ℕ), (N₁ : ℝ) ≥ B := by
    exact exists_nat_ge_real B
  rcases h1 with ⟨N₁, hN₁_ge_B⟩
  refine' ⟨N₁, _⟩
  intro n hn
  have h2 : (n : ℝ) ≥ (N₁ : ℝ) := by
    exact pnat_coe_ge_of_nat_coe_ge N₁ n hn
  have h3 : (n : ℝ) ≥ B := by
    linarith
  have h4 : C * (n : ℝ) ^ δ ≥ 1 := by
    exact real_ge_implies_C_mul_pow_ge_one C hC_pos δ hδ_pos B (by simp [hB_def]) n h3
  exact h4

theorem lemma3 (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (k : ℕ)
  (N1 : ℕ)
  (h_lemma1 : ∀ (n : ℕ+), (n : ℕ) ≥ N1 → (g (g n) : ℕ) ≥ (g n : ℕ) ^ k):
  ∀ (n : ℕ+), (n : ℕ) ≥ N1 → (g (n + 1) : ℝ) > (g n : ℝ) ^ ((k : ℝ) * r) := by
  intro n hn
  have h2 : (g (g n) : ℝ) ≥ (g n : ℝ) ^ k := by
    exact convert_nat_inequality_to_real_power_inequality g n k (h_lemma1 n hn)
  have h3 : (g n : ℝ) ≥ 0 ∧ (g (g n) : ℝ) ≥ 0 := by
    exact pnat_function_values_are_nonnegative g h_g_prop n
  have h31 : (g n : ℝ) ≥ 0 := h3.left
  have h32 : (g (g n) : ℝ) ≥ 0 := h3.right
  have hr_pos : r > 0 := by linarith
  have h5 : (g (g n) : ℝ) ^ r ≥ (g n : ℝ) ^ ((k : ℝ) * r) := by
    exact real_rpow_inequality_from_base_inequality (g n : ℝ) (g (g n) : ℝ) k r h31 h32 hr_pos h2
  have h6 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g n : ℝ) ^ ((k : ℝ) * r) := by
    exact get_lower_bound_on_difference_of_consecutive_terms r g k h_ineq n h5
  have h7 : (g (n + 1) : ℝ) ≥ (g n : ℝ) + (g n : ℝ) ^ ((k : ℝ) * r) := by
    exact sub_ge_implication_for_reals ((g (n + 1) : ℝ)) ((g n : ℝ)) ((g n : ℝ) ^ ((k : ℝ) * r)) h6
  have h8 : (g n : ℝ) > 0 := by
    exact pnat_function_is_strictly_positive g h_g_prop n
  have h9 : (g n : ℝ) + (g n : ℝ) ^ ((k : ℝ) * r) > (g n : ℝ) ^ ((k : ℝ) * r) := by
    exact adding_positive_is_strictly_greater (g n : ℝ) ((g n : ℝ) ^ ((k : ℝ) * r)) h8
  linarith

theorem lemma5_g_n_plus_1_gt_g_g_n_r (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (n : ℕ+)
  (h : (g n : ℕ) ≥ n + 2):
  (g (n + 1) : ℝ) > (g (g n) : ℝ) ^ r := by
  have h1 : (g n : ℝ) > 0 := by
    exact lemma_g_n_is_positive_from_ge_n_plus_2 g n h
  have h2 : (g (n + 1) : ℝ) ≥ (g n : ℝ) + (g (g n) : ℝ) ^ r := by
    exact lemma_ineq_from_h_ineq_rearranged r g h_ineq n
  have h3 : (g n : ℝ) + (g (g n) : ℝ) ^ r > (g (g n) : ℝ) ^ r := by
    exact lemma_add_positive_gt_self (g n : ℝ) ((g (g n) : ℝ) ^ r) h1
  linarith

theorem lemma6_inequality_with_rpow (x y z r : ℝ)
  (hx_pos : x > 0)
  (hy_pos : y > 0)
  (hz_pos : z > 0)
  (hr_pos : r > 0)
  (h1 : x > y ^ r)
  (h2 : y ≥ z)
  (h3 : z ≥ x ^ 5):
  x > x ^ (5 * r) := by
  have h4 : y ≥ x ^ 5 := by
    exact lemma1_ge_transitivity x y z h2 h3
  have h5 : y ^ r ≥ x ^ (5 * r) := by
    exact lemma2_rpow_monotone x y r hx_pos hr_pos h4
  have h6 : x > x ^ (5 * r) := by
    exact lemma3_transitivity_inequality x (y ^ r) (x ^ (5 * r)) h1 h5
  exact h6

theorem lemma_g_of_g_n_lower_bound_from_hypotheses (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (α : ℝ)
  (hα : α ≥ 1)
  (N₀ : ℕ)
  (C : ℝ)
  (hC_pos : C > 0)
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α):
  ∀ (n : ℕ+), (n : ℕ) ≥ max 1 N₀ → (g (g n) : ℝ) ≥ C ^ (α + 1) * (n : ℝ) ^ (α ^ 2) := by
  intro n hn
  have h1 : (g n : ℝ) ≥ C * (n : ℝ) ^ α := by
    exact first_g_lower_bound g h_g_ge_n α hα N₀ C hC_pos h_hyp n hn
  have h2 : (g n : ℕ) ≥ N₀ := by
    exact g_n_nat_ge_N0 g h_g_ge_n N₀ n hn
  have h3 : (g (g n) : ℝ) ≥ C * (g n : ℝ) ^ α := by
    exact second_application_of_hyp g α hα N₀ C hC_pos h_hyp n h2
  have h4 : C * (g n : ℝ) ^ α ≥ C ^ (α + 1) * (n : ℝ) ^ (α ^ 2) := by
    exact power_inequality_step α hα C hC_pos N₀ n g hn h1
  linarith [h3, h4]

theorem sum_ge_integral_lower_bound (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  ∀ (n : ℕ), n > M →
    (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥
      (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) := by
  intro n hn_gt_M
  have h1 : ∀ i ∈ Finset.Ico M n, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β) ≤ (i : ℝ) ^ β := by
    intro i hi
    have h11 : i ≥ M := (Finset.mem_Ico.mp hi).1
    have h13 : i ≥ 1 := by linarith
    exact integral_le_pow_at_right_endpoint β hβ_pos i h13
  have h2 : (∑ i ∈ Finset.Ico M n, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) ≤ (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h1 i hi
  have h3 : (∑ i ∈ Finset.Ico M n, (∫ (x : ℝ) in ((i : ℝ) - 1)..(i : ℝ), x ^ β)) = ∫ (x : ℝ) in ((M : ℝ) - 1)..((n : ℝ) - 1), x ^ β := by
    exact sum_of_integrals_eq_integral β hβ_pos M hM_ge_1 n hn_gt_M
  have h4 : ∫ (x : ℝ) in ((M : ℝ) - 1)..((n : ℝ) - 1), x ^ β = (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) := by
    exact integral_power_eval β hβ_pos M hM_ge_1 n hn_gt_M
  linarith [h2, h3, h4]

theorem sequence_exceeds_constant_if_converges_to_larger (a : ℕ → ℝ)
  (L : ℝ)
  (hL_pos : L > 0)
  (h_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - L| < ε)
  (C : ℝ)
  (hC_pos : C > 0)
  (hC_lt_L : C < L):
  ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → a n > C := by
  have h_ineq_lemma : ∀ (x L C : ℝ), L > C → |x - L| < L - C → x > C := by
    intro x L C h_L_gt_C h
    exact real_abs_ineq_implies_gt x L C h_L_gt_C h
  have h_N0_exists : ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - L| < L - C := by
    exact exists_N0_for_L_minus_C_bound a L C hL_pos hC_pos hC_lt_L h_converges
  rcases h_N0_exists with ⟨N₀, hN₀_spec⟩
  have h3 : ∀ (n : ℕ), n ≥ N₀ → a n > C := by
    exact apply_real_ineq_to_sequence a L C N₀ (by linarith) hN₀_spec h_ineq_lemma
  exact ⟨N₀, h3⟩

theorem sequence_inequality_implies_sum_inequality (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (n : ℕ)
  (hn : n ≥ M + 1)
  (C_sum : ℝ)
  (hC_sum_pos : C_sum > 0)
  (h_ineq : (((( (n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) / ((n : ℝ) ^ (β + 1))) > C_sum):
  (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) > C_sum * (n : ℝ) ^ (β + 1) := by
  have h1 : β + 1 > 0 := by
    exact beta_plus_one_is_positive β hβ_pos
  have h2 : (n : ℝ) ^ (β + 1) > 0 := by
    exact n_rpow_is_positive β M hM_ge_1 n hn h1
  have h4 : ((( (n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) / ((n : ℝ) ^ (β + 1)) > C_sum := h_ineq
  set x : ℝ := ((( (n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) with hx_def
  set y : ℝ := ((n : ℝ) ^ (β + 1)) with hy_def
  set z : ℝ := C_sum with hz_def
  have h41 : x / y > z := by
    rw [hx_def, hy_def, hz_def] at *
    exact h4
  have h5 : x > z * y := by
    exact div_inequality_to_mul_inequality x y z h2 h41
  have h_final : (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) > C_sum * (n : ℝ) ^ (β + 1) := by
    rw [hx_def, hy_def, hz_def] at h5
    simpa using h5
  exact h_final

theorem g_n_ge_g_M_plus_K_times_sum (g : ℕ+ → ℕ+)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (β : ℝ)
  (K : ℝ)
  (hK_pos : K > 0)
  (h_diff_ineq : ∀ (n : ℕ+), (n : ℕ) ≥ M → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β)
  (n : ℕ)
  (hn_ge_M_plus_1 : n ≥ M + 1)
  (hM_pos : 0 < M)
  (hn_pos : 0 < n):
  (g (⟨n, hn_pos⟩ : ℕ+) : ℝ) ≥ (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) + K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) := by
  have h11 : ∃ (f : ℕ → ℝ), ∀ (k : ℕ) (h_k : 0 < k), f k = (g (⟨k, h_k⟩ : ℕ+) : ℝ) := by
    exact exists_real_valued_function_from_N_to_g g
  rcases h11 with ⟨f, hf⟩
  have h12 : M ≤ n := by linarith
  have h13 : (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) = f n - f M := by
    exact telescoping_sum_formula f M n h12
  have h14 : ∀ i ∈ Finset.Ico M n, f (i + 1) - f i ≥ K * (i : ℝ) ^ β := by
    exact pointwise_inequality_for_f g M hM_ge_1 β K hK_pos h_diff_ineq n hn_ge_M_plus_1 hM_pos hn_pos f hf
  have h15 : (∑ i ∈ Finset.Ico M n, (f (i + 1) - f i)) ≥ K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) := by
    exact sum_inequality_from_pointwise_inequality f M n K β hn_ge_M_plus_1 hM_pos hn_pos h14
  have h16 : f n = (g (⟨n, hn_pos⟩ : ℕ+) : ℝ) ∧ f M = (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) := by
    exact f_values_at_M_and_n g M hM_ge_1 n hn_ge_M_plus_1 hM_pos hn_pos f hf
  have h17 : f n - f M ≥ K * (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) := by linarith [h13, h15]
  have h161 : f n = (g (⟨n, hn_pos⟩ : ℕ+) : ℝ) := h16.1
  have h162 : f M = (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) := h16.2
  linarith

theorem lemma_g_n_ge_n_minus_1_sq_from_N0 (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (N0 : ℕ)
  (h_N0 : ∀ (k : ℕ+), (k : ℕ) ≥ N0 → (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ 2):
  (let N2 := max (N0 + 1) 4;
   ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (g n : ℕ) ≥ (n - 1) ^ 2) := by
  have h11 : ∀ (n : ℕ+), (n : ℕ) ≥ max (N0 + 1) 4 → (n : ℕ) ≥ N0 + 1 := by
    intro n hn
    have h111 : (n : ℕ) ≥ max (N0 + 1) 4 := hn
    have h112 : N0 + 1 ≤ max (N0 + 1) 4 := by
      apply le_max_left
    linarith
  have h12 : ∀ (n : ℕ+), (n : ℕ) ≥ max (N0 + 1) 4 → (n : ℕ) ≥ 4 := by
    intro n hn
    have h121 : (n : ℕ) ≥ max (N0 + 1) 4 := hn
    have h122 : 4 ≤ max (N0 + 1) 4 := by
      apply le_max_right
    linarith
  dsimp only
  intro n hn
  have h_n1 : (n : ℕ) ≥ N0 + 1 := h11 n hn
  have h_n2 : (n : ℕ) ≥ 4 := h12 n hn
  have h21 : ∃ (k : ℕ+), (k : ℕ) = (n : ℕ) - 1 := by
    exact lemma2_exists_pos_nat_k_eq_n_minus_one N0 n h_n1 h_n2
  rcases h21 with ⟨k, hk⟩
  have h22 : (k : ℕ) ≥ N0 := by
    have h221 : (n : ℕ) ≥ N0 + 1 := h_n1
    have h222 : (k : ℕ) = (n : ℕ) - 1 := hk
    omega
  have h23 : (g (k + 1) : ℕ) ≥ (k : ℕ) ^ 2 := by
    exact lemma1_g_k_plus_one_ge_k_sq r g h_ineq h_g_prop N0 h_N0 k h22
  have h24 : (k : ℕ) + 1 = (n : ℕ) := by
    have h241 : (k : ℕ) = (n : ℕ) - 1 := hk
    omega
  have h25 : (g (k + 1) : ℕ) = (g n : ℕ) := by
    exact lemma3_g_k_plus_one_eq_g_n_when_k_plus_one_eq_n g k n h24
  have h26 : (g n : ℕ) ≥ (k : ℕ) ^ 2 := by
    linarith
  have h27 : (g n : ℕ) ≥ ((n : ℕ) - 1) ^ 2 := by
    have h271 : (k : ℕ) = (n : ℕ) - 1 := hk
    rw [h271] at h26
    exact h26
  simpa using h27

theorem limit_of_M_minus_one_pow_div_n_pow_converges_to_zero (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |(((M : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) - 0| < ε := by
  have h1 : ((M : ℝ) - 1 = 0) ∨ ((M : ℝ) - 1 > 0) := by
    exact M_value_dichotomy_lemma M hM_ge_1
  have hp_pos : (β + 1) > 0 := by linarith
  intro ε hε_pos
  cases h1 with
  | inl h11 =>
    have h_num_zero : ((M : ℝ) - 1) ^ (β + 1) = 0 := by
      exact zero_power_lemma ((M : ℝ) - 1) (β + 1) h11 hp_pos
    have h3 : ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |(((M : ℝ) - 1) ^ (β + 1)) / (n : ℝ) ^ (β + 1)| < ε := by
      exact zero_numerator_lemma (((M : ℝ) - 1) ^ (β + 1)) (β + 1) h_num_zero hp_pos
    rcases h3 ε hε_pos with ⟨N₂, hN₂⟩
    refine ⟨N₂, fun n hn => ?_⟩
    have h5 := hN₂ n hn
    have h6 : |(((M : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) - 0| = |(((M : ℝ) - 1) ^ (β + 1)) / (n : ℝ) ^ (β + 1)| := by
      simp
    rw [h6]
    exact h5
  | inr h12 =>
    have h_num_pos : ((M : ℝ) - 1) ^ (β + 1) > 0 := by
      exact positive_power_lemma ((M : ℝ) - 1) (β + 1) h12 hp_pos
    have h4 : ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |(((M : ℝ) - 1) ^ (β + 1)) / (n : ℝ) ^ (β + 1)| < ε := by
      exact positive_numerator_lemma (((M : ℝ) - 1) ^ (β + 1)) (β + 1) h_num_pos hp_pos
    rcases h4 ε hε_pos with ⟨N₂, hN₂⟩
    refine ⟨N₂, fun n hn => ?_⟩
    have h5 := hN₂ n hn
    have h6 : |(((M : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) - 0| = |(((M : ℝ) - 1) ^ (β + 1)) / (n : ℝ) ^ (β + 1)| := by
      simp
    rw [h6]
    exact h5

theorem exists_divergent_sequence_e (r : ℝ)
  (hr : r > 1/4):
  ∃ (e : ℕ → ℝ), e 0 = 1 ∧ (∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1) ∧
  ∀ (k : ℝ), ∃ (M : ℕ), e M > k := by
  have h1 : ∃ (e : ℕ → ℝ), e 0 = 1 ∧ (∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1) := by
    exact exists_sequence_with_recurrence r
  rcases h1 with ⟨e, h_e0, h_e_rec⟩
  have h2 : ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), r * x^2 + 1 - x ≥ δ := by
    exact exists_positive_delta_for_lower_bound r hr
  rcases h2 with ⟨δ, h_δ_pos, h_ineq⟩
  have h3 : ∀ (n : ℕ), e n ≥ 1 + (n : ℝ) * δ := by
    exact sequence_has_linear_lower_bound r e δ hr h_e0 h_e_rec h_δ_pos h_ineq
  have h4 : ∀ (k : ℝ), ∃ (M : ℕ), e M > k := by
    intro k
    have h41 : ∃ (M : ℕ), (1 : ℝ) + (M : ℝ) * δ > k := by
      exact exists_natural_number_for_arithmetic_progression_exceeds δ h_δ_pos k
    rcases h41 with ⟨M, h411⟩
    refine' ⟨M, _⟩
    have h42 : e M ≥ (1 : ℝ) + (M : ℝ) * δ := h3 M
    linarith
  exact ⟨e, h_e0, h_e_rec, h4⟩

theorem induction_on_m_for_growth (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (e : ℕ → ℝ)
  (he1 : e 0 = 1)
  (he2 : ∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1)
  (h_growth_step : ∀ (α : ℝ)
    (hα : α ≥ 1)
    (N₀ : ℕ)
    (C : ℝ)
    (hC_pos : C > 0)
    (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α),
    ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * α^2 + 1)):
  ∀ (m : ℕ), ∃ (N_m : ℕ) (C_m : ℝ), C_m > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N_m → (g n : ℝ) ≥ C_m * (n : ℝ) ^ (e m) := by
  have h1 : ∀ (m : ℕ), e m ≥ 1 := by
    exact lemma_e_m_ge_one r hr e he1 he2
  have h_base : ∃ (N₀ : ℕ) (C₀ : ℝ), C₀ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C₀ * (n : ℝ) ^ (e 0) := by
    exact lemma_base_case_m_eq_0 r hr g h_g_ge_n e he1
  have h_induction : ∀ (m : ℕ), ∃ (N_m : ℕ) (C_m : ℝ), C_m > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N_m → (g n : ℝ) ≥ C_m * (n : ℝ) ^ (e m) := by
    intro m
    induction m with
    | zero =>
      rcases h_base with ⟨N₀, C₀, hC₀_pos, h_hyp0⟩
      refine' ⟨N₀, C₀, hC₀_pos, _⟩
      simpa [he1] using h_hyp0
    | succ m ih =>
      rcases ih with ⟨N_m, C_m, hC_m_pos, h_hyp_m⟩
      have h_e_m_ge_1 : e m ≥ 1 := h1 m
      have h_step : ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (e (m + 1)) := by
        exact lemma_inductive_step r hr g h_g_ge_n e he1 he2 h_growth_step m N_m C_m hC_m_pos h_hyp_m h_e_m_ge_1
      rcases h_step with ⟨N₁, C₁, hC₁_pos, h_hyp1⟩
      refine' ⟨N₁, C₁, hC₁_pos, _⟩
      exact h_hyp1
  intro m
  exact h_induction m

theorem from_super_exponential_to_nat_power (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (k : ℕ)
  (N₀ : ℕ)
  (C : ℝ)
  (hC_pos : C > 0)
  (α : ℝ)
  (h_α_gt_k : α > (k : ℝ))
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α):
  ∃ (N₂ : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N₂ → (g n : ℕ) ≥ (n : ℕ) ^ k := by
  set δ : ℝ := α - (k : ℝ) with hδ_def
  have hδ_pos : δ > 0 := by
    linarith
  have h1 : ∃ (N₁ : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (C : ℝ) * (n : ℝ) ^ δ ≥ 1 := by
    exact exists_N1_for_coeff_domination C hC_pos δ hδ_pos
  rcases h1 with ⟨N₁, hN₁⟩
  set N₂ : ℕ := max N₀ N₁ with hN₂_def
  refine' ⟨N₂, _⟩
  intro n hn
  have h_n_ge_N₀ : (n : ℕ) ≥ N₀ := by
    have h11 : N₂ ≥ N₀ := by apply le_max_left
    linarith
  have h_n_ge_N₁ : (n : ℕ) ≥ N₁ := by
    have h12 : N₂ ≥ N₁ := by apply le_max_right
    linarith
  have h13 : (g n : ℝ) ≥ C * (n : ℝ) ^ α := h_hyp n h_n_ge_N₀
  have h14 : (C : ℝ) * (n : ℝ) ^ δ ≥ 1 := hN₁ n h_n_ge_N₁
  have h15 : (n : ℝ) ^ α = (n : ℝ) ^ δ * (n : ℝ) ^ (k : ℝ) := by
    have h151 := real_power_decomposition_by_exponent_diff k α h_α_gt_k n
    have h152 : α - (k : ℝ) = δ := by
      rw [hδ_def]
    rw [h152] at h151
    exact h151
  have h16 : (g n : ℝ) ≥ (C * (n : ℝ) ^ δ) * (n : ℝ) ^ (k : ℝ) := by
    calc
      (g n : ℝ) ≥ C * (n : ℝ) ^ α := h13
      _ = C * ((n : ℝ) ^ δ * (n : ℝ) ^ (k : ℝ)) := by rw [h15]
      _ = (C * (n : ℝ) ^ δ) * (n : ℝ) ^ (k : ℝ) := by ring
  have h17 : (n : ℝ) > 0 := by
    have h171 : (n : ℕ) ≥ 1 := by exact PNat.one_le n
    have h172 : (n : ℝ) ≥ 1 := by exact_mod_cast h171
    linarith
  have h18 : (n : ℝ) ^ (k : ℝ) > 0 := by positivity
  have h19 : (C * (n : ℝ) ^ δ) * (n : ℝ) ^ (k : ℝ) ≥ (n : ℝ) ^ (k : ℝ) := by
    exact inequality_with_positive_factor C ((n : ℝ) ^ δ) ((n : ℝ) ^ (k : ℝ)) h14 h18
  have h20 : (g n : ℝ) ≥ (n : ℝ) ^ (k : ℝ) := by linarith
  exact real_power_to_nat_inequality n k (g n) h20

theorem super_polynomial_implies_exponential_growth (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_super : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g n : ℕ) ≥ (n : ℕ) ^ k)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n)):
  ∀ (M : ℝ), M > 0 → ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M := by
  intro M hM
  have h21 : ∃ (k : ℕ), (k : ℝ) * r ≥ M := by
    exact lemma2 r hr M hM
  rcases h21 with ⟨k, hk⟩
  have h11 : ∃ (N1 : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N1 → (g (g n) : ℕ) ≥ (g n : ℕ) ^ k := by
    exact lemma1 r hr g h_super h_g_prop k
  rcases h11 with ⟨N1, hN1⟩
  set N : ℕ := max N1 2 with hN_def
  have h31 : ∀ (n : ℕ+), (n : ℕ) ≥ N1 → (g (n + 1) : ℝ) > (g n : ℝ) ^ ((k : ℝ) * r) := by
    exact lemma3 r hr g h_ineq h_g_prop k N1 hN1
  have h51 : ∀ (n : ℕ+), (n : ℕ) ≥ N → (g n : ℝ) > 1 := by
    intro n hn
    have h511 : (n : ℕ) ≥ 2 := by
      have h5111 : N ≥ 2 := by
        apply le_max_right
      have h5112 : (n : ℕ) ≥ N := hn
      linarith
    exact lemma5 g h_g_prop n h511
  have h_final : ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M := by
    intro n hn
    have h512 : (g n : ℝ) > 1 := h51 n hn
    have h513 : (n : ℕ) ≥ N1 := by
      have hN12 : N ≥ N1 := by apply le_max_left
      have h5131 : (n : ℕ) ≥ N := hn
      linarith
    have h311 : (g (n + 1) : ℝ) > (g n : ℝ) ^ ((k : ℝ) * r) := h31 n h513
    have h41 : (g n : ℝ) ^ ((k : ℝ) * r) ≥ (g n : ℝ) ^ M := by
      exact lemma4 (g n : ℝ) h512 ((k : ℝ) * r) M (by linarith) (by linarith)
    have h514 : (g (n + 1) : ℝ) > (g n : ℝ) ^ M := by linarith
    have h515 : (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M := by linarith
    exact h515
  exact ⟨N, h_final⟩

theorem difference_lower_bound_lemma (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (α : ℝ)
  (hα : α ≥ 1)
  (N₀ : ℕ)
  (C : ℝ)
  (hC_pos : C > 0)
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α):
  ∃ (β : ℝ) (K : ℝ),
    β = r * α^2 ∧
    K = C ^ (r * (α + 1)) ∧
    K > 0 ∧
    ∀ (n : ℕ+), (n : ℕ) ≥ max 1 N₀ → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β := by
  set β : ℝ := r * α ^ 2 with hβ_def
  set K : ℝ := C ^ (r * (α + 1)) with hK_def
  have hr_pos : r > 0 := by
    linarith
  have hK_pos : K > 0 := by
    exact lemma_positivity_of_K C r α hC_pos hr_pos hα
  have h_ineq1 : ∀ (n : ℕ+), (n : ℕ) ≥ max 1 N₀ → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β := by
    intro n hn
    have h1 : (n : ℝ) > 0 := by
      exact lemma_pnat_cast_real_positive n
    have h4 : (g (g n) : ℝ) ≥ C ^ (α + 1) * (n : ℝ) ^ (α ^ 2) := by
      exact lemma_g_of_g_n_lower_bound_from_hypotheses r hr g h_g_ge_n α hα N₀ C hC_pos h_hyp n hn
    have h5 : C ^ (α + 1) * (n : ℝ) ^ (α ^ 2) ≥ 0 := by
      exact lemma_nonnegativity_of_intermediate_expression C (n : ℝ) α hC_pos h1
    have h6 : (g (g n) : ℝ) ^ r ≥ (C ^ (α + 1) * (n : ℝ) ^ (α ^ 2)) ^ r := by
      exact lemma_monotonicity_of_rpow ((g (g n) : ℝ)) (C ^ (α + 1) * (n : ℝ) ^ (α ^ 2)) r h4 h5 hr_pos
    have h7 : (C ^ (α + 1) * (n : ℝ) ^ (α ^ 2)) ^ r = C ^ (r * (α + 1)) * (n : ℝ) ^ (r * (α ^ 2)) := by
      exact lemma_rpow_of_product_and_power C (n : ℝ) r α hC_pos h1
    have h8 : (g (g n) : ℝ) ^ r ≥ C ^ (r * (α + 1)) * (n : ℝ) ^ (r * (α ^ 2)) := by
      linarith [h6, h7]
    have h9 : (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r := h_ineq n
    have h10 : C ^ (r * (α + 1)) * (n : ℝ) ^ (r * (α ^ 2)) = K * (n : ℝ) ^ β := by
      rw [hK_def, hβ_def]
    have h11 : (g (g n) : ℝ) ^ r ≥ K * (n : ℝ) ^ β := by
      linarith [h8, h10]
    linarith [h9, h11]
  exact ⟨β, K, by linarith, by linarith, hK_pos, h_ineq1⟩

theorem g_n_from_differences_and_powers_lemma (g : ℕ+ → ℕ+)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1)
  (β : ℝ)
  (K : ℝ)
  (hK_pos : K > 0)
  (h_diff_ineq : ∀ (n : ℕ+), (n : ℕ) ≥ M → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β)
  (N_sum : ℕ)
  (C_sum : ℝ)
  (hC_sum_pos : C_sum > 0)
  (h_sum_ineq : ∀ (n : ℕ), n ≥ N_sum → (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ C_sum * (n : ℝ) ^ (β + 1)):
  ∃ (N' : ℕ),
    N' ≥ N_sum ∧ N' ≥ M ∧
    ∀ (n : ℕ+), (n : ℕ) ≥ N' → (g n : ℝ) ≥ K * C_sum * (n : ℝ) ^ (β + 1) := by
  set N' : ℕ := max N_sum (M + 1) with hN'_def
  have h1 : N' ≥ N_sum ∧ N' ≥ M + 1 := by
    have h51 : max N_sum (M + 1) ≥ N_sum ∧ max N_sum (M + 1) ≥ M + 1 := by
      exact ⟨(max_of_two_naturals_ge_each N_sum (M + 1)).1, (max_of_two_naturals_ge_each N_sum (M + 1)).2⟩
    exact ⟨by simp [hN'_def], by simp [hN'_def]⟩
  have hN'_ge_N_sum : N' ≥ N_sum := h1.1
  have hN'_ge_M_plus_1 : N' ≥ M + 1 := h1.2
  have hN'_ge_M : N' ≥ M := by linarith
  have h10 : ∀ (n : ℕ+), (n : ℕ) ≥ N' → (g n : ℝ) ≥ K * C_sum * (n : ℝ) ^ (β + 1) := by
    intro n hn_ge_N'
    have h_n_ge_N_sum : (n : ℕ) ≥ N_sum := by
      linarith
    have h_n_ge_M_plus_1 : (n : ℕ) ≥ M + 1 := by
      linarith
    have hM_pos : 0 < M := by
      exact nat_ge_one_implies_pos M hM_ge_1
    have hn_pos : 0 < (n : ℕ) := by
      exact nat_n_ge_M_plus_one_and_M_ge_one_implies_n_pos M (n : ℕ) hM_ge_1 h_n_ge_M_plus_1
    have h_ineq1 : (g (⟨(n : ℕ), hn_pos⟩ : ℕ+) : ℝ) ≥ (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) + K * (∑ i ∈ Finset.Ico M (n : ℕ), (i : ℝ) ^ β) := by
      exact g_n_ge_g_M_plus_K_times_sum g M hM_ge_1 β K hK_pos h_diff_ineq (n : ℕ) h_n_ge_M_plus_1 hM_pos hn_pos
    have h_ineq2 : K * (∑ i ∈ Finset.Ico M (n : ℕ), (i : ℝ) ^ β) ≥ K * C_sum * ((n : ℕ) : ℝ) ^ (β + 1) := by
      exact K_mul_sum_ge_K_mul_C_sum_times_n_pow M N_sum C_sum K β hK_pos hC_sum_pos (n : ℕ) h_n_ge_N_sum h_sum_ineq
    have h_ineq3 : (g (⟨(n : ℕ), hn_pos⟩ : ℕ+) : ℝ) ≥ (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) + K * C_sum * ((n : ℕ) : ℝ) ^ (β + 1) := by
      linarith
    have h4 : (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) > 0 := by
      exact g_M_is_positive_real g M hM_pos
    have h4' : (g (⟨M, hM_pos⟩ : ℕ+) : ℝ) ≥ 0 := by linarith
    have h_final : (g (⟨(n : ℕ), hn_pos⟩ : ℕ+) : ℝ) ≥ K * C_sum * ((n : ℕ) : ℝ) ^ (β + 1) := by
      exact real_ge_add_and_nonneg_left_factor_implies_ge ((g (⟨(n : ℕ), hn_pos⟩ : ℕ+) : ℝ)) ((g (⟨M, hM_pos⟩ : ℕ+) : ℝ)) (K * C_sum * ((n : ℕ) : ℝ) ^ (β + 1)) h_ineq3 h4'
    simpa [hn_pos] using h_final
  exact ⟨N', ⟨hN'_ge_N_sum, hN'_ge_M, h10⟩⟩

theorem lemma1_g_n_ge_n_plus_2_exists (r : ℝ)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (h_exp_growth : ∀ (M : ℝ), M > 0 → ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M):
  ∃ (N2 : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (g n : ℕ) ≥ n + 2 := by
  have h1 : ∃ (N0 : ℕ), ∀ (k : ℕ+), (k : ℕ) ≥ N0 → (g (k + 1) : ℝ) ≥ (g k : ℝ) ^ 2 := by
    exact lemma_exists_N0_for_g_k_plus_1_ge_g_k_sq r g h_ineq h_g_prop h_exp_growth
  rcases h1 with ⟨N0, h_N0⟩
  have h2 : (let N2 := max (N0 + 1) 4; ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (g n : ℕ) ≥ (n - 1) ^ 2) := by
    exact lemma_g_n_ge_n_minus_1_sq_from_N0 r g h_ineq h_g_prop N0 h_N0
  have h3 : ∀ (n : ℕ), n ≥ 4 → (n - 1) ^ 2 ≥ n + 2 := by
    exact lemma_nat_inequality_n_minus_1_sq_ge_n_plus_2
  set N2 : ℕ := max (N0 + 1) 4 with hN2_def
  have h4 : ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (g n : ℕ) ≥ (n - 1) ^ 2 := by
    simpa [hN2_def] using h2
  have h5 : ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (n : ℕ) ≥ 4 := by
    intro n hn
    have h51 : N2 ≥ 4 := by
      rw [hN2_def]
      apply le_max_right
    linarith
  have h6 : ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (g n : ℕ) ≥ (n : ℕ) + 2 := by
    intro n hn
    have h61 : (g n : ℕ) ≥ (n - 1) ^ 2 := h4 n hn
    have h62 : (n : ℕ) ≥ 4 := h5 n hn
    have h63 : (n - 1) ^ 2 ≥ (n : ℕ) + 2 := h3 (n : ℕ) h62
    exact le_trans h63 h61
  exact ⟨N2, h6⟩

theorem asymptotic_sequence_converges (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  let a : ℕ → ℝ := fun (n : ℕ) => ((((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) / ((n : ℝ) ^ (β + 1));
  ∀ (ε : ℝ), ε > 0 → ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - (1 / (β + 1))| < ε := by
  dsimp
  intro ε hε
  set x : ℕ → ℝ := fun n => (1 - 1 / (n : ℝ)) ^ (β + 1) with hx_def
  set y : ℕ → ℝ := fun n => (((M : ℝ) - 1) ^ (β + 1)) / ((n : ℝ) ^ (β + 1)) with hy_def
  set u : ℕ → ℝ := fun n => (1 / (β + 1)) * x n with hu_def
  set v : ℕ → ℝ := fun n => (1 / (β + 1)) * y n with hv_def
  have hx_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → |x n - 1| < ε := by
    intro ε hε_pos
    exact limit_of_one_minus_one_over_n_power_converges_to_one β hβ_pos ε hε_pos
  have hu_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₄ : ℕ), ∀ (n : ℕ), n ≥ N₄ → |u n - (1 / (β + 1))| < ε := by
    intro ε hε_pos
    exact sequence_converging_to_one_scaled_converges_to_scaled_value β hβ_pos x (hx_converges) ε hε_pos
  have hy_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → |y n - 0| < ε := by
    intro ε hε_pos
    exact limit_of_M_minus_one_pow_div_n_pow_converges_to_zero β hβ_pos M hM_ge_1 ε hε_pos
  have hv_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₅ : ℕ), ∀ (n : ℕ), n ≥ N₅ → |v n - 0| < ε := by
    intro ε hε_pos
    exact sequence_converging_to_zero_scaled_converges_to_zero β hβ_pos y (hy_converges) ε hε_pos
  have huv_converges : ∃ (N₆ : ℕ), ∀ (n : ℕ), n ≥ N₆ → |(u n - v n) - (1 / (β + 1) - 0)| < ε := by
    have h : ∀ (ε : ℝ), ε > 0 → ∃ (N₆ : ℕ), ∀ (n : ℕ), n ≥ N₆ → |(u n - v n) - (1 / (β + 1) - 0)| < ε := by
      exact difference_of_two_convergent_sequences_converges_to_difference_of_limits u v (1 / (β + 1)) 0 (hu_converges) (hv_converges)
    exact h ε hε
  rcases huv_converges with ⟨N₆, hN₆⟩
  set N₀ : ℕ := max N₆ 1 with hN₀_def
  refine' ⟨N₀, _⟩
  intro n hn
  have h_n_ge_N₆ : n ≥ N₆ := by
    have h1 : n ≥ N₀ := hn
    have h2 : N₀ ≥ N₆ := by
      apply le_max_left
    linarith
  have h_n_ge_1 : n ≥ 1 := by
    have h1 : n ≥ N₀ := hn
    have h2 : N₀ ≥ 1 := by
      apply le_max_right
    linarith
  have h1 : ((((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) / ((n : ℝ) ^ (β + 1)) = u n - v n := by
    have h11 := algebraic_rewriting_of_sequence_a β hβ_pos M hM_ge_1 n h_n_ge_1
    simp only [hu_def, hv_def, hx_def, hy_def] at *
    linarith
  have h2 : |(u n - v n) - (1 / (β + 1) - 0)| < ε := hN₆ n h_n_ge_N₆
  have h2' : |(u n - v n) - (1 / (β + 1))| < ε := by simpa [sub_zero] using h2
  rw [h1]
  simpa [sub_zero] using h2'

theorem exponential_growth_and_inequality_imply_contradiction (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_prop : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n))
  (h_exp_growth : ∀ (M : ℝ), M > 0 → ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M):
  False := by
  have h1 : ∃ (N2 : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N2 → (g n : ℕ) ≥ n + 2 := by
    exact lemma1_g_n_ge_n_plus_2_exists r g h_ineq h_g_prop h_exp_growth
  rcases h1 with ⟨N2, h_N2_prop⟩
  have h2 : ∃ (N5 : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N5 → (g (n + 2) : ℝ) ≥ (g (n + 1) : ℝ) ^ 5 := by
    exact lemma3_exists_N5_g_n_plus_2_ge_g_n_plus_1_pow_5 g h_g_prop h_exp_growth
  rcases h2 with ⟨N5, h_N5_prop⟩
  set N : ℕ := max N2 N5 with hN_def
  have hN1 : N + 1 ≥ 1 := by omega
  set n : ℕ+ := ⟨N + 1, by bound⟩ with hn_def
  have h_n_ge_N2 : (n : ℕ) ≥ N2 := by
    have h11 : N ≥ N2 := by apply le_max_left
    have h111 : (n : ℕ) = N + 1 := by simp [hn_def]
    omega
  have h_n_ge_N5 : (n : ℕ) ≥ N5 := by
    have h12 : N ≥ N5 := by apply le_max_right
    have h121 : (n : ℕ) = N + 1 := by simp [hn_def]
    omega
  have h51 : (g n : ℕ) ≥ n + 2 := h_N2_prop n h_n_ge_N2
  have h6 : (g (n + 1) : ℝ) > (g (g n) : ℝ) ^ r := by
    exact lemma5_g_n_plus_1_gt_g_g_n_r r g h_ineq h_g_prop n h51
  have h7 : (g (g n) : ℝ) ≥ (g (n + 2) : ℝ) := by
    exact lemma2_g_g_n_ge_g_n_plus_2 g h_g_prop n h51
  have h8 : (g (n + 2) : ℝ) ≥ (g (n + 1) : ℝ) ^ 5 := by
    exact h_N5_prop n h_n_ge_N5
  have hr_pos : r > 0 := by linarith
  have hx_pos : (g (n + 1) : ℝ) > 0 := by positivity
  have hy_pos : (g (g n) : ℝ) > 0 := by positivity
  have hz_pos : (g (n + 2) : ℝ) > 0 := by positivity
  have h9 : (g (n + 1) : ℝ) > (g (n + 1) : ℝ) ^ (5 * r) := by
    exact lemma6_inequality_with_rpow (g (n + 1) : ℝ) (g (g n) : ℝ) (g (n + 2) : ℝ) r hx_pos hy_pos hz_pos hr_pos h6 h7 h8
  have h10 : (g (n + 1) : ℝ) > 1 := by
    exact lemma7_g_n_plus_1_gt_1 g h_g_prop n N2 h_n_ge_N2 h_N2_prop
  have h11 : (5 * r) < 1 := by
    exact lemma4_x_gt_x_pow_k_implies_k_lt_1 (g (n + 1) : ℝ) (5 * r) h10 h9
  have h12 : (5 * r) > 1 := by
    linarith
  linarith

theorem sum_of_powers_lemma (β : ℝ)
  (hβ_pos : β > 0)
  (M : ℕ)
  (hM_ge_1 : M ≥ 1):
  ∃ (N_sum : ℕ) (C_sum : ℝ),
    C_sum > 0 ∧
    ∀ (n : ℕ), n ≥ N_sum →
      (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ C_sum * (n : ℝ) ^ (β + 1) := by
  have h1 : β + 1 > 0 := by linarith
  set L : ℝ := 1 / (β + 1) with hL_def
  have hL_pos : L > 0 := by
    rw [hL_def]
    apply _root_.div_pos
    · norm_num
    · linarith
  set C_sum : ℝ := L / 2 with hC_sum_def
  have hC_sum_pos : C_sum > 0 := by
    rw [hC_sum_def]
    linarith
  have hC_sum_lt_L : C_sum < L := by
    rw [hC_sum_def]
    linarith
  set a : ℕ → ℝ := fun (n : ℕ) => ((((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1)) / ((n : ℝ) ^ (β + 1)) with ha_def
  have h_converges : ∀ (ε : ℝ), ε > 0 → ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - (1 / (β + 1))| < ε := by
    exact asymptotic_sequence_converges β hβ_pos M hM_ge_1
  have h_converges' : ∀ (ε : ℝ), ε > 0 → ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → |a n - L| < ε := by
    intro ε hε
    have h : ∀ (n : ℕ), |a n - L| < ε ↔ |a n - (1 / (β + 1))| < ε := by
      intro n
      have hL_def1 : L = 1 / (β + 1) := by
        rw [hL_def]
      rw [hL_def1]
    have h2 := h_converges ε hε
    rcases h2 with ⟨N₀, hN₀⟩
    refine' ⟨N₀, _⟩
    intro n hn
    have h21 := hN₀ n hn
    have h22 := (h n).mpr h21
    exact h22
  have h_N0_exists : ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → a n > C_sum := by
    exact sequence_exceeds_constant_if_converges_to_larger a L hL_pos h_converges' C_sum hC_sum_pos hC_sum_lt_L
  rcases h_N0_exists with ⟨N₀, hN₀⟩
  set N_sum : ℕ := max N₀ (M + 1) with hN_sum_def
  refine' ⟨N_sum, C_sum, hC_sum_pos, _⟩
  intro n hn
  have h2 : n ≥ N₀ := by
    have h21 : N_sum ≥ N₀ := by apply le_max_left
    linarith
  have h3 : n ≥ M + 1 := by
    have h22 : N_sum ≥ M + 1 := by apply le_max_right
    linarith
  have h4 : a n > C_sum := hN₀ n h2
  have h5 : (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) > C_sum * (n : ℝ) ^ (β + 1) := by
    exact sequence_inequality_implies_sum_inequality β hβ_pos M hM_ge_1 n h3 C_sum hC_sum_pos h4
  have h6 : n > M := by linarith
  have h7 : (∑ i ∈ Finset.Ico M n, (i : ℝ) ^ β) ≥ (((n : ℝ) - 1) ^ (β + 1) - ((M : ℝ) - 1) ^ (β + 1)) / (β + 1) := by
    have h71 := sum_ge_integral_lower_bound β hβ_pos M hM_ge_1 n h6
    simpa using h71
  linarith

theorem function_with_super_polynomial_growth_cannot_satisfy_inequality_for_r_greater_than_one_fourth (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_super : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g n : ℕ) ≥ (n : ℕ) ^ k)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r):
  False := by
  have h1 : (∀ (n : ℕ+), g (n + 1) > g n) ∧ (∀ (n : ℕ+), (g n : ℕ) ≥ n) := by
    exact g_is_strictly_increasing_and_ge_n r hr g h_ineq
  have h2 : ∀ (M : ℝ), M > 0 → ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g (n + 1) : ℝ) ≥ (g n : ℝ) ^ M := by
    exact super_polynomial_implies_exponential_growth r hr g h_super h_ineq h1
  have h3 : False := by
    exact exponential_growth_and_inequality_imply_contradiction r hr g h_ineq h1 h2
  exact h3

theorem growth_iteration_step (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r)
  (h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ))
  (α : ℝ)
  (hα : α ≥ 1)
  (N₀ : ℕ)
  (C : ℝ)
  (hC_pos : C > 0)
  (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α):
  ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * α^2 + 1) := by
  have h1 : ∃ (β : ℝ) (K : ℝ),
    β = r * α^2 ∧
    K = C ^ (r * (α + 1)) ∧
    K > 0 ∧
    ∀ (n : ℕ+), (n : ℕ) ≥ max 1 N₀ → (g (n + 1) : ℝ) - (g n : ℝ) ≥ K * (n : ℝ) ^ β := by
    exact difference_lower_bound_lemma r hr g h_ineq h_g_ge_n α hα N₀ C hC_pos h_hyp
  rcases h1 with ⟨β, K, hβ_eq, hK_eq, hK_pos, h_diff_ineq⟩
  have hβ_pos : β > 0 := by
    have h11 : r > 0 := by linarith
    have h12 : α ^ 2 > 0 := by
      have h121 : α ≥ 1 := hα
      have h122 : α ^ 2 ≥ 1 := by nlinarith
      linarith
    have h13 : β = r * α ^ 2 := hβ_eq
    nlinarith
  have hM_ge_1 : max 1 N₀ ≥ 1 := by
    simp
  have h2 : ∃ (N_sum : ℕ) (C_sum : ℝ),
    C_sum > 0 ∧
    ∀ (n : ℕ), n ≥ N_sum → (∑ i ∈ Finset.Ico (max 1 N₀) n, (i : ℝ) ^ β) ≥ C_sum * (n : ℝ) ^ (β + 1) := by
    exact sum_of_powers_lemma β hβ_pos (max 1 N₀) hM_ge_1
  rcases h2 with ⟨N_sum, C_sum, hC_sum_pos, h_sum_ineq⟩
  have h3 : ∃ (N' : ℕ),
    N' ≥ N_sum ∧ N' ≥ max 1 N₀ ∧
    ∀ (n : ℕ+), (n : ℕ) ≥ N' → (g n : ℝ) ≥ K * C_sum * (n : ℝ) ^ (β + 1) := by
    exact g_n_from_differences_and_powers_lemma g (max 1 N₀) hM_ge_1 β K hK_pos
      (fun (n : ℕ+) => h_diff_ineq n) N_sum C_sum hC_sum_pos h_sum_ineq
  rcases h3 with ⟨N', hN'_ge_N_sum, hN'_ge_M, h_g_bound⟩
  set N₁ := N' with hN₁_def
  set C₁ := K * C_sum with hC₁_def
  have hC₁_pos : C₁ > 0 := mul_pos hK_pos hC_sum_pos
  have h51 : β + 1 = r * α^2 + 1 := by
    linarith [hβ_eq]
  refine' ⟨N₁, C₁, hC₁_pos, _⟩
  intro n hn
  have h52 : (g n : ℝ) ≥ K * C_sum * (n : ℝ) ^ (β + 1) := h_g_bound n hn
  have h53 : (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (β + 1) := by
    simpa [hC₁_def] using h52
  have h54 : (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * α^2 + 1) := by
    rw [h51] at h53
    exact h53
  simpa using h54

theorem r_greater_than_one_fourth_implies_function_has_super_polynomial_growth (r : ℝ)
  (hr : r > 1/4)
  (g : ℕ+ → ℕ+)
  (h_ineq : ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r):
  ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g n : ℕ) ≥ (n : ℕ) ^ k := by
  intro k
  have h_g_ge_n : ∀ (n : ℕ+), (g n : ℕ) ≥ (n : ℕ) := by
    exact g_ge_n r hr g h_ineq
  have h1 : ∃ (e : ℕ → ℝ), e 0 = 1 ∧ (∀ m : ℕ, e (m + 1) = r * (e m)^2 + 1) ∧ ∀ (k : ℝ), ∃ (M : ℕ), e M > k := by
    exact exists_divergent_sequence_e r hr
  rcases h1 with ⟨e, he1, he2, he3⟩
  have h_growth_step : ∀ (α : ℝ)
    (hα : α ≥ 1)
    (N₀ : ℕ)
    (C : ℝ)
    (hC_pos : C > 0)
    (h_hyp : ∀ (n : ℕ+), (n : ℕ) ≥ N₀ → (g n : ℝ) ≥ C * (n : ℝ) ^ α),
    ∃ (N₁ : ℕ) (C₁ : ℝ), C₁ > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N₁ → (g n : ℝ) ≥ C₁ * (n : ℝ) ^ (r * α^2 + 1) := by
    intro α hα N₀ C hC_pos h_hyp
    exact growth_iteration_step r hr g h_ineq h_g_ge_n α hα N₀ C hC_pos h_hyp
  have h_induction : ∀ (m : ℕ), ∃ (N_m : ℕ) (C_m : ℝ), C_m > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N_m → (g n : ℝ) ≥ C_m * (n : ℝ) ^ (e m) := by
    exact induction_on_m_for_growth r hr g h_ineq h_g_ge_n e he1 he2 h_growth_step
  have h51 : ∃ (M : ℕ), e M > (k : ℝ) := by
    have h511 := he3 ((k : ℝ))
    simpa using h511
  rcases h51 with ⟨M, hM⟩
  have h52 : ∃ (N_M : ℕ) (C_M : ℝ), C_M > 0 ∧ ∀ (n : ℕ+), (n : ℕ) ≥ N_M → (g n : ℝ) ≥ C_M * (n : ℝ) ^ (e M) := by
    exact h_induction M
  rcases h52 with ⟨N_M, C_M, hC_M_pos, h_hyp⟩
  have h_final : ∃ (N₂ : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N₂ → (g n : ℕ) ≥ (n : ℕ) ^ k := by
    exact from_super_exponential_to_nat_power r hr g k N_M C_M hC_M_pos (e M) hM h_hyp
  simpa using h_final

theorem putnam_2025_b6 :
  IsGreatest {r : ℝ | ∃ g : ℕ+ → ℕ+, ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r} (1/4 : ℝ) := by
    have h1 : (1/4 : ℝ) ∈ {r : ℝ | ∃ g : ℕ+ → ℕ+, ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r} := by
      exact one_fourth_is_in_the_set
    have h2 : ∀ r : ℝ, r ∈ {r : ℝ | ∃ g : ℕ+ → ℕ+, ∀ n : ℕ+, (g (n + 1) : ℝ) - (g n : ℝ) ≥ (g (g n) : ℝ) ^ r} → r ≤ (1/4 : ℝ) := by
      intro r hr
      by_contra h21
      have h22 : r > (1/4 : ℝ) := by linarith
      rcases hr with ⟨g, h_ineq⟩
      have h_super : ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ+), (n : ℕ) ≥ N → (g n : ℕ) ≥ (n : ℕ) ^ k := by
        exact r_greater_than_one_fourth_implies_function_has_super_polynomial_growth r h22 g h_ineq
      have h_contra : False := by
        exact function_with_super_polynomial_growth_cannot_satisfy_inequality_for_r_greater_than_one_fourth r h22 g h_super h_ineq
      exact h_contra
    exact ⟨h1, fun r hr => h2 r hr⟩

end Putnam2025B6
