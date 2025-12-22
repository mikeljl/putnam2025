import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Regular
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
set_option linter.unusedVariables false

namespace Putnam2025B4

def MatrixProp (n : ℕ) (A : ℕ → ℕ → ℕ) : Prop :=
  (∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i + j ≤ n → A i j = 0) ∧
  (∀ i j : ℕ, 1 ≤ i → i ≤ n - 1 → 1 ≤ j → j ≤ n →
    A (i + 1) j = A i j ∨ A (i + 1) j = A i j + 1) ∧
  (∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n - 1 →
    A i (j + 1) = A i j ∨ A i (j + 1) = A i j + 1)

def colSum (n : ℕ) (A : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun i => A (i + 1) j)

def colNonzeros (n : ℕ) (A : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => A (i + 1) j ≠ 0)).card

def totalSum (n : ℕ) (A : ℕ → ℕ → ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun j => colSum n A (j + 1))

def nonzeroCount (n : ℕ) (A : ℕ → ℕ → ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun j => colNonzeros n A (j + 1))

lemma round1_h1 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (j : ℕ)
  (hj1 : 1 ≤ j)
  (hj2 : j < n):
  ∀ (i : ℕ), 1 ≤ i → i ≤ n → A i j ≤ i - 1 := by
  intro i
  induction i with
  | zero =>
    intro h_i1 h_i2
    omega
  | succ i ih =>
    intro h_i1 h_i2
    cases i with
    | zero =>
      have h_i1' : 1 ≤ 1 := by norm_num
      have h_i2' : 1 ≤ n := by omega
      have h_j_le_n : j ≤ n := by omega
      have h9 : A 1 j = 0 := h.1 1 j (by omega) (by omega) hj1 h_j_le_n (by omega)
      simp [h9]
    | succ i' =>
      have h10 := h.2.1 (i' + 1) j (by omega) (by omega) (by omega) (by omega)
      simp at h10 ⊢ ; omega

lemma round1_h2 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (i : ℕ)
  (h_i1 : 1 ≤ i)
  (h_i2 : i ≤ n):
  A i n ≤ i := by
  have h_j : 1 ≤ n - 1 := by omega
  have h_j2 : n - 1 < n := by omega
  have h1' := round1_h1 n hn A h (n - 1) h_j h_j2
  have h3 : A i (n - 1) ≤ i - 1 := h1' i h_i1 h_i2
  have h5 : A i ((n - 1) + 1) = A i (n - 1) ∨ A i ((n - 1) + 1) = A i (n - 1) + 1 := h.2.2 i (n - 1) (by omega) (by omega) (by omega) (by omega)
  have h6 : (n - 1) + 1 = n := by omega
  rw [h6] at h5
  rcases h5 with (h5 | h5)
  ·
    rw [h5]
    have h7 : A i (n - 1) ≤ i - 1 := h3
    omega
  ·
    rw [h5]
    have h7 : A i (n - 1) ≤ i - 1 := h3
    omega

lemma round1_h3 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  ∀ (i j : ℕ), 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → A i j ≤ i := by
  intro i j h_i1 h_i2 h_j1 h_j2
  by_cases h_j_lt_n : j < n
  ·
    have h4 : A i j ≤ i - 1 := round1_h1 n hn A h j h_j1 h_j_lt_n i h_i1 h_i2
    omega
  ·
    have h_j_eq_n : j = n := by omega
    rw [h_j_eq_n]
    exact round1_h2 n hn A h i h_i1 h_i2

lemma round2_h1 (n : ℕ)
  (A : ℕ → ℕ → ℕ)
  (j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ n)
  (h : MatrixProp n A)
  (h3 : ∀ (i j : ℕ), 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → A i j ≤ i):
  let b : ℕ → ℕ := fun i => A (i + 1) j
  ∀ m : ℕ, m < n → b m ≤ ((Finset.range m).filter (fun i => b i ≠ 0)).card + 1 := by
  dsimp only
  intro m
  induction m with
  | zero =>
    intro hmn
    have h4 : A 1 j ≤ 1 := h3 1 j (by norm_num) (by linarith) (by linarith) (by linarith)
    simpa using h4
  | succ m ih =>
    intro hmn
    have h1 : m < n := by linarith
    have h2 : m ≤ n - 2 := by omega
    have h_step1 : (A (m + 2) j = A (m + 1) j ∨ A (m + 2) j = A (m + 1) j + 1) := by
      have h5 := h.2.1 (m + 1) j (by omega) (by omega) (by linarith) (by linarith)
      simpa using h5
    let S_m := (Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)
    let S_mp1 := (Finset.range (m + 1)).filter (fun i => (A (i + 1) j) ≠ 0)
    have h_ih1 : A (m + 1) j ≤ S_m.card + 1 := ih h1
    by_cases hbm : (A (m + 1) j) = 0
    ·
      have hS : S_mp1 = S_m := by
        ext x
        simp only [S_mp1, S_m, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h_x_lt, h_A_ne_zero⟩
          have h_x_lt_m : x < m := by
            by_contra h
            have h' : x ≥ m := by omega
            have h_x_eq_m : x = m := by omega
            rw [h_x_eq_m] at h_A_ne_zero
            rw [hbm] at h_A_ne_zero ; contradiction
          exact ⟨h_x_lt_m, h_A_ne_zero⟩
        · rintro ⟨h_x_lt_m, h_A_ne_zero⟩
          exact ⟨by omega, h_A_ne_zero⟩
      have h_bmp1 : A (m + 2) j ≤ S_mp1.card + 1 := by
        have h6 : A (m + 2) j = 0 ∨ A (m + 2) j = 1 := by
          rcases h_step1 with (h | h) <;> simp [hbm, h]
        rw [hS]
        rcases h6 with (h6 | h6) <;> simp [h6]
      simpa using h_bmp1
    ·
      have hS : S_mp1 = S_m ∪ ({m} : Finset ℕ) := by
        ext x
        simp only [S_mp1, S_m, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
        simp_all [S_m]
        obtain ⟨left, right⟩ := hj
        cases h_step1 with
        | inl h_1 =>
          apply Iff.intro
          · intro a
            simp_all only [not_false_eq_true, and_true]
            obtain ⟨left_1, right_1⟩ := a
            omega
          · intro a
            cases a with
            | inl h_2 =>
              simp_all only [not_false_eq_true, and_true]
              obtain ⟨left_1, right_1⟩ := h_2
              omega
            | inr h_3 =>
              subst h_3
              simp_all only [lt_add_iff_pos_right, zero_lt_one, not_false_eq_true, and_self]
        | inr h_2 =>
          apply Iff.intro
          · intro a
            simp_all only [not_false_eq_true, and_true]
            obtain ⟨left_1, right_1⟩ := a
            omega
          · intro a
            cases a with
            | inl h_1 =>
              simp_all only [not_false_eq_true, and_true]
              obtain ⟨left_1, right_1⟩ := h_1
              omega
            | inr h_3 =>
              subst h_3
              simp_all only [lt_add_iff_pos_right, zero_lt_one, not_false_eq_true, and_self]
      have h_disj : Disjoint S_m ({m} : Finset ℕ) := by
        rw [Finset.disjoint_left]
        intro x hx
        have h_x_in_range_m : x ∈ Finset.range m := (Finset.mem_filter.mp hx).1
        have h_x_lt_m : x < m := Finset.mem_range.mp h_x_in_range_m
        simp only [Finset.mem_singleton] at *
        omega
      have h_card : S_mp1.card = S_m.card + 1 := by
        rw [hS]
        rw [Finset.card_union_of_disjoint h_disj]
        simp
      have h_bmp1 : A (m + 2) j ≤ A (m + 1) j + 1 := by
        rcases h_step1 with (h | h) <;> omega
      have h_goal : A (m + 2) j ≤ S_mp1.card + 1 := by
        rw [h_card]
        linarith
      simpa using h_goal

lemma round2_h2 (n : ℕ)
  (A : ℕ → ℕ → ℕ)
  (j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ n)
  (h : MatrixProp n A)
  (h3 : ∀ (i j : ℕ), 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → A i j ≤ i)
  (h1 : ∀ m : ℕ, m < n → (A (m + 1) j) ≤ ((Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)).card + 1):
  ∀ m : ℕ, m ≤ n → 2 * (Finset.sum (Finset.range m) (fun i => A (i + 1) j)) ≤
    ((Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)).card * (((Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)).card + 1) := by
  intro m
  induction m with
  | zero =>
    intro hmn
    simp
  | succ m ih =>
    intro hmn
    let S_m := (Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)
    let S_mp1 := (Finset.range (m + 1)).filter (fun i => (A (i + 1) j) ≠ 0)
    let b_m := A (m + 1) j
    have h_ih' : 2 * (Finset.sum (Finset.range m) (fun i => A (i + 1) j)) ≤ S_m.card * (S_m.card + 1) := ih (by linarith)
    by_cases hbm : b_m = 0
    ·
      have h6 : A (m + 1) j = 0 := by exact hbm
      have hS : S_mp1 = S_m := by
        ext x
        simp only [S_mp1, S_m, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨h_x_lt, h_A_ne_zero⟩
          have h_x_lt_m : x < m := by
            by_contra h
            have h' : x ≥ m := by omega
            have h_x_eq_m : x = m := by omega
            rw [h_x_eq_m] at h_A_ne_zero
            simp [h6] at h_A_ne_zero
          exact ⟨h_x_lt_m, h_A_ne_zero⟩
        · rintro ⟨h_x_lt_m, h_A_ne_zero⟩
          exact ⟨by omega, h_A_ne_zero⟩
      have h_sum : Finset.sum (Finset.range (m + 1)) (fun i => A (i + 1) j) = Finset.sum (Finset.range m) (fun i => A (i + 1) j) := by
        have h7 : Finset.sum (Finset.range (m + 1)) (fun i => A (i + 1) j) = Finset.sum (Finset.range m) (fun i => A (i + 1) j) + A (m + 1) j := by
          rw [Finset.sum_range_succ]
        rw [h7, h6] ; simp
      have h_card_eq : S_mp1.card = S_m.card := by
        rw [hS]
      have h_goal : 2 * (Finset.sum (Finset.range (m + 1)) (fun i => A (i + 1) j)) ≤ S_mp1.card * (S_mp1.card + 1) := by
        have h9 : 2 * (Finset.sum (Finset.range (m + 1)) (fun i => A (i + 1) j)) = 2 * (Finset.sum (Finset.range m) (fun i => A (i + 1) j)) := by
          rw [h_sum]
        rw [h9]
        have h10 : S_mp1.card * (S_mp1.card + 1) = S_m.card * (S_m.card + 1) := by
          rw [h_card_eq]
        rw [h10]
        exact h_ih'
      exact h_goal
    ·
      have h6 : A (m + 1) j ≠ 0 := hbm
      have hS : S_mp1 = S_m ∪ ({m} : Finset ℕ) := by
        ext x
        simp only [S_mp1, S_m, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
        simp_all only [ne_eq, not_false_eq_true, implies_true, S_m, b_m]
        obtain ⟨left, right⟩ := hj
        apply Iff.intro
        · intro a
          simp_all only [not_false_eq_true, and_true]
          obtain ⟨left_1, right_1⟩ := a
          omega
        · intro a
          cases a with
          | inl h_1 =>
            simp_all only [not_false_eq_true, and_true]
            obtain ⟨left_1, right_1⟩ := h_1
            omega
          | inr h_2 =>
            subst h_2
            simp_all only [lt_add_iff_pos_right, zero_lt_one, not_false_eq_true, and_self]
      have h_disj : Disjoint S_m ({m} : Finset ℕ) := by
        rw [Finset.disjoint_left]
        intro x hx
        have h_x_in_range_m : x ∈ Finset.range m := (Finset.mem_filter.mp hx).1
        have h_x_lt_m : x < m := Finset.mem_range.mp h_x_in_range_m
        simp only [Finset.mem_singleton] at *
        omega
      have h_card : S_mp1.card = S_m.card + 1 := by
        rw [hS]
        rw [Finset.card_union_of_disjoint h_disj]
        simp
      have h_b1 : b_m ≤ S_m.card + 1 := by
        have h5 : m < n := by linarith
        exact h1 m h5
      have h_sum : Finset.sum (Finset.range (m + 1)) (fun i => A (i + 1) j) = Finset.sum (Finset.range m) (fun i => A (i + 1) j) + b_m := by
        have h7 : Finset.sum (Finset.range (m + 1)) (fun i => A (i + 1) j) = Finset.sum (Finset.range m) (fun i => A (i + 1) j) + A (m + 1) j := by
          rw [Finset.sum_range_succ]
        simpa using h7
      rw [h_sum, h_card]
      nlinarith

lemma lemma1 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ n):
  2 * colSum n A j ≤ colNonzeros n A j * (colNonzeros n A j + 1) := by
  have h3 : ∀ (i j : ℕ), 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → A i j ≤ i := round1_h3 n hn A h
  have h1 : ∀ m : ℕ, m < n → (A (m + 1) j) ≤ ((Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)).card + 1 :=
    round2_h1 n A j hj h h3
  have h2 : ∀ m : ℕ, m ≤ n → 2 * (Finset.sum (Finset.range m) (fun i => A (i + 1) j)) ≤
      ((Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)).card * (((Finset.range m).filter (fun i => (A (i + 1) j) ≠ 0)).card + 1) :=
    round2_h2 n A j hj h h3 h1
  have h_main : 2 * (Finset.sum (Finset.range n) (fun i => A (i + 1) j)) ≤
      ((Finset.range n).filter (fun i => (A (i + 1) j) ≠ 0)).card * (((Finset.range n).filter (fun i => (A (i + 1) j) ≠ 0)).card + 1) :=
    h2 n (by linarith)
  simpa [colSum, colNonzeros] using h_main

lemma round1_h_lemma5 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  ∀ (i : ℕ), 1 ≤ i → i ≤ n - 1 → A i 1 = 0 := by
  intro i hi1 hi2
  have h1 : i + 1 ≤ n := by omega
  have h2 : 1 ≤ i := hi1
  have h3 : i ≤ n - 1 := hi2
  have h4 : 1 ≤ (1 : ℕ) := by norm_num
  have h5 : (1 : ℕ) ≤ n := by omega
  have h6 : i + 1 ≤ n := h1
  have h7 := h.1 i 1 h2 (by omega) h4 h5 h6
  exact h7

lemma round1_h_lemma7 (n : ℕ)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (j : ℕ)
  (hj1 : 1 ≤ j)
  (hj2 : j + 1 ≤ n):
  colSum n A (j + 1) ≤ colSum n A j + colNonzeros n A (j + 1) := by
  have h_j_le : j ≤ n - 1 := by omega
  have h_main : ∀ (i : ℕ), i ∈ Finset.range n → A (i + 1) (j + 1) ≤ A (i + 1) j + (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ)) := by
    intro i hi
    have h_i_lt_n : i < n := Finset.mem_range.mp hi
    have h_i1 : 1 ≤ i + 1 := by omega
    have h_i2 : i + 1 ≤ n := by omega
    have h_j1 : 1 ≤ j := hj1
    have h_j2' : j ≤ n - 1 := h_j_le
    have h_cond : A (i + 1) (j + 1) = A (i + 1) j ∨ A (i + 1) (j + 1) = A (i + 1) j + 1 := h.2.2 (i + 1) j h_i1 h_i2 h_j1 h_j2'
    by_cases h4 : A (i + 1) (j + 1) ≠ 0
    ·
      have h5 : (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ)) = 1 := by
        simp [h4]
      rw [h5]
      rcases h_cond with (h_cond1 | h_cond2) <;> linarith
    ·
      have h6 : A (i + 1) (j + 1) = 0 := by simpa using h4
      have h7 : (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ)) = 0 := by
        simp [h4]
      rw [h7]
      simp [h6]
  have h_sum : Finset.sum (Finset.range n) (fun i : ℕ => A (i + 1) (j + 1)) ≤ Finset.sum (Finset.range n) (fun i : ℕ => (A (i + 1) j + (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ)))) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h_main i hi
  have h_sum2 : Finset.sum (Finset.range n) (fun i : ℕ => (A (i + 1) j + (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ)))) =
    (Finset.sum (Finset.range n) (fun i : ℕ => A (i + 1) j)) + Finset.sum (Finset.range n) (fun i : ℕ => (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ))) := by
    rw [Finset.sum_add_distrib]
  rw [h_sum2] at h_sum
  have h_sum3 : Finset.sum (Finset.range n) (fun i : ℕ => (if A (i + 1) (j + 1) ≠ 0 then (1 : ℕ) else (0 : ℕ))) = ((Finset.range n).filter (fun i => A (i + 1) (j + 1) ≠ 0)).card := by
    simp [Finset.sum_ite, Finset.sum_const]
  have h_final : Finset.sum (Finset.range n) (fun i : ℕ => A (i + 1) (j + 1)) ≤ Finset.sum (Finset.range n) (fun i : ℕ => A (i + 1) j) + ((Finset.range n).filter (fun i => A (i + 1) (j + 1) ≠ 0)).card := by
    rw [h_sum3] at h_sum
    exact h_sum
  simpa [colSum, colNonzeros] using h_final

lemma round1_h_lemma8 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  A n 1 ≤ 1 := by
  have h1 : n ≥ 2 := hn
  have h2 : 1 ≤ n - 1 := by omega
  have h3 : n - 1 ≤ n - 1 := by omega
  have h4 : A (n - 1) 1 = 0 := round1_h_lemma5 n hn A h (n - 1) h2 h3
  have h5 : A ((n - 1) + 1) 1 = A (n - 1) 1 ∨ A ((n - 1) + 1) 1 = A (n - 1) 1 + 1 := h.2.1 (n - 1) 1 (by omega) (by omega) (by norm_num) (by omega)
  have h6 : (n - 1) + 1 = n := by omega
  rw [h6] at h5
  rw [h4] at h5
  rcases h5 with (h5 | h5) <;> omega

lemma round1_h_lemma9 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  colSum n A 1 = A n 1 := by
  have h1 : colSum n A 1 = Finset.sum (Finset.range n) (fun i : ℕ => A (i + 1) 1) := by rfl
  rw [h1]
  have h2 : ∀ i ∈ Finset.range n, i ≠ n - 1 → A (i + 1) 1 = 0 := by
    intro i hi hne
    have h3 : i < n := Finset.mem_range.mp hi
    have h4 : i + 1 ≤ n - 1 := by omega
    have h5 : 1 ≤ i + 1 := by omega
    exact round1_h_lemma5 n hn A h (i + 1) (by omega) (by omega)
  have h4 : n - 1 ∈ Finset.range n := by
    simp
    omega
  have h5 : Finset.sum (Finset.range n) (fun i : ℕ => A (i + 1) 1) = A ((n - 1) + 1) 1 := by
    rw [Finset.sum_eq_single_of_mem (n - 1) h4]
    · intro i _ hne
      exact h2 i ‹_› hne
  have h6 : (n - 1) + 1 = n := by omega
  rw [h5, h6]

lemma round1_h_lemma10 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  colSum n A 1 ≤ colNonzeros n A 1 := by
  have h_sum : colSum n A 1 = A n 1 := round1_h_lemma9 n hn A h
  have h_an1 : A n 1 ≤ 1 := round1_h_lemma8 n hn A h
  have h_main : A n 1 ≤ colNonzeros n A 1 := by
    by_cases h_case : A n 1 = 0
    · rw [h_case]
      simp
    · have h_pos : A n 1 ≠ 0 := by
        tauto
      have h6 : n - 1 ∈ (Finset.range n).filter (fun i : ℕ => A (i + 1) 1 ≠ 0) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · omega
        · have h8 : (n - 1) + 1 = n := by omega
          rw [h8]
          exact h_pos
      have h7 : 1 ≤ ((Finset.range n).filter (fun i : ℕ => A (i + 1) 1 ≠ 0)).card := by
        apply Finset.one_le_card.mpr
        exact ⟨n - 1, h6⟩
      have h9 : A n 1 ≤ 1 := h_an1
      have h10 : 1 ≤ ((Finset.range n).filter (fun i : ℕ => A (i + 1) 1 ≠ 0)).card := h7
      have h11 : A n 1 ≤ ((Finset.range n).filter (fun i : ℕ => A (i + 1) 1 ≠ 0)).card := by
        calc
          A n 1 ≤ 1 := h9
          _ ≤ ((Finset.range n).filter (fun i : ℕ => A (i + 1) 1 ≠ 0)).card := h10
      exact h11
  rw [h_sum]
  exact h_main

lemma lemma2 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ n):
  colSum n A j ≤ Finset.sum (Finset.range j) (fun t => colNonzeros n A (t + 1)) := by
  induction j with
  | zero =>
    exfalso
    linarith
  | succ j ih =>
    have h1 : 1 ≤ j + 1 := by linarith
    have h2 : j + 1 ≤ n := hj.2
    by_cases h_j0 : j = 0
    ·
      subst h_j0
      simpa [Finset.sum_range_succ] using round1_h_lemma10 n hn A h
    ·
      have h_j_pos : 1 ≤ j := by omega
      have h_j_le_n : j ≤ n := by omega
      have h_ih' : colSum n A j ≤ Finset.sum (Finset.range j) (fun t => colNonzeros n A (t + 1)) := ih ⟨h_j_pos, h_j_le_n⟩
      have h_step : colSum n A (j + 1) ≤ colSum n A j + colNonzeros n A (j + 1) := round1_h_lemma7 n A h j h_j_pos h2
      have h_goal : colSum n A (j + 1) ≤ Finset.sum (Finset.range (j + 1)) (fun t => colNonzeros n A (t + 1)) := by
        rw [Finset.sum_range_succ]
        linarith
      simpa using h_goal

lemma round1_h_lemma3 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ n):
  colNonzeros n A j ≤ j := by
  have h1 : ∀ i ∈ (Finset.range n).filter (fun i => A (i + 1) j ≠ 0), i ≥ n - j := by
    intro i hi
    have h2 : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
    have h3 : A (i + 1) j ≠ 0 := (Finset.mem_filter.mp hi).2
    have h4 : i < n := Finset.mem_range.mp h2
    have h5 : 1 ≤ i + 1 := by omega
    have h6 : i + 1 ≤ n := by omega
    have h7 : 1 ≤ j := hj.1
    have h8 : j ≤ n := hj.2
    by_contra h9
    have h10 : i < n - j := by omega
    have h11 : i + 1 + j ≤ n := by omega
    have h12 : A (i + 1) j = 0 := h.1 (i + 1) j h5 h6 h7 h8 h11
    contradiction
  have h_subset : (Finset.range n).filter (fun i => A (i + 1) j ≠ 0) ⊆ Finset.Ico (n - j) n := by
    intro i hi
    have h13 : i ≥ n - j := h1 i hi
    have h14 : i < n := Finset.mem_range.mp ( (Finset.mem_filter.mp hi).1 )
    exact Finset.mem_Ico.mpr ⟨h13, h14⟩
  have h_card : ((Finset.range n).filter (fun i => A (i + 1) j ≠ 0)).card ≤ (Finset.Ico (n - j) n).card := by
    apply Finset.card_le_card h_subset
  have h_card2 : (Finset.Ico (n - j) n).card = j := by
    simp
    omega
  rw [h_card2] at h_card
  simpa [colNonzeros] using h_card

lemma lemma3 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A)
  (j : ℕ)
  (hj : 1 ≤ j ∧ j ≤ n):
  colNonzeros n A j ≤ j := by
  exact round1_h_lemma3 n hn A h j hj

lemma round1_h_sum1 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  2 * totalSum n A ≤ Finset.sum (Finset.range n) (fun j => colNonzeros n A (j + 1) * (colNonzeros n A (j + 1) + 1)) := by
  have h₁ : ∀ j ∈ Finset.range n, 2 * colSum n A (j + 1) ≤ colNonzeros n A (j + 1) * (colNonzeros n A (j + 1) + 1) := by
    intro j hj
    have h₂ : 1 ≤ (j + 1) ∧ (j + 1) ≤ n := by
      simp [Finset.mem_range] at hj ⊢ ; omega
    exact lemma1 n hn A h (j + 1) h₂
  have h₃ : 2 * totalSum n A = Finset.sum (Finset.range n) (fun j => 2 * colSum n A (j + 1)) := by
    simp [totalSum, colSum, Finset.mul_sum]
  rw [h₃]
  apply Finset.sum_le_sum
  intro i _
  exact h₁ i ‹_›

lemma round1_h_sum_identity (n : ℕ)
  (k : ℕ → ℕ):
  Finset.sum (Finset.range n) (fun j : ℕ => Finset.sum (Finset.range (j + 1)) (fun t : ℕ => k (t + 1))) =
  Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k (t + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ : Finset.sum (Finset.range (n + 1)) (fun j : ℕ => Finset.sum (Finset.range (j + 1)) (fun t : ℕ => k (t + 1))) =
        (Finset.sum (Finset.range n) (fun j : ℕ => Finset.sum (Finset.range (j + 1)) (fun t : ℕ => k (t + 1)))) +
        (Finset.sum (Finset.range (n + 1)) (fun t : ℕ => k (t + 1))) := by
      rw [Finset.sum_range_succ]
    rw [h₁]
    have h₂₁ : Finset.sum (Finset.range (n + 1)) (fun t : ℕ => (n + 1 - t) * k (t + 1)) =
        Finset.sum (Finset.range n) (fun t : ℕ => (n + 1 - t) * k (t + 1)) + (n + 1 - n) * k (n + 1) := by
      rw [Finset.sum_range_succ]
    have h₂₂ : Finset.sum (Finset.range n) (fun t : ℕ => (n + 1 - t) * k (t + 1)) =
        Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k (t + 1)) + Finset.sum (Finset.range n) (fun t : ℕ => k (t + 1)) := by
      have h₃ : ∀ t ∈ Finset.range n, (n + 1 - t) * k (t + 1) = (n - t) * k (t + 1) + k (t + 1) := by
        intro t ht
        have h₄ : t < n := Finset.mem_range.mp ht
        have h₅ : n + 1 - t = (n - t) + 1 := by omega
        rw [h₅]
        ring
      calc
        Finset.sum (Finset.range n) (fun t : ℕ => (n + 1 - t) * k (t + 1))
          = Finset.sum (Finset.range n) (fun t : ℕ => ((n - t) * k (t + 1) + k (t + 1))) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact h₃ t ht
        _ = Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k (t + 1)) + Finset.sum (Finset.range n) (fun t : ℕ => k (t + 1)) := by
            rw [Finset.sum_add_distrib]
    have h₂ : Finset.sum (Finset.range (n + 1)) (fun t : ℕ => (n + 1 - t) * k (t + 1)) =
        (Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k (t + 1))) + Finset.sum (Finset.range (n + 1)) (fun t : ℕ => k (t + 1)) := by
      rw [h₂₁, h₂₂]
      simp [Finset.sum_range_succ]
      ring
    have h_main : Finset.sum (Finset.range (n + 1)) (fun t : ℕ => (n + 1 - t) * k (t + 1)) =
        (Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k (t + 1))) + Finset.sum (Finset.range (n + 1)) (fun t : ℕ => k (t + 1)) := h₂
    simpa [ih] using by
      rw [h_main]

lemma round1_h_sum2 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  totalSum n A ≤ Finset.sum (Finset.range n) (fun j => (n - (j + 1) + 1) * colNonzeros n A (j + 1)) := by
  have h₁ : ∀ j ∈ Finset.range n, colSum n A (j + 1) ≤ Finset.sum (Finset.range (j + 1)) (fun t => colNonzeros n A (t + 1)) := by
    intro j hj
    have h₂ : 1 ≤ (j + 1) ∧ (j + 1) ≤ n := by
      simp [Finset.mem_range] at hj ⊢ ; omega
    exact lemma2 n hn A h (j + 1) h₂
  have h₃ : totalSum n A = Finset.sum (Finset.range n) (fun j => colSum n A (j + 1)) := by
    simp [totalSum, colSum]
  have h₄ : Finset.sum (Finset.range n) (fun j => colSum n A (j + 1)) ≤ Finset.sum (Finset.range n) (fun j => Finset.sum (Finset.range (j + 1)) (fun t => colNonzeros n A (t + 1))) := by
    apply Finset.sum_le_sum
    intro i _
    exact h₁ i ‹_›
  let k' := fun (s : ℕ) => colNonzeros n A s
  have h₅ : Finset.sum (Finset.range n) (fun j : ℕ => Finset.sum (Finset.range (j + 1)) (fun t : ℕ => k' (t + 1)))
    = Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k' (t + 1)) := round1_h_sum_identity n k'
  have h₆ : Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k' (t + 1))
    = Finset.sum (Finset.range n) (fun j : ℕ => (n - (j + 1) + 1) * colNonzeros n A (j + 1)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h₇ : x < n := Finset.mem_range.mp hx
    have h₈ : x + 1 ≤ n := by omega
    have h₉ : n - x = (n - (x + 1)) + 1 := by omega
    have h₁₀ : (n - x) * k' (x + 1) = (n - (x + 1) + 1) * k' (x + 1) := by
      rw [h₉]
    simpa [k'] using h₁₀
  have h_main : Finset.sum (Finset.range n) (fun j => colSum n A (j + 1)) ≤ Finset.sum (Finset.range n) (fun j => (n - (j + 1) + 1) * colNonzeros n A (j + 1)) := by
    calc
      Finset.sum (Finset.range n) (fun j => colSum n A (j + 1))
        ≤ Finset.sum (Finset.range n) (fun j : ℕ => Finset.sum (Finset.range (j + 1)) (fun t : ℕ => k' (t + 1))) := h₄
      _ = Finset.sum (Finset.range n) (fun t : ℕ => (n - t) * k' (t + 1)) := h₅
      _ = Finset.sum (Finset.range n) (fun j : ℕ => (n - (j + 1) + 1) * colNonzeros n A (j + 1)) := h₆
  rw [h₃]
  exact h_main

theorem putnam_2025_b4 (n : ℕ)
  (hn : 2 ≤ n)
  (A : ℕ → ℕ → ℕ)
  (h : MatrixProp n A):
  3 * totalSum n A ≤ (n + 2) * nonzeroCount n A := by
    have h_sum1 := round1_h_sum1 n hn A h
    have h_sum2 := round1_h_sum2 n hn A h
    let k : ℕ → ℕ := fun j => colNonzeros n A (j + 1)
    have h₃ : ∀ j ∈ Finset.range n, k j ≤ j + 1 := by
      intro j hj
      have h₄ : 1 ≤ (j + 1) ∧ (j + 1) ≤ n := by
        simp [Finset.mem_range] at hj ⊢ ; omega
      exact lemma3 n hn A h (j + 1) h₄
    have h₄ : 3 * totalSum n A ≤ Finset.sum (Finset.range n) (fun j => k j * (k j + 1)) + Finset.sum (Finset.range n) (fun j => (n - (j + 1) + 1) * k j) := by
      linarith
    have h₅ : Finset.sum (Finset.range n) (fun j => k j * (k j + 1)) + Finset.sum (Finset.range n) (fun j => (n - (j + 1) + 1) * k j) = Finset.sum (Finset.range n) (fun j => k j * (k j + 1 + (n - (j + 1) + 1))) := by
      rw [←Finset.sum_add_distrib]
      congr
      funext j
      ring
    have h₆ : ∀ j ∈ Finset.range n, k j * (k j + 1 + (n - (j + 1) + 1)) ≤ k j * (n + 2) := by
      intro j hj
      have h₇ : j < n := Finset.mem_range.mp hj
      have h₈ : k j ≤ j + 1 := h₃ j hj
      have h₉ : k j + 1 + (n - (j + 1) + 1) ≤ n + 2 := by omega
      exact mul_le_mul_of_nonneg_left h₉ (by positivity)
    have h₇ : Finset.sum (Finset.range n) (fun j => k j * (k j + 1 + (n - (j + 1) + 1))) ≤ Finset.sum (Finset.range n) (fun j => k j * (n + 2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact h₆ i ‹_›
    have h₈ : Finset.sum (Finset.range n) (fun j => k j * (n + 2)) = (n + 2) * Finset.sum (Finset.range n) (fun j => k j) := by
      have h₉ : ∀ j ∈ Finset.range n, k j * (n + 2) = (n + 2) * k j := by
        intro j _
        ring
      calc
        Finset.sum (Finset.range n) (fun j => k j * (n + 2))
          = Finset.sum (Finset.range n) (fun j => (n + 2) * k j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact h₉ j ‹_›
        _ = (n + 2) * Finset.sum (Finset.range n) (fun j => k j) := by
            rw [Finset.mul_sum]
    have h₁₀ : Finset.sum (Finset.range n) (fun j => k j) = nonzeroCount n A := by
      simp [nonzeroCount, colNonzeros]
      rfl
    rw [h₅] at h₄
    rw [h₈, h₁₀] at h₇
    linarith

end Putnam2025B4
