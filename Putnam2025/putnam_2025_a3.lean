import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Bound
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Classical Finset

namespace Putnam2025A3

abbrev State (n : ℕ) : Type := (Fin n → Fin 3) × Finset (Fin n → Fin 3)

abbrev State.validNext {n : ℕ} (s : State n) : Finset (State n) :=
  {s' |
    s'.1 ∈ s.2 ∧
    (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), s'.1 i = s.1 i + δ.val ∧ ∀ j ≠ i, s'.1 j = s.1 j) ∧
    s'.2 = s.2.erase s'.1}

abbrev State.init (n : ℕ) : State n := ⟨fun _ ↦ 0, Finset.univ.erase (fun _ ↦ 0)⟩

abbrev Strategy (n : ℕ) : Type := State n → State n

abbrev IsRollout {n : ℕ} (a b : Strategy n) (s : ℕ → State n) : Prop :=
  s 0 = State.init n ∧
  (∀ i, Even i → s (i + 1) = a (s i)) ∧
  (∀ i, Odd i → s (i + 1) = b (s i))

lemma round1_h3 (n : ℕ):
  ∀ (i : Fin n) (x : Fin n → Fin 3),
    let apply_op_at (i : Fin n) (x : Fin n → Fin 3) :=
        let xi := x i
        if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
        else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
        else x
    (apply_op_at i (apply_op_at i x) = x) := by
  intros i x
  let apply_op_at (i : Fin n) (x : Fin n → Fin 3) :=
    let xi := x i
    if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
    else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
    else x
  dsimp only
  let xi := x i
  have h_main : xi = (0 : Fin 3) ∨ xi = (1 : Fin 3) ∨ xi = (2 : Fin 3) := by
    have h : xi.val = 0 ∨ xi.val = 1 ∨ xi.val = 2 := by omega
    rcases h with (h | h | h) <;> simp [Fin.ext_iff, h]
  rcases h_main with (h0 | h1 | h2)
  ·
    have h : (apply_op_at i (apply_op_at i x)) = x := by
      have h1 : apply_op_at i x = x := by
        simp [apply_op_at]
        aesop
      rw [h1]
      simp [apply_op_at] ; aesop
    exact h
  ·
    have h : (apply_op_at i (apply_op_at i x)) = x := by
      have hxi1 : xi = (1 : Fin 3) := h1
      let y := apply_op_at i x
      have hy_def : y = Function.update x i (xi + 1) := by
        simp [apply_op_at, hxi1] ; aesop
      have hyi : y i = (2 : Fin 3) := by
        rw [hy_def]
        simp [hxi1]
      have h2 : (apply_op_at i y) = x := by
        simp [apply_op_at, hy_def] ; aesop
      simpa [y] using h2
    exact h
  ·
    have h : (apply_op_at i (apply_op_at i x)) = x := by
      have hxi2 : xi = (2 : Fin 3) := h2
      let y := apply_op_at i x
      have hy_def : y = Function.update x i (xi - 1) := by
        simp [apply_op_at, hxi2] ; aesop
      have hyi : y i = (1 : Fin 3) := by
        rw [hy_def]
        simp [hxi2]
      have h2 : (apply_op_at i y) = x := by
        simp [apply_op_at, hy_def] ; aesop
      simpa [y] using h2
    exact h

lemma round1_h_main3' (n : ℕ)
  (apply_op_at : (Fin n) → (Fin n → Fin 3) → (Fin n → Fin 3))
  (h2 : ∀ (a : Fin 3), a ≠ (0 : Fin 3) → (a = (1 : Fin 3) ∨ a = (2 : Fin 3)))
  (h_def : ∀ (i : Fin n) (x : Fin n → Fin 3),
    apply_op_at i x =
      let xi := x i
      if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
      else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
      else x):
  ∀ (i : Fin n) (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → x i ≠ (0 : Fin 3) →
     ∃ (δ : ({1, -1} : Finset ℤ)), (apply_op_at i x) i = x i + δ.val ∧ ∀ (j : Fin n), j ≠ i → (apply_op_at i x) j = x j := by
  intro i x hx hxi
  have h5 : x i = (1 : Fin 3) ∨ x i = (2 : Fin 3) := h2 (x i) hxi
  have h_def' : apply_op_at i x =
      (let xi := x i
      if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
      else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
      else x) := h_def i x
  rcases h5 with (h5 | h5)
  ·
    refine ⟨⟨1, by decide⟩, ?_⟩
    have h6 : (apply_op_at i x) i = x i + (1 : ℤ) := by
      rw [h_def']
      simp [h5]
    have h7 : ∀ (j : Fin n), j ≠ i → (apply_op_at i x) j = x j := by
      intro j hj
      rw [h_def']
      simp [h5, hj]
    exact ⟨h6, h7⟩
  ·
    refine ⟨⟨-1, by decide⟩, ?_⟩
    have h6 : (apply_op_at i x) i = x i + (-1 : ℤ) := by
      rw [h_def']
      simp [h5]
    have h7 : ∀ (j : Fin n), j ≠ i → (apply_op_at i x) j = x j := by
      intro j hj
      rw [h_def']
      simp [h5, hj]
    exact ⟨h6, h7⟩

lemma round2_h4 (n : ℕ)
  (apply_op_at : (Fin n) → (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_def : ∀ (i : Fin n) (x : Fin n → Fin 3),
    apply_op_at i x =
      (let xi := x i
      if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
      else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
      else x))
  (h2 : ∀ (a : Fin 3), a ≠ (0 : Fin 3) → (a = (1 : Fin 3) ∨ a = (2 : Fin 3))):
  ∀ (i : Fin n) (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → x i ≠ (0 : Fin 3) →
    apply_op_at i x ≠ (fun (_ : Fin n) => (0 : Fin 3)) := by
  intro i x hx hxi
  have h5 : x i ≠ (0 : Fin 3) := hxi
  have h6 : x i = (1 : Fin 3) ∨ x i = (2 : Fin 3) := h2 (x i) h5
  intro h_contra
  have h7 : (apply_op_at i x) i = (0 : Fin 3) := by
    have h8 : apply_op_at i x = (fun (_ : Fin n) => (0 : Fin 3)) := h_contra
    rw [h8]
  rcases h6 with (h6 | h6)
  ·
    have h9 : (apply_op_at i x) i = (x i + 1) := by
      rw [h_def i x]
      simp [h6]
    rw [h9] at h7
    simp [h6] at h7
  ·
    have h9 : (apply_op_at i x) i = (x i - 1) := by
      rw [h_def i x]
      simp [h6]
    rw [h9] at h7
    simp [h6] at h7

lemma round2_h9 (n : ℕ)
  (hn : 1 ≤ n)
  (apply_op_at : (Fin n) → (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_def : ∀ (i : Fin n) (x : Fin n → Fin 3),
    apply_op_at i x =
      (let xi := x i
      if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
      else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
      else x))
  (hS_nonempty : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
    (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).Nonempty):
  ∀ (x : Fin n → Fin 3) (hx : x ≠ (fun (_ : Fin n) => (0 : Fin 3)))
    (i : Fin n)
    (hi : i = (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x hx))
    (y : Fin n → Fin 3) (hy_eq : y = apply_op_at i x),
    ∀ (j : Fin n), j ∈ (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ) → i ≤ j := by
  intro x hx i hi y hy_eq j hj
  let Sx := Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ
  let Sy := Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ
  have hSx_nonempty : Sx.Nonempty := hS_nonempty x hx
  have h11 : j ∈ Sy := hj
  have h12 : y j ≠ (0 : Fin 3) := (Finset.mem_filter.mp h11).2
  by_cases h14 : j < i
  ·
    have h15 : j ≠ i := by
      intro h16
      rw [h16] at h14
      exact lt_irrefl i h14
    have h17 : y j = x j := by
      rw [hy_eq, h_def i x] ; simp ; aesop
    have h18 : x j ≠ (0 : Fin 3) := by
      rw [←h17] ; exact h12
    have h19 : j ∈ Finset.univ := by simp
    have h20 : j ∈ Sx := by
      exact Finset.mem_filter.mpr ⟨h19, h18⟩
    have h21 : i ≤ j := by
      rw [hi]
      exact Finset.min'_le Sx j h20
    exact False.elim (not_le.mpr h14 h21)
  ·
    exact le_of_not_gt h14

lemma round2_h20 (n : ℕ)
  (apply_op_at : (Fin n) → (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_def : ∀ (i : Fin n) (x : Fin n → Fin 3),
    apply_op_at i x =
      (let xi := x i
      if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
      else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
      else x))
  (h2 : ∀ (a : Fin 3), a ≠ (0 : Fin 3) → (a = (1 : Fin 3) ∨ a = (2 : Fin 3)))
  (i : Fin n)
  (x : Fin n → Fin 3)
  (hx : x i ≠ (0 : Fin 3)):
  (apply_op_at i x) i ≠ (0 : Fin 3) := by
  have h3 : x i = (1 : Fin 3) ∨ x i = (2 : Fin 3) := h2 (x i) hx
  rcases h3 with (h3 | h3)
  ·
    have h4 : (apply_op_at i x) i = (x i + 1) := by
      rw [h_def i x] ; simp [h3]
    rw [h4, h3] ; decide
  ·
    have h4 : (apply_op_at i x) i = (x i - 1) := by
      rw [h_def i x] ; simp [h3]
    rw [h4, h3] ; decide

theorem round1_h_f (n : ℕ)
  (hn : 1 ≤ n):
  ∃ (f : (Fin n → Fin 3) → (Fin n → Fin 3)),
    (∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x) ∧
    (∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ (fun (_ : Fin n) => (0 : Fin 3))) ∧
    (∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
      ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j) := by
  have h1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → ∃ (i : Fin n), x i ≠ (0 : Fin 3) := by
    intro x hx
    by_contra h
    push_neg at h
    have h4 : ∀ (i : Fin n), x i = 0 := by simpa using h
    have h5 : x = (fun (_ : Fin n) => (0 : Fin 3)) := by
      funext i
      exact h4 i
    exact hx h5
  have h2 : ∀ (a : Fin 3), a ≠ (0 : Fin 3) → (a = (1 : Fin 3) ∨ a = (2 : Fin 3)) := by
    intro a ha
    fin_cases a <;> simp_all (config := {decide := true})
  let apply_op_at (i : Fin n) (x : Fin n → Fin 3) : (Fin n → Fin 3) :=
    let xi := x i
    if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
    else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
    else x
  have h_def : ∀ (i : Fin n) (x : Fin n → Fin 3),
    apply_op_at i x =
      (let xi := x i
      if hxi1 : xi = (1 : Fin 3) then Function.update x i (xi + 1)
      else if hxi2 : xi = (2 : Fin 3) then Function.update x i (xi - 1)
      else x) := by
    intro i x
    rfl
  have h3 : ∀ (i : Fin n) (x : Fin n → Fin 3), (apply_op_at i (apply_op_at i x) = x) := by
    exact round1_h3 n
  have h4 : ∀ (i : Fin n) (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → x i ≠ (0 : Fin 3) →
    apply_op_at i x ≠ (fun (_ : Fin n) => (0 : Fin 3)) := by
    exact round2_h4 n apply_op_at h_def h2
  have h_main3' := round1_h_main3' n apply_op_at h2 h_def
  have hS_nonempty : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
    (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).Nonempty := by
    intro x hx
    have h5 : ∃ (i : Fin n), x i ≠ (0 : Fin 3) := h1 x hx
    rcases h5 with ⟨i, hi⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let I (x : Fin n → Fin 3) : Fin n := if h : x = (fun (_ : Fin n) => (0 : Fin 3)) then i₀ else (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x h)
  have hI_spec : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → x (I x) ≠ (0 : Fin 3) := by
    intro x hx
    have h5 : I x = (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x hx) := by
      simp [I, hx]
    rw [h5]
    have h6 : ((Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x hx)) ∈ (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ) :=
      Finset.min'_mem (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ) (hS_nonempty x hx)
    have h7 : x (((Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x hx))) ≠ (0 : Fin 3) := by
      have h8 : ((Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x hx)) ∈ (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ) := h6
      have h9 := (Finset.mem_filter.mp h8).2
      exact h9
    exact h7
  let f : (Fin n → Fin 3) → (Fin n → Fin 3) := fun x => if h : x = (fun (_ : Fin n) => (0 : Fin 3)) then x else apply_op_at (I x) x
  have h_main2 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ (fun (_ : Fin n) => (0 : Fin 3)) := by
    intro x hx
    have h6 : ¬ (x = (fun (_ : Fin n) => (0 : Fin 3))) := hx
    have h5 : f x = apply_op_at (I x) x := by
      unfold f
      split_ifs ; tauto
    rw [h5]
    have h7 : x (I x) ≠ (0 : Fin 3) := hI_spec x hx
    exact h4 (I x) x hx h7
  have h_main3 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
      ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j := by
    intro x hx
    have h6 : ¬ (x = (fun (_ : Fin n) => (0 : Fin 3))) := hx
    have h5 : f x = apply_op_at (I x) x := by
      unfold f
      split_ifs ; tauto
    have h_i : x (I x) ≠ (0 : Fin 3) := hI_spec x hx
    have h7 : ∃ (δ : ({1, -1} : Finset ℤ)), (apply_op_at (I x) x) (I x) = x (I x) + δ.val ∧ ∀ (j : Fin n), j ≠ I x → (apply_op_at (I x) x) j = x j :=
      h_main3' (I x) x hx h_i
    rcases h7 with ⟨δ, h71, h72⟩
    refine ⟨I x, δ, ?_⟩
    rw [h5]
    exact ⟨h71, fun j hj => h72 j hj⟩
  have h_main1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x := by
    intro x hx
    let i := I x
    have hi : x i ≠ (0 : Fin 3) := hI_spec x hx
    let y := f x
    have hy_def : y = f x := by rfl
    have h6 : ¬ (x = (fun (_ : Fin n) => (0 : Fin 3))) := hx
    have hy_eq : y = apply_op_at i x := by
      rw [hy_def]
      unfold f
      split_ifs ; tauto
    have h_pos_y : y ≠ (fun (_ : Fin n) => (0 : Fin 3)) := h_main2 x hx
    have h_pos_y' : (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ).Nonempty := hS_nonempty y h_pos_y
    have h_i_def : i = (Finset.filter (fun (j : Fin n) => x j ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty x h6) := by
      simp [I] ; aesop
    have h20 : (apply_op_at i x) i ≠ (0 : Fin 3) := round2_h20 n apply_op_at h_def h2 i x hi
    have h21 : y i ≠ (0 : Fin 3) := by
      have h22 : y = apply_op_at i x := hy_eq
      rw [h22] at *
      exact h20
    have h9 : i ∈ (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h21⟩
    let min_y := (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ).min' h_pos_y'
    have h8 : ∀ (j : Fin n), j ∈ (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ) → i ≤ j :=
      round2_h9 n hn apply_op_at h_def hS_nonempty x h6 i h_i_def y hy_eq
    have h10 : min_y ≤ i := Finset.min'_le (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ) i h9
    have h11 : i ≤ min_y := by
      exact h8 min_y (Finset.min'_mem (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ) h_pos_y')
    have h12 : i = min_y := by exact le_antisymm h11 h10
    have hI_y : I y = i := by
      have h13 : ¬ (y = (fun (_ : Fin n) => (0 : Fin 3))) := h_pos_y
      have h14 : I y = (Finset.filter (fun (k : Fin n) => y k ≠ (0 : Fin 3)) Finset.univ).min' (hS_nonempty y h13) := by
        unfold I
        split_ifs ; tauto
      rw [h14]
      exact h12.symm
    have h15 : f y = apply_op_at i y := by
      have h16 : ¬ (y = (fun (_ : Fin n) => (0 : Fin 3))) := h_pos_y
      have h17 : I y = i := hI_y
      unfold f
      split_ifs ; tauto
    have h18 : f (f x) = f y := by rfl
    rw [h18, h15]
    have h19 : apply_op_at i y = apply_op_at i (apply_op_at i x) := by
      rw [hy_eq]
    rw [h19]
    exact h3 i x
  exact ⟨f, h_main1, h_main2, h_main3⟩

lemma round1_h_main (n : ℕ)
  (a : Strategy n)
  (b : Strategy n)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (h : ∀ (m : ℕ), s (m + 1) ∈ State.validNext (s m)):
  False := by
  have h_dec : ∀ (m : ℕ), (s m).2.card = (s 0).2.card - m := by
    intro m
    induction m with
    | zero =>
      rfl
    | succ m ih =>
      have h1 : s (m + 1) ∈ State.validNext (s m) := h m
      have h_prop1 : (s (m + 1)).1 ∈ (s m).2 ∧
                      (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), (s (m + 1)).1 i = (s m).1 i + δ.val ∧ ∀ (j : Fin n), j ≠ i → (s (m + 1)).1 j = (s m).1 j) ∧
                      (s (m + 1)).2 = (s m).2.erase (s (m + 1)).1 := by
        have h2 : s (m + 1) ∈ (State.validNext (s m)) := h1
        have h3 : s (m + 1) ∈ ({s' : State n | s'.1 ∈ (s m).2 ∧ (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), s'.1 i = (s m).1 i + δ.val ∧ ∀ (j : Fin n), j ≠ i → s'.1 j = (s m).1 j) ∧ s'.2 = (s m).2.erase s'.1} : Set (State n)) := by
          simpa [State.validNext] using h2
        simpa [Set.mem_setOf_eq] using h3
      rcases h_prop1 with ⟨hA, _, hB⟩
      have h4 : (s (m + 1)).2.card = (s m).2.card - 1 := by
        rw [hB]
        rw [Finset.card_erase_of_mem hA]
      rw [h4, ih] ; omega
  have h5 : ∃ m : ℕ, (s m).2.card = 0 := by
    refine ⟨(s 0).2.card, by
      have h6 := h_dec (s 0).2.card
      rw [Nat.sub_self] at h6
      exact h6⟩
  rcases h5 with ⟨m, hm⟩
  have h6 : (s m).2 = ∅ := by
    exact Finset.card_eq_zero.mp hm
  have h7 : s (m + 1) ∈ State.validNext (s m) := h m
  have h_prop2 : (s (m + 1)).1 ∈ (s m).2 ∧
                    (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), (s (m + 1)).1 i = (s m).1 i + δ.val ∧ ∀ (j : Fin n), j ≠ i → (s (m + 1)).1 j = (s m).1 j) ∧
                    (s (m + 1)).2 = (s m).2.erase (s (m + 1)).1 := by
    have h8 : s (m + 1) ∈ (State.validNext (s m)) := h7
    have h9 : s (m + 1) ∈ ({s' : State n | s'.1 ∈ (s m).2 ∧ (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), s'.1 i = (s m).1 i + δ.val ∧ ∀ (j : Fin n), j ≠ i → s'.1 j = (s m).1 j) ∧ s'.2 = (s m).2.erase s'.1} : Set (State n)) := by
      simpa [State.validNext] using h8
    simpa [Set.mem_setOf_eq] using h9
  rcases h_prop2 with ⟨h10, _, _⟩
  have h11 : (s (m + 1)).1 ∈ (s m).2 := h10
  have h12 : (s (m + 1)).1 ∈ (∅ : Finset (Fin n → Fin 3)) := by
    have h13 : (s m).2 = (∅ : Finset (Fin n → Fin 3)) := h6
    rw [h13] at h11
    simp at h11
  simp at h12

theorem round1_h_k0_exists_min (n : ℕ)
  (hn : 1 ≤ n):
  ∀ (a : Strategy n) (b : Strategy n) (s : ℕ → State n)
    (hrollout : IsRollout a b s),
    ∃ k₀ : ℕ, (s (k₀ + 1) ∉ State.validNext (s k₀)) ∧ (∀ m < k₀, s (m + 1) ∈ State.validNext (s m)) := by
  intro a b s hrollout
  have h₁ : ∃ (m : ℕ), s (m + 1) ∉ State.validNext (s m) := by
    by_contra h
    push_neg at h
    exact round1_h_main n a b s hrollout h
  classical
  let K : Set ℕ := {m | s (m + 1) ∉ State.validNext (s m)}
  have hK_nonempty : Set.Nonempty K := by
    rcases h₁ with ⟨m, hm⟩
    refine ⟨m, hm⟩
  let k₀ : ℕ := Nat.find hK_nonempty
  have hk₀₁ : s (k₀ + 1) ∉ State.validNext (s k₀) := Nat.find_spec hK_nonempty
  have hk₀₂ : ∀ (m : ℕ), m < k₀ → s (m + 1) ∈ State.validNext (s m) := by
    intro m hm
    have h₃ : m ∉ K := Nat.find_min hK_nonempty hm
    have h₄ : ¬ (s (m + 1) ∉ State.validNext (s m)) := by
      simpa [K] using h₃
    tauto
  exact ⟨k₀, hk₀₁, hk₀₂⟩

lemma round1_h_main_aux1 (n : ℕ)
  (hn : 1 ≤ n)
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (t : ℕ)
  (x : Fin n → Fin 3):
  ( (∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) ∧ x ≠ (s (t + 1)).1 ) ↔
  ( ∀ r : ℕ, 1 ≤ r → r ≤ t + 1 → x ≠ (s r).1 ) := by
  constructor
  ·
    rintro ⟨h1, h2⟩
    intro r hr1 hr2
    have h4 : r ≤ t + 1 := hr2
    by_cases h5 : r ≤ t
    ·
      exact h1 r hr1 h5
    ·
      have h6 : r = t + 1 := by omega
      rw [h6]
      exact h2
  ·
    intro h
    constructor
    ·
      intro r hr1 hr2
      have h4 : 1 ≤ r := hr1
      have h5 : r ≤ t := hr2
      have h6 : r ≤ t + 1 := by linarith
      exact h r h4 h6
    ·
      have h4 : 1 ≤ t + 1 := by omega
      have h5 : t + 1 ≤ t + 1 := by linarith
      have h6 := h (t + 1) h4 h5
      exact h6

lemma round1_h_main_00b527 (n : ℕ)
  (hn : 1 ≤ n)
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (k₀ : ℕ)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m)):
  ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3),
    x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) := by
  intro t
  induction t with
  | zero =>
    intro h_t
    intro x
    have h1 : (s 0).2 = (Finset.univ : Finset (Fin n → Fin 3)).erase (fun (_ : Fin n) => (0 : Fin 3)) := by
      have hrollout1 : s 0 = State.init n := hrollout.1
      rw [hrollout1]
    rw [h1]
    simp only [Finset.mem_erase, Finset.mem_univ]
    simp
    {
      have h_goal : (x ≠ (fun (_ : Fin n) => (0 : Fin 3))) ↔
                    (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ (r : ℕ), 1 ≤ r → r ≤ 0 → x ≠ (s r).1) := by
        constructor
        · intro h
          exact ⟨h, by
            intro r hr1 hr2
            exfalso
            linarith⟩
        · rintro ⟨h, _⟩
          exact h
      simpa using h_goal
    }
  | succ t ih =>
    intro h_t
    intro x
    have h_lt : t < k₀ := by linarith
    have hvalid : s (t + 1) ∈ State.validNext (s t) := h2 t h_lt
    have h3 : (s (t + 1)).2 = (s t).2.erase (s (t + 1)).1 := by
      have h4 : s (t + 1) ∈ State.validNext (s t) := hvalid
      have h5 : ∀ (s' : State n), s' ∈ State.validNext (s t) → s'.2 = (s t).2.erase s'.1 := by
        intro s' hs'
        have h_prop : s'.1 ∈ (s t).2 ∧ (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), s'.1 i = (s t).1 i + δ.val ∧ ∀ j ≠ i, s'.1 j = (s t).1 j) ∧ s'.2 = (s t).2.erase s'.1 := by
          simpa [State.validNext] using hs'
        tauto
      exact h5 (s (t + 1)) h4
    have h_iht : ∀ (x : Fin n → Fin 3), x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) := ih (by linarith)
    have h4 : x ∈ (s (t + 1)).2 ↔ x ∈ (s t).2 ∧ x ≠ (s (t + 1)).1 := by
      rw [h3]
      simp [Finset.mem_erase]
      apply And.comm
    rw [h4]
    have h6 : x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) := h_iht x
    rw [h6]
    set P := (x ≠ (fun (_ : Fin n) => (0 : Fin 3))) with hP
    set Q := (∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) with hQ
    set R := (x ≠ (s (t + 1)).1) with hR
    have h7 : (Q ∧ R) ↔ (∀ r : ℕ, 1 ≤ r → r ≤ t + 1 → x ≠ (s r).1) := round1_h_main_aux1 n hn b a s t x
    simp only [hP, hQ, hR]
    tauto

theorem round1_h_lemma1_strong (n : ℕ)
  (hn : 1 ≤ n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (k₀ : ℕ)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m)):
  ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3),
    x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) := by
  exact round1_h_main_00b527 n hn b a s hrollout k₀ h2

theorem round1_h_f_x_neq_x (n : ℕ)
  (hn : 1 ≤ n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_f1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x)
  (h_f2 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ (fun (_ : Fin n) => (0 : Fin 3)))
  (h_f3 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
    ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j):
  ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ x := by
  intro x hx
  by_contra h_contra
  have h_main : ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ (j : Fin n), j ≠ i → f x j = x j := h_f3 x hx
  rcases h_main with ⟨i, δ, h₁, h₂⟩
  have h₃ : f x i = x i := by
    rw [h_contra]
  have h₄ : (f x i : ℤ) = (x i : ℤ) + δ.val := h₁
  rw [h₃] at h₄
  have h₅ : (x i : ℤ) = (x i : ℤ) + δ.val := h₄
  have h₆ : (δ.val : ℤ) = 0 := by linarith
  have h₇ : δ.val ∈ ({1, -1} : Finset ℤ) := δ.prop
  have h₈ : (δ.val : ℤ) = 1 ∨ (δ.val : ℤ) = -1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₇ ; omega
  rcases h₈ with (h₈ | h₈)
  ·
    linarith
  ·
    linarith

theorem round1_h1 (n : ℕ)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (k₀ : ℕ):
  ∀ (u v : State n), u ∈ State.validNext v → u.1 ∈ v.2 := by
  intro u v h
  have h₁ : u.1 ∈ v.2 ∧ (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), u.1 i = v.1 i + δ.val ∧ ∀ j ≠ i, u.1 j = v.1 j) ∧ u.2 = v.2.erase u.1 := by
    simpa [State.validNext, Set.mem_setOf_eq] using h
  exact h₁.1

theorem round1_lemma_l1 (n : ℕ)
  (hn : 1 ≤ n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (k₀ : ℕ)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m))
  (h_lemma1_strong : ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3),
    x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1))
  (h1 : ∀ (u v : State n), u ∈ State.validNext v → u.1 ∈ v.2):
  ∀ (t : ℕ), 1 ≤ t → t ≤ k₀ → (s t).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ (r : ℕ), 1 ≤ r → r ≤ t - 1 → (s t).1 ≠ (s r).1 := by
  intro t ht1 ht2
  have h_t1 : t - 1 < k₀ := by omega
  have h_eq : (t - 1) + 1 = t := by omega
  have h3 : s (((t - 1) + 1)) ∈ State.validNext (s (t - 1)) := h2 (t - 1) h_t1
  rw [h_eq] at h3
  have h4 : (s t).1 ∈ (s (t - 1)).2 := h1 (s t) (s (t - 1)) h3
  have h5 : t - 1 ≤ k₀ := by omega
  have h6 := h_lemma1_strong (t - 1) h5 ((s t).1)
  have h7 : (s t).1 ∈ (s (t - 1)).2 := h4
  have h8 : (s t).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ (r : ℕ), 1 ≤ r → r ≤ t - 1 → (s t).1 ≠ (s r).1 := by
    have h9 : (s t).1 ∈ (s (t - 1)).2 := h7
    have h10 := h6.mp h9
    simpa using h10
  exact h8

theorem round1_lemma_l2 (n : ℕ)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (k₀ : ℕ)
  (hrollout : IsRollout a b s)
  (h_b_def : ∀ (st : State n), b st = (f st.1, st.2.erase (f st.1))):
  ∀ (r : ℕ), Odd r → (s (r + 1)).1 = f ((s r).1) := by
  intro r hr
  have h1 : ∀ i, Odd i → s (i + 1) = b (s i) := hrollout.2.2
  have h1r : s (r + 1) = b (s r) := h1 r hr
  have h2 : b (s r) = (f (s r).1, (s r).2.erase (f (s r).1)) := h_b_def (s r)
  rw [h1r, h2]

theorem round1_lemma_l4 (n : ℕ)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (k₀ : ℕ)
  (lemma_l1 : ∀ (t : ℕ), 1 ≤ t → t ≤ k₀ → (s t).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ (r : ℕ), 1 ≤ r → r ≤ t - 1 → (s t).1 ≠ (s r).1):
  ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := by
  intro m h1 h2
  have h_main : (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ (r : ℕ), 1 ≤ r → r ≤ m - 1 → (s m).1 ≠ (s r).1 := lemma_l1 m h1 h2
  exact h_main.1

theorem round1_lemma_l3 (n : ℕ)
  (hn : 1 ≤ n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_f1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x)
  (b : Strategy n)
  (a : Strategy n)
  (s : ℕ → State n)
  (k₀ : ℕ)
  (lemma_l2 : ∀ (r : ℕ), Odd r → (s (r + 1)).1 = f ((s r).1))
  (lemma_l4 : ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3))):
  ∀ (r : ℕ), Even r → 2 ≤ r → r ≤ k₀ → f ((s r).1) = (s (r - 1)).1 := by
  intro r h_even h2 h_le
  have h1 : 2 ≤ r := h2
  have h3 : 1 ≤ r - 1 := by omega
  have h4 : r - 1 ≤ k₀ := by omega
  have h5 : Odd (r - 1) := by
    rcases h_even with ⟨k, hk⟩
    have h6 : r = k + k := hk
    have h7 : r = 2 * k := by
      linarith
    have h8 : 1 ≤ k := by omega
    have h9 : ∃ k' : ℕ, k = k' + 1 := by
      refine' ⟨k - 1, _⟩
      omega
    rcases h9 with ⟨k', hk'⟩
    have h10 : r = 2 * (k' + 1) := by
      linarith
    have h11 : r - 1 = 2 * k' + 1 := by omega
    rw [Nat.odd_iff]
    omega
  have h6 : (s r).1 = f ((s (r - 1)).1) := by
    have h7 := lemma_l2 (r - 1) h5
    have h8 : (r - 1) + 1 = r := by omega
    rw [h8] at h7
    exact h7
  have h_x_ne_zero : (s (r - 1)).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := lemma_l4 (r - 1) h3 h4
  have h9 : f ((s r).1) = f (f ((s (r - 1)).1)) := by rw [h6]
  rw [h9]
  have h10 : f (f ((s (r - 1)).1)) = (s (r - 1)).1 := h_f1 ((s (r - 1)).1) h_x_ne_zero
  rw [h10]

lemma round1_h_x_ne_zero (n : ℕ)
  (k₀ : ℕ)
  (a b : Strategy n)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m))
  (h_lemma1_strong : ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3), x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1))
  (h_k₀_pos : 1 ≤ k₀)
  (h_k_odd : Odd k₀):
  (s k₀).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := by
  have h_k₀_pos' : k₀ ≥ 1 := h_k₀_pos
  have h1 : k₀ - 1 < k₀ := by omega
  have h2' : s ((k₀ - 1) + 1) ∈ State.validNext (s (k₀ - 1)) := h2 (k₀ - 1) h1
  have h_eq : (k₀ - 1) + 1 = k₀ := by omega
  rw [h_eq] at h2'
  have h_main : (s k₀).1 ∈ (s (k₀ - 1)).2 ∧ (∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), (s k₀).1 i = (s (k₀ - 1)).1 i + δ.val ∧ ∀ j ≠ i, (s k₀).1 j = (s (k₀ - 1)).1 j) ∧ (s k₀).2 = (s (k₀ - 1)).2.erase (s k₀).1 := by
    simpa [State.validNext] using h2'
  have h3 : (s k₀).1 ∈ (s (k₀ - 1)).2 := h_main.1
  by_contra h4
  have h5 : (fun (_ : Fin n) => (0 : Fin 3)) ∈ (s (k₀ - 1)).2 := by
    rw [h4] at h3
    exact h3
  have h6 := h_lemma1_strong (k₀ - 1) (by omega) (fun (_ : Fin n) => (0 : Fin 3))
  rw [h6] at h5
  simp at h5

lemma round1_h_main_goal (n : ℕ)
  (k₀ : ℕ)
  (a b : Strategy n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_f1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x)
  (h_f2 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ (fun (_ : Fin n) => (0 : Fin 3)))
  (h_f3 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m))
  (h_lemma1_strong : ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3), x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1))
  (h_f_not_in_prev : ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → Odd m → ∀ r : ℕ, 1 ≤ r → r ≤ m → f ((s m).1) ≠ (s r).1)
  (h_b_def : ∀ (st : State n), b st = (f st.1, st.2.erase (f st.1)))
  (h_k_odd : Odd k₀):
  s (k₀ + 1) ∈ State.validNext (s k₀) := by
  have h_k₀_pos : 1 ≤ k₀ := by
    by_contra h
    have h' : k₀ = 0 := by omega
    rw [h'] at h_k_odd
    simp_all [Nat.odd_iff]
  let x := (s k₀).1
  have hx : x ≠ (fun (_ : Fin n) => (0 : Fin 3)) := round1_h_x_ne_zero n k₀ a b s hrollout h2 h_lemma1_strong h_k₀_pos h_k_odd
  have h5 : ∀ r : ℕ, 1 ≤ r → r ≤ k₀ → f x ≠ (s r).1 := h_f_not_in_prev k₀ h_k₀_pos (by linarith) h_k_odd
  have h6 : f x ≠ (fun (_ : Fin n) => (0 : Fin 3)) := h_f2 x hx
  have h7 : f x ∈ (s k₀).2 := by
    have h8 := h_lemma1_strong k₀ (by linarith) (f x)
    rw [h8] ; exact ⟨h6, h5⟩
  have h9 : s (k₀ + 1) = b (s k₀) := by
    have h10 : ∀ i : ℕ, Odd i → s (i + 1) = b (s i) := hrollout.right.2
    exact h10 k₀ h_k_odd
  have h111 : b (s k₀) = (f ((s k₀).1), (s k₀).2.erase (f ((s k₀).1))) := h_b_def (s k₀)
  have h11 : b (s k₀) = (f x, (s k₀).2.erase (f x)) := by
    simpa [show x = (s k₀).1 from rfl] using h111
  have h12 : s (k₀ + 1) = (f x, (s k₀).2.erase (f x)) := by
    rw [h9, h11]
  have h13 : s (k₀ + 1) ∈ State.validNext (s k₀) := by
    rw [h12]
    simpa [State.validNext, hx, h7, h_f3 x hx] using h_f3 x hx
  exact h13

theorem round1_h_lemma3 (n : ℕ)
  (hn : 1 ≤ n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_f1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x)
  (h_f2 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ (fun (_ : Fin n) => (0 : Fin 3)))
  (h_f3 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
    ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j)
  (b : Strategy n)
  (h_b_def : ∀ (st : State n), b st = (f st.1, st.2.erase (f st.1)))
  (a : Strategy n)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (k₀ : ℕ)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m))
  (h_lemma1_strong : ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3),
    x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1))
  (h_f_x_neq_x : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ x)
  (h_f_not_in_prev : ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → Odd m → ∀ r : ℕ, 1 ≤ r → r ≤ m → f ((s m).1) ≠ (s r).1):
  ∀ m : ℕ, 1 ≤ m → m ≤ k₀ → Odd m → s (m + 1) ∈ State.validNext (s m) := by
  have h_main_goal : ∀ (h_k_odd : Odd k₀), s (k₀ + 1) ∈ State.validNext (s k₀) := by
    intro h_k_odd
    exact round1_h_main_goal n k₀ a b f h_f1 h_f2 h_f3 s hrollout h2 h_lemma1_strong h_f_not_in_prev h_b_def h_k_odd
  intro m h1 h2' h3
  by_cases hlt : m < k₀
  ·
    exact h2 m hlt
  ·
    have h_eq : m = k₀ := by omega
    rw [h_eq]
    have h4 : Odd k₀ := by
      rw [← h_eq]
      exact h3
    exact h_main_goal h4

theorem round1_h_f_not_in_prev (n : ℕ)
  (hn : 1 ≤ n)
  (f : (Fin n → Fin 3) → (Fin n → Fin 3))
  (h_f1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x)
  (h_f3 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
    ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j)
  (b : Strategy n)
  (h_b_def : ∀ (st : State n), b st = (f st.1, st.2.erase (f st.1)))
  (a : Strategy n)
  (s : ℕ → State n)
  (hrollout : IsRollout a b s)
  (k₀ : ℕ)
  (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m))
  (h_lemma1_strong : ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3),
    x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1))
  (h_f_x_neq_x : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ x):
  ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → Odd m → ∀ r : ℕ, 1 ≤ r → r ≤ m → f ((s m).1) ≠ (s r).1 := by
  have h1 : ∀ (u v : State n), u ∈ State.validNext v → u.1 ∈ v.2 := by
    exact round1_h1 n f b a s k₀
  have lemma_l1 : ∀ (t : ℕ), 1 ≤ t → t ≤ k₀ → (s t).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ (r : ℕ), 1 ≤ r → r ≤ t - 1 → (s t).1 ≠ (s r).1 := by
    exact round1_lemma_l1 n hn f b a s k₀ h2 h_lemma1_strong h1
  have lemma_l2 : ∀ (r : ℕ), Odd r → (s (r + 1)).1 = f ((s r).1) := by
    exact round1_lemma_l2 n f b a s k₀ hrollout h_b_def
  have lemma_l4 : ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := by
    exact round1_lemma_l4 n f b a s k₀ lemma_l1
  have lemma_l3 : ∀ (r : ℕ), Even r → 2 ≤ r → r ≤ k₀ → f ((s r).1) = (s (r - 1)).1 := by
    exact round1_lemma_l3 n hn f h_f1 b a s k₀ lemma_l2 lemma_l4
  intro m hm1 hm2 hm3
  intro r hr1 hr2
  by_contra h_contra
  have h : f ((s m).1) = (s r).1 := by tauto
  by_cases h6 : r = m
  ·
    have h61 : f ((s m).1) = (s m).1 := by
      rw [h6] at h
      tauto
    have h62 : (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := lemma_l4 m hm1 hm2
    have h63 : f ((s m).1) ≠ (s m).1 := h_f_x_neq_x ((s m).1) h62
    tauto
  ·
    have h7 : r < m := by
      omega
    by_cases h8 : Odd r
    ·
      have h91 : f ((s r).1) = (s m).1 := by
        have h911 : (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := lemma_l4 m hm1 hm2
        have h912 : f (f ((s m).1)) = (s m).1 := h_f1 ((s m).1) h911
        have h913 : f (f ((s m).1)) = f ((s r).1) := by
          have h9131 : f ((s m).1) = (s r).1 := by tauto
          rw [h9131]
        have h914 : f ((s r).1) = (s m).1 := by
          have h915 : f (f ((s m).1)) = (s m).1 := h912
          have h916 : f (f ((s m).1)) = f ((s r).1) := h913
          rw [h916] at h915
          tauto
        tauto
      have h92 : (s (r + 1)).1 = f ((s r).1) := lemma_l2 r h8
      have h93 : (s m).1 = (s (r + 1)).1 := by
        have h931 : (s (r + 1)).1 = f ((s r).1) := h92
        have h932 : f ((s r).1) = (s m).1 := h91
        rw [h931, h932]
      have h94 : r + 1 ≠ m := by
        by_contra h941
        have h942 : r + 1 = m := by tauto
        have h95 : Odd r := h8
        have h96 : Even (r + 1) := by
          simp [Nat.even_iff, Nat.odd_iff] at h95 ⊢ ; omega
        have h97 : Odd m := hm3
        have h98 : r + 1 = m := h942
        have h99 : Even m := by
          have h100 : Even (r + 1) := h96
          have h101 : r + 1 = m := h98
          have h102 : Even m := by
            rw [h101] at h100
            tauto
          tauto
        simp [Nat.odd_iff, Nat.even_iff] at h97 h99 ; omega
      have h95 : r + 1 < m := by
        omega
      have h96 : r + 1 ≤ m - 1 := by
        omega
      have h97 : 1 ≤ r + 1 := by omega
      have h98 : (s m).1 ≠ (s (r + 1)).1 := by
        have h981 := (lemma_l1 m hm1 hm2).2 (r + 1) (by bound) (by omega)
        tauto
      tauto
    ·
      have h81 : Even r := by
        by_cases h82 : Even r
        · tauto
        ·
          have h83 : Odd r := by
            simp [Nat.even_iff, Nat.odd_iff] at * ; bound
          tauto
      have h10 : 2 ≤ r := by
        grind
      have h101 : r ≤ k₀ := by omega
      have h14 : f ((s r).1) = (s (r - 1)).1 := by
        exact lemma_l3 r h81 h10 h101
      have h15 : (s m).1 = (s (r - 1)).1 := by
        have h151 : (s m).1 ≠ (fun (_ : Fin n) => (0 : Fin 3)) := lemma_l4 m hm1 hm2
        have h152 : f (f ((s m).1)) = (s m).1 := h_f1 ((s m).1) h151
        have h153 : f (f ((s m).1)) = f ((s r).1) := by
          have h1531 : f ((s m).1) = (s r).1 := by tauto
          rw [h1531]
        have h154 : (s m).1 = f ((s r).1) := by
          have h1541 : f (f ((s m).1)) = (s m).1 := h152
          have h1542 : f (f ((s m).1)) = f ((s r).1) := h153
          rw [h1542] at h1541
          tauto
        have h155 : f ((s r).1) = (s (r - 1)).1 := h14
        rw [h155] at h154
        tauto
      have h16 : 1 ≤ r - 1 := by omega
      have h17 : r - 1 ≤ m - 1 := by bound
      have h18 : (s m).1 ≠ (s (r - 1)).1 := by
        have h181 := (lemma_l1 m hm1 hm2).2 (r - 1) (by omega) (by bound)
        tauto
      tauto

theorem round1_h_k0_is_even (n : ℕ)
  (hn : 1 ≤ n):
  ∀ (f : (Fin n → Fin 3) → (Fin n → Fin 3))
    (h_f1 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f (f x) = x)
    (h_f2 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ (fun (_ : Fin n) => (0 : Fin 3)))
    (h_f3 : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) →
      ∃ (i : Fin n) (δ : ({1, -1} : Finset ℤ)), f x i = x i + δ.val ∧ ∀ j ≠ i, f x j = x j)
    (b : Strategy n)
    (h_b_def : ∀ (st : State n), b st = (f st.1, st.2.erase (f st.1)))
    (a : Strategy n)
    (s : ℕ → State n)
    (hrollout : IsRollout a b s)
    (k₀ : ℕ)
    (h1 : s (k₀ + 1) ∉ State.validNext (s k₀))
    (h2 : ∀ m < k₀, s (m + 1) ∈ State.validNext (s m)),
    Even k₀ := by
  intro f h_f1 h_f2 h_f3 b h_b_def a s hrollout k₀ h1 h2
  have h_lemma1_strong : ∀ t : ℕ, t ≤ k₀ → ∀ (x : Fin n → Fin 3),
    x ∈ (s t).2 ↔ (x ≠ (fun (_ : Fin n) => (0 : Fin 3)) ∧ ∀ r : ℕ, 1 ≤ r → r ≤ t → x ≠ (s r).1) := by
    exact round1_h_lemma1_strong n hn f b a s hrollout k₀ h2
  have h_f_x_neq_x : ∀ (x : Fin n → Fin 3), x ≠ (fun (_ : Fin n) => (0 : Fin 3)) → f x ≠ x := by
    exact round1_h_f_x_neq_x n hn f h_f1 h_f2 h_f3
  have h_f_not_in_prev : ∀ (m : ℕ), 1 ≤ m → m ≤ k₀ → Odd m → ∀ r : ℕ, 1 ≤ r → r ≤ m → f ((s m).1) ≠ (s r).1 := by
    exact round1_h_f_not_in_prev n hn f h_f1 h_f3 b h_b_def a s hrollout k₀ h2 h_lemma1_strong h_f_x_neq_x
  have h_lemma3 : ∀ m : ℕ, 1 ≤ m → m ≤ k₀ → Odd m → s (m + 1) ∈ State.validNext (s m) := by
    exact round1_h_lemma3 n hn f h_f1 h_f2 h_f3 b h_b_def a s hrollout k₀ h2 h_lemma1_strong h_f_x_neq_x h_f_not_in_prev
  by_cases h : Odd k₀
  ·
    have h3 : 1 ≤ k₀ := by
      by_contra h31
      have h32 : k₀ = 0 := by omega
      rw [h32] at h
      norm_num at h
    have h4 : s (k₀ + 1) ∈ State.validNext (s k₀) := h_lemma3 k₀ (by omega) (by linarith) h
    tauto
  ·
    have h5 : Even k₀ := by
      simp [Nat.even_iff, Nat.odd_iff] at h ⊢ ; omega
    tauto

theorem putnam_2025_a3 (n : ℕ)
  (hn : 1 ≤ n):
  ∃ b : Strategy n, ∀ a : Strategy n,
    ∀ s : ℕ → State n, IsRollout a b s →
      ∃ k : ℕ, Even k ∧ (∀ i < k, s (i + 1) ∈ (s i).validNext) ∧ s (k + 1) ∉ (s k).validNext := by
      have h_f := round1_h_f n hn
      have h_k0_exists_min := round1_h_k0_exists_min n hn
      have h_k0_is_even := round1_h_k0_is_even n hn
      rcases h_f with ⟨f, h_f1, h_f2, h_f3⟩
      set b : Strategy n := fun (st : State n) => (f st.1, st.2.erase (f st.1)) with hb_def
      use b
      intro a s hrollout
      have h_k0 : ∃ k₀ : ℕ, (s (k₀ + 1) ∉ State.validNext (s k₀)) ∧ (∀ m < k₀, s (m + 1) ∈ State.validNext (s m)) := by
        exact h_k0_exists_min a b s hrollout
      rcases h_k0 with ⟨k₀, h1, h2⟩
      have h_even_k₀ : Even k₀ := by
        exact h_k0_is_even f h_f1 h_f2 h_f3 b (by
          intro st
          rfl) a s hrollout k₀ h1 h2
      refine' ⟨k₀, h_even_k₀, _⟩
      exact ⟨h2, h1⟩

end Putnam2025A3
