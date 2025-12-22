import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Finset ZMod Classical

namespace Putnam2025B5

lemma round1_h1 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p):
  ((x : ZMod p)⁻¹).val < p := by
  exact ZMod.val_lt ((x : ZMod p)⁻¹)

lemma round1_h2 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p)
  (h1 : ((x : ZMod p)⁻¹).val < p):
  1 ≤ ((x : ZMod p)⁻¹).val := by
  let y : ZMod p := (x : ZMod p)⁻¹
  have h_x_ne_zero : (x : ZMod p) ≠ 0 := by
    intro h
    have h' : (x : ZMod p) = 0 := h
    have h'' : p ∣ x := (ZMod.natCast_eq_zero_iff x p).mp h'
    have h₃ : x < p := hx2
    have h₄ : p ∣ x := h''
    have h₅ : x = 0 := Nat.eq_zero_of_dvd_of_lt h₄ h₃
    linarith
  have h₃ : (x : ZMod p) * y = 1 := by
    simp [y, h_x_ne_zero]
  have h_inv_ne_zero : y ≠ (0 : ZMod p) := by
    intro h
    rw [h] at h₃
    simp at h₃
  have h₆ : ((y.val : ZMod p)) = y := by
    exact natCast_zmod_val y
  have h₇ : y.val ≠ 0 := by
    intro h_contra
    rw [h_contra] at h₆
    have h₈ : ((0 : ℕ) : ZMod p) = y := by simpa using h₆
    have h₉ : (0 : ZMod p) = y := by simpa using h₈
    exact h_inv_ne_zero (Eq.symm h₉)
  have h₁₀ : 1 ≤ y.val := Nat.pos_of_ne_zero h₇
  exact h₁₀

lemma round1_h3 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p)
  (h1 : ((x : ZMod p)⁻¹).val < p)
  (h2 : 1 ≤ ((x : ZMod p)⁻¹).val):
  (x * ((x : ZMod p)⁻¹).val) % p = 1 := by
  let y : ZMod p := (x : ZMod p)⁻¹
  have h_x_ne_zero : (x : ZMod p) ≠ 0 := by
    intro h
    have h' : (x : ZMod p) = 0 := h
    have h'' : p ∣ x := (ZMod.natCast_eq_zero_iff x p).mp h'
    have h₃ : x < p := hx2
    have h₄ : p ∣ x := h''
    have h₅ : x = 0 := Nat.eq_zero_of_dvd_of_lt h₄ h₃
    linarith
  have h₃ : (x : ZMod p) * y = 1 := by
    simp [y, h_x_ne_zero]
  have h₆ : ((y.val : ZMod p)) = y := by
    exact natCast_zmod_val y
  have h₇ : (((x * y.val : ℕ) : ZMod p)) = (1 : ZMod p) := by
    calc
      (((x * y.val : ℕ) : ZMod p)) = (x : ZMod p) * (y.val : ZMod p) := by
        simp
      _ = (x : ZMod p) * y := by rw [h₆]
      _ = 1 := h₃
  have h₉ : (p : ℕ) > 1 := by linarith
  have h₁₆ : ((x * y.val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    simpa using h₇
  have h₁₇ : (x * y.val) ≡ 1 [MOD p] := by
    have h₁₈ : ((x * y.val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := h₁₆
    have h₁₉ : (x * y.val) ≡ 1 [MOD p] := by
      let h₂₀ := (ZMod.eq_iff_modEq_nat (n := p) (a := x * y.val) (b := 1))
      exact h₂₀.mp h₁₈
    exact h₁₉
  have h₁₁ : (x * y.val) % p = 1 % p := by
    simpa [Nat.ModEq] using h₁₇
  have h₁₂ : 1 % p = 1 := by
    apply Nat.mod_eq_of_lt
    linarith
  rw [h₁₂] at h₁₁
  exact h₁₁

theorem round1_exists_inv_function (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p):
  ∃ (inv : ℕ → ℕ), ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1) := by
  let inv : ℕ → ℕ := fun x => ((x : ZMod p)⁻¹).val
  refine' ⟨inv, _⟩
  intro x hx
  have hx1 : 1 ≤ x := hx.1
  have hx2 : x < p := hx.2
  have h1 : 1 ≤ inv x := round1_h2 p hp3 x hx1 hx2 (round1_h1 p hp3 x hx1 hx2)
  have h2 : inv x < p := round1_h1 p hp3 x hx1 hx2
  have h3 : (x * inv x) % p = 1 := round1_h3 p hp3 x hx1 hx2 (round1_h1 p hp3 x hx1 hx2) h1
  exact ⟨h1, h2, h3⟩

lemma round1_h3_a1ad03 (p a m : ℕ)
  (hp : p > 10)
  (h1 : 2 * a + m = p - 1)
  (h2 : m ≤ 6):
  2 * a ≥ p - 7 := by
  omega

lemma round1_h_main (p a m : ℕ)
  (hp : p > 10)
  (h3 : 2 * a ≥ p - 7):
  (a : ℝ) > (p : ℝ) / 4 - 1 := by
  have h_p_ge_7 : p ≥ 7 := by omega
  have h41 : (2 * a : ℕ) ≥ (p - 7 : ℕ) := h3
  have h4 : (2 * (a : ℝ)) ≥ ((p : ℝ) - 7) := by
    have h42 : ((2 * a : ℕ) : ℝ) ≥ ((p - 7 : ℕ) : ℝ) := by exact_mod_cast h41
    have h43 : ((p - 7 : ℕ) : ℝ) = (p : ℝ) - 7 := by
      rw [Nat.cast_sub h_p_ge_7]
      simp
    rw [h43] at h42
    simpa using h42
  have h5 : (p : ℝ) > 10 := by exact_mod_cast hp
  have h6 : ((p : ℝ) - 7) > ((p : ℝ) / 2) - 2 := by linarith
  have h7 : (2 * (a : ℝ)) > ((p : ℝ) / 2) - 2 := by linarith
  have h8 : (4 * (a : ℝ)) > (p : ℝ) - 4 := by linarith
  have h9 : (a : ℝ) > (p : ℝ) / 4 - 1 := by linarith
  exact h9

theorem round1_inequality_lemma (p a m : ℕ)
  (hp : p > 10)
  (h1 : 2 * a + m = p - 1)
  (h2 : m ≤ 6):
  (a : ℝ) > (p : ℝ) / 4 - 1 := by
  have h3 : 2 * a ≥ p - 7 := by
    exact round1_h3_a1ad03 p a m hp h1 h2
  have h_main : (a : ℝ) > (p : ℝ) / 4 - 1 := by
    exact round1_h_main p a m hp h3
  exact h_main

lemma round1_h_main_1046b9 (p : ℕ)
  [hp : Fact p.Prime]
  (P : ZMod p → Prop)
  [hP : DecidablePred P]:
  (#{x : ZMod p | P x} : ℝ) = ((Finset.filter (fun (x : ZMod p) => P x) (Finset.univ : Finset (ZMod p))).card : ℝ) := by
  let S := (Finset.filter (fun (x : ZMod p) => P x) (Finset.univ : Finset (ZMod p)))
  have h₁ : (S : Set (ZMod p)) = {x : ZMod p | P x} := by
    ext x
    simp [S]
  have h₂ : Set.encard ({x : ZMod p | P x} : Set (ZMod p)) = S.card := by
    have h₃ : Set.encard ((S : Set (ZMod p))) = S.card := by
      exact Set.encard_coe_eq_coe_finsetCard S
    rw [h₁.symm] at *
    exact h₃
  norm_cast at h₂ ⊢

theorem round1_ncard_to_finset_card (p : ℕ)
  [hp : Fact p.Prime]
  (P : ZMod p → Prop)
  [hP : DecidablePred P]:
  (#{x : ZMod p | P x} : ℝ) = ((Finset.filter (fun (x : ZMod p) => P x) (Finset.univ : Finset (ZMod p))).card : ℝ) := by
  exact round1_h_main_1046b9 p P

lemma round1_h5 (α β : Type*)
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (T : Finset β)
  (f : α → β)
  (g : β → α)
  (h3 : ∀ x ∈ S, g (f x) = x):
  ∀ (x₁ x₂ : α), x₁ ∈ S → x₂ ∈ S → f x₁ = f x₂ → x₁ = x₂ := by
  intro x₁ x₂ hx₁ hx₂ h_eq
  have h5₁ : g (f x₁) = x₁ := h3 x₁ hx₁
  have h5₂ : g (f x₂) = x₂ := h3 x₂ hx₂
  rw [h_eq] at h5₁
  rw [h5₁] at h5₂
  exact h5₂

lemma round1_h_S_le_T (α β : Type*)
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (T : Finset β)
  (f : α → β)
  (g : β → α)
  (h1 : ∀ x ∈ S, f x ∈ T)
  (h3 : ∀ x ∈ S, g (f x) = x):
  S.card ≤ T.card := by
  have h5 : ∀ (x₁ x₂ : α), x₁ ∈ S → x₂ ∈ S → f x₁ = f x₂ → x₁ = x₂ := round1_h5 α β S T f g h3
  have h5' : Set.InjOn f (S : Set α) := by
    intro x₁ hx₁ x₂ hx₂ h_eq
    exact h5 x₁ x₂ hx₁ hx₂ h_eq
  have h6 : (Finset.image f S).card = S.card := Finset.card_image_of_injOn h5'
  have h7 : Finset.image f S ⊆ T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact h1 x hx
  have h8 : (Finset.image f S).card ≤ T.card := Finset.card_le_card h7
  rw [h6] at h8
  exact h8

lemma round1_h6 (α β : Type*)
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (T : Finset β)
  (f : α → β)
  (g : β → α)
  (h4 : ∀ y ∈ T, f (g y) = y):
  ∀ (y₁ y₂ : β), y₁ ∈ T → y₂ ∈ T → g y₁ = g y₂ → y₁ = y₂ := by
  intro y₁ y₂ hy₁ hy₂ h_eq
  have h6₁ : f (g y₁) = y₁ := h4 y₁ hy₁
  have h6₂ : f (g y₂) = y₂ := h4 y₂ hy₂
  rw [h_eq] at h6₁
  rw [h6₁] at h6₂
  exact h6₂

lemma round1_h_T_le_S (α β : Type*)
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (T : Finset β)
  (f : α → β)
  (g : β → α)
  (h2 : ∀ y ∈ T, g y ∈ S)
  (h4 : ∀ y ∈ T, f (g y) = y):
  T.card ≤ S.card := by
  have h6 : ∀ (y₁ y₂ : β), y₁ ∈ T → y₂ ∈ T → g y₁ = g y₂ → y₁ = y₂ := round1_h6 α β S T f g h4
  have h6' : Set.InjOn g (T : Set β) := by
    intro y₁ hy₁ y₂ hy₂ h_eq
    exact h6 y₁ y₂ hy₁ hy₂ h_eq
  have h7 : (Finset.image g T).card = T.card := Finset.card_image_of_injOn h6'
  have h8 : Finset.image g T ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact h2 y hy
  have h9 : (Finset.image g T).card ≤ S.card := Finset.card_le_card h8
  rw [h7] at h9
  exact h9

theorem round1_finset_card_eq_of_bijection_general {α β : Type*}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (T : Finset β)
  (f : α → β)
  (g : β → α)
  (h1 : ∀ x ∈ S, f x ∈ T)
  (h2 : ∀ y ∈ T, g y ∈ S)
  (h3 : ∀ x ∈ S, g (f x) = x)
  (h4 : ∀ y ∈ T, f (g y) = y):
  S.card = T.card := by
  have h_S_le_T : S.card ≤ T.card := round1_h_S_le_T α β S T f g h1 h3
  have h_T_le_S : T.card ≤ S.card := round1_h_T_le_S α β S T f g h2 h4
  exact Nat.le_antisymm h_S_le_T h_T_le_S

lemma round1_h_main_7d1b7e (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2 := by
  intro z y1 y2 h
  rcases h with ⟨hz1, hz2, hy11, hy12, hy21, hy22, h_eq1, h_eq2⟩
  have h1 : (z : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ z := (ZMod.natCast_eq_zero_iff z p).mp hz
    have hle : z < p := hz2
    have hpos : 0 < p := by omega
    have h_contra : z = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hle
    omega
  have h_pos_p : 0 < p := by omega
  have h_gt_one_p : 1 < p := by omega
  have h1mod : (1 % p : ℕ) = 1 := by
    simp [Nat.mod_eq_of_lt h_gt_one_p]
  have h21 : ((z * y1 : ℕ) % p = (1 : ℕ) % p) := by
    rw [h1mod]
    exact h_eq1
  have h22 : ((z * y1 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [ZMod.eq_iff_modEq_nat]
    simpa [Nat.ModEq] using h21
  have h2 : (z : ZMod p) * (y1 : ZMod p) = (1 : ZMod p) := by
    have h_cast : (z : ZMod p) * (y1 : ZMod p) = ((z * y1 : ℕ) : ZMod p) := by
      norm_cast
    rw [h_cast]
    simpa using h22
  have h31 : ((z * y2 : ℕ) % p = (1 : ℕ) % p) := by
    rw [h1mod]
    exact h_eq2
  have h32 : ((z * y2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [ZMod.eq_iff_modEq_nat]
    simpa [Nat.ModEq] using h31
  have h3 : (z : ZMod p) * (y2 : ZMod p) = (1 : ZMod p) := by
    have h_cast : (z : ZMod p) * (y2 : ZMod p) = ((z * y2 : ℕ) : ZMod p) := by
      norm_cast
    rw [h_cast]
    simpa using h32
  have h4 : (z : ZMod p) * (y1 : ZMod p) = (z : ZMod p) * (y2 : ZMod p) := by
    rw [h2, h3]
  have h5 : (y1 : ZMod p) = (y2 : ZMod p) := by
    apply mul_left_cancel₀ h1
    simpa using h4
  have h6 : y1 = y2 := by
    have h7 : (y1 : ZMod p) = (y2 : ZMod p) := h5
    have h8 : y1 % p = y2 % p := by
      rw [ZMod.eq_iff_modEq_nat] at h7
      simpa [Nat.ModEq] using h7
    have h9 : y1 < p := hy12
    have h10 : y2 < p := hy22
    have h11 : y1 % p = y1 := Nat.mod_eq_of_lt h9
    have h12 : y2 % p = y2 := Nat.mod_eq_of_lt h10
    rw [h11, h12] at h8
    omega
  exact h6

theorem round1_modular_inverse_unique_lemma (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2 := by
  have h_main : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2 := by
    exact round1_h_main_7d1b7e p hp3 inv h_inv
  exact h_main

lemma round1_h_main_d8c38f (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2):
  ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x := by
  intro x hx
  have h1 : 1 ≤ inv x := (h_inv x hx).1
  have h2 : inv x < p := (h_inv x hx).2.1
  have hxy : (x * inv x) % p = 1 := (h_inv x hx).2.2
  let y := inv x
  have hy1 : 1 ≤ y := h1
  have hy2 : y < p := h2
  have h_yx : (y * x) % p = 1 := by
    have h : (y * x) % p = (x * y) % p := by
      rw [mul_comm]
    rw [h]
    exact hxy
  have h3 : 1 ≤ inv y := (h_inv y ⟨hy1, hy2⟩).1
  have h4 : inv y < p := (h_inv y ⟨hy1, hy2⟩).2.1
  have hyz : (y * inv y) % p = 1 := (h_inv y ⟨hy1, hy2⟩).2.2
  have h5 : (y * inv y) % p = 1 ∧ (y * x) % p = 1 := ⟨hyz, h_yx⟩
  have h6 : inv y = x := h_modular_inverse_unique y (inv y) x ⟨hy1, hy2, h3, h4, hx.1, hx.2, h5⟩
  exact h6

theorem round1_inv_is_involution_lemma (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2):
  ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x := by
  have h_main : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x := by
    exact round1_h_main_d8c38f p hp3 inv h_inv h_modular_inverse_unique
  exact h_main

lemma round1_h_main_3e7737 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2):
  ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a := by
  intro a h
  have h_a1 : 1 ≤ a := h.1
  have h_a2 : a < p := h.2
  let y := (( (a : ZMod p) )⁻¹).val
  have h1 : y < p := by
    exact ZMod.val_lt (((a : ZMod p))⁻¹)
  have h_coprime : Nat.Coprime a p := by
    have h10 : Nat.gcd a p ∣ p := Nat.gcd_dvd_right a p
    have h11 : Nat.gcd a p = 1 ∨ Nat.gcd a p = p := by
      have h12 : Nat.Prime p := hp.1
      have h13 : Nat.gcd a p ∣ p := h10
      exact (Nat.Prime.eq_one_or_self_of_dvd h12 (Nat.gcd a p) h13)
    cases h11 with
    | inl h11 =>
      exact h11
    | inr h11 =>
      have h14 : Nat.gcd a p ∣ a := Nat.gcd_dvd_left a p
      rw [h11] at h14
      have h15 : p ∣ a := h14
      have h16 : p ≤ a := Nat.le_of_dvd (by omega) h15
      omega
  have h_eq1 : ((a : ZMod p) * (((a : ZMod p))⁻¹)) = 1 := by
    exact ZMod.coe_mul_inv_eq_one a h_coprime
  have h_eq2 : (((a : ZMod p))⁻¹) = (y : ZMod p) := by
    simp [y, ZMod.natCast_val]
  have h_eq : (a : ZMod p) * (y : ZMod p) = 1 := by
    rw [h_eq2] at h_eq1
    exact h_eq1
  have h51 : ((a * y : ℕ) : ZMod p) = 1 := by
    simpa [mul_comm] using h_eq
  have h52 : (a * y) ≡ 1 [MOD p] := by
    have h55 : ((a * y : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa using h51
    have h56 : (a * y) ≡ 1 [MOD p] := by
      exact (natCast_eq_natCast_iff (a * y) 1 p).mp h55
    exact h56
  have h_p_gt_one : 1 < p := by linarith
  have h53 : (a * y) % p = 1 % p := by
    exact h52
  have h54 : 1 % p = 1 := by
    apply Nat.mod_eq_of_lt
    linarith
  have h5 : (a * y) % p = 1 := by
    rw [h54] at h53
    exact h53
  have h2 : y ≠ 0 := by
    by_contra h2'
    rw [h2'] at h_eq
    norm_num at h_eq
  have h7 : 1 ≤ y := by omega
  have h6 : 1 ≤ inv a := (h_inv a h).1
  have h8 : inv a < p := (h_inv a h).2.1
  have h9 : (a * inv a) % p = 1 := (h_inv a h).2.2
  have h10 : y = inv a := by
    apply h_modular_inverse_unique a y (inv a) ⟨h_a1, h_a2, h7, h1, h6, h8, h5, h9⟩
  exact h10

theorem round1_zmod_val_eq_inv_lemma (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2):
  ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a := by
  exact round1_h_main_3e7737 p hp3 inv h_inv h_modular_inverse_unique

lemma round1_mod_lemma (p a : ℕ)
  (hp : Fact p.Prime)
  (hp3 : 3 < p)
  (h1 : 1 ≤ a)
  (h2 : a < p):
  (a * (p - 1)) % p = p - a := by
  have h3 : p > 0 := by linarith
  have h4 : a * (p - 1) = a * p - a := by
    cases p with
    | zero => omega
    | succ p' =>
      cases p' with
      | zero => omega
      | succ p'' =>
        simp [Nat.mul_succ, Nat.add_assoc] ; ring_nf ; omega
  rw [h4]
  have h5 : a ≥ 1 := by omega
  have h6 : a * p - a = p * (a - 1) + (p - a) := by
    cases a with
    | zero => omega
    | succ a' =>
      simp ; ring_nf ; omega
  rw [h6]
  have h7 : (p - a) < p := by omega
  have h8 : ((p - a) % p) = (p - a) := Nat.mod_eq_of_lt h7
  have h9 : (p * (a - 1) + (p - a)) % p = ((p * (a - 1)) % p + ((p - a) % p)) % p := by
    rw [Nat.add_mod]
  rw [h9]
  have h10 : (p * (a - 1)) % p = 0 := by
    simp
  rw [h10, h8]
  simp
  omega

lemma round1_h_b_plus_1_lt_p (p a : ℕ)
  (hp : Fact p.Prime)
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h : 1 ≤ a ∧ a + 1 < p):
  inv a + 1 < p := by
  have h₁ : a < p - 1 := by omega
  by_contra h₂
  have h₃ : inv a + 1 ≥ p := by omega
  have h₄ : inv a ≥ p - 1 := by omega
  have h₅ : 1 ≤ a ∧ a < p := ⟨h.1, by omega⟩
  have h₆ : 1 ≤ inv a ∧ inv a < p ∧ (a * inv a) % p = 1 := h_inv a h₅
  have h₇ : inv a < p := h₆.2.1
  have h₈ : inv a = p - 1 := by omega
  have h₉ : (a * inv a) % p = 1 := h₆.2.2
  rw [h₈] at h₉
  have h₁₀ : (a * (p - 1)) % p = 1 := h₉
  have h11 : (a * (p - 1)) % p = p - a := round1_mod_lemma p a hp hp3 h₅.1 h₅.2
  rw [h11] at h₁₀
  have h₁₂ : p - a = 1 := by omega
  have h₁₃ : a = p - 1 := by omega
  omega

lemma round1_acmod_lemma (p a c : ℕ)
  (hp : Fact p.Prime)
  (hp3 : 3 < p)
  (h1 : 1 < c ∧ c < p)
  (h2 : (a * c + c) % p = 1):
  (a * c) % p = p + 1 - c := by
  have h3 : p > 0 := by linarith
  let r := (a * c) % p
  have hr : r < p := Nat.mod_lt (a * c) h3
  have h4 : (r + c) % p = 1 := by
    have h5 : (a * c + c) % p = ((a * c) % p + c % p) % p := by
      simp [Nat.add_mod]
    have h6 : c % p = c := by
      apply Nat.mod_eq_of_lt
      linarith
    rw [h6] at h5
    have h7 : (a * c + c) % p = (r + c) % p := by
      simp [r]
    rw [h7] at h2
    exact h2
  let x := r + c
  have h_lt1 : x < 2 * p := by
    dsimp [x, r]
    omega
  have h_eq1 : x % p = 1 := h4
  let q := x / p
  have h_div : p * q + x % p = x := Nat.div_add_mod x p
  have h_eq2 : p * q + 1 = x := by
    rw [h_eq1] at h_div
    simpa using h_div
  have h_eq3 : x = p * q + 1 := by linarith
  have hq_lt2 : q < 2 := by
    by_contra h
    have h' : q ≥ 2 := Nat.le_of_not_lt h
    have h_contra : x ≥ 2 * p + 1 := by
      rw [h_eq3]
      nlinarith
    linarith
  have hq01 : q = 0 ∨ q = 1 := by
    interval_cases q <;> tauto
  rcases hq01 with (h_cases0 | h_cases1)
  ·
    have h_x_eq1 : x = 1 := by
      rw [h_cases0] at h_eq3 ; omega
    have h_rc_eq1 : r + c = 1 := by
      simpa [x] using h_x_eq1
    have h_c_ge2 : c ≥ 2 := by linarith [h1.1]
    have h_pos : r + c ≥ 2 := by
      linarith
    rw [h_rc_eq1] at h_pos
    norm_num at h_pos
  ·
    have h_x_eq_p1 : x = p + 1 := by
      rw [h_cases1] at h_eq3
      ring_nf at * ; linarith
    have h_rc_eq_p1 : r + c = p + 1 := by
      simpa [x] using h_x_eq_p1
    have h_goal : r = p + 1 - c := by omega
    simpa [r] using h_goal

lemma round1_main_arith_lemma (p a : ℕ)
  (hp : Fact p.Prime)
  (hp3 : 3 < p)
  (b c : ℕ)
  (h1 : 1 ≤ a ∧ a < p)
  (h2 : 1 ≤ a + 1 ∧ a + 1 < p)
  (hb1 : 1 ≤ b ∧ b < p ∧ (a * b) % p = 1)
  (hc1 : 1 ≤ c ∧ c < p ∧ ((a + 1) * c) % p = 1):
  ((b + 1) * (p + 1 - c)) % p = 1 := by
  have h₃ : p > 0 := by linarith
  have h₄ : (a * b) % p = 1 := hb1.2.2
  have h₅ : ((a + 1) * c) % p = 1 := hc1.2.2
  have h₆ : 1 ≤ c := hc1.1
  have h₇ : c < p := hc1.2.1
  have h₈ : 1 < c := by
    by_contra h₉
    have h₁₀ : c ≤ 1 := by omega
    have h₁₁ : c = 1 := by omega
    rw [h₁₁] at h₅
    have h12 : ((a + 1) * 1) % p = 1 := h₅
    have h13 : (a + 1) % p = 1 := by simpa using h12
    have h14 : a + 1 < p := h2.2
    have h15 : (a + 1) % p = a + 1 := Nat.mod_eq_of_lt h14
    rw [h15] at h13
    omega
  let d := p + 1 - c
  have h9 : (a * c + c) % p = 1 := by
    have h10 : (a * c + c) = (a + 1) * c := by ring
    rw [h10]
    exact h₅
  have h11 : (a * c) % p = d := round1_acmod_lemma p a c hp hp3 ⟨h₈, h₇⟩ h9
  have h12 : ((a * c) * (b + 1)) % p = 1 := by
    have h13 : (a * c) * (b + 1) = c * (a * b) + a * c := by ring
    have h17 : ((c * (a * b)) % p) = c % p := by
      simp [Nat.mul_mod, h₄]
    have h18 : (((a * c) * (b + 1)) % p) = ((c * (a * b) + a * c) % p) := by rw [h13]
    rw [h18]
    have h19 : ((c * (a * b) + a * c) % p) = ( ( (c * (a * b)) % p ) + ( (a * c) % p ) ) % p := by simp [Nat.add_mod]
    rw [h19, h17]
    have h20 : c % p = c := Nat.mod_eq_of_lt h₇
    rw [h20]
    have h21 : (c + (a * c) % p) % p = 1 := by
      have h22 : (a * c) % p = d := h11
      rw [h22]
      have h23 : (c + d) % p = 1 := by
        have h24 : c + d = p + 1 := by omega
        rw [h24]
        have h26 : p > 0 := h₃
        have h27 : 1 < p := by linarith
        have h25 : (p + 1) % p = 1 % p := by
          simp
        rw [h25]
        have h28 : 1 % p = 1 := Nat.mod_eq_of_lt h27
        rw [h28]
      exact h23
    exact h21
  have h15 : d < p := by omega
  have h16 : (d * (b + 1)) % p = ((a * c) * (b + 1)) % p := by
    have h17 : (d * (b + 1)) % p = ((d % p) * ((b + 1) % p)) % p := by
      simp [Nat.mul_mod]
    have h18 : (d % p) = d := by
      apply Nat.mod_eq_of_lt
      exact h15
    rw [h17, h18]
    have h19 : ((a * c) * (b + 1)) % p = (((a * c) % p) * ((b + 1) % p)) % p := by
      simp [Nat.mul_mod]
    rw [h19]
    rw [h11]
  have h_goal : (d * (b + 1)) % p = 1 := by
    calc
      (d * (b + 1)) % p = ((a * c) * (b + 1)) % p := h16
      _ = 1 := h12
  simpa [mul_comm d (b + 1)] using h_goal

theorem round1_key_property_lemma (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a):
  ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1) := by
  intro a h
  have h1 : 1 ≤ a ∧ a < p := ⟨h.1, by omega⟩
  have h2 : 1 ≤ a + 1 ∧ a + 1 < p := ⟨by omega, h.2⟩
  let b := inv a
  let c := inv (a + 1)
  have hb : 1 ≤ b ∧ b < p ∧ (a * b) % p = 1 := h_inv a h1
  have hc : 1 ≤ c ∧ c < p ∧ ((a + 1) * c) % p = 1 := h_inv (a + 1) h2
  let d := p + 1 - c
  have h_c_gt_one : 1 < c := by
    by_contra h_contra
    have h₁₀ : c ≤ 1 := by omega
    have h₁₁ : c = 1 := by omega
    rw [h₁₁] at hc
    have h12 : ((a + 1) * 1) % p = 1 := hc.2.2
    have h13 : (a + 1) % p = 1 := by simpa using h12
    have h14 : a + 1 < p := h2.2
    have h15 : (a + 1) % p = a + 1 := Nat.mod_eq_of_lt h14
    rw [h15] at h13
    omega
  have h_main : ((b + 1) * d) % p = 1 := round1_main_arith_lemma p a (by assumption) (by assumption) b c h1 h2 hb hc
  have h_b_plus_1_lt_p : b + 1 < p := round1_h_b_plus_1_lt_p p a (by assumption) (by assumption) inv h_inv h
  have h_d_lt_p : d < p := by
    dsimp only [d]
    omega
  have h_pos1 : 1 ≤ b + 1 := by omega
  have h_pos2 : 1 ≤ d := by omega
  have h_inv_b_plus_1_all := h_inv (b + 1) ⟨h_pos1, h_b_plus_1_lt_p⟩
  have h_inv_b_plus_1_1 : 1 ≤ inv (b + 1) := h_inv_b_plus_1_all.1
  have h_inv_b_plus_1_2 : inv (b + 1) < p := h_inv_b_plus_1_all.2.1
  have h_eq_z1 : ((b + 1) * inv (b + 1)) % p = 1 := h_inv_b_plus_1_all.2.2
  have h_unique : inv (b + 1) = d := h_modular_inverse_unique (b + 1) (inv (b + 1)) d ⟨h_pos1, h_b_plus_1_lt_p, h_inv_b_plus_1_1, h_inv_b_plus_1_2, h_pos2, h_d_lt_p, h_eq_z1, h_main⟩
  simpa [b, c, d] using h_unique

lemma round1_h1_ad7e4f (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (k : ZMod p)
  (hk1 : k ≠ 0)
  (hk2 : k ≠ -1):
  2 ≤ ((k⁻¹).val + 1) ∧ ((k⁻¹).val + 1) < p := by
  have h_y1 : (k⁻¹).val ≥ 1 := by
    by_contra h
    have h' : (k⁻¹).val = 0 := by omega
    have h₁ : (k⁻¹ : ZMod p) = 0 := by
      rw [← ZMod.natCast_zmod_val (k⁻¹)]
      simp [h']
    have h₂ : (k : ZMod p) * (k⁻¹) = 1 := by exact CommGroupWithZero.mul_inv_cancel k hk1
    rw [h₁] at h₂
    simp at h₂
  have h_y2 : (k⁻¹).val < p - 1 := by
    by_contra h
    have h' : (k⁻¹).val ≥ p - 1 := by omega
    have h₃ : (k⁻¹).val < p := ZMod.val_lt (k⁻¹)
    have h₄ : (k⁻¹).val = p - 1 := by omega
    have h₅₁ : (k⁻¹ : ZMod p) = ↑((k⁻¹).val) := by
      exact (ZMod.natCast_zmod_val (k⁻¹)).symm
    have h₅₂ : (↑((k⁻¹).val) : ZMod p) = (↑(p - 1 : ℕ) : ZMod p) := by
      rw [h₄]
    have h₅₃ : (↑(p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
      have h₅₄ : p > 0 := by linarith
      have h₅₅ : (↑(p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
        simp [h₅₄]
      exact h₅₅
    have h₅ : (k⁻¹ : ZMod p) = (-1 : ZMod p) := by
      rw [h₅₁, h₅₂, h₅₃]
    have h₆ : (k : ZMod p) * (k⁻¹) = 1 := by exact CommGroupWithZero.mul_inv_cancel k hk1
    rw [h₅] at h₆
    have h₇ : (k : ZMod p) * (-1 : ZMod p) = 1 := h₆
    have h₈ : -(k : ZMod p) = 1 := by
      simpa [mul_neg] using h₇
    have h₉ : (k : ZMod p) + 1 = 0 := by
      simpa [neg_eq_iff_add_eq_zero] using h₈
    have h₁₀ : (k : ZMod p) = -1 := by
      simpa [add_eq_zero_iff_eq_neg] using h₉
    exact hk2 h₁₀
  omega

lemma round1_h2_051c42 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1))
  (k : ZMod p)
  (hk1 : k ≠ 0)
  (hk2 : k ≠ -1)
  (hk3 : (k + 1)⁻¹.val < k⁻¹.val):
  let y := (k⁻¹).val + 1
  y + inv y > p + 2 := by
  let a := (k⁻¹).val
  have h_a1 : 1 ≤ a ∧ a < p := by
    have h1 : 2 ≤ a + 1 := (round1_h1_ad7e4f p hp3 inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv k hk1 hk2).1
    have h2 : a + 1 < p := (round1_h1_ad7e4f p hp3 inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv k hk1 hk2).2
    omega
  have h_main1 : 1 ≤ a ∧ a + 1 < p := by
    have h1 : 2 ≤ a + 1 := (round1_h1_ad7e4f p hp3 inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv k hk1 hk2).1
    have h2 : a + 1 < p := (round1_h1_ad7e4f p hp3 inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv k hk1 hk2).2
    exact ⟨by omega, h2⟩
  let x := inv a
  have h1 : 1 ≤ x := by
    have h_inv_a := h_inv a h_a1
    exact h_inv_a.1
  have h2 : x < p := by
    have h_inv_a := h_inv a h_a1
    exact h_inv_a.2.1
  have h_x_lt_p1 : x < p - 1 := by
    by_contra h
    have h₃ : x ≥ p - 1 := by omega
    have h₄ : x < p := h2
    have h₅ : x = p - 1 := by omega
    have h_eq_x : x = inv a := by rfl
    have h7 : ((a : ZMod p) )⁻¹.val = inv a := h_zmod_val_eq_inv a h_a1
    have h6 : inv a = ((k : ZMod p).val) := by
      simpa [a, ZMod.natCast_zmod_val] using h7.symm
    rw [h_eq_x] at h₅
    have h₇ : (k : ZMod p).val = p - 1 := by
      simpa [h6] using h₅
    have h₉ : ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
      simp [Nat.cast_sub (show 1 ≤ p by linarith)]
    have h10 : ((k : ZMod p).val : ZMod p) = (k : ZMod p) := by exact natCast_zmod_val k
    have h11 : (k : ZMod p) = ((k : ZMod p).val : ZMod p) := h10.symm
    have h12 : (k : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
      rw [h11, h₇]
    have h8 : (k : ZMod p) = -1 := by
      rw [h12, h₉]
    exact hk2 h8
  have h_x1' : 1 ≤ x ∧ x + 1 < p := by omega
  have h_eq1 : inv (x + 1) = p + 1 - inv (a + 1) := h_key_property a h_main1
  have h7 : ((a : ZMod p) )⁻¹.val = inv a := h_zmod_val_eq_inv a h_a1
  have h6 : inv a = ((k : ZMod p).val) := by
    simpa [a, ZMod.natCast_zmod_val] using h7.symm
  have h_x_eq_kval : x = (k : ZMod p).val := by
    simp [x, h6]
  have h9 : inv (x + 1) = (k + 1)⁻¹.val := by
    have h10 : 1 ≤ x + 1 ∧ x + 1 < p := by omega
    have h11 : inv (x + 1) = ((( (x + 1 : ℕ) : ZMod p ) )⁻¹).val := by
      exact (h_zmod_val_eq_inv (x + 1) h10).symm
    rw [h11]
    have h12 : ( (x + 1 : ℕ) : ZMod p ) = (k + 1 : ZMod p) := by
      rw [h_x_eq_kval]
      simp
    rw [h12]
  have h13 : (k + 1)⁻¹.val = p + 1 - inv (a + 1) := by
    have h14 : inv (x + 1) = (k + 1)⁻¹.val := h9
    have h15 : inv (x + 1) = p + 1 - inv (a + 1) := h_eq1
    rw [h14] at *
    tauto
  have h14 : (k + 1)⁻¹.val < a := hk3
  have h15 : p + 1 - inv (a + 1) < a := by
    linarith [h13, h14]
  have h16 : p + 1 < a + inv (a + 1) := by omega
  let y := a + 1
  have h17 : y + inv y = a + 1 + inv (a + 1) := by
    dsimp only [y]
  have h_goal : y + inv y > p + 2 := by
    rw [h17]
    omega
  exact h_goal

theorem round1_S_to_A_well_defined (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1)):
  let S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p));
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  let f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1;
  ∀ x ∈ S, f x ∈ A := by
  dsimp only
  intro k hk
  have h1 : k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val := by
    simpa [Finset.mem_filter] using hk
  have hk1 : k ≠ 0 := h1.1
  have hk2 : k ≠ -1 := h1.2.1
  have hk3 : (k + 1)⁻¹.val < k⁻¹.val := h1.2.2
  let y := (k⁻¹).val + 1
  have h4 : 2 ≤ y ∧ y < p := round1_h1_ad7e4f p hp3 inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv k hk1 hk2
  have h5 : y + inv y > p + 2 := round1_h2_051c42 p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property k hk1 hk2 hk3
  have h6 : y ∈ (Finset.Ico 2 p) := by
    exact Finset.mem_Ico.mpr ⟨h4.1, h4.2⟩
  have h7 : y ∈ (Finset.Ico 2 p).filter (fun x : ℕ => x + inv x > p + 2) := by
    exact Finset.mem_filter.mpr ⟨h6, h5⟩
  have h_main : ((k⁻¹).val + 1) ∈ (Finset.Ico 2 p).filter (fun x : ℕ => x + inv x > p + 2) := h7
  exact h_main

lemma round1_h141 (p a : ℕ)
  (hp : p > 1)
  (h1 : (a * (p - 1)) % p = 1)
  (ha : a < p):
  (p : ℕ) ∣ (a + 1) := by
  have h2 : (((a * (p - 1)) % p : ℕ) : ZMod p) = (1 : ZMod p) := by
    rw [h1] ; simp
  have h2' : (((a * (p - 1)) : ℕ) : ZMod p) = (((a * (p - 1)) % p : ℕ) : ZMod p) := by
    simp [ZMod.natCast_mod]
  have h2'' : (((a * (p - 1)) : ℕ) : ZMod p) = (1 : ZMod p) := by
    rw [h2'] ; exact h2
  have h3 : ( (p - 1 : ℕ) : ZMod p) = -1 := by
    have h4 : p > 0 := by linarith
    simp [Nat.cast_sub (show 1 ≤ p from by linarith)]
  have h5 : (((a * (p - 1) : ℕ) : ZMod p)) = ((a : ZMod p) * ((p - 1 : ℕ) : ZMod p)) := by
    norm_cast
  rw [h5] at h2''
  rw [h3] at h2''
  have h6 : (a : ZMod p) * (-1 : ZMod p) = (1 : ZMod p) := h2''
  have h7 : -( (a : ZMod p)) = (1 : ZMod p) := by simpa [mul_neg] using h6
  have h8 : (a : ZMod p) = -1 := by
    have h9 : (a : ZMod p) = - (1 : ZMod p) := by
      calc
        (a : ZMod p) = - (-(a : ZMod p)) := by ring
        _ = - (1 : ZMod p) := by rw [h7]
        _ = - (1 : ZMod p) := by rfl
    simpa using h9
  have h10 : ((a + 1 : ℕ) : ZMod p) = 0 := by
    simpa [add_comm] using show (a : ZMod p) + (1 : ZMod p) = 0 from by
      rw [h8] ; ring
  exact (ZMod.natCast_eq_zero_iff (a + 1) p).mp h10

theorem round1_A_to_S_well_defined (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1)):
  let S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p));
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  let g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹;
  ∀ y ∈ A, g y ∈ S := by
  dsimp only
  intro y hy
  have h_y_mem_Ico : y ∈ Finset.Ico 2 p := (Finset.mem_filter.mp hy).1
  have h_sum : y + inv y > p + 2 := (Finset.mem_filter.mp hy).2
  have h_y1 : 2 ≤ y := (Finset.mem_Ico.mp h_y_mem_Ico).1
  have h_y2 : y < p := (Finset.mem_Ico.mp h_y_mem_Ico).2
  have h_a_lt_p_minus_1 : y - 1 < p - 1 := by omega
  let a := y - 1
  have ha1 : 1 ≤ a := by omega
  have hap : a < p := by omega
  have ha2 : a + 1 = y := by omega
  have h_a_plus_one_lt_p : a + 1 < p := by omega
  let k : ZMod p := ((a : ℕ) : ZMod p)⁻¹
  have h_main_goal : inv (inv a + 1) < a := by
    have h4 : inv (inv a + 1) = p + 1 - inv (a + 1) := h_key_property a ⟨ha1, h_a_plus_one_lt_p⟩
    have h5 : (a + 1) + inv (a + 1) > p + 2 := by
      rw [show a + 1 = y from by omega] at *
      exact h_sum
    rw [h4]
    omega
  have h103 : (a : ZMod p) ≠ 0 := by
    intro h
    have h104 : (p : ℕ) ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h
    have h105 : a ≥ p := Nat.le_of_dvd (by omega) h104
    omega
  have h10 : k ≠ 0 := by
    intro h101
    have h102 : ((a : ZMod p)⁻¹) = (0 : ZMod p) := by simpa [k] using h101
    have h104 : (a : ZMod p) * ((a : ZMod p)⁻¹) = 1 := by field_simp [h103]
    have h105 : (a : ZMod p) * ((a : ZMod p)⁻¹) = (0 : ZMod p) := by
      rw [h102] ; ring
    rw [h104] at h105
    norm_num at h105
  have h11 : k ≠ -1 := by
    intro h111
    have h112 : (k : ZMod p) = -1 := h111
    have h113 : ((a : ZMod p)⁻¹) = (-1 : ZMod p) := by simpa [k] using h112
    have h114 : (a : ZMod p) * ((a : ZMod p)⁻¹) = 1 := by field_simp [h103]
    have h115 : (a : ZMod p) * ((a : ZMod p)⁻¹) = (a : ZMod p) * (-1 : ZMod p) := by rw [h113]
    have h116 : (a : ZMod p) * (-1 : ZMod p) = -(a : ZMod p) := by ring
    rw [h116] at h115
    have h117 : (1 : ZMod p) = -(a : ZMod p) := by
      rw [h114] at h115 ; simpa using h115
    have h118 : (a : ZMod p) = -1 := by
      have h119 : (1 : ZMod p) = - (a : ZMod p) := h117
      have h200 : (a : ZMod p) = -1 := by
        calc
          (a : ZMod p) = - (-(a : ZMod p)) := by ring
          _ = - (1 : ZMod p) := by rw [h119]
          _ = -1 := by ring
      exact h200
    have h119 : ((a + 1 : ℕ) : ZMod p) = 0 := by
      calc
        ((a + 1 : ℕ) : ZMod p)
          = (a : ZMod p) + (1 : ZMod p) := by
            norm_cast
        _ = (-1 : ZMod p) + (1 : ZMod p) := by rw [h118]
        _ = 0 := by ring
    have h120 : (p : ℕ) ∣ (a + 1) := (ZMod.natCast_eq_zero_iff (a + 1) p).mp h119
    have h121 : a + 1 < p := by omega
    have h122 : p ≤ a + 1 := Nat.le_of_dvd (by omega) h120
    omega
  have h13 : k⁻¹.val = a := by
    have h131 : k⁻¹ = (a : ZMod p) := by
      simp [k]
    rw [h131]
    have h132 : ((a : ZMod p)).val = a % p := by
      rw [ZMod.val_natCast]
    rw [h132]
    have h133 : a % p = a := by
      apply Nat.mod_eq_of_lt
      exact hap
    rw [h133]
  have h123 : 1 ≤ inv a ∧ inv a < p ∧ (a * inv a) % p = 1 := h_inv a ⟨ha1, hap⟩
  have h124 : inv a < p := h123.2.1
  have h125 : 1 ≤ inv a := h123.1
  have h126 : inv a + 1 < p := by
    by_contra h
    have h127 : inv a + 1 ≥ p := by omega
    have h128 : inv a + 1 = p := by omega
    have h129 : inv a = p - 1 := by omega
    have h130 : (a * inv a) % p = 1 := h123.2.2
    rw [h129] at h130
    have h140 : (p : ℕ) ∣ (a + 1) := round1_h141 p a (by linarith) h130 hap
    have h141 : a + 1 < p := by omega
    have h142 : p ≤ a + 1 := Nat.le_of_dvd (by omega) h140
    omega
  let x : ZMod p := k + 1
  have h_k_val : k.val = inv a := h_zmod_val_eq_inv a ⟨ha1, hap⟩
  have h140 : k.val + 1 < p := by
    rw [h_k_val] ; exact h126
  have h141 : x.val = k.val + 1 := by
    dsimp [x]
    have h1 : x.val = (k + (1 : ZMod p)).val := by rfl
    rw [h1]
    have h2 : (k + (1 : ZMod p)).val = (k.val + (1 : ZMod p).val) % p := by
      rw [ZMod.val_add]
    rw [h2]
    have h3 : (1 : ZMod p).val = 1 := by
      exact val_one p
    rw [h3]
    have h4 : (k.val + 1) % p = k.val + 1 := by
      apply Nat.mod_eq_of_lt
      exact h140
    rw [h4]
  have h142 : x.val = inv a + 1 := by
    rw [h141, h_k_val]
  have h144 : 1 ≤ x.val := by
    rw [h142] ; linarith
  have h145 : x.val < p := by
    rw [h142] ; exact h126
  have h146 : (x⁻¹).val = inv (x.val) := by
    have h147 : (x : ZMod p) = ((x.val : ℕ) : ZMod p) := by
      simp [x]
    rw [h147]
    simpa using h_zmod_val_eq_inv (x.val) ⟨h144, h145⟩
  have h147 : (k + 1)⁻¹.val = inv (inv a + 1) := by
    simpa [x, h142] using h146
  have h12 : (k + 1)⁻¹.val < k⁻¹.val := by
    rw [h147, h13]
    exact h_main_goal
  have h_final : k ∈ (Finset.univ : Finset (ZMod p)) := by simp
  exact Finset.mem_filter.mpr ⟨h_final, h10, h11, h12⟩

lemma round1_h_main_a709f3 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1)):
  ∀ (x : ZMod p), (let S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p));
    let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
    let f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1;
    let g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹;
    g (f x) = x) := by
  intro x
  dsimp only
  let y : ZMod p := x⁻¹
  have h1 : (( (x⁻¹).val + 1 - 1 : ℕ) : ZMod p) = (x⁻¹ : ZMod p) := by
    simp
  have h2 : ((( (x⁻¹).val + 1) - 1 : ℕ) : ZMod p) = (x⁻¹ : ZMod p) := by
    simp
  have h_main : ((( (x⁻¹).val + 1) - 1 : ℕ) : ZMod p)⁻¹ = x := by
    rw [h2]
    simp
  simp

theorem round1_g_f_is_identity_on_S (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1)):
  let S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p));
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  let f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1;
  let g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹;
  ∀ x ∈ S, g (f x) = x := by
  have h_main : ∀ (x : ZMod p),
    (let S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p));
      let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
      let f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1;
      let g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹;
      g (f x) = x) := by
    exact round1_h_main_a709f3 p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property
  dsimp only
  intro x hx
  exact h_main x

lemma round1_h_main_e1715a (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1))
  (y : ℕ)
  (hy1 : y ∈ (Finset.Ico 2 p)):
  let f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1
  let g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹
  f (g y) = y := by
  dsimp only
  have h₁ : 2 ≤ y := (Finset.mem_Ico.mp hy1).1
  have h₂ : y < p := (Finset.mem_Ico.mp hy1).2
  have h₃ : 1 ≤ y - 1 := by omega
  have h₄ : y - 1 < p := by omega
  let z : ZMod p := (y - 1 : ℕ)
  have hz_ne_zero : z ≠ 0 := by
    intro h
    have h₅ : ( (y - 1 : ℕ) : ZMod p ) = 0 := h
    have h₆ : (p : ℕ) ∣ (y - 1) := (ZMod.natCast_eq_zero_iff (y - 1) p).mp h₅
    have h₇ : y - 1 > 0 := by omega
    have h₉ : y - 1 < p := h₄
    have h₁₀ : ¬ (p : ℕ) ∣ (y - 1) := Nat.not_dvd_of_pos_of_lt h₇ h₉
    exact h₁₀ h₆
  let k : ZMod p := z⁻¹
  have h₅ : k⁻¹ = z := by
    have h₅₁ : k = z⁻¹ := rfl
    rw [h₅₁]
    field_simp [hz_ne_zero]
  have h₆ : (k⁻¹).val = z.val := by
    rw [h₅]
  have h₇₁ : (y - 1) % p = y - 1 := by
    apply Nat.mod_eq_of_lt
    exact h₄
  have h₇ : z.val = (y - 1) % p := by
    simp [z]
  have h₇₂ : z.val = y - 1 := by
    rw [h₇, h₇₁]
  have h₈ : (k⁻¹).val + 1 = y := by
    rw [h₆, h₇₂]
    omega
  exact h₈

theorem round1_f_g_is_identity_on_A (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2)
  (h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x)
  (h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a)
  (h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1)):
  let S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p));
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  let f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1;
  let g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹;
  ∀ y ∈ A, f (g y) = y := by
  dsimp only
  intro y hy
  have hy1 : y ∈ (Finset.Ico 2 p) := by
    exact (Finset.mem_filter.mp hy).1
  exact round1_h_main_e1715a p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property y hy1

lemma round1_h1_da72e1 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  ∀ (a b b' : ℕ), (1 ≤ a ∧ a < p) → (1 ≤ b ∧ b < p) → (1 ≤ b' ∧ b' < p) → (a * b) % p = 1 → (a * b') % p = 1 → b = b' := by
  intro a b b' ha hb hb' h1 h1'
  have h_eq1 : (a * (b * b')) % p = (b') % p := by
    calc
      (a * (b * b')) % p
        = ((a * b) * b') % p := by ring_nf
      _ = (((a * b) % p) * b') % p := by simp [Nat.mul_mod]
      _ = (1 * b') % p := by rw [h1]
      _ = (b') % p := by simp
  have h_eq2 : (a * (b * b')) % p = (b) % p := by
    calc
      (a * (b * b')) % p
        = (a * (b' * b)) % p := by ring_nf
      _ = (((a * b') * b) % p) := by ring_nf
      _ = (((a * b') % p) * b) % p := by simp [Nat.mul_mod]
      _ = (1 * b) % p := by rw [h1']
      _ = (b) % p := by simp
  have h_eq3 : (b') % p = (b) % p := by
    rw [←h_eq1, h_eq2]
  have h6 : b % p = b := by
    apply Nat.mod_eq_of_lt
    exact hb.2
  have h7 : b' % p = b' := by
    apply Nat.mod_eq_of_lt
    exact hb'.2
  have h_final : b' = b := by
    rw [h6, h7] at h_eq3
    exact h_eq3
  exact h_final.symm

lemma round1_h_mod (p a b : ℕ)
  (hp_pos : 0 < p)
  (h : (p : ℤ) ∣ (a : ℤ) - (b : ℤ)):
  a % p = b % p := by
  have h₁ : (p : ℤ) ∣ (a : ℤ) - (b : ℤ) := h
  have h₂ : (a : ℤ) ≡ (b : ℤ) [ZMOD (p : ℤ)] := by
    simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h₁
  have h₃ : (a % p : ℤ) = (b % p : ℤ) := by
    simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h₂
  have h₄ : a % p = b % p := by
    exact_mod_cast h₃
  exact h₄

lemma round1_h_mul (p u v : ℕ)
  (hp_pos : 0 < p)
  (hu : u < p)
  (hv : v < p):
  ((p - u) * (p - v)) % p = (u * v) % p := by
  have h₂ : ((p : ℤ) - (u : ℤ)) ≡ -((u : ℤ)) [ZMOD (p : ℤ)] := by
    simp [Int.ModEq]
  have h₃ : ((p : ℤ) - (v : ℤ)) ≡ -((v : ℤ)) [ZMOD (p : ℤ)] := by
    simp [Int.ModEq]
  have h₄ : (((p : ℤ) - (u : ℤ)) * ((p : ℤ) - (v : ℤ))) ≡ ((u : ℤ) * (v : ℤ)) [ZMOD (p : ℤ)] := by
    have h₅ : (((p : ℤ) - (u : ℤ)) * ((p : ℤ) - (v : ℤ))) ≡ ( (-(u : ℤ)) * (-(v : ℤ)) ) [ZMOD (p : ℤ)] := Int.ModEq.mul h₂ h₃
    have h₆ : ( (-(u : ℤ)) * (-(v : ℤ)) ) = ((u : ℤ) * (v : ℤ)) := by ring
    rw [h₆] at h₅
    exact h₅
  have h₇ : (p : ℤ) ∣ (((p : ℤ) - (u : ℤ)) * ((p : ℤ) - (v : ℤ))) - ((u : ℤ) * (v : ℤ)) := by
    exact Int.ModEq.dvd (id (Int.ModEq.symm h₄))
  have h₈ : (p : ℤ) ∣ (↑(((p - u) * (p - v)) : ℕ) - ↑(u * v : ℕ)) := by
    have h₉₁ : (↑(p - u) : ℤ) = (p : ℤ) - (u : ℤ) := by
      simp [Nat.cast_sub (by omega : u ≤ p)]
    have h₉₂ : (↑(p - v) : ℤ) = (p : ℤ) - (v : ℤ) := by
      simp [Nat.cast_sub (by omega : v ≤ p)]
    have h₉₃ : (↑(((p - u) * (p - v)) : ℕ) : ℤ) = (↑(p - u) : ℤ) * (↑(p - v) : ℤ) := by
      norm_cast
    have h₉₄ : (↑(((p - u) * (p - v)) : ℕ) : ℤ) = (((p : ℤ) - (u : ℤ)) * ((p : ℤ) - (v : ℤ))) := by
      rw [h₉₃, h₉₁, h₉₂]
    have h₁₀ : (↑(u * v : ℕ) : ℤ) = ((u : ℤ) * (v : ℤ)) := by norm_cast
    rw [h₉₄, h₁₀]
    exact h₇
  exact round1_h_mod p ((p - u) * (p - v)) (u * v) hp_pos h₈

lemma round1_h2_b605e5 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h1 : ∀ (a b b' : ℕ), (1 ≤ a ∧ a < p) → (1 ≤ b ∧ b < p) → (1 ≤ b' ∧ b' < p) → (a * b) % p = 1 → (a * b') % p = 1 → b = b'):
  ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (p - x) = p - inv x := by
  intro x hx
  have h_x1 : 1 ≤ x := hx.1
  have h_x2 : x < p := hx.2
  have h_inv_x1 : 1 ≤ inv x := (h_inv x hx).1
  have h_inv_x2 : inv x < p := (h_inv x hx).2.1
  have hp_pos : 0 < p := by linarith
  set a := p - x with ha_def
  set b := p - inv x with hb_def
  have ha : 1 ≤ a ∧ a < p := by omega
  have h_b : 1 ≤ b ∧ b < p := by omega
  have h_mul : (a * b) % p = 1 := by
    have h₁ : ((p - x) * (p - inv x)) % p = (x * inv x) % p := round1_h_mul p x (inv x) hp_pos h_x2 h_inv_x2
    have h₂ : (x * inv x) % p = 1 := (h_inv x hx).2.2
    rw [h₁, h₂]
  have h_inv_a : 1 ≤ inv a ∧ inv a < p ∧ (a * inv a) % p = 1 := h_inv a ha
  have h4 : (a * (inv a)) % p = 1 := h_inv_a.2.2
  have h6 : 1 ≤ inv a ∧ inv a < p := ⟨h_inv_a.1, h_inv_a.2.1⟩
  have h7 : inv a = b := h1 a (inv a) b ha h6 h_b h4 h_mul
  simpa [ha_def, hb_def] using h7

lemma round1_h_eq (p x y : ℕ)
  (h1 : x < p)
  (h2 : y < p):
  (p - x) + (p - y) = 2 * p - (x + y) := by
  have h3 : x ≤ p := by linarith
  have h4 : y ≤ p := by linarith
  have h5 : x + y < 2 * p := by linarith
  zify [h3, h4, h5] at *
  linarith

theorem round1_A_card_eq_B_card (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  let B : Finset ℕ := (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2);
  A.card = B.card := by
  have h1 : ∀ (a b b' : ℕ), (1 ≤ a ∧ a < p) → (1 ≤ b ∧ b < p) → (1 ≤ b' ∧ b' < p) → (a * b) % p = 1 → (a * b') % p = 1 → b = b' :=
    round1_h1_da72e1 p hp3 inv h_inv
  have h2 : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (p - x) = p - inv x := round1_h2_b605e5 p hp3 inv h_inv h1
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2)
  let B : Finset ℕ := (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2)
  have h3 : ∀ x ∈ A, p - x ∈ B := by
    intro x hx
    have hx1 : x ∈ Finset.Ico 2 p := (Finset.mem_filter.mp hx).1
    have hx2 : x + inv x > p + 2 := (Finset.mem_filter.mp hx).2
    have h_x1 : 2 ≤ x := (Finset.mem_Ico.mp hx1).1
    have h_x2 : x < p := (Finset.mem_Ico.mp hx1).2
    have h_inv_x1 : 1 ≤ inv x := (h_inv x ⟨by omega, h_x2⟩).1
    have h_inv_x2 : inv x < p := (h_inv x ⟨by omega, h_x2⟩).2.1
    have h4 : 1 ≤ p - x := by omega
    have h5 : p - x < p := by omega
    have h6 : p - x ∈ Finset.Ico 1 p := by
      exact Finset.mem_Ico.mpr ⟨h4, h5⟩
    have h7 : inv (p - x) = p - inv x := h2 x ⟨by omega, h_x2⟩
    have h_eq : (p - x) + (p - inv x) = 2 * p - (x + inv x) := round1_h_eq p x (inv x) h_x2 h_inv_x2
    have h8 : (p - x) + inv (p - x) < p - 2 := by
      rw [h7, h_eq]
      omega
    exact Finset.mem_filter.mpr ⟨h6, h8⟩
  have h4 : ∀ y ∈ B, p - y ∈ A := by
    intro y hy
    have hy1 : y ∈ Finset.Ico 1 p := (Finset.mem_filter.mp hy).1
    have hy2 : y + inv y < p - 2 := (Finset.mem_filter.mp hy).2
    have h_y1 : 1 ≤ y := (Finset.mem_Ico.mp hy1).1
    have h_y2 : y < p := (Finset.mem_Ico.mp hy1).2
    have h_inv_y1 : 1 ≤ inv y := (h_inv y ⟨h_y1, h_y2⟩).1
    have h_inv_y2 : inv y < p := (h_inv y ⟨h_y1, h_y2⟩).2.1
    have h9 : 2 ≤ p - y := by omega
    have h10 : p - y < p := by omega
    have h11 : p - y ∈ Finset.Ico 2 p := by
      exact Finset.mem_Ico.mpr ⟨h9, h10⟩
    have h12 : inv (p - y) = p - inv y := h2 y ⟨h_y1, h_y2⟩
    have h_eq : (p - y) + (p - inv y) = 2 * p - (y + inv y) := round1_h_eq p y (inv y) h_y2 h_inv_y2
    have h13 : (p - y) + inv (p - y) > p + 2 := by
      rw [h12, h_eq]
      omega
    exact Finset.mem_filter.mpr ⟨h11, h13⟩
  apply Finset.card_bij' (fun x _ => p - x)
    (fun y _ => p - y)
  <;> simp_all
  <;> aesop?
  <;> omega

lemma round1_h_disj1 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  Disjoint
    ((Finset.Ico 2 p).filter (fun x => x + inv x > p + 2))
    ((Finset.Ico 1 p).filter (fun x => x + inv x < p - 2)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 : x + inv x > p + 2 := (Finset.mem_filter.mp hx1).2
  have h2 : x + inv x < p - 2 := (Finset.mem_filter.mp hx2).2
  omega

lemma round1_h_disj2 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  Disjoint
    ((Finset.Ico 2 p).filter (fun x => x + inv x > p + 2))
    ((Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 : x + inv x > p + 2 := (Finset.mem_filter.mp hx1).2
  have h2 : x + inv x ≤ p + 2 := (Finset.mem_filter.mp hx2).2 |>.2
  omega

lemma round1_h_disj3 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  Disjoint
    ((Finset.Ico 1 p).filter (fun x => x + inv x < p - 2))
    ((Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 : x + inv x < p - 2 := (Finset.mem_filter.mp hx1).2
  have h2 : p - 2 ≤ x + inv x := (Finset.mem_filter.mp hx2).2 |>.1
  omega

lemma round1_h_main_62bb71 (p : ℕ)
  (x : ℕ)
  (inv : ℕ → ℕ)
  (h₁ : 1 ≤ x ∧ x < p)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (hp3 : 3 < p):
  ((2 ≤ x ∧ x < p) ∧ x + inv x > p + 2) ∨ ((1 ≤ x ∧ x < p) ∧ x + inv x < p - 2) ∨ ((1 ≤ x ∧ x < p) ∧ (p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)) := by
  have h5 : 1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1 := h_inv x h₁
  have h6 : 1 ≤ inv x := h5.1
  have h7 : inv x < p := h5.2.1
  have h9 : (x + inv x > p + 2) ∨ (x + inv x < p - 2) ∨ (p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2) := by omega
  rcases h9 with h9 | h9 | h9
  ·
    have h10 : x ≥ 2 := by
      by_contra h11
      have h12 : x < 2 := by omega
      have h13 : x = 1 := by omega
      have h_inv1 : 1 ≤ inv 1 ∧ inv 1 < p ∧ (1 * inv 1) % p = 1 := h_inv 1 ⟨by norm_num, by linarith⟩
      have h15 : (1 * inv 1) % p = 1 := h_inv1.2.2
      have h16 : inv 1 < p := h_inv1.2.1
      have h17 : (1 * inv 1) % p = (inv 1) % p := by simp
      rw [h17] at h15
      have h18 : (inv 1) % p = 1 := h15
      have h19 : inv 1 = 1 := by
        simp [Nat.mod_eq_of_lt h16] at h18 ; omega
      rw [h13, h19] at h9
      omega
    have h14 : 2 ≤ x ∧ x < p := by omega
    have hP1 : (2 ≤ x ∧ x < p) ∧ x + inv x > p + 2 := by
      exact ⟨h14, h9⟩
    tauto
  ·
    have hP2 : (1 ≤ x ∧ x < p) ∧ x + inv x < p - 2 := by
      exact ⟨h₁, h9⟩
    tauto
  ·
    have hP3 : (1 ≤ x ∧ x < p) ∧ (p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2) := by
      exact ⟨h₁, h9⟩
    tauto

lemma round1_h_union (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2)
  let B : Finset ℕ := (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2)
  let M : Finset ℕ := (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)
  A ∪ B ∪ M = Finset.Ico 1 p := by
  dsimp only
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
  constructor
  ·
    intro h
    rcases h with (h1 | h2)
    ·
      rcases h1 with (h1a | h1b)
      ·
        have h1a1 : 2 ≤ x ∧ x < p := h1a.1
        have h1a2 : 2 ≤ x := h1a1.1
        have h1a3 : x < p := h1a1.2
        have h1a4 : 1 ≤ x := by omega
        exact ⟨h1a4, h1a3⟩
      ·
        exact h1b.1
    ·
      exact h2.1
  ·
    intro h
    have h_main : ((2 ≤ x ∧ x < p) ∧ x + inv x > p + 2) ∨ ((1 ≤ x ∧ x < p) ∧ x + inv x < p - 2) ∨ ((1 ≤ x ∧ x < p) ∧ (p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)) :=
      round1_h_main_62bb71 p x inv h h_inv hp3
    rcases h_main with (h1 | h2 | h3)
    ·
      left
      left
      exact h1
    ·
      left
      right
      exact h2
    ·
      right
      exact h3

theorem round1_sum_of_cards (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  let B : Finset ℕ := (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2);
  let M : Finset ℕ := (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2);
  A.card + B.card + M.card = p - 1 := by
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2)
  let B : Finset ℕ := (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2)
  let M : Finset ℕ := (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)
  have h_disj1 : Disjoint A B := round1_h_disj1 p hp3 inv h_inv
  have h_disj2 : Disjoint A M := round1_h_disj2 p hp3 inv h_inv
  have h_disj3 : Disjoint B M := round1_h_disj3 p hp3 inv h_inv
  have h_union : A ∪ B ∪ M = Finset.Ico 1 p := round1_h_union p hp3 inv h_inv
  have h_disj4 : Disjoint (A ∪ B) M := by
    apply Finset.disjoint_union_left.mpr
    constructor
    · exact h_disj2
    · exact h_disj3
  have h1 : (A ∪ B ∪ M).card = (A ∪ B).card + M.card := by
    rw [Finset.card_union_of_disjoint h_disj4]
  have h2 : (A ∪ B).card = A.card + B.card := by
    rw [Finset.card_union_of_disjoint h_disj1]
  have h3 : (A ∪ B ∪ M).card = A.card + B.card + M.card := by
    rw [h1, h2]
  have h4 : (A ∪ B ∪ M).card = (Finset.Ico 1 p).card := by rw [h_union]
  have h5 : (Finset.Ico 1 p).card = p - 1 := by
    simp
  have h6 : A.card + B.card + M.card = p - 1 := by
    calc
      A.card + B.card + M.card = (A ∪ B ∪ M).card := by rw [h3]
      _ = (Finset.Ico 1 p).card := h4
      _ = p - 1 := h5
  exact h6

lemma round1_h_main_contradiction (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (x y : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p)
  (hy1 : 1 ≤ y)
  (hy2 : y < p)
  (h_sum : x + y = p + 2)
  (h_mod : (x * y) % p = 1):
  False := by
  let X : ℤ := (x : ℤ)
  let Y : ℤ := (y : ℤ)
  let P : ℤ := (p : ℤ)
  have h1 : 0 < p := by linarith [hp3]
  have hP_gt_one : 1 < P := by
    have h1' : 1 < p := by linarith [hp3]
    have h2 : (1 : ℤ) < (p : ℤ) := by exact_mod_cast h1'
    exact h2
  have hp_pos' : (0 : ℤ) < P := by linarith
  have hX2 : X < P := by
    have hX2' : x < p := hx2
    have h : (x : ℤ) < (p : ℤ) := by exact_mod_cast hX2'
    exact h
  have hY1 : (1 : ℤ) ≤ Y := by
    have hY1' : 1 ≤ y := hy1
    have h : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hY1'
    exact h
  have hY2 : Y < P := by
    have hY2' : y < p := hy2
    have h : (y : ℤ) < (p : ℤ) := by exact_mod_cast hY2'
    exact h
  have h_sum' : X + Y = P + 2 := by
    have h_sum' : x + y = p + 2 := h_sum
    have h : (x : ℤ) + (y : ℤ) = (p : ℤ) + 2 := by
      norm_cast
    exact h
  have h_div_thm : ∃ q : ℕ, x * y = p * q + (x * y) % p := by
    refine' ⟨(x * y) / p, _⟩
    rw [Nat.div_add_mod]
  have h_mod' : (x * y) % p = 1 := h_mod
  have h_exists : ∃ k : ℕ, x * y = p * k + 1 := by
    rcases h_div_thm with ⟨k, hk⟩
    refine' ⟨k, _⟩
    rw [h_mod'] at hk
    exact hk
  rcases h_exists with ⟨k, hk⟩
  have h_eq_nat : x * y = p * k + 1 := hk
  have h_eq_int : (X * Y) = P * (k : ℤ) + 1 := by
    have h1 : (X * Y) = ((x * y : ℕ) : ℤ) := by norm_cast
    rw [h1]
    norm_cast ; linarith
  have h_one_mod : (1 : ℤ) % P = 1 := by
    have hP_gt_one' : 1 < P := hP_gt_one
    rw [Int.emod_eq_of_lt] <;> omega
  have h_mod_int : (X * Y) % P = 1 := by
    rw [h_eq_int]
    simp [h_one_mod]
  have hdiv : (P : ℤ) ∣ (X * Y - 1) := by
    rw [h_eq_int]
    use (k : ℤ)
    ring
  have h_eq1 : X = P + 2 - Y := by linarith
  rw [h_eq1] at hdiv
  have h_h : ((P + 2 - Y) * Y - 1) = P * Y - (Y - 1)^2 := by
    ring
  rw [h_h] at hdiv
  have hdiv2 : (P : ℤ) ∣ (P * Y - (Y - 1)^2) := hdiv
  have hdiv3 : (P : ℤ) ∣ (Y - 1)^2 := by
    have h1 : (P : ℤ) ∣ (P * Y) := by
      use Y
    simpa [sub_eq_add_neg] using dvd_sub hdiv2 h1
  have hP_prime_nat : Nat.Prime p := Fact.out
  have hP_prime_int : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP_prime_nat
  have hdiv4 : (P : ℤ) ∣ (Y - 1) := by
    exact Prime.dvd_of_dvd_pow hP_prime_int hdiv3
  have h_Y_ge1 : 0 ≤ Y - 1 := by linarith
  have h_Y_lt_p : Y - 1 < P := by linarith
  have h_main : Y - 1 = 0 := by
    rcases hdiv4 with ⟨k, hk⟩
    have h_eq : Y - 1 = P * k := hk
    have h_k_nonneg : 0 ≤ k := by
      by_contra h
      have h' : k < 0 := by linarith
      have h_neg : P * k < 0 := by nlinarith
      linarith
    by_contra h_contra
    have h_k_pos : 0 < k := by
      by_contra h
      have h' : k = 0 := by linarith
      rw [h'] at h_eq
      linarith
    have h1 : k ≥ 1 := by linarith
    have h2 : P * k ≥ P := by nlinarith
    linarith
  have hY_eq1 : Y = 1 := by linarith
  have hX_eq : X = P + 1 := by linarith
  have h10 : X < P := hX2
  rw [hX_eq] at h10
  linarith

lemma round1_h_int_div_of_bounds (p : ℕ)
  (hp_pos : 0 < p)
  (a b : ℤ)
  (ha_nonneg : 0 ≤ a)
  (ha_lt : a < (p : ℤ))
  (hb_nonneg : 0 ≤ b)
  (hb_lt : b < (p : ℤ))
  (h : (p : ℤ) ∣ (a - b)):
  a - b = 0 := by
  rcases h with ⟨k, hk⟩
  have h1 : a - b = (p : ℤ) * k := by linarith
  have h2 : a - b < (p : ℤ) := by
    linarith
  have h3 : -((p : ℤ)) < a - b := by
    linarith
  have h4 : -((p : ℤ)) < (p : ℤ) * k := by rw [← h1] ; exact h3
  have h5 : (p : ℤ) * k < (p : ℤ) := by rw [← h1] ; exact h2
  have h6 : k > -1 := by nlinarith
  have h7 : k < 1 := by nlinarith
  have h8 : k = 0 := by omega
  rw [h8] at h1
  linarith

lemma round1_h_sum_eq_p (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (x1 x2 : ℕ)
  (hx1 : x1 < p)
  (hx2 : x2 < p)
  (hne : x1 ≠ x2)
  (h1 : (x1 ^ 2 + x1 + 1) % p = 0)
  (h2 : (x2 ^ 2 + x2 + 1) % p = 0):
  x1 + x2 + 1 = p := by
  have hP : Nat.Prime p := Fact.out
  have hP_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hP
  have h_p_pos : 0 < (p : ℤ) := by exact_mod_cast (show 0 < p from by linarith [hp3])
  have h1' : (p : ℤ) ∣ ((x1 ^ 2 + x1 + 1 : ℤ)) := by
    rw [Int.dvd_iff_emod_eq_zero]
    norm_cast
  have h2' : (p : ℤ) ∣ ((x2 ^ 2 + x2 + 1 : ℤ)) := by
    rw [Int.dvd_iff_emod_eq_zero]
    norm_cast
  have h3' : (p : ℤ) ∣ (((x1 : ℤ) ^ 2 + (x1 : ℤ) + 1) - ((x2 : ℤ) ^ 2 + (x2 : ℤ) + 1)) :=
    dvd_sub h1' h2'
  have h4' : (((x1 : ℤ) ^ 2 + (x1 : ℤ) + 1) - ((x2 : ℤ) ^ 2 + (x2 : ℤ) + 1)) = ((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ) + 1) := by
    ring
  rw [h4'] at h3'
  have h5' : (p : ℤ) ∣ ((x1 : ℤ) - (x2 : ℤ)) ∨ (p : ℤ) ∣ ((x1 : ℤ) + (x2 : ℤ) + 1) := hP_int.dvd_or_dvd h3'
  cases h5' with
  | inl h5'' =>
    have h6 : (x1 : ℤ) - (x2 : ℤ) = 0 := round1_h_int_div_of_bounds p (show 0 < p from by linarith [hp3]) (x1 : ℤ) (x2 : ℤ) (by positivity) (by exact_mod_cast hx1) (by positivity) (by exact_mod_cast hx2) h5''
    have h7 : (x1 : ℤ) = (x2 : ℤ) := by linarith
    have h8 : x1 = x2 := by exact_mod_cast h7
    exfalso
    exact hne h8
  | inr h5'' =>
    have h6 : 0 < (x1 + x2 + 1 : ℤ) := by positivity
    have h7 : (x1 + x2 + 1 : ℤ) < 2 * (p : ℤ) := by
      have h71 : (x1 : ℤ) < (p : ℤ) := by exact_mod_cast hx1
      have h72 : (x2 : ℤ) < (p : ℤ) := by exact_mod_cast hx2
      linarith
    have h8 : (p : ℤ) ∣ ((x1 + x2 + 1 : ℤ)) := by exact_mod_cast h5''
    rcases h8 with ⟨k, hk⟩
    have h9 : (x1 + x2 + 1 : ℤ) = (p : ℤ) * k := by linarith
    have h10 : 0 < k := by
      by_contra h10
      have h11 : k ≤ 0 := by linarith
      have h12 : (x1 + x2 + 1 : ℤ) ≤ 0 := by
        nlinarith [h_p_pos]
      linarith
    have h11 : k < 2 := by
      nlinarith [h_p_pos]
    have h12 : k = 1 := by omega
    rw [h12] at h9
    norm_cast at h9 ⊢ ; linarith

lemma round1_h_S1_at_most_two (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p):
  ∀ (x1 x2 x3 : ℕ), x1 < p → x2 < p → x3 < p → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
    (x1 ^ 2 + x1 + 1) % p = 0 → (x2 ^ 2 + x2 + 1) % p = 0 → (x3 ^ 2 + x3 + 1) % p = 0 → False := by
  intro x1 x2 x3 hx1 hx2 hx3 h12 h13 h23 h_eq1 h_eq2 h_eq3
  have h4 : x1 + x2 + 1 = p := round1_h_sum_eq_p p hp3 x1 x2 hx1 hx2 h12 h_eq1 h_eq2
  have h5 : x1 + x3 + 1 = p := round1_h_sum_eq_p p hp3 x1 x3 hx1 hx3 h13 h_eq1 h_eq3
  have h6 : x2 = x3 := by omega
  exact h23 h6

lemma round1_h_sum_eq_p2 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (x1 x2 : ℕ)
  (h_x1_pos : 1 ≤ x1)
  (hx1 : x1 < p)
  (h_x2_pos : 1 ≤ x2)
  (hx2 : x2 < p)
  (hne : x1 ≠ x2)
  (h1 : (x1 ^ 2 + 1) % p = 0)
  (h2 : (x2 ^ 2 + 1) % p = 0):
  x1 + x2 = p := by
  have hP : Nat.Prime p := Fact.out
  have hP_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hP
  have h_p_pos : 0 < (p : ℤ) := by exact_mod_cast (show 0 < p from by linarith [hp3])
  have h1' : (p : ℤ) ∣ ((x1 ^ 2 + 1 : ℤ)) := by
    rw [Int.dvd_iff_emod_eq_zero]
    norm_cast
  have h2' : (p : ℤ) ∣ ((x2 ^ 2 + 1 : ℤ)) := by
    rw [Int.dvd_iff_emod_eq_zero]
    norm_cast
  have h3' : (p : ℤ) ∣ (((x1 : ℤ) ^ 2 + 1) - ((x2 : ℤ) ^ 2 + 1)) := dvd_sub h1' h2'
  have h4' : (((x1 : ℤ) ^ 2 + 1) - ((x2 : ℤ) ^ 2 + 1)) = ((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ)) := by
    ring
  rw [h4'] at h3'
  have h5' : (p : ℤ) ∣ ((x1 : ℤ) - (x2 : ℤ)) ∨ (p : ℤ) ∣ ((x1 : ℤ) + (x2 : ℤ)) := hP_int.dvd_or_dvd h3'
  cases h5' with
  | inl h5'' =>
    have h6 : (x1 : ℤ) - (x2 : ℤ) = 0 := round1_h_int_div_of_bounds p (show 0 < p from by linarith [hp3]) (x1 : ℤ) (x2 : ℤ) (by positivity) (by exact_mod_cast hx1) (by positivity) (by exact_mod_cast hx2) h5''
    have h7 : (x1 : ℤ) = (x2 : ℤ) := by linarith
    have h8 : x1 = x2 := by exact_mod_cast h7
    exfalso
    exact hne h8
  | inr h5'' =>
    have h6 : 0 < (x1 + x2 : ℤ) := by
      have h61 : 1 ≤ x1 := h_x1_pos
      have h62 : 1 ≤ x2 := h_x2_pos
      omega
    have h7 : (x1 + x2 : ℤ) < 2 * (p : ℤ) := by
      have h71 : (x1 : ℤ) < (p : ℤ) := by exact_mod_cast hx1
      have h72 : (x2 : ℤ) < (p : ℤ) := by exact_mod_cast hx2
      linarith
    have h8 : (p : ℤ) ∣ ((x1 + x2 : ℤ)) := by exact_mod_cast h5''
    rcases h8 with ⟨k, hk⟩
    have h9 : (x1 + x2 : ℤ) = (p : ℤ) * k := by linarith
    have h10 : 0 < k := by
      by_contra h10
      have h11 : k ≤ 0 := by linarith
      have h12 : (x1 + x2 : ℤ) ≤ 0 := by nlinarith [h_p_pos]
      linarith
    have h11 : k < 2 := by
      nlinarith [h_p_pos]
    have h12 : k = 1 := by omega
    rw [h12] at h9
    norm_cast at h9 ⊢ ; linarith

lemma round2_h_main_step (p : ℕ)
  (hp3 : 3 < p)
  (x y : ℕ)
  (h1 : x + y = p - 2)
  (h2 : (x * y) % p = 1):
  (p : ℤ) ∣ ((x : ℤ) + 1)^2 := by
  have hp_pos : 0 < p := by linarith
  let n := (x * y) / p
  have hq : x * y = p * n + ((x * y) % p) := by
    exact Eq.symm (Nat.div_add_mod (x * y) p)
  have h2' : (x * y) % p = 1 := h2
  have h_eq : x * y = p * n + 1 := by
    rw [h2'] at hq
    simpa using hq
  have h_eq_comm : x * y = n * p + 1 := by
    have h₁ : p * n = n * p := by ring
    rw [h₁] at h_eq
    exact h_eq
  have h_eq1 : (x : ℤ) + (y : ℤ) = (p : ℤ) - 2 := by
    have h' : (x : ℤ) + (y : ℤ) = ((p : ℤ) - 2) := by
      omega
    exact h'
  have h_eq2 : (y : ℤ) = (p : ℤ) - 2 - (x : ℤ) := by
    linarith
  have h4 : ((x : ℤ) * (y : ℤ)) = ((n : ℤ) * (p : ℤ) + 1) := by
    exact_mod_cast h_eq_comm
  have h3 : ((x : ℤ) * (y : ℤ)) = (x : ℤ) * (p : ℤ) - 2 * (x : ℤ) - (x : ℤ)^2 := by
    rw [h_eq2] ; ring
  have h5 : (x : ℤ)^2 + 2 * (x : ℤ) + 1 = (p : ℤ) * ((x : ℤ) - (n : ℤ)) := by
    linarith [h3, h4]
  have h6 : (p : ℤ) ∣ ((x : ℤ)^2 + 2 * (x : ℤ) + 1) := by
    use ((x : ℤ) - (n : ℤ))
  have h7 : ((x : ℤ)^2 + 2 * (x : ℤ) + 1) = ((x : ℤ) + 1)^2 := by ring
  rw [h7] at h6
  exact h6

lemma round2_h_A_empty (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p):
  x + inv x ≠ p - 2 := by
  intro h_eq
  let y := inv x
  have hy1 : 1 ≤ y := (h_inv x ⟨hx1, hx2⟩).1
  have hy2 : y < p := (h_inv x ⟨hx1, hx2⟩).2.1
  have hxy : (x * y) % p = 1 := (h_inv x ⟨hx1, hx2⟩).2.2
  have h_main : (p : ℤ) ∣ ((x : ℤ) + 1)^2 := round2_h_main_step p hp3 x y h_eq hxy
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have h4 : (p : ℤ) ∣ ((x : ℤ) + 1) := by
    apply hP.dvd_of_dvd_pow h_main
  have h6 : 2 ≤ (x : ℤ) + 1 := by linarith [show (1 : ℤ) ≤ (x : ℤ) from by exact_mod_cast hx1]
  have h7 : (x : ℤ) + 1 < (p : ℤ) + 1 := by linarith [show (x : ℤ) < (p : ℤ) from by exact_mod_cast hx2]
  rcases h4 with ⟨k, hk⟩
  have h9 : k = 1 := by
    have h_p_pos' : (0 : ℤ) < (p : ℤ) := by exact_mod_cast (show 0 < p from by linarith)
    nlinarith
  have h10 : (x : ℤ) + 1 = (p : ℤ) := by
    rw [h9] at hk ; linarith
  have h11 : x + 1 = p := by
    norm_cast at h10 ⊢
  have h12 : x = p - 1 := by omega
  rw [h12] at h_eq
  omega

lemma round2_h1 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p)
  (h_eq : x + inv x = p - 1):
  (x ^ 2 + x + 1) % p = 0 := by
  let y := inv x
  have hy1 : 1 ≤ y := (h_inv x ⟨hx1, hx2⟩).1
  have hy2 : y < p := (h_inv x ⟨hx1, hx2⟩).2.1
  have hxy : (x * y) % p = 1 := (h_inv x ⟨hx1, hx2⟩).2.2
  let n := (x * y) / p
  have hq : x * y = p * n + ((x * y) % p) := by exact Eq.symm (Nat.div_add_mod (x * y) p)
  have h2' : (x * y) % p = 1 := hxy
  have h_eq_comm : x * y = n * p + 1 := by
    have h₁ : x * y = p * n + 1 := by
      rw [h2'] at hq ; simpa using hq
    have h₂ : p * n = n * p := by ring
    rw [h₂] at h₁
    exact h₁
  have h_eq1 : (x : ℤ) + (y : ℤ) = (p : ℤ) - 1 := by
    have h' : (x : ℤ) + (y : ℤ) = ((p : ℤ) - 1) := by
      omega
    exact h'
  have h_eq2 : (y : ℤ) = (p : ℤ) - 1 - (x : ℤ) := by linarith
  have h4 : ((x : ℤ) * (y : ℤ)) = ((n : ℤ) * (p : ℤ) + 1) := by exact_mod_cast h_eq_comm
  have h3 : ((x : ℤ) * (y : ℤ)) = (x : ℤ) * (p : ℤ) - (x : ℤ) - (x : ℤ)^2 := by
    rw [h_eq2] ; ring
  have h5 : (x : ℤ)^2 + (x : ℤ) + 1 = (p : ℤ) * ((x : ℤ) - (n : ℤ)) := by linarith [h3, h4]
  have h6 : (p : ℤ) ∣ ((x : ℤ)^2 + (x : ℤ) + 1) := by
    use ((x : ℤ) - (n : ℤ))
  norm_cast at h6 ⊢
  omega

lemma round2_h2 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p)
  (h_eq : x + inv x = p):
  (x ^ 2 + 1) % p = 0 := by
  let y := inv x
  have hy1 : 1 ≤ y := (h_inv x ⟨hx1, hx2⟩).1
  have hy2 : y < p := (h_inv x ⟨hx1, hx2⟩).2.1
  have hxy : (x * y) % p = 1 := (h_inv x ⟨hx1, hx2⟩).2.2
  let n := (x * y) / p
  have hq : x * y = p * n + ((x * y) % p) := by exact Eq.symm (Nat.div_add_mod (x * y) p)
  have h2' : (x * y) % p = 1 := hxy
  have h_eq_comm : x * y = n * p + 1 := by
    have h₁ : x * y = p * n + 1 := by
      rw [h2'] at hq ; simpa using hq
    have h₂ : p * n = n * p := by ring
    rw [h₂] at h₁
    exact h₁
  have h_eq1 : (x : ℤ) + (y : ℤ) = (p : ℤ) := by
    have h' : (x : ℤ) + (y : ℤ) = (p : ℤ) := by
      omega
    exact h'
  have h_eq2 : (y : ℤ) = (p : ℤ) - (x : ℤ) := by linarith
  have h4 : ((x : ℤ) * (y : ℤ)) = ((n : ℤ) * (p : ℤ) + 1) := by exact_mod_cast h_eq_comm
  have h3 : ((x : ℤ) * (y : ℤ)) = (x : ℤ) * (p : ℤ) - (x : ℤ)^2 := by
    rw [h_eq2] ; ring
  have h5 : (x : ℤ)^2 + 1 = (p : ℤ) * ((x : ℤ) - (n : ℤ)) := by linarith [h3, h4]
  have h6 : (p : ℤ) ∣ ((x : ℤ)^2 + 1) := by
    use ((x : ℤ) - (n : ℤ))
  norm_cast at h6 ⊢
  omega

lemma round2_h3 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (x : ℕ)
  (hx1 : 1 ≤ x)
  (hx2 : x < p)
  (h_eq : x + inv x = p + 1):
  (x ^ 2 - x + 1) % p = 0 := by
  have h_x2_ge_x : x ^ 2 ≥ x := by nlinarith
  let x' : ℕ := x ^ 2 - x
  let z : ℕ := x' + 1
  have h_z1 : (z : ℤ) = (x : ℤ)^2 - (x : ℤ) + 1 := by
    simp [z, x', Nat.cast_add, Nat.cast_sub (by nlinarith : x ≤ x ^ 2)]
  let y := inv x
  have hy1 : 1 ≤ y := (h_inv x ⟨hx1, hx2⟩).1
  have hy2 : y < p := (h_inv x ⟨hx1, hx2⟩).2.1
  have hxy : (x * y) % p = 1 := (h_inv x ⟨hx1, hx2⟩).2.2
  let n := (x * y) / p
  have hq : x * y = p * n + ((x * y) % p) := by exact Eq.symm (Nat.div_add_mod (x * y) p)
  have h2' : (x * y) % p = 1 := hxy
  have h_eq_comm : x * y = n * p + 1 := by
    have h₁ : x * y = p * n + 1 := by
      rw [h2'] at hq ; simpa using hq
    have h₂ : p * n = n * p := by ring
    rw [h₂] at h₁
    exact h₁
  have h_eq1 : (x : ℤ) + (y : ℤ) = (p : ℤ) + 1 := by
    have h' : (x : ℤ) + (y : ℤ) = (p : ℤ) + 1 := by
      omega
    exact h'
  have h_eq2 : (y : ℤ) = (p : ℤ) + 1 - (x : ℤ) := by linarith
  have h4 : ((x : ℤ) * (y : ℤ)) = ((n : ℤ) * (p : ℤ) + 1) := by exact_mod_cast h_eq_comm
  have h3 : ((x : ℤ) * (y : ℤ)) = (x : ℤ) * (p : ℤ) + (x : ℤ) - (x : ℤ)^2 := by
    rw [h_eq2] ; ring
  have h5 : (x : ℤ)^2 - (x : ℤ) + 1 = (p : ℤ) * ((x : ℤ) - (n : ℤ)) := by linarith [h3, h4]
  have h6 : (x : ℤ)^2 - (x : ℤ) + 1 = (p : ℤ) * ((x : ℤ) - (n : ℤ)) := h5
  have h_p_pos : (p : ℤ) > 0 := by exact_mod_cast (show 0 < p from by linarith)
  let m : ℤ := (x : ℤ) - (n : ℤ)
  have h7 : (x : ℤ)^2 - (x : ℤ) + 1 = (p : ℤ) * m := h6
  have h_pos : (x : ℤ)^2 - (x : ℤ) + 1 > 0 := by
    have h8 : (x : ℤ) ≥ 1 := by exact_mod_cast hx1
    nlinarith
  have h_m_pos : m > 0 := by
    have h : (p : ℤ) * m = (x : ℤ)^2 - (x : ℤ) + 1 := h7.symm
    have h' : (p : ℤ) * m > 0 := by linarith
    nlinarith
  have h_exists_k : ∃ (k : ℕ), (m : ℤ) = (k : ℤ) := by
    refine' ⟨m.toNat, _⟩
    simp [Int.toNat_of_nonneg (show 0 ≤ m by linarith)]
  rcases h_exists_k with ⟨k, hk⟩
  have h_eq_nat : (z : ℤ) = (p : ℤ) * (k : ℤ) := by
    rw [h_z1, h7, hk]
  have h_final : z = p * k := by
    apply Int.ofNat.inj
    simpa using h_eq_nat
  have h_goal : z % p = 0 := by
    rw [h_final]
    simp
  have h_main : (x ^ 2 - x + 1) = z := by
    simp [z, x']
  rw [h_main] at *
  exact h_goal

lemma round2_h_card_le_two' (U : Finset ℕ)
  (P : ℕ → Prop)
  (h : ∀ (x1 x2 x3 : ℕ), x1 ∈ U → x2 ∈ U → x3 ∈ U → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 → P x1 → P x2 → P x3 → False):
  (Finset.filter P U).card ≤ 2 := by
  let s := Finset.filter P U
  by_contra h'
  have h₁ : 2 < s.card := by
    by_contra h₂
    have h₃ : s.card ≤ 2 := by linarith
    exact h' h₃
  have h₂ : 3 ≤ s.card := by linarith
  have h3 : ∃ (x1 x2 x3 : ℕ), x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 := by
    exact two_lt_card_iff.mp h₁
  rcases h3 with ⟨x1, x2, x3, hx1, hx2, hx3, hne12, hne13, hne23⟩
  have hx1U : x1 ∈ U := (Finset.mem_filter.mp hx1).1
  have hP1 : P x1 := (Finset.mem_filter.mp hx1).2
  have hx2U : x2 ∈ U := (Finset.mem_filter.mp hx2).1
  have hP2 : P x2 := (Finset.mem_filter.mp hx2).2
  have hx3U : x3 ∈ U := (Finset.mem_filter.mp hx3).1
  have hP3 : P x3 := (Finset.mem_filter.mp hx3).2
  exact h x1 x2 x3 hx1U hx2U hx3U hne12 hne13 hne23 hP1 hP2 hP3

lemma round2_h_card_bound2 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p):
  (Finset.filter (fun x : ℕ ↦ (x ^ 2 + 1) % p = 0) (Finset.Ico 1 p)).card ≤ 2 := by
  let s := Finset.filter (fun x : ℕ ↦ (x ^ 2 + 1) % p = 0) (Finset.Ico 1 p)
  by_contra h
  have h₁ : 2 < s.card := by
    by_contra h₂
    have h₃ : s.card ≤ 2 := by linarith
    exact h h₃
  have h2 : ∃ (x1 x2 x3 : ℕ), x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 := by
    exact two_lt_card_iff.mp h₁
  rcases h2 with ⟨x1, x2, x3, hx1, hx2, hx3, hne12, hne13, hne23⟩
  have hx1U : x1 ∈ Finset.Ico 1 p := (Finset.mem_filter.mp hx1).1
  have hP1 : (x1 ^ 2 + 1) % p = 0 := (Finset.mem_filter.mp hx1).2
  have hx2U : x2 ∈ Finset.Ico 1 p := (Finset.mem_filter.mp hx2).1
  have hP2 : (x2 ^ 2 + 1) % p = 0 := (Finset.mem_filter.mp hx2).2
  have hx3U : x3 ∈ Finset.Ico 1 p := (Finset.mem_filter.mp hx3).1
  have hP3 : (x3 ^ 2 + 1) % p = 0 := (Finset.mem_filter.mp hx3).2
  have h11 : 1 ≤ x1 := (Finset.mem_Ico.mp hx1U).1
  have h12 : x1 < p := (Finset.mem_Ico.mp hx1U).2
  have h21 : 1 ≤ x2 := (Finset.mem_Ico.mp hx2U).1
  have h22 : x2 < p := (Finset.mem_Ico.mp hx2U).2
  have h31 : 1 ≤ x3 := (Finset.mem_Ico.mp hx3U).1
  have h32 : x3 < p := (Finset.mem_Ico.mp hx3U).2
  have h_eq1 : x1 + x2 = p := round1_h_sum_eq_p2 p hp3 x1 x2 h11 h12 h21 h22 hne12 hP1 hP2
  have h_eq2 : x1 + x3 = p := round1_h_sum_eq_p2 p hp3 x1 x3 h11 h12 h31 h32 hne13 hP1 hP3
  have h_contra : x2 = x3 := by omega
  exact hne23 h_contra

lemma algebra_identity (p x : ℤ):
  (p - x)^2 + (p - x) + 1 - (x^2 - x + 1) = p * (p - 2 * x + 1) := by
  ring

lemma round2_h_mod_lemma (p x : ℕ)
  (hp : 0 < p)
  (hx1 : 1 ≤ x)
  (hx2 : x < p):
  ((p - x)^2 + (p - x) + 1) % p = (x ^ 2 - x + 1) % p := by
  let px : ℤ := (p : ℤ)
  let hx : ℤ := (x : ℤ)
  let y : ℤ := px - hx
  let A : ℕ := (p - x)^2 + (p - x) + 1
  let B : ℕ := x ^ 2 - x + 1
  have h_x2_ge_x : x ^ 2 ≥ x := by nlinarith
  have h1 : (A : ℤ) = y ^ 2 + y + 1 := by
    simp [A, y, px, hx, Nat.cast_sub (show x ≤ p from by omega)]
  have h2 : (B : ℤ) = hx ^ 2 - hx + 1 := by
    have h_x2_ge_x' : x ^ 2 ≥ x := h_x2_ge_x
    have h_cast : ((x ^ 2 - x : ℕ) : ℤ) = (hx ^ 2) - hx := by
      rw [Nat.cast_sub h_x2_ge_x']
      simp [hx, pow_two]
    have hB_eq : B = (x ^ 2 - x) + 1 := by omega
    rw [hB_eq]
    simp [h_cast]
  have h3 : (A : ℤ) - (B : ℤ) = px * (px - 2 * hx + 1) := by
    rw [h1, h2]
    exact algebra_identity px hx
  have h4 : px ∣ ((A : ℤ) - (B : ℤ)) := by
    rw [h3]
    exact dvd_mul_right px _
  have h5 : (A : ℤ) ≡ (B : ℤ) [ZMOD px] := by
    simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h4
  have h6 : (A : ℤ) % px = (B : ℤ) % px := by
    exact h5
  have h7 : (A % p : ℤ) = ((A : ℤ) % px) := by
    simp [px]
  have h8 : (B % p : ℤ) = ((B : ℤ) % px) := by
    simp [px]
  have h9 : (A % p : ℤ) = (B % p : ℤ) := by
    rw [h7, h8, h6]
  have h10 : A % p = B % p := by
    exact_mod_cast h9
  exact h10

lemma round2_h_card_bound3 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p):
  (Finset.filter (fun x : ℕ ↦ (x ^ 2 - x + 1) % p = 0) (Finset.Ico 1 p)).card ≤ 2 := by
  let s := Finset.filter (fun x : ℕ ↦ (x ^ 2 - x + 1) % p = 0) (Finset.Ico 1 p)
  let U := (Finset.Ico 1 p)
  let P' : ℕ → Prop := fun x ↦ (x ^ 2 + x + 1) % p = 0
  have h_dec' : ∀ (x : ℕ), Decidable (P' x) := by
    intro x
    simp only [P'] ; infer_instance
  let h_dec_pred : DecidablePred P' := by
    exact fun x => h_dec' x
  have h_prop : ∀ (x1 x2 x3 : ℕ), x1 ∈ U → x2 ∈ U → x3 ∈ U → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 → P' x1 → P' x2 → P' x3 → False := by
    intro x1 x2 x3 hx1 hx2 hx3 hne12 hne13 hne23 h1 h2 h3
    exact round1_h_S1_at_most_two p hp3 x1 x2 x3 (Finset.mem_Ico.mp hx1).2 (Finset.mem_Ico.mp hx2).2 (Finset.mem_Ico.mp hx3).2 hne12 hne13 hne23 h1 h2 h3
  let t1 : Finset ℕ := Finset.filter P' U
  let t2 : Finset ℕ := @Finset.filter ℕ P' (fun (_ : ℕ) => propDecidable (P' _)) U
  have h_eq : t1 = t2 := by
    ext x
    simp [t1, t2]
  have h_main2 : t2.card ≤ 2 := by
    have h := round2_h_card_le_two' U P' h_prop
    simpa using h
  have h_main : t1.card ≤ 2 := by
    rw [h_eq]
    exact h_main2
  have h1 : ∀ x ∈ s, (p - x) ∈ t1 := by
    intro x hx
    have hx_ico : x ∈ Finset.Ico 1 p := (Finset.mem_filter.mp hx).1
    have h_eq : (x ^ 2 - x + 1) % p = 0 := (Finset.mem_filter.mp hx).2
    have h11 : 1 ≤ x := (Finset.mem_Ico.mp hx_ico).1
    have h12 : x < p := (Finset.mem_Ico.mp hx_ico).2
    have h21 : 1 ≤ p - x := by omega
    have h22 : p - x < p := by omega
    have h3 : ((p - x) ^ 2 + (p - x) + 1) % p = 0 := by
      have h4 := round2_h_mod_lemma p x (show 0 < p from by omega) h11 h12
      rw [h4, h_eq]
    exact Finset.mem_filter.mpr ⟨show (p - x) ∈ Finset.Ico 1 p from by simp [h21, h22], h3⟩
  have h_inj : Set.InjOn (fun x : ℕ ↦ p - x) s := by
    intro x1 hx1 x2 hx2 h_eq
    have h13 : p - x1 = p - x2 := h_eq
    have h_x1_lt_p : x1 < p := (Finset.mem_Ico.mp ((Finset.mem_filter.mp hx1).1)).2
    have h_x2_lt_p : x2 < p := (Finset.mem_Ico.mp ((Finset.mem_filter.mp hx2).1)).2
    have h_x1_le_p : x1 ≤ p := by omega
    have h_x2_le_p : x2 ≤ p := by omega
    have h14 : x1 = x2 := by omega
    exact h14
  have h_card : s.card ≤ t1.card := by
    apply Finset.card_le_card_of_injOn (f := fun x ↦ p - x) h1 h_inj
  exact le_trans h_card h_main

theorem round1_M_card_le_6 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  let M : Finset ℕ := (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2);
  M.card ≤ 6 := by
  set S1 := (Finset.Ico 1 p).filter (fun x ↦ x + inv x = p - 2) with hS1
  set S2 := (Finset.Ico 1 p).filter (fun x ↦ x + inv x = p - 1) with hS2
  set S3 := (Finset.Ico 1 p).filter (fun x ↦ x + inv x = p) with hS3
  set S4 := (Finset.Ico 1 p).filter (fun x ↦ x + inv x = p + 1) with hS4
  let M : Finset ℕ := (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2)
  have h_main_contra : ∀ (x : ℕ), x ∈ Finset.Ico 1 p → x + inv x ≠ p + 2 := by
    intro x hx
    have hx1 : 1 ≤ x := (Finset.mem_Ico.mp hx).1
    have hx2 : x < p := (Finset.mem_Ico.mp hx).2
    have hy1 : 1 ≤ inv x := (h_inv x ⟨hx1, hx2⟩).1
    have hy2 : inv x < p := (h_inv x ⟨hx1, hx2⟩).2.1
    have hmod : (x * inv x) % p = 1 := (h_inv x ⟨hx1, hx2⟩).2.2
    intro h_eq
    exact round1_h_main_contradiction p hp3 x (inv x) hx1 hx2 hy1 hy2 h_eq hmod
  have h_S1_empty : S1 = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx
    have hx1 : 1 ≤ x := (Finset.mem_Ico.mp hx).1
    have hx2 : x < p := (Finset.mem_Ico.mp hx).2
    exact round2_h_A_empty p hp3 inv h_inv x hx1 hx2
  have h_S2_card : S2.card ≤ 2 := by
    let U := (Finset.Ico 1 p)
    let P' : ℕ → Prop := fun x ↦ (x ^ 2 + x + 1) % p = 0
    let t1 : Finset ℕ := Finset.filter P' U
    have h_main : t1.card ≤ 2 := by
      let t2 : Finset ℕ := @Finset.filter ℕ P' (fun (_ : ℕ) => propDecidable (P' _)) U
      have h_eq : t1 = t2 := by
        ext x
        simp [t1, t2]
      have h_main2 : t2.card ≤ 2 := by
        have h := round2_h_card_le_two' U P' (by
          intro x1 x2 x3 hx1 hx2 hx3 hne12 hne13 hne23 h1 h2 h3
          exact round1_h_S1_at_most_two p hp3 x1 x2 x3 (Finset.mem_Ico.mp hx1).2 (Finset.mem_Ico.mp hx2).2 (Finset.mem_Ico.mp hx3).2 hne12 hne13 hne23 h1 h2 h3)
        simpa using h
      rw [h_eq]
      exact h_main2
    have h_main_sub : S2 ⊆ t1 := by
      intro y hy
      have h2 : y + inv y = p - 1 := (Finset.mem_filter.mp hy).2
      have h3 : (y ^ 2 + y + 1) % p = 0 := round2_h1 p hp3 inv h_inv y
        ((Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).1)
        ((Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).2) h2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, h3⟩
    have h4 : S2.card ≤ t1.card := Finset.card_le_card h_main_sub
    exact le_trans h4 h_main
  have h_S3_card : S3.card ≤ 2 := by
    have h_main : S3 ⊆ Finset.filter (fun x : ℕ ↦ (x ^ 2 + 1) % p = 0) (Finset.Ico 1 p) := by
      intro y hy
      have h2 : y + inv y = p := (Finset.mem_filter.mp hy).2
      have h3 : (y ^ 2 + 1) % p = 0 := round2_h2 p hp3 inv h_inv y
        ((Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).1)
        ((Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).2) h2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, h3⟩
    have h4 : S3.card ≤ (Finset.filter (fun x : ℕ ↦ (x ^ 2 + 1) % p = 0) (Finset.Ico 1 p)).card := Finset.card_le_card h_main
    have h5 : (Finset.filter (fun x : ℕ ↦ (x ^ 2 + 1) % p = 0) (Finset.Ico 1 p)).card ≤ 2 := round2_h_card_bound2 p hp3
    exact le_trans h4 h5
  have h_S4_card : S4.card ≤ 2 := by
    have h_main : S4 ⊆ Finset.filter (fun x : ℕ ↦ (x ^ 2 - x + 1) % p = 0) (Finset.Ico 1 p) := by
      intro y hy
      have h2 : y + inv y = p + 1 := (Finset.mem_filter.mp hy).2
      have h3 : (y ^ 2 - y + 1) % p = 0 := round2_h3 p hp3 inv h_inv y
        ((Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).1)
        ((Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).2) h2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, h3⟩
    have h4 : S4.card ≤ (Finset.filter (fun x : ℕ ↦ (x ^ 2 - x + 1) % p = 0) (Finset.Ico 1 p)).card := Finset.card_le_card h_main
    have h5 : (Finset.filter (fun x : ℕ ↦ (x ^ 2 - x + 1) % p = 0) (Finset.Ico 1 p)).card ≤ 2 := round2_h_card_bound3 p hp3
    exact le_trans h4 h5
  have h_disj12 : Disjoint S1 S2 := by simp [hS1, hS2, Finset.disjoint_left] ; omega
  have h_disj13 : Disjoint S1 S3 := by simp [hS1, hS3, Finset.disjoint_left] ; omega
  have h_disj14 : Disjoint S1 S4 := by simp [hS1, hS4, Finset.disjoint_left] ; omega
  have h_disj23 : Disjoint S2 S3 := by simp [hS2, hS3, Finset.disjoint_left] ; omega
  have h_disj24 : Disjoint S2 S4 := by simp [hS2, hS4, Finset.disjoint_left] ; omega
  have h_disj34 : Disjoint S3 S4 := by simp [hS3, hS4, Finset.disjoint_left] ; omega
  let S_union := S1 ∪ S2 ∪ S3 ∪ S4
  have h_union : M = S_union := by
    apply Finset.Subset.antisymm
    · intro x hx
      have h_mem1 : x ∈ Finset.Ico 1 p := (Finset.mem_filter.mp hx).1
      have h_mem2 : p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2 := (Finset.mem_filter.mp hx).2
      have h4 : x + inv x ≠ p + 2 := h_main_contra x h_mem1
      have h5 : x + inv x ≤ p + 1 := by omega
      have h6 : p - 2 ≤ x + inv x := h_mem2.1
      have h_cases : x + inv x = p - 2 ∨ x + inv x = p - 1 ∨ x + inv x = p ∨ x + inv x = p + 1 := by omega
      have h_goal : x ∈ S_union := by
        rcases h_cases with (h | h | h | h)
        · have hS1 : x ∈ S1 := by
            rw [hS1]
            exact Finset.mem_filter.mpr ⟨h_mem1, h⟩
          simp [S_union, hS1]
        · have hS2 : x ∈ S2 := by
            rw [hS2]
            exact Finset.mem_filter.mpr ⟨h_mem1, h⟩
          simp [S_union, hS2]
        · have hS3 : x ∈ S3 := by
            rw [hS3]
            exact Finset.mem_filter.mpr ⟨h_mem1, h⟩
          simp [S_union, hS3]
        · have hS4 : x ∈ S4 := by
            rw [hS4]
            exact Finset.mem_filter.mpr ⟨h_mem1, h⟩
          simp [S_union, hS4]
      exact h_goal
    · intro x hx
      have h1 : x ∈ S_union := hx
      have h2 : x ∈ S1 ∨ x ∈ S2 ∨ x ∈ S3 ∨ x ∈ S4 := by
        simp only [S_union, Finset.mem_union] at h1 ⊢ ; tauto
      rcases h2 with (h2 | h2 | h2 | h2)
      ·
        have h_x_in_ico : x ∈ Finset.Ico 1 p := (Finset.mem_filter.mp h2).1
        have h_eq : x + inv x = p - 2 := (Finset.mem_filter.mp h2).2
        have h_eq1 : p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2 := by
          constructor <;> omega
        exact Finset.mem_filter.mpr ⟨h_x_in_ico, h_eq1⟩
      ·
        have h_x_in_ico : x ∈ Finset.Ico 1 p := (Finset.mem_filter.mp h2).1
        have h_eq : x + inv x = p - 1 := (Finset.mem_filter.mp h2).2
        have h_eq1 : p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2 := by
          constructor <;> omega
        exact Finset.mem_filter.mpr ⟨h_x_in_ico, h_eq1⟩
      ·
        have h_x_in_ico : x ∈ Finset.Ico 1 p := (Finset.mem_filter.mp h2).1
        have h_eq : x + inv x = p := (Finset.mem_filter.mp h2).2
        have h_eq1 : p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2 := by
          constructor <;> omega
        exact Finset.mem_filter.mpr ⟨h_x_in_ico, h_eq1⟩
      ·
        have h_x_in_ico : x ∈ Finset.Ico 1 p := (Finset.mem_filter.mp h2).1
        have h_eq : x + inv x = p + 1 := (Finset.mem_filter.mp h2).2
        have h_eq1 : p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2 := by
          constructor <;> omega
        exact Finset.mem_filter.mpr ⟨h_x_in_ico, h_eq1⟩
  have h_disj134 : Disjoint S1 (S3 ∪ S4) := by
    apply Finset.disjoint_union_right.mpr
    constructor
    · exact h_disj13
    · exact h_disj14
  have h_disj234 : Disjoint S2 (S3 ∪ S4) := by
    apply Finset.disjoint_union_right.mpr
    constructor
    · exact h_disj23
    · exact h_disj24
  have h_card_eq : S_union.card = S1.card + S2.card + S3.card + S4.card := by
    have h1_def : S_union = S1 ∪ (S2 ∪ (S3 ∪ S4)) := by
      ext x
      simp [S_union, Finset.mem_union]
    have h_main : (S1 ∪ (S2 ∪ (S3 ∪ S4))).card = S1.card + (S2 ∪ (S3 ∪ S4)).card := by
      apply Finset.card_union_of_disjoint
      apply Finset.disjoint_union_right.mpr
      constructor
      · exact h_disj12
      · exact h_disj134
    have h_main2 : (S2 ∪ (S3 ∪ S4)).card = S2.card + (S3 ∪ S4).card := by
      apply Finset.card_union_of_disjoint h_disj234
    have h_main3 : (S3 ∪ S4).card = S3.card + S4.card := by
      apply Finset.card_union_of_disjoint h_disj34
    rw [h1_def]
    rw [h_main, h_main2, h_main3]
    ring
  have h_S1_card0 : S1.card = 0 := by rw [h_S1_empty] ; simp
  have h_goal : S_union.card ≤ 6 := by
    rw [h_card_eq, h_S1_card0]
    linarith [h_S2_card, h_S3_card, h_S4_card]
  have h_M_eq_Sunion : M.card = S_union.card := by
    congr
  have h_final : M.card ≤ 6 := by
    have h : M.card = S_union.card := h_M_eq_Sunion
    rw [h]
    exact h_goal
  exact h_final

lemma round1_h_inv2 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_p5 : p = 5):
  inv 2 = 3 := by
  subst h_p5
  have h2 : 1 ≤ (2 : ℕ) ∧ (2 : ℕ) < 5 := by norm_num
  have h3 := h_inv 2 h2
  have h4 : 1 ≤ inv 2 ∧ inv 2 < 5 ∧ (2 * inv 2) % 5 = 1 := h3
  have h5 : inv 2 < 5 := h4.2.1
  have h6 : (2 * inv 2) % 5 = 1 := h4.2.2
  interval_cases h7 : inv 2 <;> norm_num at h6 ⊢

lemma round1_h_inv3 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_p5 : p = 5):
  inv 3 = 2 := by
  subst h_p5
  have h2 : 1 ≤ (3 : ℕ) ∧ (3 : ℕ) < 5 := by norm_num
  have h3 := h_inv 3 h2
  have h4 : 1 ≤ inv 3 ∧ inv 3 < 5 ∧ (3 * inv 3) % 5 = 1 := h3
  have h5 : inv 3 < 5 := h4.2.1
  have h6 : (3 * inv 3) % 5 = 1 := h4.2.2
  interval_cases h7 : inv 3 <;> norm_num at h6 ⊢

lemma round1_h_inv4 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_p5 : p = 5):
  inv 4 = 4 := by
  subst h_p5
  have h2 : 1 ≤ (4 : ℕ) ∧ (4 : ℕ) < 5 := by norm_num
  have h3 := h_inv 4 h2
  have h4 : 1 ≤ inv 4 ∧ inv 4 < 5 ∧ (4 * inv 4) % 5 = 1 := h3
  have h5 : inv 4 < 5 := h4.2.1
  have h6 : (4 * inv 4) % 5 = 1 := h4.2.2
  interval_cases h7 : inv 4 <;> norm_num at h6 ⊢

lemma round1_hA_eq (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_p5 : p = 5)
  (A : Finset ℕ)
  (hA_def : A = (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2))
  (h_inv2 : inv 2 = 3)
  (h_inv3 : inv 3 = 2)
  (h_inv4 : inv 4 = 4):
  A = {4} := by
  subst h_p5
  rw [hA_def]
  apply Finset.ext
  intro x
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  ·
    rintro ⟨h1, h2⟩
    have h11 : 2 ≤ x := h1.1
    have h12 : x < 5 := h1.2
    have h3 : x = 2 ∨ x = 3 ∨ x = 4 := by omega
    rcases h3 with (rfl | rfl | rfl)
    ·
      rw [h_inv2] at h2
      norm_num at h2
    ·
      rw [h_inv3] at h2
      norm_num at h2
    ·
      rw [h_inv4] at h2
  ·
    rintro rfl
    simp [h_inv4]

theorem round1_p5_case_lemma (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_p5 : p = 5)
  (A : Finset ℕ)
  (hA_def : A = (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2))
  (B : Finset ℕ)
  (hB_def : B = (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2))
  (M : Finset ℕ)
  (hM_def : M = (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2))
  (h21 : (Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card = A.card)
  (h3 : A.card = B.card)
  (h4 : A.card + B.card + M.card = p - 1)
  (h5 : M.card ≤ 6):
  (A.card : ℝ) > (p : ℝ) / 4 - 1 := by
  have h_inv2 : inv 2 = 3 := round1_h_inv2 p hp3 inv h_inv h_p5
  have h_inv3 : inv 3 = 2 := round1_h_inv3 p hp3 inv h_inv h_p5
  have h_inv4 : inv 4 = 4 := round1_h_inv4 p hp3 inv h_inv h_p5
  have hA_eq : A = {4} := round1_hA_eq p hp3 inv h_inv h_p5 A hA_def h_inv2 h_inv3 h_inv4
  have hA_card : A.card = 1 := by
    rw [hA_eq]
    simp
  rw [hA_card, h_p5]
  norm_num

lemma round1_inv1 :
  (1 : ZMod 7)⁻¹ = (1 : ZMod 7) := by
  have h : (1 : ZMod 7) * (1 : ZMod 7) = 1 := by decide
  exact ZMod.inv_one 7

lemma round1_inv2 :
  (2 : ZMod 7)⁻¹ = (4 : ZMod 7) := by
  have h : (2 : ZMod 7) * (4 : ZMod 7) = 1 := by decide
  exact ZMod.inv_eq_of_mul_eq_one 7 2 4 h

lemma round1_inv3 :
  (3 : ZMod 7)⁻¹ = (5 : ZMod 7) := by
  have h : (3 : ZMod 7) * (5 : ZMod 7) = 1 := by decide
  exact ZMod.inv_eq_of_mul_eq_one 7 3 5 h

lemma round1_inv4 :
  (4 : ZMod 7)⁻¹ = (2 : ZMod 7) := by
  have h : (4 : ZMod 7) * (2 : ZMod 7) = 1 := by decide
  exact ZMod.inv_eq_of_mul_eq_one 7 4 2 h

lemma round1_inv5 :
  (5 : ZMod 7)⁻¹ = (3 : ZMod 7) := by
  have h : (5 : ZMod 7) * (3 : ZMod 7) = 1 := by decide
  exact ZMod.inv_eq_of_mul_eq_one 7 5 3 h

lemma round1_inv6 :
  (6 : ZMod 7)⁻¹ = (6 : ZMod 7) := by
  have h : (6 : ZMod 7) * (6 : ZMod 7) = 1 := by decide
  exact ZMod.inv_eq_of_mul_eq_one 7 6 6 h

lemma round1_h_forward (k : ZMod 7)
  (h : k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val):
  k = (3 : ZMod 7) := by
  have h1 : k ≠ 0 := h.1
  have h2 : k ≠ -1 := h.2.1
  have h3 : (k + 1)⁻¹.val < k⁻¹.val := h.2.2
  have h1v1 : ((1 : ZMod 7)⁻¹).val = 1 := by rw [round1_inv1] ; decide
  have h2v : ((2 : ZMod 7)⁻¹).val = 4 := by rw [round1_inv2] ; decide
  have h3v : ((3 : ZMod 7)⁻¹).val = 5 := by rw [round1_inv3] ; decide
  have h4v : ((4 : ZMod 7)⁻¹).val = 2 := by rw [round1_inv4] ; decide
  have h5v : ((5 : ZMod 7)⁻¹).val = 3 := by rw [round1_inv5] ; decide
  have h6v : ((6 : ZMod 7)⁻¹).val = 6 := by rw [round1_inv6] ; decide
  fin_cases k
  · contradiction
  ·
    have h4 : ( (1 : ZMod 7) + 1)⁻¹.val < (1 : ZMod 7)⁻¹.val := h3
    have h5 : ( (1 : ZMod 7) + 1)⁻¹.val = 4 := by
      rw [show (1 : ZMod 7) + 1 = (2 : ZMod 7) from by decide]
      exact h2v
    rw [h5, h1v1] at h4
    norm_num at h4
  ·
    have h4 : ( (2 : ZMod 7) + 1)⁻¹.val < (2 : ZMod 7)⁻¹.val := h3
    have h5 : ( (2 : ZMod 7) + 1)⁻¹.val = 5 := by
      rw [show (2 : ZMod 7) + 1 = (3 : ZMod 7) from by decide]
      exact h3v
    rw [h5, h2v] at h4
    norm_num at h4
  ·
    rfl
  ·
    have h4 : ( (4 : ZMod 7) + 1)⁻¹.val < (4 : ZMod 7)⁻¹.val := h3
    have h5 : ( (4 : ZMod 7) + 1)⁻¹.val = 3 := by
      rw [show (4 : ZMod 7) + 1 = (5 : ZMod 7) from by decide]
      exact h5v
    rw [h5, h4v] at h4
    norm_num at h4
  ·
    have h4 : ( (5 : ZMod 7) + 1)⁻¹.val < (5 : ZMod 7)⁻¹.val := h3
    have h5 : ( (5 : ZMod 7) + 1)⁻¹.val = 6 := by
      rw [show (5 : ZMod 7) + 1 = (6 : ZMod 7) from by decide]
      exact h6v
    rw [h5, h5v] at h4
    norm_num at h4
  ·
    simp at h2 ; tauto

lemma round1_h_backward (k : ZMod 7)
  (h : k = (3 : ZMod 7)):
  (k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) := by
  subst h
  have h1v : ((4 : ZMod 7)⁻¹).val = 2 := by
    have h1 : (4 : ZMod 7)⁻¹ = (2 : ZMod 7) := round1_inv4
    rw [h1]
    decide
  have h2v : ((3 : ZMod 7)⁻¹).val = 5 := by
    have h2 : (3 : ZMod 7)⁻¹ = (5 : ZMod 7) := round1_inv3
    rw [h2]
    decide
  have h_eq1 : (3 : ZMod 7) + 1 = (4 : ZMod 7) := by decide
  have h3 : ((3 : ZMod 7) + 1)⁻¹.val < (3 : ZMod 7)⁻¹.val := by
    rw [h_eq1]
    rw [h1v, h2v]
    norm_num
  have h4 : (3 : ZMod 7) ≠ 0 := by decide
  have h5 : (3 : ZMod 7) ≠ -1 := by decide
  exact ⟨h4, h5, h3⟩

lemma round1_zmod7_prop (k : ZMod 7):
  (k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) ↔ k = (3 : ZMod 7) := by
  constructor
  · exact round1_h_forward k
  · exact round1_h_backward k

lemma round1_filter_eq :
  Finset.filter (fun (k : ZMod 7) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod 7)) = ({(3 : ZMod 7)} : Finset (ZMod 7)) := by
  ext x
  simp [round1_zmod7_prop]

lemma round1_card_eq_one :
  (Finset.filter (fun (k : ZMod 7) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod 7))).card = 1 := by
  rw [round1_filter_eq]
  simp

theorem round1_p7_case_lemma (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1))
  (h_p7 : p = 7)
  (A : Finset ℕ)
  (hA_def : A = (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2))
  (B : Finset ℕ)
  (hB_def : B = (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2))
  (M : Finset ℕ)
  (hM_def : M = (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2))
  (h21 : (Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card = A.card)
  (h3 : A.card = B.card)
  (h4 : A.card + B.card + M.card = p - 1)
  (h5 : M.card ≤ 6):
  (A.card : ℝ) > (p : ℝ) / 4 - 1 := by
  subst h_p7
  have h_main : (Finset.filter (fun (k : ZMod 7) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod 7))).card = 1 := round1_card_eq_one
  have h_eq : (Finset.filter (fun (k : ZMod 7) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod 7))).card = A.card := by
    exact h21
  have h_A_card : A.card = 1 := by
    linarith
  rw [h_A_card]
  norm_num

theorem round1_finset_card_eq_A (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p)
  (inv : ℕ → ℕ)
  (h_inv : ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1)):
  let A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2);
  (Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card = A.card := by
  have h_modular_inverse_unique : ∀ (z y1 y2 : ℕ), 1 ≤ z ∧ z < p ∧ 1 ≤ y1 ∧ y1 < p ∧ 1 ≤ y2 ∧ y2 < p ∧ (z * y1) % p = 1 ∧ (z * y2) % p = 1 → y1 = y2 := by
    exact round1_modular_inverse_unique_lemma p hp3 inv h_inv
  have h_inv_is_involution : ∀ (x : ℕ), 1 ≤ x ∧ x < p → inv (inv x) = x := by
    exact round1_inv_is_involution_lemma p hp3 inv h_inv h_modular_inverse_unique
  have h_zmod_val_eq_inv : ∀ (a : ℕ), 1 ≤ a ∧ a < p → (( (a : ZMod p) )⁻¹).val = inv a := by
    exact round1_zmod_val_eq_inv_lemma p hp3 inv h_inv h_modular_inverse_unique
  have h_key_property : ∀ (a : ℕ), 1 ≤ a ∧ a + 1 < p → inv (inv a + 1) = p + 1 - inv (a + 1) := by
    exact round1_key_property_lemma p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv
  set S := Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p)) with hS_def
  set A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2) with hA_def
  set f : (ZMod p) → ℕ := fun k => (k⁻¹).val + 1 with hf_def
  set g : ℕ → (ZMod p) := fun x => ((x - 1 : ℕ) : ZMod p)⁻¹ with hg_def
  have h1 : ∀ x ∈ S, f x ∈ A := by
    exact round1_S_to_A_well_defined p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property
  have h2 : ∀ y ∈ A, g y ∈ S := by
    exact round1_A_to_S_well_defined p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property
  have h3 : ∀ x ∈ S, g (f x) = x := by
    exact round1_g_f_is_identity_on_S p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property
  have h4 : ∀ y ∈ A, f (g y) = y := by
    exact round1_f_g_is_identity_on_A p hp3 inv h_inv h_modular_inverse_unique h_inv_is_involution h_zmod_val_eq_inv h_key_property
  have h5 : S.card = A.card := by
    exact round1_finset_card_eq_of_bijection_general S A f g h1 h2 h3 h4
  exact h5

theorem putnam_2025_b5 (p : ℕ)
  [hp : Fact p.Prime]
  (hp3 : 3 < p):
  (#{k : ZMod p | k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val} : ℝ) > p / 4 - 1 := by
    have h1 : ∃ (inv : ℕ → ℕ), ∀ (x : ℕ), 1 ≤ x ∧ x < p → (1 ≤ inv x ∧ inv x < p ∧ (x * inv x) % p = 1) := by
      exact round1_exists_inv_function p hp3
    rcases h1 with ⟨inv, h_inv⟩
    set A : Finset ℕ := (Finset.Ico 2 p).filter (fun x => x + inv x > p + 2) with hA_def
    set B : Finset ℕ := (Finset.Ico 1 p).filter (fun x => x + inv x < p - 2) with hB_def
    set M : Finset ℕ := (Finset.Ico 1 p).filter (fun x => p - 2 ≤ x + inv x ∧ x + inv x ≤ p + 2) with hM_def
    have h21 : (Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card = A.card := by
      exact round1_finset_card_eq_A p hp3 inv h_inv
    have h3 : A.card = B.card := by
      exact round1_A_card_eq_B_card p hp3 inv h_inv
    have h4 : A.card + B.card + M.card = p - 1 := by
      exact round1_sum_of_cards p hp3 inv h_inv
    have h5 : M.card ≤ 6 := by
      exact round1_M_card_le_6 p hp3 inv h_inv
    have h6 : 2 * A.card + M.card = p - 1 := by
      omega
    by_cases h10 : p > 10
    ·
      have h11 : (A.card : ℝ) > (p : ℝ) / 4 - 1 := by
        exact round1_inequality_lemma p A.card M.card h10 h6 h5
      have h22 : (#{k : ZMod p | k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val} : ℝ) = ((Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card : ℝ) := by
        exact round1_ncard_to_finset_card p (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val)
      have h23 : ((Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card : ℝ) = (A.card : ℝ) := by
        rw [h21]
      linarith
    ·
      have h101 : p ≤ 10 := by linarith
      have h102 : p = 5 ∨ p = 7 := by
        have h1021 : Nat.Prime p := by exact Fact.out
        have h1022 : 3 < p := hp3
        have h1023 : p ≤ 10 := h101
        interval_cases p <;> norm_num at h1021 ⊢
      rcases h102 with (h102 | h102)
      ·
        have h11 : (A.card : ℝ) > (p : ℝ) / 4 - 1 := by
          exact round1_p5_case_lemma p hp3 inv h_inv h102 A hA_def B hB_def M hM_def h21 h3 h4 h5
        have h22 : (#{k : ZMod p | k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val} : ℝ) = ((Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card : ℝ) := by
          exact round1_ncard_to_finset_card p (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val)
        have h23 : ((Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card : ℝ) = (A.card : ℝ) := by
          rw [h21]
        linarith
      ·
        have h11 : (A.card : ℝ) > (p : ℝ) / 4 - 1 := by
          exact round1_p7_case_lemma p hp3 inv h_inv h102 A hA_def B hB_def M hM_def h21 h3 h4 h5
        have h22 : (#{k : ZMod p | k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val} : ℝ) = ((Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card : ℝ) := by
          exact round1_ncard_to_finset_card p (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val)
        have h23 : ((Finset.filter (fun (k : ZMod p) => k ≠ 0 ∧ k ≠ -1 ∧ (k + 1)⁻¹.val < k⁻¹.val) (Finset.univ : Finset (ZMod p))).card : ℝ) = (A.card : ℝ) := by
          rw [h21]
        linarith

end Putnam2025B5
