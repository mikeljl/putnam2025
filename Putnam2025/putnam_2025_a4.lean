import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Int.Star
import Mathlib.Tactic.NormNum.IsCoprime

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Classical

namespace Putnam2025A4

lemma round1_h1 :
  Real.pi / 2 < (2 * Real.pi * 508) / 2025 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  nlinarith [Real.pi_pos]

lemma round1_h2 :
  (2 * Real.pi * 508) / 2025 < Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  nlinarith [Real.pi_pos]

lemma round1_h3 (h1 : Real.pi / 2 < (2 * Real.pi * 508) / 2025)
  (h2 : (2 * Real.pi * 508) / 2025 < Real.pi):
  Real.cos ((2 * Real.pi * 508) / 2025) < 0 := by
  have h4 : Real.pi / 2 < (2 * Real.pi * 508) / 2025 := h1
  have h5 : (2 * Real.pi * 508) / 2025 < Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
  have h6 : Real.cos ((2 * Real.pi * 508) / 2025) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h4 h5
  exact h6

theorem round1_h2' :
  ∃ (α h : ℝ), α = (2 * Real.pi * 508) / 2025 ∧ h > 0 ∧ h ^ 2 + Real.cos α = 0 := by
  have h1 : Real.pi / 2 < (2 * Real.pi * 508) / 2025 := round1_h1
  have h2 : (2 * Real.pi * 508) / 2025 < Real.pi := round1_h2
  have h3 : Real.cos ((2 * Real.pi * 508) / 2025) < 0 := round1_h3 h1 h2
  set α : ℝ := (2 * Real.pi * 508) / 2025 with hα
  have h4 : Real.cos α < 0 := h3
  have h5 : 0 < -Real.cos α := by linarith
  set h : ℝ := Real.sqrt (-Real.cos α) with hh
  have h6 : h > 0 := by
    rw [hh]
    exact Real.sqrt_pos.mpr h5
  have h7 : h ^ 2 + Real.cos α = 0 := by
    rw [hh]
    have h8 : (Real.sqrt (-Real.cos α)) ^ 2 = -Real.cos α := Real.sq_sqrt (by linarith)
    linarith
  refine' ⟨α, h, by simp [hα], h6, h7⟩

lemma round1_commute_1x1_matrices (X Y : Matrix (Fin 1) (Fin 1) ℝ):
  X * Y = Y * X := by
  ext i j
  fin_cases i ; fin_cases j ; simp [Matrix.mul_apply] ; ring

theorem round1_lemma_k_ne_1 (k : ℕ)
  (hk : k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)):
  k ≠ 1 := by
  by_contra h
  have h₁ : k = 1 := h
  rcases hk with ⟨hk_pos, ⟨A, hA⟩⟩
  have h₂ : ∀ (i j : Fin 2025), (A i * A j = A j * A i) := by
    intro i j
    have h_k1 : k = 1 := h₁
    have h₃ : (A i : Matrix (Fin k) (Fin k) ℝ) * (A j) = (A j) * (A i) := by
      subst h_k1
      simpa using round1_commute_1x1_matrices (A i) (A j)
    exact h₃
  have h₄ : ∀ (i j : Fin 2025), |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ) := by
    intro i j
    have h₅ : (A i * A j = A j * A i) := h₂ i j
    have h₆ : (A i * A j = A j * A i) ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ) := hA i j
    exact h₆.mp h₅
  have h₅ := h₄ (0 : Fin 2025) (2 : Fin 2025)
  norm_num at h₅

lemma round1_h_coprime :
  Nat.Coprime 508 2025 := by
  norm_num

lemma round1_h3_a580cb (α : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (d : ℤ)
  (h : (2025 : ℤ) ∣ (d - 1)):
  Real.cos ((d : ℝ) * α) = Real.cos α := by
  rcases h with ⟨m, hm⟩
  have h4 : (d : ℝ) - 1 = (2025 : ℝ) * (m : ℝ) := by exact_mod_cast hm
  have h5 : (d : ℝ) * α = α + ((508 * m : ℤ) : ℝ) * (2 * Real.pi) := by
    have hα : (2025 : ℝ) * α = 2 * Real.pi * 508 := by
      rw [h21] ; ring
    calc
      (d : ℝ) * α
        = ((d : ℝ) - 1 + 1) * α := by ring
      _ = (((2025 : ℝ) * (m : ℝ)) + 1) * α := by rw [h4]
      _ = ((2025 : ℝ) * (m : ℝ)) * α + α := by ring
      _ = (m : ℝ) * ((2025 : ℝ) * α) + α := by ring
      _ = (m : ℝ) * (2 * Real.pi * 508) + α := by rw [hα]
      _ = α + (m : ℝ) * (2 * Real.pi * 508) := by ring
      _ = α + (((508 * m : ℤ) : ℝ) * (2 * Real.pi)) := by
        simp [mul_comm] ; ring_nf
  rw [h5]
  have h6 : Real.cos (α + ((508 * m : ℤ) : ℝ) * (2 * Real.pi)) = Real.cos α := by
    simpa [Real.cos_add_int_mul_two_pi] using Real.cos_add_int_mul_two_pi α (508 * m)
  exact h6

lemma round1_h4 (α : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (d : ℤ)
  (h : (2025 : ℤ) ∣ (d + 1)):
  Real.cos ((d : ℝ) * α) = Real.cos α := by
  rcases h with ⟨m, hm⟩
  have h4 : (d : ℝ) + 1 = (2025 : ℝ) * (m : ℝ) := by exact_mod_cast hm
  have h5 : (d : ℝ) * α = -α + ((508 * m : ℤ) : ℝ) * (2 * Real.pi) := by
    have hα : (2025 : ℝ) * α = 2 * Real.pi * 508 := by
      rw [h21] ; ring
    calc
      (d : ℝ) * α
        = (((d : ℝ) + 1) - 1) * α := by ring
      _ = (((2025 : ℝ) * (m : ℝ)) - 1) * α := by rw [h4]
      _ = ((2025 : ℝ) * (m : ℝ)) * α - α := by ring
      _ = (m : ℝ) * ((2025 : ℝ) * α) - α := by ring
      _ = (m : ℝ) * (2 * Real.pi * 508) - α := by rw [hα]
      _ = -α + (m : ℝ) * (2 * Real.pi * 508) := by ring
      _ = -α + (((508 * m : ℤ) : ℝ) * (2 * Real.pi)) := by
        simp [mul_comm] ; ring_nf
  rw [h5]
  have h6 : Real.cos (-α + ((508 * m : ℤ) : ℝ) * (2 * Real.pi)) = Real.cos α := by
    have h7 : Real.cos (-α + ((508 * m : ℤ) : ℝ) * (2 * Real.pi)) = Real.cos (-α) := by
      simpa [Real.cos_add_int_mul_two_pi] using Real.cos_add_int_mul_two_pi (-α) (508 * m)
    rw [h7]
    rw [Real.cos_neg]
  exact h6

lemma round1_algebra_case1 (α : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (d k : ℤ)
  (h_eq : (d : ℝ) * α = (α : ℝ) + 2 * (k : ℝ) * Real.pi):
  (2025 : ℤ) ∣ (d - 1) := by
  have hα : (2025 : ℝ) * α = 2 * Real.pi * 508 := by
    rw [h21] ; field_simp
  have h1 : 2025 * (((d : ℝ) - 1) * α) = 2025 * (2 * ((k : ℝ)) * Real.pi) := by
    have h2 : ((d : ℝ) * α) = (α : ℝ) + 2 * (k : ℝ) * Real.pi := h_eq
    have h3 : ((d : ℝ) - 1) * α = 2 * ((k : ℝ)) * Real.pi := by
      linarith
    rw [h3]
  have h4 : 2025 * (((d : ℝ) - 1) * α) = ((d : ℝ) - 1) * ((2025 : ℝ) * α) := by ring
  rw [h4] at h1
  have h5 : ((d : ℝ) - 1) * ((2025 : ℝ) * α) = ((d : ℝ) - 1) * (2 * Real.pi * 508) := by
    rw [hα]
  rw [h5] at h1
  have h6 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h7 : ((d : ℝ) - 1) * (508 : ℝ) = (k : ℝ) * (2025 : ℝ) := by
    apply (mul_right_inj' h6).mp
    linarith
  have h8 : (508 : ℤ) * (d - 1) = 2025 * k := by
    norm_cast at h7 ⊢ ; linarith
  have h9 : (2025 : ℤ) ∣ (508 : ℤ) * (d - 1) := ⟨k, h8⟩
  have h_coprime_nat : Nat.Coprime 508 2025 := round1_h_coprime
  have h_coprime_int : IsCoprime (508 : ℤ) (2025 : ℤ) := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr h_coprime_nat
  have h10 : IsCoprime (2025 : ℤ) (508 : ℤ) := by
    exact IsCoprime.symm h_coprime_int
  exact IsCoprime.dvd_of_dvd_mul_left h10 h9

lemma round1_algebra_case2 (α : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (d k : ℤ)
  (h_eq : (d : ℝ) * α = - (α : ℝ) + 2 * (k : ℝ) * Real.pi):
  (2025 : ℤ) ∣ (d + 1) := by
  have hα : (2025 : ℝ) * α = 2 * Real.pi * 508 := by
    rw [h21] ; field_simp
  have h1 : 2025 * (((d : ℝ) + 1) * α) = 2025 * (2 * ((k : ℝ)) * Real.pi) := by
    have h2 : ((d : ℝ) * α) = - (α : ℝ) + 2 * (k : ℝ) * Real.pi := h_eq
    have h3 : ((d : ℝ) + 1) * α = 2 * ((k : ℝ)) * Real.pi := by
      linarith
    rw [h3]
  have h4 : 2025 * (((d : ℝ) + 1) * α) = ((d : ℝ) + 1) * ((2025 : ℝ) * α) := by ring
  rw [h4] at h1
  have h5 : ((d : ℝ) + 1) * ((2025 : ℝ) * α) = ((d : ℝ) + 1) * (2 * Real.pi * 508) := by
    rw [hα]
  rw [h5] at h1
  have h6 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h7 : ((d : ℝ) + 1) * (508 : ℝ) = (k : ℝ) * (2025 : ℝ) := by
    apply (mul_right_inj' h6).mp
    linarith
  have h8 : (508 : ℤ) * (d + 1) = 2025 * k := by
    norm_cast at h7 ⊢ ; linarith
  have h9 : (2025 : ℤ) ∣ (508 : ℤ) * (d + 1) := ⟨k, h8⟩
  have h_coprime_nat : Nat.Coprime 508 2025 := round1_h_coprime
  have h_coprime_int : IsCoprime (508 : ℤ) (2025 : ℤ) := by exact Int.isCoprime_iff_gcd_eq_one.mpr h_coprime_nat
  have h10 : IsCoprime (2025 : ℤ) (508 : ℤ) := by exact IsCoprime.symm h_coprime_int
  exact IsCoprime.dvd_of_dvd_mul_left h10 h9

lemma round1_h_main (α : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (d : ℤ)
  (h : Real.cos ((d : ℝ) * α) = Real.cos α)
  (h_bounds : -2024 ≤ d ∧ d ≤ 2024):
  |d| ∈ ({0, 1, 2024} : Set ℤ) := by
  have h_iff : ∃ (k : ℤ), (α : ℝ) = 2 * (k : ℝ) * Real.pi + (d : ℝ) * α ∨ (α : ℝ) = 2 * (k : ℝ) * Real.pi - (d : ℝ) * α := by
    exact Real.cos_eq_cos_iff.mp h
  rcases h_iff with ⟨k, h1 | h2⟩
  ·
    have h1' : (d : ℝ) * α = (α : ℝ) + 2 * ((-k : ℤ) : ℝ) * Real.pi := by
      have h_eq : (α : ℝ) = 2 * (k : ℝ) * Real.pi + (d : ℝ) * α := h1
      have h : (d : ℝ) * α = (α : ℝ) - 2 * (k : ℝ) * Real.pi := by linarith
      have h2 : (α : ℝ) - 2 * (k : ℝ) * Real.pi = (α : ℝ) + 2 * ((-k : ℤ) : ℝ) * Real.pi := by
        simp [mul_comm]
        ring
      rw [h2] at h
      exact h
    have h3 : (2025 : ℤ) ∣ (d - 1) := round1_algebra_case1 α h21 d (-k) h1'
    rcases h3 with ⟨m, hm⟩
    have h_eq : d - 1 = 2025 * m := by exact_mod_cast hm
    have h_ge1 : -2025 ≤ d - 1 := by linarith [h_bounds.1]
    have h_ge2 : d - 1 ≤ 2023 := by linarith [h_bounds.2]
    rw [h_eq] at h_ge1 h_ge2
    have h_m : m = 0 ∨ m = -1 := by omega
    rcases h_m with (h_m0 | h_m_neg1)
    · have h_d : d = 1 := by
        rw [h_m0] at h_eq ; omega
      have h_goal : |d| = 1 := by
        rw [h_d] ; norm_num
      rw [h_goal]
      simp
    · have h_d : d = -2024 := by
        rw [h_m_neg1] at h_eq ; omega
      have h_goal : |d| = 2024 := by
        rw [h_d] ; norm_num
      rw [h_goal]
      simp
  ·
    have h2' : (d : ℝ) * α = - (α : ℝ) + 2 * (k : ℝ) * Real.pi := by
      have h_eq : (α : ℝ) = 2 * (k : ℝ) * Real.pi - (d : ℝ) * α := h2
      have h : (d : ℝ) * α = - (α : ℝ) + 2 * (k : ℝ) * Real.pi := by linarith
      exact h
    have h3 : (2025 : ℤ) ∣ (d + 1) := round1_algebra_case2 α h21 d k h2'
    rcases h3 with ⟨m, hm⟩
    have h_eq : d + 1 = 2025 * m := by exact_mod_cast hm
    have h_ge1 : -2023 ≤ d + 1 := by linarith [h_bounds.1]
    have h_ge2 : d + 1 ≤ 2025 := by linarith [h_bounds.2]
    rw [h_eq] at h_ge1 h_ge2
    have h_m : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    rcases h_m with (h_m_neg1 | h_m0 | h_m1)
    · exfalso
      linarith
    · have h_d : d = -1 := by
        rw [h_m0] at h_eq ; omega
      have h_goal : |d| = 1 := by
        rw [h_d] ; norm_num
      rw [h_goal]
      simp
    · have h_d : d = 2024 := by
        rw [h_m1] at h_eq ; omega
      have h_goal : |d| = 2024 := by
        rw [h_d] ; norm_num
      rw [h_goal]
      simp

lemma round2_main_equivalence (u v : Fin 3 → ℝ):
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun r s => u r * u s
  let B : Matrix (Fin 3) (Fin 3) ℝ := fun r s => v r * v s
  (A * B = B * A) ↔ (u ⬝ᵥ v = 0) ∨ (∀ r s : Fin 3, u r * v s = v r * u s) := by
  let c : ℝ := u ⬝ᵥ v
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun r s => u r * u s
  let B : Matrix (Fin 3) (Fin 3) ℝ := fun r s => v r * v s
  let M1 : Matrix (Fin 3) (Fin 3) ℝ := fun r s => u r * v s
  let M2 : Matrix (Fin 3) (Fin 3) ℝ := fun r s => v r * u s
  have h1 : A * B = c • M1 := by
    ext r s
    simp [Matrix.mul_apply, c, A, B, M1, dotProduct, Fin.sum_univ_three]
    ring
  have h2 : B * A = c • M2 := by
    ext r s
    simp [Matrix.mul_apply, c, A, B, M2, dotProduct, Fin.sum_univ_three]
    ring
  constructor
  · intro h
    rw [h1, h2] at h
    have h3 : c • M1 = c • M2 := h
    have h4 : c = 0 ∨ M1 = M2 := by
      by_cases hc : c = 0
      · exact Or.inl hc
      · have h5 : M1 = M2 := by
          have h6 : c • (M1 - M2) = 0 := by
            simpa [sub_eq_add_neg, add_comm] using sub_eq_zero.mpr h3
          have h7 : ∀ (i j : Fin 3), (M1 - M2) i j = 0 := by
            intro i j
            have h8 : c * ((M1 - M2) i j) = 0 := by
              simpa [Matrix.sub_apply] using congr_fun (congr_fun h6 i) j
            exact (mul_eq_zero.mp h8).resolve_left hc
          have h9 : M1 - M2 = 0 := by
            ext i j
            exact h7 i j
          simpa [sub_eq_zero] using h9
        exact Or.inr h5
    cases h4 with
    | inl hc =>
      exact Or.inl hc
    | inr hM =>
      have h5 : ∀ (r s : Fin 3), u r * v s = v r * u s := by
        simpa [M1, M2, Matrix.ext_iff] using hM
      exact Or.inr h5
  · rintro (hc | hM)
    · have h4 : c • M1 = c • M2 := by
        have h5 : c = 0 := hc
        have h6 : c • M1 = 0 := by
          rw [h5] ; simp
        have h7 : c • M2 = 0 := by
          rw [h5] ; simp
        rw [h6, h7]
      rw [h1, h2] ; exact h4
    · have h3 : M1 = M2 := by
        ext r s
        simpa [M1, M2] using hM r s
      have h4 : c • M1 = c • M2 := by
        rw [h3]
      rw [h1, h2] ; exact h4

lemma round2_commute_implies_linearly_dependent (u v : Fin 3 → ℝ)
  (h_u2 : u 2 ≠ 0)
  (h : ∀ (r s : Fin 3), u r * v s = v r * u s):
  ∃ (k : ℝ), ∀ (s : Fin 3), v s = k * u s := by
  have h1 : ∃ (r₀ : Fin 3), u r₀ ≠ 0 := ⟨2, h_u2⟩
  rcases h1 with ⟨r₀, hr₀⟩
  use (v r₀ / u r₀)
  intro s
  have h2 : u r₀ * v s = v r₀ * u s := h r₀ s
  field_simp [hr₀] at h2 ⊢
  linarith

lemma round2_h_main2 (α : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (d : ℤ)
  (h_bounds : -2024 ≤ d ∧ d ≤ 2024)
  (h_cos : Real.cos ((d : ℝ) * α) = 1):
  d = 0 := by
  have h_eq1 : ∃ (n : ℤ), ((n : ℝ) * (2 * Real.pi)) = (d : ℝ) * α := by
    rw [Real.cos_eq_one_iff] at h_cos ; simpa using h_cos
  rcases h_eq1 with ⟨n, hn⟩
  have h_eq2 : (d : ℝ) * α = (n : ℝ) * (2 * Real.pi) := by exact hn.symm
  have h_pi_pos : 0 < 2 * Real.pi := by positivity
  have h2 : (d : ℝ) * (2 * Real.pi * 508 / 2025) = (n : ℝ) * (2 * Real.pi) := by
    rw [h21] at h_eq2 ; exact h_eq2
  have h3 : (d : ℝ) * (508 : ℝ) = (n : ℝ) * (2025 : ℝ) := by
    have h4 : (d : ℝ) * (2 * Real.pi * 508 / 2025) = (n : ℝ) * (2 * Real.pi) := h2
    have h5 : (2 * Real.pi) ≠ 0 := by positivity
    have h6 : (d : ℝ) * (508 / 2025 : ℝ) = (n : ℝ) := by
      apply (mul_right_inj' h5).mp
      linarith
    have h7 : (d : ℝ) * (508 : ℝ) = (n : ℝ) * (2025 : ℝ) := by
      calc
        (d : ℝ) * (508 : ℝ) = 2025 * ((d : ℝ) * (508 / 2025 : ℝ)) := by ring
        _ = 2025 * (n : ℝ) := by rw [h6]
        _ = (n : ℝ) * (2025 : ℝ) := by ring
    exact h7
  have h4 : (d : ℤ) * 508 = n * 2025 := by exact_mod_cast h3
  have h5 : (2025 : ℤ) ∣ (d : ℤ) * 508 := by
    use n
    simpa [mul_comm] using h4
  have h_coprime : IsCoprime (2025 : ℤ) (508 : ℤ) := by norm_num
  have h6 : (2025 : ℤ) ∣ (d : ℤ) := by
    exact IsCoprime.dvd_of_dvd_mul_right h_coprime h5
  have h9 : -2024 ≤ d := h_bounds.1
  have h10 : d ≤ 2024 := h_bounds.2
  have h11 : d = 0 := by omega
  exact h11

lemma round3_hQ_implies_d_eq_zero (α h : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (h22 : h > 0)
  (i j : Fin 2025)
  (d : ℤ)
  (hd : d = (i : ℤ) - (j : ℤ))
  (xi : ℝ)
  (yi : ℝ)
  (xj : ℝ)
  (yj : ℝ)
  (h_val : ℝ)
  (hxi : xi = Real.cos ((i : ℝ) * α))
  (hyi : yi = Real.sin ((i : ℝ) * α))
  (hxj : xj = Real.cos ((j : ℝ) * α))
  (hyj : yj = Real.sin ((j : ℝ) * α))
  (hh_val : h_val = h)
  (u : Fin 3 → ℝ)
  (hu0 : u 0 = xi)
  (hu1 : u 1 = yi)
  (hu2 : u 2 = h_val)
  (v : Fin 3 → ℝ)
  (hv0 : v 0 = xj)
  (hv1 : v 1 = yj)
  (hv2 : v 2 = h_val)
  (hQ : ∀ (r s : Fin 3), u r * v s = v r * u s):
  d = 0 := by
  have h24 : u 2 ≠ 0 := by
    rw [hu2, hh_val] ; exact h22.ne'
  have h_exists : ∃ (k : ℝ), ∀ (s : Fin 3), v s = k * u s := round2_commute_implies_linearly_dependent u v h24 hQ
  rcases h_exists with ⟨k, hk⟩
  have h4 : v 2 = k * u 2 := hk 2
  have h5 : u 2 = h_val := by exact hu2
  have h6 : v 2 = h_val := by exact hv2
  rw [h5, h6] at h4
  have h7 : h_val = k * h_val := h4
  have h8 : h_val = h := by exact hh_val
  rw [h8] at h7
  have hk1 : k = 1 := by
    apply mul_left_cancel₀ h22.ne'
    linarith
  have h_eq_v_u : ∀ (s : Fin 3), v s = u s := by
    intro s
    have h9 : v s = k * u s := hk s
    rw [hk1] at h9
    norm_num at h9 ⊢ ; linarith
  have h10 : v 0 = u 0 := h_eq_v_u 0
  have h11 : v 1 = u 1 := h_eq_v_u 1
  have h12 : xj = xi := by
    simpa [hv0, hu0] using h10
  have h13 : yj = yi := by
    simpa [hv1, hu1] using h11
  have h14 : Real.cos ((d : ℝ) * α) = 1 := by
    have h15 : (d : ℝ) * α = (i : ℝ) * α - (j : ℝ) * α := by
      simp [hd] ; ring
    rw [h15]
    have h16 : Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) = Real.cos ((i : ℝ) * α) * Real.cos ((j : ℝ) * α) + Real.sin ((i : ℝ) * α) * Real.sin ((j : ℝ) * α) := by
      rw [Real.cos_sub]
    rw [h16]
    have h17 : Real.cos ((i : ℝ) * α) = xi := by
      exact hxi.symm
    have h18 : Real.sin ((i : ℝ) * α) = yi := by
      exact hyi.symm
    have h19 : Real.cos ((j : ℝ) * α) = xj := by
      exact hxj.symm
    have h20 : Real.sin ((j : ℝ) * α) = yj := by
      exact hyj.symm
    rw [h17, h18, h19, h20]
    have h21 : xj = xi := h12
    have h22 : yj = yi := h13
    rw [h21, h22]
    have h23 : xi ^ 2 + yi ^ 2 = 1 := by
      have h24 : xi = Real.cos ((i : ℝ) * α) := hxi
      have h25 : yi = Real.sin ((i : ℝ) * α) := hyi
      rw [h24, h25]
      exact Real.cos_sq_add_sin_sq ((i : ℝ) * α)
    nlinarith
  have h_bounds : -2024 ≤ d ∧ d ≤ 2024 := by
    omega
  exact round2_h_main2 α h21 d h_bounds h14

theorem round1_h3' (α h : ℝ)
  (h21 : α = (2 * Real.pi * 508) / 2025)
  (h22 : h > 0)
  (h23 : h ^ 2 + Real.cos α = 0):
  let x : Fin 2025 → ℝ := fun (i : Fin 2025) => Real.cos ((i : ℝ) * α)
  let y : Fin 2025 → ℝ := fun (i : Fin 2025) => Real.sin ((i : ℝ) * α)
  let z : Fin 2025 → ℝ := fun (i : Fin 2025) => h
  let A : Fin 2025 → Matrix (Fin 3) (Fin 3) ℝ := fun (i : Fin 2025) =>
    fun (r s : Fin 3) =>
      match r, s with
      | 0, 0 => (x i) * (x i)
      | 0, 1 => (x i) * (y i)
      | 0, 2 => (x i) * (z i)
      | 1, 0 => (y i) * (x i)
      | 1, 1 => (y i) * (y i)
      | 1, 2 => (y i) * (z i)
      | 2, 0 => (z i) * (x i)
      | 2, 1 => (z i) * (y i)
      | 2, 2 => (z i) * (z i)
  ∀ (i j : Fin 2025), (A i) * (A j) = (A j) * (A i) ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ) := by
  dsimp only
  let x : Fin 2025 → ℝ := fun (i : Fin 2025) => Real.cos ((i : ℝ) * α)
  let y : Fin 2025 → ℝ := fun (i : Fin 2025) => Real.sin ((i : ℝ) * α)
  let z : Fin 2025 → ℝ := fun (_ : Fin 2025) => h
  let A : Fin 2025 → Matrix (Fin 3) (Fin 3) ℝ := fun (i : Fin 2025) =>
    fun (r s : Fin 3) =>
      match r, s with
      | 0, 0 => (x i) * (x i)
      | 0, 1 => (x i) * (y i)
      | 0, 2 => (x i) * (z i)
      | 1, 0 => (y i) * (x i)
      | 1, 1 => (y i) * (y i)
      | 1, 2 => (y i) * (z i)
      | 2, 0 => (z i) * (x i)
      | 2, 1 => (z i) * (y i)
      | 2, 2 => (z i) * (z i)
  intro i j
  let d : ℤ := (i : ℤ) - (j : ℤ)
  let xi := Real.cos ((i : ℝ) * α)
  let yi := Real.sin ((i : ℝ) * α)
  let xj := Real.cos ((j : ℝ) * α)
  let yj := Real.sin ((j : ℝ) * α)
  let h_val : ℝ := h
  let u : Fin 3 → ℝ := ![xi, yi, h_val]
  let v : Fin 3 → ℝ := ![xj, yj, h_val]
  have hA_i : (A i) = fun (r s : Fin 3) => u r * u s := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [A, u, xi, yi, h_val, x, y, z]
  have hA_j : (A j) = fun (r s : Fin 3) => v r * v s := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [A, v, xj, yj, h_val, x, y, z]
  have h_main1 : ((A i) * (A j) = (A j) * (A i)) ↔ (u ⬝ᵥ v = 0) ∨ (∀ r s : Fin 3, u r * v s = v r * u s) := by
    rw [hA_i, hA_j]
    exact round2_main_equivalence u v
  let P : Prop := u ⬝ᵥ v = 0
  let Q : Prop := (∀ r s : Fin 3, u r * v s = v r * u s)
  have h_main_goal : (P ∨ Q) ↔ |d| ∈ ({0, 1, 2024} : Set ℤ) := by
    constructor
    ·
      intro h
      cases h with
      | inl hP =>
        have h_cos : Real.cos ((d : ℝ) * α) = Real.cos α := by
          have h_dot : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
            simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
          have h_eq1 : u ⬝ᵥ v = 0 := hP
          have h_eq2 : xi * xj + yi * yj + h_val ^ 2 = 0 := by
            have h_h : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
              simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
            rw [h_h] at h_eq1
            exact h_eq1
          have h1 : xi * xj + yi * yj = Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) := by
            simp [xi, yi, xj, yj, Real.cos_sub]
          have h2 : Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) = Real.cos ((d : ℝ) * α) := by
            have h3 : ((i : ℝ) * α) - ((j : ℝ) * α) = (d : ℝ) * α := by
              simp [d] ; ring
            rw [h3]
          have h3 : xi * xj + yi * yj = Real.cos ((d : ℝ) * α) := by linarith
          nlinarith
        have h_bounds : -2024 ≤ d ∧ d ≤ 2024 := by omega
        exact round1_h_main α h21 d h_cos h_bounds
      | inr hQ =>
        have h_d_eq_zero : d = 0 := round3_hQ_implies_d_eq_zero α h h21 h22 i j d rfl xi yi xj yj h_val rfl rfl rfl rfl rfl u rfl rfl rfl v rfl rfl rfl hQ
        have h4 : |d| = 0 := by
          rw [h_d_eq_zero] ; norm_num
        have h_goal : |d| ∈ ({0, 1, 2024} : Set ℤ) := by
          rw [h4] ; simp
        exact h_goal
    ·
      intro h
      have h_bounds : -2024 ≤ d ∧ d ≤ 2024 := by omega
      have h_cases : |d| = 0 ∨ |d| = 1 ∨ |d| = 2024 := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ; tauto
      rcases h_cases with (h0 | h1 | h2024)
      ·
        have hd0 : d = 0 := by
          rw [abs_eq_zero] at h0 ; exact h0
        have h_i_eq_j : (i : ℤ) = (j : ℤ) := by
          have h_id : (i : ℤ) - (j : ℤ) = 0 := by
            simpa [d] using hd0
          omega
        have h_ij_eq : i = j := by
          apply Fin.ext
          exact_mod_cast h_i_eq_j
        subst h_ij_eq
        have hQ : Q := by
          simp [Q, u, v] ; aesop
        exact Or.inr hQ
      ·
        have h_d1 : d = 1 ∨ d = -1 := by
          have h_abs : |d| = 1 := h1
          by_cases h_pos : 0 ≤ d
          · have h1' : |d| = d := abs_of_nonneg h_pos
            have h2 : d = 1 := by linarith
            exact Or.inl h2
          · have h3 : d < 0 := by linarith
            have h4 : |d| = -d := abs_of_neg h3
            have h5 : d = -1 := by linarith
            exact Or.inr h5
        rcases h_d1 with (h_d_eq1 | h_d_eq_neg1)
        ·
          have h_cos : Real.cos ((d : ℝ) * α) = Real.cos α := round1_h3_a580cb α h21 d (by omega)
          have h_dot : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
            simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
          have h4 : xi * xj + yi * yj + h_val ^ 2 = 0 := by
            have h1 : xi * xj + yi * yj = Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) := by
              simp [xi, yi, xj, yj, Real.cos_sub]
            have h2 : Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) = Real.cos ((d : ℝ) * α) := by
              have h3 : ((i : ℝ) * α) - ((j : ℝ) * α) = (d : ℝ) * α := by
                simp [d] ; ring
              rw [h3]
            have h3 : xi * xj + yi * yj = Real.cos ((d : ℝ) * α) := by linarith
            have h5 : Real.cos ((d : ℝ) * α) = Real.cos α := h_cos
            nlinarith [h23]
          have hP : P := by
            have h_dot2 : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
              simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
            have h_goal : u ⬝ᵥ v = 0 := by
              calc
                u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := h_dot2
                _ = 0 := h4
            simpa [P] using h_goal
          exact Or.inl hP
        ·
          have h_cos : Real.cos ((d : ℝ) * α) = Real.cos α := round1_h4 α h21 d (by omega)
          have h_dot : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
            simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
          have h4 : xi * xj + yi * yj + h_val ^ 2 = 0 := by
            have h1 : xi * xj + yi * yj = Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) := by
              simp [xi, yi, xj, yj, Real.cos_sub]
            have h2 : Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) = Real.cos ((d : ℝ) * α) := by
              have h3 : ((i : ℝ) * α) - ((j : ℝ) * α) = (d : ℝ) * α := by
                simp [d] ; ring
              rw [h3]
            have h3 : xi * xj + yi * yj = Real.cos ((d : ℝ) * α) := by linarith
            have h5 : Real.cos ((d : ℝ) * α) = Real.cos α := h_cos
            nlinarith [h23]
          have hP : P := by
            have h_dot2 : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
              simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
            have h_goal : u ⬝ᵥ v = 0 := by
              calc
                u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := h_dot2
                _ = 0 := h4
            simpa [P] using h_goal
          exact Or.inl hP
      ·
        have h_d2024 : d = 2024 ∨ d = -2024 := by
          have h_abs : |d| = 2024 := h2024
          by_cases h_pos : 0 ≤ d
          · have h1' : |d| = d := abs_of_nonneg h_pos
            have h2 : d = 2024 := by linarith
            exact Or.inl h2
          · have h3 : d < 0 := by linarith
            have h4 : |d| = -d := abs_of_neg h3
            have h5 : d = -2024 := by linarith
            exact Or.inr h5
        rcases h_d2024 with (h_d_eq2024 | h_d_eq_neg2024)
        ·
          have h_cos : Real.cos ((d : ℝ) * α) = Real.cos α := round1_h4 α h21 d (by omega)
          have h_dot : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
            simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
          have h4 : xi * xj + yi * yj + h_val ^ 2 = 0 := by
            have h1 : xi * xj + yi * yj = Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) := by
              simp [xi, yi, xj, yj, Real.cos_sub]
            have h2 : Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) = Real.cos ((d : ℝ) * α) := by
              have h3 : ((i : ℝ) * α) - ((j : ℝ) * α) = (d : ℝ) * α := by
                simp [d] ; ring
              rw [h3]
            have h3 : xi * xj + yi * yj = Real.cos ((d : ℝ) * α) := by linarith
            have h5 : Real.cos ((d : ℝ) * α) = Real.cos α := h_cos
            nlinarith [h23]
          have hP : P := by
            have h_dot2 : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
              simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
            have h_goal : u ⬝ᵥ v = 0 := by
              calc
                u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := h_dot2
                _ = 0 := h4
            simpa [P] using h_goal
          exact Or.inl hP
        ·
          have h_cos : Real.cos ((d : ℝ) * α) = Real.cos α := round1_h3_a580cb α h21 d (by omega)
          have h_dot : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
            simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
          have h4 : xi * xj + yi * yj + h_val ^ 2 = 0 := by
            have h1 : xi * xj + yi * yj = Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) := by
              simp [xi, yi, xj, yj, Real.cos_sub]
            have h2 : Real.cos (((i : ℝ) * α) - ((j : ℝ) * α)) = Real.cos ((d : ℝ) * α) := by
              have h3 : ((i : ℝ) * α) - ((j : ℝ) * α) = (d : ℝ) * α := by
                simp [d] ; ring
              rw [h3]
            have h3 : xi * xj + yi * yj = Real.cos ((d : ℝ) * α) := by linarith
            have h5 : Real.cos ((d : ℝ) * α) = Real.cos α := h_cos
            nlinarith [h23]
          have hP : P := by
            have h_dot2 : u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := by
              simp [u, v, dotProduct, Fin.sum_univ_three, xi, yi, xj, yj, h_val] ; ring
            have h_goal : u ⬝ᵥ v = 0 := by
              calc
                u ⬝ᵥ v = xi * xj + yi * yj + h_val ^ 2 := h_dot2
                _ = 0 := h4
            simpa [P] using h_goal
          exact Or.inl hP
  rw [h_main1]
  exact h_main_goal

lemma round1_commutes_with_all (k : ℕ)
  (c : ℝ)
  (M : Matrix (Fin k) (Fin k) ℝ):
  (∀ (r : Fin k) (c1 : Fin k), M r c1 = if r = c1 then c else 0) →
  ∀ (N : Matrix (Fin k) (Fin k) ℝ), M * N = N * M := by
  intro hM N
  have h1 : M * N = N * M := by
    ext r s
    have h2 : (M * N) r s = c * (N r s) := by
      simp [Matrix.mul_apply, hM, mul_comm]
    have h3 : (N * M) r s = c * (N r s) := by
      simp [Matrix.mul_apply, hM, Finset.sum_ite_eq', mul_comm]
    rw [h2, h3]
  exact h1

lemma round1_h_main_goal (i : Fin 2025):
  let j : Fin 2025 := i + 2
  |(i : ℤ) - (j : ℤ)| ∉ ({0, 1, 2024} : Set ℤ) := by
  let x : ℤ := (i.val : ℤ)
  let j : Fin 2025 := i + 2
  let y : ℤ := (j.val : ℤ)
  have h_x_lt : x < 2025 := by
    have h1 : i.val < 2025 := i.is_lt
    have h2 : (x : ℤ) = (i.val : ℤ) := by rfl
    rw [h2]
    exact_mod_cast h1
  have h_main : |x - y| ≠ 0 ∧ |x - y| ≠ 1 ∧ |x - y| ≠ 2024 := by
    by_cases h : x + 2 < 2025
    ·
      have h_j_val : (j.val : ℤ) = x + 2 := by
        dsimp [j]
        rw [Fin.add_def]
        norm_num
        omega
      have hy : y = x + 2 := by
        simpa [y] using h_j_val
      rw [hy]
      norm_num
    ·
      have h' : x + 2 ≥ 2025 := by omega
      have h4 : x = 2023 ∨ x = 2024 := by omega
      rcases h4 with (h4 | h4)
      ·
        have h_j_val : (j.val : ℤ) = 0 := by
          dsimp [j]
          rw [Fin.add_def] ; norm_num ; omega
        have hy : y = 0 := by
          simpa [y] using h_j_val
        rw [hy, h4]
        norm_num
      ·
        have h_j_val : (j.val : ℤ) = 1 := by
          dsimp [j]
          rw [Fin.add_def] ; norm_num ; omega
        have hy : y = 1 := by
          simpa [y] using h_j_val
        rw [hy, h4]
        norm_num
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h_main

theorem round1_lemma_all_not_scalar (k : ℕ)
  (hk : k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ))
  (h_k_ne_1 : k ≠ 1)
  (A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ)
  (hA : ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)):
  ∀ (i : Fin 2025), ¬ (∃ (c : ℝ), ∀ (r : Fin k) (c1 : Fin k), (A i) r c1 = if r = c1 then c else 0) := by
  intro i
  intro h
  rcases h with ⟨c, hc⟩
  have h_commutes : ∀ (j : Fin 2025), A i * A j = A j * A i := by
    intro j
    exact round1_commutes_with_all k c (A i) hc (A j)
  let j : Fin 2025 := i + 2
  have h2 : A i * A j = A j * A i := h_commutes j
  have h3 : |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ) := (hA i j).mp h2
  have h4 : |(i : ℤ) - (j : ℤ)| ∉ ({0, 1, 2024} : Set ℤ) := round1_h_main_goal i
  exact h4 h3

lemma round1_h1_cf5543 (k : ℕ)
  (A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ)
  (hA : ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)):
  ∀ (m : Fin 2025), A m * A (m + 1) = A (m + 1) * A m := by
  intro m
  have h2 : |(m : ℤ) - ((m + 1 : Fin 2025) : ℤ)| ∈ ({0, 1, 2024} : Set ℤ) := by
    by_cases h : m.val < 2024
    ·
      have h' : m.val + 1 < 2025 := by omega
      have h3 : (m + 1 : Fin 2025).val = m.val + 1 := by
        simp [Fin.add_def, h']
      have h4 : ((m + 1 : Fin 2025) : ℤ) = (m : ℤ) + 1 := by
        norm_cast
      rw [h4]
      norm_num
    ·
      have h' : m.val = 2024 := by omega
      have h3 : (m + 1 : Fin 2025).val = 0 := by
        simp [Fin.add_def, h']
      have h4 : ((m + 1 : Fin 2025) : ℤ) = 0 := by
        norm_cast ; omega
      rw [h4]
      rw [show (m : ℤ) = 2024 by omega] ; norm_num
  have h4 := hA m (m + 1)
  tauto

lemma round1_h3_3819f1 (k : ℕ)
  (A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ)
  (hA : ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)):
  ∀ (m : Fin 2025), ¬ (A m * A (m + 2) = A (m + 2) * A m) := by
  intro m
  let x : ℤ := (m : ℤ)
  let y : ℤ := ((m + 2 : Fin 2025) : ℤ)
  have h_main : |x - y| ∉ ({0, 1, 2024} : Set ℤ) := by
    by_cases h : m.val + 2 < 2025
    ·
      have h61 : (m + 2 : Fin 2025).val = m.val + 2 := by
        rw [Fin.add_def]
        simp [Nat.mod_eq_of_lt h]
      have hy : y = ((m.val + 2 : ℤ)) := by
        dsimp [y]
        rw [show ((m + 2 : Fin 2025) : ℤ) = (((m + 2 : Fin 2025).val : ℤ)) from by exact rfl]
        rw [h61] ; norm_cast
      have h_x_eq : x = (m.val : ℤ) := by
        dsimp [x]
      have h_diff : x - y = -2 := by
        rw [h_x_eq, hy]
        simp [sub_eq_add_neg]
      have h10 : |x - y| = 2 := by
        rw [h_diff]
        norm_num
      rw [h10]
      decide
    ·
      have h7 : m.val ≥ 2023 := by omega
      have h8 : m.val = 2023 ∨ m.val = 2024 := by omega
      rcases h8 with (h8 | h8)
      ·
        have h91 : (m + 2 : Fin 2025).val = 0 := by
          rw [Fin.add_def]
          simp [h8]
        have hy : y = (0 : ℤ) := by
          dsimp [y]
          rw [show ((m + 2 : Fin 2025) : ℤ) = (((m + 2 : Fin 2025).val : ℤ)) from by exact rfl]
          rw [h91] ; norm_num
        have hx : x = (2023 : ℤ) := by
          dsimp [x] ; rw [h8] ; norm_num
        have h10 : |x - y| = 2023 := by
          rw [hx, hy] ; norm_num
        rw [h10]
        decide
      ·
        have h91 : (m + 2 : Fin 2025).val = 1 := by
          rw [Fin.add_def]
          simp [h8]
        have hy : y = (1 : ℤ) := by
          dsimp [y]
          rw [show ((m + 2 : Fin 2025) : ℤ) = (((m + 2 : Fin 2025).val : ℤ)) from by exact rfl]
          rw [h91] ; norm_num
        have hx : x = (2024 : ℤ) := by
          dsimp [x] ; rw [h8] ; norm_num
        have h10 : |x - y| = 2023 := by
          rw [hx, hy] ; norm_num
        rw [h10]
        decide
  have h5 : ¬ (A m * A (m + 2) = A (m + 2) * A m) := by
    have h6 := hA m (m + 2)
    tauto
  exact h5

lemma round2_commute_with_fixed_matrix_has_form (B X : Matrix (Fin 2) (Fin 2) ℝ)
  (hB_non_scalar : ¬ (∃ (c : ℝ), ∀ (r c1 : Fin 2), B r c1 = if r = c1 then c else 0))
  (hX : X * B = B * X):
  ∃ (c d : ℝ), X = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B := by
  let b00 := B 0 0
  let b01 := B 0 1
  let b10 := B 1 0
  let b11 := B 1 1
  let x00 := X 0 0
  let x01 := X 0 1
  let x10 := X 1 0
  let x11 := X 1 1
  have h1 : x01 * b10 = b01 * x10 := by
    have h := congr_fun (congr_fun hX 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢ ; linarith
  have h2 : x00 * b01 + x01 * b11 = b00 * x01 + b01 * x11 := by
    have h := congr_fun (congr_fun hX 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢ ; linarith
  have h3 : x10 * b00 + x11 * b10 = b10 * x00 + b11 * x10 := by
    have h := congr_fun (congr_fun hX 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢ ; linarith
  have h4 : x10 * b01 + x11 * b11 = b10 * x01 + b11 * x11 := by
    have h := congr_fun (congr_fun hX 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢ ; linarith
  have hB : ¬ (b01 = 0 ∧ b10 = 0 ∧ b00 = b11) := by
    intro h
    rcases h with ⟨h1, h2, h3⟩
    have h4 : ∃ (c : ℝ), ∀ (r c1 : Fin 2), B r c1 = if r = c1 then c else 0 := by
      refine ⟨b00, ?_⟩
      intro r c1
      fin_cases r <;> fin_cases c1 <;> simp [h3] <;> aesop
    exact hB_non_scalar h4
  by_cases h : b01 ≠ 0 ∨ b10 ≠ 0
  ·
    rcases h with (h_b01 | h_b10)
    ·
      let d : ℝ := x01 / b01
      have hdx01 : x01 = d * b01 := by
        have h5 : d * b01 = (x01 / b01) * b01 := by rfl
        have h6 : (x01 / b01) * b01 = x01 := by
          field_simp [h_b01]
        linarith
      have hdx10 : x10 = d * b10 := by
        have h5 : x01 * b10 = b01 * x10 := h1
        have h6 : (d * b01) * b10 = b01 * x10 := by
          rw [hdx01] at h5 ; exact h5
        have h7 : d * b10 = x10 := by
          apply (mul_right_inj' h_b01).mp
          linarith
        linarith
      have h_eq : x00 - d * b00 = x11 - d * b11 := by
        have h6 : x00 * b01 + x01 * b11 = b00 * x01 + b01 * x11 := h2
        have h7 : x00 * b01 + (d * b01) * b11 = b00 * (d * b01) + b01 * x11 := by
          rw [hdx01] at h6 ; exact h6
        have h8 : b01 * (x00 + d * b11) = b01 * (d * b00 + x11) := by
          linarith
        have h9 : x00 + d * b11 = d * b00 + x11 := by
          apply (mul_right_inj' h_b01).mp
          linarith
        linarith
      let c : ℝ := x00 - d * b00
      have h_eq1 : x00 = c + d * b00 := by
        simp [c]
      have h_eq4 : x11 = c + d * b11 := by
        simp [c] ; linarith
      have h_main : X = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B := by
        ext i j
        fin_cases i <;> fin_cases j
        <;> simp
        <;> linarith
      exact ⟨c, d, h_main⟩
    ·
      let d : ℝ := x10 / b10
      have hdx10 : x10 = d * b10 := by
        have h5 : d * b10 = (x10 / b10) * b10 := by rfl
        have h6 : (x10 / b10) * b10 = x10 := by
          field_simp [h_b10]
        linarith
      have hdx01 : x01 = d * b01 := by
        have h5 : x01 * b10 = b01 * x10 := h1
        have h6 : x01 * b10 = b01 * (d * b10) := by
          rw [hdx10] at h5 ; exact h5
        have h7 : x01 = d * b01 := by
          apply (mul_right_inj' h_b10).mp
          linarith
        linarith
      have h_eq : x00 - d * b00 = x11 - d * b11 := by
        have h6 : x10 * b00 + x11 * b10 = b10 * x00 + b11 * x10 := h3
        have h7 : (d * b10) * b00 + x11 * b10 = b10 * x00 + b11 * (d * b10) := by
          rw [hdx10] at h6 ; exact h6
        have h8 : b10 * (d * b00 + x11) = b10 * (x00 + d * b11) := by
          linarith
        have h9 : d * b00 + x11 = x00 + d * b11 := by
          apply (mul_right_inj' h_b10).mp
          linarith
        linarith
      let c : ℝ := x00 - d * b00
      have h_eq1 : x00 = c + d * b00 := by
        simp [c]
      have h_eq4 : x11 = c + d * b11 := by
        simp [c] ; linarith
      have h_main : X = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B := by
        ext i j
        fin_cases i <;> fin_cases j
        <;> simp
        <;> linarith
      exact ⟨c, d, h_main⟩
  ·
    have h_b01_eq : b01 = 0 := by tauto
    have h_b10_eq : b10 = 0 := by tauto
    have h_b00_ne_b11 : b00 ≠ b11 := by
      intro h_eq
      have h5 : b01 = 0 ∧ b10 = 0 ∧ b00 = b11 := ⟨h_b01_eq, h_b10_eq, h_eq⟩
      exact hB h5
    have hx01_eq_0 : x01 = 0 := by
      have h5 : x00 * b01 + x01 * b11 = b00 * x01 + b01 * x11 := h2
      have h6 : x01 * b11 = b00 * x01 := by
        rw [h_b01_eq] at h5 ; linarith
      have h7 : x01 * (b11 - b00) = 0 := by linarith
      have h8 : b11 - b00 ≠ 0 := by
        intro h9
        have h10 : b00 = b11 := by linarith
        apply h_b00_ne_b11
        exact h10
      have h10 : x01 = 0 := (mul_eq_zero.mp h7).resolve_right h8
      exact h10
    have hx10_eq_0 : x10 = 0 := by
      have h5 : x10 * b00 + x11 * b10 = b10 * x00 + b11 * x10 := h3
      simp [h_b10_eq] at h5
      have h6 : x10 * (b00 - b11) = 0 := by linarith
      have h7 : b00 - b11 ≠ 0 := by
        intro h8
        apply h_b00_ne_b11
        linarith
      have h9 : x10 = 0 := (mul_eq_zero.mp h6).resolve_right h7
      exact h9
    let d : ℝ := (x00 - x11) / (b00 - b11)
    let c : ℝ := x00 - d * b00
    have h_eq1 : x00 = c + d * b00 := by
      simp [c, d]
    have h_eq4 : x11 = c + d * b11 := by
      simp [c, d] ; field_simp [show (b00 - b11 : ℝ) ≠ 0 by intro h10; apply h_b00_ne_b11; linarith] ; ring
    have h_main : X = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B := by
      ext i j
      fin_cases i <;> fin_cases j
      ·
        simp ; linarith
      ·
        have h_goal : x01 = (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B) 0 1 := by
          have h : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B) 0 1 = d * b01 := by
            simp [b01]
          rw [h]
          rw [h_b01_eq] ; simp [hx01_eq_0]
        exact h_goal
      ·
        have h_goal : x10 = (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B) 1 0 := by
          have h : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B) 1 0 = d * b10 := by
            simp [b10]
          rw [h]
          rw [h_b10_eq] ; simp [hx10_eq_0]
        exact h_goal
      ·
        simp ; linarith
    exact ⟨c, d, h_main⟩

lemma round2_commute_aux (B : Matrix (Fin 2) (Fin 2) ℝ)
  (c d : ℝ):
  (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B) * B = B * (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d • B) := by
  ext i j
  fin_cases i <;> fin_cases j
  <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add]
  <;> ring

theorem round1_lemma_k_ne_2 (k : ℕ)
  (hk : k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ))
  (h_k_ne_1 : k ≠ 1)
  (A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ)
  (hA : ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ))
  (h_no_scalar : ∀ (i : Fin 2025), ¬ (∃ (c : ℝ), ∀ (r : Fin k) (c1 : Fin k), (A i) r c1 = if r = c1 then c else 0)):
  k ≠ 2 := by
  by_contra h_k_eq_2
  have h_k_eq_2' : k = 2 := h_k_eq_2
  subst h_k_eq_2'
  let m : Fin 2025 := 0
  have h1 : (A m) * (A (m + 1)) = (A (m + 1)) * (A m) := round1_h1_cf5543 (k := 2) (A := A) hA m
  have h5 : (A (m + 1)) * (A (m + 2)) = (A (m + 2)) * (A (m + 1)) := round1_h1_cf5543 (k := 2) (A := A) hA (m + 1)
  have h_eq1 : ∃ (c1 d1 : ℝ), (A (m + 1)) = c1 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d1 • (A m) := by
    exact round2_commute_with_fixed_matrix_has_form (A m) (A (m + 1)) (h_no_scalar m) h1.symm
  have h_eq2 : ∃ (c2 d2 : ℝ), (A (m + 2)) = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d2 • (A (m + 1)) := by
    exact round2_commute_with_fixed_matrix_has_form (A (m + 1)) (A (m + 2)) (h_no_scalar (m + 1)) h5.symm
  rcases h_eq1 with ⟨c1, d1, h_eq1⟩
  rcases h_eq2 with ⟨c2, d2, h_eq2⟩
  set B := (A m : Matrix (Fin 2) (Fin 2) ℝ) with hB
  set X := (A (m + 1) : Matrix (Fin 2) (Fin 2) ℝ) with hX
  set Y := (A (m + 2) : Matrix (Fin 2) (Fin 2) ℝ) with hY
  have h_eq1' : X = c1 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d1 • B := by
    simpa [hB, hX] using h_eq1
  have h_eq2' : Y = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d2 • X := by
    simpa [hX, hY] using h_eq2
  let c3 : ℝ := c2 + d2 * c1
  let d3 : ℝ := d2 * d1
  have h_step1 : d2 • (c1 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (d2 * c1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [smul_smul]
  have h_eq_Y : Y = c3 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d3 • B := by
    calc
      Y = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d2 • X := h_eq2'
      _ = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d2 • (c1 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d1 • B) := by rw [h_eq1']
      _ = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (d2 • (c1 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + d2 • (d1 • B)) := by
        rw [smul_add]
      _ = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (d2 * c1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d2 • (d1 • B) := by
        rw [h_step1]
        abel
      _ = c2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (d2 * c1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (d2 * d1) • B := by
        have h6 : d2 • (d1 • B) = (d2 * d1) • B := by
          rw [smul_smul]
        rw [h6]
      _ = (c2 + d2 * c1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (d2 * d1) • B := by
        simp [add_smul]
  have h_step2 : (c3 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d3 • B) * B = B * (c3 • (1 : Matrix (Fin 2) (Fin 2) ℝ) + d3 • B) :=
    round2_commute_aux B c3 d3
  have h_comm : Y * B = B * Y := by
    rw [h_eq_Y] at *
    exact h_step2
  have h_comm' : (A (m + 2)) * (A m) = (A m) * (A (m + 2)) := by
    simpa [hB, hY] using h_comm
  have h3 : ¬ ((A m) * (A (m + 2)) = (A (m + 2)) * (A m)) := round1_h3_3819f1 (k := 2) (A := A) hA m
  have h4 : (A m) * (A (m + 2)) = (A (m + 2)) * (A m) := h_comm'.symm
  exact h3 h4

theorem three_is_in_set :
  3 > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin 3) (Fin 3) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ) := by
  have h2 := round1_h2'
  rcases h2 with ⟨α, h, h21, h22, h23⟩
  set x : Fin 2025 → ℝ := fun (i : Fin 2025) => Real.cos ((i : ℝ) * α) with hx_def
  set y : Fin 2025 → ℝ := fun (i : Fin 2025) => Real.sin ((i : ℝ) * α) with hy_def
  set z : Fin 2025 → ℝ := fun (i : Fin 2025) => h with hz_def
  set A : Fin 2025 → Matrix (Fin 3) (Fin 3) ℝ := fun (i : Fin 2025) =>
    fun (r s : Fin 3) =>
      match r, s with
      | 0, 0 => (x i) * (x i)
      | 0, 1 => (x i) * (y i)
      | 0, 2 => (x i) * (z i)
      | 1, 0 => (y i) * (x i)
      | 1, 1 => (y i) * (y i)
      | 1, 2 => (y i) * (z i)
      | 2, 0 => (z i) * (x i)
      | 2, 1 => (z i) * (y i)
      | 2, 2 => (z i) * (z i) with hA_def
  have h3 := round1_h3' α h h21 h22 h23
  constructor
  ·
    norm_num
  ·
    exact ⟨A, h3⟩

theorem three_is_lower_bound (k : ℕ)
  (hk : k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)):
  3 ≤ k := by
  have h1 : k ≠ 1 := by
    exact round1_lemma_k_ne_1 k hk
  rcases hk with ⟨hk_pos, h_exists⟩
  rcases h_exists with ⟨A, hA⟩
  have h_no_scalar : ∀ (i : Fin 2025), ¬ (∃ (c : ℝ), ∀ (r : Fin k) (c1 : Fin k), (A i) r c1 = if r = c1 then c else 0) := by
    exact round1_lemma_all_not_scalar k ⟨hk_pos, ⟨A, hA⟩⟩ h1 A hA
  have h2 : k ≠ 2 := by
    exact round1_lemma_k_ne_2 k ⟨hk_pos, ⟨A, hA⟩⟩ h1 A hA h_no_scalar
  have h3 : k > 0 := hk_pos
  omega

theorem putnam_2025_a4 :
  IsLeast {k : ℕ | k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)} 3 := by
      have h1 : (3 : ℕ) ∈ {k : ℕ | k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)} := by
        exact three_is_in_set
      have h2 : ∀ k : ℕ, k ∈ {k : ℕ | k > 0 ∧ ∃ A : Fin 2025 → Matrix (Fin k) (Fin k) ℝ, ∀ i j, A i * A j = A j * A i ↔ |(i : ℤ) - (j : ℤ)| ∈ ({0, 1, 2024} : Set ℤ)} → 3 ≤ k := by
        intro k hk
        exact three_is_lower_bound k hk
      exact ⟨h1, fun k hk => h2 k hk⟩

end Putnam2025A4
