import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open Classical Set Real

namespace Putnam2025A2

theorem round1_lemma1 :
  ∀ (x : ℝ), 0 ≤ x ∧ x ≤ π / 2 → cos x ≥ 1 - (2 / π) * x := by
  intro x h
  have hx₀ : 0 ≤ x := h.1
  have hx : x ≤ π / 2 := h.2
  have h_main : 1 - (2 / π) * x ≤ cos x := by
    exact Real.one_sub_mul_le_cos hx₀ hx
  linarith

lemma round1_h_neg (x : ℝ)
  (hx1 : 0 < x)
  (hx2 : x ≤ Real.pi / 2):
  x * Real.cos x - Real.sin x < 0 := by
  have h_pos : 0 < Real.pi := Real.pi_pos
  let h : ℝ → ℝ := fun x => x * Real.cos x - Real.sin x
  have h_diff : Differentiable ℝ h := by
    fun_prop
  have h_cont : ContinuousOn h (Set.Icc 0 x) := by
    apply Continuous.continuousOn
    fun_prop
  have h_diff2 : DifferentiableOn ℝ h (Set.Ioo 0 x) := h_diff.differentiableOn
  have h_main : ∃ c ∈ Set.Ioo 0 x, deriv h c = (h x - h 0) / (x - 0) := by
    apply exists_deriv_eq_slope h (show (0 : ℝ) < x by linarith) h_cont h_diff2
  rcases h_main with ⟨c, hc, hceq⟩
  have hc1 : 0 < c := hc.1
  have hc2 : c < x := hc.2
  have hc3 : c < Real.pi / 2 := by linarith
  have h5 : Real.sin c > 0 := Real.sin_pos_of_pos_of_lt_pi hc1 (by linarith [h_pos])
  have h_deriv : ∀ (z : ℝ), deriv h z = - (z * Real.sin z) := by
    intro z
    simp [h]
  have h6 : deriv h c < 0 := by
    rw [h_deriv c]
    nlinarith
  have h7 : (h x - h 0) / (x - 0) = deriv h c := by exact hceq.symm
  have h8 : h 0 = 0 := by norm_num [h]
  have h9 : (h x - 0) / x = deriv h c := by simpa [h8] using hceq.symm
  have h10 : h x = (deriv h c) * x := by
    field_simp [hx1.ne'] at h9 ⊢ ; linarith
  have h11 : h x < 0 := by
    rw [h10]
    nlinarith
  exact h11

lemma round1_f_strict_anti :
  StrictAntiOn (fun x : ℝ => Real.sin x / x) (Set.Ioo 0 (Real.pi / 2)) := by
  let f : ℝ → ℝ := fun x => Real.sin x / x
  have h_cont1 : Continuous (fun x : ℝ => Real.sin x) := by fun_prop
  have h_cont2 : Continuous (fun x : ℝ => x) := by fun_prop
  have h_cont : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := by
    apply ContinuousOn.div
    · exact h_cont1.continuousOn
    · exact h_cont2.continuousOn
    · intro x hx
      exact hx.1.ne'
  have h1 : ∀ z ∈ Set.Ioo 0 (Real.pi / 2), deriv f z < 0 := by
    intro z hz
    have hz1 : 0 < z := hz.1
    have hz2 : z < Real.pi / 2 := hz.2
    have h2 : deriv f z = (z * Real.cos z - Real.sin z) / (z ^ 2) := by
      simp [f, div_eq_mul_inv]
      field_simp
      ring_nf
    rw [h2]
    have h3 : z * Real.cos z - Real.sin z < 0 := round1_h_neg z hz1 (by linarith)
    have h4 : 0 < z ^ 2 := by positivity
    exact div_neg_of_neg_of_pos h3 h4
  have h_main : StrictAntiOn f (Set.Ioo 0 (Real.pi / 2)) := by
    have h_inter : interior (Set.Ioo 0 (Real.pi / 2)) = Set.Ioo 0 (Real.pi / 2) := by
      simp
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (Real.pi / 2)) h_cont
    rw [h_inter]
    exact h1
  exact h_main

lemma round2_sin_div_ge (u : ℝ)
  (h1 : 0 < u)
  (h2 : u ≤ Real.pi / 4):
  Real.sin u / u ≥ Real.sin (Real.pi / 4) / (Real.pi / 4) := by
  have h3 : u < Real.pi / 2 := by linarith [Real.pi_pos]
  have h4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have h5 : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  by_cases h6 : u < Real.pi / 4
  ·
    have h7 : u ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h1, h3⟩
    have h8 : (Real.pi / 4 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h5, h4⟩
    have h9 : Real.sin u / u > Real.sin (Real.pi / 4) / (Real.pi / 4) := round1_f_strict_anti h7 h8 h6
    linarith
  ·
    have h7 : u = Real.pi / 4 := by linarith
    rw [h7]

lemma round1_sin_sq_main (u : ℝ)
  (hu1 : 0 ≤ u)
  (hu2 : u ≤ Real.pi / 4):
  Real.sin u ^ 2 ≥ (8 / Real.pi ^ 2) * u ^ 2 := by
  by_cases h : u = 0
  ·
    rw [h]
    norm_num
  ·
    have h_pos : 0 < u := by
      by_contra h'
      have : u ≤ 0 := by linarith
      have h'' : u = 0 := by linarith
      contradiction
    have h2 : u < Real.pi / 2 := by linarith [Real.pi_pos]
    have h3 : 0 < u := h_pos
    have h4 : u ≤ Real.pi / 4 := hu2
    have h6 : Real.sin u / u ≥ Real.sin (Real.pi / 4) / (Real.pi / 4) := round2_sin_div_ge u h3 h4
    have h7 : Real.sin u ≥ u * (Real.sin (Real.pi / 4) / (Real.pi / 4)) := by
      have h71 : 0 < u := h3
      have h72 : Real.sin u / u ≥ Real.sin (Real.pi / 4) / (Real.pi / 4) := h6
      have h73 : Real.sin u ≥ u * (Real.sin (Real.pi / 4) / (Real.pi / 4)) := by
        calc
          Real.sin u = u * (Real.sin u / u) := by field_simp [h71.ne']
          _ ≥ u * (Real.sin (Real.pi / 4) / (Real.pi / 4)) := by gcongr
      exact h73
    have h8 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [Real.sin_pi_div_four]
    have h9 : Real.sin (Real.pi / 4) / (Real.pi / 4) = (2 * Real.sqrt 2) / Real.pi := by
      rw [h8] ; field_simp ; ring_nf
    rw [h9] at h7
    have h10 : Real.sin u ≥ u * ((2 * Real.sqrt 2) / Real.pi) := h7
    have h11 : 0 ≤ Real.sin u := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
    have h12 : 0 ≤ u * ((2 * Real.sqrt 2) / Real.pi) := by positivity
    have h13 : (Real.sin u) ^ 2 ≥ (u * ((2 * Real.sqrt 2) / Real.pi)) ^ 2 := by nlinarith [h10, h11, h12]
    have h14 : (u * ((2 * Real.sqrt 2) / Real.pi)) ^ 2 = (8 / Real.pi ^ 2) * u ^ 2 := by
      field_simp ; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h14] at h13
    linarith

lemma round1_h_main1 :
  ∀ (t : ℝ), 0 ≤ t ∧ t ≤ Real.pi / 2 → Real.cos t ≤ 1 - (4 / Real.pi ^ 2) * t ^ 2 := by
  intro t ht
  have h1 : 0 ≤ t := ht.1
  have h2 : t ≤ Real.pi / 2 := ht.2
  set u := t / 2 with hu
  have hu1 : 0 ≤ u := by linarith
  have hu2 : u ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hsin_sq : Real.sin u ^ 2 ≥ (8 / Real.pi ^ 2) * u ^ 2 := round1_sin_sq_main u hu1 hu2
  have h10 : 1 - Real.cos t = 2 * Real.sin u ^ 2 := by
    have h11 : t = 2 * u := by
      rw [show u = t / 2 by rfl] ; ring
    rw [h11]
    have h12 : 1 - Real.cos (2 * u) = 2 * Real.sin u ^ 2 := by
      have h13 : Real.cos (2 * u) = 2 * Real.cos u ^ 2 - 1 := Real.cos_two_mul u
      rw [h13]
      ring_nf
      nlinarith [Real.sin_sq_add_cos_sq u]
    exact h12
  have h14 : u = t / 2 := by rfl
  have h15 : (8 : ℝ) / Real.pi ^ 2 * u ^ 2 = (2 : ℝ) / Real.pi ^ 2 * t ^ 2 := by
    rw [h14]
    ring_nf
  have h16 : Real.sin u ^ 2 ≥ (2 : ℝ) / Real.pi ^ 2 * t ^ 2 := by
    calc
      Real.sin u ^ 2 ≥ (8 / Real.pi ^ 2) * u ^ 2 := hsin_sq
      _ = (2 : ℝ) / Real.pi ^ 2 * t ^ 2 := h15
  have h17 : 2 * Real.sin u ^ 2 ≥ (4 : ℝ) / Real.pi ^ 2 * t ^ 2 := by
    calc
      2 * Real.sin u ^ 2 ≥ 2 * ((2 : ℝ) / Real.pi ^ 2 * t ^ 2) := by gcongr
      _ = (4 : ℝ) / Real.pi ^ 2 * t ^ 2 := by ring
  have h18 : 1 - Real.cos t ≥ (4 / Real.pi ^ 2) * t ^ 2 := by
    linarith [h10, h17]
  linarith

theorem round1_lemma5_helper :
  ∀ (t : ℝ), -π / 2 ≤ t ∧ t ≤ π / 2 → cos t ≤ 1 - (4 / π ^ 2) * t ^ 2 := by
  have h_main1 := round1_h_main1
  intro t ht
  have h1 : -Real.pi / 2 ≤ t := ht.1
  have h2 : t ≤ Real.pi / 2 := ht.2
  by_cases h3 : 0 ≤ t
  ·
    have h4 : 0 ≤ t := h3
    have h5 : t ≤ Real.pi / 2 := h2
    have h6 : 0 ≤ t ∧ t ≤ Real.pi / 2 := ⟨h4, h5⟩
    exact h_main1 t h6
  ·
    have h4 : t < 0 := by linarith
    set s := -t with hs
    have hs1 : 0 ≤ s := by linarith
    have hs2 : s ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have h_main : Real.cos s ≤ 1 - (4 / Real.pi ^ 2) * s ^ 2 := h_main1 s ⟨hs1, hs2⟩
    have h_eq1 : Real.cos t = Real.cos s := by
      have h9 : s = -t := by linarith
      have h10 : Real.cos s = Real.cos (-t) := by rw [h9]
      have h11 : Real.cos (-t) = Real.cos t := Real.cos_neg t
      have h12 : Real.cos s = Real.cos t := by
        rw [h10, h11]
      exact h12.symm
    have h_eq2 : t ^ 2 = s ^ 2 := by
      have h9 : s = -t := by linarith
      rw [h9] ; ring
    rw [h_eq1, h_eq2]
    exact h_main

lemma round1_h_prime (h1 : ∀ (x : ℝ), 0 ≤ x ∧ x ≤ π / 2 → cos x ≥ 1 - (2 / π) * x):
  ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) (π / 2) → 2 * t - π + π * Real.cos t ≥ 0 := by
  intro t ht
  have h2 : 0 ≤ t := ht.1
  have h3 : t ≤ π / 2 := ht.2
  have h4 : Real.cos t ≥ 1 - (2 / π) * t := h1 t ⟨h2, h3⟩
  have h5 : 0 < π := Real.pi_pos
  have h6 : π * Real.cos t ≥ π - 2 * t := by
    calc
      π * Real.cos t ≥ π * (1 - (2 / π) * t) := by gcongr
      _ = π - 2 * t := by
        field_simp [h5.ne']
  linarith

lemma round1_h_main3 (h1 : ∀ (x : ℝ), 0 ≤ x ∧ x ≤ π / 2 → cos x ≥ 1 - (2 / π) * x):
  ∀ (x : ℝ), x ∈ Icc (0 : ℝ) (π / 2) → sin x ≥ (1 / π) * x * (π - x) := by
  have h_prime : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) (π / 2) → 2 * t - π + π * Real.cos t ≥ 0 :=
    round1_h_prime h1
  let f : ℝ → ℝ := fun t ↦ π * Real.sin t - π * t + t^2
  have h_deriv : ∀ (t : ℝ), HasDerivAt f (π * Real.cos t - π + 2 * t) t := by
    intro t
    have h12 : HasDerivAt (fun t : ℝ ↦ π * Real.sin t) (π * Real.cos t) t := by
      simpa using HasDerivAt.const_mul π (Real.hasDerivAt_sin t)
    have h13 : HasDerivAt (fun t : ℝ ↦ π * t) (π) t := by
      simpa using (hasDerivAt_id t).const_mul π
    have h14 : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h15 : HasDerivAt f (π * Real.cos t - π + 2 * t) t := by
      simpa [f] using (h12.sub h13).add h14
    exact h15
  intro x hx
  have h2 : 0 ≤ x := hx.1
  have h3 : x ≤ π / 2 := hx.2
  by_cases h_x0 : x = 0
  · rw [h_x0]
    simp
  · have h_pos : 0 < x := by
      exact lt_of_le_of_ne h2 (Ne.symm h_x0)
    have h_cont : ContinuousOn f (Set.Icc 0 x) := by
      fun_prop
    have h_diff_at : ∀ (t : ℝ), DifferentiableAt ℝ f t := fun t => (h_deriv t).differentiableAt
    have h_diff_on : DifferentiableOn ℝ f (Set.Ioo 0 x) := by
      intro t ht
      have h : DifferentiableAt ℝ f t := h_diff_at t
      exact h.differentiableWithinAt
    have h4 : ∃ c ∈ Set.Ioo (0 : ℝ) x, deriv f c = (f x - f 0) / (x - 0) := by
      exact exists_deriv_eq_slope (f := f) (a := (0 : ℝ)) (b := x) (h_pos) h_cont h_diff_on
    rcases h4 with ⟨c, hc, h_eq⟩
    have hc1 : 0 < c := hc.1
    have hc2 : c < x := hc.2
    have hc3 : c ∈ Set.Icc (0 : ℝ) (π / 2) := by
      constructor <;> linarith [h2, h3, hc1, hc2]
    have h5 : deriv f c = π * Real.cos c - π + 2 * c := by
      exact (h_deriv c).deriv
    have h6 : 2 * c - π + π * Real.cos c ≥ 0 := h_prime c hc3
    have h7 : deriv f c ≥ 0 := by
      rw [h5]
      linarith
    have h8 : (f x - f 0) / (x - 0) ≥ 0 := by
      rw [←h_eq] ; exact h7
    have h9 : x - 0 > 0 := by linarith
    have h10 : f x - f 0 ≥ 0 := by
      have h11 : (f x - f 0) / (x - 0) ≥ 0 := h8
      have h12 : (x - 0) > 0 := h9
      have h13 : (f x - f 0) ≥ 0 := by
        calc
          (f x - f 0) = ((f x - f 0) / (x - 0)) * (x - 0) := by
            field_simp [h12.ne']
          _ ≥ 0 := by
            apply mul_nonneg h11
            linarith
      exact h13
    have h11 : f 0 = 0 := by
      simp [f]
    have h12 : f x ≥ 0 := by linarith
    have h13 : π * Real.sin x - π * x + x ^ 2 ≥ 0 := h12
    have h14 : 0 < π := Real.pi_pos
    have h15 : Real.sin x ≥ (1 / π) * x * (π - x) := by
      have h16 : π * Real.sin x ≥ x * (π - x) := by linarith
      calc
        Real.sin x = (π * Real.sin x) / π := by
          field_simp [h14.ne']
        _ ≥ (x * (π - x)) / π := by gcongr
        _ = (1 / π) * x * (π - x) := by ring
    exact h15

theorem round1_lemma1_implies_lemma2_ineq (h1 : ∀ (x : ℝ), 0 ≤ x ∧ x ≤ π / 2 → cos x ≥ 1 - (2 / π) * x):
  ∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → sin x ≥ (1 / π) * x * (π - x) := by
  have h_main3 : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) (π / 2) → sin x ≥ (1 / π) * x * (π - x) :=
    round1_h_main3 h1
  intro x hx
  have h2 : 0 ≤ x := hx.1
  have h3 : x ≤ π := hx.2
  by_cases h4 : x ≤ π / 2
  ·
    have h5 : x ∈ Icc (0 : ℝ) (π / 2) := ⟨h2, h4⟩
    exact h_main3 x h5
  ·
    have h4' : x > π / 2 := by linarith
    have h6 : 0 ≤ π - x := by linarith [Real.pi_pos]
    have h7 : π - x ≤ π / 2 := by linarith [Real.pi_pos]
    have h8 : (π - x) ∈ Icc (0 : ℝ) (π / 2) := ⟨h6, h7⟩
    have h9 : sin x = sin (π - (π - x)) := by
      ring_nf
    have h10 : sin (π - (π - x)) = sin (π - x) := by
      rw [Real.sin_pi_sub]
    have h11 : sin x = sin (π - x) := by
      rw [h9, h10]
    rw [h11]
    have h12 : sin (π - x) ≥ (1 / π) * (π - x) * (π - (π - x)) := h_main3 (π - x) h8
    have h13 : (1 / π) * (π - x) * (π - (π - x)) = (1 / π) * x * (π - x) := by
      ring
    rw [h13] at h12
    exact h12

lemma round1_h_main1_bc4a57 (x : ℝ):
  1 - (4 / π ^ 2) * (x - π / 2) ^ 2 = (4 / π ^ 2) * x * (π - x) := by
  field_simp [pow_two]
  ring_nf

lemma round1_h_main2 (x : ℝ):
  Real.cos (x - π / 2) = Real.sin x := by
  rw [Real.cos_sub]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem round1_lemma5_helper_implies_lemma5_ineq (h2 : ∀ (t : ℝ), -π / 2 ≤ t ∧ t ≤ π / 2 → cos t ≤ 1 - (4 / π ^ 2) * t ^ 2):
  ∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → sin x ≤ (4 / π ^ 2) * x * (π - x) := by
  intro x hx
  have h3 : 0 ≤ x := hx.1
  have h4 : x ≤ π := hx.2
  have h5 : -π / 2 ≤ x - π / 2 := by linarith [Real.pi_pos]
  have h6 : x - π / 2 ≤ π / 2 := by linarith [Real.pi_pos]
  have h7 : -π / 2 ≤ (x - π / 2) ∧ (x - π / 2) ≤ π / 2 := ⟨h5, h6⟩
  have h8 : Real.cos (x - π / 2) ≤ 1 - (4 / π ^ 2) * (x - π / 2) ^ 2 := h2 (x - π / 2) h7
  have h9 : Real.sin x ≤ 1 - (4 / π ^ 2) * (x - π / 2) ^ 2 := by
    have h10 : Real.cos (x - π / 2) = Real.sin x := round1_h_main2 x
    linarith
  have h11 : 1 - (4 / π ^ 2) * (x - π / 2) ^ 2 = (4 / π ^ 2) * x * (π - x) := round1_h_main1_bc4a57 x
  rw [h11] at h9
  exact h9

lemma round1_h2_e6c986 (a : ℝ)
  (h : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → a * x * (π - x) ≤ sin x):
  ∀ (z : ℝ), 0 < z → z < π → a * (π - z) < 1 := by
  intro z hz_pos hz_lt_pi
  have h_x_pos : 0 < π - z := by linarith [Real.pi_pos]
  have h_x_def : π - z > 0 := h_x_pos
  have h_x_lt_pi : π - z < π := by linarith [Real.pi_pos]
  have h_x_nonneg : 0 ≤ π - z := by linarith [Real.pi_pos]
  have h_x_in_Icc : (π - z) ∈ Icc (0 : ℝ) π := ⟨h_x_nonneg, by linarith [Real.pi_pos]⟩
  have h_main : a * ((π - z)) * (π - (π - z)) ≤ sin (π - z) := h (π - z) h_x_in_Icc
  have h_sin : sin (π - z) = sin z := by rw [Real.sin_pi_sub]
  have h4 : π - (π - z) = z := by ring
  rw [h4, h_sin] at h_main
  have h5 : a * (π - z) * z ≤ sin z := h_main
  have h6 : sin z < z := Real.sin_lt (by linarith [Real.pi_pos])
  have h7 : a * (π - z) * z < z := by linarith
  have h8 : 0 < z := hz_pos
  have h9 : a * (π - z) < 1 := by
    nlinarith
  exact h9

theorem round1_lemma3_optimality_lower :
  ∀ (a : ℝ), (∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → a * x * (π - x) ≤ sin x) → a ≤ 1 / π := by
  intro a h
  have h_main1 : ∀ (z : ℝ), 0 < z → z < π → a * (π - z) < 1 := round1_h2_e6c986 a h
  by_contra h_contra
  have h_contra' : a > 1 / π := by linarith
  have ha_pos : 0 < a := by
    have h1 : 0 < 1 / π := by positivity
    linarith
  have h11 : 1 < a * π := by
    have h12 : a > 1 / π := h_contra'
    have h13 : 0 < π := Real.pi_pos
    have h14 : a * π > (1 / π) * π := mul_lt_mul_of_pos_right h12 h13
    have h15 : (1 / π) * π = 1 := by
      field_simp [h13.ne']
    rw [h15] at h14
    linarith
  have h10 : 0 < 1 / a := by positivity
  have h11' : 1 / a < π := by
    have h12 : 0 < a := ha_pos
    have h13 : a * (1 / a) = 1 := by
      field_simp [h12.ne']
    nlinarith
  set z' := π - (1 / a) with hz'
  have hz'_pos : 0 < z' := by
    have h15 : 1 / a < π := h11'
    linarith [Real.pi_pos]
  have hz'_lt_pi : z' < π := by
    have h15 : 0 < 1 / a := h10
    linarith [Real.pi_pos]
  have h16 : 0 < π - z' := by
    have h17 : z' = π - 1 / a := by simp [hz']
    rw [h17]
    linarith
  have h18 : π - z' = 1 / a := by
    simp [hz']
  have h19 : a * (π - z') < 1 := h_main1 z' hz'_pos hz'_lt_pi
  rw [h18] at h19
  have h20 : a * (1 / a) < 1 := h19
  have h21 : a * (1 / a) = 1 := by
    field_simp [ha_pos.ne']
  rw [h21] at h20
  linarith

lemma round1_h_main (b : ℝ)
  (h : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → b * x * (π - x) ≥ sin x):
  b ≥ 4 / π ^ 2 := by
  have h1 : (π / 2 : ℝ) ∈ Icc (0 : ℝ) π := by
    constructor
    ·
      linarith [Real.pi_pos]
    ·
      linarith [Real.pi_pos]
  have h2 := h (π / 2) h1
  have h3 : b * (π / 2 : ℝ) * (π - (π / 2 : ℝ)) ≥ sin (π / 2) := h2
  have h4 : (π / 2 : ℝ) * (π - (π / 2 : ℝ)) = (π ^ 2) / 4 := by
    ring
  have h5 : b * (π / 2 : ℝ) * (π - (π / 2 : ℝ)) = b * ((π / 2 : ℝ) * (π - (π / 2 : ℝ))) := by ring
  rw [h5] at h3
  rw [h4] at h3
  have h6 : sin (π / 2) = 1 := by
    rw [Real.sin_pi_div_two]
  rw [h6] at h3
  have h7 : 0 < (π ^ 2 : ℝ) / 4 := by positivity
  have h8 : b * ((π ^ 2 : ℝ) / 4) ≥ 1 := h3
  have h9 : b ≥ 4 / π ^ 2 := by
    calc
      b = (b * ((π ^ 2 : ℝ) / 4)) / ((π ^ 2 : ℝ) / 4) := by
        field_simp [h7.ne']
      _ ≥ 1 / ((π ^ 2 : ℝ) / 4) := by gcongr
      _ = 4 / π ^ 2 := by
        field_simp [Real.pi_ne_zero]
  exact h9

theorem round1_lemma4_optimality_upper :
  ∀ (b : ℝ), (∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → b * x * (π - x) ≥ sin x) → b ≥ 4 / π ^ 2 := by
  intro b h
  exact round1_h_main b h

theorem putnam_2025_a2 :
  IsGreatest {a : ℝ | ∀ x ∈ Icc 0 π, a * x * (π - x) ≤ sin x} (1 / π) ∧
  IsLeast {b : ℝ | ∀ x ∈ Icc 0 π, b * x * (π - x) ≥ sin x} (4 / π ^ 2) := by
      have lemma2_ineq : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → sin x ≥ (1 / π) * x * (π - x) := by
        exact round1_lemma1_implies_lemma2_ineq (round1_lemma1)
      have lemma5_ineq : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → sin x ≤ (4 / π ^ 2) * x * (π - x) := by
        exact round1_lemma5_helper_implies_lemma5_ineq (round1_lemma5_helper)
      have optimality_lower : ∀ (a : ℝ), (∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → a * x * (π - x) ≤ sin x) → a ≤ 1 / π := by
        exact round1_lemma3_optimality_lower
      have optimality_upper : ∀ (b : ℝ), (∀ (x : ℝ), x ∈ Icc (0 : ℝ) π → b * x * (π - x) ≥ sin x) → b ≥ 4 / π ^ 2 := by
        exact round1_lemma4_optimality_upper
      constructor
      ·
        have h11 : (1 / π) ∈ {a : ℝ | ∀ x ∈ Icc 0 π, a * x * (π - x) ≤ sin x} := by
          intro x hx
          have h111 := lemma2_ineq x hx
          have h112 : (1 / π) * x * (π - x) ≤ sin x := by linarith
          exact h112
        have h12 : ∀ a ∈ {a : ℝ | ∀ x ∈ Icc 0 π, a * x * (π - x) ≤ sin x}, a ≤ (1 / π) := by
          intro a ha
          exact optimality_lower a ha
        exact ⟨h11, fun a ha => h12 a ha⟩
      ·
        have h21 : (4 / π ^ 2) ∈ {b : ℝ | ∀ x ∈ Icc 0 π, b * x * (π - x) ≥ sin x} := by
          intro x hx
          have h211 := lemma5_ineq x hx
          have h212 : (4 / π ^ 2) * x * (π - x) ≥ sin x := by linarith
          exact h212
        have h22 : ∀ b ∈ {b : ℝ | ∀ x ∈ Icc 0 π, b * x * (π - x) ≥ sin x}, (4 / π ^ 2) ≤ b := by
          intro b hb
          exact optimality_upper b (fun x hx => hb x hx)
        exact ⟨h21, fun b hb => h22 b hb⟩

end Putnam2025A2
