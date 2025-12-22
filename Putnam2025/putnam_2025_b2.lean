import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Real.StarOrdered
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open BigOperators Real Nat Topology Rat MeasureTheory Set Real

namespace Putnam2025B2

lemma nonneg_integrand (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (x u : ℝ)
  (hx : x ∈ Icc (0 : ℝ) 1)
  (hu : u ∈ Icc (0 : ℝ) 1):
  (x - u) * f x * f u * (f x - f u) ≥ 0 := by
  have h1 : 0 ≤ f x := hf x hx
  have h2 : 0 ≤ f u := hf u hu
  have h3 : 0 ≤ f x * f u := by positivity
  have h4 : (x - u) * (f x - f u) ≥ 0 := by
    by_cases h5 : x ≥ u
    ·
      have h6 : x - u ≥ 0 := by linarith
      have h7 : f x ≥ f u := by
        apply hfm.monotone
        linarith
      have h8 : f x - f u ≥ 0 := by linarith
      have h9 : (x - u) * (f x - f u) ≥ 0 := by positivity
      exact h9
    ·
      have h5' : x < u := by linarith
      have h6 : x - u < 0 := by linarith
      have h7 : f x < f u := hfm h5'
      have h8 : f x - f u < 0 := by linarith
      have h9 : (x - u) * (f x - f u) ≥ 0 := by nlinarith
      exact h9
  have h10 : (x - u) * f x * f u * (f x - f u) = ((x - u) * (f x - f u)) * (f x * f u) := by ring
  rw [h10]
  exact mul_nonneg h4 h3

lemma hI1 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f):
  (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u) =
    (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) * (∫ (x : ℝ) in (0)..1, f x) := by
  let A := (∫ (x : ℝ) in (0)..1, f x)
  have h : (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u) =
    ∫ (x : ℝ) in (0)..1, (x * f x ^ 2) * (∫ (u : ℝ) in (0)..1, f u) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have h' : ∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u = (x * f x ^ 2) * (∫ (u : ℝ) in (0)..1, f u) := by
      rw [intervalIntegral.integral_const_mul]
    exact h'
  rw [h]
  have h2 : ∫ (x : ℝ) in (0)..1, (x * f x ^ 2) * A = A * ∫ (x : ℝ) in (0)..1, x * f x ^ 2 := by
    have h3 : ∫ (x : ℝ) in (0)..1, (x * f x ^ 2) * A = ∫ (x : ℝ) in (0)..1, A * (x * f x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [h3]
    rw [intervalIntegral.integral_const_mul]
  rw [h2] ; ring

lemma hI2 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f):
  (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2) =
    (∫ (x : ℝ) in (0)..1, x * f x) * (∫ (x : ℝ) in (0)..1, (f x) ^ 2) := by
  let C := (∫ (x : ℝ) in (0)..1, (f x) ^ 2)
  have h : (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2) =
    ∫ (x : ℝ) in (0)..1, (x * f x) * (∫ (u : ℝ) in (0)..1, f u ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have h' : ∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2 = (x * f x) * (∫ (u : ℝ) in (0)..1, f u ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    exact h'
  rw [h]
  have h2 : ∫ (x : ℝ) in (0)..1, (x * f x) * C = C * ∫ (x : ℝ) in (0)..1, x * f x := by
    have h3 : ∫ (x : ℝ) in (0)..1, (x * f x) * C = ∫ (x : ℝ) in (0)..1, C * (x * f x) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [h3]
    rw [intervalIntegral.integral_const_mul]
  rw [h2] ; ring

lemma hI3 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f):
  (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u) =
    (∫ (x : ℝ) in (0)..1, (f x) ^ 2) * (∫ (u : ℝ) in (0)..1, u * f u) := by
  let K := (∫ (u : ℝ) in (0)..1, u * f u)
  let C := (∫ (x : ℝ) in (0)..1, (f x) ^ 2)
  have h1 : ∀ x : ℝ, ∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u = f x ^ 2 * K := by
    intro x
    have h2 : ∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u = ∫ (u : ℝ) in (0)..1, (f x ^ 2 * (u * f u)) := by
      congr with u
      ring
    rw [h2]
    have h3 : ∫ (u : ℝ) in (0)..1, (f x ^ 2 * (u * f u)) = f x ^ 2 * (∫ (u : ℝ) in (0)..1, u * f u) := by
      rw [intervalIntegral.integral_const_mul]
    simp [K]
  have h : (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u) =
    ∫ (x : ℝ) in (0)..1, (f x ^ 2 * K) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h1 x
  rw [h]
  have h4 : ∫ (x : ℝ) in (0)..1, (f x ^ 2 * K) = K * ∫ (x : ℝ) in (0)..1, (f x ^ 2) := by
    have h5 : ∫ (x : ℝ) in (0)..1, (f x ^ 2 * K) = ∫ (x : ℝ) in (0)..1, K * (f x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [h5]
    rw [intervalIntegral.integral_const_mul]
  rw [h4]
  simp [K] ; ring

lemma hI4 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f):
  (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2) =
    (∫ (x : ℝ) in (0)..1, f x) * (∫ (u : ℝ) in (0)..1, u * f u ^ 2) := by
  let K := (∫ (u : ℝ) in (0)..1, u * f u ^ 2)
  let A := (∫ (x : ℝ) in (0)..1, f x)
  have h1 : ∀ x : ℝ, ∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2 = f x * K := by
    intro x
    have h2 : ∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2 = ∫ (u : ℝ) in (0)..1, (f x * (u * f u ^ 2)) := by
      congr with u
      ring
    rw [h2]
    have h3 : ∫ (u : ℝ) in (0)..1, (f x * (u * f u ^ 2)) = f x * (∫ (u : ℝ) in (0)..1, u * f u ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    simp [K]
  have h : (∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2) =
    ∫ (x : ℝ) in (0)..1, (f x * K) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact h1 x
  rw [h]
  have h4 : ∫ (x : ℝ) in (0)..1, (f x * K) = K * ∫ (x : ℝ) in (0)..1, f x := by
    have h5 : ∫ (x : ℝ) in (0)..1, (f x * K) = ∫ (x : ℝ) in (0)..1, K * (f x) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [h5]
    rw [intervalIntegral.integral_const_mul]
  rw [h4]
  simp [K] ; ring

lemma h_int_u (f : ℝ → ℝ)
  (hfc : Continuous f)
  (x : ℝ):
  ∫ (u : ℝ) in (0)..1, (x * f x ^ 2 * f u - x * f x * f u ^ 2 - u * f x ^ 2 * f u + u * f x * f u ^ 2)
  = (∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u)
    - (∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2)
    - (∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u)
    + (∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2) := by
  let f1 := (fun u : ℝ ↦ x * f x ^ 2 * f u)
  let f2 := (fun u : ℝ ↦ x * f x * f u ^ 2)
  let f3 := (fun u : ℝ ↦ u * f x ^ 2 * f u)
  let f4 := (fun u : ℝ ↦ u * f x * f u ^ 2)
  have h_cont1 : Continuous f1 := by continuity
  have h_cont2 : Continuous f2 := by continuity
  have h_cont3 : Continuous f3 := by continuity
  have h_cont4 : Continuous f4 := by continuity
  have h_i1 : IntervalIntegrable f1 volume 0 1 := h_cont1.intervalIntegrable 0 1
  have h_i2 : IntervalIntegrable f2 volume 0 1 := h_cont2.intervalIntegrable 0 1
  have h_i3 : IntervalIntegrable f3 volume 0 1 := h_cont3.intervalIntegrable 0 1
  have h_i4 : IntervalIntegrable f4 volume 0 1 := h_cont4.intervalIntegrable 0 1
  have h_eq_main : ∫ (u : ℝ) in (0)..1, (f1 u - f2 u - f3 u + f4 u)
    = (∫ (u : ℝ) in (0)..1, f1 u) - (∫ (u : ℝ) in (0)..1, f2 u) - (∫ (u : ℝ) in (0)..1, f3 u) + (∫ (u : ℝ) in (0)..1, f4 u) := by
    have h5 : ∫ (u : ℝ) in (0)..1, (f1 u - f2 u - f3 u + f4 u) = ∫ (u : ℝ) in (0)..1, ((f1 u - f2 u) - (f3 u - f4 u)) := by
      congr with u
      ring
    rw [h5]
    have h6 : IntervalIntegrable (fun u ↦ f1 u - f2 u) volume 0 1 := by
      exact h_i1.sub h_i2
    have h7 : IntervalIntegrable (fun u ↦ f3 u - f4 u) volume 0 1 := by
      exact h_i3.sub h_i4
    rw [intervalIntegral.integral_sub h6 h7]
    rw [intervalIntegral.integral_sub h_i1 h_i2, intervalIntegral.integral_sub h_i3 h_i4] ; ring
  simpa [f1, f2, f3, f4] using h_eq_main

lemma hH1 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (x : ℝ):
  (∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u) = x * (f x)^2 * (∫ (x : ℝ) in (0)..1, f x) := by
  have h : (∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u) = x * f x ^ 2 * (∫ (u : ℝ) in (0)..1, f u) := by
    have h' : ∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u = ∫ (u : ℝ) in (0)..1, (x * f x ^ 2) * f u := by
      rfl
    rw [h']
    rw [intervalIntegral.integral_const_mul]
  simp

lemma hH2 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (x : ℝ):
  (∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2) = x * f x * (∫ (x : ℝ) in (0)..1, (f x) ^ 2) := by
  have h : (∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2) = x * f x * (∫ (u : ℝ) in (0)..1, f u ^ 2) := by
    have h' : ∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2 = ∫ (u : ℝ) in (0)..1, (x * f x) * f u ^ 2 := by
      rfl
    rw [h']
    rw [intervalIntegral.integral_const_mul]
  simp

lemma hH3 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (x : ℝ):
  (∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u) = (f x)^2 * (∫ (u : ℝ) in (0)..1, u * f u) := by
  have h : (∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u) = f x ^ 2 * (∫ (u : ℝ) in (0)..1, u * f u) := by
    have h' : ∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u = ∫ (u : ℝ) in (0)..1, f x ^ 2 * (u * f u) := by
      congr with u
      ring
    rw [h']
    rw [intervalIntegral.integral_const_mul]
  simpa using h

lemma hH4 (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (x : ℝ):
  (∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2) = f x * (∫ (u : ℝ) in (0)..1, u * f u ^ 2) := by
  have h : (∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2) = f x * (∫ (u : ℝ) in (0)..1, u * f u ^ 2) := by
    have h' : ∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2 = ∫ (u : ℝ) in (0)..1, f x * (u * f u ^ 2) := by
      congr with u
      ring
    rw [h']
    rw [intervalIntegral.integral_const_mul]
  simpa using h

lemma main_identity_final (f : ℝ → ℝ)
  (hfc : Continuous f)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f):
  ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x - u) * f x * f u * (f x - f u) =
    2 * ((∫ (x : ℝ) in (0)..1, f x) * (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) - (∫ (x : ℝ) in (0)..1, x * f x) * (∫ (x : ℝ) in (0)..1, (f x) ^ 2)) := by
  let A := (∫ (x : ℝ) in (0)..1, f x)
  let B := (∫ (x : ℝ) in (0)..1, x * f x)
  let C := (∫ (x : ℝ) in (0)..1, (f x) ^ 2)
  let D := (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2)
  let H1 (x : ℝ) := ∫ (u : ℝ) in (0)..1, x * f x ^ 2 * f u
  let H2 (x : ℝ) := ∫ (u : ℝ) in (0)..1, x * f x * f u ^ 2
  let H3 (x : ℝ) := ∫ (u : ℝ) in (0)..1, u * f x ^ 2 * f u
  let H4 (x : ℝ) := ∫ (u : ℝ) in (0)..1, u * f x * f u ^ 2
  have hH1 : ∀ x : ℝ, H1 x = x * (f x)^2 * A := fun x ↦ hH1 f hfc hf hfm x
  have hH2 : ∀ x : ℝ, H2 x = x * f x * C := fun x ↦ hH2 f hfc hf hfm x
  have hH3 : ∀ x : ℝ, H3 x = (f x)^2 * B := fun x ↦ hH3 f hfc hf hfm x
  have hH4 : ∀ x : ℝ, H4 x = f x * D := fun x ↦ hH4 f hfc hf hfm x
  have hI1' := hI1 f hfc hf hfm
  have hI2' := hI2 f hfc hf hfm
  have hI3' := hI3 f hfc hf hfm
  have hI4' := hI4 f hfc hf hfm
  have h_eq1 : ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x - u) * f x * f u * (f x - f u)
    = ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x * f x ^ 2 * f u - x * f x * f u ^ 2 - u * f x ^ 2 * f u + u * f x * f u ^ 2) := by
    congr ; funext x ; congr ; funext u ; ring
  rw [h_eq1]
  have h_sum1 : ∀ (x : ℝ), ∫ (u : ℝ) in (0)..1, (x * f x ^ 2 * f u - x * f x * f u ^ 2 - u * f x ^ 2 * f u + u * f x * f u ^ 2)
    = H1 x - H2 x - H3 x + H4 x := fun x ↦ h_int_u f hfc x
  have hC : ∫ (x : ℝ) in (0)..1, (∫ (u : ℝ) in (0)..1, (x * f x ^ 2 * f u - x * f x * f u ^ 2 - u * f x ^ 2 * f u + u * f x * f u ^ 2))
    = ∫ (x : ℝ) in (0)..1, (H1 x - H2 x - H3 x + H4 x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact h_sum1 x
  rw [show ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x * f x ^ 2 * f u - x * f x * f u ^ 2 - u * f x ^ 2 * f u + u * f x * f u ^ 2)
    = ∫ (x : ℝ) in (0)..1, (∫ (u : ℝ) in (0)..1, (x * f x ^ 2 * f u - x * f x * f u ^ 2 - u * f x ^ 2 * f u + u * f x * f u ^ 2)) by rfl]
  rw [hC]
  have h1H1 : Continuous (fun x : ℝ ↦ x * (f x)^2 * A) := by
    have h_cont_f : Continuous f := hfc
    continuity
  have h1H2 : Continuous (fun x : ℝ ↦ x * f x * C) := by
    have h_cont_f : Continuous f := hfc
    continuity
  have h1H3 : Continuous (fun x : ℝ ↦ (f x)^2 * B) := by
    have h_cont_f : Continuous f := hfc
    continuity
  have h1H4 : Continuous (fun x : ℝ ↦ f x * D) := by
    have h_cont_f : Continuous f := hfc
    continuity
  have h_int1 : IntervalIntegrable (fun x : ℝ ↦ x * (f x)^2 * A) volume 0 1 := h1H1.intervalIntegrable 0 1
  have h_int2 : IntervalIntegrable (fun x : ℝ ↦ x * f x * C) volume 0 1 := h1H2.intervalIntegrable 0 1
  have h_int3 : IntervalIntegrable (fun x : ℝ ↦ (f x)^2 * B) volume 0 1 := h1H3.intervalIntegrable 0 1
  have h_int4 : IntervalIntegrable (fun x : ℝ ↦ f x * D) volume 0 1 := h1H4.intervalIntegrable 0 1
  have h_eqH1 : ∀ x, H1 x = x * (f x)^2 * A := hH1
  have h_eqH2 : ∀ x, H2 x = x * f x * C := hH2
  have h_eqH3 : ∀ x, H3 x = (f x)^2 * B := hH3
  have h_eqH4 : ∀ x, H4 x = f x * D := hH4
  let g1 := (fun x : ℝ ↦ x * (f x)^2 * A)
  let g2 := (fun x : ℝ ↦ x * f x * C)
  let g3 := (fun x : ℝ ↦ (f x)^2 * B)
  let g4 := (fun x : ℝ ↦ f x * D)
  have h_goal : ∫ (x : ℝ) in (0)..1, (H1 x - H2 x - H3 x + H4 x) = ∫ (x : ℝ) in (0)..1, (g1 x - g2 x - g3 x + g4 x) := by
    congr with x
    simp [g1, g2, g3, g4, h_eqH1, h_eqH2, h_eqH3, h_eqH4]
  rw [h_goal]
  have h_final : ∫ (x : ℝ) in (0)..1, (g1 x - g2 x - g3 x + g4 x) = (∫ (x : ℝ) in (0)..1, g1 x) - (∫ (x : ℝ) in (0)..1, g2 x) - (∫ (x : ℝ) in (0)..1, g3 x) + (∫ (x : ℝ) in (0)..1, g4 x) := by
    have h1 : ∫ (x : ℝ) in (0)..1, (g1 x - g2 x - g3 x + g4 x) = ∫ (x : ℝ) in (0)..1, ((g1 x - g2 x) - (g3 x - g4 x)) := by
      congr with x
      ring
    rw [h1]
    have h2 : IntervalIntegrable (fun x ↦ g1 x - g2 x) volume 0 1 := h_int1.sub h_int2
    have h3 : IntervalIntegrable (fun x ↦ g3 x - g4 x) volume 0 1 := h_int3.sub h_int4
    have h4 := intervalIntegral.integral_sub h2 h3
    rw [h4]
    have h5 : ∫ (x : ℝ) in (0)..1, (g1 x - g2 x) = (∫ (x : ℝ) in (0)..1, g1 x) - (∫ (x : ℝ) in (0)..1, g2 x) := intervalIntegral.integral_sub h_int1 h_int2
    have h6 : ∫ (x : ℝ) in (0)..1, (g3 x - g4 x) = (∫ (x : ℝ) in (0)..1, g3 x) - (∫ (x : ℝ) in (0)..1, g4 x) := intervalIntegral.integral_sub h_int3 h_int4
    rw [h5, h6] ; ring
  rw [h_final]
  have h7 : (∫ (x : ℝ) in (0)..1, g1 x) = A * D := by
    have h71 : (∫ (x : ℝ) in (0)..1, g1 x) = ∫ (x : ℝ) in (0)..1, (x * (f x)^2 * A) := by rfl
    rw [h71]
    have h72 : ∀ x : ℝ, x * (f x)^2 * A = A * (x * (f x)^2) := by
      intro x
      ring
    have h73 : ∫ (x : ℝ) in (0)..1, (x * (f x)^2 * A) = ∫ (x : ℝ) in (0)..1, (A * (x * (f x)^2)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact h72 x
    rw [h73]
    rw [intervalIntegral.integral_const_mul]
  have h8 : (∫ (x : ℝ) in (0)..1, g2 x) = B * C := by
    have h81 : (∫ (x : ℝ) in (0)..1, g2 x) = ∫ (x : ℝ) in (0)..1, (x * f x * C) := by rfl
    rw [h81]
    have h82 : ∀ x : ℝ, x * f x * C = C * (x * f x) := by
      intro x
      ring
    have h83 : ∫ (x : ℝ) in (0)..1, (x * f x * C) = ∫ (x : ℝ) in (0)..1, (C * (x * f x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact h82 x
    rw [h83]
    rw [intervalIntegral.integral_const_mul] ; ring
  have h9 : (∫ (x : ℝ) in (0)..1, g3 x) = C * B := by
    have h91 : (∫ (x : ℝ) in (0)..1, g3 x) = ∫ (x : ℝ) in (0)..1, ((f x)^2 * B) := by rfl
    rw [h91]
    have h92 : ∀ x : ℝ, (f x)^2 * B = B * ((f x)^2) := by
      intro x
      ring
    have h93 : ∫ (x : ℝ) in (0)..1, ((f x)^2 * B) = ∫ (x : ℝ) in (0)..1, (B * ((f x)^2)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact h92 x
    rw [h93]
    rw [intervalIntegral.integral_const_mul] ; ring
  have h10 : (∫ (x : ℝ) in (0)..1, g4 x) = A * D := by
    have h101 : (∫ (x : ℝ) in (0)..1, g4 x) = ∫ (x : ℝ) in (0)..1, (f x * D) := by rfl
    rw [h101]
    have h102 : ∀ x : ℝ, f x * D = D * (f x) := by
      intro x
      ring
    have h103 : ∫ (x : ℝ) in (0)..1, (f x * D) = ∫ (x : ℝ) in (0)..1, (D * (f x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact h102 x
    rw [h103]
    rw [intervalIntegral.integral_const_mul] ; ring
  rw [h7, h8, h9, h10] ; ring

lemma round3_exists_pos_integrand (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  ∃ (x u : ℝ), x ∈ Icc (0 : ℝ) 1 ∧ u ∈ Icc (0 : ℝ) 1 ∧ (x - u) * f x * f u * (f x - f u) > 0 := by
  by_cases h : f 0 > 0
  ·
    refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    have h1 : (1 : ℝ) - (0 : ℝ) > 0 := by norm_num
    have h2 : f 1 > f 0 := hfm (show (0 : ℝ) < (1 : ℝ) by norm_num)
    have h3 : f 1 - f 0 > 0 := by linarith
    have h4 : f 1 > 0 := by linarith
    have h5 : f 0 > 0 := h
    have h6 : f 1 * f 0 > 0 := mul_pos h4 h5
    have h7 : (f 1 * f 0) * (f 1 - f 0) > 0 := mul_pos h6 h3
    have h8 : ((1 : ℝ) - (0 : ℝ)) * (f 1 * f 0 * (f 1 - f 0)) > 0 := by
      rw [show (1 : ℝ) - (0 : ℝ) = 1 by norm_num]
      simpa using h7
    simpa [mul_assoc] using h8
  ·
    have h' : f 0 = 0 := by
      have h9 : 0 ≤ f 0 := hf 0 (by norm_num)
      linarith
    have h_f1_pos : f 1 > 0 := by
      have h10 : f 1 > f 0 := hfm (show (0 : ℝ) < (1 : ℝ) by norm_num)
      rw [h'] at h10 ; linarith
    have h_cont_at_1 : ContinuousAt f 1 := hfc.continuousAt
    have h141 : ∃ ε > 0, ∀ (y : ℝ), |y - 1| < ε → f y > 0 := by
      have h142 : ∃ ε > 0, ∀ (y : ℝ), |y - 1| < ε → |f y - f 1| < f 1 := Metric.continuousAt_iff.mp h_cont_at_1 (f 1) h_f1_pos
      rcases h142 with ⟨ε, hε_pos, h143⟩
      refine ⟨ε, hε_pos, fun y hy => ?_⟩
      have h144 : |f y - f 1| < f 1 := h143 y hy
      have h145 : f y - f 1 > -f 1 := by linarith [abs_lt.mp h144]
      linarith
    rcases h141 with ⟨ε, hε_pos, h14⟩
    let ε₁ := min ε 1
    have hε₁_pos : 0 < ε₁ := by
      exact lt_min hε_pos (by norm_num)
    have hε₁_le_ε : ε₁ ≤ ε := min_le_left ε 1
    have hε₁_le_1 : ε₁ ≤ 1 := min_le_right ε 1
    let u := 1 - ε₁ / 2
    have h15 : u < 1 := by
      dsimp only [u, ε₁]
      linarith [hε₁_pos]
    have h16 : 0 ≤ u := by
      dsimp only [u, ε₁]
      linarith [hε₁_le_1]
    have h17 : u ∈ Icc (0 : ℝ) 1 := ⟨h16, by linarith⟩
    have h18 : |u - 1| < ε := by
      dsimp only [u, ε₁]
      rw [show u - 1 = -(ε₁ / 2) by ring]
      rw [abs_neg, abs_of_pos (show (0 : ℝ) < ε₁ / 2 by linarith [hε₁_pos])]
      linarith [hε₁_le_ε]
    have h19 : f u > 0 := h14 u h18
    refine ⟨(1 : ℝ), u, by norm_num, h17, ?_⟩
    have h20 : (1 : ℝ) - u > 0 := by linarith
    have h21 : f (1 : ℝ) > f u := hfm (show (u : ℝ) < (1 : ℝ) by linarith)
    have h22 : f (1 : ℝ) - f u > 0 := by linarith
    have h23 : f (1 : ℝ) > 0 := h_f1_pos
    have h24 : (f (1 : ℝ)) * (f u) > 0 := mul_pos h23 h19
    have h25 : ((f (1 : ℝ)) * (f u)) * (f (1 : ℝ) - f u) > 0 := mul_pos h24 h22
    have h26 : ((1 : ℝ) - u) * (((f (1 : ℝ)) * (f u)) * (f (1 : ℝ) - f u)) > 0 := by
      apply mul_pos h20 h25
    simpa [mul_assoc] using h26

lemma round7_double_integral_pos (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x - u) * f x * f u * (f x - f u) > 0 := by
  have h_nonneg : ∀ (x u : ℝ), x ∈ Icc (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 → (x - u) * f x * f u * (f x - f u) ≥ 0 := by
    intro x u hx hu
    exact nonneg_integrand f hf hfm x u hx hu
  have h_main1 : ∃ (x₀ u₀ : ℝ), x₀ ∈ Icc (0 : ℝ) 1 ∧ u₀ ∈ Icc (0 : ℝ) 1 ∧ (x₀ - u₀) * f x₀ * f u₀ * (f x₀ - f u₀) > 0 :=
    round3_exists_pos_integrand f hf hfm hfc
  rcases h_main1 with ⟨x₀, u₀, hx₀, hu₀, h_pos⟩
  let g : ℝ → ℝ → ℝ := fun x u ↦ (x - u) * f x * f u * (f x - f u)
  have h_g_nonneg : ∀ (x u : ℝ), x ∈ Icc (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 → g x u ≥ 0 := h_nonneg
  let h : ℝ → ℝ := fun x ↦ ∫ (u : ℝ) in (0)..1, g x u
  have h1 : ∀ x ∈ Icc (0 : ℝ) 1, h x ≥ 0 := by
    intro x hx
    have h12 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
    have h11 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ g x u := fun u hu => h_g_nonneg x u hx hu
    have h13 : 0 ≤ ∫ (u : ℝ) in (0)..1, g x u := intervalIntegral.integral_nonneg h12 h11
    simpa [h] using h13
  have h2 : h x₀ > 0 := by
    have h_cont1 : Continuous (fun u : ℝ ↦ g x₀ u) := by
      fun_prop
    have h_cont2 : ContinuousOn (fun u : ℝ ↦ g x₀ u) (Icc (0 : ℝ) 1) := h_cont1.continuousOn
    have hle : ∀ u ∈ Ioc (0 : ℝ) 1, 0 ≤ g x₀ u := by
      intro u hu
      have h4 : u ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hu
      exact h_g_nonneg x₀ u hx₀ h4
    have hlt : ∃ c ∈ Icc (0 : ℝ) 1, 0 < g x₀ c := ⟨u₀, hu₀, h_pos⟩
    have h5 : 0 < ∫ (u : ℝ) in (0)..1, g x₀ u := intervalIntegral.integral_pos (show (0 : ℝ) < (1 : ℝ) by norm_num) h_cont2 hle hlt
    simpa [h] using h5
  have h_cont_h : Continuous h := by
    fun_prop
  have h_cont3 : ContinuousOn h (Icc (0 : ℝ) 1) := h_cont_h.continuousOn
  have h6 : (0 : ℝ) < (1 : ℝ) := by norm_num
  have hle2 : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ h x := by
    intro x hx
    have h7 : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
    exact h1 x h7
  have h3 : ∫ (x : ℝ) in (0)..1, h x > 0 := by
    exact intervalIntegral.integral_pos h6 h_cont3 hle2 ⟨x₀, hx₀, h2⟩
  simpa [h, g] using h3

theorem A_mul_D_sub_B_mul_C_is_positive (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  (∫ (x : ℝ) in (0)..1, f x) * (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) - (∫ (x : ℝ) in (0)..1, x * f x) * (∫ (x : ℝ) in (0)..1, (f x) ^ 2) > 0 := by
  have h_main_id := main_identity_final f hfc hf hfm
  have h_strict_pos : ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x - u) * f x * f u * (f x - f u) > 0 :=
    round7_double_integral_pos f hf hfm hfc
  have h_eq : ∫ (x : ℝ) in (0)..1, ∫ (u : ℝ) in (0)..1, (x - u) * f x * f u * (f x - f u) =
    2 * ((∫ (x : ℝ) in (0)..1, f x) * (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) - (∫ (x : ℝ) in (0)..1, x * f x) * (∫ (x : ℝ) in (0)..1, (f x) ^ 2)) := h_main_id
  rw [h_eq] at h_strict_pos
  have h_pos : ((∫ (x : ℝ) in (0)..1, f x) * (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) - (∫ (x : ℝ) in (0)..1, x * f x) * (∫ (x : ℝ) in (0)..1, (f x) ^ 2)) > 0 := by
    linarith
  exact h_pos

lemma round1_h3 (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x):
  ∀ x ∈ Icc (0 : ℝ) 1, (∫ (y : ℝ) in Icc 0 (f x), (1 : ℝ)) = f x := by
  intro x hx
  have h4 : 0 ≤ f x := hf x hx
  simp [h4]

lemma round2_R_measurable (f : ℝ → ℝ)
  (hfc : Continuous f):
  MeasurableSet ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }) := by
  have h1 : MeasurableSet ({ x : ℝ × ℝ | 0 ≤ x.1 }) := by
    have h1₁ : ({ x : ℝ × ℝ | 0 ≤ x.1 } : Set (ℝ × ℝ)) = Prod.fst ⁻¹' (Set.Ici (0 : ℝ)) := by
      ext ⟨x, y⟩ ; simp
    rw [h1₁]
    apply MeasurableSet.preimage
    · exact measurableSet_Ici
    · exact measurable_fst
  have h2 : MeasurableSet ({ x : ℝ × ℝ | x.1 ≤ 1 }) := by
    have h2₁ : ({ x : ℝ × ℝ | x.1 ≤ 1 } : Set (ℝ × ℝ)) = Prod.fst ⁻¹' (Set.Iic (1 : ℝ)) := by
      ext ⟨x, y⟩ ; simp
    rw [h2₁]
    apply MeasurableSet.preimage
    · exact measurableSet_Iic
    · exact measurable_fst
  have h3 : MeasurableSet ({ x : ℝ × ℝ | 0 ≤ x.2 }) := by
    have h3₁ : ({ x : ℝ × ℝ | 0 ≤ x.2 } : Set (ℝ × ℝ)) = Prod.snd ⁻¹' (Set.Ici (0 : ℝ)) := by
      ext ⟨x, y⟩ ; simp
    rw [h3₁]
    apply MeasurableSet.preimage
    · exact measurableSet_Ici
    · exact measurable_snd
  let g : (ℝ × ℝ) → ℝ := fun p ↦ p.2 - f p.1
  have hg_cont : Continuous g := by
    have h6 : Continuous (fun (p : ℝ × ℝ) ↦ p.2) := continuous_snd
    have h7 : Continuous (fun (p : ℝ × ℝ) ↦ f p.1) := hfc.comp continuous_fst
    exact Continuous.sub h6 h7
  have hg : Measurable g := hg_cont.measurable
  have h4 : MeasurableSet ({ x : ℝ × ℝ | x.2 ≤ f x.1 }) := by
    have h4₁ : ({ x : ℝ × ℝ | x.2 ≤ f x.1 } : Set (ℝ × ℝ)) = g ⁻¹' (Set.Iic (0 : ℝ)) := by
      ext ⟨x, y⟩ ; simp [g]
    rw [h4₁]
    have h42 : MeasurableSet (Set.Iic (0 : ℝ)) := by exact measurableSet_Iic
    exact h42.preimage hg
  have h_main : ({ x : ℝ × ℝ | 0 ≤ x.1 } ∩ { x : ℝ × ℝ | x.1 ≤ 1 } ∩ { x : ℝ × ℝ | 0 ≤ x.2 } ∩ { x : ℝ × ℝ | x.2 ≤ f x.1 }) = { x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 } := by
    ext ⟨x, y⟩
    simp
    tauto
  rw [← h_main]
  exact (h1.inter h2).inter h3 |>.inter h4

lemma round2_R_finite_volume (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f):
  volume ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }) < ⊤ := by
  have h_compact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have h_cont_on : ContinuousOn f (Icc (0 : ℝ) 1) := hfc.continuousOn
  have h_bounded : BddAbove (f '' (Icc (0 : ℝ) 1)) := h_compact.bddAbove_image h_cont_on
  rcases h_bounded with ⟨M, hM⟩
  have hM' : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ M := by
    intro x hx
    have hfx : f x ∈ f '' (Icc (0 : ℝ) 1) := ⟨x, hx, rfl⟩
    exact hM hfx
  let S := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) M
  have h_subset : ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }) ⊆ S := by
    intro ⟨x, y⟩ h
    have hx1 : 0 ≤ x := h.1
    have hx2 : x ≤ 1 := h.2.1
    have hy1 : 0 ≤ y := h.2.2.1
    have hy2 : y ≤ f x := h.2.2.2
    have hfxM : f x ≤ M := hM' x ⟨hx1, hx2⟩
    have h1 : x ∈ Icc (0 : ℝ) 1 := ⟨hx1, hx2⟩
    have h2 : y ∈ Icc (0 : ℝ) M := ⟨hy1, by linarith⟩
    exact ⟨h1, h2⟩
  have hvol1 : volume (Icc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Icc]
    simp
  have hvol2 : volume (Icc (0 : ℝ) M) < ⊤ := by
    rw [Real.volume_Icc]
    simp
  have hvol_S : volume S < ⊤ := by
    have h : volume S = (volume.prod volume) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) M) := by rfl
    rw [h]
    have h' : (volume.prod volume) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) M) = volume (Icc (0 : ℝ) 1) * volume (Icc (0 : ℝ) M) := by
      exact Measure.prod_prod (Icc 0 1) (Icc 0 M)
    rw [h']
    exact ENNReal.mul_lt_top hvol1 hvol2
  have hvol_R : volume ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }) ≤ volume S := by
    apply volume.mono h_subset
  exact lt_of_le_of_lt hvol_R hvol_S

lemma round2_has_finite_integral {α : Type*}
  [MeasurableSpace α]
  (μ : Measure α)
  (f : α → ℝ)
  (S : Set α)
  (hSmeas : MeasurableSet S)
  (hS : μ S < ⊤)
  (h1 : ∀ (x : α), ‖f x‖ ≤ 1)
  (h2 : Function.support f ⊆ S)
  (hf : AEMeasurable f μ):
  HasFiniteIntegral f μ := by
  let g : α → ENNReal := fun x ↦ ENNReal.ofReal ‖f x‖
  have h3 : ∀ (x : α), g x ≤ 1 := by
    intro x
    have h4 : ‖f x‖ ≤ 1 := h1 x
    have h5 : g x = ENNReal.ofReal ‖f x‖ := rfl
    rw [h5]
    have h6 : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal (1 : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      exact h4
    simpa using h6
  have h4 : ∀ (x : α), x ∉ S → g x = 0 := by
    intro x hx_notin_S
    have h5 : x ∉ Function.support f := by
      intro h_contra
      have h6 : x ∈ Function.support f := h_contra
      have h7 : x ∈ S := h2 h6
      exact hx_notin_S h7
    have h_fx_eq_zero : f x = 0 := by
      simpa [Function.mem_support] using h5
    have h7 : ‖f x‖ = 0 := by
      rw [h_fx_eq_zero] ; norm_num
    have h8 : g x = 0 := by
      unfold g
      rw [h7]
      norm_num
    exact h8
  have h5 : g = Set.indicator S g := by
    ext x
    by_cases hx : x ∈ S
    · simp [hx, Set.indicator]
    · simp [hx, Set.indicator, h4 x hx]
  have h61 : Set.indicator S (Set.indicator S g) = Set.indicator S g := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx, Set.indicator]
  have h6 : (∫⁻ x, Set.indicator S g x ∂μ) = (∫⁻ x, g x ∂μ) := by
    have h62 : Set.indicator S g = g := h5.symm
    rw [h62]
  have h7 : (∫⁻ x, Set.indicator S g x ∂μ) = (∫⁻ x in S, g x ∂μ) := by
    rw [MeasureTheory.lintegral_indicator hSmeas]
  have h8 : (∫⁻ x, g x ∂μ) = (∫⁻ x in S, g x ∂μ) := by
    rw [← h6, h7]
  have h9 : (∫⁻ x in S, g x ∂μ) ≤ (∫⁻ x in S, (1 : ENNReal) ∂μ) := by
    apply lintegral_mono_ae
    filter_upwards with x
    exact h3 x
  have h10 : (∫⁻ x in S, (1 : ENNReal) ∂μ) = μ S := by
    simp
  have h11 : (∫⁻ x, g x ∂μ) < ⊤ := by
    calc
      (∫⁻ x, g x ∂μ) = (∫⁻ x in S, g x ∂μ) := h8
      _ ≤ (∫⁻ x in S, (1 : ENNReal) ∂μ) := h9
      _ = μ S := h10
      _ < ⊤ := hS
  have h12 : (∫⁻ (a : α), ‖f a‖ₑ ∂μ) = (∫⁻ x, g x ∂μ) := by
    apply congr_arg (fun F : α → ENNReal ↦ ∫⁻ x, F x ∂μ)
    funext x
    simp only [g]
    exact Eq.symm (ofReal_norm_eq_enorm (f x))
  have h13 : HasFiniteIntegral f μ := by
    simpa [HasFiniteIntegral, h12] using h11
  exact h13

lemma round2_integrable_fst (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f)
  (R : Set (ℝ × ℝ))
  (hR_def : R = { x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }):
  Integrable (Set.indicator R (fun p : ℝ × ℝ ↦ p.1)) volume := by
  have hRm : MeasurableSet R := by
    rw [hR_def]
    exact round2_R_measurable f hfc
  have hRvol : volume R < ⊤ := by
    rw [hR_def]
    exact round2_R_finite_volume f hf hfc
  let g₁ : (ℝ × ℝ) → ℝ := Set.indicator R (fun p : ℝ × ℝ ↦ p.1)
  have h_meas_fst : Measurable (fun p : ℝ × ℝ ↦ p.1) := by fun_prop
  have h_meas_g₁ : Measurable g₁ := by
    exact h_meas_fst.indicator hRm
  have h_aemeas : AEMeasurable g₁ volume := h_meas_g₁.aemeasurable
  have h1 : ∀ (x : ℝ × ℝ), ‖g₁ x‖ ≤ 1 := by
    intro x
    have hgx : g₁ x = Set.indicator R (fun p : ℝ × ℝ ↦ p.1) x := rfl
    rw [hgx]
    by_cases hx : x ∈ R
    · have h2 : Set.indicator R (fun p : ℝ × ℝ ↦ p.1) x = x.1 := by
        simp [hx]
      rw [h2]
      have h31 : 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 := by
        rw [hR_def] at hx
        simpa using hx
      have h3 : 0 ≤ x.1 ∧ x.1 ≤ 1 := ⟨h31.1, h31.2.1⟩
      have h4 : ‖x.1‖ ≤ 1 := by
        have h5 : 0 ≤ x.1 := h3.1
        have h6 : x.1 ≤ 1 := h3.2
        rw [show ‖x.1‖ = |x.1| from by rfl]
        rw [abs_of_nonneg h5]
        linarith
      exact h4
    · have h2 : Set.indicator R (fun p : ℝ × ℝ ↦ p.1) x = 0 := by
        simp [hx]
      rw [h2]
      norm_num
  have h2 : Function.support g₁ ⊆ R := by
    intro x hx
    have hgx_ne_zero : g₁ x ≠ 0 := by
      simpa [Function.mem_support] using hx
    have h4 : x ∈ R := by
      by_contra h5
      have h6 : g₁ x = 0 := by
        simp [g₁, h5]
      contradiction
    exact h4
  have h_main : HasFiniteIntegral g₁ volume := round2_has_finite_integral volume g₁ R hRm hRvol h1 h2 h_aemeas
  have h_aessm : AEStronglyMeasurable g₁ volume := by
    exact h_aemeas.aestronglyMeasurable
  have h_integrable : Integrable g₁ volume := by
    exact ⟨h_aessm, h_main⟩
  exact h_integrable

lemma round2_num_eq_iterated (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfc : Continuous f):
  (∫ p : ℝ × ℝ, Set.indicator ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }) (fun p : ℝ × ℝ => p.1) p ∂volume)
  = ∫ x in Icc (0:ℝ) 1, x * f x := by
  let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }
  have hR_def : R = { x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 } := rfl
  have h_meas : MeasurableSet R := round2_R_measurable f hfc
  have h_int : Integrable (Set.indicator R (fun p : ℝ × ℝ => p.1)) volume := round2_integrable_fst f hf hfc (R) (by rfl)
  let μ : Measure ℝ := volume
  have hvol_eq : (volume : Measure (ℝ × ℝ)) = μ.prod μ := by exact rfl
  have h_main : (∫ p : ℝ × ℝ, Set.indicator R (fun p : ℝ × ℝ => p.1) p ∂volume) = ∫ x : ℝ, ∫ y : ℝ, Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) ∂μ ∂μ := by
    rw [hvol_eq]
    exact integral_prod (R.indicator fun p => p.1) h_int
  rw [h_main]
  have h_inner : ∀ (x : ℝ), (∫ y : ℝ, Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) ∂μ) = if h : x ∈ Icc (0 : ℝ) 1 then x * f x else 0 := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp only [hx, dif_pos]
      have hfx : 0 ≤ f x := hf x hx
      have h1 : ∀ (y : ℝ), Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) = x * Set.indicator (Icc (0 : ℝ) (f x)) (fun (_ : ℝ) => (1 : ℝ)) y := by
        intro y
        have h2 : (x, y) ∈ R ↔ y ∈ Icc (0 : ℝ) (f x) := by
          simp [hR_def] ; aesop
        rw [Set.indicator_apply, Set.indicator_apply]
        split_ifs <;> aesop
      have h3 : (∫ y : ℝ, Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) ∂μ) = ∫ y : ℝ, x * Set.indicator (Icc (0 : ℝ) (f x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ := by
        congr 1 with y
        exact h1 y
      rw [h3]
      have h41 : (∫ y : ℝ, x * Set.indicator (Icc (0 : ℝ) (f x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ)
          = x * (∫ y : ℝ, Set.indicator (Icc (0 : ℝ) (f x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ) := by
        rw [integral_mul_left]
      rw [h41]
      have h42 : (∫ y : ℝ, Set.indicator (Icc (0 : ℝ) (f x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ) = ∫ (y : ℝ) in Icc 0 (f x), (1 : ℝ) := by
        have h421 : (∫ y : ℝ, Set.indicator (Icc (0 : ℝ) (f x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ) = ∫ (y : ℝ) in Icc (0 : ℝ) (f x), (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator (show MeasurableSet (Icc (0 : ℝ) (f x)) from measurableSet_Icc)]
        exact h421
      rw [h42]
      have h43 : (∫ (y : ℝ) in Icc 0 (f x), (1 : ℝ)) = f x := round1_h3 f hf x hx
      rw [h43]
    · simp only [hx, dif_neg, not_false_eq_true]
      have h1 : ∀ (y : ℝ), Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) = 0 := by
        intro y
        have h2 : (x, y) ∉ R := by
          simp [hR_def] ; aesop
        simp [h2]
      have h3 : (∫ y : ℝ, Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) ∂μ) = ∫ y : ℝ, (0 : ℝ) ∂μ := by
        congr 1 with y
        exact h1 y
      rw [h3]
      simp
  have h4 : ∫ x : ℝ, ∫ y : ℝ, Set.indicator R (fun p : ℝ × ℝ => p.1) (x, y) ∂μ ∂μ = ∫ x : ℝ, (if h : x ∈ Icc (0 : ℝ) 1 then x * f x else 0) ∂μ := by
    congr with x
    exact h_inner x
  rw [h4]
  have h5 : (∫ x : ℝ, (if h : x ∈ Icc (0 : ℝ) 1 then x * f x else 0) ∂μ) = ∫ x in Icc (0 : ℝ) 1, x * f x := by
    rw [← integral_indicator (show MeasurableSet (Icc (0 : ℝ) 1) from measurableSet_Icc)]
    congr with x ; aesop
  exact h5

lemma round2_den_eq_real (g : ℝ → ℝ)
  (hg : ∀ x ∈ Icc 0 1, 0 ≤ g x)
  (hgc : Continuous g):
  (∫ p : ℝ × ℝ, Set.indicator ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ g x.1 }) (fun (_ : ℝ × ℝ) => (1 : ℝ)) p ∂volume)
  = ∫ x in Icc (0:ℝ) 1, g x := by
  let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ g x.1 }
  have hR_def : R = { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ g x.1 } := rfl
  have h_meas : MeasurableSet R := round2_R_measurable g hgc
  have hvol_R_finite : volume R < ⊤ := round2_R_finite_volume g hg hgc
  have h_bdd : ∀ (p : ℝ × ℝ), ‖Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p‖ ≤ (1 : ℝ) := by
    intro p
    have h : Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p = if p ∈ R then (1 : ℝ) else (0 : ℝ) := by
      rw [Set.indicator_apply]
    rw [h]
    split_ifs <;> norm_num
  have h_aem : AEMeasurable (fun (p : ℝ × ℝ) => Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p) volume := by
    have h_meas' : Measurable (fun (p : ℝ × ℝ) => Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p) := by
      exact (measurable_indicator_const_iff 1).mpr h_meas
    exact h_meas'.aemeasurable
  have h_support : Function.support (Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ))) ⊆ R := by
    intro p hp
    simpa [Function.support, Set.indicator_apply] using hp
  have h_hfi : HasFiniteIntegral (fun (p : ℝ × ℝ) => Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p) volume :=
    round2_has_finite_integral volume (fun (p : ℝ × ℝ) => Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p) R h_meas hvol_R_finite h_bdd h_support h_aem
  let F : (ℝ × ℝ) → ℝ := fun p => Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p
  have h_aessm : AEStronglyMeasurable F volume := h_aem.aestronglyMeasurable
  have h_int : Integrable F volume := ⟨h_aessm, h_hfi⟩
  let μ : Measure ℝ := volume
  have hvol_eq : (volume : Measure (ℝ × ℝ)) = μ.prod μ := by exact rfl
  have h_main : (∫ p : ℝ × ℝ, F p ∂volume) = ∫ x : ℝ, ∫ y : ℝ, F (x, y) ∂μ ∂μ := by
    have h1 : (volume : Measure (ℝ × ℝ)) = μ.prod μ := hvol_eq
    rw [h1]
    have h2 : Integrable F (μ.prod μ) := by
      simpa [h1] using h_int
    simpa using MeasureTheory.integral_prod (μ := μ) (ν := μ) (f := F) h2
  have h_inner : ∀ (x : ℝ), (∫ y : ℝ, F (x, y) ∂μ) = if h : x ∈ Icc (0 : ℝ) 1 then g x else 0 := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp only [hx, dif_pos]
      have hgx : 0 ≤ g x := hg x hx
      have h1 : ∀ (y : ℝ), F (x, y) = Set.indicator (Icc (0 : ℝ) (g x)) (fun (_ : ℝ) => (1 : ℝ)) y := by
        intro y
        have h2 : ((x, y) ∈ R ↔ y ∈ Icc (0 : ℝ) (g x)) := by
          simp [hR_def] ; aesop
        simp only [F, Set.indicator_apply]
        split_ifs <;> aesop
      have h3 : (∫ y : ℝ, F (x, y) ∂μ) = ∫ y : ℝ, Set.indicator (Icc (0 : ℝ) (g x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ := by
        congr 1 with y
        exact h1 y
      rw [h3]
      have h42 : (∫ y : ℝ, Set.indicator (Icc (0 : ℝ) (g x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ) = ∫ (y : ℝ) in Icc 0 (g x), (1 : ℝ) := by
        have h421 : (∫ y : ℝ, Set.indicator (Icc (0 : ℝ) (g x)) (fun (_ : ℝ) => (1 : ℝ)) y ∂μ) = ∫ (y : ℝ) in Icc (0 : ℝ) (g x), (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator (show MeasurableSet (Icc (0 : ℝ) (g x)) from measurableSet_Icc)]
        exact h421
      rw [h42]
      have h43 : (∫ (y : ℝ) in Icc 0 (g x), (1 : ℝ)) = g x := round1_h3 g hg x hx
      rw [h43]
    · simp only [hx, dif_neg, not_false_eq_true]
      have h1 : ∀ (y : ℝ), F (x, y) = 0 := by
        intro y
        have h2 : (x, y) ∉ R := by
          simp [hR_def] ; aesop
        simp [F, Set.indicator_apply, h2]
      have h3 : (∫ y : ℝ, F (x, y) ∂μ) = ∫ y : ℝ, (0 : ℝ) ∂μ := by
        congr 1 with y
        exact h1 y
      rw [h3] ; simp
  have h4 : ∫ x : ℝ, ∫ y : ℝ, F (x, y) ∂μ ∂μ = ∫ x : ℝ, (if h : x ∈ Icc (0 : ℝ) 1 then g x else 0) ∂μ := by
    congr with x
    exact h_inner x
  have h5 : (∫ x : ℝ, (if h : x ∈ Icc (0 : ℝ) 1 then g x else 0) ∂μ) = ∫ x in Icc (0 : ℝ) 1, g x := by
    rw [← integral_indicator (show MeasurableSet (Icc (0 : ℝ) 1) from measurableSet_Icc)]
    congr with x ; aesop
  calc
    (∫ p : ℝ × ℝ, Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p ∂volume)
      = ∫ p : ℝ × ℝ, F p ∂volume := by rfl
    _ = ∫ x : ℝ, ∫ y : ℝ, F (x, y) ∂μ ∂μ := h_main
    _ = ∫ x : ℝ, (if h : x ∈ Icc (0 : ℝ) 1 then g x else 0) ∂μ := h4
    _ = ∫ x in Icc (0 : ℝ) 1, g x := h5

lemma round2_h_den (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfc : Continuous f)
  (R : Set (ℝ × ℝ))
  (hR_def : R = { x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 })
  (hR_meas : MeasurableSet R):
  (volume R).toReal = ∫ (x : ℝ) in Icc (0 : ℝ) 1, f x := by
  have h₁ : (∫ (p : ℝ × ℝ), Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p ∂volume) = ∫ (x : ℝ) in Icc (0 : ℝ) 1, f x := by
    have h₁₁ : (∫ (p : ℝ × ℝ), Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p ∂volume) = (∫ (p : ℝ × ℝ), Set.indicator ({ x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }) (fun (_ : ℝ × ℝ) => (1 : ℝ)) p ∂volume) := by
      rw [hR_def]
    rw [h₁₁]
    exact round2_den_eq_real f hf hfc
  have h₂ : (∫ (p : ℝ × ℝ), Set.indicator R (fun (_ : ℝ × ℝ) => (1 : ℝ)) p ∂volume) = ∫ p in R, (1 : ℝ) ∂volume := by
    rw [integral_indicator]
    aesop
  have h₃ : (∫ p in R, (1 : ℝ) ∂volume) = (volume R).toReal := by
    have h₃₁ : (∫ p in R, (1 : ℝ) ∂volume) = (volume R).toReal • (1 : ℝ) := by
      apply MeasureTheory.setIntegral_const
    simpa using h₃₁
  rw [h₂, h₃] at h₁
  exact h₁

lemma round2_intervalIntegral_eq_Icc (f : ℝ → ℝ):
  (∫ (x : ℝ) in (0)..1, f x) = (∫ (x : ℝ) in Icc (0 : ℝ) 1, f x) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have h_main₁ : (∫ (x : ℝ) in (0)..1, f x) = ∫ (x : ℝ) in Ioc (0 : ℝ) 1, f x := by
    have h₃ : (∫ (x : ℝ) in (0)..1, f x) = ∫ (x : ℝ) in Ioc (0 : ℝ) 1, f x := by
      exact intervalIntegral.integral_of_le h01
    exact h₃
  have h_main₂ : (∫ (x : ℝ) in Icc (0 : ℝ) 1, f x) = ∫ (x : ℝ) in Ioc (0 : ℝ) 1, f x := by
    apply MeasureTheory.integral_Icc_eq_integral_Ioc (x := (0 : ℝ)) (y := 1)
  rw [h_main₁, h_main₂]

theorem x1_is_B_div_A (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
   let x₁ : ℝ := ⨍ x in R, x.1;
   x₁) = (∫ (x : ℝ) in (0)..1, x * f x) / (∫ (x : ℝ) in (0)..1, f x) := by
  let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }
  have hR_def : R = { x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 } := by rfl
  have hR_meas : MeasurableSet R := round2_R_measurable f hfc
  have hR_fin : volume R < ⊤ := round2_R_finite_volume f hf hfc
  dsimp only
  change (⨍ x in R, x.1) = (∫ (x : ℝ) in (0)..1, x * f x) / (∫ (x : ℝ) in (0)..1, f x)
  have h_avg : (⨍ x in R, x.1) = (volume R).toReal⁻¹ * ∫ x in R, x.1 := by
    have h₁ : ( (⨍ x in R, x.1 : ℝ) ) = (volume R).toReal⁻¹ • (∫ x in R, x.1 : ℝ) := by
      have h₂ : ( (⨍ x in R, x.1 : ℝ) ) = (volume R).toReal⁻¹ • ∫ x in R, x.1 := by
        simpa using (MeasureTheory.setAverage_eq (f := fun (p : ℝ × ℝ) ↦ p.1) (s := R) (μ := volume))
      exact h₂
    simpa [smul_eq_mul] using h₁
  have h_num : ∫ x in R, x.1 = ∫ (x : ℝ) in Icc (0 : ℝ) 1, x * f x := by
    have h₁ : ∫ x in R, x.1 = ∫ (p : ℝ × ℝ), Set.indicator R (fun p : ℝ × ℝ ↦ p.1) p ∂volume := by
      rw [integral_indicator]
      aesop
    rw [h₁]
    simpa [R] using round2_num_eq_iterated f hf hfc
  have h_den : (volume R).toReal = ∫ (x : ℝ) in Icc (0 : ℝ) 1, f x := by
    exact round2_h_den f hf hfc R hR_def hR_meas
  have h_main₁ : ∫ (x : ℝ) in (0)..1, x * f x = ∫ (x : ℝ) in Icc (0 : ℝ) 1, x * f x := by
    exact round2_intervalIntegral_eq_Icc (fun (x : ℝ) ↦ x * f x)
  have h_main₂ : ∫ (x : ℝ) in (0)..1, f x = ∫ (x : ℝ) in Icc (0 : ℝ) 1, f x := by
    exact round2_intervalIntegral_eq_Icc f
  have h_main : (⨍ x in R, x.1) = ((volume R).toReal)⁻¹ * ∫ x in Icc (0 : ℝ) 1, x * f x := by
    rw [h_avg, h_num]
  have h_final : ((volume R).toReal)⁻¹ * ∫ x in Icc (0 : ℝ) 1, x * f x = (∫ x in Icc (0 : ℝ) 1, x * f x) / (volume R).toReal := by
    rw [div_eq_mul_inv]
    ring
  rw [h_main, h_final, h_den, h_main₁, h_main₂]

lemma round1_h1' (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x):
  (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
   let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ };
   R' ⊆ { p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 }) := by
  dsimp only
  intro p hp
  rcases hp with ⟨x, hx, θ, h1, h2, h3⟩
  have h4 : 0 ≤ x.1 := hx.1
  have h5 : x.1 ≤ 1 := hx.2.1
  have h6 : 0 ≤ x.2 := hx.2.2.1
  have h7 : x.2 ≤ f x.1 := hx.2.2.2
  have h8 : p.1 = x.1 := h1
  have h9 : p.2.1 = x.2 * Real.cos θ := h2
  have h10 : p.2.2 = x.2 * Real.sin θ := h3
  have h11 : p.1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h12 : p.2.1 ^ 2 + p.2.2 ^ 2 = x.2 ^ 2 := by
    rw [h9, h10]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have h13 : x.2 ^ 2 ≤ (f x.1) ^ 2 := by nlinarith [hf x.1 ⟨by linarith, by linarith⟩]
  have h14 : p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 := by
    rw [h8] at *
    nlinarith
  exact ⟨h11, h14⟩

lemma round1_h2 (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x):
  (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
   let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ };
   { p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 } ⊆ R') := by
  dsimp only
  intro p hp
  have h1 : p.1 ∈ Set.Icc (0 : ℝ) 1 := hp.1
  have h2 : p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 := hp.2
  have h1' : 0 ≤ p.1 := h1.1
  have h1'' : p.1 ≤ 1 := h1.2
  set x₂ : ℝ := Real.sqrt (p.2.1 ^ 2 + p.2.2 ^ 2) with hx₂_def
  have h3 : 0 ≤ x₂ := Real.sqrt_nonneg _
  have h4 : x₂ ^ 2 = p.2.1 ^ 2 + p.2.2 ^ 2 := by
    rw [Real.sq_sqrt] ; nlinarith
  have h5 : x₂ ≤ f p.1 := by
    nlinarith [hf p.1 h1]
  have h6 : 0 ≤ f p.1 := hf p.1 h1
  let x : ℝ × ℝ := (p.1, x₂)
  have hx : x ∈ { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨h1', h1'', h3, h5⟩
  by_cases h10 : x₂ = 0
  ·
    have h11 : p.2.1 ^ 2 + p.2.2 ^ 2 = 0 := by
      nlinarith [h4]
    have h12 : p.2.1 = 0 := by nlinarith
    have h13 : p.2.2 = 0 := by nlinarith
    refine ⟨x, hx, (0 : ℝ), by simp [x], ?_⟩
    norm_num ; aesop
  ·
    have h10' : 0 < x₂ := by
      exact lt_of_le_of_ne h3 (Ne.symm h10)
    have h11 : p.2.1 ^ 2 ≤ x₂ ^ 2 := by nlinarith
    have h12 : (p.2.1 / x₂) ^ 2 ≤ 1 := by
      have h13 : (p.2.1 / x₂) ^ 2 = p.2.1 ^ 2 / x₂ ^ 2 := by
        field_simp [h10']
      rw [h13]
      have h14 : 0 < x₂ ^ 2 := by positivity
      rw [div_le_one h14]
      nlinarith
    have h14 : -1 ≤ p.2.1 / x₂ ∧ p.2.1 / x₂ ≤ 1 := by
      have h15 : (p.2.1 / x₂) ^ 2 ≤ 1 := h12
      have h16 : -1 ≤ p.2.1 / x₂ := by nlinarith [sq_nonneg (p.2.1 / x₂)]
      have h17 : p.2.1 / x₂ ≤ 1 := by nlinarith [sq_nonneg (p.2.1 / x₂)]
      exact ⟨h16, h17⟩
    set θ : ℝ := Real.arccos (p.2.1 / x₂) with hθ_def
    have h21 : Real.cos θ = p.2.1 / x₂ := by
      rw [hθ_def]
      rw [Real.cos_arccos] <;> linarith [h14.1, h14.2]
    have h22 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have h23 : Real.sin θ ^ 2 = (p.2.2 / x₂) ^ 2 := by
      have h24 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
      rw [h24, h21]
      field_simp [h10'] ; nlinarith [h4]
    have h25 : Real.sin θ = p.2.2 / x₂ ∨ Real.sin θ = - (p.2.2 / x₂) := by
      have h26 : Real.sin θ ^ 2 - (p.2.2 / x₂) ^ 2 = 0 := by linarith
      have h27 : (Real.sin θ - (p.2.2 / x₂)) * (Real.sin θ + (p.2.2 / x₂)) = 0 := by linarith
      have h28 : (Real.sin θ - (p.2.2 / x₂)) = 0 ∨ (Real.sin θ + (p.2.2 / x₂)) = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h27
      cases h28 with
      | inl h28 =>
        left
        linarith
      | inr h28 =>
        right
        linarith
    cases h25 with
    | inl h25 =>
      refine ⟨x, hx, θ, by simp [x], ?_⟩
      constructor
      · have h29 : x.2 * Real.cos θ = p.2.1 := by
          simp [x, h21] ; field_simp [h10']
        exact Eq.symm h29
      · have h30 : x.2 * Real.sin θ = p.2.2 := by
          simp [x, h25] ; field_simp [h10']
        exact Eq.symm h30
    | inr h25 =>
      let θ' := -θ
      have h31 : Real.cos θ' = Real.cos θ := by
        simp [θ', Real.cos_neg]
      have h32 : Real.sin θ' = - Real.sin θ := by
        simp [θ', Real.sin_neg]
      have h33 : Real.sin θ' = p.2.2 / x₂ := by
        rw [h32, h25] ; ring
      refine ⟨x, hx, θ', by simp [x], ?_⟩
      constructor
      · have h34 : x.2 * Real.cos θ' = p.2.1 := by
          rw [h31]
          simp [x, h21] ; field_simp [h10']
        exact Eq.symm h34
      · have h35 : x.2 * Real.sin θ' = p.2.2 := by
          rw [h33]
          simp [x] ; field_simp [h10']
        exact Eq.symm h35

lemma h_abs (x y : ℝ):
  Complex.abs (⟨x, y⟩ : ℂ) = Real.sqrt (x ^ 2 + y ^ 2) := by
  have h1 : Complex.normSq (⟨x, y⟩ : ℂ) = x ^ 2 + y ^ 2 := by
    simp [Complex.normSq]
    ring
  have h2 : Complex.abs (⟨x, y⟩ : ℂ) = Real.sqrt (Complex.normSq (⟨x, y⟩ : ℂ)) := by
    exact rfl
  rw [h2, h1]

lemma round2_eq_S (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x):
  (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
   let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ };
   (R' : Set (ℝ × ℝ × ℝ))) =
  ({ p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 }) := by
  dsimp only
  let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }
  let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ }
  let S : Set (ℝ × ℝ × ℝ) := { p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 }
  have h1 : R' ⊆ S := round1_h1' f hf
  have h2 : S ⊆ R' := round1_h2 f hf
  have h3 : R' = S := Set.Subset.antisymm h1 h2
  exact h3

lemma h_ennreal_nnreal (x : NNReal):
  (↑x : ENNReal) = ENNReal.ofReal (↑x : ℝ) := by
  exact ENNReal.coe_nnreal_eq x

lemma round2_disc_volume :
  ∀ (r : ℝ), 0 ≤ r →
    MeasureTheory.volume ({ q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2 } : Set (ℝ × ℝ)) =
    ENNReal.ofReal (Real.pi * r ^ 2) := by
  intro r hr
  let e : (ℝ × ℝ) ≃ ℂ := Complex.measurableEquivRealProd.symm
  have h1 : MeasureTheory.MeasurePreserving e volume volume := by
    exact Complex.volume_preserving_equiv_real_prod.symm
  let A : Set (ℝ × ℝ) := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2 }
  have hA1 : A = (fun (p : ℝ × ℝ) => p.1 ^ 2 + p.2 ^ 2) ⁻¹' (Set.Iic (r ^ 2)) := by
    ext ⟨x, y⟩
    simp [A, Set.Iic]
  have h_cont : Continuous (fun (p : ℝ × ℝ) => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
  have h_cont_m : Measurable (fun (p : ℝ × ℝ) => p.1 ^ 2 + p.2 ^ 2) := by exact Continuous.measurable h_cont
  have h2 : MeasurableSet (Set.Iic (r ^ 2 : ℝ)) := by exact measurableSet_Iic
  have hA_meas : MeasurableSet A := by
    rw [hA1]
    exact h_cont_m h2
  have h_eq_img : e '' A = Metric.closedBall (0 : ℂ) r := by
    ext z
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq1 : q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2 := hq
      have h_abs_eq : Complex.abs (e q) = Real.sqrt (q.1 ^ 2 + q.2 ^ 2) := by
        exact h_abs (e q).re (e q).im
      have h2 : Complex.abs (e q) ≤ r := by
        rw [h_abs_eq]
        apply Real.sqrt_le_iff.mpr
        constructor <;> nlinarith
      have h3 : Dist.dist (e q) 0 = Complex.abs (e q - 0) := by
        rw [Complex.dist_eq]
      have h4 : Dist.dist (e q) 0 ≤ r := by
        rw [h3]
        simpa using h2
      exact h4
    · intro hz
      let q : ℝ × ℝ := (z.re, z.im)
      have h_dist : Dist.dist z 0 ≤ r := hz
      have h_abs : Complex.abs z ≤ r := by
        have h3 : Dist.dist z 0 = Complex.abs (z - 0) := by
          rw [Complex.dist_eq]
        have h4 : Dist.dist z 0 = Complex.abs z := by
          simp
        rw [h4] at h_dist
        exact h_dist
      have hq : q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2 := by
        have h_eq2 : q.1 ^ 2 + q.2 ^ 2 = Complex.normSq z := by
          simp [q, Complex.normSq] ; ring
        have h3 : (Complex.abs z) ^ 2 = Complex.normSq z := by exact Complex.sq_abs z
        have h4 : 0 ≤ Complex.abs z := by positivity
        have h5 : (Complex.abs z) ^ 2 ≤ r ^ 2 := by nlinarith
        rw [h_eq2, ← h3]
        exact h5
      refine ⟨q, hq, ?_⟩
      simp [e, q]
  have h1' : MeasureTheory.MeasurePreserving e.symm volume volume := by
    exact h1.symm
  have h41 : ∀ (s : Set (ℝ × ℝ)), MeasurableSet s → volume (e '' s) = volume s := by
    intro s hs
    have h42 : e '' s = e.symm ⁻¹' s := by
      simp [Equiv.image_eq_preimage]
    rw [h42]
    have h45 : NullMeasurableSet s (μ := volume) := hs.nullMeasurableSet
    have h46 : volume (e.symm ⁻¹' s) = volume s := by
      exact h1'.measure_preimage h45
    exact h46
  have h4 : volume (e '' A) = volume A := h41 A hA_meas
  rw [← h4, h_eq_img]
  have h5 : volume (Metric.closedBall (0 : ℂ) r) = (ENNReal.ofReal r) ^ 2 * (NNReal.pi : ENNReal) :=
    Complex.volume_closedBall (0 : ℂ) r
  rw [h5]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h71 : (NNReal.pi : ℝ) = Real.pi := by norm_num [NNReal.pi]
  have h72 : ( (NNReal.pi : ENNReal) ) = ENNReal.ofReal ( (NNReal.pi : ℝ) ) := h_ennreal_nnreal NNReal.pi
  rw [h72, h71]
  have h8 : (ENNReal.ofReal r) ^ 2 * ENNReal.ofReal Real.pi = ENNReal.ofReal (Real.pi * r ^ 2) := by
    have h9 : (ENNReal.ofReal r) ^ 2 = ENNReal.ofReal (r * r) := by
      rw [pow_two, ENNReal.ofReal_mul (show 0 ≤ r by linarith)]
    rw [h9]
    have h10 : ENNReal.ofReal (r * r) * ENNReal.ofReal Real.pi = ENNReal.ofReal ((r * r) * Real.pi) := by
      rw [ENNReal.ofReal_mul (show 0 ≤ r * r by positivity)]
    rw [h10]
    have h11 : (r * r) * Real.pi = Real.pi * r ^ 2 := by ring
    rw [h11]
  exact h8

lemma round2_hA_meas (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (x : ℝ)
  (hx : x ∈ Icc (0 : ℝ) 1):
  MeasurableSet {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2} := by
  have h_cont : Continuous (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) := by fun_prop
  have h_meas : Measurable (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) := h_cont.measurable
  have h_meas_set : MeasurableSet (Set.Iic ((f x) ^ 2 : ℝ)) := by
    exact isClosed_Iic.measurableSet
  have h_main : MeasurableSet ( (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) ⁻¹' (Set.Iic ((f x) ^ 2 : ℝ)) ) :=
    h_meas h_meas_set
  simpa only [Set.preimage] using h_main

lemma round2_S_meas (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfc : Continuous f):
  MeasurableSet ({ p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 }) := by
  let S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2 }
  have h_fst : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := by fun_prop
  have h2 : MeasurableSet (Set.Icc (0 : ℝ) 1) := isClosed_Icc.measurableSet
  have h6 : MeasurableSet ((fun p : ℝ × ℝ × ℝ => p.1) ⁻¹' (Set.Icc (0 : ℝ) 1)) := by
    exact h_fst h2
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1 ^ 2 + p.2.2 ^ 2) := by fun_prop
  have h4 : Measurable (fun p : ℝ × ℝ × ℝ => (f p.1) ^ 2) := by
    have h5 : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := by fun_prop
    exact (hfc.comp h5).pow 2 |>.measurable
  have h5 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1) ^ 2} := by
    exact measurableSet_le h3 h4
  have h7 : MeasurableSet S := h6.inter h5
  exact h7

lemma round2_den_pos (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  0 < ∫ x in (0)..1, (f x)^2 := by
  let g : ℝ → ℝ := fun x ↦ (f x)^2
  have hg_cont : Continuous g := by
    have h1 : Continuous (fun x : ℝ => f x) := hfc
    have h2 : Continuous (fun x : ℝ => (f x)^2) := by exact h1.pow 2
    exact h2
  have h0le : 0 ≤ f 0 := hf 0 (by norm_num)
  have h01 : f 0 < f 1 := hfm (by norm_num)
  have hpos1 : 0 < f 1 := by
    have h1 : 0 ≤ f 0 := h0le
    have h2 : f 0 < f 1 := h01
    linarith
  have hpos1sq : 0 < (f 1)^2 := by positivity
  have h_nonneg_Icc : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x := by
    intro x hx
    have h5 : 0 ≤ f x := hf x hx
    positivity
  have h_nonneg_Ioc : ∀ x ∈ Ioc (0:ℝ) 1, 0 ≤ g x := by
    intro x hx
    have h6 : x ∈ Icc (0:ℝ) 1 := by exact ⟨hx.1.le, hx.2⟩
    exact h_nonneg_Icc x h6
  have hpos_Icc : ∃ c ∈ Icc (0:ℝ) 1, 0 < g c := ⟨1, by norm_num, hpos1sq⟩
  have h_cont_on : ContinuousOn g (Icc (0:ℝ) 1) := hg_cont.continuousOn
  have h_main : 0 < ∫ x in (0)..1, g x := by
    apply intervalIntegral.integral_pos (by norm_num) h_cont_on h_nonneg_Ioc hpos_Icc
  simpa [g] using h_main

lemma helper_integrable (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f):
  ENNReal.ofReal (∫ x in Set.Icc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume)
  = ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((f x)^2) ∂MeasureTheory.volume := by
  have h_nonneg : ∀ x : ℝ, 0 ≤ (f x)^2 := fun x => by positivity
  have h_int : IntegrableOn (fun x : ℝ => (f x)^2) (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn (hfc.pow 2) |>.integrableOn_Icc
  have h_pos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)), 0 ≤ (f x)^2 := by
    filter_upwards with x
    exact h_nonneg x
  have h12 : AEStronglyMeasurable (fun x : ℝ => (f x)^2) (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact (hfc.pow 2).continuousOn.aestronglyMeasurable measurableSet_Icc
  have h19 : ENNReal.ofReal (∫ x in Set.Icc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume) = (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((f x)^2) ∂MeasureTheory.volume) := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_pos
  exact h19

lemma round2_disc_volume_ofReal (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (x : ℝ)
  (hx : x ∈ Set.Icc (0 : ℝ) 1):
  MeasureTheory.volume ({ q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 })
  = ENNReal.ofReal (Real.pi * (f x)^2) := by
  have h1 : 0 ≤ f x := hf x hx
  exact round2_disc_volume (f x) h1

lemma round2_den_eq_step1 (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f):
  let S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 }
  let E (x : ℝ) : Set (ℝ × ℝ) := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }
  MeasureTheory.volume S = ∫⁻ x in Set.Icc (0 : ℝ) 1, MeasureTheory.volume (E x) ∂MeasureTheory.volume := by
  let S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 }
  let E (x : ℝ) : Set (ℝ × ℝ) := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }
  have hS_meas : MeasurableSet S := round2_S_meas f hf hfc
  have h_main1 : MeasureTheory.volume S = ∫⁻ x, MeasureTheory.volume ({q : ℝ × ℝ | (x, q) ∈ S}) ∂MeasureTheory.volume := by
    rw [show (MeasureTheory.volume : Measure (ℝ × ℝ × ℝ)) = (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure (ℝ × ℝ)) from by exact rfl]
    exact Measure.prod_apply hS_meas
  have h2 : ∀ (x : ℝ), {q : ℝ × ℝ | (x, q) ∈ S} = if h : x ∈ Set.Icc (0 : ℝ) 1 then E x else (∅ : Set (ℝ × ℝ)) := by
    intro x
    ext q
    simp only [S, E, Set.mem_setOf_eq] ; aesop
  have h3 : ∀ (x : ℝ), MeasureTheory.volume ({q : ℝ × ℝ | (x, q) ∈ S}) = (if h : x ∈ Set.Icc (0 : ℝ) 1 then MeasureTheory.volume (E x) else 0) := by
    intro x
    rw [h2 x] ; split_ifs <;> simp
  have h_main2 : (∫⁻ x, MeasureTheory.volume ({q : ℝ × ℝ | (x, q) ∈ S}) ∂MeasureTheory.volume) = (∫⁻ x, (if h : x ∈ Set.Icc (0 : ℝ) 1 then MeasureTheory.volume (E x) else 0) ∂MeasureTheory.volume) := by
    congr with x
    exact h3 x
  have h5₁ : (fun (x : ℝ) => (if h : x ∈ Set.Icc (0 : ℝ) 1 then MeasureTheory.volume (E x) else 0)) = Set.indicator (Set.Icc (0 : ℝ) 1) (fun (x : ℝ) => MeasureTheory.volume (E x)) := by
    ext x
    simp [Set.indicator]
  have hIcc_meas : MeasurableSet (Set.Icc (0 : ℝ) 1) := by exact measurableSet_Icc
  have h5 : (∫⁻ x, Set.indicator (Set.Icc (0 : ℝ) 1) (fun (x : ℝ) => MeasureTheory.volume (E x)) x ∂MeasureTheory.volume) = (∫⁻ x in Set.Icc (0 : ℝ) 1, MeasureTheory.volume (E x) ∂MeasureTheory.volume) := by
    rw [MeasureTheory.lintegral_indicator hIcc_meas]
  have h6 : MeasureTheory.volume S = ∫⁻ x, MeasureTheory.volume ({q : ℝ × ℝ | (x, q) ∈ S}) ∂MeasureTheory.volume := h_main1
  rw [h_main2, h5₁, h5] at h6
  exact h6

lemma round2_den_eq_step2 (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f)
  (hfm : StrictMono f):
  (∫⁻ x in Set.Icc (0 : ℝ) 1, MeasureTheory.volume ({ q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }) ∂MeasureTheory.volume)
  = ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2) := by
  let E (x : ℝ) : Set (ℝ × ℝ) := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }
  have h_pos_pi : 0 ≤ Real.pi := Real.pi_pos.le
  have hvol (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : MeasureTheory.volume (E x) = ENNReal.ofReal (Real.pi * (f x)^2) :=
    round2_disc_volume_ofReal f hf x hx
  have h1 : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → MeasureTheory.volume (E x) = ENNReal.ofReal (Real.pi * (f x)^2) := fun x hx => hvol x hx
  have h_mem : MeasurableSet (Set.Icc (0 : ℝ) 1) := by exact measurableSet_Icc
  have h2 : ∀ᵐ (x : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)), MeasureTheory.volume (E x) = ENNReal.ofReal (Real.pi * (f x) ^ 2) := by
    exact MeasureTheory.ae_restrict_of_forall_mem h_mem h1
  have h_step2 : (∫⁻ x in Set.Icc (0 : ℝ) 1, MeasureTheory.volume (E x) ∂MeasureTheory.volume)
      = ∫⁻ x in Set.Icc (0 : ℝ) 1, (ENNReal.ofReal (Real.pi * (f x)^2)) ∂MeasureTheory.volume := by
    apply MeasureTheory.lintegral_congr_ae h2
  have h8 : ∀ x : ℝ, (ENNReal.ofReal (Real.pi * (f x)^2)) = ENNReal.ofReal Real.pi * ENNReal.ofReal ((f x)^2) := by
    intro x
    rw [ENNReal.ofReal_mul h_pos_pi]
  have h9 : Measurable (fun x : ℝ => ENNReal.ofReal ((f x)^2)) := by
    have h10 : Continuous (fun x : ℝ => (f x)^2) := hfc.pow 2
    have h11 : Measurable (fun x : ℝ => (f x)^2) := h10.measurable
    exact h11.ennreal_ofReal
  have h_step3 : (∫⁻ x in Set.Icc (0 : ℝ) 1, (ENNReal.ofReal (Real.pi * (f x)^2)) ∂MeasureTheory.volume)
      = ENNReal.ofReal Real.pi * ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((f x)^2) ∂MeasureTheory.volume := by
    conv_lhs => rw [show (fun x : ℝ => ENNReal.ofReal (Real.pi * (f x)^2)) = fun x => ENNReal.ofReal Real.pi * ENNReal.ofReal ((f x)^2) from by funext x; exact h8 x]
    rw [MeasureTheory.lintegral_const_mul _ h9]
  have h19 := helper_integrable f hf hfc
  have h_step4 : (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((f x)^2) ∂MeasureTheory.volume)
      = ENNReal.ofReal (∫ x in Set.Icc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume) := by
    exact h19.symm
  have h_nonneg : 0 ≤ fun (x : ℝ) => (f x)^2 := by
    exact fun x => sq_nonneg (f x)
  have h20 : 0 ≤ ∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_nonneg
    exact h_nonneg
  have h_eq1 : (∫ x in Set.Icc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume) = (∫ x in (0)..1, (f x)^2) := by
    have h_Icc_eq_Ioc : ∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume = ∫ (x : ℝ) in Set.Ioc (0 : ℝ) 1, (f x)^2 ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_Icc_eq_integral_Ioc' (show (MeasureTheory.volume : Measure ℝ) {0} = 0 from by simp)
    simp [intervalIntegral, h_Icc_eq_Ioc]
  have h10 : 0 ≤ ∫ (x : ℝ) in (0)..1, (f x)^2 := by
    rw [← h_eq1]
    exact h20
  have h_goal : ENNReal.ofReal Real.pi * ENNReal.ofReal (∫ (x : ℝ) in (0)..1, (f x)^2) = ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2) := by
    rw [← ENNReal.ofReal_mul h_pos_pi]
  rw [h_step2, h_step3, h_step4, h_eq1, h_goal]

lemma round2_den_eq (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f)
  (hfm : StrictMono f):
  MeasureTheory.volume ({ p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 })
  = ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2) := by
  let S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 }
  let E (x : ℝ) : Set (ℝ × ℝ) := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }
  have h_step1 : MeasureTheory.volume S = ∫⁻ x in Set.Icc (0 : ℝ) 1, MeasureTheory.volume (E x) ∂MeasureTheory.volume :=
    round2_den_eq_step1 f hf hfc
  have h_step2 : (∫⁻ x in Set.Icc (0 : ℝ) 1, MeasureTheory.volume (E x) ∂MeasureTheory.volume)
      = ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2) :=
    round2_den_eq_step2 f hf hfc hfm
  rw [h_step1, h_step2]

lemma round2_proj_integrable (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfc : Continuous f)
  (hfm : StrictMono f):
  Integrable (fun p : ℝ × ℝ × ℝ => p.1) (MeasureTheory.volume.restrict
    ({ p : ℝ × ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 })) := by
  let S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 }
  have hS_meas : MeasurableSet S := round2_S_meas f hf hfc
  have h1 : ∀ (p : ℝ × ℝ × ℝ), p ∈ S → p.1 ∈ Set.Icc (0 : ℝ) 1 := by
    intro p hp
    exact hp.1
  have h_den_eq : MeasureTheory.volume S = ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2) :=
    round2_den_eq f hf hfc hfm
  let c : ℝ := Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2
  have h_den_eq2 : MeasureTheory.volume S = ENNReal.ofReal c := h_den_eq
  have h_lt_top : MeasureTheory.volume S < ⊤ := by
    rw [h_den_eq2]
    exact ENNReal.ofReal_lt_top
  have h_main : (MeasureTheory.volume.restrict S) Set.univ < ⊤ := by
    have h_eq : (MeasureTheory.volume.restrict S) Set.univ = MeasureTheory.volume S := by
      rw [MeasureTheory.Measure.restrict_apply_univ]
    rw [h_eq]
    exact h_lt_top
  have h_instance : IsFiniteMeasure (MeasureTheory.volume.restrict S) := by
    constructor
    exact h_main
  have h_cont : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := by continuity
  have h_aemeasurable : AEMeasurable (fun p : ℝ × ℝ × ℝ => p.1) (MeasureTheory.volume.restrict S) := h_cont.aemeasurable
  have h2 : ∀ᵐ (p : ℝ × ℝ × ℝ) ∂(MeasureTheory.volume.restrict S), p.1 ∈ Set.Icc (0 : ℝ) 1 := by
    have h3 : ∀ (p : ℝ × ℝ × ℝ), p ∈ S → p.1 ∈ Set.Icc (0 : ℝ) 1 := h1
    have h4 : ∀ᵐ (p : ℝ × ℝ × ℝ) ∂(MeasureTheory.volume.restrict S), p ∈ S := by
      filter_upwards [MeasureTheory.ae_restrict_of_forall_mem hS_meas (fun x hx => hx)] with x hx
      exact hx
    filter_upwards [h4] with p hp
    exact h3 p hp
  exact Integrable.of_mem_Icc (0 : ℝ) 1 h_aemeasurable h2

lemma round2_inner_volume (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (x : ℝ)
  (hx : x ∈ Set.Icc (0 : ℝ) 1):
  (∫ q : ℝ × ℝ, Set.indicator ({ q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }) (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q ∂volume)
  = Real.pi * (f x) ^ 2 := by
  let E_x := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x) ^ 2 }
  have h_E_x_meas : MeasurableSet E_x := round2_hA_meas f hf x hx
  have hvol : MeasureTheory.volume E_x = ENNReal.ofReal (Real.pi * (f x)^2) := round2_disc_volume_ofReal f hf x hx
  have h_pos : 0 ≤ Real.pi * (f x)^2 := by positivity
  have h_main1 : (∫ q : ℝ × ℝ, Set.indicator E_x (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q ∂volume) = (∫ q in E_x, (1 : ℝ) ∂volume) := by
    rw [MeasureTheory.integral_indicator (s := E_x) (f := (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)))]
    aesop
  have h_main2 : (∫ q in E_x, (1 : ℝ) ∂volume) = (MeasureTheory.volume E_x).toReal * (1 : ℝ) := by
    have h₃ : (∫ q in E_x, (1 : ℝ) ∂MeasureTheory.volume) = MeasureTheory.volume.real E_x • (1 : ℝ) := by
      exact MeasureTheory.setIntegral_const (1 : ℝ) (s := E_x)
    simp [MeasureTheory.Measure.real, mul_comm]
  have h_main3 : (∫ q : ℝ × ℝ, Set.indicator E_x (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q ∂volume) = (MeasureTheory.volume E_x).toReal := by
    rw [h_main1, h_main2] ; ring
  have h_final : (MeasureTheory.volume E_x).toReal = Real.pi * (f x) ^ 2 := by
    rw [hvol]
    rw [ENNReal.toReal_ofReal h_pos]
  rw [h_main3, h_final]

lemma round2_num_eq (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  (∫ p : ℝ × ℝ × ℝ in
      ({ p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 }), p.1)
    = Real.pi * ∫ x : ℝ in Set.Icc (0 : ℝ) 1, x * (f x)^2 := by
  set S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 } with hS
  let h : (ℝ × ℝ × ℝ) → ℝ := fun p ↦ p.1
  let g (p : ℝ × ℝ × ℝ) : ℝ := Set.indicator S h p
  have h_S_meas : MeasurableSet S := round2_S_meas f hf hfc
  have h_main1 : (∫ p in S, h p ∂MeasureTheory.volume) = ∫ p : ℝ × ℝ × ℝ, g p ∂MeasureTheory.volume := by
    have h₁ := MeasureTheory.integral_indicator (μ := MeasureTheory.volume) (s := S) (f := h)
    have h₂ : (∫ p : ℝ × ℝ × ℝ, g p ∂MeasureTheory.volume) = (∫ (p : ℝ × ℝ × ℝ) in S, h p ∂MeasureTheory.volume) := by
      simpa [g] using h₁ h_S_meas
    exact h₂.symm
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let t (x : ℝ) : Set (ℝ × ℝ) := { q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ (f x)^2 }
  have h1 : IntegrableOn h S := round2_proj_integrable f hf hfc hfm
  have h_int_main : Integrable g := by
    have h2 : IntegrableOn h S := h1
    simpa [g, IntegrableOn, integrable_indicator_iff h_S_meas] using h2
  have hvol : MeasureTheory.volume (α := ℝ × ℝ × ℝ) = (MeasureTheory.volume (α := ℝ)).prod (MeasureTheory.volume (α := ℝ × ℝ)) := by exact rfl
  let h' : (ℝ × (ℝ × ℝ)) → ℝ := fun z ↦ g z
  have h_int_main' : Integrable h' (MeasureTheory.volume.prod MeasureTheory.volume) := by
    simpa [h', hvol] using h_int_main
  have h_main2 : ∫ p : ℝ × ℝ × ℝ, g p ∂MeasureTheory.volume = ∫ (x : ℝ), ∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    have h_eq1 : (∫ p : ℝ × ℝ × ℝ, g p ∂MeasureTheory.volume) = ∫ z : ℝ × (ℝ × ℝ), h' z ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
      simp [h', hvol]
    rw [h_eq1]
    have h_eq2 : ∫ (z : ℝ × (ℝ × ℝ)), h' z ∂(MeasureTheory.volume.prod MeasureTheory.volume) = ∫ (x : ℝ), ∫ (q : ℝ × ℝ), h' (x, q) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
      exact integral_prod h' h_int_main
    rw [h_eq2]
  let h3 (x : ℝ) : ℝ := ∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume
  have hs : MeasurableSet s := measurableSet_Icc
  have h4 : ∀ (x : ℝ), h3 x = if h1 : x ∈ s then x * (Real.pi * (f x)^2) else 0 := by
    intro x
    by_cases h1 : x ∈ s
    · have h5 : h3 x = ∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume := rfl
      rw [h5]
      have h6 : ∀ (q : ℝ × ℝ), g (x, q) = x * Set.indicator (t x) (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q := by
        intro q
        have h7 : (x, q) ∈ S ↔ q ∈ t x := by
          simp [S, t]
          aesop
        simp [g, h, h7, Set.indicator]
      have h7 : (∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume)
            = x * (Real.pi * (f x)^2) := by
        have h8 : (∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume)
              = ∫ (q : ℝ × ℝ), x * Set.indicator (t x) (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q ∂MeasureTheory.volume := by
          congr 1 ; funext q ; exact h6 q
        rw [h8]
        have h9 : (∫ (q : ℝ × ℝ), x * Set.indicator (t x) (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q ∂MeasureTheory.volume)
              = x * (∫ (q : ℝ × ℝ), Set.indicator (t x) (fun (_ : ℝ × ℝ) ↦ (1 : ℝ)) q ∂MeasureTheory.volume) := by
          rw [integral_mul_left]
        rw [h9]
        have h10 := round2_inner_volume f hf x h1
        rw [h10]
      simpa [h1] using h7
    · have h7 : h3 x = 0 := by
        have h8 : ∀ (q : ℝ × ℝ), g (x, q) = 0 := by
          intro q
          have h9 : (x, q) ∉ S := by
            simp [S] ; tauto
          simp [g, h, h9, Set.indicator]
        have h10 : (∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume) = 0 := by
          rw [show (∫ (q : ℝ × ℝ), g (x, q) ∂MeasureTheory.volume) = ∫ (q : ℝ × ℝ), (0 : ℝ) ∂MeasureTheory.volume from by
            congr 1 ; funext q ; exact h8 q]
          simp
        simpa using h10
      simp [h1, h7]
  have h5 : ∫ (x : ℝ), h3 x ∂MeasureTheory.volume = ∫ x in s, x * (Real.pi * (f x)^2) ∂MeasureTheory.volume := by
    have h6 : ∀ (x : ℝ), h3 x = (Set.indicator s (fun x ↦ x * (Real.pi * (f x)^2))) x := by
      intro x
      by_cases h1 : x ∈ s
      · simp [h4, h1, Set.indicator]
      · simp [h4, h1, Set.indicator]
    have h7 : h3 = Set.indicator s (fun x ↦ x * (Real.pi * (f x)^2)) := by
      funext x
      exact h6 x
    rw [h7]
    have hhs : MeasurableSet s := hs
    simpa using MeasureTheory.integral_indicator hhs
  rw [h_main1, h_main2, h5]
  have h8 : ∫ x in s, x * (Real.pi * (f x)^2) ∂MeasureTheory.volume = Real.pi * ∫ x in s, x * (f x)^2 ∂MeasureTheory.volume := by
    have h9 : (∫ x in s, x * (Real.pi * (f x)^2) ∂MeasureTheory.volume) = ∫ x in s, Real.pi * (x * (f x)^2) ∂MeasureTheory.volume := by
      congr 1 ; funext x ; ring
    rw [h9]
    have h10 : (∫ x in s, Real.pi * (x * (f x)^2) ∂MeasureTheory.volume) = Real.pi * ∫ x in s, x * (f x)^2 ∂MeasureTheory.volume := by
      rw [MeasureTheory.integral_mul_left]
    exact h10
  rw [h8]

theorem x2_is_D_div_C (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
   let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ };
   let x₂ : ℝ := ⨍ x' in R', x'.1;
   x₂) = (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) / (∫ (x : ℝ) in (0)..1, (f x) ^ 2) := by
  dsimp only
  let S : Set (ℝ × ℝ × ℝ) := { p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (f p.1)^2 }
  let R' : Set (ℝ × ℝ × ℝ) := { p' | ∃ x ∈ ({ x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 } : Set (ℝ × ℝ)), ∃ θ : ℝ, p'.1 = x.1 ∧ p'.2.1 = x.2 * Real.cos θ ∧ p'.2.2 = x.2 * Real.sin θ }
  have hR' : (R' : Set (ℝ × ℝ × ℝ)) = S := round2_eq_S f hf
  have hvol0 : MeasureTheory.volume ({(0 : ℝ)} : Set ℝ) = 0 := by simp
  have h_num_eq' : (∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, x * (f x)^2) = (∫ (x : ℝ) in (0)..1, x * (f x)^2) := by
    have h1 : (∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, x * (f x)^2) = ∫ (x : ℝ) in Set.Ioc (0 : ℝ) 1, x * (f x)^2 := by
      apply MeasureTheory.integral_Icc_eq_integral_Ioc' (μ := MeasureTheory.volume) (x := (0 : ℝ)) (y := (1 : ℝ))
      exact hvol0
    rw [h1]
    simp [intervalIntegral.integral_of_le]
  have h_den_eq' : (∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, (f x)^2) = (∫ (x : ℝ) in (0)..1, (f x)^2) := by
    have h1 : (∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, (f x)^2) = ∫ (x : ℝ) in Set.Ioc (0 : ℝ) 1, (f x)^2 := by
      apply MeasureTheory.integral_Icc_eq_integral_Ioc' (μ := MeasureTheory.volume) (x := (0 : ℝ)) (y := (1 : ℝ))
      exact hvol0
    rw [h1]
    simp [intervalIntegral.integral_of_le]
  have h_num : (∫ p in S, (p : ℝ × ℝ × ℝ).1) = Real.pi * ∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, x * (f x)^2 :=
    round2_num_eq f hf hfm hfc
  have h_den : MeasureTheory.volume S = ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2) :=
    round2_den_eq f hf hfc hfm
  have h_pos : (0 : ℝ) < ∫ (x : ℝ) in (0)..1, (f x)^2 := round2_den_pos f hf hfm hfc
  have h_main1 : (⨍ p in R', (p : ℝ × ℝ × ℝ).1) = (MeasureTheory.volume R').toReal⁻¹ * ∫ (p : ℝ × ℝ × ℝ) in R', (p : ℝ × ℝ × ℝ).1 := by
    simp [MeasureTheory.average]
  have hR'_eq_S : R' = S := by exact_mod_cast hR'
  rw [h_main1, hR'_eq_S]
  have h_main2 : (MeasureTheory.volume S).toReal⁻¹ * ∫ (p : ℝ × ℝ × ℝ) in S, (p : ℝ × ℝ × ℝ).1
    = (∫ (p : ℝ × ℝ × ℝ) in S, (p : ℝ × ℝ × ℝ).1) / (MeasureTheory.volume S).toReal := by
    field_simp
  rw [h_main2, h_num, h_den]
  have h_den_real : ENNReal.toReal (ENNReal.ofReal (Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2)) = Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2 := by
    simp [show (0 : ℝ) ≤ Real.pi * ∫ (x : ℝ) in (0)..1, (f x)^2 from by positivity]
  rw [h_den_real]
  have h_eq1 : Real.pi * ∫ (x : ℝ) in Set.Icc (0 : ℝ) 1, x * (f x)^2 = Real.pi * ∫ (x : ℝ) in (0)..1, x * (f x)^2 := by
    rw [h_num_eq']
  rw [h_eq1]
  field_simp [h_pos.ne'] ; ring

lemma round1_h1'' (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x)
  (hfm : StrictMono f):
  f 1 > 0 := by
  have h11 : f 0 < f 1 := hfm (by norm_num)
  have h12 : 0 ≤ f 0 := hf 0 (by norm_num)
  linarith

theorem A_and_C_are_positive (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  (∫ (x : ℝ) in (0)..1, f x) > 0 ∧ (∫ (x : ℝ) in (0)..1, (f x) ^ 2) > 0 := by
  have h1 : f 1 > 0 := round1_h1'' f hf hfm
  have h_main1 : (∫ (x : ℝ) in (0)..1, f x) > 0 := by
    apply intervalIntegral.integral_pos (by norm_num)
    · exact hfc.continuousOn
    · intro x hx
      have h2 : x ∈ Icc (0 : ℝ) 1 := by
        exact Ioc_subset_Icc_self hx
      exact hf x h2
    · refine ⟨(1 : ℝ), ⟨by norm_num, by norm_num⟩, h1⟩
  have h_main2 : (∫ (x : ℝ) in (0)..1, (f x) ^ 2) > 0 := by
    have h3 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (f x) ^ 2 := by
      intro x hx
      have h4 : 0 ≤ f x := hf x hx
      positivity
    have h4 : Continuous (fun x : ℝ ↦ (f x) ^ 2) := by
      exact hfc.pow 2
    apply intervalIntegral.integral_pos (by norm_num)
    · exact h4.continuousOn
    · intro x hx
      have h5 : x ∈ Icc (0 : ℝ) 1 := by
        exact Ioc_subset_Icc_self hx
      exact h3 x h5
    · have h6 : (f 1) ^ 2 > 0 := by positivity
      refine ⟨(1 : ℝ), ⟨by norm_num, by norm_num⟩, h6⟩
  exact ⟨h_main1, h_main2⟩

lemma round1_h_forward (A B C D : ℝ)
  (hA : A > 0)
  (hC : C > 0):
  B / A < D / C → A * D - B * C > 0 := by
  intro h
  have h1 : A * C > 0 := mul_pos hA hC
  have h2 : B / A < D / C := h
  have h3 : A * C * (B / A) < A * C * (D / C) := by
    exact mul_lt_mul_of_pos_left h2 h1
  have h4 : A * C * (B / A) = C * B := by
    field_simp [hA.ne'] ; ring
  have h5 : A * C * (D / C) = A * D := by
    field_simp [hC.ne'] ; ring
  rw [h4, h5] at h3
  linarith

lemma round1_h_backward (A B C D : ℝ)
  (hA : A > 0)
  (hC : C > 0):
  A * D - B * C > 0 → B / A < D / C := by
  intro h
  have h1 : A * C > 0 := mul_pos hA hC
  have h2 : A * D > B * C := by linarith
  have h3 : (A * D) / (A * C) > (B * C) / (A * C) := by
    apply div_lt_div_of_pos_right h2 h1
  have h4 : (A * D) / (A * C) = D / C := by
    field_simp [hA.ne', hC.ne'] ; ring
  have h5 : (B * C) / (A * C) = B / A := by
    field_simp [hA.ne', hC.ne'] ; ring
  rw [h4, h5] at h3
  linarith

theorem fraction_inequality_to_algebraic (A B C D : ℝ)
  (hA : A > 0)
  (hC : C > 0):
  B / A < D / C ↔ A * D - B * C > 0 := by
  constructor
  · exact round1_h_forward A B C D hA hC
  · exact round1_h_backward A B C D hA hC

theorem putnam_2025_b2 (f : ℝ → ℝ)
  (hf : ∀ x ∈ Icc 0 1, 0 ≤ f x)
  (hfm : StrictMono f)
  (hfc : Continuous f):
  let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 }
  let x₁ : ℝ := ⨍ x in R, x.1
  let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ }
  let x₂ : ℝ := ⨍ x' in R', x'.1
  x₁ < x₂ := by
    set A : ℝ := (∫ (x : ℝ) in (0)..1, f x) with hA_def
    set B : ℝ := (∫ (x : ℝ) in (0)..1, x * f x) with hB_def
    set C : ℝ := (∫ (x : ℝ) in (0)..1, (f x) ^ 2) with hC_def
    set D : ℝ := (∫ (x : ℝ) in (0)..1, x * (f x) ^ 2) with hD_def
    have h_pos : A > 0 ∧ C > 0 := by
      exact A_and_C_are_positive f hf hfm hfc
    have hA_pos : A > 0 := h_pos.1
    have hC_pos : C > 0 := h_pos.2
    have h1 : (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
              let x₁ : ℝ := ⨍ x in R, x.1;
              x₁) = B / A := by
      exact x1_is_B_div_A f hf hfm hfc
    have h2 : (let R : Set (ℝ × ℝ) := { x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ f x.1 };
              let R' : Set (ℝ × ℝ × ℝ) := { x' | ∃ x ∈ R, ∃ θ : ℝ, x'.1 = x.1 ∧ x'.2.1 = x.2 * cos θ ∧ x'.2.2 = x.2 * sin θ };
              let x₂ : ℝ := ⨍ x' in R', x'.1;
              x₂) = D / C := by
      exact x2_is_D_div_C f hf hfm hfc
    have h3 : A * D - B * C > 0 := by
      have h31 := A_mul_D_sub_B_mul_C_is_positive f hf hfm hfc
      simpa [hA_def, hB_def, hC_def, hD_def] using h31
    have h4 : B / A < D / C ↔ A * D - B * C > 0 := by
      exact fraction_inequality_to_algebraic A B C D hA_pos hC_pos
    have h5 : B / A < D / C := h4.mpr h3
    dsimp only at *
    rw [h1, h2]
    exact h5

end Putnam2025B2
