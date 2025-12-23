import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleRing.Principal

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option tactic.hygienic false
set_option linter.unusedVariables false
open EuclideanGeometry Affine Simplex

namespace Putnam2025B1

theorem key_lemma1 (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t)):
  ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
  ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2),
    X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧
    dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧
    c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P) := by
  intro P ρ hρ h
  rcases h with ⟨X, Y, Z, hXY, hYZ, hXZ, h_distX, h_distY, h_distZ, h_cX, h_cY, h_cZ⟩
  have h1 : c X ≠ c P := h_cX
  have h2 : c Y ≠ c P := h_cY
  have h3 : c Z ≠ c P := h_cZ
  have h4 : c X = c Y := by
    have h11 : c X ≠ c P := h1
    have h12 : c Y ≠ c P := h2
    cases hCP : c P <;> simp_all
  have h5 : c X = c Z := by
    have h11 : c X ≠ c P := h1
    have h12 : c Z ≠ c P := h3
    cases hCP : c P <;> simp_all
  have h_indep : AffineIndependent ℝ ![X, Y, Z] := by
    have hS : ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) ⊆ {Q | dist Q P = ρ} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl)
      · exact h_distX
      · exact h_distY
      · exact h_distZ
    have h_main : ∃ (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ), ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) ⊆ {x | dist x center = r} := ⟨P, ρ, hS⟩
    exact Cospherical.affineIndependent_of_ne h_main hXY hXZ hYZ
  let t : Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨![X, Y, Z], h_indep⟩
  have h₁ : ∀ (i : Fin 3), dist (t.points i) P = ρ := by
    intro i
    fin_cases i
    · simpa [t] using h_distX
    · simpa [t] using h_distY
    · simpa [t] using h_distZ
  have h_dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
    have h₁ : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Fintype.card (Fin 2) := by
      exact finrank_euclideanSpace_fin
    rw [h₁]
    simp
  have h_card : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + 1 := by
    rw [h_dim] ; norm_num
  have haffine_span_eq_top : affineSpan ℝ (Set.range t.points) = ⊤ := by
    have h : AffineIndependent ℝ t.points := h_indep
    rw [h.affineSpan_eq_top_iff_card_eq_finrank_add_one] ; simp [h_card]
  have haffine : P ∈ affineSpan ℝ (Set.range t.points) := by
    rw [haffine_span_eq_top] ; trivial
  have h_main_eq : P = t.circumcenter := eq_circumcenter_of_dist_eq (s := t) (p := P) haffine (r := ρ) h₁
  have h6 : c (t.points 0) = c (t.circumcenter) := hc t h4 h5
  have h7 : c X = c (t.points 0) := by
    have h71 : t.points 0 = X := by
      simp [t]
    rw [h71]
  have h8 : c X = c (t.circumcenter) := by
    exact Eq.trans h7 h6
  have h9 : c X = c P := by
    have h10 : c (t.circumcenter) = c P := by
      rw [h_main_eq]
    rw [h8, h10]
  exact h1 h9

lemma round1_h_main (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (r b : EuclideanSpace ℝ (Fin 2))
  (d : ℝ)
  (hd_pos : d > 0)
  (S : Finset (EuclideanSpace ℝ (Fin 2))):
  ∃ (y : ℝ), 1.5 * d < y ∧ y < 3 * d ∧ (∀ p ∈ S, dist p b ≠ y) := by
  let D : Finset ℝ := S.image (fun p => dist p b)
  have h1 : 1.5 * d < 3 * d := by linarith
  have h_main_contra : ¬ (∀ (y : ℝ), (1.5 * d < y ∧ y < 3 * d) → y ∈ (D : Set ℝ)) := by
    intro h
    have h2 : Set.Ioo (1.5 * d) (3 * d) ⊆ (D : Set ℝ) := by
      intro x hx
      exact h x ⟨hx.1, hx.2⟩
    have h4 : Set.Infinite (Set.Ioo (1.5 * d) (3 * d)) := by
      exact Set.Ioo_infinite h1
    have h5 : Set.Finite (D : Set ℝ) := Finset.finite_toSet D
    have h7 : Set.Finite (Set.Ioo (1.5 * d) (3 * d)) := h5.subset h2
    exact h4 h7
  have h_exists : ∃ (y : ℝ), (1.5 * d < y ∧ y < 3 * d) ∧ y ∉ (D : Set ℝ) := by
    have h' : ∃ (y : ℝ), (1.5 * d < y ∧ y < 3 * d) ∧ y ∉ (D : Set ℝ) := by
      push_neg at h_main_contra
      exact h_main_contra
    exact h'
  rcases h_exists with ⟨y, ⟨hy1, hy2⟩, hy3⟩
  refine' ⟨y, hy1, hy2, _⟩
  simpa [D] using hy3

theorem key_lemma2 (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (r b : EuclideanSpace ℝ (Fin 2))
  (d : ℝ)
  (hd : d = dist r b)
  (hd_pos : d > 0)
  (S : Finset (EuclideanSpace ℝ (Fin 2))):
  ∃ y : ℝ, 1.5 * d < y ∧ y < 3 * d ∧ (∀ p ∈ S, dist p b ≠ y) := by
  have h_main : ∃ (y : ℝ), 1.5 * d < y ∧ y < 3 * d ∧ (∀ p ∈ S, dist p b ≠ y) :=
    round1_h_main c r b d hd_pos S
  exact h_main

lemma round1_h1 (d y z : ℝ)
  (hd_pos : d > 0)
  (hy1 : 1.5 * d < y)
  (hy2 : y < 3 * d)
  (h_z : z = 2 * d):
  0 < y^2 - ((y^2 - z^2 + d^2) / (2 * d)) ^ 2 := by
  have h11 : 0 < d := hd_pos
  have h12 : d ^ 2 < y ^ 2 := by nlinarith
  have h13 : y ^ 2 < 9 * d ^ 2 := by nlinarith
  have h14 : (y ^ 2 - d ^ 2) * (y ^ 2 - 9 * d ^ 2) < 0 := by nlinarith
  have h_goal : 0 < y^2 - ((y^2 - z^2 + d^2) / (2 * d)) ^ 2 := by
    rw [h_z]
    field_simp [h11.ne']
    nlinarith
  exact h_goal

lemma round1_h2 (d y z : ℝ)
  (hd_pos : d > 0)
  (hy1 : 1.5 * d < y)
  (hy2 : y < 3 * d)
  (h_z : z = 2.5 * d):
  0 < y^2 - ((y^2 - z^2 + d^2) / (2 * d)) ^ 2 := by
  have h11 : 0 < d := hd_pos
  have h12 : 2.25 * d ^ 2 < y ^ 2 := by nlinarith
  have h13 : y ^ 2 < 9 * d ^ 2 := by nlinarith
  have h14 : y ^ 2 < 12.25 * d ^ 2 := by nlinarith
  have h15 : (y ^ 2) ^ 2 - 14.5 * d ^ 2 * (y ^ 2) + 27.5625 * d ^ 4 < 0 := by nlinarith
  have h16 : 0 < d ^ 2 := by positivity
  rw [h_z]
  field_simp [h11.ne']
  nlinarith

lemma round1_orthogonal_smul (v u : EuclideanSpace ℝ (Fin 2))
  (a b : ℝ)
  (horth : inner ℝ v u = 0):
  ‖a • v + b • u‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 + b ^ 2 * ‖u‖ ^ 2 := by
  have h_main : inner ℝ (a • v + b • u) (a • v + b • u)
    = a ^ 2 * inner ℝ v v + 2 * a * b * inner ℝ v u + b ^ 2 * inner ℝ u u := by
    have hsym : inner ℝ u v = inner ℝ v u := by
      exact real_inner_comm v u
    calc
      inner ℝ (a • v + b • u) (a • v + b • u)
        = inner ℝ (a • v) (a • v) + inner ℝ (a • v) (b • u) + inner ℝ (b • u) (a • v) + inner ℝ (b • u) (b • u) := by
          rw [inner_add_add_self]
      _ = a ^ 2 * inner ℝ v v + (a * b * inner ℝ v u) + (b * a * inner ℝ u v) + b ^ 2 * inner ℝ u u := by
          simp [inner_smul_left, inner_smul_right] ; ring
      _ = a ^ 2 * inner ℝ v v + 2 * a * b * inner ℝ v u + b ^ 2 * inner ℝ u u := by
          rw [hsym] ; ring
  have h1 : inner ℝ (a • v + b • u) (a • v + b • u) = ‖a • v + b • u‖ ^ 2 := by exact real_inner_self_eq_norm_sq (a • v + b • u)
  rw [←h1, h_main]
  have h2 : inner ℝ v v = ‖v‖ ^ 2 := by exact real_inner_self_eq_norm_sq v
  have h3 : inner ℝ u u = ‖u‖ ^ 2 := by exact real_inner_self_eq_norm_sq u
  rw [h2, h3, horth] ; ring

lemma round1_main_lemma (d y z : ℝ)
  (b r : EuclideanSpace ℝ (Fin 2))
  (hd_pos : d > 0)
  (hy1 : 1.5 * d < y)
  (hy2 : y < 3 * d)
  (h_z : z = 2 * d ∨ z = 2.5 * d)
  (hvd : dist r b = d):
  ∃ (X X' : EuclideanSpace ℝ (Fin 2)),
    (dist X b = y ∧ dist X r = z) ∧
    (dist X' b = y ∧ dist X' r = z) ∧ (X ≠ X') := by
  let v : EuclideanSpace ℝ (Fin 2) := r - b
  have hv : ‖v‖ = d := by
    simpa [v, dist_eq_norm] using hvd
  have hvd_pos : 0 < d := hd_pos
  set x : ℝ := (y^2 - z^2 + d^2) / (2 * d) with hx_def
  have h1 : 0 < y^2 - x^2 := by
    rcases h_z with (h_z | h_z)
    · exact round1_h1 d y z hvd_pos hy1 hy2 h_z
    · exact round1_h2 d y z hvd_pos hy1 hy2 h_z
  let s : ℝ := Real.sqrt (y^2 - x^2)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h1
  have hs2 : s ^ 2 = y^2 - x^2 := Real.sq_sqrt (by linarith)
  let u : EuclideanSpace ℝ (Fin 2) :=
    fun i : Fin 2 =>
      match i with
      | 0 => -v 1
      | 1 => v 0
  have h_inner_uv : inner ℝ u v = 0 := by
    simp [u, inner, Fin.sum_univ_two] ; ring
  have h_inner_uv' : inner ℝ v u = 0 := by
    have hsym : inner ℝ v u = inner ℝ u v := by exact real_inner_comm u v
    rw [hsym, h_inner_uv]
  have h_norm_u_sq : ‖u‖ ^ 2 = d ^ 2 := by
    have h : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
      simp [u, norm, Fin.sum_univ_two] ; ring_nf
    rw [h, hv]
  have h_norm_u : ‖u‖ = d := by
    have h : ‖u‖ ^ 2 = d ^ 2 := h_norm_u_sq
    have h' : 0 ≤ ‖u‖ := by positivity
    have h'' : 0 ≤ d := by linarith
    nlinarith
  set X : EuclideanSpace ℝ (Fin 2) := b + (x / d) • v + (s / d) • u with hX_def
  set X' : EuclideanSpace ℝ (Fin 2) := b + (x / d) • v - (s / d) • u with hX'_def
  have h_eq1 : (b + (x / d) • v + (s / d) • u) - b = (x / d) • v + (s / d) • u := by
    abel
  have hv_eq : v = r - b := by simp [v]
  have h_eq2 : (b + (x / d) • v + (s / d) • u) - r = ((x - d) / d) • v + (s / d) • u := by
    have h : (b + (x / d) • v + (s / d) • u) - r
      = (x / d) • v + (s / d) • u - (r - b) := by abel
    rw [h, hv_eq]
    have h2 : (x / d) • v + (s / d) • u - v = ((x / d) - 1) • v + (s / d) • u := by
      rw [sub_smul, one_smul] ; abel
    have h3 : ((x / d) - 1) = ((x - d) / d) := by
      field_simp [hvd_pos.ne']
    rw [h2, h3]
  have h_eq3 : (b + (x / d) • v - (s / d) • u) - b = (x / d) • v - (s / d) • u := by abel
  have h_eq4 : (b + (x / d) • v - (s / d) • u) - r = ((x - d) / d) • v - (s / d) • u := by
    have h : (b + (x / d) • v - (s / d) • u) - r
      = (x / d) • v - (s / d) • u - (r - b) := by abel
    rw [h, hv_eq]
    have h2 : (x / d) • v - (s / d) • u - v = ((x / d) - 1) • v - (s / d) • u := by
      rw [sub_smul, one_smul] ; abel
    have h3 : ((x / d) - 1) = ((x - d) / d) := by
      field_simp [hvd_pos.ne']
    rw [h2, h3]
  have h_dist_X_b : dist X b = y := by
    have h2 : dist X b = ‖X - b‖ := by simp [dist_eq_norm]
    rw [h2, hX_def, h_eq1]
    have h5 := round1_orthogonal_smul v u (x / d) (s / d) h_inner_uv'
    have h6 : ‖(x / d) • v + (s / d) • u‖ ^ 2 = (x / d) ^ 2 * ‖v‖ ^ 2 + (s / d) ^ 2 * ‖u‖ ^ 2 := h5
    have h_goal : ‖(x / d) • v + (s / d) • u‖ ^ 2 = y ^ 2 := by
      have h7 : (x / d) ^ 2 * ‖v‖ ^ 2 + (s / d) ^ 2 * ‖u‖ ^ 2 = y ^ 2 := by
        rw [hv, h_norm_u] ; field_simp [hvd_pos.ne'] ; nlinarith [hs2]
      rw [h6, h7]
    have h7 : 0 < y := by linarith
    have h8 : ‖(x / d) • v + (s / d) • u‖ = y := by
      nlinarith [norm_nonneg ((x / d) • v + (s / d) • u)]
    exact h8
  have h_key : ((x - d) ^ 2) + s ^ 2 = z ^ 2 := by
    have h2 : 2 * x * d = y^2 - z^2 + d^2 := by
      rw [hx_def] ; field_simp [hvd_pos.ne'] ;
    nlinarith [hs2]
  have h_dist_X_r : dist X r = z := by
    have h2 : dist X r = ‖X - r‖ := by simp [dist_eq_norm]
    rw [h2, hX_def, h_eq2]
    have h5 := round1_orthogonal_smul v u ((x - d) / d) (s / d) h_inner_uv'
    have h6 : ‖((x - d) / d) • v + (s / d) • u‖ ^ 2 = ((x - d) / d) ^ 2 * ‖v‖ ^ 2 + (s / d) ^ 2 * ‖u‖ ^ 2 := h5
    have h_goal : ‖((x - d) / d) • v + (s / d) • u‖ ^ 2 = z ^ 2 := by
      have h7 : ((x - d) / d) ^ 2 * ‖v‖ ^ 2 + (s / d) ^ 2 * ‖u‖ ^ 2 = ((x - d) ^ 2) + s ^ 2 := by
        rw [hv, h_norm_u] ; field_simp [hvd_pos.ne']
      rw [h6, h7, h_key]
    have hz_pos : 0 < z := by rcases h_z with (h_z | h_z) <;> linarith
    have h8 : ‖((x - d) / d) • v + (s / d) • u‖ = z := by
      nlinarith [norm_nonneg (((x - d) / d) • v + (s / d) • u)]
    exact h8
  have h_dist_X'_b : dist X' b = y := by
    have h2 : dist X' b = ‖X' - b‖ := by simp [dist_eq_norm]
    rw [h2, hX'_def, h_eq3]
    have h5 := round1_orthogonal_smul v u (x / d) (-(s / d)) h_inner_uv'
    have h6 : ‖(x / d) • v + (-(s / d)) • u‖ ^ 2 = (x / d) ^ 2 * ‖v‖ ^ 2 + (-(s / d)) ^ 2 * ‖u‖ ^ 2 := h5
    have h7 : ‖(x / d) • v - (s / d) • u‖ = ‖(x / d) • v + (-(s / d)) • u‖ := by
      simp [neg_smul] ; congr
    have h_goal : ‖(x / d) • v - (s / d) • u‖ ^ 2 = y ^ 2 := by
      have h8 : (x / d) ^ 2 * ‖v‖ ^ 2 + (-(s / d)) ^ 2 * ‖u‖ ^ 2 = y ^ 2 := by
        rw [hv, h_norm_u] ; field_simp [hvd_pos.ne'] ; nlinarith [hs2]
      rw [h7, h6, h8]
    have h9 : ‖(x / d) • v - (s / d) • u‖ = y := by
      nlinarith [norm_nonneg ((x / d) • v - (s / d) • u)]
    exact h9
  have h_dist_X'_r : dist X' r = z := by
    have h2 : dist X' r = ‖X' - r‖ := by simp [dist_eq_norm]
    rw [h2, hX'_def, h_eq4]
    have h5 := round1_orthogonal_smul v u ((x - d) / d) (-(s / d)) h_inner_uv'
    have h6 : ‖((x - d) / d) • v + (-(s / d)) • u‖ ^ 2 = ((x - d) / d) ^ 2 * ‖v‖ ^ 2 + (-(s / d)) ^ 2 * ‖u‖ ^ 2 := h5
    have h7 : ‖((x - d) / d) • v - (s / d) • u‖ = ‖((x - d) / d) • v + (-(s / d)) • u‖ := by
      simp [neg_smul] ; congr
    have h_goal : ‖((x - d) / d) • v - (s / d) • u‖ ^ 2 = z ^ 2 := by
      have h8 : ((x - d) / d) ^ 2 * ‖v‖ ^ 2 + (-(s / d)) ^ 2 * ‖u‖ ^ 2 = ((x - d) ^ 2) + s ^ 2 := by
        rw [hv, h_norm_u] ; field_simp [hvd_pos.ne']
      rw [h7, h6, h8, h_key]
    have hz_pos : 0 < z := by rcases h_z with (h_z | h_z) <;> linarith
    have h9 : ‖((x - d) / d) • v - (s / d) • u‖ = z := by
      nlinarith [norm_nonneg (((x - d) / d) • v - (s / d) • u)]
    exact h9
  have hX_ne_X' : X ≠ X' := by
    intro h
    have h10 : (x / d) • v + (s / d) • u = (x / d) • v - (s / d) • u := by
      simpa [hX_def, hX'_def, sub_eq_add_neg] using congr_arg (fun t : EuclideanSpace ℝ (Fin 2) => t - b) h
    have h11 : (s / d) • u + (s / d) • u = 0 := by
      have h12 : (s / d) • u = -((s / d) • u) := by
        simpa using congr_arg (fun z : EuclideanSpace ℝ (Fin 2) => z - (x / d) • v) h10
      simpa using add_eq_zero_iff_eq_neg.mpr h12
    have h13 : (2 : ℝ) • ((s / d) • u) = 0 := by
      simpa [two_smul] using h11
    have h14 : (s / d) • u = 0 := by
      simpa [mul_eq_zero] using h13
    have h16 : (s / d = 0) ∨ (u = 0) := by
      simpa [smul_eq_zero] using h14
    cases h16 with
    | inl h17 =>
      have h18 : s / d = 0 := h17
      have h19 : s = 0 := by
        field_simp [hvd_pos.ne'] at h18 ; simp at h18 ; exact h18
      linarith [hs_pos]
    | inr h17 =>
      have h18 : u = 0 := h17
      have h19 : ‖u‖ = 0 := by
        rw [h18] ; simp
      have h20 : ‖u‖ = d := h_norm_u
      rw [h19] at h20
      linarith [hvd_pos]
  exact ⟨X, X', ⟨h_dist_X_b, h_dist_X_r⟩, ⟨h_dist_X'_b, h_dist_X'_r⟩, hX_ne_X'⟩

theorem key_lemma3 (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t))
  (r b : EuclideanSpace ℝ (Fin 2))
  (d : ℝ)
  (hd : d = dist r b)
  (hd_pos : d > 0)
  (y : ℝ)
  (hy1 : 1.5 * d < y)
  (hy2 : y < 3 * d):
  ∃ X1 X2 X3 X4 : EuclideanSpace ℝ (Fin 2),
    X1 ≠ X2 ∧ X3 ≠ X4 ∧ X1 ≠ X3 ∧ X1 ≠ X4 ∧ X2 ≠ X3 ∧ X2 ≠ X4 ∧
    dist X1 b = y ∧ dist X1 r = 2 * d ∧
    dist X2 b = y ∧ dist X2 r = 2 * d ∧
    dist X3 b = y ∧ dist X3 r = 2.5 * d ∧
    dist X4 b = y ∧ dist X4 r = 2.5 * d := by
  have h_main1 := round1_main_lemma d y (2 * d) b r hd_pos hy1 hy2 (Or.inl rfl) (by simp [hd])
  have h_main2 := round1_main_lemma d y (2.5 * d) b r hd_pos hy1 hy2 (Or.inr rfl) (by simp [hd])
  rcases h_main1 with ⟨X1, X2, h11, h12, h13⟩
  rcases h_main2 with ⟨X3, X4, h21, h22, h23⟩
  have hX1_ne_X3 : X1 ≠ X3 := by
    intro h
    have h' : dist X1 r = dist X3 r := by rw [h]
    have h1 : dist X1 r = 2 * d := h11.2
    have h2 : dist X3 r = 2.5 * d := h21.2
    rw [h1, h2] at h'
    linarith [hd_pos]
  have hX1_ne_X4 : X1 ≠ X4 := by
    intro h
    have h' : dist X1 r = dist X4 r := by rw [h]
    have h1 : dist X1 r = 2 * d := h11.2
    have h2 : dist X4 r = 2.5 * d := h22.2
    rw [h1, h2] at h'
    linarith [hd_pos]
  have hX2_ne_X3 : X2 ≠ X3 := by
    intro h
    have h' : dist X2 r = dist X3 r := by rw [h]
    have h1 : dist X2 r = 2 * d := h12.2
    have h2 : dist X3 r = 2.5 * d := h21.2
    rw [h1, h2] at h'
    linarith [hd_pos]
  have hX2_ne_X4 : X2 ≠ X4 := by
    intro h
    have h' : dist X2 r = dist X4 r := by rw [h]
    have h1 : dist X2 r = 2 * d := h12.2
    have h2 : dist X4 r = 2.5 * d := h22.2
    rw [h1, h2] at h'
    linarith [hd_pos]
  refine' ⟨X1, X2, X3, X4, h13, h23, hX1_ne_X3, hX1_ne_X4, hX2_ne_X3, hX2_ne_X4, h11.1, h11.2, h12.1, h12.2, h21.1, h21.2, h22.1, h22.2⟩

lemma round1_main (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (h_not_constant : ¬(∃ c0 : Bool, ∀ A : EuclideanSpace ℝ (Fin 2), c A = c0)):
  ∃ (r b : EuclideanSpace ℝ (Fin 2)), c r ≠ c b := by
  have h1 : ∃ (r : EuclideanSpace ℝ (Fin 2)), c r ≠ true := by
    by_contra h
    push_neg at h
    have h2 : ∃ (c0 : Bool), ∀ (A : EuclideanSpace ℝ (Fin 2)), c A = c0 := ⟨true, h⟩
    exact h_not_constant h2
  have h2 : ∃ (b : EuclideanSpace ℝ (Fin 2)), c b ≠ false := by
    by_contra h
    push_neg at h
    have h3 : ∃ (c0 : Bool), ∀ (A : EuclideanSpace ℝ (Fin 2)), c A = c0 := ⟨false, h⟩
    exact h_not_constant h3
  rcases h1 with ⟨r, hr⟩
  rcases h2 with ⟨b, hb⟩
  have hcr : c r = false := by
    have h4 : c r = true ∨ c r = false := by exact Bool.eq_false_or_eq_true (c r)
    rcases h4 with (h4 | h4)
    · contradiction
    · exact h4
  have hcb : c b = true := by
    have h5 : c b = true ∨ c b = false := by exact Bool.eq_false_or_eq_true (c b)
    rcases h5 with (h5 | h5)
    · exact h5
    · contradiction
  refine' ⟨r, b, _⟩
  rw [hcr, hcb]
  simp

theorem key_lemma4 (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t))
  (h_not_constant : ¬(∃ c0 : Bool, ∀ A : EuclideanSpace ℝ (Fin 2), c A = c0)):
  ∃ r b : EuclideanSpace ℝ (Fin 2), c r ≠ c b ∧ dist r b > 0 := by
  have h_main : ∃ (r b : EuclideanSpace ℝ (Fin 2)), c r ≠ c b := round1_main c h_not_constant
  rcases h_main with ⟨r, b, hne⟩
  have hne' : r ≠ b := by
    intro h
    rw [h] at hne
    contradiction
  have h_dist : dist r b > 0 := by
    exact dist_pos.mpr hne'
  exact ⟨r, b, hne, h_dist⟩

theorem round1_at_most_two_points_with_property (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t))
  (P : EuclideanSpace ℝ (Fin 2))
  (ρ : ℝ)
  (hρ : ρ > 0):
  ∃ (F : Finset (EuclideanSpace ℝ (Fin 2))), F.card ≤ 2 ∧
  (∀ p : EuclideanSpace ℝ (Fin 2), dist p P = ρ ∧ c p ≠ c P → p ∈ F) := by
  have h_key1 : ∀ (P' : EuclideanSpace ℝ (Fin 2)) (ρ' : ℝ) (hρ' : ρ' > 0),
    ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X P' = ρ' ∧ dist Y P' = ρ' ∧ dist Z P' = ρ' ∧ c X ≠ c P' ∧ c Y ≠ c P' ∧ c Z ≠ c P') := by
    exact key_lemma1 c hc
  have h_main : ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧ c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P) := h_key1 P ρ hρ
  by_cases h0 : (∀ (p : EuclideanSpace ℝ (Fin 2)), ¬ (dist p P = ρ ∧ c p ≠ c P))
  ·
    refine' ⟨∅, by simp, _⟩
    intro p hp
    exfalso
    exact h0 p hp
  ·
    push_neg at h0
    rcases h0 with ⟨s₁, hs₁⟩
    let h1 : dist s₁ P = ρ ∧ c s₁ ≠ c P := hs₁
    by_cases h2 : ∀ (p : EuclideanSpace ℝ (Fin 2)), (dist p P = ρ ∧ c p ≠ c P) → p = s₁
    ·
      refine' ⟨{s₁}, by simp, _⟩
      intro p hp
      have hpi : p = s₁ := h2 p hp
      simp [hpi]
    ·
      push_neg at h2
      rcases h2 with ⟨s₂, hs₂, hne⟩
      have h_s2 : dist s₂ P = ρ ∧ c s₂ ≠ c P := hs₂
      have hne12 : s₂ ≠ s₁ := hne
      have hne21 : s₁ ≠ s₂ := by
        intro h
        apply hne12
        exact h.symm
      by_cases h4 : ∀ (p : EuclideanSpace ℝ (Fin 2)), (dist p P = ρ ∧ c p ≠ c P) → p = s₁ ∨ p = s₂
      ·
        have h_card : ({s₁, s₂} : Finset (EuclideanSpace ℝ (Fin 2))).card ≤ 2 := by
          have h : ({s₁, s₂} : Finset (EuclideanSpace ℝ (Fin 2))).card = 2 := by
            rw [Finset.card_insert_of_notMem]
            · simp
            · simp [hne21]
          linarith
        refine' ⟨{s₁, s₂}, h_card, _⟩
        intro p hp
        have hpi : p = s₁ ∨ p = s₂ := h4 p hp
        cases hpi with
        | inl h => simp [h]
        | inr h => simp [h]
      ·
        push_neg at h4
        rcases h4 with ⟨s₃, hs₃, h₃1, h₃2⟩
        have h_s3 : dist s₃ P = ρ ∧ c s₃ ≠ c P := hs₃
        have hne13 : s₁ ≠ s₃ := by
          intro h
          apply h₃1
          exact h.symm
        have hne23 : s₂ ≠ s₃ := by
          intro h
          apply h₃2
          exact h.symm
        have h_contra : ∃ (X Y Z : EuclideanSpace ℝ (Fin 2)), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧ c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P := by
          refine' ⟨s₁, s₂, s₃, by tauto, by tauto, by tauto, h1.1, h_s2.1, h_s3.1, h1.2, h_s2.2, h_s3.2⟩
        exact False.elim (h_main h_contra)

lemma round1_h1_94378b (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (at_most_two_points_with_property : ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
    ∃ (F : Finset (EuclideanSpace ℝ (Fin 2))), F.card ≤ 2 ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), dist p P = ρ ∧ c p ≠ c P → p ∈ F)):
  ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
    ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2),
        X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧
        dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧
        c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P) := by
  intro P ρ hρ
  intro h
  rcases h with ⟨X, Y, Z, hXY, hYZ, hXZ, hXdist, hYdist, hZdist, hXc, hYc, hZc⟩
  have h_main : ∃ (F : Finset (EuclideanSpace ℝ (Fin 2))), F.card ≤ 2 ∧ (∀ p : EuclideanSpace ℝ (Fin 2), dist p P = ρ ∧ c p ≠ c P → p ∈ F) := at_most_two_points_with_property P ρ hρ
  rcases h_main with ⟨F, hF_card, hF_prop⟩
  have h1 : X ∈ F := hF_prop X ⟨hXdist, hXc⟩
  have h2 : Y ∈ F := hF_prop Y ⟨hYdist, hYc⟩
  have h3 : Z ∈ F := hF_prop Z ⟨hZdist, hZc⟩
  have h4 : ({X, Y, Z} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl) <;> tauto
  have h5 : (({X, Y, Z} : Finset (EuclideanSpace ℝ (Fin 2))).card) ≤ F.card := Finset.card_le_card h4
  have h6 : ({X, Y, Z} : Finset (EuclideanSpace ℝ (Fin 2))).card = 3 := by
    simp [hXY, hYZ, hXZ]
  rw [h6] at h5
  linarith

lemma round1_h_exists_two (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (h_main1 : ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
    ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧ c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P))
  (X1 X2 X3 X4 : EuclideanSpace ℝ (Fin 2))
  (b : EuclideanSpace ℝ (Fin 2))
  (y : ℝ)
  (hy_pos : y > 0)
  (hX1b : dist X1 b = y)
  (hX2b : dist X2 b = y)
  (hX3b : dist X3 b = y)
  (hX4b : dist X4 b = y)
  (hX12 : X1 ≠ X2)
  (hX13 : X1 ≠ X3)
  (hX14 : X1 ≠ X4)
  (hX23 : X2 ≠ X3)
  (hX24 : X2 ≠ X4)
  (hX34 : X3 ≠ X4):
  (c X1 = c b) ∨ (c X2 = c b) ∨ (c X3 = c b) ∨ (c X4 = c b) := by
  by_contra h
  push_neg at h
  have h1 : c X1 ≠ c b := h.1
  have h2 : c X2 ≠ c b := h.2.1
  have h3 : c X3 ≠ c b := h.2.2.1
  have h4 : c X4 ≠ c b := h.2.2.2
  have h_contra : ∃ (X Y Z : EuclideanSpace ℝ (Fin 2)), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X b = y ∧ dist Y b = y ∧ dist Z b = y ∧ c X ≠ c b ∧ c Y ≠ c b ∧ c Z ≠ c b :=
    ⟨X1, X2, X3, hX12, hX23, hX13, hX1b, hX2b, hX3b, h1, h2, h3⟩
  exact h_main1 b y hy_pos h_contra

lemma round2_h_main_aux (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t))
  (h_main1 : ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
    ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧ c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P))
  (r b : EuclideanSpace ℝ (Fin 2))
  (d : ℝ)
  (hd : d = dist r b)
  (hd_pos : d > 0)
  (y : ℝ)
  (hy1 : 1.5 * d < y)
  (hy2 : y < 3 * d):
  ∃ (P : EuclideanSpace ℝ (Fin 2)), (dist P r = 2 * d ∨ dist P r = 2.5 * d) ∧ dist P b = y ∧ c P = c b := by
  have hy_pos : y > 0 := by linarith
  have h_main2 := key_lemma3 c hc r b d hd hd_pos y hy1 hy2
  rcases h_main2 with ⟨X1, X2, X3, X4, hX12, hX34, hX13, hX14, hX23, hX24, hX1b, hX1r, hX2b, hX2r, hX3b, hX3r, hX4b, hX4r⟩
  have h6 : (c X1 = c b) ∨ (c X2 = c b) ∨ (c X3 = c b) ∨ (c X4 = c b) := round1_h_exists_two c h_main1 X1 X2 X3 X4 b y hy_pos hX1b hX2b hX3b hX4b hX12 hX13 hX14 hX23 hX24 hX34
  rcases h6 with (h6 | h6 | h6 | h6)
  · refine ⟨X1, Or.inl hX1r, hX1b, h6⟩
  · refine ⟨X2, Or.inl hX2r, hX2b, h6⟩
  · refine ⟨X3, Or.inr hX3r, hX3b, h6⟩
  · refine ⟨X4, Or.inr hX4r, hX4b, h6⟩

lemma round3_h_S_infinite (d : ℝ)
  (hd_pos : d > 0):
  Set.Infinite { y : ℝ | 1.5 * d < y ∧ y < 3 * d } := by
  have h_main : Set.Infinite { y : ℝ | 1.5 * d < y ∧ y < 3 * d } := by
    let f : ℕ → ℝ := fun n : ℕ => 1.5 * d + d / (n + 2 : ℝ)
    have h1 : ∀ n : ℕ, f n ∈ { y : ℝ | 1.5 * d < y ∧ y < 3 * d } := by
      intro n
      have h_pos_d : 0 < d := hd_pos
      have h_pos_n : (0 : ℝ) < (n + 2 : ℝ) := by positivity
      have h7 : 0 < d / (n + 2 : ℝ) := by
        apply div_pos h_pos_d h_pos_n
      have h2 : (n + 2 : ℝ) ≥ 2 := by exact_mod_cast (by linarith)
      have h3 : 1 / ((n + 2 : ℝ)) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by positivity) h2
      have h4 : d / (n + 2 : ℝ) ≤ d / 2 := by
        have h5 : d / (n + 2 : ℝ) = d * (1 / ((n + 2 : ℝ))) := by field_simp
        have h6 : d / 2 = d * (1 / 2) := by field_simp
        rw [h5, h6]
        gcongr
      have h5 : 1.5 * d + d / (n + 2 : ℝ) < 3 * d := by
        calc
          1.5 * d + d / (n + 2 : ℝ) ≤ 1.5 * d + d / 2 := by gcongr
          _ = 2 * d := by ring
          _ < 3 * d := by
            have h8 : 2 * d < 3 * d := by
              nlinarith
            exact h8
      have h9 : 1.5 * d < 1.5 * d + d / (n + 2 : ℝ) := by
        have h10 : 0 < d / (n + 2 : ℝ) := h7
        linarith
      constructor
      · exact h9
      · exact h5
    have h_inj : Function.Injective f := by
      intro n m h
      simp only [f] at h
      have h4 : d / (n + 2 : ℝ) = d / (m + 2 : ℝ) := by linarith
      have h5 : (n + 2 : ℝ) = (m + 2 : ℝ) := by
        have hn : (n + 2 : ℝ) ≠ 0 := by positivity
        have hm : (m + 2 : ℝ) ≠ 0 := by positivity
        field_simp [hd_pos.ne', hn, hm] at h4
        linarith
      have h6 : (n : ℝ) = (m : ℝ) := by linarith
      exact_mod_cast h6
    have h3 : Set.Infinite (Set.range f) := Set.infinite_range_of_injective h_inj
    have h4 : Set.range f ⊆ { y : ℝ | 1.5 * d < y ∧ y < 3 * d } := by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      exact h1 n
    exact Set.Infinite.mono h4 h3
  exact h_main

theorem round1_c_is_constant (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t))
  (at_most_two_points_with_property : ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
    ∃ (F : Finset (EuclideanSpace ℝ (Fin 2))), F.card ≤ 2 ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), dist p P = ρ ∧ c p ≠ c P → p ∈ F)):
  ∃ c0 : Bool, ∀ A : EuclideanSpace ℝ (Fin 2), c A = c0 := by
  by_cases h : ∃ c0 : Bool, ∀ (A : EuclideanSpace ℝ (Fin 2)), c A = c0
  · exact h
  · exfalso
    have h' : ¬(∃ c0 : Bool, ∀ (A : EuclideanSpace ℝ (Fin 2)), c A = c0) := h
    have h_main1 : ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
        ¬(∃ X Y Z : EuclideanSpace ℝ (Fin 2), X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧ dist X P = ρ ∧ dist Y P = ρ ∧ dist Z P = ρ ∧ c X ≠ c P ∧ c Y ≠ c P ∧ c Z ≠ c P) :=
      round1_h1_94378b c at_most_two_points_with_property
    have h4 : ∃ (r b : EuclideanSpace ℝ (Fin 2)), c r ≠ c b ∧ dist r b > 0 := key_lemma4 c hc h'
    rcases h4 with ⟨r, b, hcrb, hdist_pos⟩
    set d := dist r b with hd
    have hd_pos : d > 0 := hdist_pos
    let S : Set ℝ := { y : ℝ | 1.5 * d < y ∧ y < 3 * d }
    have h_S_infinite : Set.Infinite S := round3_h_S_infinite d hd_pos
    have h_main_aux3 : ∀ (y : ℝ), y ∈ S → ∃ (P : EuclideanSpace ℝ (Fin 2)), (dist P r = 2 * d ∨ dist P r = 2.5 * d) ∧ dist P b = y ∧ c P = c b :=
      fun y hy => round2_h_main_aux c hc h_main1 r b d rfl hd_pos y hy.1 hy.2
    let P_choice : ℝ → EuclideanSpace ℝ (Fin 2) := fun y => if h : y ∈ S then Classical.choose (h_main_aux3 y h) else 0
    have hP_prop : ∀ (y : ℝ), y ∈ S →
        (dist (P_choice y) r = 2 * d ∨ dist (P_choice y) r = 2.5 * d) ∧ dist (P_choice y) b = y ∧ c (P_choice y) = c b := by
      intro y hy
      have h₁ : P_choice y = Classical.choose (h_main_aux3 y hy) := by
        simp [P_choice, hy]
      rw [h₁]
      exact Classical.choose_spec (h_main_aux3 y hy)
    let S1 : Set ℝ := { y ∈ S | dist (P_choice y) r = 2 * d }
    let S2 : Set ℝ := { y ∈ S | dist (P_choice y) r = 2.5 * d }
    have h_union : S = S1 ∪ S2 := by
      ext y
      simp only [S1, S2, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro hy
        have h_main_prop := hP_prop y hy
        have h_disj : dist (P_choice y) r = 2 * d ∨ dist (P_choice y) r = 2.5 * d := h_main_prop.1
        cases h_disj with
        | inl h1 =>
          left
          exact ⟨hy, h1⟩
        | inr h2 =>
          right
          exact ⟨hy, h2⟩
      · intro h
        cases h with
        | inl h => exact h.1
        | inr h => exact h.1
    have h_infinite1_or2 : Set.Infinite S1 ∨ Set.Infinite S2 := by
      by_contra h
      push_neg at h
      have h1 : ¬ Set.Infinite S1 := h.1
      have h2 : ¬ Set.Infinite S2 := h.2
      have h1' : Set.Finite S1 := by
        exact Set.not_infinite.mp h1
      have h2' : Set.Finite S2 := by
        exact Set.not_infinite.mp h2
      have h3 : Set.Finite (S1 ∪ S2) := Set.Finite.union h1' h2'
      have h4 : S = S1 ∪ S2 := h_union
      rw [h4] at h_S_infinite
      exact Set.not_infinite.mpr h3 h_S_infinite
    cases h_infinite1_or2 with
    | inl h_S1_infinite =>
      let S1' : Type _ := S1
      let f : S1' → EuclideanSpace ℝ (Fin 2) := fun y => P_choice y.val
      have h_inj1 : Function.Injective f := by
        intro y1 y2 h
        have hy1 : y1.val ∈ S := y1.property.1
        have h_eq : P_choice (y1.val) = P_choice (y2.val) := h
        have h_main_prop1 := hP_prop y1.val hy1
        have h_main_prop2 := hP_prop y2.val y2.property.1
        have h_dist1 : dist (P_choice y1.val) b = y1.val := h_main_prop1.2.1
        have h_dist2 : dist (P_choice y2.val) b = y2.val := h_main_prop2.2.1
        have h_val_eq : y1.val = y2.val := by
          rw [h_eq] at h_dist1
          linarith
        apply Subtype.ext
        exact h_val_eq
      have h_infinite_S1 : Infinite S1' := Set.infinite_coe_iff.mpr h_S1_infinite
      have h_infinite_range1 : Set.Infinite (Set.range f) := Set.infinite_range_of_injective h_inj1
      have hF1 : ∃ (F1 : Finset (EuclideanSpace ℝ (Fin 2))), F1.card ≤ 2 ∧ (∀ p : EuclideanSpace ℝ (Fin 2), dist p r = 2 * d ∧ c p ≠ c r → p ∈ F1) :=
        at_most_two_points_with_property r (2 * d) (by positivity)
      rcases hF1 with ⟨F1, hF1_card, hF1_prop⟩
      have h_subset1 : Set.range f ⊆ (F1 : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro z hz
        rcases hz with ⟨y, rfl⟩
        have hy : y.val ∈ S1 := y.property
        have hy_S : y.val ∈ S := hy.1
        have h_prop1 : dist (f y) r = 2 * d := by
          simpa [f, S1, hy] using hy.2
        have h_c : c (f y) = c b := (hP_prop y.val hy_S).2.2
        have h9 : c (f y) ≠ c r := by
          rw [h_c] ; tauto
        have h10 : dist (f y) r = 2 * d ∧ c (f y) ≠ c r := ⟨h_prop1, h9⟩
        exact hF1_prop (f y) h10
      have h_finite1 : Set.Finite (F1 : Set (EuclideanSpace ℝ (Fin 2))) := by exact Finset.finite_toSet F1
      have h_contra1 : Set.Infinite (F1 : Set (EuclideanSpace ℝ (Fin 2))) := Set.Infinite.mono h_subset1 h_infinite_range1
      exact Set.not_infinite.mpr h_finite1 h_contra1
    | inr h_S2_infinite =>
      let S2' : Type _ := S2
      let f : S2' → EuclideanSpace ℝ (Fin 2) := fun y => P_choice y.val
      have h_inj2 : Function.Injective f := by
        intro y1 y2 h
        have hy1 : y1.val ∈ S := y1.property.1
        have h_eq : P_choice (y1.val) = P_choice (y2.val) := h
        have h_main_prop1 := hP_prop y1.val hy1
        have h_main_prop2 := hP_prop y2.val y2.property.1
        have h_dist1 : dist (P_choice y1.val) b = y1.val := h_main_prop1.2.1
        have h_dist2 : dist (P_choice y2.val) b = y2.val := h_main_prop2.2.1
        have h_val_eq : y1.val = y2.val := by
          rw [h_eq] at h_dist1
          linarith
        apply Subtype.ext
        exact h_val_eq
      have h_infinite_S2 : Infinite S2' := Set.infinite_coe_iff.mpr h_S2_infinite
      have h_infinite_range2 : Set.Infinite (Set.range f) := Set.infinite_range_of_injective h_inj2
      have hF2 : ∃ (F2 : Finset (EuclideanSpace ℝ (Fin 2))), F2.card ≤ 2 ∧ (∀ p : EuclideanSpace ℝ (Fin 2), dist p r = 2.5 * d ∧ c p ≠ c r → p ∈ F2) :=
        at_most_two_points_with_property r (2.5 * d) (by positivity)
      rcases hF2 with ⟨F2, hF2_card, hF2_prop⟩
      have h_subset2 : Set.range f ⊆ (F2 : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro z hz
        rcases hz with ⟨y, rfl⟩
        have hy : y.val ∈ S2 := y.property
        have hy_S : y.val ∈ S := hy.1
        have h_prop2 : dist (f y) r = 2.5 * d := by
          simpa [f, S2, hy] using hy.2
        have h_c : c (f y) = c b := (hP_prop y.val hy_S).2.2
        have h9 : c (f y) ≠ c r := by
          rw [h_c] ; tauto
        have h10 : dist (f y) r = 2.5 * d ∧ c (f y) ≠ c r := ⟨h_prop2, h9⟩
        exact hF2_prop (f y) h10
      have h_finite2 : Set.Finite (F2 : Set (EuclideanSpace ℝ (Fin 2))) := by exact Finset.finite_toSet F2
      have h_contra2 : Set.Infinite (F2 : Set (EuclideanSpace ℝ (Fin 2))) := Set.Infinite.mono h_subset2 h_infinite_range2
      exact Set.not_infinite.mpr h_finite2 h_contra2

theorem key_lemma5 (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) → c (t.points 0) = c (circumcenter t))
  (r : EuclideanSpace ℝ (Fin 2))
  (d : ℝ)
  (hd_pos : d > 0):
  ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))), S.card ≤ 2 ∧
  (∀ p : EuclideanSpace ℝ (Fin 2), (dist p r = 2 * d ∨ dist p r = 2.5 * d) ∧ c p ≠ c r → p ∈ S) := by
  have at_most_two_points_with_property : ∀ (P : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (hρ : ρ > 0),
    ∃ (F : Finset (EuclideanSpace ℝ (Fin 2))), F.card ≤ 2 ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), dist p P = ρ ∧ c p ≠ c P → p ∈ F) := by
    intro P ρ hρ
    exact round1_at_most_two_points_with_property c hc P ρ hρ
  have h_const : ∃ c0 : Bool, ∀ A : EuclideanSpace ℝ (Fin 2), c A = c0 := by
    exact round1_c_is_constant c hc at_most_two_points_with_property
  rcases h_const with ⟨c0, hc0⟩
  refine' ⟨(∅ : Finset (EuclideanSpace ℝ (Fin 2))), _ , _⟩
  ·
    simp
  ·
    intro p hp
    have h131 : c p = c0 := hc0 p
    have h132 : c r = c0 := hc0 r
    have h133 : c p = c r := by rw [h131, h132]
    have h134 : c p ≠ c r := hp.2
    tauto

theorem putnam_2025_b1 (c : EuclideanSpace ℝ (Fin 2) → Bool)
  (hc : ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), c (t.points 0) = c (t.points 1) → c (t.points 0) = c (t.points 2) →
    c (t.points 0) = c (circumcenter t)):
  ∃ c0 : Bool, ∀ A, c A = c0 := by
      by_cases h : ∃ c0 : Bool, ∀ A : EuclideanSpace ℝ (Fin 2), c A = c0
      ·
        tauto
      ·
        have h1 : ∃ r b : EuclideanSpace ℝ (Fin 2), c r ≠ c b ∧ dist r b > 0 := by
          exact key_lemma4 c hc h
        rcases h1 with ⟨r, b, hcr_neq_cb, h_d_pos'⟩
        set d : ℝ := dist r b with hd_def
        have hd_pos : d > 0 := by simpa [hd_def] using h_d_pos'
        have h5 : ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))), S.card ≤ 2 ∧
            (∀ p : EuclideanSpace ℝ (Fin 2), (dist p r = 2 * d ∨ dist p r = 2.5 * d) ∧ c p ≠ c r → p ∈ S) := by
          exact key_lemma5 c hc r d hd_pos
        rcases h5 with ⟨S, hS_card, hS_prop⟩
        have h6 : ∃ y : ℝ, 1.5 * d < y ∧ y < 3 * d ∧ (∀ p ∈ S, dist p b ≠ y) := by
          exact key_lemma2 c r b d (by linarith) hd_pos S
        rcases h6 with ⟨y, hy1, hy2, hy3⟩
        have h7 : ∃ X1 X2 X3 X4 : EuclideanSpace ℝ (Fin 2),
            X1 ≠ X2 ∧ X3 ≠ X4 ∧ X1 ≠ X3 ∧ X1 ≠ X4 ∧ X2 ≠ X3 ∧ X2 ≠ X4 ∧
            dist X1 b = y ∧ dist X1 r = 2 * d ∧
            dist X2 b = y ∧ dist X2 r = 2 * d ∧
            dist X3 b = y ∧ dist X3 r = 2.5 * d ∧
            dist X4 b = y ∧ dist X4 r = 2.5 * d := by
          exact key_lemma3 c hc r b d (by linarith) hd_pos y hy1 hy2
        rcases h7 with ⟨X1, X2, X3, X4, h10_neq12, h10_neq34, h10_neq13, h10_neq14, h10_neq23, h10_neq24, h10_X1_b, h10_X1_r, h10_X2_b, h10_X2_r, h10_X3_b, h10_X3_r, h10_X4_b, h10_X4_r⟩
        have h_c_X1 : c X1 = c r := by
          by_contra h_c_X1_hyp
          have hX1_in_S : X1 ∈ S := by
            have h101 : (dist X1 r = 2 * d ∨ dist X1 r = 2.5 * d) := by
              left
              linarith
            have h102 : c X1 ≠ c r := by tauto
            exact hS_prop X1 ⟨h101, h102⟩
          have h_contra1 : dist X1 b ≠ y := hy3 X1 hX1_in_S
          have h10_X1_b1 : dist X1 b = y := h10_X1_b
          tauto
        have h_c_X2 : c X2 = c r := by
          by_contra h_c_X2_hyp
          have hX2_in_S : X2 ∈ S := by
            have h101 : (dist X2 r = 2 * d ∨ dist X2 r = 2.5 * d) := by
              left
              linarith
            have h102 : c X2 ≠ c r := by tauto
            exact hS_prop X2 ⟨h101, h102⟩
          have h_contra2 : dist X2 b ≠ y := hy3 X2 hX2_in_S
          have h10_X2_b1 : dist X2 b = y := h10_X2_b
          tauto
        have h_c_X3 : c X3 = c r := by
          by_contra h_c_X3_hyp
          have hX3_in_S : X3 ∈ S := by
            have h101 : (dist X3 r = 2 * d ∨ dist X3 r = 2.5 * d) := by
              right
              linarith
            have h102 : c X3 ≠ c r := by tauto
            exact hS_prop X3 ⟨h101, h102⟩
          have h_contra3 : dist X3 b ≠ y := hy3 X3 hX3_in_S
          have h10_X3_b1 : dist X3 b = y := h10_X3_b
          tauto
        have h_c_X1_neq_cb : c X1 ≠ c b := by
          by_contra h111
          have h114 : c r = c b := by
            have h1141 : c r = c X1 := by
              rw [h_c_X1]
            have h1142 : c X1 = c b := h111
            rw [h1141, h1142]
          tauto
        have h_c_X2_neq_cb : c X2 ≠ c b := by
          by_contra h111
          have h114 : c r = c b := by
            have h1141 : c r = c X2 := by
              rw [h_c_X2]
            have h1142 : c X2 = c b := h111
            rw [h1141, h1142]
          tauto
        have h_c_X3_neq_cb : c X3 ≠ c b := by
          by_contra h111
          have h114 : c r = c b := by
            have h1141 : c r = c X3 := by
              rw [h_c_X3]
            have h1142 : c X3 = c b := h111
            rw [h1141, h1142]
          tauto
        have hy_pos : y > 0 := by
          have h121 : 1.5 * d < y := hy1
          have h122 : d > 0 := hd_pos
          linarith
        have h12 := key_lemma1 c hc b y hy_pos
        have h13 : ∃ X Y Z : EuclideanSpace ℝ (Fin 2),
            X ≠ Y ∧ Y ≠ Z ∧ X ≠ Z ∧
            dist X b = y ∧ dist Y b = y ∧ dist Z b = y ∧
            c X ≠ c b ∧ c Y ≠ c b ∧ c Z ≠ c b := by
          refine' ⟨X1, X2, X3, _⟩
          exact ⟨h10_neq12, h10_neq23, h10_neq13, h10_X1_b, h10_X2_b, h10_X3_b, h_c_X1_neq_cb, h_c_X2_neq_cb, h_c_X3_neq_cb⟩
        exact False.elim (h12 h13)

end Putnam2025B1
