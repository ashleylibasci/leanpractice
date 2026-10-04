import Mathlib

open scoped BigOperators

/-!
# Cauchy-Schwarz in R^n from the discriminant of a quadratic

For y != 0, consider

  f(t) = ||x - t y||^2.

It is nonnegative for every real t.  Its coefficients are

  a = ||y||^2,  b = -2 <x,y>,  c = ||x||^2,

so its discriminant is nonpositive.
-/

/- If a > 0 and a*t^2 + b*t + c is always nonnegative, then its
   discriminant is nonpositive. -/
lemma quadratic_nonneg_discriminant
    {a b c : ℝ} (ha : 0 < a)
    (hf : ∀ t : ℝ, 0 ≤ a * t ^ 2 + b * t + c) :
    b ^ 2 - 4 * a * c ≤ 0 := by
  have hane : a ≠ 0 := ne_of_gt ha
  -- Evaluate the quadratic at its vertex t = -b/(2a).
  have hvertex := hf (-b / (2 * a))
  have hscaled :
      0 ≤ 4 * a * (a * (-b / (2 * a)) ^ 2
        + b * (-b / (2 * a)) + c) :=
    mul_nonneg (by positivity) hvertex
  -- This is the completed-square identity after clearing denominators.
  have hid :
      4 * a * (a * (-b / (2 * a)) ^ 2
        + b * (-b / (2 * a)) + c) =
        4 * a * c - b ^ 2 := by
    field_simp [hane]
    ring
  rw [hid] at hscaled
  linarith

theorem cauchy_schwarz_quadratic
    (n : ℕ) (x y : Fin n → ℝ) :
    (∑ i, x i * y i) ^ 2 ≤
      (∑ i, (x i) ^ 2) * (∑ i, (y i) ^ 2) := by
  let A : ℝ := ∑ i, (x i) ^ 2
  let B : ℝ := ∑ i, x i * y i
  let C : ℝ := ∑ i, (y i) ^ 2
  change B ^ 2 ≤ A * C
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  -- This is the same y = 0 versus y != 0 split as in the paper proof.
  by_cases hyzero : y = 0
  · have hBzero : B = 0 := by
      simp [B, hyzero]
    have hCzero : C = 0 := by
      simp [C, hyzero]
    simp [hBzero, hCzero]
  · have hCne : C ≠ 0 := by
      intro hCzero
      have hycoord : ∀ i, y i = 0 := by
        intro i
        have hyi_nonneg : 0 ≤ (y i) ^ 2 := sq_nonneg (y i)
        have hyi_le : (y i) ^ 2 ≤ C := by
          dsimp [C]
          exact Finset.single_le_sum
            (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
        nlinarith
      apply hyzero
      funext i
      exact hycoord i
    have hCpos : 0 < C :=
      lt_of_le_of_ne hC0 (Ne.symm hCne)
    -- Expand f(t) = ||x - t y||^2 and prove that it is nonnegative.
    have hf : ∀ t : ℝ,
        0 ≤ C * t ^ 2 + (-2 * B) * t + A := by
      intro t
      have hsum :
          0 ≤ ∑ i : Fin n, (x i - t * y i) ^ 2 := by
        positivity
      have hexpand :
          (∑ i : Fin n, (x i - t * y i) ^ 2) =
            C * t ^ 2 + (-2 * B) * t + A := by
        dsimp [A, B, C]
        calc
          _ = ∑ i : Fin n,
                ((x i) ^ 2
                  - 2 * t * (x i * y i)
                  + t ^ 2 * (y i) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = _ := by
                simp [Finset.sum_add_distrib,
                  Finset.sum_sub_distrib,
                  Finset.mul_sum, Finset.sum_mul]
                ring_nf
      rw [← hexpand]
      exact hsum
    have hdisc :
        (-2 * B) ^ 2 - 4 * C * A ≤ 0 :=
      quadratic_nonneg_discriminant hCpos hf
    nlinarith
