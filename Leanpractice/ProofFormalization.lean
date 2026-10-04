
import Mathlib

/-!
# Theorem 3.65
Let V and W be finite-dimensional vector spaces
over a field K, with equal dimensions.

We prove that a linear map T : V → W is
invertible if and only if it is injective,
if and only if it is surjective.
-/

section Theorem365

variable {K V W : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V]
variable [FiniteDimensional K W]

-- Fact A:
-- T is injective iff its kernel is {0}.

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem factA (T : V →ₗ[K] W) :
    Function.Injective T ↔ T.ker = ⊥ := by
  exact (LinearMap.ker_eq_bot).symm

-- Fact B:
-- A subspace having the same dimension
-- as the whole space equals that space.

theorem factB (U : Submodule K W)
    (h : Module.finrank K U =
         Module.finrank K W) :
    U = ⊤ := by
  exact Submodule.eq_top_of_finrank_eq h

-- Lemma C:
-- T is invertible iff it is both
-- injective and surjective.
--
-- Invertibility is represented by the
-- existence of a linear equivalence
-- agreeing with T on every vector.

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem lemmaC (T : V →ₗ[K] W) :
    (∃ e : V ≃ₗ[K] W, ∀ v, e v = T v) ↔
      Function.Injective T ∧
      Function.Surjective T := by
  constructor
  · rintro ⟨e, he⟩
    constructor
    · intro x y hxy
      apply e.injective
      calc
        e x = T x := he x
        _ = T y := hxy
        _ = e y := (he y).symm
    · intro w
      obtain ⟨v, hv⟩ := e.surjective w
      refine ⟨v, ?_⟩
      calc
        T v = e v := (he v).symm
        _ = w := hv
  · rintro ⟨hinj, hsurj⟩
    let e : V ≃ₗ[K] W :=
      LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
    refine ⟨e, ?_⟩
    intro v
    exact LinearEquiv.ofBijective_apply T v

-- Theorem 3.65:
-- Assume dim V = dim W.
-- Then injective iff surjective.

theorem theorem365_inj_surj
    (T : V →ₗ[K] W)
    (hdim : Module.finrank K V =
            Module.finrank K W) :
    Function.Injective T ↔
    Function.Surjective T := by
  constructor
  · intro hinj
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim).mp hinj
  · intro hsurj
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim).mpr hsurj

-- Final conclusion:
-- Invertible iff injective,
-- and injective iff surjective.

theorem theorem365
    (T : V →ₗ[K] W)
    (hdim : Module.finrank K V =
            Module.finrank K W) :
    ((∃ e : V ≃ₗ[K] W, ∀ v, e v = T v) ↔
       Function.Injective T) ∧
    (Function.Injective T ↔
       Function.Surjective T) := by
  have h :
      Function.Injective T ↔
      Function.Surjective T :=
    theorem365_inj_surj T hdim
  constructor
  · constructor
    · intro hinv
      exact (lemmaC T).mp hinv |>.1
    · intro hinj
      apply (lemmaC T).mpr
      exact ⟨hinj, h.mp hinj⟩
  · exact h

end Theorem365
