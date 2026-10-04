
import Mathlib

/-!
LEAN SYNTAX GUIDE: THEOREM 3.65

This file demonstrates how to write and structure
formal proofs using Lean 4 and Mathlib.

Lean checks that every proof establishes its
declared proposition.

Common symbols:
  →    implication or function arrow
  ↔    if and only if
  ∧    logical AND
  ∃    there exists
  ∀    for every
  =    equality
  ⊥    bottom element (here, zero subspace)
  ⊤    top element (here, entire subspace)
  :=   assigns a definition or proof
  by   begins a tactic-based proof

Comments:
  --          single-line comment
  /- ... -/   block comment
  /-! ... -/  documentation-style block
-/

-- section groups related declarations together.
-- It also limits the scope of local variables.
section Theorem365

-- variable introduces parameters used in the section.
-- Type* allows Lean to infer the universe level.
-- Braces { } indicate implicit parameters.
variable {K V W : Type*}

-- Square brackets [ ] declare typeclass instances.
-- Lean automatically supplies these instances
-- when a theorem requires them.
variable [Field K]

variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]
variable [FiniteDimensional K W]


/-!
PART 1: FACT A

New Lean syntax:

theorem NAME : STATEMENT := by
  TACTICS

theorem:
  Declares a proposition and provides a proof.

:= by:
  Begins a proof written using tactics.

exact:
  Closes the current goal by providing
  a term whose type matches that goal.

.symm:
  Reverses an equality or equivalence.

omit:
  Excludes specified section variables
  from an individual declaration.
-/

-- omit prevents Lean from automatically including
-- these unused typeclass assumptions.
omit [FiniteDimensional K V] [FiniteDimensional K W] in

-- theorem defines a named result.
-- (T : ...) declares an explicit parameter.
-- The colon introduces the proposition to prove.
theorem factA (T : V →ₗ[K] W) :
    Function.Injective T ↔ T.ker = ⊥ := by

  -- exact finishes a goal when the supplied
  -- theorem or expression proves exactly that goal.
  --
  -- .symm reverses the two sides of ↔.
  exact (LinearMap.ker_eq_bot).symm


/-!
PART 2: FACT B

New Lean syntax:

(U : Submodule K W):
  Introduces a parameter named U with a type.

(h : P):
  Introduces an assumption h that proves P.

Submodule:
  A Mathlib type representing a submodule.

Module.finrank:
  A Mathlib function returning finite rank
  as a natural number.

The name h can be used later in the proof
as evidence that its proposition holds.
-/

theorem factB (U : Submodule K W)
    (h : Module.finrank K U =
         Module.finrank K W) :
    U = ⊤ := by

  -- Pass h as an argument to a Mathlib theorem.
  -- The expression produced by applying that
  -- theorem matches our goal exactly.
  exact Submodule.eq_top_of_finrank_eq h


/-!
PART 3: LEMMA C

Important Lean tactics:

constructor:
  Splits a goal into the components required
  by its constructor.
  For ↔, this creates two implication goals.
  For ∧, this creates two component goals.

intro:
  Introduces variables or assumptions
  from the current goal into the context.

rintro:
  Similar to intro, but also destructures
  introduced data using patterns.

apply:
  Uses a theorem whose conclusion matches
  the goal, creating goals for its premises.

obtain:
  Extracts values and proofs from an
  existing hypothesis or expression.

refine:
  Supplies a partial proof and leaves
  placeholders to be completed.

calc:
  Writes a chain of relations, such
  as multiple equalities.

let:
  Introduces a local definition.

exact:
  Supplies a complete proof of the goal.
-/

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem lemmaC (T : V →ₗ[K] W) :
    (∃ e : V ≃ₗ[K] W, ∀ v, e v = T v) ↔
      Function.Injective T ∧
      Function.Surjective T := by

  -- constructor splits the ↔ goal
  -- into its forward and reverse implications.
  constructor

  -- The bullet · starts a separate tactic branch.
  -- It keeps the subproofs organized.
  ·
    -- rintro introduces the hypothesis and
    -- immediately destructures its existential proof.
    --
    -- ⟨e, he⟩ extracts:
    -- e: the witness
    -- he: the property satisfied by e
    rintro ⟨e, he⟩

    -- The goal contains ∧, so constructor
    -- produces one goal for each component.
    constructor

    ·
      -- intro introduces x, y, and hxy
      -- from the current implication goal.
      intro x y hxy

      -- apply uses a theorem to work backward
      -- from the goal.
      --
      -- Here Lean replaces the current goal
      -- with the equality needed by e.injective.
      apply e.injective

      -- calc creates a chain of equalities.
      --
      -- The first line specifies the starting
      -- expression and its replacement.
      --
      -- Each underscore _ refers to the
      -- right-hand side of the preceding line.
      --
      -- := introduces the proof for each equality.
      calc
        e x = T x := he x
        _ = T y := hxy
        _ = e y := (he y).symm

    ·
      -- intro introduces an arbitrary target
      -- from the universal quantifier.
      intro w

      -- obtain destructures an existential result.
      --
      -- ⟨v, hv⟩ gives:
      -- v: a witness
      -- hv: proof of its required property
      obtain ⟨v, hv⟩ := e.surjective w

      -- refine supplies part of the proof.
      --
      -- ⟨v, ?_⟩ specifies v as our witness.
      -- ?_ is a placeholder for a remaining goal.
      refine ⟨v, ?_⟩

      -- calc completes that remaining equality.
      calc
        T v = e v := (he v).symm
        _ = w := hv

  ·
    -- rintro also supports patterns for ∧.
    --
    -- This extracts both components of
    -- the conjunction into named hypotheses.
    rintro ⟨hinj, hsurj⟩

    -- let creates a local definition.
    --
    -- The name e can be used in the remainder
    -- of this proof branch.
    --
    -- ⟨hinj, hsurj⟩ constructs a proof of AND
    -- from separate proofs of both components.
    let e : V ≃ₗ[K] W :=
      LinearEquiv.ofBijective T ⟨hinj, hsurj⟩

    -- refine provides a witness for ∃
    -- while leaving one remaining goal.
    refine ⟨e, ?_⟩

    -- intro introduces v from the ∀ goal.
    intro v

    -- exact closes the remaining goal.
    exact LinearEquiv.ofBijective_apply T v


/-!
PART 4: INJECTIVE IFF SURJECTIVE

New Lean syntax:

.mp:
  Extracts the forward implication from ↔.

.mpr:
  Extracts the reverse implication from ↔.

For a proof h : P ↔ Q:

h.mp  : P → Q
h.mpr : Q → P

When writing:

h.mp hp

Lean applies the forward implication to
hp : P and produces a proof of Q.

Parentheses group expressions so Lean
knows which result is being used.
-/

theorem theorem365_inj_surj
    (T : V →ₗ[K] W)

    -- hdim is a named hypothesis.
    (hdim : Module.finrank K V =
            Module.finrank K W) :

    Function.Injective T ↔
    Function.Surjective T := by

  -- Splits the iff into two directions.
  constructor

  ·
    -- Introduces the hypothesis of the
    -- forward implication.
    intro hinj

    -- The Mathlib theorem returns a proof of ↔.
    --
    -- .mp selects its forward implication.
    -- hinj supplies the premise.
    -- exact uses the resulting proof.
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim).mp hinj

  ·
    -- Introduces the hypothesis of the
    -- reverse implication.
    intro hsurj

    -- .mpr selects the reverse implication.
    -- hsurj supplies its premise.
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hdim).mpr hsurj


/-!
PART 5: FINAL THEOREM

Additional Lean syntax:

have:
  Introduces an intermediate statement
  together with its proof.

h : P:
  Means h is a proof of proposition P.

|>:
  Pipeline operator.
  Passes the expression on its left
  to the function on its right.

.1:
  Extracts the first component of a pair
  or a proof of a conjunction.

.2:
  Extracts the second component.

For example, if h : P ∧ Q:

h.1 proves P
h.2 proves Q

⟨hp, hq⟩:
  Constructs a proof of P ∧ Q from
  hp : P and hq : Q.
-/

theorem theorem365
    (T : V →ₗ[K] W)
    (hdim : Module.finrank K V =
            Module.finrank K W) :

    ((∃ e : V ≃ₗ[K] W, ∀ v, e v = T v) ↔
       Function.Injective T) ∧
    (Function.Injective T ↔
       Function.Surjective T) := by

  -- have declares an intermediate proof
  -- that can be referenced later.
  --
  -- The theorem name after := supplies
  -- the proof of the declared statement.
  have h :
      Function.Injective T ↔
      Function.Surjective T :=
    theorem365_inj_surj T hdim

  -- The outer goal is a conjunction.
  -- constructor separates its two components.
  constructor

  ·
    -- The first component is an iff statement.
    -- constructor separates both directions.
    constructor

    ·
      -- Introduce the assumption.
      intro hinv

      -- (lemmaC T).mp gives the forward direction
      -- of the equivalence in lemmaC.
      --
      -- Applying it to hinv produces a conjunction.
      --
      -- |>.1 extracts the first component.
      exact (lemmaC T).mp hinv |>.1

    ·
      -- Introduce the assumption.
      intro hinj

      -- apply works backward using the
      -- reverse implication of lemmaC.
      --
      -- The new goal is to provide a
      -- conjunction of two propositions.
      apply (lemmaC T).mpr

      -- ⟨ , ⟩ builds the required pair.
      --
      -- hinj proves the first component.
      -- h.mp hinj proves the second component.
      exact ⟨hinj, h.mp hinj⟩

  ·
    -- h already has exactly the required type.
    -- Therefore exact closes the final goal.
    exact h

-- end closes the section.
-- Local section variables no longer remain in scope.
end Theorem365
