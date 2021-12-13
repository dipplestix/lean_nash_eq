import tactic
import lovelib

--Define a game
/-! A game is defines as <N, Aᵢ, ≿ᵢ> (Osborne, 1994) where:
N is the set of players 
Aᵢ is the set of action for each player i∈N
≿ᵢ is the preference relation for each player i∈N 

For this project we'll consider the prisoner's dilemma where the bigraph of utilities looks like

    c         d
  c (3, 3)    (0, 5)
  d (5, 0)    (1, 1)

N will be {A, B}
Aᵢ will be {c, d} ∀i ∈ N
We will define a utility function u: A₋ᵢ× Aᵢ → ℕ (should be reals, but this is all that's needed), 
and our preference relation will be higher utilities are better


-/

-- Define the set of players
inductive Player 
  | A    : Player
  | B    : Player


-- Define the set of actions
inductive Action 
  | c    : Action
  | d    : Action


-- Define the utility function as a function of player (you), opponent's action, and your action
def pris_dil : Player → Action → Action → ℕ 
| Player.A   Action.c   Action.c   := 3
| Player.A   Action.c   Action.d   := 5
| Player.A   Action.d   Action.c   := 0
| Player.A   Action.d   Action.d   := 1
| Player.B   Action.c   Action.c   := 3
| Player.B   Action.c   Action.d   := 5
| Player.B   Action.d   Action.c   := 0
| Player.B   Action.d   Action.d   := 1


-- Test it
#eval pris_dil Player.A Action.c Action.c
#eval pris_dil Player.A Action.c Action.d


-- Show that it is bounded
lemma pris_dil_bounded : ∀a : Player, ∀ b c : Action, ∃ u, pris_dil a b c ≤ u :=
begin
  intros a b c,
  apply exists.intro 5,
  induction' a,
  induction' b,
  induction' c,
  rw pris_dil,
  linarith,
  rw pris_dil,
  induction' c,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
  induction' b,
  induction' c,
  rw pris_dil,
  linarith,
  rw pris_dil,
  induction' c,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
end

-- Show that for a given player and opponent action, there's a best response
lemma best_response_exists  (f : Player → Action → Action → ℕ)  (a : Player)(b : Action): 
∃ o : Action, ∀ c : Action, 
  pris_dil a b o ≥ pris_dil a b c  :=
begin
  apply exists.intro Action.d,
  intro action,
  induction a,
  induction b,
  induction action,
  rw pris_dil,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
  induction action,
  rw pris_dil,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
  induction b,
  induction action,
  rw pris_dil,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
  induction action,
  rw pris_dil,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
end


-- Find the function that returns a best action
noncomputable def best_action (f : Player → Action → Action → ℕ)(a : Player)(b : Action) :=
classical.some (best_response_exists f a b)

-- Sanity check the type
#check best_action

/-!
Fixed point theorem.
1) If the range of a set-valued function is compact, convex (it's not convex, but this is a 
special case. Mixed stratgeis would be convex), and nonempty
2) A function, f, is nonempty (this is true because we can use axiom of choice)
3) The funciton is upper hemicontinuous (this is true because utility function is continuous and compact)
4) The function is convex (this is true since if two strategies are equally good, the convec combination
is also equally good)
Then it has a fixed point
-/
lemma kakutani_fixed_point (f : (Player → Action → Action → ℕ) → Player → Action → Action) 
(u : Player → Action → Action → ℕ ) (a b : Player): 
-- f bound (pris_dil_bounded) → f (x) is nonempty (best_response_exists)
-- → range f convex (not true for this case, but will be for the mixed strategy case)
  ∃ l m : Action, f u a m = l  ∧ f u b l = m :=
begin
  sorry,
end


--Proof that NE exists
lemma NE_exists (a b : Player) : 
∃ l m : Action, best_action pris_dil Player.A m = l ∧ best_action pris_dil Player.B l = m :=
begin
  apply kakutani_fixed_point,
end

/-!
To-dos:
1) List the conditions for K fixed points and use the pris_dil_bounded and best_response_exists lemmas
inside the NE lemma
2) Start working on the same things, but for mixed strategies
  - Create a simplex class
  - Switch from Action to Strategy (action is just strategy where ps are 1 or 0)
  - Do the same for a game that requires mixed strategy
  - Probbaly won't finish this part, but think I can make some good progress on it
-/
