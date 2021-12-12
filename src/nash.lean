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
| Player.A   Action.c   Action.d   := 0
| Player.A   Action.d   Action.c   := 5
| Player.A   Action.d   Action.d   := 1
| Player.B   Action.c   Action.c   := 3
| Player.B   Action.c   Action.d   := 5
| Player.B   Action.d   Action.c   := 0
| Player.B   Action.d   Action.d   := 1


-- Test it
#eval pris_dil Player.A Action.c Action.c


-- Show that it is bounded
lemma pris_dil_bounded : ∀a : Player, ∀ b c : Action, ∃ u, pris_dil a b c < u :=
begin
  intros a b c,
  apply exists.intro 200,
  induction' a,
  induction' b,
  induction' c,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
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
  linarith,
  induction' c,
  rw pris_dil,
  linarith,
  rw pris_dil,
  linarith,
end

-- Show that for a given player and opponent action, there's a best response
lemma best_response_exists  : ∀ a: Player, ∀ b c : Action, ∃ o : Action, 
  pris_dil a b o ≥ pris_dil a b c  :=
begin
  intros a b c,

end



--Fixed point theorem (can be sorryed)
lemma kakutani_fixed_point (a : ℕ) : 2 > 0:=
begin
  sorry,
end


--Proof that NE exists
lemma NE_exists (l : ℕ) (B : ℕ → ℕ): ∃l, B(l) = l :=
begin
  sorry
end


