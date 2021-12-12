import tactic.linarith

--Define a game
--Take in a player, other player's action, your action and return a utility
def pris_dil ℕ → ℕ → ℕ → ℝ:
| 1   1   1   3
| 1   1   2   5
| 1   2   1   0
| 1   2   2   1
| 2   1   1   3
| 2   1   2   5
| 2   2   1   0
| 2   2   2   1




--Define the best response function (do I have to show this exists?)
def best_response (f: ℕ → ℕ) (convex f) :


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


