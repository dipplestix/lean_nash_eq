
/-!

For the mixed strategy case, I decided to just reimplement the code in this paper (https://arxiv.org/pdf/1709.02096.pdf) from coq to lean

My first attempt tried to create a simplex class and combine the simplex with fixed strategies, but that got nowhere.



Tried doing the general case and ran into too many issues, so commented it out since some of it worked and kept the more specific two-player case
-/

-- -- These are the basic types
-- variable Agent : Type
-- variable Strategy : Agent → Type
-- variable Outcome : Type

-- -- Still not 100% sure on which of these is correct
-- variable strategies : Π a : Agent, Strategy a
-- variable strategies2 : sigma Strategy


-- -- A game is defined as a preference relationship and the result

-- -- This will return true if the agent prefers the second outcome, false otherwise
-- variable prefs : Agent → Outcome → Outcome → bool
-- variable game_result : (Π a : Agent, Strategy a) → Outcome





-- -- a strategy is a nash equilibrium, if for each agent, no agent will prefer the result from
-- -- a different strategy to the one they get
-- def is_ne (s : (Π a : Agent, Strategy a)) : Prop :=
-- ∀ a : Agent, ∀ s' : (Π a : Agent, Strategy a), (∀ b : Agent, a ≠ b → s b = s' b) → 
-- ¬ prefs a (game_result s) (game_result s') 

-- #check is_ne

-- -- This should take a game (defined by game_result and prefs) and return a list of 
-- -- all nash equilibriums. (does not currently work)
-- def ex_ne := {s : (Π a : Agent, Strategy a) | is_ne s}



-- Player and outcome types along with a strategy type for each player. The strategy type can later be 
-- put in a Π type paired with the player we're playing for. 
inductive player 
| A    : player
| B    : player

inductive outc
| wA    : outc
| wB    : outc

-- There's infinite many strategies (all points in the ℝᵈ simplex), so this has to stay general (and causes all the issues later on)
variable strategy : player → Type

-- Maps a set of strategies for each player to an outcome
variable result : (Π a : player, strategy a) → outc


-- Player A wants to win (same for player B)
def winlose_prefs : player → outc → outc → bool
| player.A   outc.wB   outc.wA   := tt
| player.B   outc.wA   outc.wB   := tt
| _           _         _        := ff


#eval winlose_prefs player.A outc.wB outc.wA
#eval winlose_prefs player.A outc.wA outc.wB

-- Only two outcomes to simplify
def pref_outc : player → outc
| player.A    := outc.wA
| player.B    := outc.wB

#eval pref_outc player.A


-- Returns whether a strategy is a winning strategy for a player
def win_strat (a : player)(sa : strategy a) : Prop :=
∀ strat : (Π b : player, strategy b), strat a = sa → result strat = pref_outc a

-- If a game has a winning strategy for a player, then that strategy is determined.
-- I don't know why this doesn't type check properly, coq to lean is not as easy as I thought it would be
def determined_strat (a : player) := {sa : strategy a | win_strat a sa} 

-- Returns whether a set of strategies is an ne. In english
-- We look at all sets of strategies and take the ones where ever player but player a is the same
-- If player a is playing the best action and this is true for ∀ a : player, then it's a ne
def is_ne (s : (Π a : player, strategy a)) : Prop :=
∀ a : player, ∀ s' : (Π a : player, strategy a), (∀ b : player, a ≠ b → s b = s' b) → 
¬ winlose_prefs a (result s) (result s') 

-- This is the set of all nash equilibria. This also doesn't type check
def set_ne := {s : (Π a : player, strategy a) | is_ne s}


-- Definition determined Strat (v : game_form_2 winlose_outc Strat) : Type :=
-- {a : player & {sa : Strat a | win_strat v a sa}}.

/-! There's some more work that needs to be done, but I couldn't get it done in the time period. The theorem
everything is working towards is that there exists some strategy that is a ne. I think the type of s is 
somehow wrong, but I've tried every combination of Pi/Sigma types and can't get it to properly type check.
Room for future work. 
The proof of the sketch is quite simple. You find a set of stratgeies for each player R₁ ⊆ S₁ and R₂⊆S₂
and show that inside R₁×R₂ is at least one NE. 
-/
lemma ne_exists : ∃ s : (Π a : player, strategy a), is_ne s :=
sorry