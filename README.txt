https://en.wikipedia.org/wiki/Tower_of_Hanoi

////////////////////////////////
Objective
////////////////////////////////

We decided to model the puzzle game "Tower of Hanoi".
In the classic game, there are 3 poles and 3 rings of distinct radius. At the 
start of the game, all 3 rings are stacked on a single pole with each ring 
directly above the next largest ring (so the radii increase as you go towards 
the bottom). The goal of the puzzle is to move the entire stack to a different 
pole. In each turn, you can move only the top ring from any pole to a different 
pole, but you can never place a ring on top of a smaller ring. 
Our goal was to model this game in forge to see if it could find an optimal 
solution for the 3 ring/pole version of the game.

////////////////////////////////
Model Design Choices:
////////////////////////////////

A difference between a physical Tower of Hanoi game and ours is the ordering
of the poles. A real game has a concrete first and last pole, where the stack
must start and end, respectively, but our model does not have this notion
builtin. Instead, it is sufficient to have all of the rings start on some
arbitrary pole, to later be moved to a distinct arbitrary pole. Since the pole
numbers are consistent across model states, this is equivalent to the original
game's setup. A beneficial aspect of our digital implementation is that we can
arbitrarily change the number of rings, poles, and allowed total number of
states. This is useful because we can verify our model's correctness by running
it with the publicly-known minimum number of states for a given number of rings
and poles. Moreover, for less-common combinations of rings and poles, we can
easily increase the number of searchable states in the hopes of finding a
solution. In the Sterling visualization, it is imperative to look at an instance
by creating a "Time Projection" on the "State" signature. Then, you will see a
network of rings and poles, along with the radius of the rings. We recommend
setting the "radius" field as an attribute of rings, simplifying the
visualization. Then, the "ringMap" field shows which pole a given ring is on,
and following the "underMe" field shows the stack of rings on a given pole.
Finally, the "top" field holds a reference to a pole's top ring. By clicking
through the time projection, you should be able to see all transitions of valid
moves and resultant states, starting with all rings on one pole, and ending with
all rings on a different pole. We attempted to write a custom visualization, and
made decent progress in being able to draw out the poles for each state, but
were unable to access pfunc values inside of the visualization. Going forward, we
would have a working visualization if we knew how to access a pole's "top" field
in a given state, and similarly a ring's "underMe" field in a given state.

////////////////////////////////
Description of Sigs/Preds:
////////////////////////////////

We decided to represent poles (Pole) and rings (Ring) as their own sigs as they 
all represent distinct objects in our game. Since our ultimate goal was to 
generate sequences of moves to solve the puzzle, we also had a State sig which 
would allow us to generate traces of valid moves.

Moves in this game consist of moving the top ring from any pole, so we decided 
to give the Pole sig a 'top' field, which (given a state) tells us which ring 
is at the top of that Pole (if any) - this was important to keep track of which 
rings were available to be moved in any given state.

Rings themselves have a fixed radius which determines what other rings it can 
stack on top of, so we put this as an int field in Ring. Also, to be able to 
ensure that a ring is never above a smaller ring, we maintain an 'underMe' 
field in the Ring sig which points to the ring directly below it. With this, at 
each state and for each ring we can easily get access to the ring directly 
below it (if any) and ensure that it is larger.

To allow for traces, each State sig had a lone 'next' field representing the 
next state after a move. Each state also had a 'ringMap' which mapped every 
ring to a pole. This was useful to ensure that every ring stayed on some pole 
in every state, as well as ensure that only one ring moved per turn.

Preds:

allRingsTogether - this predicate checked to see if all rings were on the same 
pole in a given state. We used this predicate to create both our init and final 
states (since in both init/final, the rings all share a pole).

validStates - this predicate ensures all states are valid in the trace. It 
checks the stacking-radius constraint, that all rings are always on some pole, 
that the top of each pole is well defined as well as that all rings on a single 
pole are connected in a chain via the 'underMe' field

validRadii - this predicate ensures that all rings have a unique radius which 
is important for the setup of the game. On top of this, this predicate went a 
little further (mostly for quality of life) by also ensuring that all radii 
were unique and count up consecutively from 1 (ex: given 3 rings, they will 
have the radii 1,2,3). This made it easier to visually verify that the radius 
condition was maintained and would've been helpful in a visualizer.

canTransition - this is the main predicate which, given 2 states, checks if 
there was a valid move to go between them. It checks that only one 'top' ring 
moved (no others) and that the other invariants were maintained (the 'tops' 
were reassigned properly, 'underMe's were updated, etc). This predicate is how 
we can ensure that traces consist of only legal moves.

transitionStates - this predicate constrains forge to generating only a valid 
trace. It makes sure that there is an init/final state (which have rings all 
together on different poles, using allRingsTogether) and that all states are 
connected by valid transitions using canTransition.

When we want to generate a valid trace, we make a run statement which specifies 
that we want validStates, validRadii, and transitionStates.