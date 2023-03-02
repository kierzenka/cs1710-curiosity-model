#lang forge/bsl

sig Ring {
  underMe: pfunc State -> Ring, //link to ring directly below
  radius: one Int               //radius of this ring
}

sig Pole {
  top: pfunc State -> Ring      //link to pole's top ring
}

sig State {
  next: lone State,             //next state in trace
  ringMap: pfunc Ring -> Pole   //mapping of ring to pole
}

// Checks if all rings are on the same pole in given state
pred allRingsTogether[s:State] {
  all a,b : Ring | {
    s.ringMap[a] = s.ringMap[b]
  }

}

// Checks that all states obey the invariants of the game
pred validStates {
  all s: State, r: Ring | {
    // if a ring has an underMe, the radii are valid
    some r.underMe[s] implies (r.underMe[s]).radius > r.radius

    //all rings are on some pole
    some s.ringMap[r]
  }

  all s: State, p: Pole | {
    //a pole's top must be a ring on that pole
    some p.top[s] implies {s.ringMap[(p.top[s])] = p}
  }

  all s: State, p: Pole | {
    // if a pole has a ring, it must have a top
    (some r:Ring | s.ringMap[r] = p) implies {some p.top[s]}
  }

  all s: State, p: Pole | {
    // if a pole has a top, it must be the smallest ring on that pole
    some p.top[s] implies {
      all r: Ring | {
          (p.top[s] != r) implies {
            (p.top[s]).radius < r.radius or s.ringMap[r] != s.ringMap[p.top[s]]
          }
        }
    }
  }

  all s: State | {
    all r: Ring | {
      // if a ring has no underMe, then it must be the largest ring on its pole
      (no r.underMe[s]) implies {
        all r2: Ring | {
          (r2 != r) implies {
            r2.radius < r.radius or s.ringMap[r] != s.ringMap[r2]
          }
          
        }
      }
    }
  }

  all s: State | {
    all disj a,b : Ring | {
      // no rings can have the same ring under them
      some a.underMe[s] implies {a.underMe[s] != b.underMe[s]}
    }
  }
}

//checks that all radii are unique and makes them consecutive starting w/ 1
pred validRadii {
  one r: Ring | {
    r.radius = 1
  }

  all a: Ring | {
    (a.radius != 1) implies {
      one b: Ring | {
        a.radius = add[b.radius, 1]
      }
    }
  }
}

// checks that 2 states are separated by a valid move
pred canTransition[s1:State, s2:State] {
  one r: Ring | {
    // s1.ringMap[r] is the "leaving pole"
    // s2.ringMap[r] is the "landing pole"
    s1.ringMap[r] != s2.ringMap[r]

    // r was the top of leaving and is new top of landing
    (s1.ringMap[r]).top[s1] = r
    (s2.ringMap[r]).top[s2] = r

    // r is now on top of the old landing top
    r.underMe[s2] = (s2.ringMap[r]).top[s1]

    // second to top of leaving pole is new top
    ((s1.ringMap[r]).top[s1]).underMe[s1] = (s1.ringMap[r]).top[s2]

    // no other ring moves
    all a: Ring | (a != r) implies {
      s1.ringMap[a] = s2.ringMap[a]
      a.underMe[s1] = a.underMe[s2]
    }

    // no other pole changes top
    all p: Pole | {
      (p != s1.ringMap[r] and p != s2.ringMap[r]) implies {
        p.top[s1] = p.top[s2]
      }
    }
  }
}

// Checks for a valid trace
pred transitionStates {
	some init, final: State {
		-- constraints on the initial state
		allRingsTogether[init]

		-- constraints on the final state
		allRingsTogether[final]
		no final.next

    -- different end pole
    init != final
    some r: Ring | {
      init.ringMap[r] != final.ringMap[r]
    }

		all s: State | {
			-- all states are reachable from the initial state
			s != init implies reachable[s, init, next]

			s.next != init

			-- all of the transitions between initial to final state are valid
			s != final implies canTransition[s, s.next]
		}
	}
}

// run statement finds optimal solution for 3 ring/pole
run {
  validStates
  validRadii
  transitionStates
} for exactly 3 Pole, exactly 3 Ring,8 State for {next is linear}