#lang forge/bsl

sig Ring {
  underMe: pfunc State -> Ring,
  radius: one Int
}

sig Pole {
  top: pfunc State -> Ring
}

sig State {
  next: lone State,
  ringMap: pfunc Ring -> Pole
}

pred allRingsTogether[s:State] {
  all a,b : Ring | {
    s.ringMap[a] = s.ringMap[b]
  }
}

pred validStates {
  all s: State, r: Ring | {
    some r.underMe[s] implies (r.underMe[s]).radius > r.radius
    some s.ringMap[r]
  }

  all s: State, p: Pole | {
    s.ringMap[(p.top[s])] = p
  }
}

pred validRadii {
  all disj a, b: Ring | {
    a.radius != b.radius
  }

  all a: Ring | {
    a.radius > 0
  }
}

pred canTransition[s1:State, s2:State] {
  one r: Ring | {
    // s1.ringMap[r] is the "leaving pole"
    // s2.ringMap[r] is the "landing pole"
    s1.ringMap[r] != s2.ringMap[r]

    (s1.ringMap[r]).top[s1] = r
    (s2.ringMap[r]).top[s2] = r
    r.underMe[s2] = (s2.ringMap[r]).top[s1]

    ((s1.ringMap[r]).top[s1]).underMe[s1] = (s1.ringMap[r]).top[s2]

    all a: Ring | (a != r) implies {
      s1.ringMap[a] = s2.ringMap[a]
      a.underMe[s1] = a.underMe[s2]
    }
  }
}

pred transitionStates {
	some init, final: State {
		-- constrains on the initial state
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

run {
  validStates
  validRadii
  transitionStates
} for exactly 3 Pole, exactly 3 Ring, 6 State for {next is linear}