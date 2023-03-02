#lang forge/bsl

open "hanoi.frg"

test suite for validStates {
  example misorderedRings is not validStates for {
    State = `State0
    Ring = `Ring0 + `Ring1 + `Ring2
    Pole = `Pole0
    no next
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole0)
    radius = `Ring0 -> 1 + `Ring1 -> 3 + `Ring2 -> 2
    underMe = `Ring0 -> `State0 -> `Ring1 + `Ring1 -> `State0 -> `Ring2
  }
}

test suite for canTransition {
  example validMove is {some pre, post: State | canTransition[pre, post]} for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1
    Pole = `Pole0 + `Pole1
    next = `State0 -> `State1
    top = `Pole0 -> (`State0 -> `Ring0 + `State1 -> `Ring1) +
          `Pole1 -> `State1 -> `Ring0
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole0)
    radius = `Ring0 -> 1 + `Ring1 -> 2
    underMe = `Ring0 -> `State0 -> `Ring1
  }

  example noMove is not {some pre, post: State | canTransition[pre, post]} for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1 + `Ring2
    Pole = `Pole0 + `Pole1 + `Pole2
    next = `State0 -> `State1
    top = `Pole0 -> `State0 -> `Ring0 +
          `Pole1 -> `State1 -> `Ring0
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole2) +
              `State1 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole2)
    radius = `Ring0 -> 1 + `Ring1 -> 2 + `Ring2 -> 3
    underMe = `Ring0 -> (`State0 -> `Ring1 + `State1 -> `Ring1)
  }

  example multipleMoves is not {some pre, post: State | canTransition[pre, post]} for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1
    Pole = `Pole0 + `Pole1
    next = `State0 -> `State1
    top = `Pole0 -> `State0 -> `Ring0 +
          `Pole1 -> `State1 -> `Ring0
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole1)
    radius = `Ring0 -> 1 + `Ring1 -> 2
    underMe = `Ring0 -> (`State0 -> `Ring1 + `State1 -> `Ring1)
  }

  example doubleTop is not {some pre, post: State | canTransition[pre, post]} for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1
    Pole = `Pole0 + `Pole1
    next = `State0 -> `State1
    top = `Pole0 -> (`State0 -> `Ring0 + `State1 -> `Ring0) + `Pole1 -> `State1 -> `Ring0
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole0)
    radius = `Ring0 -> 1 + `Ring1 -> 2
    underMe = `Ring0 -> `State0 -> `Ring1
  }

  example noTop is not {some pre, post: State | canTransition[pre, post]} for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1
    Pole = `Pole0 + `Pole1
    next = `State0 -> `State1
    top = `Pole0 -> (`State0 -> `Ring0 + `State1 -> `Ring1)
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole0)
    radius = `Ring0 -> 1 + `Ring1 -> 2
    underMe = `Ring0 -> `State0 -> `Ring1
  }

  example noTopUpdate is not {some pre, post: State | canTransition[pre, post]} for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1
    Pole = `Pole0 + `Pole1
    next = `State0 -> `State1
    top = `Pole0 -> `State0 -> `Ring0 + `Pole1 -> `State1 -> `Ring0
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole0)
    radius = `Ring0 -> 1 + `Ring1 -> 2
    underMe = `Ring0 -> `State0 -> `Ring1
  }

}

test suite for transitionStates {
  example invalidInitState is not transitionStates for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1 + `Ring2
    Pole = `Pole0 + `Pole1 + `Pole2
    next = `State0 -> `State1
    top = `Pole0 -> `State0 -> `Ring0 +
          `Pole1 -> `State1 -> `Ring0 +
          `Pole2 -> `State0 -> `Ring2
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole2) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole1 + `Ring2 -> `Pole1)
    radius = `Ring0 -> 1 + `Ring1 -> 2 + `Ring2 -> 3
    underMe = `Ring0 -> (`State0 -> `Ring1 + `State1 -> `Ring1) +
              `Ring1 -> (`State1 -> `Ring2)
  }

  example invalidFinalState is not transitionStates for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1 + `Ring2
    Pole = `Pole0 + `Pole1 + `Pole2
    next = `State0 -> `State1
    top = `Pole0 -> `State0 -> `Ring0 +
          `Pole1 -> `State1 -> `Ring0 +
          `Pole2 -> `State0 -> `Ring2
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole1 + `Ring1 -> `Pole1 + `Ring2 -> `Pole2)
    radius = `Ring0 -> 1 + `Ring1 -> 2 + `Ring2 -> 3
    underMe = `Ring0 -> (`State0 -> `Ring1 + `State1 -> `Ring1) +
              `Ring1 -> (`State0 -> `Ring2)
  }

  example endedOnInitPole is not transitionStates for {
    State = `State0 + `State1
    Ring = `Ring0 + `Ring1 + `Ring2
    Pole = `Pole0 + `Pole1
    next = `State0 -> `State1
    top = `Pole0 -> (`State0 -> `Ring0 + `State1 -> `Ring0)
    ringMap = `State0 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole0) +
              `State1 -> (`Ring0 -> `Pole0 + `Ring1 -> `Pole0 + `Ring2 -> `Pole0)
    radius = `Ring0 -> 1 + `Ring1 -> 2 + `Ring2 -> 3
    underMe = `Ring0 -> `State0 -> `Ring1 + `Ring1 -> `State0 -> `Ring2
  }
}

test suite for validRadii {
  example allValidRadii is validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> 1 + `Ring1 -> 3 + `Ring2 -> 2 + `Ring3 -> 4 + `Ring4 -> 5
  }

  example valueGap is not validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> 1 + `Ring1 -> 3 + `Ring2 -> 2 + `Ring3 -> 4 + `Ring4 -> 6
  }

  example duplicateRadius is not validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> 1 + `Ring1 -> 3 + `Ring2 -> 2 + `Ring3 -> 3 + `Ring4 -> 4
  }

  example greaterThanOneStart is not validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> 2 + `Ring1 -> 3 + `Ring2 -> 4 + `Ring3 -> 5 + `Ring4 -> 6
  }

  example zeroStart is not validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> 0 + `Ring1 -> 1 + `Ring2 -> 2 + `Ring3 -> 3 + `Ring4 -> 4
  }

  example negativeStartIncluding1 is not validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> -1 + `Ring1 -> 0 + `Ring2 -> 1 + `Ring3 -> 2 + `Ring4 -> 3
  }

  example negativeStartExcluding1 is not validRadii for {
    Ring = `Ring0 + `Ring1 + `Ring2 + `Ring3 + `Ring4
    radius = `Ring0 -> -4 + `Ring1 -> -3 + `Ring2 -> -2 + `Ring3 -> -1 + `Ring4 -> 0
  }
}