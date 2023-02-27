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
    underMe = `Ring0 ->`State0 -> `Ring1 + `Ring1 -> `State0 -> `Ring2
  }
}