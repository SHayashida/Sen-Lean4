import Std.Tactic.BVDecide

example (x : BitVec 8) : x ^^^ x = 0 := by
  bv_decide?
