import BilinearComplexity.BinaryKMRegression

set_option autoImplicit false

open Lean
open BilinearComplexity.BinaryKMRegression

/-- Print the four frozen real-compiler regression packets as JSON Lines. -/
def main : IO Unit := do
  IO.println (Json.compress (toJson case1Packet))
  IO.println (Json.compress (toJson case2Packet))
  IO.println (Json.compress (toJson case3Packet))
  IO.println (Json.compress (toJson case4Packet))

example : main = (do
    IO.println (Json.compress (toJson case1Packet))
    IO.println (Json.compress (toJson case2Packet))
    IO.println (Json.compress (toJson case3Packet))
    IO.println (Json.compress (toJson case4Packet))) := rfl

#check @main
#print axioms main
