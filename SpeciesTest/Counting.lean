import Mathlib.Data.Finset.Sort
import Species.Instances.Instances
import Species.Enumeration
import Species.Operations.Operations

open Species

local notation "One"  => Species.One
local notation "Zero" => Species.Zero
local notation "Add"  => Species.Add
local notation "Mul"  => Species.Mul

#guard card X 1        = 1
#guard seq  X 5        = [0, 1, 0, 0, 0]
#guard seq  E 5        = [1, 1, 1, 1, 1]
#guard seq  Powerset 5 = [1, 2, 4, 8, 16]
#guard seq  Zero 5     = [0, 0, 0, 0, 0]
#guard seq  One 5      = [1, 0, 0, 0, 0]
#guard seq  C 5        = [0, 1, 1, 2, 6]
#guard seq  L 5        = [1, 1, 2, 6, 24]
#guard seq  S 5        = [1, 1, 2, 6, 24]

#guard seq (Add E E)             5 = [2, 2, 2, 2, 2]
#guard seq (CartProd E Powerset) 5 = [1, 2, 4, 8, 16]
#guard seq (Restrict Powerset 3) 5 = [0, 0, 0, 8, 0]

/- Simple structures -/
#eval structuresCanonical L 3
#eval structuresCanonical C 4
#eval structuresCanonical C 0
#eval structuresCanonical L 0
#eval structuresCanonical E 3
#eval structuresCanonical One 0
#eval structuresCanonical One 3
#eval structuresCanonical S 3
#eval structuresCanonical Powerset 3
#eval structuresCanonical X 0
#eval structuresCanonical X 1
#eval structuresCanonical X 2
#eval structuresCanonical Zero 0
#eval structuresCanonical Zero 3

/- Combined structures -/
#eval structuresCanonical (Add E L) 3
#eval structuresCanonical (Add E (Add E E)) 3
#eval structuresCanonical (Mul E L) 3
#eval structuresCanonical (Mul E E) 5
#eval structuresCanonical (Mul (Add C L) S) 3
#eval structuresCanonical (Mul (Mul C L) S) 3
#eval structuresCanonical (CartProd E L) 3
#eval structuresCanonical (Deriv E) 3
#eval structuresCanonical (Deriv L) 3
#eval structuresCanonical (Restrict Powerset 3) 5
#eval structuresCanonical (Restrict Powerset 3) 3
#eval structuresCanonical (Composition L L) 3
