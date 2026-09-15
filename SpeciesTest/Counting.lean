import Species.Instances.Instances
import Species.Cardinality
import Species.Operations.Operations
import Mathlib.Data.Finset.Sort

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
#guard seq (cartProd E Powerset) 5 = [1, 2, 4, 8, 16]
#guard seq (Restrict Powerset 3) 5 = [0, 0, 0, 8, 0]

/- Simple structures -/
#eval structures_canonical L 3
#eval structures_canonical C 4
#eval structures_canonical C 0
#eval structures_canonical L 0
#eval structures_canonical E 3
#eval structures_canonical One 0
#eval structures_canonical One 3
#eval structures_canonical S 3
#eval structures_canonical Powerset 3
#eval structures_canonical X 0
#eval structures_canonical X 1
#eval structures_canonical X 2
#eval structures_canonical Zero 0
#eval structures_canonical Zero 3

/- Combined structures -/
#eval structures_canonical (Add E L) 3
#eval structures_canonical (Add E (Add E E)) 3
#eval structures_canonical (Mul E L) 3
#eval structures_canonical (Mul E E) 5
#eval structures_canonical (Mul (Add C L) S) 3
#eval structures_canonical (Mul (Mul C L) S) 3
#eval structures_canonical (cartProd E L) 3
#eval structures_canonical (Deriv E) 3
#eval structures_canonical (Deriv L) 3
#eval structures_canonical (Restrict Powerset 3) 5
#eval structures_canonical (Restrict Powerset 3) 3
/- #eval structures_canonical (Composition L L) 3 -/
