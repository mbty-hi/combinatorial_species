import Species.Instances.E
import Species.Instances.L
import Species.Instances.Powerset
import Species.Instances.X
import Species.Instances.Zero
import Species.Cardinality
import Species.Operations.Add
import Species.Operations.CartesianProd
import Mathlib.Data.Finset.Sort

#guard card SX 1        = 1
#guard seq  SX 5        = [0, 1, 0, 0, 0]
#guard seq  SE 5        = [1, 1, 1, 1, 1]
#guard seq  SPowerset 5 = [1, 2, 4, 8, 16]
#guard seq  SZero 5     = [0, 0, 0, 0, 0]

#guard seq (SE + SE)     5 = [2,2,2,2,2]
#guard seq (SE × Finset) 5 = [1,2,4,8,16]

#eval structures_canonical Arrangement 3
