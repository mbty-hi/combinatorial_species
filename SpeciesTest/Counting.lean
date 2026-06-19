import Species.Instances.Instances
import Species.Cardinality
import Species.Operations.Operations
import Mathlib.Data.Finset.Sort

#guard card SX 1        = 1
#guard seq  SX 5        = [0, 1, 0, 0, 0]
#guard seq  SE 5        = [1, 1, 1, 1, 1]
#guard seq  SPowerset 5 = [1, 2, 4, 8, 16]
#guard seq  SZero 5     = [0, 0, 0, 0, 0]
#guard seq  SOne 5      = [1, 0, 0, 0, 0]
#guard seq  SCycle 5    = [0, 1, 1, 2, 6]

#guard seq (Species.add SE SE)          5 = [2, 2, 2, 2, 2]
#guard seq (Species.cartProd SE Finset) 5 = [1, 2, 4, 8, 16]
#guard seq (Restrict SPowerset 3)       5 = [0, 0, 0, 8, 0]

/- Simple structures -/
#eval structures_canonical Arrangement 3
#eval structures_canonical SCycle 4
#eval structures_canonical SE 3
#eval structures_canonical SOne 0
#eval structures_canonical SOne 3
#eval structures_canonical SPermutation 3
#eval structures_canonical SPowerset 3
#eval structures_canonical SX 0
#eval structures_canonical SX 1
#eval structures_canonical SX 2
#eval structures_canonical SZero 0
#eval structures_canonical SZero 3

/- Combined structures -/
#eval structures_canonical (Species.add SE Arrangement) 3
#eval structures_canonical (Species.cartProd SE Arrangement) 3
#eval structures_canonical (Species.Deriv SE) 3
#eval structures_canonical (Species.Deriv Arrangement) 3
#eval structures_canonical (Restrict SPowerset 3) 5
#eval structures_canonical (Restrict SPowerset 3) 3
