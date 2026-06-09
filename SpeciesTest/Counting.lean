import Species.Instances.X
import Species.Instances.E
import Species.Instances.Powerset
import Species.Instances.Zero
import Species.Cardinality

#guard card SX 1     = 1
#guard seq  SX 5     = [0, 1, 0, 0, 0]
#guard seq  SE 5     = [1, 1, 1, 1, 1]
#guard seq  Finset 5 = [1, 2, 4, 8, 16]
#guard seq  SZero  5 = [0, 0, 0, 0, 0]
