import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.WithBot

/- Matthías: found this, do not keep as is: should be scoped, or maybe WithBot should be used
   directly. The reason is that we do not want to introduce a global linear order for options.
   Option is deliberately not equipped with an instance bc it leads to arbitrary choices. WithBot is
   just an alias of LinearOrder that comes with the instance we talked about; there is also
   WithTop. Using WithBot is probably cleaner? Only thing is, the name hides the fact that we are
   dealing with an option. -/

instance {α: Type} [LinearOrder α] : LinearOrder (Option α) :=
  inferInstanceAs (LinearOrder (WithBot α))
