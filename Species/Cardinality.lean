import Species.Basic
import Species.Labels.FinNat

/- Number of `F`-structures on `n` labels. -/
def card (F: Type → Type) [Species F] (n: ℕ) : ℕ := Fintype.card (F (FinNat n))

/- The first `n` terms of `F`'s counting sequence. -/
def seq (F: Type → Type) [Species F] (n: ℕ) : List ℕ := (List.range n).map (card F)
