import Species.Basic
import Species.Operations.Mul
import Species.Instances.One

namespace Species

/- `(mul SOne S) U` is a partitioning of `U` by a boolean predicate `d`. The set of labels making
   `d` true carries an `SOne`-structure, and its complement carries an `S`-structure. Since there
   are no `SOne`-structures for nonempty label sets, `d` must return `false` for all inputs. The
   isomorphism is therefore mostly about transport of the `S`-structure along
   `{u : U // d u = false} ≃ U`. -/
def one_mul {S: Type → Type} [Species S] {U} [Finite U] : (mul SOne S) U ≃ S U where
  toFun := by
    rintro ⟨d, one, s⟩
    have d_is_false : ∀u, d u = false := by -- we show that `d` must be `fun _ => false` (pointwise)
      intro u; rcases h : d u; rfl; nomatch (one ⟨u, h⟩)
    have equiv : {u // d u = false} ≃ U := Equiv.subtypeUnivEquiv d_is_false
    exact transportEquiv equiv s

  /- We must be very careful about how we write this function. Indeed,
     `{u // (fun _ => false) u = true}` and `{u // False}`, though equivalent, are different types
     (same goes for `{u // (fun _ => false) u = false}` and `{u // True}`). Being too eager with
     simplifications would force us to use `HEq` in `left_inv`, which is doable but more painful
     than being careful here. -/
  invFun := by
    intros s; unfold mul SOne
    refine ⟨fun _ => false, ?one, ?s⟩ -- we define `d` as `fun _ => false`
    case one => intros x; nomatch x   -- nothing ends up in the set carrying an `SOne`-structure
    case s   =>
      have equiv : {u // false = false} ≃ U := Equiv.subtypeUnivEquiv (by simp)
      exact transportEquiv equiv.symm s

  left_inv := by
    rintro ⟨d, one, s⟩
    have d_is_false : d = fun _ => false := by
      funext u; rcases h : d u; rfl; nomatch one ⟨u, h⟩
    subst d_is_false; simp; congr 2
    · funext x; nomatch x
    · rw [transportEquiv_symm, Equiv.symm_apply_apply]

  right_inv := by intros _; simp [transportEquiv_symm, Equiv.apply_symm_apply]

/- Same logic as `one_mul`, except for some flipped branches. See above for comments. -/
def mul_one {S : Type → Type} [Species S] {U} [Finite U] : (mul S SOne) U ≃ S U where
  toFun := by
    rintro ⟨d, s, one⟩
    have d_is_true : ∀u, d u = true := by -- we show that `d` must be `fun _ => true` (pointwise)
      intro u; rcases h : d u; nomatch (one ⟨u, h⟩); rfl
    have equiv : {u // d u = true} ≃ U := Equiv.subtypeUnivEquiv d_is_true
    exact transportEquiv equiv s

  invFun := by
    intros s; unfold mul SOne
    refine ⟨fun _ => true, ?s, ?one⟩ -- we define `d` as `fun _ => true`
    case s   =>
      have equiv : {u // true = true} ≃ U := Equiv.subtypeUnivEquiv (by simp)
      exact transportEquiv equiv.symm s
    case one => intros x; nomatch x  -- nothing ends up in the set carrying an `SOne`-structure

  left_inv := by
    rintro ⟨d, s, one⟩
    have d_is_true : d = fun _ => true := by
      funext u; rcases h : d u; nomatch one ⟨u, h⟩; rfl
    subst d_is_true; simp; congr 2
    · rw [transportEquiv_symm, Equiv.symm_apply_apply]
    · funext x; nomatch x

  right_inv := by intros _; simp[transportEquiv_symm, Equiv.apply_symm_apply]

end Species
