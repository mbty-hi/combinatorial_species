# Combinatorial species in Lean
A Lean formalization of combinatorial species following the combinatorial approach of Bergeron,
Labelle and Leroux (shortened to BLL below).

Developed at the University of Iceland (Iceproof project) by Matthieu Baty, under the supervision of
Anders Claesson, with contributions from Matthías Andri Hrafnkelsson.

## Building
First, install [elan](https://github.com/leanprover/elan). The required Lean version is pinned in
`lean-toolchain` (currently: `v4.35.0`), and `elan` installs it automatically.

```bash
git clone https://github.com/mbty-hi/combinatorial_species.git
cd combinatorial_species
lake exe cache get   # download prebuilt Mathlib files (much faster than building Mathlib)
lake build
```

To run the tests:
```bash
lake build SpeciesTest
```

## A brief overview of combinatorial species
A species is a rule (`F` of type `Type → Type`) that associates to each finite set (`U`) a finite
set `F[U]`, independently of the nature of the elements of `U`. The elements of `F[U]` are called
`F`-structures.

For instance, `F` could be the species `L` of linear orders. If `U` is `{a, b, c}`, then the
`L`-structures are `a > b > c`, `a > c > b`, `b > a > c`, `b > c > a`, `c > a > b` and `c > b > a`.
This means six possibilities in total, and there would be six possibilities for all other sets with
three elements (remember that the rule is independent of the nature of the elements of `U`).

Given two finite sets `U` and `V` such that `U ≅ V`, we can relabel an F-structure on U and obtain
an F-structure on `V`. This operation is called `transport`. Note that the linear orders `a > b > c`
and `c > b > a` are equivalent up to transport (via the automorphism with fixpoint `b` that sends
`a` to `c` and `c` to `a`). It is easy to convince oneself that all linear orders on a given `U` are
equivalent up to relabelling.

Graphs are another example of species, and they are quite different from linear orders in that for
sets `U` with at least two elements, we can produce graphs that are not equivalent up to
relabelling. Consider for instance the two graphs below:
```
           │    b
 a ═ b ═ c │ a ═╣
           │    c
```

An intuitive way of seeing that is to become blind to the nature of labels; the underlying shapes
are different:
```
           │    •
 • ═ • ═ • │ • ═╣
           │    •
```

The same cannot be said for linear orders, where becoming blind to labels leaves the same structure:
```
 a > b > c │ c > b > a

 • > • > • │ • > • > •
```

Combinatorial species were introduced by Joyal (1981) as a unified framework for the
generating-series-based methods of enumerative combinatorics, turning counting problems about such
families of structures into algebra. Each species has three generating series:
* the exponential generating series (EGS) for labelled counting
* the type generating series (TGS) for unlabelled counting
* the cycle index series (CIS) recording how many structures are fixed by relabelling operations of
  different cycle types; the EGS and the TGS can be derived from it

The framework also gives tools for computing these series for species built by combining species
according to classical operations (such as sum, product, or composition).

## What is supported
### Core definition (`Basic.lean`)
The core definition is faithful to BLL. We introduce a `Species` class that applies to a family of
structures `F`:
* `finite`: a proof of the fact that for any finite set of labels `U`, the number of `F`-structures
  on `U` is finite
* `transport`: the function that turns an `F`-structure on `U` to an `F`-structure on `V`, given a
  bijection between finite sets `U` and `V`
* `id_transport`: `transport id` is the same as `id`
* `comp_transport`: `transport f ∘ transport g` is the same as `transport (f ∘ g)`

The last two fields are the functoriality laws of `transport`. The functorial `transport` is what
guarantees that `F` does not depend on the nature of the label set's contents: it can tell labels
apart, but it cannot use any of their other properties.

In practice, we use label *types* (with `Finite`) and not label *sets* as in the book. This has no
bearing on the expressivity of the resulting theory, but it makes the proofs nicer.

### Computable species (`Computable.lean`)
A secondary objective of this work is to provide computable functions for generating structures. For
instance, a user should be able to enumerate all linear orders of sets of non-empty cycles labelled
with `{1, 2, 3, 4}` (each label used exactly once).

We introduce computable species as an optional extension to more general species. They add the
following two fields to the original definition, which both assume a finite and linearly ordered set
of labels `U` (`LabelType`):
* `fintype`: like `finite`, but builds an actual `Fintype` (i.e., a finite set containing all
  possible `F`-structures on `U`) instead of being a mere proof of such a set's finiteness
* `decEq`: the equality on the `F`-structures on `U` is decidable

### Enumeration (`Enumeration.lean`)
Auxiliary functions for enumerating `F`-structures in computable settings.

### Categorical bridge (`Categorical.lean`)
A bridge to Joyal's categorical definition of species.

### Isomorphism (`Isomorphism.lean`)
Isomorphisms of species (families of bijections compatible with relabelling).

### Labels (`Labels` folder)
#### Canonical (`Labels/Canonical.lean`)
The canonical label type `Fin n` (e.g., `Fin 3` has values in `{0, 1, 2}`).

#### Label type (`Labels/LabelType.lean`)
A finite and linearly ordered label type. The order is required for computability (`Finset` exposes
a `sort` function that gives a list of its members, and it requires `LinearOrder`).

### Instances (`Instances` folder)
All of these are computable:
* `0`: the empty species (in `Zero.lean`, uninhabited type)
* `1`: the unit species (in `One.lean`)
* `C`: cycles
* `E`: sets
* `L`: linear orders
* `Powerset`: powersets
* `S`: permutations
* `X`: singletons

### Operations (`Operations` folder)
#### Instances
All of these preserve computability:
* Sum
* Product
* Cartesian product
* Composition
* Derivative
* Pointing
* Restriction

#### Algebra (`Operations/Algebra` folder)
The operations satisfy the semiring laws only up to isomorphism, so we provide them as a collection
of isomorphisms rather than as a `Semiring` instance. `mulComm` and `mulAssoc` are currently only
shown up to bijection.

### Identities (`Identities` folder)
* `DerivC`: the derivative of cycles is linear orders (our proof is a bit ugly, the natural version
  would go via embeddings within graphs)
* `DerivE`: the derivative of sets is sets

### Series (`Series` folder)
* Exponential generating series (EGS): for labelled counting
* Type generating series (TGS): for unlabelled counting
* Cycle index series (CIS): for recording how many structures are fixed by relabelling operations of
  different cycle types. We give alternative definitions of the EGS and the TGS based on it, and
  show them equivalent to the classical ones.

#### Instances (`Series/Instances` folder)
Results about instances:
* C: EGS/TGS
* E: EGS/TGS
* L: EGS/TGS
* One: EGS/TGS
* Zero: EGS/TGS

#### Operations (`Series/Operations` folder)
Results about operations:
* Sum: EGS

### Tests (from the root: `SpeciesTest/Counting.lean`)
Building concrete F-structures and some sanity checks.

## Remaining work
### Unsorryfication
* `mulAssoc` (bijection ok, isomorphism TODO)
* `mulComm` (bijection ok, isomorphism TODO)
* `DerivC` (bijection ok, isomorphism TODO)

### More results about series
* Classical EGS/TGS/CIS for all instances
* Classical EGS/TGS/CIS for all operations
* Closed forms
* Isomorphic → series agree

### More species
* Ballots (linearly ordered partitions)
* Derangements (permutations with no fixed points)
* Endofunctions/Involutions/etc. Maybe `S` should be phrased as bijective endofunctions.
* Graphs: simple graphs, connected simple graphs, directed graphs
* Trees: trees and rooted trees (well, related to graphs)

### More identities
* `S ≅ E ∘ C`
* Ballots as linear orders of non-empty sets

### Fun problems/illustrations
* Montmort's hat-check problem
* Set partitions

### Additional concepts
* L-species
* Subspecies
* Virtual species
* Weighted species

### Computability
* Printing unlabelled species

## License
This project is released under the Apache License 2.0 (see `LICENSE`; this is the same license as
Mathlib).
