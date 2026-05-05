/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.SourceBlock
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.QueryImpl
import VCVio.OracleComp.SimSemantics.SimulateQ
import Examples.CKA.Defs

/-!
# VCV-io Oracle Encoding

How the CKA oracle game is represented with `OracleSpec`, `OracleComp`, and
`QueryImpl`.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "VCV-io Oracle Encoding" =>
%%%
tag := "vcvio_oracles"
%%%

:::group "vcvio_core"
The VCV-io layer that turns Figure 3 into typed oracle syntax plus an
interpreter.
:::

The paper describes an interactive game by listing oracle procedures. VCV-io
separates that into two parts:

```
syntax:        which oracle calls may the adversary make?
semantics:     how does the challenger answer each oracle call?
```

The syntax is an `OracleSpec`. The adversary is an `OracleComp` over that spec.
The challenger is a `QueryImpl`, and `simulateQ` folds the adversary syntax
through that implementation.

```
Read this page as a stack:

OracleSpec       polynomial signature: query -> response type
OracleQuery      one query node plus all response continuations
OracleComp       free monad: adaptive oracle-program trees
QueryImpl        semantics for primitive query nodes
simulateQ        interpreter from syntax into a semantic monad
ProbComp         OracleComp specialized to uniform finite sampling
evalDist         probabilistic semantics as an SPMF
CKA game         StateT GameState ProbComp running adversary syntax
```

# Poly and Probabilistic Monad Theory

```
Main slogan:

OracleComp is syntax.
simulateQ runs that syntax against an implementation.
evalDist turns probabilistic syntax into an output distribution.
```

# OracleSpec Is The Polynomial Signature

The core VCV-io encoding is:

```
OracleSpec iota := iota -> Type
```

For `spec : OracleSpec iota`, VCV-io exposes:

```
spec.Domain  := iota
spec.Range q := spec q
```

Despite the name, `Range` is not the image of a map. It is the response fiber
over a query. Mathematically, write:

```
Q     := spec.Domain
R q   := spec.Range q
```

so that `spec` is a dependent family `R : Q -> Type`. As a
container/polynomial functor:

```
P(X) = Sum (q : Q), X^(R q)
     = Sigma (q : Q), (R q -> X)
```

Here `q : Q` is a query shape or oracle input, and `R q` is the type of possible
responses to that query. The continuation `R q -> X` records what the program
will do for every possible oracle answer.

VCV-io makes this polynomial presentation literal:

```
def OracleSpec.toPFunctor (spec : OracleSpec iota) : PFunctor :=
  { A := iota, B := spec }
```

# OracleQuery Is One Oracle Node

The corresponding one-step query functor is:

```
OracleQuery spec alpha
  = P(alpha)
  = Sigma (q : spec.Domain), (spec.Range q -> alpha)
```

The relation with `OracleSpec` is exactly the relation between a polynomial
signature and its value at a type:

```
iota : Type          query/index type
spec : OracleSpec iota
                    the response-family, equivalently spec : iota -> Type

spec                 corresponds to the polynomial P
OracleQuery spec X   corresponds to the evaluated functor P(X)
```

The identifier `spec` is just a conventional variable name for an oracle
specification. It is the whole interface, not the index type. The index type
`iota` gives the possible query shapes; the value `spec` assigns a response
type to each query shape.

It is called `spec` because it is the oracle specification: it specifies, for
each query shape/input `q : ι`, the type of valid oracle responses `spec q`.

So `spec : OracleSpec iota` remembers only the interface of primitive oracle
calls: which queries exist, and which response type belongs to each query. By
contrast, `OracleQuery spec X` is one layer of use of that interface, already
equipped with continuations into `X`.

Equivalently, the `OracleQuery` signature says: evaluate this polynomial on
some return/continuation type. If `spec : OracleSpec ι`, then
`OracleQuery spec X` means "evaluate the polynomial encoded by `spec` at
`X : Set`", morally and categorically; in Lean the universe-polymorphic
replacement for `Set` is a type.

An element of `OracleQuery spec alpha` is therefore one unresolved oracle
interaction: choose a query `q`, and provide a continuation for each response.
At this layer the continuation returns an ordinary `alpha`, not another
computation.

# OracleComp Is The Free Monad

`OracleComp spec alpha` is the free monad on that polynomial:

```
OracleComp spec alpha := PFunctor.FreeM spec.toPFunctor alpha
```

This is syntax, not probability. A value of `OracleComp spec alpha` is a
well-founded adaptive oracle-program tree:

```
pure x

or

ask q, then for each response r : spec.Range q continue as another tree
```

# Free Monad Construction

The polynomial free-monad construction can be read as the
`pattern_runs_on_matter` construction. In the monoidal category
`(Poly, triangleleft, y)`, with `triangleleft` meaning substitution of
polynomials and `y` the unit, the free monad on a polynomial

```
p = Sum (q : Q), y^(R q)
```

is built from the transfinite chain:

```
p^(0)        := y
p^(alpha+1) := y + p triangleleft p^(alpha)
p^(lambda)  := colim_{alpha < lambda} p^(alpha)
```

for limit ordinals `lambda`. If `p` is `kappa`-small, the free polynomial monad
is the sufficiently large stage:

```
mathfrak_m p := p^(kappa)
```

Concretely, `p^(0)` is "stop now", `p^(1)` is "stop or perform one
`p`-operation", and `p^(2)` is "stop or perform one operation and then, for
each possible response, stop or perform another operation". The colimit stage
collects all well-founded terminating `p`-decision trees.

For an oracle polynomial `p = Sum (q : Q), y^(R q)`, a position of
`mathfrak_m p` is a well-founded tree whose internal nodes are labeled by
queries `q : Q`, and whose outgoing branches at such a node are indexed by
responses `r : R q`. The directions of such a tree are its dangling leaves.
Evaluating at a return type `X` gives:

```
(mathfrak_m p)(X)
  = Sum (T : oracle tree shape), X^(leaves T)
```

So an element is a terminating oracle decision-tree shape together with a
return value in `X` for every dangling leaf.

Lean packages this evaluated object directly as an inductive family:

```
inductive PFunctor.FreeM (P : PFunctor) : Type -> Type
  | pure {alpha} (x : alpha) : FreeM P alpha
  | roll {alpha} (a : P.A) (r : P.B a -> FreeM P alpha) :
      FreeM P alpha
```

At the evaluated level, for a fixed return type `X`, the free monad is the
least recursive solution of:

```
T X = X + P(T X)
```

The constructor `pure` is the `X` summand: stop now and return a value.
The constructor `roll` is the recursive `P(T X)` summand: perform one
`P`-operation, and for each direction/response continue recursively.

For a container polynomial, this recursive summand expands as:

```
P(T X) = Sigma (a : P.A), (P.B a -> T X)
```

so `roll a r` means: choose one operation shape `a : P.A`, and provide a
subtree `r d : T X` for every possible direction `d : P.B a`.
The name `roll` is the usual fixed-point intuition: it rolls one exposed
functor layer `P(T X)` back into the recursive type `T X`.

A finite-height approximation says the same thing without fixed-point
notation:

```
T_0 X       := X
T_(n+1) X   := X + P(T_n X)
T_infty X   := colim_n T_n X
```

Here `T_n X` contains trees of height at most `n`; the colimit collects all
finite, well-founded trees.

For `P = spec.toPFunctor`, this specializes to:

```
pure :
  alpha -> OracleComp spec alpha

roll :
  (q : spec.Domain) ->
  (spec.Range q -> OracleComp spec alpha) ->
  OracleComp spec alpha
```

This is exactly adaptive oracle-program syntax.

# Bind Is Tree Grafting

The monad structure is tree substitution. Given:

```
t : Free(P)(X)
f : X -> Free(P)(Y)
```

the bind operation `t >>= f` replaces every leaf of `t` labeled by `x : X` with
the tree `f x`:

```
bind(pure x, f)
  = f x

bind(roll q k, f)
  = roll q (fun r => bind(k r, f))
```

Thus bind does not interpret oracle queries. It preserves the query tree and
grafts new computation trees at returned leaves. A path through a tree is a
transcript:

```
q_1, r_1, q_2, r_2, ..., q_n, r_n, return x
```

The response history determines which branch is taken next.

# QueryImpl And simulateQ

A `QueryImpl` is the semantic implementation of each primitive query in some
monad `m`:

```
QueryImpl spec m := (q : spec.Domain) -> m (spec.Range q)
```

In the formulas below, `impl : QueryImpl spec m`. Thus for each primitive
query `q`, the term `impl q` is a concrete monadic computation producing a
valid response:

```
impl q : m (spec.Range q)
```

Categorically, this induces the natural transformation from the one-step
polynomial into the underlying functor of `m`:

```
theta_X : P(X) -> m X
theta_X(q, k) = map k (impl q)
```

Here `(q, k)` is an element of `P(X)`, so:

```
q : spec.Domain
k : spec.Range q -> X
```

The function `k` is the continuation for this one query node: once the oracle
answer is known, `k` tells us which `X`-value this one-step computation should
produce. The expression `map k (impl q)` is functorial post-processing inside
the monad `m`: run `impl q` to obtain a response `r : spec.Range q`, then
return `k r : X` without changing the effects carried by `m`.

VCV-io calls this one-layer action `QueryImpl.mapQuery`. The free-monad
universal property then extends it uniquely to a monad morphism:

```
simulateQ impl : OracleComp spec alpha -> m alpha
```

Operationally:

```
simulateQ impl (pure x)
  = pure x

simulateQ impl (roll q k)
  = impl q >>= fun r =>
      simulateQ impl (k r)
```

So the free monad is the pattern: every possible adaptive oracle conversation.
The `QueryImpl` is the matter: a concrete stateful game, random oracle table,
probabilistic sampler, nondeterministic semantics, or another monad. The
interpreter `simulateQ` is the operation that runs the pattern on that matter.

```
Pattern side                         Matter side
------------                         -----------
OracleComp spec alpha                QueryImpl spec m
formal adaptive tree                 concrete answers in monad m

simulateQ impl : OracleComp spec alpha -> m alpha
```

# ProbComp And evalDist

`ProbComp` is the special case where the only primitive oracle is uniform
finite sampling:

```
abbrev ProbComp : Type -> Type := OracleComp unifSpec

unifSpec : OracleSpec Nat
unifSpec n = Fin (n + 1)
```

Therefore:

```
ProbComp X
  = FreeMonad(Sum (n : Nat), y^(Fin(n + 1)))(X)
```

The query `n : Nat` has one branch for every value of `Fin(n + 1)`, which
corresponds to sampling uniformly from `{0, ..., n}`. Even here, `ProbComp` is
still syntax until it is interpreted.

The probabilistic denotation is supplied by `evalDist`, but `evalDist` is not
one concrete global function that works for every monad automatically. It is
available for a monad `m` only when Lean has an instance:

```
[Monad m] [HasEvalSPMF m]
```

The class stores a monad homomorphism into subprobability mass functions:

```
class HasEvalSPMF (m : Type -> Type) [Monad m] where
  toSPMF : m →ᵐ SPMF
```

In Lean notation this is written:

```
toSPMF : m →ᵐ SPMF
```

Here `→ᵐ` means `MonadHom`: a natural transformation between monads that
preserves `pure` and `bind`. So `toSPMF` does not merely map each type
component `m X -> SPMF X`; it also respects sequencing:

```
toSPMF (pure x) = pure x
toSPMF (mx >>= f) = toSPMF mx >>= fun x => toSPMF (f x)
```

Then `evalDist` is just the public wrapper/projection:

```
evalDist : m alpha -> SPMF alpha
evalDist mx := HasEvalSPMF.toSPMF mx
```

So yes: operationally, `evalDist` is a wrapper around the `HasEvalSPMF`
semantics chosen for the monad `m`.

There is also a total-probability version:

```
class HasEvalPMF (m : Type -> Type) [Monad m] extends HasEvalSPMF m where
  toPMF : m →ᵐ PMF
```

An instance of `HasEvalPMF` gives a `HasEvalSPMF` instance by embedding
`PMF X` into `SPMF X`. This is why total computations can still use the same
`evalDist` notation.

For `OracleComp spec`, when the response fibers are finite and inhabited,
VCV-io provides a `HasEvalPMF` instance by interpreting every primitive oracle
response uniformly:

```
evalDist mx
  = simulateQ (fun q => PMF.uniformOfFintype (spec.Range q)) mx
```

This is still exactly the polynomial/free-monad story. If
`spec : OracleSpec ι` corresponds to:

```
P(X) = Sigma (q : ι), (spec q -> X)
```

then the uniform interpretation is a concrete query implementation:

```
uniformImpl : QueryImpl spec PMF
uniformImpl q := PMF.uniformOfFintype (spec.Range q)
```

Equivalently, at one polynomial layer it induces:

```
P(X) -> PMF X
(q, k) |-> PMF.map k (PMF.uniformOfFintype (spec.Range q))
```

The universal property of the free monad extends this one-layer map to:

```
simulateQ' uniformImpl : OracleComp spec →ᵐ PMF
```

The unbundled component at a return type `alpha` is `simulateQ uniformImpl`.
The `HasEvalPMF` instance for `OracleComp spec` uses exactly this monad
homomorphism. Finally, `evalDist` views the resulting `PMF alpha` as an
`SPMF alpha`.

For `ProbComp`, this means that each query `n` is interpreted as the uniform
distribution on `Fin(n + 1)`.

Probability notation is just evaluation of the resulting mass function:

```
Pr[= x | mx] = evalDist mx x
```

This means "the probability that running computation `mx` returns `x`":

```
P[result(mx) = x]
```

It is not the probability of the proposition `x = mx`; `mx` is a computation,
not an output value.

# CKA Stack

In the CKA development, `CKAScheme.ckaSecuritySpec St Rho I` already contains
`unifSpec` as its first summand, followed by the send, receive, challenge, and
corruption oracle families. Thus:

```
CKAScheme.CKAAdversary St Rho I
  = OracleComp (CKAScheme.ckaSecuritySpec St Rho I) Bool
```

is only adversary syntax. The game supplies:

```
QueryImpl (CKAScheme.ckaSecuritySpec St Rho I)
  (StateT (CKAScheme.GameState St I Rho) ProbComp)
```

meaning: for each adversary query, explain how to answer it while reading and
updating challenger state and while using `ProbComp` for randomness. Then:

```
simulateQ gameImpl adversary
  : StateT (CKAScheme.GameState St I Rho) ProbComp Bool
```

Running the state transformer on the initial game state gives a `ProbComp Bool`,
and `evalDist` turns that syntax into the `SPMF Bool` used by the probability
statements in the security theorem.

:::definition "oracle_spec_polynomial" (lean := "OracleSpec, OracleQuery") (parent := "vcvio_core")
An oracle signature is a dependent family of response types indexed by query
shapes.

Mathematical side:

```
Q       = type of oracle queries
R q     = type of responses to query q

P X     = Sum (q : Q), (R q -> X)
```

Lean side:

```
def OracleSpec (ι : Type u) := ι -> Type v

OracleSpec.OracleQuery spec α
  -- one primitive query, plus a continuation indexed by the response
```

In polynomial-functor language, `OracleQuery spec` is the container/polynomial
layer generated by the query shapes and response positions.
:::

:::definition "oracle_comp_free_monad" (lean := "OracleComp, simulateQ") (parent := "vcvio_core")
`OracleComp spec α` is the free monad generated by one-step oracle queries.

Mathematical side:

```
Free(P) X is the type of finite adaptive trees:

pure x

or

query q, then continue as a tree for each r : R q
```

Lean side, operationally:

```
pure : α -> OracleComp spec α

query :
  (q : spec.Domain) ->
  OracleComp spec (spec.Range q)

simulateQ :
  QueryImpl spec m ->
  OracleComp spec α ->
  m α
```

For CKA, this means the adversary can decide its next oracle call after seeing
the previous oracle response. That is exactly the adaptivity in Figure 3.
:::

:::definition "query_impl" (lean := "QueryImpl, simulateQ") (parent := "vcvio_core")
A `QueryImpl` gives concrete semantics to every primitive oracle call.

Mathematical side:

```
impl : Π q : Q, m (R q)

(q, k) : Sum (q : Q), (R q -> X)
maps to
impl q >>= fun r => pure (k r)
```

Lean side:

```
def QueryImpl (spec : OracleSpec ι) (m : Type -> Type) :=
  (q : spec.Domain) -> m (spec.Range q)
```

When `m` is `StateT GameState ProbComp`, a query implementation is a stateful
randomized challenger.
:::

:::definition "prob_comp" (lean := "ProbComp, evalDist") (parent := "vcvio_core")
`ProbComp` is the special case of `OracleComp` where the only primitive oracle
is uniform finite sampling.

Mathematical side:

```
ProbComp X = randomized computation returning X
evalDist mx x = probability that mx returns x
```

Lean side:

```
abbrev ProbComp α := OracleComp unifSpec α

Pr[= x | mx]
```

For this CKA formalization, an experiment such as `securityExp` has type
`ProbComp Bool`. Applying `Pr[= true | ...]` extracts the probability of
adversary success.
:::

:::definition "stateful_challenger" (lean := "CKAScheme.ckaSecurityImpl, CKAScheme.securityExp") (parent := "vcvio_core")
The CKA challenger is an interpreter into a state transformer over
randomness.

Paper side:

```
The challenger stores local states, counters, pending messages, hidden bit b,
and answers each oracle call by updating that state.
```

Lean side:

```
CKAScheme.ckaSecurityImpl :
  QueryImpl (CKAScheme.ckaSecuritySpec St Rho I)
    (StateT (CKAScheme.GameState St I Rho) ProbComp)

CKAScheme.securityExp :
  CKAScheme ProbComp IK St I Rho ->
  CKAScheme.CKAAdversary St Rho I ->
  CKAScheme.GameParams ->
  ProbComp Bool
```

Thus the paper's interactive game is implemented by:

```
(simulateQ (ckaSecurityImpl gp cka) adversary).run initialState
```
:::
