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

$$`
P(X) \;=\; \sum_{q : Q} X^{R(q)}
\;\cong\; \sum_{q : Q} \bigl(R(q) \to X\bigr)
`

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

$$`
\operatorname{OracleQuery}(\mathsf{spec}, \alpha)
\;=\; P(\alpha)
\;\cong\;
\sum_{q : \mathsf{spec.Domain}}
  \bigl(\mathsf{spec.Range}(q) \to \alpha\bigr)
`

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

$$`
p \;=\; \sum_{q : Q} y^{R(q)}
`

is built from the transfinite chain:

$$`
p^{(0)} := y,
\qquad
p^{(\alpha+1)} := y + p \triangleleft p^{(\alpha)},
\qquad
p^{(\lambda)} := \operatorname*{colim}_{\alpha < \lambda} p^{(\alpha)}
`

for limit ordinals `lambda`. If `p` is `kappa`-small, the free polynomial monad
is the sufficiently large stage:

$$`
\mathfrak{m}(p) := p^{(\kappa)}
`

Concretely, `p^(0)` is "stop now", `p^(1)` is "stop or perform one
`p`-operation", and `p^(2)` is "stop or perform one operation and then, for
each possible response, stop or perform another operation". The colimit stage
collects all well-founded terminating `p`-decision trees.

For an oracle polynomial `p = Sum (q : Q), y^(R q)`, a position of
`mathfrak_m p` is a well-founded tree whose internal nodes are labeled by
queries `q : Q`, and whose outgoing branches at such a node are indexed by
responses `r : R q`. The directions of such a tree are its dangling leaves.
Evaluating at a return type `X` gives:

$$`
\mathfrak{m}(p)(X)
\;\cong\;
\sum_{T : \operatorname{Tree}(p)} X^{\operatorname{Leaves}(T)}
`

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

$$`
T(X) \;\cong\; X + P(T(X))
`

The constructor `pure` is the `X` summand: stop now and return a value.
The constructor `roll` is the recursive `P(T X)` summand: perform one
`P`-operation, and for each direction/response continue recursively.

For a container polynomial, this recursive summand expands as:

$$`
P(T(X))
\;\cong\;
\sum_{a : P.A} \bigl(P.B(a) \to T(X)\bigr)
`

so `roll a r` means: choose one operation shape `a : P.A`, and provide a
subtree `r d : T X` for every possible direction `d : P.B a`.
The name `roll` is the usual fixed-point intuition: it rolls one exposed
functor layer `P(T X)` back into the recursive type `T X`.

A finite-height approximation says the same thing without fixed-point
notation:

$$`
T_0(X) := X,
\qquad
T_{n+1}(X) := X + P(T_n(X)),
\qquad
T_\infty(X) := \operatorname*{colim}_{n} T_n(X)
`

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

$$`
\theta_X : P(X) \to mX,
\qquad
\theta_X(q,k) := \operatorname{map}(k)(\mathsf{impl}(q))
`

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

$$`
\operatorname{ProbComp}(X)
\;=\;
\operatorname{FreeMonad}\!\left(
  \sum_{n : \mathbb{N}} y^{\operatorname{Fin}(n+1)}
\right)(X)
`

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

$$`
P(X)
\;\cong\;
\sum_{q : \iota} \bigl(\mathsf{spec}(q) \to X\bigr)
`

then the uniform interpretation is a concrete query implementation:

```
uniformImpl : QueryImpl spec PMF
uniformImpl q := PMF.uniformOfFintype (spec.Range q)
```

Equivalently, at one polynomial layer it induces:

$$`
P(X) \to \operatorname{PMF}(X),
\qquad
(q,k) \mapsto
\operatorname{PMF.map}(k)\bigl(
  \operatorname{PMF.uniformOfFintype}(\mathsf{spec.Range}(q))
\bigr)
`

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

$$`
Q = \{\text{oracle query shapes}\},
\qquad
R(q) = \{\text{responses to } q\},
\qquad
P(X) = \sum_{q : Q} \bigl(R(q) \to X\bigr)
`

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

$$`
\mathsf{impl} : \prod_{q : Q} m(R(q)),
\qquad
(q,k) \mapsto
\operatorname{bind}\bigl(\mathsf{impl}(q),\; r \mapsto \operatorname{pure}(k(r))\bigr)
`

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

Read the local names as follows:

```
Name / notation        Meaning here
---------------------------------------------------------------------------
Exp                    experiment, not exponentiation
securityExp            security experiment: run the hidden-bit CKA game
correctnessExp         correctness experiment: check matching send/receive keys
gp                     game parameters, not a group element
→ₒ / ->o               constant oracle spec: query type -> response type
Unit →ₒ β              one command-like oracle, with response type β
Rho                    protocol-message type; this is the paper's T-space
I                      CKA epoch-key type; this is the paper's I-space
St                     local party-state type; this is the paper's γ-space
IK                     initialization-key type; this is the paper's K-space
```

The notation `A →ₒ B` is defined in `OracleSpec.lean` as:

```
notation A " →ₒ " B => OracleSpec.ofFn (fun (_ : A) => B)
```

So `Unit →ₒ Option (Rho × I)` is the oracle spec with one query input `()` and
responses of type `Option (Rho × I)`.

Paper side:

```
The challenger stores local states, counters, pending messages, hidden bit b,
and answers each oracle call by updating that state.
```

Lean side:

```
structure CKAScheme (m : Type -> Type u) [Monad m]
    (IK St I Rho : Type) where
  initKeyGen : m IK
  initA      : IK -> m St
  initB      : IK -> m St
  sendA      : St -> m (Option (I × Rho × St))
  recvA      : St -> Rho -> Option (I × St)
  sendB      : St -> m (Option (I × Rho × St))
  recvB      : St -> Rho -> Option (I × St)
```

For the security game we instantiate `m := ProbComp`, because key generation
and sending may sample randomness. The other type parameters are the protocol's
basic spaces:

```
IK   initial shared key material
St   local party state
I    epoch key / session-key material
Rho  protocol message
```

Important: `Rho` is not a map. It is only the Lean name for the type of CKA
messages. The paper writes these messages as `T`, for example `T_i`. We use
`Rho` to avoid overloading `T` with Lean's type variables. Likewise, `I` is the
type of CKA keys output in each epoch. These are the session/epoch keys that
the CKA game tests for real-or-random security. Long-lived or evolving private
protocol state lives in `St`, not in `I`.

The parameters fixed before the adversary runs are:

```
structure CKAScheme.GameParams where
  tStar          : Nat       -- paper t*
  deltaCKA       : Nat       -- paper Delta_CKA
  challengedParty : CKAParty -- paper P in {A, B}
```

Thus `gp` abbreviates "game parameters":

```
gp.tStar
gp.deltaCKA
gp.challengedParty
```

The Figure 3 oracle interface is the oracle specification:

```
def CKAScheme.ckaSecuritySpec (St Rho I : Type) :=
  ckaCorrectnessSpec Rho I
  + (Unit ->o Option (Rho × I))   -- chall-A
  + (Unit ->o Option (Rho × I))   -- chall-B
  + (Unit ->o Option St)          -- corr-A
  + (Unit ->o Option St)          -- corr-B
```

Expanding `ckaCorrectnessSpec`, this is the coproduct of these primitive
oracle families:

```
query branch        response fiber
OUnif n             Fin (n + 1)
OSendA              Option (Rho × I)
ORecvA              Unit
OSendB              Option (Rho × I)
ORecvB              Unit
OChallA             Option (Rho × I)
OChallB             Option (Rho × I)
OCorruptA           Option St
OCorruptB           Option St
```

Here "query branch" and "response fiber" are polynomial/container words:

$$`
P_{\mathrm{sec}}(X)
\;=\;
\sum_{q : Q_{\mathrm{sec}}}
  \bigl(R_{\mathrm{sec}}(q) \to X\bigr)
`

Here `query branch q` is the chosen summand / operation shape, and
`response fiber R_sec q` is the type of possible oracle answers for that
operation.

For example, `OSendA` is one branch of the coproduct. Its response fiber is
`Option (Rho × I)`: either the send request is rejected (`none`) or it returns
the message/key pair (`some (rho, key)`). In Spivak-style notation:

$$`
P_{\mathrm{sec}}
\;=\;
\sum_{q : Q_{\mathrm{sec}}} y^{R_{\mathrm{sec}}(q)}
`

so the table lists the `q`s and their corresponding `R_sec q`s.

So, as a polynomial/container, the security spec determines a query type and a
response family. To keep the mathematics readable, write the Lean oracle
specification

```
S_sec := CKAScheme.ckaSecuritySpec St Rho I
```

as `S_sec`. Then:

$$`
\begin{aligned}
Q_{\mathrm{sec}} &:= S_{\mathrm{sec}}.\operatorname{Domain}, \\
R_{\mathrm{sec}}(q) &:= S_{\mathrm{sec}}.\operatorname{Range}(q).
\end{aligned}
`

$$`
P_{\mathrm{sec}}(X)
\;=\;
\sum_{q : Q_{\mathrm{sec}}}
  \bigl(R_{\mathrm{sec}}(q) \to X\bigr)
`

An adversary is the free monad on that polynomial, returning a Boolean guess:

```
abbrev CKAScheme.CKAAdversary (St Rho I : Type) :=
  OracleComp (CKAScheme.ckaSecuritySpec St Rho I) Bool
```

The challenger implementation is one-layer semantics for that polynomial:

```
CKAScheme.ckaSecurityImpl :
  CKAScheme.GameParams ->
  CKAScheme ProbComp IK St I Rho ->
  QueryImpl (CKAScheme.ckaSecuritySpec St Rho I)
    (StateT (CKAScheme.GameState St I Rho) ProbComp)
```

Internally it is assembled by coproducting the primitive handlers:

```
ckaSecurityImpl gp cka =
  ckaCorrectnessImpl cka
  + oracleChallA gp cka
  + oracleChallB gp cka
  + oracleCorruptA gp St I Rho
  + oracleCorruptB gp St I Rho
```

The correctness spec is the send/receive-only subinterface:

```
def CKAScheme.ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec
  + (Unit →ₒ Option (Rho × I))  -- send-A
  + (Unit →ₒ Unit)              -- receive-A
  + (Unit →ₒ Option (Rho × I))  -- send-B
  + (Unit →ₒ Unit)              -- receive-B
```

It is used by `correctnessExp`: initialize both parties, run an adversary that
may schedule honest sends and receives, and return the accumulated `correct`
flag saying whether every receive-side key matched the corresponding sender
key.

Equivalently, after fixing `gp` and `cka`:

```
impl := CKAScheme.ckaSecurityImpl gp cka

impl :
  (q : Q_sec) ->
    StateT (CKAScheme.GameState St I Rho) ProbComp (R_sec q)
```

This is exactly the natural transformation from one security-oracle layer to
the semantic monad:

$$`
\theta_X :
P_{\mathrm{sec}}(X)
\to
\operatorname{StateT}(\mathsf{GameState}, \operatorname{ProbComp})(X)
`

$$`
\theta_X(q,k)
\;=\;
\operatorname{bind}\bigl(\mathsf{impl}(q),\; r \mapsto \operatorname{pure}(k(r))\bigr)
`

Here the semantic monad is:

```
StateT (CKAScheme.GameState St I Rho) ProbComp X
  = GameState St I Rho -> ProbComp (X × GameState St I Rho)
```

`StateT σ m X` is the usual state monad transformer. It turns an initial state
`σ` into an `m`-effectful pair `(output, nextState)`. Here:

```
σ = CKAScheme.GameState St I Rho
m = ProbComp
```

So answering a single oracle query may read and update the challenger state,
and may also sample randomness through `ProbComp`.

The game state is the concrete store for Figure 3:

```
Lean field       Paper object / role                   Natural language
---------------------------------------------------------------------------
stA, stB         γ_A, γ_B                               current local states
rhoA, rhoB       pending T from A/B                     undelivered messages
keyA, keyB       pending I paired with rhoA/rhoB        sender keys to compare
b                hidden bit b                           real-vs-random branch
correct          correctness accumulator                all key checks so far
lastAction       ping-pong phase                        enforce A/B alternation
tA, tB           t_A, t_B                               per-party epoch counters
```

By the universal property of the free monad, `simulateQ` extends the one-layer
implementation to all adaptive adversary trees:

```
simulateQ impl :
  OracleComp (CKAScheme.ckaSecuritySpec St Rho I) Bool ->
  StateT (CKAScheme.GameState St I Rho) ProbComp Bool
```

Operationally:

```
simulateQ impl (pure b') = pure b'

simulateQ impl (query q >>= k) =
  do
    let r <- impl q
    simulateQ impl (k r)
```

Finally, `securityExp` is the Figure 3 wrapper around that interpreter:

```
CKAScheme.securityExp :
  CKAScheme ProbComp IK St I Rho ->
  CKAScheme.CKAAdversary St Rho I ->
  CKAScheme.GameParams ->
  ProbComp Bool

securityExp cka adversary gp = do
  let ik  <- cka.initKeyGen
  let stA <- cka.initA ik
  let stB <- cka.initB ik
  let b   <- $ᵗ Bool
  let initialState := initGameState stA stB b
  let (b', _) <- (simulateQ (ckaSecurityImpl gp cka) adversary).run initialState
  return (b == b')
```

So the paper's interactive security experiment has three Lean layers:

```
1. ckaSecuritySpec
   the polynomial interface of allowed Figure 3 oracle calls

2. ckaSecurityImpl gp cka
   the one-query challenger semantics into StateT GameState ProbComp

3. simulateQ (ckaSecurityImpl gp cka) adversary
   the induced interpreter for the whole adaptive adversary tree
```

The full paper-to-code-to-language correspondence is:

* Paper `CKA-Init-A` / `CKA-Init-B`; Lean `initA` / `initB`.
  Natural language: initialize the local party states from the initial key
  material.

* Paper `CKA-S`; Lean `sendA` / `sendB`.
  Natural language: run the sending step, producing an epoch key, outgoing
  protocol message, and next local state.

* Paper `CKA-R`; Lean `recvA` / `recvB`.
  Natural language: receive a pending protocol message and update the local
  state, possibly producing the matching epoch key.

* Paper `T_i`; Lean `Rho` values and the game fields `rhoA`, `rhoB`.
  Natural language: CKA protocol messages, stored until the receiving party
  consumes them.

* Paper `I_i`; Lean `I` values and the game fields `keyA`, `keyB`.
  Natural language: CKA epoch/session keys whose real-or-random security is
  tested by the challenge oracle.

* Paper `γ_A`, `γ_B`; Lean `stA`, `stB`.
  Natural language: the evolving private local states of the two parties.

* Paper `t*`, `Delta_CKA`, `P`; Lean `gp.tStar`, `gp.deltaCKA`,
  `gp.challengedParty`.
  Natural language: fixed game parameters: the challenged epoch, allowed
  challenge window, and challenged party.

* Paper `send-P`; Lean `oracleSendA` / `oracleSendB`.
  Natural language: the honest send oracle.

* Paper `receive-P`; Lean `oracleRecvA` / `oracleRecvB`.
  Natural language: the honest receive oracle.

* Paper `chall-P`; Lean `oracleChallA` / `oracleChallB`.
  Natural language: the challenge send oracle, returning either the real epoch
  key or a random key according to the hidden bit.

* Paper `corr-P`; Lean `oracleCorruptA` / `oracleCorruptB`.
  Natural language: the allowed state-reveal oracle, guarded by the paper's
  corruption conditions.

* Paper Figure 3 oracle list; Lean `ckaSecuritySpec`.
  Natural language: the polynomial/container of all primitive oracle queries
  available to the adversary.

* Paper Figure 3 oracle procedures; Lean `ckaSecurityImpl`.
  Natural language: the one-query semantics of those oracle procedures into
  `StateT GameState ProbComp`.

* Paper adaptive attacker; Lean `CKAAdversary`.
  Natural language: a free-monad oracle program, i.e. an adaptive query tree
  returning a Boolean guess.

* Paper running the game; Lean `simulateQ impl adversary`.
  Natural language: interpret the adversary's query tree using the challenger
  implementation.

* Paper win condition `b' = b`; Lean `securityExp`.
  Natural language: the randomized experiment that returns whether the
  adversary guessed the hidden bit.

Faithfulness statement for the current branch:

```
Faithful within the documented scope:
  passive adversary
  alternating ping-pong schedule
  static challenge epoch t*
  explicit challenged party P
  send / receive / challenge / corruption oracles
  allow-corr and finished_P guards
  hidden real-or-random bit b

Intentional scope restriction:
  Figure 3's bad-randomness oracles send-P'(r) are omitted here.
```

The omission is intentional in this branch: the current CKA game keeps the
oracles needed for the DDH-CKA Theorem 3 path and the later post-quantum use
case, but does not model adversarially supplied sender coins. Therefore the
right claim is not "literal full Figure 3 including every oracle"; it is:

```
Figure 3 security game, specialized to the passive alternating static-challenge
scope and omitting send-P'(r).
```

Within that scope, the Lean model matches the paper because initialization
samples the initial key and party states, `securityExp` samples the hidden bit,
`ckaSecuritySpec` lists the allowed oracle calls, `ckaSecurityImpl` implements
the corresponding state updates and guards, failed `req` checks are represented
by `none`/no state update, and the final Boolean is exactly the event that the
adversary guessed the hidden bit.
:::
