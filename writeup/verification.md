# Verification #

One of the HECTOR requirements that PSL doesn't currently address is
verification: a programmer should be able to write a PSL program that
generates proofs that various parts of the computation were performed
correctly. Or to be more precise, that the parties know values that
satisfy various properties.

In the interest of (1) imposing as little burden as possible on the
PSL programmer and (2) being lazy language designers, the first
question we could ask is if forms and operations for verification need
to be represented explicitly in PSL programs at all: instead, can it
all just be done "under the hood" without any explicit guidance in the
program?  Unfortunately, the answer seems to be "no" for a few
reasons:

1. Verification isn't required for all problems (e.g., the merge sort
   specification explicitly calls for no verification). So in general,
   programmers shouldn't have to pay the cost of verification if they
   don't want it. And in the closer term, a resource estimate that
   includes the cost of operations for verification wouldn't be
   well-justified.
2. For most problems, the property to be verified is really that the
   parties have computed a partially "correct" value, not that the
   parties have run a particular algorithm. E.g., the property for
   quicksort is that the parties have computed a sorted list, not that
   they necessarily ran quicksort to get it. This is even more
   exaggerated in Karmarkar, where each party should get a NIZK proof
   of a different fact about the output. It also speaks directly to
   why, HECTOR aside, having this in the language would be pretty
   conceptually unappealing.

So we'll probably need to make verification explicit in PSL to at
least some extent. To get an idea of how exactly we'll do it, let's
try to mock-up a solution to one of the challenge problems.

# Verification for Quick Sort #

Let's try to mockup how we'd like verification to look for Quick
Sort. The complete specification in the GFI for verification in Quick
Sort is as follows:

"""
Assume PKI; all inputs signed by the corresponding input parties (the
signatures are not included in the output sorted list, in order to
protect the inputs privacy).

MPC generates a fingerprint of the output (e.g., Merkle tree
root). Property verified: the fingerprinted output is the correct
sorted list of all (properly signed) inputs.
"""

One ambiguity in the spec: read literally, the second paragraph seems
to have a contradiction: according to it, the output sorted list
(sensibly) should not contain signed inputs, but also the MPC should
generate a fingerprint of an output that is the sorted list of signed
inputs. One apparent way to fix the spec is to require that the MPC
should generate a fingerprint of the sorted list `l` of signed inputs
and prove that each party has signed some value (and that the list is
sorted).

The deeper issue is that the spec throws a fair amount of crypto
mechanism in our laps (PKI's and signing, fingerprints and Merkle
trees): we have to figure out how concretely these really need to be
represented in PSL. Let's consider them in turn.

## PKI's and signing ##

The verification spec states (and is in fact the only point in the
problem statement that acknowledge) that in fact all of the inputs are
really signed by the input parties, but the elements in the final
sorted list distributed to all parties are definitely unsigned (which
certainly makes sense).

Given that one of the goals for PSL is to make crypto code as
burden-free as possible (and that we want to be lazy), the first
question that comes up again is if signing needs to be represented in
PSL at all. Maybe we can just implicitly treat all read inputs as
signed and let the PSL programmer ignore signing. Unfortunately, this
doesn't seem like it'll work cleanly for Quick Sort: the inputs are
signed, but the outputs need to be unsigned, so somehow some unsigning
computation needs to happen. We might try to salvage a language design
with implicit signing by saying that outputs are *always* unsigned,
but there's no reason to believe that this actually is always what the
PSL programmer would want for all applications. Keeping signing
completely under the rug just seems untenable.

But honestly that's not the end of the world: it's not like we have to
expose all of the guts of a full-featured PKI API either. One first
stab that seems workable is:

1. Extend the types of primitive values to have a dimension/field
independent of principal knowledge/location that denotes which parties
have signed the value.
2. Alter `read` to return values signed by the party who read them.
3. Provide an `unsign` operation that removes signatures from values.

One variation that's arguably a bit more flexible and decoupled is to
keep `read` the same as it is (i.e., still returning unsigned values)
and providing a `sign` operation in addition to `unsign` (which
respects some natural laws that require the signing parties all know
the value).

## Fingerprints ##

Read literally, the spec calls for programs to generate a fingerprint
of a sorted list. A first try at supporting this might be to introduce
a type of fingerprints and a fingerprinting operation and use them
explicitly in PSL code. This would work, but it arguably exposes a lot
of detail about a crypto mechanism that's difficult to connect to the
ultimate intent of verifying that principals know a value that
satisfies some property, without additionally enabling us to express
some kind of computation that we particularly care to do. I.e., it's
not like we need PSL programs to compute fingerprints and then add
them, compare them for equality, or share them independent of the
values that they're being used to verify. The fingerprint is really
just an artifact that's ultimately exported by the program in order to
prove that the parties have computed a value that satisfies some
desired property.

Here's an alternative that hopefully abstracts the details of
fingerprinting a bit better. The basic idea is that we'll introduce
the following into PSL:

1. A family of types `t{ committed : P }`, which each denote that
   parties `P` hold witnesses that produce a value of type `t` under
   some computation.
2. A family of types `t{ nizk : P }` for various base types `t` (in
   the case of Quick Sort, `flt`), each of which will denote a
   computation of a type of value `t` whose "shape" or "topology"
   (i.e., circuit structure) is known to all principals in `P`. These
   will be analogous to the families of types for the other various
   protocols supported in PSL (e.g., `flt{ bgw : P }`).
3. Operations for building `nizk` computations: i.e., values of types
   `t{ nizk : P }`. These will be analogous to the similar operations
   for other types of shares/protocols supported by PSL.
3. An operation `commit` that builds `nizk` commitments (i.e., values
   of type `t{ committed : P }`) from `nizk` computations (i.e.,
   values of type `t{ nizk : P }`). This will be analogous to the
   `reveal` operations for other types of shares/protocols.

## Operations for building verifiable computations ##

The operations for building verifiable computations over floats (to
take one relevant base type) would include the following:

1. Build "input wires" that hold some common secret value, denoted
   `nizk_flt_in : flt{ signed, ssec : P } -> flt{ nizk : P }`. For now
   we'll consider the simple case where the Prover is some collection
   of parties holding a common secret (which unfortunately isn't
   really the case in Quick Sort).
2. Build a computation of `<=` comparison over floats:
   `nizk_flt_leq : flt{ nizk : P } -> flt{ nizk : P } -> bool{ nizk :
   P }`;
3. Build a logical `AND` gate: `nizk_and : bool{ nizk : P } -> bool{
   nizk : P } -> bool { nizk : P }`;
4. Build a logical `OR` gate: `nizk_or : bool{ nizk : P } -> bool{
   nizk : P } -> bool { nizk : P }`;
5. Build a logical `NOT` gate: `nizk_not : bool{ nizk : P } -> bool{ nizk : P }`;
6. Build a computation that checks that a signed float is indeed
   signed by principals `P`: `nizk_signed : float{ signed, nizk : P }
   -> bool{ nizk : P }`.

Under the hood, all of these operations will really just build a
representation of the computation as a Boolean circuit, whose
computation can be verified using the PANTHEON team's NIZK protocol of
choice, MPC-in-the-head (the GFI gives no directive for the ZK
protocol to use).

For other problems (namely ATQ), we'll need to define operations for
building verifiable circuits that compute over other base types,
namely `nat`s and `int`s, along with appropriate `commit` operations.

### Example: building a NIZK proof for Quick Sort ###

As an example of how these operations would get used, consider a
simplified version of Quick Sort where one principal `A` wants to just
commit to a list `l` that is a sorted list of values signed by `A`,
with a proof that

1. `A` has signed each value in `l`;
2. `l` is sorted.

We'd achieve this by having `A`:

1. Build input wires `wsort : list flt{signed, nizk : A}` for each
   element in `l`;
2. Building a circuit `all_signed lwires`, where
```
signed : list flt{ signed, nizk : A } -> bool{ nizk : A }
```

   builds a circuit that checks that each element in its input is
   signed by `A`, using calls to `nizk_signed` and `nizk_and`.

3. Building a circuit `is_sorted lwires`, where
```
is_sorted : list flt{ signed, nizk : A } -> bool{ nizk : A }
```

   builds a circuit that checks that its input list of wires is
   sorted, using calls to `nizk_flt_leq` and `nizk_and`.

## An operation for building commitments ##

The final values that will be produced for verification will be values
of type `t{ committed : P }`. Under the hood, each value of such a
type really denotes a pair:

1. A cryptographic fingerprint of values `X` held by `P`, denoted
   `F(P)`;
2. A NIZK proof that the proving parties know some values `Y` that
   some circuit `C` evaluates to `C(X)` and whose fingerprint is
   `F(X)` (I'm guessing that the laws of fingerprinting schemes ensure
   that this implies that `X = Y` with overwhelming probability).
   
At the PSL level, these would all be bundled together in the opaque
type `t{ proto : committed }` that can only be built and passed
around, never operated on.

The commitment operation needed for Quick Sort would be to build
committed values:

```
nizk_commit : bool{ nizk : P } -> bool{ committed : P }
```

For other problems (namely Karmarkar) that don't require a fingerprint
of the output, we'll also want to provide a (simpler) operation, named
something like `nizk_verify`, whose outputs correspond to only items
(2) and (3) out of the list above (i.e., it doesn't include a
fingerprint of the witness input).

### Example: committing to the output of Quick Sort ###

Returning to the simplified version of Quick Sort that we were looking
at, principal `A` would ultimately build a commitment to its signed
list `l` by evaluating the PSL program

```
let wsort = map nizl_flt_in l in
nizk_commit (nizk_and (all_signed wsort) (is_sorted wsort))
```

to obtain a value of type `bool{ committed : A }` that denotes

1. A cryptographic fingerprint of `l`, `F(l)`;
2. A NIZK proof that `A` knows some sorted list `l'` with fingerprint
   `F(l)`, in which each element is signed by `A`.

# Requirements for resource estimation #

The interpreter can be extended so that when it evaluates the
construction of a NIZK proof, it emits resource requirements that
match what the crypto team is expecting. Our interpreter would
basically need to:

1. Implement each circuit-building operation by just explicitly
   building an actual circuit;
2. Implement `commit c` by emitting the circuit `c`, for which the
   resource estimator would estimate the cost of building a NIZK proof
   of commitment.

If it turns out that the crypto resource estimator needs to know only
the number of each operation in the circuit---not the topology of the
circuit---then obviously we can design the interpreter to emit just
this information.

# Allowing for provers that are an MPC # 

Unfortunately, our running example of Quick Sort has been a fiction:
at no point does any one party know the sorted list of signed inputs:
only the "third party" simulated by an MPC ever knows that. So what
further extensions to PSL are needed in order to support this
properly?

I'm going to make a claim which is either obvious or obviously wrong,
which is that for each protocol `p` with shares that we can convert to
additive Boolean shares (which should include at least BGW and SPDZ,
the only two protocols that we need to support alongside verification
anyways), we can introduce an operation

```
nizk_flt_shrs_in : flt{ p : Q } -> flt{ nizk : Q }
```

(and similarly for other base types.) We're then free to build `nizk`
circuits and commitments just as above.

Why can such a family of operations actually be implemented?

1. All of the operations for building `nizk` computation (e.g.,
   `nizk_and`) are just building circuits that will eventually get
   verified, so nothing changes at all with them, really.

2. `commit c` basically has three obligations:
   1. Compute a cryptographic fingerprint of `c`'s input `X`. This
      seems like it can be done by converting the `p` shares into
      additive Boolean shares and then executing the fingerprinting
      function in, say, GMW.
   2. Construct a NIZK proof of knowledge of a witness that `c`
      evaluates to `C(X)`. MPC-in-the-head works by running an MPC
      protocol multiple times and having some randomly chosen parties
      reveal their views---which include their shares---each time, so
      we can't just run it directly. But it seems like we can easily
      adapt it by just having each party first share a random mask of
      their share and then running MPC-(not)-in-the-head on the masked
      shares (this last part is obviously the biggest stretch and we'd
      want to talk with a crypto person about it, but I'm also willing
      to bet that the crypto community has some solution to this
      problem, even if this exact one is broken or just silly.)
