# Current approaches to using crypto backends #

Up to this point, we've informally imagined the PSL operational
semantics as a machine that

* Evaluates non-cryptographic forms using explicit rules that we'll
  define;
* Evaluates various cryptographic operations by interpreting them in a
  "cryptographic backend".

Each backend includes a set/type of *shares*, and provides various
operations over shares, basically consisting of:

* Making shares;
* Revealing shares to a target party;
* Adding shares;
* Multiplying shares.

Examples of protocols that we expect to use to implement such backends
include

* Yao's garbled circuits;
* GMW
* BGW

We currently have reasonable confidence that all of these protocols
can be implemented as crypto backends that support the interface given
above.

# SPDZ #

SPDZ is a protocol for evaluating arithmetic circuits. It includes
many (complicated) features that it uses for optimization, but the key
idea is that it aggressively offloads as much computation as possible
to an *offline* setup phase that may be executed before all parties
are willing or able to present their inputs.

To first approximation, the idea is that in the offline phase, parties
compute a large set of *Beaver triples*, (just encrypted triples of
the form `(a, b, a * b)`). The integrity of these triples is ensured
using a MAC, performed using some key that is secret-shared between
the parties.

In the online phase, shares contain both shares of a plain value and
shares of the MAC key used to sign Beaver triples. Shares can be added
efficiently and locally (as usual). Parties multiple shares by opening
a Beaver triple and using it to evaluate the desired multiplication as
a sequence of linear operations (an old, but still amazing, idea that
dates back to the original paper by Beaver).

The main challenges from the perspective of PSL design are to
determine:

1. Can SPDZ be faithfully implemented as a crypto backend that
   implements the interface that we've used for the other protocols
   that we've considered? I.e., can we define a SPDZ crypto backend as
   interpretations of making shares, revealing shares, adding shares,
   and multiplying shares?
2. If not, how does PSL need to be extended in order to support a SPDZ
   crypto backend?
   
# Strawman 0: try to do all "offline" computation online # 

We might hope that, in the spirit of getting some working
implementation as quickly as possible, that we devise some
implementation of SPDZ that fits the current model by shoehorning all
computation that can be done offline so that it is intermixed with the
online computation that uses its results. This is obviously highly
undesirable because the "offline" computation isn't really done
offline at all, but it would be something that runs, and at least the
operations that it performs in a trace would correspond to the
operations performed by a more faithful implementation (after
reordering).

The first question is whether we can do this, and according to my
understanding of SPDZ, it may not actually be possible. By my
understanding, the key issue is that in SPDZ, the parties pre-compute
Beaver triples using shares of some MAC key that is fixed for the run
of the protocol. The correctness of multiplying shares relies
fundamentally on the fact that the shares contain shares of the same
MAC key. So there doesn't seem to be any obvious way for a PSL program
to take two SPDZ shares that were created completely independently
over an execution and correctly multiply them together.

There's arguably a deeper question that would have to be addressed
here: even if there were some way to intermix all offline computation
into the online computation, it's not clear that this will enable us
to generate a resource usage profile that matches the govt's
expectation. Oddly enough, discussion of offline vs. online resource
usage doesn't seem to have come up in any conversations with the govt
(although it certainly seems relatively nuanced). The discussion
within the PANTHEON team is still ongoing (see Mattermost).

# Strawman 1: rework the language so that each crypto backend can perform some global setup #

One apparent idea is to allow each crypto backend to create some
global initial state when each program begins execution, and update
the state as the program issues operations (e.g., multiply shares).

It certainly seems natural and likely necessary to treat crypto
backends as state machines, rather than interpretations of runtime
operations, as we have been up until now. The only sticking point with
this approach that keeps it from being able to accommodate SPDZ is
that a SPDZ backend would need to create a pool of Beaver triples
between parties that are actually going to cooperate in a SPDZ
protocol together. So we need to refine the model so that the backend
receives directives on which sets of parties are actually going to
execute together.

# Strawman 2: extend the interface of a crypto backend to include protocol instance state #

There seems to be a fairly immediate extension to PSL syntax and
semantics that can accommodate SPDZ: instead of viewing a crypto
backend as interpretations of a set of pure function, view it as
implementing operations of a state machine that maintains state for a
set of protocol *instances*, and yields values for each operation
executed in a particular instance.

In slightly more detail, in the revision of PSL, in addition to
defining a set/type of shares, a crypto backend would define a
set/type of protocol *instance state*. In the case of SPDZ, this state
would be an initial set of needed Beaver triples (or in a fancier
implementation, a handle to a process that generates Beaver triples
concurrently, etc.).

Each of the core operations of the protocol (making shares, revealing
shares, adding/multiplying shares) would now additionally be
parameterized on a protocol instance. In the case of the SPDZ backend,
it would use the pool of triples pointed to by the given instance to
perform the needed addition/multiplication operation, then update the
referenced pool to remove all triples used.

Maybe the biggest wrinkle to PSL that this would introduce is that the
types of shares would need to be indexed on protocol instances. There
are a few feasible extensions to PSL that would accommodate this:

* The simplest extension to PSL that should work for the challenge
  problems (and thus arguably the first one that we should try to code
  up) would be to have protocol instances declared similarly to how
  principals are declared currently, then extend the language so that
  declared protocol instances can be passed around analogously to how
  principals are passed currently.

* A more complicated extension would require each crypto backend `B`
  to a program operation that looks something like:

  ```
  mk_instance : (P : Principals) -> B.share P
  ```

  I don't know enough about dependent types to know how hard this
  would be to support, although it seems relatively tractable, given
  that the instances would only be subject to some simple laws
  governing their equality.
