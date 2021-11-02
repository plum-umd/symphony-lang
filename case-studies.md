# Coordination Examples / Case Studies

In our S&P reviews, we got feedback that March Madness Millionaire's (MMM) was not motivating enough.
I believe this was primarily due to the fact that one can compute the maximum of a list by iterating
over it (there's no need for a bracketed, tournament-style game).

That being said, this criticism is only partially valid. A simple, linear scan is only possible if all
parties share their value with all other parties. This yields an `N`-party MPC which can be slow [1]. In contrast,
a coordinated approach requires `N` 2-party sessions which is much faster. However, this approach is not
equivalent because it leaks more information.

Below are some candidates for other case studies that we could use in addition to MMM which may be more
interesting / convincing.

[1] Some MPC protocols are asymptotically _exponential_ in the number of parties.

## Candidates

This section presents some candidate replacements for MMM.

### March Madness Marbles

Another tournament-style game, but where two players play a game of "marbles" from Squid Game instead of Millionaire's. The idea is to
help motivate the tournament structure by having some form of "tokens" that are modified over the course of the game. It isn't clear
what the private values in this game should be, though.

### Leader Election Protocols

**Suggested by Steve Lu**

There has been an uptick of papers which do leader (/committee) election prior to performing MPC.
The idea is that a smaller committee is chosen, and then the committee performs an MPC. This is done, for example, in some cryptocurrencies
to validate blocks. From Steve:

>A toy example might be something like there are 1000 parties who want to do MPC on all their inputs, but it's too costly and we want to outsource to say, 10 of them.
>They can all publish a VRF PK and run a secure coin flipping protocol to get some random value r, and every party i publishes their v_i=VRF(r,SK).
>Top ten highest v values are now leaders and everyone secret shares their inputs to the ten of them, then the leaders run 10-party MPC to produce an output for
>everyone (note that the use of VRF here is not strictly needed as there are plenty of other ways to elect, but it has an appeal to people thinking from the blockchain angle).

This sounds really interesting and plausible. Steve suggested a VRF due to concerns about integrity. However, in the semihonest setting, we can assume
that the parties are obeying the protocol. As such, we can perform leader election more easily. From Steve:

>...if the parties are labeled 0..n-1 then all parties output a random number and they get added together mod n to elect a winner
>(the insecurity comes from "rushing" adversaries which can pick last and make the winner whoever they want, but this gets the idea across).

In other words, `N` parties can all choose a local random number and then broadcast that number to all other parties. All the parties compute the
sum modulo `N` and then the parties with the `K` highest values form the committee to perform a `K` party MPC (`K << N`).

### Dynamic Participants

**Suggested by Steve Lu**

In the malicious setting, there are MPC protocols which are able to identify when an integrity violation has taken
place. When this happens, some protocols choose to abort the computation altogether. This leads to a malicious adversary being able to cause "denial
of service" attacks in which they cause an integrity violation purposefully to invalidate the MPC.

This suggestion isn't relevant to Symphony (currently) since (1) Symphony doesn't currently handle the malicious setting, and (2) it doesn't provide
a way for parties to dynamically join / leave the distributed computation. Channels between parties are established at the beginning of the MPC and
are assumed to be stable.

### Poker

**Suggested by Brett Falk**

`N` parties play poker by proceeding in rounds. Each round, they perform MPC to shuffle the deck of cards. Each party gets their hand
by having a subset of the deck revealed to them. They can choose to fold, in which case their cards may or may not be revealed to the other parties
depending on the rules of the game.

This is an interesting case study, and we are close to being able to handle it, but there are two issues. First, we don't have an `N`-party backend.
We could add GMW, but I'm just not sure if I can get that done before the PLDI deadline. Second, it requires some interaction. There needs to be a
"game loop" that prints the hand to the user, and takes an action (bet, fold) from standard input.

### Other

**Suggested by Brett Falk**

Other suggestions Brett provided, but which aren't currently feasible. Putting them here for posterity.

>What about some form of a "virtual" database?  For example, for some kind of anomaly detection.
>A long time ago, we talked to satellite operators, and they all wanted to know what type of errors ("anomalies")
>other operators were experiencing so they could better diagnose their own problems.  The issue was that no one
>wanted to reveal when they had had a problem.  Banks have expressed interest in this type of "virtual" database
>for cyber-intrusions as well.  One way to set this up is to have everyone secret-share their anomalies to a
>single unified database that everyone can query against, but you could also imagine some kind of routing functionality.
>If each entity initially shares some limited information, and then when a user queries the unified database, if it
>looks like they have a match, they're directed to do a more in-depth secure computation with the relevant entity (entities).
>
>I forget, are you participating in RACE?   https://www.darpa.mil/program/resilient-anonymous-communication-for-everyone
>Some of the MPC-based routing that's being developed there would probably benefit from a system that can dynamically
>change the participant set based on previous computations.
>
>Are you familiar with the Ren Project?  https://github.com/renproject/ren/wiki
>They are using rotating committees of co-signers (who have secret-shares of a secret-key for a digital signature scheme),
>then they use MPC to execute the signature.  They issue is that to avoid centralization, they want to regularly change the
>committee, this new committee is currently chosen randomly, but you could imagine the choice as coming out of the MPC
>computation from the current committee.
