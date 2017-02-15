Responses to Reviewers
======================

For the paper "A Conflict-Free Replicated JSON Datatype", under submission at
IEEE TPDS. Thank you to the reviewers for their helpful comments.


Reviewer 1
----------

> **Recommendation: Author Should Prepare A Minor Revision**
> 
> The article is very well written and easy to follow. The formal rules might
> have been simpler in the format of a mathematical pseudo-code algorithm with
> some auxiliary functions, but it is a stylistic choice and the rules do serve
> the purpose of removing ambiguity and supporting the proofs.

We agree that the style using deduction rules is unfortunately harder to read than
pseudocode, but we felt that in this case, avoiding ambiguity was more important.
Our initial definition actually used a combination of mathematics and pseudocode,
but we found ourselves having to invent nonstandard notation in order to be
precise. This notation turned out to be even more confusing than the deduction
rules, which are at least a widely recognized notation.

> The work is also
> well grounded on the state of the art, so I would only draw attention to a very
> recent related work that is also related to sequences and RGA: Hagit Attiya,
> Sebastian Burckhardt, Alexey Gotsman, Adam Morrison, Hongseok Yang, and Marek
> Zawirski, Specification and complexity of collaborative text editing, PODC'16.  

Thank you for the reference; we have added it to the paper.

> As the authors acknowledge, the treatment of causality is based on the
> frameworks of causal contexts defined for delta state CRDTs, and state based
> CRDTs in general, and embodied in current Riak maps. The approach the authors
> propose for JSON looks equally robust in terms of the provided semantics, but
> uses more metadata. For instance tombstones are kept here, and are probably
> needed for RGA like lists, and thus they cannot be so compactly encoded in
> causal contexts. It would be interesting to better clarify if this limitation
> is mandatory given the JSON structure or if it can be improved in the future.

According to Attiya et al.'s paper that you mentioned above, tombstones and
metadata overhead are in some sense inherent in concurrently editable list data
structures. Since JSON is a superset of lists, this result applies to JSON as
well. We have some ideas on how metadata overhead and tombstone cost can be
reduced, but the problem is difficult enough that we cannot fit a detailed
discussion in the length restrictions of the current paper. In the conclusion we
remark that these issues need to be addressed in future work.

> In section 4, it might be timely to briefly explain "pres" and not defer for
> later.  

Restructured the explanation to avoid referring to "pres" before it is defined.

> The JSON tree can branch either by a mapT or listT, and (MV)register forms
> terminal nodes. I failed to detect in the rules what happens if one node adds a
> map under a new key and another adds a list under the same new key. When they
> merge, do we get the two types of branch there? Is there a deterministic choice
> there? Does the new key reflect the type, and in fact lead to different
> keys ...?

Our rules handle this case by tagging each key with the datatype of its value;
in this scenario, the CRDT retains both the list value and the map value, so the
datatype acts as a namespace. When a program contains an expression that
evaluates to a cursor, the expression implicitly specifies whether the program
is expecting the value to be a list or a map, and thus uses the appropriate
version.

We have added Figure 5 in the revised version of the paper to make this scenario
more explicit.

> The system uses lamport timestamps for the operation pair (c,p). Is it really
> needed to have the counter grow to the max of all received counters? Since
> causality is tracked by the "deps" field it looks that the counters would only
> need to grow locally and not jump forward to match received higher counters.
> Notice that the replica id would be enough to disambiguate concurrent list
> insertions at the same location.  

Yes, the use of the maximum is needed by the RGA algorithm, which requires the
total ordering of IDs to be consistent with causality. This fact is used in the
proof of Lemma 3.

> The system is formalized as transmitting the whole grow-only queue of operations
> all the time. This works, in theory, but can be even worse than full state based
> CRDTs, since state based does some compression already. Maybe a section on
> implementation guidelines could help bridge the gap from the formal model
> (designed for proofs) and what would be a more practical implementation.

In section 4.2.2 we already refer the reader to version vectors and related
algorithms, which are more efficient ways of expressing causal dependencies, but
which would muddy the explanation of the semantics. We agree that more detail on
the bridge from formal model to practical implementation is needed, but we do
not have space to cover the topic in the necessary detail in this paper (we are
already at the page limit).

> **Please explain how this manuscript advances this field of research and/or
> contributes something new to the literature.**
>
> The paper introduce a composable conflict-free replicated data-type that
> allows nested documents with Maps, Lists, and Multi-value registers. While
> composability has been shown before for Maps, this work shows, for the first
> time, how to integrate both lists and maps. By targeting a well established
> format, JSON, can help influence the industry practice.
>
> **Please rate the manuscript. Please explain your choice.**
>
>  Excellent

Thank you!


Reviewer 2
----------

> **Recommendation: Author Should Prepare A Major Revision For A Second Review**
> 
> Paper strength
> 
> 1. This paper is informative to readers who are not familiar with CRDTs. It is
>    written clearly and the examples are easy to follow.
> 2. It provides a good use case of applying the well-known Lamport timestamps for
>    conflict resolution.

In our opinion, the main contribution of the paper is the definition of a CRDT
that allows maps, lists, and registers to be nested arbitrarily. This data model
is widely used in practice, but has not previously been able to benefit from the
existing work on CRDTs. The fact that our algorithm uses Lamport timestamps is
mostly an incidental detail.

> Paper weakness
> 
> About the novelty of this paper: 
> 
> I truly appreciate the authors' efforts in designing the algorithm and
> semantics for enabling automatic conflict resolution for the JSON datatype.
> However, in terms of conflict handling, the authors simply adopt Lamport
> timestamps to obtain the total ordering of operations and compare their
> approach against "last write wins." In my opinion this approach may work
> regardless of the underlying datatypes. It is not clear to me how the
> algorithm and semantics designed in the first part of this paper (Sec. 3)
> relate to the second part (Sec. 4). Also the proofs for the convergence of
> document states seem quite general, which do not rely on the data structures
> (flat structure vs. arbitrarily nested structure).
> 
> As a tentative suggestion, maybe the authors could add a paragraph or two
> somewhere in Sec. 4 to further highlight and clarify the difficulty/challenge
> of applying existing techniques (e.g., Lamport timestamps) to their proposed
> datatype for conflict handling, and how their semantics help with addressing
> the problem. 

It is not true that we simply use Lamport timestamps to order operations; the
ordering of Lamport timestamps is only used in one particular scenario, namely
the concurrent insertion of elements by different replicas at the same position
in the same ordered list within a JSON tree. The property that we require for
convergence (viz. the commutativity of concurrent operations) is achieved by
carefully constructing operations and replica metadata to achieve this goal. For
example, the construction of cursors that enables the use of nested structures
is quite subtle -- we went through many failed attempts before finding
a representation of operations that converged in all circumstances.

In the revised paper, we have added two new examples to Section 3 to highlight
some more difficulties of combining concurrent editing with nested data
structures, and expanded the text to show why it is a difficult problem that has
not been solved before.

> About the completeness of this paper: 
> 
> It is a pity that the main content of this paper stops at Sec. 4 with only
> the theorem for state convergence. Since the authors mention that they have
> an experimental collaborative text editor (although I couldn't find it in the
> supplement material) which implements the proposed CRDT, maybe they could
> find a way to visualize a sequence of operations from different collaborators
> and show some interesting scenarios, e.g., (i) normal valid execution without
> network failure, (ii) execution with one of the collaborators suffering from
> temporary network failure. 

We have a limit of 14 pages for this paper, so we have to keep it focussed on
the theoretical aspects of the algorithm, and leave discussion of practical
implementations for future work. We have removed the reference to our
experimental editor to avoid muddying the waters. We believe that the
theoretical aspects are in themselves a strong contribution, as evidenced by the
positive comments from other reviewers.

Temporary network failures are an inherent part of our system model, since we do
not assume any timing guarantees about the delivery of operations from one
replica to another. We simply assume that replicas re-send any lost messages
when the network recovers, so the effect of a network interruption is equivalent
to a very long delay in the network. Since all operations work with only the
local replica state, users never have to wait for synchronous network
communication to complete, and so the algorithm works just fine when
collaborators are offline.

> The motivation of this paper closely relates to the CAP theorem, which is
> about consistency, availability and partition tolerance. It might be good if
> the authors could have a brief discussion about what kind of consistency
> model the proposed algorithm and semantics could achieve (causal
> consistency?), and what aspects are sacrificed to achieve such consistency?

We do not believe that the CAP theorem is a useful tool for reasoning about
distributed systems; see https://arxiv.org/abs/1509.05393 for a more detailed
argument.

The consistency model achieved by our algorithm is known as *strong eventual
consistency*, an aspect we have noted in Section 1.2. It is based on reliable
causal broadcast, making it closely related to observable causal consistency,
which has been shown to be the strongest possible consistency model that is
"available" in the CAP sense. See Attiya, Ellen, and Morrison: Limitations of
Highly-Available Eventually-Consistent Data Stores, PODC 2015 (cited in Section
2.1).

> More explanation is needed for why the operations and semantics defined in
> this work are more efficient than the prior work that treats a document as
> a string of characters, and what extra benefits the proposed semantics bring
> us. 

As noted before, efficiency is not a goal of this paper. We are modelling the
semantics of data structure (arbitrarily nested lists and maps) that has not
previously been implemented as a CRDT. This data structure is not equivalent to
a string of characters. Although a JSON document can be represented as a string
of characters (representing lists with square brackets, maps with curly braces,
etc.), concurrent edits of this string would very quickly lead to a document
that is no longer valid JSON (e.g. mismatched brackets). Since our datatype
explicitly maintains the tree structure of the data, it ensures that the data is
always valid JSON.

> **Please explain how this manuscript advances this field of research and/or
> contributes something new to the literature.**
>
> This paper proposes a conflict-free replicated datatype (CRDT) based on JSON,
> which can facilitate automatic conflict resolution when concurrent
> modifications are made to replicas on multiple devices that may be offline or
> suffer from poor network connectivity. Since the prior studies only focus on
> CRDTs with flat structures such as lists, maps and registers, the authors
> design an algorithm and formal semantics for the JSON data structure which
> supports arbitrarily nested data structures. In addition, the authors employ
> the Lamport timestamps to obtain a total ordering of concurrent modifications
> for peer-to-peer collaboration, whereas most existing collaboration systems
> rely on a single server to decide on a total ordering of operations which
> might become the single point of failure. The authors also prove the
> convergence of the document state when their proposed algorithm and semantics
> are applied.
>
> **Please rate the manuscript. Please explain your choice.**
>
> Fair


Reviewer 3
----------

> **Recommendation: Author Should Prepare A Minor Revision**
> 
> This paper presents a CRDT for JSON. The solution includes as basic elements:
> lists, maps and registers. It allows a list (or map) to contain maps, lists and
> registers. A JSON document can be either a list, map or register. The paper
> presents the formal semantics of the data type and a proof that the proposed
> solution converges.
> 
> I found the work interesting, as it addresses a data type that can be useful for
> a number of applications. Although the work is somehow incremental, as most of
> the ideas used have been proposed before, it applies these ideas to design a new
> and complex data type. When compared with the solution that exists in Riak
> [23,24], this work further includes the support of lists (using the existing RGA
> algorithm). The work also contributes with the formal specification of the data
> type.
> 
> My main problem with the paper is that although it is mostly well writte, it
> does not do a good job in presenting the design options of the CRDT being
> proposed, with only a few examples in sec. 3. Even if the design options are the
> same as used in literature, they should be clearly presented, so that someone
> can understand what is the final state of the data type in the presence of
> concurrent updates.

We have elaborated further on the design options in Section 3, and explained the
rationale behind our choices. We have also included two new examples (Figures
4 and 5) that further illustrate issues that occur when concurrently editing
nested data structures.

> Instead of requiring the reader to dig into the formal
> specification, the paper must informally explain what happens when there are: 
> 
> * concurrent updates of a register (this one is explained in the paper);
> * two concurrent operations in the same list;
> * two concurrent operations in the same map;
> * a delete of an element and an update in a child of the element.

All of these are already explained in the paper (Figures 1, 3, 2, and
2 respectively). We have expanded the explanation to the maximum we could fit in
the page limit, and added a new example of concurrent operations in the same
list (Figure 4).

> As such, I think this work should be accepted only after being revised to
> include this informal discussion. In general, the authors should consider always
> providing an intuition of what they are doing before resorting to the formal
> presentation.

We hope that our expanded informal explanation will now provide readers with
a good intuition before delving into the formal details.

> Other comments:
> 
> The language API for accessing lists, with cursors, feels a bit strange. Why not
> having something like list.insert(position, elem) and/or
> list.insertAfter(elem, new elem)?

The cursors are an important part of making the concurrent semantics work:
referring to a list element by position is unstable, because an insertion or
deletion changes the meaning of all subsequent positions. However, we have found
a way of expressing list access expressions in terms of indexes, rather than an
iterator, without affecting the underlying semantics. In the revised version of
the paper, the API is list.idx(index).insertAfter(newElem). We hope this will be
easier to follow.

> I found the example of figure 7 confusing - it seems that the authors are trying
> to introduce the internal representation of the data. If so, they should present
> it clearly, saying how a list/map is stored, how ids are generated.

We have removed this example, because it was more confusing than helpful, and
instead expanded the informal explanations in Section 3.

> Although the related work section is mostly complete, there are a few important
> references missing related to reconciliation in file systems (which also have an
> hierarchical structure and address one of the key problems also being addressed
> in this paper — how to handle the deletion of an element and an update in
> a child of the element):
> 
> S. Balasubramaniam and Benjamin C. Pierce. 1998. What is a file synchronizer?.
> In Proceedings of the 4th annual ACM/IEEE international conference on Mobile
> computing and networking (MobiCom '98), William P. Osborne and Dhawal Moghe
> (Eds.). ACM, New York, NY, USA, 98-108. 
> 
> Norman Ramsey and El″od Csirmaz. 2001. An algebraic approach to file
> synchronization. SIGSOFT Softw. Eng. Notes 26, 5 (September 2001), 175-185. 

Thank you for the references. We have added them to the related work section.

> Nitpicks
> 
> * p2, line 33, col 2: “they can only safely make progress if a majority of
>   participants are online and reachable.”
> 
>   To be precise, you want to say a “quorum of participants” and not a majority,
>   as there are quorum systems where a quorum does not require a majority.

Ok, updated the text as suggested.

> * p2, line 51, col 2: “The JSON datatype described in this paper is a kind of
>   CRDT.”
>   
>   Kind of CRDT does not seem very technical. Is it a CRDT or not?

It is a CRDT (here, "a kind of" was intended in the sense of "an instance of",
not "similar to"). Changed the wording to simply say that it is a CRDT.

> * p3, line 50, col 1: The discussion on Bayou is unfair. First, Bayou only use
>   serial ordering for deciding the final order of updates, but replicas can
>   observe the result of operations tentatively. In a sense, this is not much
>   different from what happens with the proposal in this paper in which until
>   receiving all concurrent updates the definite order in a list cannot be
>   established (only relative order). Second, the roll back mechanism is used for
>   supporting functionalities not supported in the proposed approach — e.g. only
>   adding an element to a list if some condition on the list holds. The authors
>   should acknowledge that these problems appear from supporting additional
>   functionality.

We acknowledge that Bayou can be used to implement functionality that requires
serializability and that cannot be expressed using CRDTs (for example, a global
uniqueness constraint). We have rewritten the description to make clear that
Bayou has this advantage, and that Bayou and CRDTs occupy different points
within the space of trade-offs between expressivity and coordination.

> * Example of figure 3 is strange from a semantics perspective - everyone know
>   that a shopping list is not really a shopping list, but a shopping set (or
>   a shopping map to be more precise)

We beg to differ. Both authors have the habit of writing their shopping lists in
a particular order, reflecting the location of the various items within the
aisles of the supermarket, so that a linear scan of the shopping list
corresponds to an optimal path through the supermarket. If the reviewer still
finds the example too contrived, we suggest thinking of it as a to-do list
instead (which is commonly ordered by priority).

> * p. 8, line 27: must define what a causal dependency is before-hand.

Done.

> **Please explain how this manuscript advances this field of research and/or
> contributes something new to the literature.**
>
> This paper presents a CRDT for JSON. This work addresses a data type that can
> be useful for a number of applications. Although the work is somehow
> incremental, as most of the ideas used have been proposed before, it applies
> these ideas to design a new and complex data type. When compared with the
> solution that exists in Riak [23,24], this work further includes the support
> of lists (using the existing RGA algorithm). The work also contributes with
> the formal specification of the data type.
>
> **Please rate the manuscript. Please explain your choice.**
>
> Excellent
