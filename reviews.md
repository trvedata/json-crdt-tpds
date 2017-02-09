Reviewer 1
==========

> **Recommendation: Author Should Prepare A Minor Revision**
> 
> The article is very well written and easy to follow. The formal rules might
> have been simpler in the format of a mathematical pseudo-code algorithm with
> some auxiliary functions, but it is a stylistic choice and the rules do serve
> the purpose of removing ambiguity and supporting the proofs. The work is also
> well grounded on the state of the art, so I would only draw attention to a very
> recent related work that is also related to sequences and RGA: Hagit Attiya,
> Sebastian Burckhardt, Alexey Gotsman, Adam Morrison, Hongseok Yang, and Marek
> Zawirski, Specification and complexity of collaborative text editing,
> PODC'16.  
> 
> As the authors acknowledge, the treatment of causality is based on the
> frameworks of causal contexts defined for delta state CRDTs, and state based
> CRDTs in general, and embodied in current Riak maps. The approach the authors
> propose for JSON looks equally robust in terms of the provided semantics, but
> uses more metadata. For instance tombstones are kept here, and are probably
> needed for RGA like lists, and thus they cannot be so compactly encoded in
> causal contexts.  It would be interesting to better clarify if this limitation
> is mandatory given the JSON structure or if it can be improved in the future.
> 
> In section 4, it might be timely to briefly explain "pres" and not defer for
> later.  
> 
> The JSON tree can branch either by a mapT or listT, and (MV)register forms
> terminal nodes. I failed to detect in the rules what happens if one node adds a
> map under a new key and another adds a list under the same new key. When they
> merge, do we get the two types of branch there? Is there a deterministic choice
> there? Does the new key reflect the type, and in fact lead to different
> keys ...?
> 
> The system uses lamport timestamps for the operation pair (c,p). Is it really
> needed to have the counter grow to the max of all received counters? Since
> causality is tracked by the "deps" field it looks that the counters would only
> need to grow locally and not jump forward to match received higher counters.
> Notice that the replica id would be enough to disambiguate concurrent list
> insertions at the same location.  
> 
> The system is formalized as transmitting the whole grow-only queue of operations
> all the time. This works, in theory, but can be even worse than full state based
> CRDTs, since state based does some compression already. Maybe a section on
> implementation guidelines could help bridge the gap from the formal model
> (designed for proofs) and what would be a more practical implementation.
> 
> 
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


Reviewer 2
==========

> **Recommendation: Author Should Prepare A Major Revision For A Second Review**
> 
> Paper strength
> 
> 1. This paper is informative to readers who are not familiar with CRDTs. It is
>    written clearly and the examples are easy to follow.
> 2. It provides a good use case of applying the well-known Lamport timestamps for
>    conflict resolution.
> 
> Paper weakness
> 
> 1. About the novelty of this paper: 
> 
>    I truly appreciate the authors' efforts in designing the algorithm and
>    semantics for enabling automatic conflict resolution for the JSON datatype.
>    However, in terms of conflict handling, the authors simply adopt Lamport
>    timestamps to obtain the total ordering of operations and compare their
>    approach against "last write wins." In my opinion this approach may work
>    regardless of the underlying datatypes. It is not clear to me how the
>    algorithm and semantics designed in the first part of this paper (Sec. 3)
>    relate to the second part (Sec. 4). Also the proofs for the convergence of
>    document states seem quite general, which do not rely on the data structures
>    (flat structure vs. arbitrarily nested structure).
> 
>    As a tentative suggestion, maybe the authors could add a paragraph or two
>    somewhere in Sec. 4 to further highlight and clarify the difficulty/challenge
>    of applying existing techniques (e.g., Lamport timestamps) to their proposed
>    datatype for conflict handling, and how their semantics help with addressing
>    the problem. 
> 
> 2. About the completeness of this paper: 
> 
>    It is a pity that the main content of this paper stops at Sec. 4 with only
>    the theorem for state convergence. Since the authors mention that they have
>    an experimental collaborative text editor (although I couldn't find it in the
>    supplement material) which implements the proposed CRDT, maybe they could
>    find a way to visualize a sequence of operations from different collaborators
>    and show some interesting scenarios, e.g., (i) normal valid execution without
>    network failure, (ii) execution with one of the collaborators suffering from
>    temporary network failure. 
> 
> 3. The motivation of this paper closely relates to the CAP theorem, which is
>    about consistency, availability and partition tolerance. It might be good if
>    the authors could have a brief discussion about what kind of consistency
>    model the proposed algorithm and semantics could achieve (causal
>    consistency?), and what aspects are sacrificed to achieve such consistency?
> 
> 4. More explanation is needed for why the operations and semantics defined in
>    this work are more efficient than the prior work that treats a document as
>    a string of characters, and what extra benefits the proposed semantics bring
>    us. 
>
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
==========

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
> concurrent updates.  Instead of requiring the reader to dig into the formal
> specification, the paper must informally explain what happens when there are: 
> 
> * concurrent updates of a register (this one is explained in the paper);
> * two concurrent operations in the same list;
> * two concurrent operations in the same map;
> * a delete of an element and an update in a child of the element.
> 
> As such, I think this work should be accepted only after being revised to
> include this informal discussion. In general, the authors should consider always
> providing an intuition of what they are doing before resorting to the formal
> presentation.
> 
> Other comments:
> 
> The language API for accessing lists, with cursors, feels a bit strange. Why not
> having something like list.insert(position, elem) and/or
> list.insertAfter(elem, new elem)?
> 
> I found the example of figure 7 confusing - it seems that the authors are trying
> to introduce the internal representation of the data. If so, they should present
> it clearly, saying how a list/map is stored, how ids are generated.
> 
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
> 
> Nitpicks
> 
> * p2, line 33, col 2: “they can only safely make progress if a majority of
>   participants are online and reachable.”
> 
>   To be precise, you want to say a “quorum of participants” and not a majority,
>   as there are quorum systems where a quorum does not require a majority.
> 
> * p2, line 51, col 2: “The JSON datatype described in this paper is a kind of
>   CRDT.”
>   
>   Kind of CRDT does not seem very technical. Is it a CRDT or not?
> 
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
> 
> * Example of figure 3 is strange from a semantics perspective - everyone know
>   that a shopping list is not really a shopping list, but a shopping set (or
>   a shopping map to be more precise)
> 
> * p. 8, line 27: must define what a causal dependency is before-hand.
>
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
