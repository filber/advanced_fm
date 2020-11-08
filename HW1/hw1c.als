// Homework #1: Modeling and Analysis with Alloy
// Part 3: Refinement
// Author : Da Li
// Andrew ID : dal2

module hw1c

open common
open hw1a
open hw1b

// maps the state of a distributed social network to an abstract one
fun abs [c : DistributedSocialNetwork ] : SocialNetwork {
    { s : SocialNetwork | s.friends = c.friends and s.posts = c.servers.posts}
}

// assertion checks that initial states in the concrete machine are also initial states in the abstract machine
assert InitRefinement {
    all c : DistributedSocialNetwork, s : SocialNetwork | 
        c in InitDSN and s=abs[c] implies s in InitSN
}
check InitRefinement for 10

// representation invariant
pred repInvariant[n:DistributedSocialNetwork] {
    invariantConc[n]
}

// assertion checks that the concrete version of the add operation (addPostConc) refines the abstract one (addPost)
assert AddRefinement {
    all n, n' : DistributedSocialNetwork, s,s' : SocialNetwork, u : User, p : Post |
        (repInvariant[n] and
        addPostConc[n, n', u, p] and
        s = abs[n] and s' = abs[n']) implies 
            addPost[s,s',u,p]
}
check AddRefinement for 10

// assertion checks that the concrete version of the remove operation (removePostConc) refines the abstract one (removePost)
assert RemoveRefinement {
    all n, n' : DistributedSocialNetwork, s,s' : SocialNetwork, u : User, p : Post |
        (repInvariant[n] and
        removePostConc[n, n', u, p] and
        s = abs[n] and s' = abs[n']) implies 
            removePost[s,s',u,p]
}
check RemoveRefinement for 10
