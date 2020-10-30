// Homework #1: Modeling and Analysis with Alloy
// Part 3: Refinement
// Author : Da Li
// Andrew ID : dal2

module hw1_3
open hw1_1
open hw1_2

// maps the state of a distributed social network to an abstract one
fun abs [c : DistributedSocialNetwork ] : SocialNetwork {
    { s : SocialNetwork | s.friends = c.friends and s.posts = c.servers.posts}
}

// assertion checks that initial states in the concrete machine are also initial states in the abstract machine
assert InitRefinement {
    all c : DistributedSocialNetwork,s:SocialNetwork | 
        s=abs[c] implies s.friends = c.friends and s.posts = c.servers.posts
}
check InitRefinement for 10

// assertion checks that the concrete version of the add operation (addPostConc) refines the abstract one (addPost)
assert AddRefinement {
    all n, n' : DistributedSocialNetwork, s: abs[n], s' : abs[n'], u : User, p : Post |
        addPostConc[n, n', u, p] implies addPost[s,s',u,p]
}
check AddRefinement for 10

// assertion checks that the concrete version of the remove operation (removePostConc) refines the abstract one (removePost)
assert RemoveRefinement {
    all n, n' : DistributedSocialNetwork, s: abs[n], s' : abs[n'], u : User, p : Post |
        removePostConc[n, n', u, p] implies removePost[s,s',u,p]
}
check RemoveRefinement for 10
