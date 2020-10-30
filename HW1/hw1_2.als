// Homework #1: Modeling and Analysis with Alloy
// Part 2: Distributed Social Network
// Author : Da Li
// Andrew ID : dal2

module hw1_2
open hw1_1

sig DistributedSocialNetwork {
    // Servers where posts are stored
    servers : set Server , 
    // Friendships between users
    friends : User -> User
}
sig Server {
    // Each server stores some subset of posts by different users
    posts : User -> Post ,
    // The maximum number of posts that can be stored on this server
    capacity : Int
}

pred postOp[n, n' : DistributedSocialNetwork] {
    n'.friends = n.friends
}

pred promote[n, n' : DistributedSocialNetwork, s, s' : Server] {
    // describes how local and global states are related
    // Pre-Condition
    s in n.servers
    // Post-Condition
    n'.servers = (n.servers - s ) + s'
}

// add a new post - local change predicate
pred addPostLocal[s, s' : Server , u : User , p : Post ] {
    // Pre-Condition
    #s.posts < s.capacity
    p not in s.posts[User]

    // Post-Condition
    s'.capacity = s.capacity
    s'.posts = s.posts + u->p
}

// add a post - local change predicate
pred removePostLocal[s, s' : Server , u : User , p : Post ] {
    // Pre-Condition
    u->p in s.posts
    // Post-Condition
    s'.capacity = s.capacity
    s'.posts = s.posts - u->p
}

// add a new post ‘‘p’’ to those belonging to user ‘‘u’’
pred addPostConc [n, n' : DistributedSocialNetwork , u : User , p : Post ] {
    postOp[n,n']
    p not in n.servers.posts[User]
    some s : n.servers, s' : n'.servers |
        promote[n, n', s, s'] and
        addPostLocal[s, s', u, p]
}

// remove an existing post ‘‘p’’ from user ‘‘u’’
pred removePostConc [n, n' : DistributedSocialNetwork , u : User , p : Post ] {
    postOp[n,n']
    u->p in n.servers.posts
    some s : n.servers, s' : n'.servers |
        promote[n, n', s, s'] and
        removePostLocal[s, s', u, p]
}

// predicate defines what it means for a social network to be in a valid state
pred invariantConc [n : DistributedSocialNetwork ] {
    // 1. friendship is symmetric
    let friendship = n.friends | ~friendship in n.friends
    // 2. a user cannot be his or her own friend
    no u : User| u->u in n.friends
    // 3. a post cannot be owned by more than one user
    all p : Post | lone n.servers.posts.p
    // 4.Each post is stored on exactly one of the servers
    all s1,s2 : n.servers | s1 != s2 implies no (s1.posts[User] & s2.posts[User])
    // 5.The number of posts in each server can't exceed its capacity
    all s : n.servers | #s.posts <= s.capacity
}

run {
    some n : DistributedSocialNetwork | 
        invariantConc[n] and
        some n.friends and
        #n.servers > 1 and
        some n.servers.posts
} for 4 but exactly 1 DistributedSocialNetwork


// assertion checks addPostConc preserves the the invariant
assert AddConcPreservesInv {
    all n, n' : DistributedSocialNetwork, u : User, p : Post |
        invariantConc[n] and addPostConc[n, n', u, p] implies
            invariantConc[n']
}
check AddConcPreservesInv

// assertion checks removePostConc preserves the the invariant
assert RemoveConcPreservesInv {
    all n, n' : DistributedSocialNetwork, u : User, p : Post |
        invariantConc[n] and removePostConc[n, n', u, p] implies
            invariantConc[n']
}
check RemoveConcPreservesInv
