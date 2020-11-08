// Homework #1: Modeling and Analysis with Alloy
// Part 1: Simple Social Network
// Author : Da Li
// Andrew ID : dal2

module hw1a

open common

sig SocialNetwork {
    posts : User -> Post,   // The set of posts owned by each user
    friends : User -> User // Friendships between users
}

some sig InitSN in SocialNetwork {
}{
    #posts=0
    #friends=0
}

pred postOp[n, n' : SocialNetwork] {
    n'.friends = n.friends
}

// add a new post ‘‘p’’ to those belonging to user ‘‘u’’
pred addPost [n, n' : SocialNetwork , u : User , p : Post ] {
    // Pre-condition
    p not in n.posts[User]
    // Post-condition
    n'.posts = n.posts + u->p
    // Frame Condition
    postOp[n,n']
}

// remove an existing post ‘‘p’’ from user ‘‘u’’
pred removePost [n, n' : SocialNetwork , u : User , p : Post ] {
    // Pre-condition
    u->p in n.posts
    // Post-condition
    n'.posts = n.posts - u->p
    // Frame Condition
    postOp[n,n']
}

// what it means for a social network to be in a valid state
pred invariant [n : SocialNetwork ] {
    // 1. friendship is symmetric
    n.friends = ~(n.friends)
    // 2. a user cannot be his or her own friend
    no u : User| u->u in n.friends
    // 3. a post cannot be owned by more than one user
    all p : Post | lone n.posts.p
}

// assertion checks addPost preserves the the invariant
assert AddPreservesInv {
    // base case
    all sni : InitSN | invariant[sni]
    // inductive case
    all n, n' : SocialNetwork, u : User, p : Post |
        invariant[n] and addPost[n, n', u, p] implies
            invariant[n']
}
check AddPreservesInv for 5

// assertion checks removePost preserves the the invariant
assert RemovePreservesInv {
    // base case
    all sni : InitSN | invariant[sni]
    // inductive case
    all n, n' : SocialNetwork, u : User, p : Post |
        invariant[n] and removePost[n, n', u, p] implies
            invariant[n']
}
check RemovePreservesInv for 5
