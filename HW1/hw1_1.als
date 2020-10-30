// Homework #1: Modeling and Analysis with Alloy
// Part 1: Simple Social Network
// Author : Da Li
// Andrew ID : dal2

module hw1_1

sig SocialNetwork {
    posts : User -> Post,   // The set of posts owned by each user
    friends : User -> User // Friendships between users
}
sig User {}
sig Post {}

pred postOp[n, n' : SocialNetwork] {
    n'.friends = n.friends
}

pred addPost [n, n' : SocialNetwork , u : User , p : Post ] {
    postOp[n,n']
    // add a new post ‘‘p’’ to those belonging to user ‘‘u’’
    p not in n.posts[User]
    n'.posts = n.posts + u->p
}

pred removePost [n, n' : SocialNetwork , u : User , p : Post ] {
    postOp[n,n']
    // remove an existing post ‘‘p’’ from user ‘‘u’’
    u->p in n.posts
    n'.posts = n.posts - u->p
}

// what it means for a social network to be in a valid state
pred invariant [n : SocialNetwork ] {
    // 1. friendship is symmetric
    let friendship=n.friends | ~friendship in n.friends
    // 2. a user cannot be his or her own friend
    no u : User| u->u in n.friends
    // 3. a post cannot be owned by more than one user
    all p : Post | lone n.posts.p
}

run {
   some n, n' : SocialNetwork, u : User, p : Post |
        invariant[n] and addPost[n, n', u, p] and
            invariant[n']
} for 4 but exactly 2 SocialNetwork


// assertion checks addPost preserves the the invariant
assert AddPreservesInv {
    all n, n' : SocialNetwork, u : User, p : Post |
        invariant[n] and addPost[n, n', u, p] implies
            invariant[n']
}
check AddPreservesInv

// assertion checks removePost preserves the the invariant
assert RemovePreservesInv {
    all n, n' : SocialNetwork, u : User, p : Post |
        invariant[n] and removePost[n, n', u, p] implies
            invariant[n']
}
check RemovePreservesInv
