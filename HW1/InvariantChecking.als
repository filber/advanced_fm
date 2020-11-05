open Library

pred libraryInvariant[l : Library] {
    // Each user can check out at most MAX_CHECKOUT
    all u : l.users | #checkedOut[l, u] <= MAX_CHECKOUT
}

fun checkedOut[l : Library, user : Person] : set Copy {
    { b : l.books |
        let r = l.records[b] | r.lastuser = user and r.status = Out
    }
}

fun MAX_CHECKOUT : Int { 3 }

// Initial States
some sig Init in Library {} {
    all b : books | let r = records[b] |
        one r and // exactly one record per book
        no r.lastuser and // without last user
        r.status = In // no book checked out
}

assert checkoutInvariantPreserved {
    all si : Init | libraryInvariant[si] // base case
    all l, l' : Library, u : Person, c : Copy | // inductive case
        libraryInvariant[l] and checkout[l,l',u,c] implies libraryInvariant[l']
}

check checkoutInvariantPreserved for 4
