sig Elem {}
sig Set {
// Abstract set
members : set Elem
}

// Abstract operations
pred add[s, s' : Set, e : Elem] {
s'.members = s.members + e
}

pred remove[s, s' : Set, e : Elem] {
s'.members = s.members - e
}

sig ListSet {
// Concrete set represented using a sequence
members : seq Elem
}

// Concrete remove operation
pred removeConc[ls, ls' : ListSet, e : Elem] {
    let i = ls.members.idxOf[e] |
        some i implies ls'.members = ls.members.delete[i] else ls' = ls
}
