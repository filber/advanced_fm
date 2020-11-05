sig Author, Title, Subject {}
sig Book {
author : Author,
title : Title,
subjects : set Subject
}
// Copies of a book are distinguished by their IDs
sig ID {}
sig Copy {
book : Book,
id : ID
}

sig Person {}
abstract sig Status {}
one sig In, Out extends Status {}
sig Record {
// Whether the book is checked out or not
status : Status,
// The last person to check out the book
lastuser : lone Person
}

sig Library {
books : set Copy,
records : books -> Record,
users, staff : set Person
}

pred addBookCopy[l, l' : Library, book : Copy] {
bookOp[l,l']
// Precondition
// 1. This copy must not already exist in the library
book not in l.books
// 2. There should be no existing copy with the same ID
//no b : l.books | b.id = book.id
book.id not in l.books.id

// Postcondition
// why don't need this??
l'.books = l.books + book
// create a new Record
some r : Record |
    no r.lastuser and
    r.status = In and
    l'.records = l.records + book->r
}

pred bookOp[l, l' : Library] {
    l'.staff = l.staff
    l'.users = l.users
}

pred removeBookCopy[l, l' : Library, book : Copy] {
    bookOp[l, l']
    // Precondition
    book in l.books    // Postcondition
    // why don't need this??
    l'.books = l.books - book
    // Keep all records beside that of ”book”
    l'.records = (Copy - book) <: l.records
}

// query without changing states
fun booksByAuthor[l : Library, a : Author]: set Copy {
    {
        b : l.books | b.book.author = a
    }
}

pred checkout[l, l' : Library, u : Person, c : Copy] {
    // Precondition
    #{ b : l.books |
       let r = l.records[b] | r.lastuser = u and r.status = Out
    } < 3
    // Postcondition
    // Modify the existing record for “c”
    // to indicate that it has been checked out by “u”
    some r, r' : Record |
        promote[l, l', r, r', c] and
        checkoutBook[r, r', u]
}

// local changes on one part of the overall system
pred checkoutBook[r, r' : Record, u : Person] {
    // Pre-condition
    r.status = In
    // Post-condition
    r'.status = Out
    r'.lastuser = u
}

pred promote[l, l' : Library, r, r' : Record, c : Copy] {
    // describes how local and global states are related
    // Pre-Condition
    l.records[c] = r
    // Post-Condition
    // Overwrite the relation
    l'.records = l.records ++ c->r'
}


// Controlling Access
pred restrictedOp[l, l' : Library, p : Person] {
    p in l.staff
}
pred unrestrictedOp[l, l' : Library, p : Person] {
    p in l.(staff + users)
}

pred safeAddBookCopy[l, l' : Library, b : Copy, p : Person] {
    restrictedOp[l, l', p] and addBookCopy[l, l', b]
}
pred safeRemoveBookCopy[l, l' : Library, b : Copy, p : Person] {
    restrictedOp[l, l', p] and removeBookCopy[l, l', b]
}
