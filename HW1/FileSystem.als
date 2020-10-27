sig Path {}
sig File {}
sig FileSystem {
map : Path -> lone File
}

pred addFile[s, s' : FileSystem, p : Path, f : File] {
p->f not in s.map
s'.map = s.map + p -> f
}


pred deleteFile[s, s' : FileSystem, p : Path] {
// Precondition
// Some file must already exist at path “p”
some s.map[p]
// Postcondition
// “p” no longer maps to any file
no s'.map[p]

// Other files do not change
all p' : Path - p | s'.map[p'] = s.map[p']
}

run deleteFile for 3

assert AddThenDeleteIsUndo {
    all s, s', s'' : FileSystem, p : Path, f : File |
        addFile[s, s', p, f] and
        deleteFile[s', s'', p] implies
            s.map = s''.map
}
check AddThenDeleteIsUndo for 10
