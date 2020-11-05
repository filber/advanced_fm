abstract sig FSObject{}

sig File extends FSObject{}

sig Directory extends FSObject {
contains : set FSObject
}

one sig Root in Directory{}

pred invariant[o:FSObject]{
 o not in o.^contains
  //o in Root.^contains
  o!=Root implies o in Root.^contains
}
run {
all o:FSObject|invariant[o]
   
}
