sig RoomNum{}

sig Hotel {
    // record of who’s staying at each room
    occupants : RoomNum lone -> Guest,
}

sig KeyCard { opens : RoomNum }

sig Guest {
    keys : set KeyCard
}

sig Room {
    num : RoomNum,
    // guests who have entered this room
    entered : set Guest
}

pred invariant[h : Hotel] {
    // only the current occupants can enter room
    all room:Room| room.entered in h.occupants[room.num]
}

run {
//    all h : Hotel | invariant[h]
   some h:Hotel, r:Room| invariant[h] and some h.occupants and some r.entered
}
