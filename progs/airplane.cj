procedure main() {
    int seats
    int agent1
    int agent2
    seats += 3
    par {
        call ag1(seats,agent1)
    },{
         call ag2(seats,agent2)
    } rap
}
procedure ag1(int seats, int agent1){
    from agent1 == 0 do {
        
    } loop {
        seats -= 1
        agent1 += 1
    } until seats <= 0
}
procedure ag2(int seats, int agent2){
    from agent2 == 0 do {
        
    } loop {
        seats -= 1
        agent1 += 1
    } until seats <= 0
}