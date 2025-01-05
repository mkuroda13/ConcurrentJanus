procedure main(){
    int n
    int r
    n += 10
    call fib(n, r)
}

procedure fib(int n, int r){
    if n <= 2 then {
        r += 1
    } else {
        par {
            local int l = n - 1
            call fib(l, r)
            delocal int l = n - 1
        }, {
            local int m = n - 2
            call fib(m, r)
            delocal int m = n - 2
        } rap
    } fi n <= 2
}
