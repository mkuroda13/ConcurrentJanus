procedure main (){
  int p[100]
  int max
  int maxrt
  int nextlock
  int plock
  max += 100
  maxrt += 10
  {
    local int k = 2
    call sieve(k,p,nextlock,max,maxrt)
    delocal int k = 2
  }
}

procedure sieve(int k, int p, int nextlock,
    int max, int maxrt, int plock){
  if maxrt >= k then {
    if p[k] = 0 then {
      par {
        local int nk = k+1
        P nextlock
        call sieve(nk,p,nextlock,max,maxrt,plock)
        delocal int nk = k+1
      }, {
        local int n = k
        from n = k do {
          n += k
        } loop {
          V plock
          {
            local int t = p[n] * (maxrt - 1)
            p[n] += t
            delocal int t = p[n]*(maxrt-1)/maxrt
          }
          p[n] += k
          P plock
          if n = (maxrt/k+1)*k then {
            V nextlock
          } else {} fi n = (maxrt/k+1)*k
        } until n >= max
        delocal int n = ((max-1)/k)*k+k
      } rap
    } else {
      local int nk = k+1
      call sieve(nk,p,nextlock,max,maxrt,plock)
      delocal int nk = k+1
    } fi p[k] = 0
  } else {} fi maxrt >= k
}
