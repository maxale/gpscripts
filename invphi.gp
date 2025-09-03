/*
** invphi.gp ver. 2.5 (c) 2005,2025 by Max Alekseyev
** based on the paper: 
** M. A. Alekseyev, Computing the Inverses, their Power Sums, and Extrema for Euler's Totient and Other Multiplicative Functions. Journal of Integer Sequences 19 (2016), Article 16.5.2
** https://cs.uwaterloo.ca/journals/JIS/VOL19/Alekseyev/alek5.html

** invphi(n, U=oo)              computes all solutions x <= U to the equation eulerphi(x) = n.
** invphiNum(n)                 equivalent to but faster than #invphi(n).
** invphiMin(n, k=1)            equivalent to but faster than vecextract(invphi(n),"1..k").
** invphiMax(n)                 equivalent to but faster than vecmax(invphi(n)).

** invsigma(n, k=1, U=oo)       computes all solutions x <= U to the equation sigma(x,k) = n. If k is omitted, it's assumed that k=1.
** invsigmaNum(n, k)            equivalent to but faster than #invsigma(n,k).
** invsigmaMin(n, k)            equivalent to but faster than vecmin(invsigma(n,k)).
** invsigmaMax(n, k)            equivalent to but faster than vecmax(invsigma(n,k)).

** invphitau(n, m)              computes all solutions x to the system { eulerphi(x) = n, numdiv(x) = m }.
** invphitauNum(n, m)           equivalent to but faster than #invphitau(n,m).
** invphitauMin(n, m)           equivalent to but faster than vecmin(invphitau(n,m)).
** invphitauMax(n, m)           equivalent to but faster than vecmax(invphitau(n,m)).

** invpsi(n, U=oo)              computes all solutions x <= U to the equation dedekind_psi(x) = n.
** invpsiNum(n)                 equivalent to but faster than #invpsi(n).
** invpsiMin(n, k=1)            equivalent to but faster than vecextract(invpsi(n),"1..k").
** invpsiMax(n)                 equivalent to but faster than vecmax(invpsi(n)).



Brief history:
* 2.5:  added support for Dedekind's psi
* 2.44: INV_ODD_ONLY retired in favor of INV_COPRIME_TO
* 2.43: improvements in cook_phitau()
*/


{ invphi(N,U=+oo) = dynamicPreimage(N,cook_phi(N),U); }
{ invphiNum(N) = dynamicNum(N,cook_phi(N)); }
{ invphiMax(N) = dynamicMax(N,cook_phi(N)); }
{ invphiMin(N,K=1) = dynamicMinK(N,cook_phi(N),K); }


{ invpsi(N,U=+oo) = dynamicPreimage(N,cook_psi(N),U); }
{ invpsiNum(N) = dynamicNum(N,cook_psi(N)); }
{ invpsiMax(N) = dynamicMax(N,cook_psi(N)); }
{ invpsiMin(N,K=1) = dynamicMinK(N,cook_psi(N),K); }


{ invsigma(N,k=1,U=+oo) = 
  if(N==1, [1], dynamicPreimage(N,cook_sigma(N,k,U),U); );
}

{ invsigmaNum(N,k=1) = 
  if(N==1, 1, dynamicNum(N,cook_sigma(N,k)) );
}

{ invsigmaMin(N,k=1) = 
  if(N==1, 1, dynamicMin(N,cook_sigma(N,k)) );
}


{ invsigmaMax(N,k=1) = 
  if(N==1, 1, dynamicMax(N,cook_sigma(N,k)) );
}

{ invsigmaDiv(N,k=1,U=+oo) = 
  if(N==1, [[1]], dynamicPreimage(N,cook_sigma(N,k,U),U,1) );
}


\\ backward compatibility
{ numinvphi(N) = invphiNum(N); }
{ numinvsigma(N,k=1) = invsigmaNum(N,k); }

INV_SQUARE_FREE = 0;
INV_COPRIME_TO = 1;
ADD_PRIMES = 0;         \\ turn on to allow easy factorization of inv*() results

{ cook_phi(N, SP=[], f_p=-1) = my(L,p,l);
    \\ SP: if nonempty, provides a list of primes for solution basis. By default, such primes are computed.
    \\ f_p = f(p) - p; that is, -1 when f Euler's phi, +1 when f is Dedekind's psi.

  L=Map();

  if(!SP,
      SP = List();
      fordiv(N,n,
          p = n - f_p;
          if( !ispseudoprime(p), next );
          if(INV_COPRIME_TO%p==0, next);
          if(ADD_PRIMES, addprimes(p));
          listput(SP,p);
      );
  );
  
  foreach(SP,p,
      l = [];
      mapisdefined(L,p,&l);
      my(k = valuation(N,p)+1);
      if(INV_SQUARE_FREE, k=min(k,1));
      mapput(~L, p, concat(l, vector(k,i,[(p+f_p)*p^(i-1),p^i])) );
  );

  if(#L,Mat(L)[,2],[]);
}

{ cook_psi(N, SP=[]) = cook_phi(N,SP,1); }

{ cook_sigma_collect_primes_nfroots(k,d) =
    if(d==1,return([]));
    my( P = List() );
    for(m=1,logint(d*(2^k-1)+1,2)\k-1,
        \\ print1(Strchr(13),"m: ",m,"   ");
        foreach(nfroots(,sum(i=0,m,'x^(i*k))-d),p,
            if(ispseudoprime(p), listput(~P,[p,m,d]) );
        );
    );
    P;
}

{ cook_sigma_collect_primes_factor(k,d) = my(P,q,t);
    P = List();
    foreach(factorint(d-1)[,1], p,
      q = d*(p^k-1)+1;
      t = valuation(q,p);                       \\ we have t/k = m+1
      if( t<=k || t%k || q!=p^t, next );
      listput(~P,[p,t\k-1]);
    );
    P;
}

export(cook_sigma_collect_primes_nfroots, cook_sigma_collect_primes_factor);

cook_sigma_collect_primes = [cook_sigma_collect_primes_nfroots, cook_sigma_collect_primes_factor];

{ cook_sigma(N,k,B=+oo) = my(L, p, q, t, l); 

  if(k==0,                      \\ k=0 makes sense only for Min function
    return( apply(p->concat(apply(d->if(d==1||d>logint(B,p)+1,[],[[d,p^(d-1)]]),divisors(N))), primes(bigomega(N)) ) );
  );

  L = Map(); 

  /*
  fordiv(N,d,
    if(d==1,next);
    iferr(parapply(f->error(f(k,d)), cook_sigma_collect_primes), E, q=component(E,1)[1], err_name(E)="e_USER");
    foreach(q,p,
          if(INV_COPRIME_TO%p[1]==0, next);
          if(ADD_PRIMES, addprimes(p[1]));
          l = [];
          mapisdefined(L,p[1],&l);
          mapput(~L, p[1], concat(l, [[d,p[1]^p[2]]] ) );
    );
  );
  */

  my(F = factor(N));
  parforvec(e=apply(z->[0,z],F[,2]),
    cook_sigma_collect_primes_nfroots(k,factorback(F[,1],e)),
    q,
    foreach(q,p,
          if(INV_COPRIME_TO%p[1]==0, next);
          if(ADD_PRIMES, addprimes(p[1]));
          l = [];
          mapisdefined(L,p[1],&l);
          mapput(~L, p[1], concat(l, [[p[3],p[1]^p[2]]] ) );
    );
  );

  if(#L,Mat(L)[,2],[]);
}



/*
{ cook_sigma(N,k,B=+oo) = my(L, p, q, t, l); 

  if(k==0,                      \\ k=0 makes sense only for Min function
    return( apply(p->concat(apply(d->if(d==1||d>logint(B,p)+1,[],[[d,p^(d-1)]]),divisors(N))), primes(bigomega(N)) ) );
  );

  L = Map(); 

  fordiv(N,d,
    if(d==1,next);
    \\ foreach(factorint(d-1)[,1], p,

    \\ we have ((2^k)^(m+1) - 1)/(2^k-1) <= 1 + ... + p^(m*k) = d
    for(m=1,logint(d*(2^k-1)+1,2)\k-1,foreach(nfroots(,sum(i=0,m,x^(i*k))-d),p,
      if(!ispseudoprime(p),next);

      if(INV_COPRIME_TO%p==0, next);

      q = d*(p^k-1)+1;
      t = valuation(q,p);                       \\ we have t/k = m+1
      if( t<=k || t%k || q!=p^t, next );

      \\ we have d = sigma_k(p^(t/k - 1))

      if(ADD_PRIMES, addprimes(p));

      l = [];
      mapisdefined(L,p,&l);
      mapput(~L, p, concat(l, [[d,p^(t/k - 1)]] ) );
    );
  \\ );
  ));

  if(#L,Mat(L)[,2],[]);
}
*/


{ cook_phitau(N,M,coprime_to=1) = my(L,p,l);
  L = Map();

  \\ quick test for solubility
  if(M>1,
    if(if(N==1,0,vecmax(factor(N)[,2])) < vecmax(factor(M)[,1])-2, return([]) );
  );

  fordiv(N,n,
      p = n+1;
      if( coprime_to%p==0 || !ispseudoprime(p), next );

      if(ADD_PRIMES, addprimes(p));

      l = [];
      mapisdefined(L,p,&l);
      l = concat(l, select(x->(M%x[3])==0, vector(valuation(N,p)+1,i,[n*p^(i-1),p^i,i+1]) ));
      if(l, mapput(~L, p, l); );
  );

  if(#L,Mat(L)[,2],[]);
}


{ dynamicNum(N,L) = my(D,r,t);
  \\ dynamic programming; L is destroyed
  D = Set(divisors(N));
  r = vector(#D);
  r[1] = 1;
  for(i=1,#L,
    t = r;       \\ stands for 1 in 1 + terms of L 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n,
        t[setsearch(D,n*L[i][j][1])] += r[setsearch(D,n)];
      );
    );
    r = t;
  );
  r[#D];
}


{ dynamicPreimage(N,L,U=+oo,Full=0) = my(l, D, r, t); 
  \\ dynamic programming
  D = Set(divisors(N));
  r = vector(#D,i,[]);
  r[1] = [1];
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n,
        l = setsearch(D,n*L[i][j][1]);
        t[l] = setunion(t[l],select(x->x<=U,r[setsearch(D,n)]*L[i][j][2]));
      );
    );
    r = t;
  );
  if(Full,r,r[#D]);
}


{ dynamicMin(N,L) = my(l, D, r, t, p); 
  \\ dynamic programming
  D = Set(divisors(N));
  r = vector(#D,i,oo);
  r[1] = 1;
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n,
        l = setsearch(D,n*L[i][j][1]);
        p = r[setsearch(D,n)];
        if( p < oo,
            p *= L[i][j][2];
        );
        t[l] = min(t[l],p);
      );
    );
    r = t;
  );
  r[#D];
}


\\ computes up to K minimum values
{ dynamicMinK(N,L,K=1) = my(l, D, r, t, p); 
  \\ dynamic programming
  D = Set(divisors(N));
  r = vector(#D,i,[]);
  r[1] = [1];
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n,
        l = setsearch(D,n*L[i][j][1]);
        t[l] = setunion(t[l], r[setsearch(D,n)] * L[i][j][2]);
        if(#t[l] > K,
            t[l] = vecextract(t[l],concat("1..",K))
        );
      );
    );
    r = t;
  );
  r[#D];
}


{ dynamicMax(N,L) = my(l, D, r, t); 
  \\ dynamic programming
  D = Set(divisors(N));
  r = vector(#D,i,0);
  r[1] = 1;      \\  FIXME  ?
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n,
        l = setsearch(D,n*L[i][j][1]);
        t[l] = max(t[l],r[setsearch(D,n)]*L[i][j][2]);
      );
    );
    r = t;
  );
  r[#D];
}


\\ M is the number of divisors
{ invphitau_dyn(N,M,coprime_to=1) = my(L,p, l, k, DN, DM, r, t); 
  L = cook_phitau(N,M,coprime_to);
  if(!L, return( if(N==1 && M==1,[1],[]) ) );

  \\ print("N,M: ",[N,M]);
  \\ print("#L: ",#L," ",vecsum(apply(x->#x,L)));

  \\ dynamic programming
  DN = Set(divisors(N));
  DM = Set(divisors(M));
  r = matrix(#DN,#DM,i,j,[]);
  r[1,1] = [1];
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    foreach(L[i],Lt,
      fordiv(N/Lt[1],n, 
        l = setsearch(DN,n*Lt[1]);
        fordiv(M/Lt[3],m,
          k = setsearch(DM,m*Lt[3]);
          t[l,k] = setunion(t[l,k],r[setsearch(DN,n),setsearch(DM,m)]*Lt[2]);
        );
      );
    );
    r = t;
  );
  r[#DN,#DM];   \\ * R
}

{ invphitau(N,M,coprime_to=1) = my(p,F,res);
  if(M==1, return(if(N==1,[1],[])));
  p = vecmax(factor(M)[,1]);
  if(p==2, return(invphitau_dyn(N,M,coprime_to)) );
  F = factor(N);
  res = Set();
  fordiv(M\p,d,
    my(q=d*p);
    for(i=1,#F~,
        if(F[i,2]>=q-2 && N%(F[i,1]-1)==0 && coprime_to%F[i,1],
            res = setunion(res, invphitau(N\(F[i,1]-1)\F[i,1]^(q-2),M\q,coprime_to*F[i,1]) * F[i,1]^(q-1) );
        );
    );
  );
  res;
}

{ invphitauMin(N,M) = my(L, p, l, D, r, t); 
  L = cook_phitau(N,M);
  if(!L, return( if(N==1 && M==1,[1],[]) ) );

  \\ dynamic programming
  D = Set(divisors(N));
  r = matrix(#D,M,i,j,oo);
  r[1,1] = 1;
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n, 
        l = setsearch(D,n*L[i][j][1]);
        fordiv(M/L[i][j][3],m,
            p = r[setsearch(D,n),m];
            if( p<oo,
              p *= L[i][j][2];
            );
            t[l,m*L[i][j][3]] = min( t[l,m*L[i][j][3]], p );
        );
      );
    );
    r = t;
  );
  r[#D,M];
}

{ invphitauMax(N,M) = my(L, l, D, r, t); 
  L = cook_phitau(N,M);
  if(!L, return( if(N==1 && M==1,[1],[]) ) );

  \\ dynamic programming
  D = Set(divisors(N));
  r = matrix(#D,M,i,j,0);
  r[1,1] = 1;
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n, 
        l = setsearch(D,n*L[i][j][1]);
        fordiv(M/L[i][j][3],m,
            t[l,m*L[i][j][3]] = max( t[l,m*L[i][j][3]], r[setsearch(D,n),m]*L[i][j][2] );
        );
      );
    );
    r = t;
  );
  r[#D,M];
}

{ invphitauNum(N,M) = my(L, l, D, r, t); 
  L = cook_phitau(N,M);
  if(!L, return( if(N==1 && M==1,[1],[]) ) );

  \\ dynamic programming
  D = Set(divisors(N));
  r = matrix(#D,M,i,j,0);
  r[1,1] = 1;
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n, 
        l = setsearch(D,n*L[i][j][1]);
        fordiv(M/L[i][j][3],m,
            t[l,m*L[i][j][3]] += r[setsearch(D,n),m]*L[i][j][2];
        );
      );
    );
    r = t;
  );
  r[#D,M];
}



{ A055488(n) = invsigmaMin(n!); }
{ A055489(n) = invsigmaMax(n!); }
{ A055486(n) = invsigmaNum(n!); }

{ A055487(n) = invphiMin(n!); }
{ A165774(n) = invphiMax(n!); }
{ A055506(n) = invphiNum(n!); }

{ A153076(n) = invphiMin(prod(i=1,n,prime(i))); }
{ A153077(n) = invphiMax(prod(i=1,n,prime(i))); }
{ A153078(n) = invphiNum(prod(i=1,n,prime(i))); }

{ A110077(n) = invsigmaMin(10^n); }
{ A110076(n) = invsigmaMax(10^n); }
{ A110078(n) = invsigmaNum(10^n); }

{ A072075(n) = invphiMin(10^n); }
{ A072076(n) = invphiMax(10^n); }
{ A072074(n) = invphiNum(10^n); }

\\ A061300 Least number whose number of divisors is n!.
{ A061300(n) = my(f,B,L,N);
  if(n<=1,return(1));
  N = n!;
  f = factor(N);
  f = concat(vector(matsize(f)[1],i,vector(f[i,2],j,f[i,1])));
  B = prod(i=1,#f,prime(i)^(f[#f+1-i]-1));          \\ = A037019(n!), a bound for A061300(n)
  L = apply(i->concat(apply(d->if(d==1||d>logint(B,vecprod(primes(i)))+1,[],[[d,prime(i)^(d-1)]]),divisors(N))), vector(bigomega(N),i,i) );
  my(r = dynamicMin(N,L) );
  if(r!=B, print("======> ",B) );
  r;
}
