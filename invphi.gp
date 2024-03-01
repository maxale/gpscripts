/*
** invphi.gp ver. 2.3 (c) 2005,2023 by Max Alekseyev
** based on the paper: 
** M. A. Alekseyev, Computing the Inverses, their Power Sums, and Extrema for Euler's Totient and Other Multiplicative Functions. Journal of Integer Sequences 19 (2016), Article 16.5.2
** https://cs.uwaterloo.ca/journals/JIS/VOL19/Alekseyev/alek5.html

** invphi(n)		computes all solutions to the equation eulerphi(x)=n with respect to x.
** invphiNum(n)		equivalent to but faster than #invphi(n).
** invphiMin(n)		equivalent to but faster than vecmin(invphi(n)).
** invphiMax(n)		equivalent to but faster than vecmax(invphi(n)).

** invsigma(n,k)	computes all solutions to the equation sigma(x,k)=n with respect to x. If k is omitted, it's assumed that k=1.
** invsigmaNum(n,k)	equivalent to but faster than #invsigma(n,k).
** invsigmaMin(n,k)	equivalent to but faster than vecmin(invsigma(n,k)).
** invsigmaMax(n,k)	equivalent to but faster than vecmax(invsigma(n,k)).

** invphitau(n,m)	computes all solutions to the system { eulerphi(x)=n, numdiv(x)=m } with respect to x.
** invphitauNum(n,m)	equivalent to but faster than #invphitau(n,m).
** invphitauMin(n,m)	equivalent to but faster than vecmin(invphitau(n,m)).
** invphitauMax(n,m)	equivalent to but faster than vecmax(invphitau(n,m)).
*/


{ invphi(N) = dynamicPreimage(N,cook_phi(N)); }

{ invphiNum(N) = dynamicNum(N,cook_phi(N)); }

{ invphiMax(N) = dynamicMax(N,cook_phi(N)); }

{ invphiMin(N) = dynamicMin(N,cook_phi(N)); }


{ invsigma(N,k=1) = 
  if(N==1, [1], dynamicPreimage(N,cook_sigma(N,k)) );
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



\\ backward compatibility
{ numinvphi(N) = invphiNum(N); }
{ numinvsigma(N,k=1) = invsigmaNum(N,k); }


{ cook_phi(N) = my(L,p,l);
  L=Map();

  fordiv(N,n,
      p = n+1;
      if( !ispseudoprime(p), next );

      l = [];
      mapisdefined(L,p,&l);
      mapput(L, p, concat(l, vector(valuation(N,p)+1,i,[(p-1)*p^(i-1),p^i])) );
  );

  if(#L,Mat(L)[,2],[]);
}

INVSIGMA_ODD_ONLY = 0;

{ cook_sigma(N,k,B=+oo) = my(L, p, q, t, l); 

  if(k==0,                      \\ k=0 makes sense only for Min function
    return( apply(p->concat(apply(d->if(d==1||d>logint(B,p)+1,[],[[d,p^(d-1)]]),divisors(N))), primes(bigomega(N)) ) );
  );

  L = Map(); 

  fordiv(N,d,
    if(d==1,next);
    foreach(factorint(d-1)[,1], p,

      if( INVSIGMA_ODD_ONLY && p==2, next );            \\ hack to report only odd solutions

      q = d*(p^k-1)+1;
      t = valuation(q,p);
      if( t<=k || t%k || q!=p^t, next );

      \\ we have d = sigma_k(p^(t/k - 1))

      l = [];
      mapisdefined(L,p,&l);
      mapput(L, p, concat(l, [[d,p^(t/k - 1)]] ) );
    );
  );

  if(#L,Mat(L)[,2],[]);
}


{ cook_phitau(N,M) = my(L,p,l);
  L = Map();

  fordiv(N,n,
      p = n+1;
      if( !ispseudoprime(p), next );

      l = [];
      mapisdefined(L,p,&l);
      mapput(L, p, concat(l, select(x->(M%x[3])==0, vector(valuation(N,p)+1,i,[n*p^(i-1),p^i,i+1]) )) );
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


{ dynamicPreimage(N,L) = my(l, D, r, t); 
  \\ dynamic programming
  D = Set(divisors(N));
  r = vector(#D,i,[]);
  r[1] = [1];
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n,
        l = setsearch(D,n*L[i][j][1]);
        t[l] = vecsort(concat(t[l],r[setsearch(D,n)]*L[i][j][2]),,8);
      );
    );
    r = t;
  );
  r[#D];
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
{ invphitau(N,M) = my(L, p, l, D, r, t); 
  L = cook_phitau(N,M);

  \\ dynamic programming
  D = Set(divisors(N));
  r = matrix(#D,M,i,j,[]);
  r[1,1] = [1];
  for(i=1,#L,
    t = r;       \\ stands for 1 in (1 + terms of L) 
    for(j=1,#(L[i]),
      fordiv(N/L[i][j][1],n, 
        l = setsearch(D,n*L[i][j][1]);
        fordiv(M/L[i][j][3],m,
          t[l,m*L[i][j][3]] = vecsort(concat(t[l,m*L[i][j][3]],r[setsearch(D,n),m]*L[i][j][2]),,8);
        );
      );
    );
    r = t;
  );
  r[#D,M];
}


{ invphitauMin(N,M) = my(L, p, l, D, r, t); 
  L = cook_phitau(N,M);

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
