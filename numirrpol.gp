/*
 * Implementation of the formula for the number of monic irreducible polynomials over a finite field:
 * http://dxdy.ru/post7034.html#7034 (derived and posted to Russian forum by Max Alekseyev in 2006)
 * Recently the same formula was published in:
 * Arnaud Bodin "Number of irreducible polynomials in several variables over finite fields". 
 * Amer. Math. Monthly, 115 (2008), 653-660. http://arxiv.org/abs/0706.0157
 *
 * ver. 1.1 (c) 2006,24 by Max Alekseyev
 */


\\ Count the monic irreducible polynomials in n variables over GF(q) of degree <=u.
\\ Return a vector of size u with the j-th component equal to the number of such polynomials of degree j.
{ numirrpol(q,n,u) =
  glob_f = vector(u);
  glob_f[1] = q*(q^n - 1) / (q-1);
  for(d=2,u,
    glob_s = 0; Scomp(d,d-1,1);
    glob_f[d] = q^numcomp(d-1,n+1)*(q^numcomp(d,n)-1)/(q-1) - glob_s;
  );
  return(glob_f);
}


\\ number of compositions of n into t nonnegative parts
{ numcomp(n,t) = binomial(n+t-1,n) }


{ Scomp(m,k,p) = 
  if(k<1, return);
  if(k==1, 
    glob_s += numcomp(m,glob_f[1])*p,
    for(i=0,m\k,Scomp(m-i*k,k-1,p*numcomp(i,glob_f[k])))
  )
}


