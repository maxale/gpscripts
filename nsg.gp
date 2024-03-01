/*
 * Implementation of the formula for the number of subgroups of an abelian group
 * from the paper G.A Miller "On the Subgroups of an Abelian Group",
 * The Annals of Mathematics, 2nd Ser., Vol. 6, No. 1 (Oct., 1904), pp. 1-6
 * http://dx.doi.org/10.2307/2007151
 *
 * ver. 1.2 (c) 2007,2018 by Max Alekseyev
 */


\\ number of subgroups of the group C_{p^a1} x C_{p^a2} x ... C_{p^ak} where 
\\ p is prime and a=[a1,a2,...,ak] with 1 <= a1 <= a2 <= ... <= ak
{ numsubgrp(p,a,b=0) = my(r=0,q,n,m,n1,m1);
  a = vecsort(a);
  if(b==0,
    forvec(c=vector(#a,i,[0,a[i]]), 
      if(c==0,next); 
      r+=numsubgrp(p,a,c), 
    1);
    return(r + 1);
  );

  \\ removing leading zeros from b
  q=1; while(q<=#b && b[q]==0,q++);
  if(q>#b,return(0));
  b = vecextract(b,2^#b-2^(q-1));

  \\ initialize q, m[], n[]
  q = #b;
  m = n = vector(b[q]);
  m1 = 1;
  n1 = 1; 
  for(i=1,b[q],
    while(i>a[m1],m1++);
    m[i] = #a - m1 + 1;
    while(i>b[n1],n1++);
    n[i] = q - n1 + 1;
  );

  prod(i=1,q, (p^(m[b[q-i+1]]-i+1) - 1) / (p^(n[b[q-i+1]]-i+1) - 1) ) * 
  p^sum(x=0,q-1, (q-x) * sum(j=if(x<1,1,b[x]),b[x+1]-1, m[j] - n[j]) );
}


{ A006116(n) = numsubgrp(2,vector(n,i,1)); }

\\ { A061034(n) = my(f=factorint(n),r); prod(i=1,#f~, r=0; forpart(q=f[i,2], r=max(r,numsubgrp(f[i,1],q))); r ); }

{ A061034(n) = my(f=factorint(n)); prod(i=1,#f~, vecmax(apply(x->numsubgrp(f[i,1],x),partitions(f[i,2]))) ); }
