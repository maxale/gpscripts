/*
** binomod.gp ver. 1.6 (c) 2007,21 by Max Alekseyev
**
** binomod(n,k,m)	computes binomial(n,k) modulo integer m
** binocoprime(n,k,m)	tests if binomial(n,k) is co-prime to integer m
** binoval(n,k,p)	valuation of binomial(n,k) with respect to prime p
**
** Notes. The input m is factored inside binocoprime(n,k,m) and that may take time for large m. 
** The functionality of binoval(n,k,p) is equivalent to valuation(binomial(n,k),p) but the former 
** does not compute binomial(n,k) explicitly and takes only O(log(n)) arithmetic operations.
**
** The implementation is based on Lucas' Theorem and its generalization given in the paper: 
** Andrew Granville "The Arithmetic Properties of Binomial Coefficients", In Proceedings of 
** the Organic Mathematics Workshop, Simon Fraser University, December 12-14, 1995.
*/

\\ binomial(n,k) mod m
{  binomod(n,k,m) = my(d,e,p,q,r,t,v,f,np,kp,rp,N,K,R,F);
   
   if(k<0 || m==1, return(Mod(0,m)) );
   if(n<0 ,return( (-1)^k*binomod(-n+k-1,k,m) ) );
   if(k>n, return(Mod(0,m)) );
   if(k==0||k==n, return(Mod(1,m)) );

   if( ispseudoprime(m),
     p = m;
     v = Map(); \\ v = vector(p);
     while(k,
       np = n%p;
       kp = k%p;
       if(kp>np,return(Mod(0,p)));
       if(kp && np-kp,
            \\ v[np]++; v[kp]--; v[np-kp]--;

         t = 0;
         mapisdefined(v,np,&t);
         mapput(v,np,t+1);

         t = 0;
         mapisdefined(v,kp,&t);
         mapput(v,kp,t-1);

         t = 0;
         mapisdefined(v,np-kp,&t);
         mapput(v,np-kp,t-1);
       );
       n\=p; k\=p;
     );
     f = r = Mod(1,p); 
     \\ for(i=2,p-1,f*=i;if(mapv[i],r*=f^v[i]) );
     for(i=2,p-1,f*=i; if(mapisdefined(v,i,&t), r*=f^t) );
     return(r);
   );

   f = factor(m);
   F = vector(matsize(f)[1]);

   for(z=1,matsize(f)[1],
     p = f[z,1];
     q = f[z,2];

     d = ceil( log(n-0.5)/log(p) );

     np = vector(d+1,i,(n\p^(i-1))%p);
     kp = vector(d+1,i,(k\p^(i-1))%p);
     rp = vector(d+1,i,((n-k)\p^(i-1))%p);

     \\ cumulative number "carries" from (i-1)-th position and on
     e = vector(d+1); 
     for(i=1,d+1,
       e[i]=np[i]<kp[i]+if(i>1,e[i-1]);
     );
     forstep(i=d,1,-1, e[i]+=e[i+1]);

     if( e[1] >= q, 
       F[z] = Mod(0,p^q); 
       next;
     );
     q -= e[1];

     N = vector(d+1,i,(n\p^(i-1))%p^q);
     K = vector(d+1,i,(k\p^(i-1))%p^q);
     R = vector(d+1,i,((n-k)\p^(i-1))%p^q);

     v = p^e[1] * prod(j=1,d+1, factorialmodp1(N[j],p,q) / factorialmodp1(K[j],p,q) / factorialmodp1(R[j],p,q) );

     if( (p>2 || q<3) && q<=#e, v *= (-1)^e[q] );
     F[z] = Mod(v,p^f[z,2]);
   );
   chinese(F);
}


\\ is binomial(n,k) co-prime to m
{  binocoprime(n,k,m) = my(p,np,kp,f);
   if(k<0,return(0));
   if(n<0,n=-n+k-1);
   if(k>n,return(0));

   foreach(factorint(m)[,1],p,
     np=n; kp=min(k,n-k);
     while(kp,
       if((kp%p)>(np%p),return(0));
       np\=p; kp\=p;
     );
   );
   1;
}


\\ valuation( binomial(n,k), p ), p is prime
{  binoval(n,k,p) = my(m=[n,k,n-k],r=0);
   while(m,
     m \= p;
     r += m[1] - m[2] - m[3];
   );
   r;
}


\\ factorial modulo prime p
{  factorialmodp(n,p) = my(r);
   if( n<=1, return(1+O(p)));

   r = ((-1)^(n\p) + O(p)) * factorialmodp(n\p,p) * p^(n\p);
   for(i=2,n%p, r*=i );
   r;
}


\\ factorial_p modulo prime p^k
{  factorialmodp1(n,p,k) = my(r);
   if( n<=1, return(1+O(p^k)));

   r = (-1)^(n\p^k) + O(p^k);
   for(i=2,n%p^k,if(i%p,r*=i));
   r;
}

