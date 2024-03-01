\\ number of hamiltonian paths
{ nhp(A) = my(d,n,r,M); 
  n=matsize(A)[1]; 
  /*
  r=0; 
  for(s=1,2^n-1,
    M=vecextract(A,s,s)^(n-1);
    d=matsize(M)[1];
    r+=(-1)^(n-d)*sum(i=1,d,sum(j=1,d,M[i,j]));
  );
  r;
  */
  parsum(s=1,2^n-1,
    my( M = vecextract(A,s,s)^(n-1), d = matsize(M)[1] );
    (-1)^(n-d) * sum(i=1,d,sum(j=1,d,M[i,j]));
  );
}

\\ number of simple paths of length k
{ NSP(A,k) = my(d,n,r,M); 
  n=matsize(A)[1]; 
  /*
  r=0; 
  for(s=1,2^n-1,
    M=vecextract(A,s,s)^k;
    d=matsize(M)[1];
    r+=(-1)^(k+1-d)*binomial(n-d,k+1-d)*sum(i=1,d,sum(j=1,d,M[i,j]));
  );
  r;
  */
  parsum(s=1,2^n-1,
    my( M = vecextract(A,s,s)^k, d = matsize(M)[1] );
    (-1)^(k+1-d) * binomial(n-d,k+1-d) * sum(i=1,d,sum(j=1,d,M[i,j]));
  );
}



\\ number of hamiltonian cycles
{ nhc(A) = my(d,n,r,M); 
  n = matsize(A)[1]; 
  /*
  r=0; 
  forstep(s=1,2^n-1,2,
    M=vecextract(A,s,s)^n;
    d=matsize(M)[1];
    r+=(-1)^(n-d)*M[1,1];
  );
  r;
  */
  parsum(t=0,2^(n-1)-1, 
    my( M = vecextract(A,2*t+1,2*t+1)^n );
    (-1)^(n-matsize(M)[1])*M[1,1]
  );
}



\\ number of simple cycles of length k
{ NSC(A) = my(d,n,r,M); 
  n=matsize(A)[1]; 
  r=0; 
  forstep(s=1,2^n-1,2,
    M=vecextract(A,s,s)^k;
    d=matsize(M)[1];
    r+=(-1)^(k-d)*binomial(n-d,k-d)*trace(M);
  );
  r/k;
}


{ nhcTEST(A) = my(d,n,r,M); 
  n=matsize(A)[1]; 
  r=0; 
  for(s=1,2^n-1,
    M=vecextract(A,s,s)^n;
    d=matsize(M)[1];
    r+=(-1)^(n-d)*trace(M);
  );
  r/n;
}



{ nhc2(A) = my(n);
  n=matsize(A)[1]; 
  parsum(i=0,2^(n-1)-1,
    my(M);
    M=vecextract(A,2*i+1,2*i+1)^n;
    (-1)^(n-matsize(M)[1])*M[1,1];
  );
}



\\ simplify SYMMETRIC adjacency matrix (i.e., undirected graph)
{ SimpAdj(A) =
  V = vector(matsize(A)[1],i,[i]);

while(1,
  n = matsize(A)[1];
  for(i=1,n,
    if( !V[i], next );
    s = sum(j=1,n,A[i,j]);

    if( s==1,
      t = select(x->A[i,x],vector(n,j,j))[1];
      V[i] = concat(V[i],V[t]);
      V[t] = [];
      A[i,] = A[t,];

      A[,t] = vectorv(n,j,0);
      A[t,] = vector(n,j,0);
    );
    if( s==2,
      t = select(x->A[i,x],vector(n,j,j));
      if( vecmax([ #V[t[1]],#V[t[2]],#V[i] ]) == 1,
        V[i] = concat([ V[t[1]],V[i],V[t[2]] ]);
        V[t[1]] = [];
        V[t[2]] = [];
 
        A[i,] = A[t[2],];
        A[,i] = A[,t[1]];

        A[t[1],] = vector(n,j,0);
        A[t[2],] = vector(n,j,0);
        A[,t[1]] = vectorv(n,j,0);
        A[,t[2]] = vectorv(n,j,0);
      );
    );

    s = sum(j=1,n,A[j,i]);
    if( s==1,
      t = select(x->A[x,i],vector(n,j,j))[1];
      V[i] = concat(V[t],V[i]);
      V[t] = [];
      
      A[,i] = A[,t];

      A[,t] = vectorv(n,j,0);
      A[t,] = vector(n,j,0);
    );
  );
  
  t = sum(i=1,n, if( V[i], 2^(i-1)) );
  if( t==2^n-1, break );

  A = vecextract(A,t,t);
  V = vecextract(V,t);
);

  [A,V];
}


{ find_hp(A) = my(n);
  n=matsize(A)[1]; 
  for(i=1,n,for(j=1,i-1,
    if( A[i,j],
      A[i,j] = A[j,i] = 0;
      if(nhp(A)==0,
	A[i,j] = A[j,i] = 1;
      );
    );
  ));
  A;
}
