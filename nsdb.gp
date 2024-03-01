/*
 * nsdb.gp ver. 1.2 (c) 2008 by Max Alekseyev
 *
 * Computes the number of self-dual and self-dual normal bases of GF(q^m) over GF(q)
 * from the formulae given in the paper:
 *
 * Dieter Jungnickel, Alfred J. Menezes, Scott A. Vanstone 
 * "On the Number of Self-Dual Bases of GF(q^m) Over GF(q)"
 * Proceedings of the American Mathematical Society (1990), 109 (1), 23-29. 
 * http://dx.doi.org/10.2307/2048357 
 * Also available at: http://www.math.uwaterloo.ca/~ajmenezes/publications/sdb.pdf
 *
 */


\\ number of distinct self-dual bases of GF(q^m) over GF(q) where q is a power of prime
{ sd(m,q) = 
  if( q%2 && !(m%2), return(0) );
  (q%2 + 1) * prod(i=1,m-1, q^i - (i+1)%2) / m!
}


\\ number of distinct self-dual normal bases of GF(q^m) over GF(q) where q is prime
{ sdn(m,q) = local(F,f,g,s,c,d);

  if( q==2 && m%4==0, return(0) );

  \\ case q|m
  if( !(m%q),
    s = m\q;
    return( q^((q-1)*(s+(s*(q+1))%2)/2-1) * sdn(s,q) );
  );

  \\ case (m,q)==1
  F = factormod( (x^m - 1)/(x - 1), q );
  c = d = [];
  for(i=1,matsize(F)[1],
    f = lift(F[i,1]);
    g = polrecip(f);
    if( f==g, 
      c = concat( c, vector(F[i,2],j,poldegree(f)/2) );
    );
    if( lex(Vec(f),Vec(g))==1, 
      d = concat( d, vector(F[i,2],j,poldegree(f)) );
    );
  );
  2^(q%2) * prod(i=1,#c, q^c[i] + 1) * prod(j=1,#d, q^d[j] - 1) / m
}
