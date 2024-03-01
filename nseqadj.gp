/*
 * Implementation of the formula for the number of sequences, consisting of elements from
 * a number of classes, where every pair of adjacent elements are from distinct classes.
 * Based on the paper: L. Q. Eifler, K. B. Reid Jr., D. P. Roselle, 
 * "Sequences with adjacent elements unequal". Aequationes Mathematicae (1971), 6 (2-3), 256-262. 
 * http://dx.doi.org/10.1007/BF01819761
 *
 * ver. 1.1 (c) 2008,2023 by Max Alekseyev
 */


\\ For a given k-dimensional vector s, M(s) computes the number of linear sequences, consisting 
\\ of k classes of elements with s[i] elements in the i-th class, where every pair of adjacent
\\ elements are from distinct classes.
{ M(s) = my(r,J);
  r = 0;
  forvec(j=vector(#s-1,i,[1,s[i]]), 
    J = sum(i=1,#j,j[i]); 
    r += (-1)^J * prod(t=1,#j, binomial(s[t]-1,j[t]-1) / j[t]! ) * binomial(J+1,s[#s]) * J!;
  ); 
  r * (-1)^sum(i=1,#s-1,s[i])
}
