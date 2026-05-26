**Theorem**: For all positive integers n,
1 + 2 + ... + n = n(n+1)/2

**Proof**:

Base Case (n=1):
Left side: 1
Right side: 1(1+1)/2 = 1
Equal.

Inductive Step:
Assume true for k: 1 + 2 + ... + k = k(k+1)/2

For k+1:
1 + 2 + ... + k + (k+1) = k(k+1)/2 + (k+1)
                          = [k(k+1) + 2(k+1)] / 2
                          = (k+1)(k+2)/2

Thus, true for all n by induction.