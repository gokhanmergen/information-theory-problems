import numpy as np
from fractions import Fraction as F
Q=np.array([.25,.25,.5]); W=np.array([[.45,.15,.4],[.15,.45,.4],[.2,.2,.6]])
def kl(p,q):
    m=p>0; return np.sum(p[m]*np.log(p[m]/q[m]))
best=0;arg=None
N=1500
for i in range(N+1):
  for j in range(N+1-i):
    P=np.array([i,j,N-i-j])/N
    d=kl(P,Q)
    if d<1e-9: continue
    r=kl(P@W,Q@W)/d
    if r>best: best=r;arg=P
print("max ratio grid",best,arg)
# near Q along eigvecs
M=np.diag(np.sqrt(Q))@W@np.diag(1/np.sqrt(Q))
print(np.linalg.eigvalsh((M+M.T)/2))
# ribbon check
P=np.diag(Q)@W
R=np.array([[1,2,2],[3,54,14],[2,12,10]])/100
p,q=1.27,4
lhs=kl(R.sum(1),P.sum(1))/p+(1-1/q)*kl(R.sum(0),P.sum(0)); rhs=kl(R.ravel(),P.ravel())
print(lhs/np.log(2),rhs/np.log(2),(lhs-rhs)/np.log(2))
# reverse channel ratio
print("PXY symmetric", np.allclose(P,P.T))
