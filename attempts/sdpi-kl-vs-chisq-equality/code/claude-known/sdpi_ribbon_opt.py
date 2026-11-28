import numpy as np
from scipy.optimize import minimize
Q=np.array([.25,.25,.5]); W=np.array([[.45,.15,.4],[.15,.45,.4],[.2,.2,.6]]); P=np.diag(Q)@W
def kl(p,q):
    m=p>1e-15; return np.sum(p[m]*np.log(p[m]/q[m]))
def viol(R,p,q):
    R=R.reshape(3,3); return kl(R.sum(1),Q)/p+(1-1/q)*kl(R.sum(0),Q)-kl(R.ravel(),P.ravel())
def opt(p,q):
    best=(-1,None)
    rng=np.random.default_rng(0)
    for t in range(60):
        z0=rng.normal(size=9)*2
        f=lambda z: -viol(np.exp(z)/np.exp(z).sum(),p,q)
        r=minimize(f,z0,method='Nelder-Mead',options={'maxiter':20000,'xatol':1e-10,'fatol':1e-13})
        r=minimize(f,r.x,method='BFGS')
        if -r.fun>best[0]: best=(-r.fun,np.exp(r.x)/np.exp(r.x).sum())
    return best
for p in [1.05,1.1,1.2,1.27,1.4,1.6,2.0,3.0]:
    q=1+(p-1)/0.09
    v,R=opt(p,q)
    print(p,q,v,np.round(R.reshape(3,3),4).tolist())
