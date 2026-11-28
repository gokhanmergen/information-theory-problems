import sympy as sp, pickle, itertools, numpy as np, sys
from scipy.optimize import linprog
x,t=sp.symbols('x t')
G=pickle.load(open('G.pkl','rb'))
sign=int(sys.argv[1])  # +1 : x in [0,1], -1: x in [-1,0]
X=sp.Symbol('X')  # X = sign*x >=0
Gs=sp.expand(G.subs(x,sign*X))
DX,DT=7,5
Ks=[sp.Rational(k,100) for k in range(20,60,4)]
bases=[('X2',X**2),('T2',t**2),('XT',X*t)]+[(f'sq{k}',(X-k*t)**2) for k in Ks]
dict_=[]
for name,b in bases:
  bx=sp.degree(b,X); bt=sp.degree(b,t)
  for a in range(DX+1):
    for bb in range(DX+1-a):
      for c in range(DT+1):
        for d in range(DT+1-c):
          p=b*X**a*(1-X)**bb*t**c*(1-t)**d
          if sp.degree(p,X)<=DX and sp.degree(p,t)<=DT:
            dict_.append(((name,a,bb,c,d),sp.expand(p)))
print(len(dict_))
monos=set()
polys=[]
for k,p in dict_:
  P=sp.Poly(p,X,t); polys.append(P.as_dict()); monos|=set(P.as_dict().keys())
Gd=sp.Poly(Gs,X,t).as_dict(); monos|=set(Gd.keys())
monos=sorted(monos); idx={m:i for i,m in enumerate(monos)}
A=np.zeros((len(monos),len(dict_)))
for j,d in enumerate(polys):
  for m,cf in d.items(): A[idx[m],j]=float(cf)
b=np.zeros(len(monos))
for m,cf in Gd.items(): b[idx[m]]=float(cf)
res=linprog(np.ones(len(dict_)),A_eq=A,b_eq=b,bounds=(0,None),method='highs')
print(res.status,res.message)
if res.status==0:
  sol=res.x; nz=[(dict_[j][0],sol[j]) for j in range(len(sol)) if sol[j]>1e-12]
  print(len(nz))
  for k,v in nz: print(k,v)
  pickle.dump(([dict_[j] for j in range(len(sol)) if sol[j]>1e-12]),open(f'cert{sign}.pkl','wb'))
