import sympy as sp
x,t=sp.symbols('x t')
R=sp.Rational
s=(1+x)/2; q=5+x; rho=5*(1+x)/q
inner = R(9,100)*(t/2+t**2/12+t**3/30+t**4/56) - R(45,1000)*rho*t - R(675,1000000)*rho**3*t**2 - R(15,100)*(t**3/480+t**4/3584+R(2,135)*t**5/256)
G = q**3*(R(9,100)*x**2/2 - x**2/50 - x**4/7200) + q**3*s*inner
G=sp.expand(sp.simplify(G))
print(G)
import numpy as np
f=sp.lambdify((x,t),G,'numpy')
X,T=np.meshgrid(np.linspace(-1,1,2001),np.linspace(0,1,1001))
v=f(X,T); m=(X**2+T**2)>1e-12
r=np.where(m,v/np.where(m,X**2+T**2,1),1); i=np.unravel_index(np.argmin(r),r.shape)
print(v.min(), r.min(), X[i], T[i])
import pickle; pickle.dump(G,open('G.pkl','wb'))
