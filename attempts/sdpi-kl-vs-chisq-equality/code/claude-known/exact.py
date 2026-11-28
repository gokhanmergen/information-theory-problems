import sympy as sp, pickle
x,t,X=sp.symbols('x t X')
G=pickle.load(open('G.pkl','rb'))
for sign in [1,-1]:
  cert=pickle.load(open(f'cert{sign}.pkl','rb'))
  Gs=sp.expand(G.subs(x,sign*X))
  lam=sp.symbols(f'l0:{len(cert)}')
  expr=sp.expand(Gs-sum(l*p for l,(k,p) in zip(lam,cert)))
  eqs=sp.Poly(expr,X,t).coeffs()
  sol=sp.solve(eqs,lam,dict=True)
  print(sign,len(sol), sol[0] if sol else None)
  if sol:
    s=sol[0]; free=[l for l in lam if l not in s]
    print('free',free)
    vals=[s.get(l,l) for l in lam]
    pickle.dump(vals,open(f'lam{sign}.pkl','wb'))
    print([float(v) if v.is_number else v for v in vals])
