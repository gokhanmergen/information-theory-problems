import sympy as sp, pickle, textwrap
x,t,X=sp.symbols('x t X')
G=pickle.load(open('G.pkl','rb'))
def basestr(name):
  if name=='X2': return '(X ^ 2)','(sq_nonneg X)'
  if name=='T2': return '(t ^ 2)','(sq_nonneg t)'
  if name=='XT': return '(X * t)','(mul_nonneg hX ht)'
  k=sp.Rational(name[2:])
  return f'((X - {k} * t) ^ 2)', '(sq_nonneg _)'
gs=sp.sstr(G).replace('**','^')
toks=gs.replace(' - ',' -~').replace(' + ',' +~').split('~')
lines=[];cur='  '
for tk in toks:
  if len(cur)+len(tk)+1>98: lines.append(cur.rstrip()); cur='    '+tk
  else: cur=(cur+' '+tk) if cur.strip() else cur+tk
lines.append(cur.rstrip())
out=['/-- The polynomial `(5 + x)³ · E / 2` to which the global inequality reduces. -/\nnoncomputable def Gpoly (x t : ℝ) : ℝ :=\n'+'\n'.join(lines)+'\n']
for sign,nm,arg in [(1,'pos','X'),(-1,'neg','(-X)')]:
  cert=pickle.load(open(f'cert{sign}.pkl','rb')); lam=pickle.load(open(f'lam{sign}.pkl','rb'))
  terms=[]
  for l,((name,a,b,c,d),p) in zip(lam,cert):
    B,pf=basestr(name)
    terms.append(f'({sp.sstr(l)} : ℝ) *\n      box_mono X t hX hX1 ht ht1 {B} {pf} {a} {b} {c} {d}')
  doc = ('/-- `Gpoly ≥ 0` for `x ∈ [0, 1]`: an exact nonnegative combination (found by LP, checked by\n    `ring`) of `X², t², X·t, (X - κt)²` times products of `X, 1 - X, t, 1 - t`. -/\n' if sign==1 else
         '/-- `Gpoly ≥ 0` for `x ∈ [-1, 0]` (`x = -X`), certified the same way. -/\n')
  out.append(doc+f'theorem Gpoly_{nm} (X t : ℝ) (hX : 0 ≤ X) (hX1 : X ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :\n    0 ≤ Gpoly {arg} t := by\n  unfold Gpoly\n  linear_combination\n    ' + ' +\n    '.join(terms) + '\n')
open('Gthms4.lean','w').write('\n'.join(out))
