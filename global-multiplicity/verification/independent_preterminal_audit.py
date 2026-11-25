from math import prod
import sympy as S
from functools import cache

s,z,k,u = S.symbols('s z k u')

def Q(txt):
    return tuple(map(S.Rational,txt.split()))

pairs=[
  ["1 2 3 1 3 1 2 2 2","16/29 29/8 9/4 4/3 481/232 3/2 8/9 3 16/9"],
  ["2 1 1 3 4 2 4 2 1 1 2","63/41 82/63 5/6 24/5 3 7306/2583 7/2 6/5 5/4 2 3/4"],
  ["3 4 4 4 3 2 4 1 2","44/17 51/11 10/3 24/5 332/187 11/3 3 6/5 2"],
]

def continuant(diag, edges):
    previous, previous2 = [S.S.One], []
    for j,d in enumerate(diag):
        current=[d*x+y for x,y in zip(previous+[0],[0]+previous)]
        if j:
            for i,x in enumerate(previous2):
                current[i]-=edges[j-1]*x
        previous2,previous=previous,current
    return previous

@cache
def system(n):
    af=S.symbols('a1:'+str(n))
    br=S.symbols('b1:'+str(n))
    h=S.symbols('h')
    diagonal=[a+b+(h if j==n-2 else 0) for j,(a,b) in enumerate(zip((*af,0),(0,*br)))]
    edges=[a*b for a,b in zip(af,br)]
    D=continuant(diagonal,edges)
    W=continuant(diagonal[3:],edges[3:])
    H=continuant(diagonal[:-1],edges[:-1])
    F=S.Matrix([*D[:-1],*W[:-1],af[0]*af[1], prod(af)])
    var=(*af,*br,h)
    J=F.jacobian(var)
    return S.lambdify(var, [list(F),list(J),H], modules='math',cse=True,docstring_limit=0)

def P(coeff):
    return S.Poly.from_list(list(reversed(coeff)),s)

def solve_poly(D,W,p):
    n=D.degree()
    inv=S.invert(W,D)
    mult=[S.rem(inv*P(v),D).as_expr() for v in ([p,0,1],[0,1])]
    formal=S.Poly(k*mult[0]+u*mult[1],s)
    coeff=S.solve([formal.nth(n-1)-1,formal.nth(n-2)-D.nth(n-1)+z],(k,u))
    H=S.Poly(formal.as_expr().subs(coeff),s)
    # H/D = 1/s - z/s^2 + v/s^3 + ... and r=H(0)/D(0).
    r=S.expand(H.nth(0)/D.nth(0))
    v=S.expand(H.nth(n-3)-D.nth(n-2)+z*D.nth(n-1))
    return H,r,v

for raw in pairs:
    vectors=[Q(t) for t in raw]
    n=(len(vectors[0])+1)//2
    pr=system(n)
    out=[]
    assert all(t>0 for row in vectors for t in row)
    print('n =',n, flush=True)
    for t in vectors:
        f,J,hh=pr(*t)
        out.append(f)
        D,W,H=P(f[:n]+[1]),P(f[n:-2]+[1]),P(hh)
        jac=S.Matrix(len(t),len(t),J)
        print(' determinant =',jac.det(method='domain-ge'),flush=True)
        p,q=f[-2:]
        HH,r,v=solve_poly(D,W,p)
        g=q/D.nth(0)
        xi=t[-2]
        vi=S.expand(v.subs(z,xi))
        assert (HH.as_expr().subs(z,xi)-H.as_expr()).expand()==0
        assert r.subs(z,xi)-1/xi==g
        assert t[-1]==(vi/xi**2-1)/g
    assert out[0]==out[1]
    print('  D,W,p,q =',D.as_expr(),W.as_expr(), p,q)
    print('  remainder, resultant, gcd =',D.rem(W).as_expr(),D.resultant(W),D.gcd(W).as_expr())
    assert D.gcd(W).is_one
    a,b,c,d=r.coeff(z),r.subs(z,0),v.coeff(z),v.subs(z,0)
    levels=S.factor((g+1/z-r)*z)
    gx=b+c/d if d!=0 else None
    print('  r(z),v(z),g,quadratic =',r,v,g,levels)
    print('  criterion residual, candidate exceptional q =',c-d*(g-b),None if gx is None else gx*D.nth(0))
    print('  b_last, h =',[(t[-2],t[-1]) for t in vectors])
    x,y=(t[-2] for t in vectors)
    assert a*x*y==-1 and (c-d*(g-b)==0)==(vectors[0][-1]==vectors[1][-1])
