"""Independent exact checks for the proposed positive multiplicity theorem. Python 3, stdlib."""
from fractions import Fraction as Q
from itertools import product
from math import prod

# Polynomials in ascending order.
def trim(v):
    v = list(v)
    while v and v[-1] == 0:
        v.pop()
    return v

def add(a,b,scale=1):
    return trim([(a[i] if i<len(a) else 0) + scale*(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])

def mul(a,b):
    r=[0]*(len(a)+len(b))
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r[i+j]+=x*y
    return trim(r)

def divide(a,b):
    r=trim(a)
    quotient=[0]*max(0,len(r)-len(b)+1)
    while len(r)>=len(b):
        k=len(r)-len(b)
        quotient[k]=Q(r[-1],b[-1])
        r=add(r,[0]*k+b,-quotient[k])
    return quotient,r

def inverse_mod(a,mod):
    f,g=mod,a
    u,v=[],[1]
    while g:
        q,r=divide(f,g)
        f,g=g,r
        u,v=v,add(u,mul(q,v),-1)
    assert len(f)==1
    return [Q(x,f[0]) for x in u]

def continuant(d,beta):
    before,previous=[],[1]
    for i,x in enumerate(d):
        current=mul([x,1],previous)
        if i:
            current=add(current,before,-beta[i-1])
        before,previous=previous,current
    return previous

def observations(x,ell):
    n=(len(x)+1)//2
    a,b,h=x[:n-1],x[n-1:-1],x[-1]
    d=[aa+bb+h*(i==ell-1) for i,(aa,bb) in enumerate(zip([*a,0],[0,*b]))]
    beta=[u*v for u,v in zip(a,b)]
    D,W=continuant(d,beta),continuant(d[3:],beta[3:])
    return D[:-1]+W[:-1]+[a[0]*a[1],prod(a)]

def physical_moments(d,beta,m):
    # A diagonal similarity permits superdiagonal 1 and subdiagonal beta.
    v=[0]*(len(d)-1)+[1]
    moments=[]
    for _ in range(2*m):
        moments.append(v[-1])
        v=[d[i]*v[i]+(v[i+1] if i+1<len(d) else 0)+(beta[i-1]*v[i-1] if i else 0)
           for i in range(len(d))]
    return moments

def gram_minimum(minus,moments,m):
    gram=[[moments[i+j+1] for j in range(m)] for i in range(m)]
    den=eliminate(gram)
    assert den>0
    block=[[minus,*moments[:m]]]+[[moments[i],*gram[i]] for i in range(m)]
    return Q(eliminate(block),den)

def eliminate(A):
    A=[list(map(Q,row)) for row in A]
    det=1
    for i in range(len(A)):
        pivot=next((k for k in range(i,len(A)) if A[k][i]),None)
        if pivot is None: return 0
        if pivot!=i:
            A[pivot],A[i]=A[i],A[pivot]
            det=-det
        det*=A[i][i]
        for k in range(i+1,len(A)):
            t=A[k][i]/A[i][i]
            for j in range(i,len(A[k])):
                A[k][j]-=t*A[i][j]
    return det

def jacobian(x,ell,measure=observations):
    base=measure(x,ell)
    columns=[]
    for j in range(len(x)):
        y=list(x)
        y[j]+=1
        columns.append([b-a for a,b in zip(base,measure(y,ell))])
    return eliminate(columns)

def seed(x,y,ell):
    assert x!=y and min(*x,*y)>0
    assert observations(x,ell)==observations(y,ell)
    dets=jacobian(x,ell),jacobian(y,ell)
    assert all(dets)
    print('seed', (len(x)+1)//2,ell,'determinants',*dets)
    return dets

def spectral(D,W,t,p,m):
    # Solve W H = K E mod D and normalize H to be monic of degree n-1.
    E=[p,t,1]
    _,H=divide(mul(inverse_mod(W,D),E),D)
    assert len(H)==len(D)-1
    H=[Q(z,H[-1]) for z in H]
    n=len(D)-1
    # Euclidean Jacobi reconstruction and Sylvester's criterion for T>0.
    curr,prev=D,H
    d,beta=[],[]
    while len(curr)>1:
        assert curr[0]>0
        q,rem=divide(curr,prev)
        assert len(q)==2 and q[1]==1
        d.insert(0,q[0])
        if len(prev)==1: break
        assert len(rem)+1==len(prev) and rem[-1]<0
        beta.insert(0,-rem[-1])
        curr,prev=prev,[Q(z,rem[-1]) for z in rem]
    assert continuant(d[3:],beta[3:])==W
    assert continuant(d[:2],beta[:1])==E
    minus=Q(H[0],D[0])
    phi=gram_minimum(minus,physical_moments(d,beta,m),m)
    correction=Q(continuant(d[n-m:-1],beta[n-m:-1])[0],continuant(d[n-m:],beta[n-m:])[0]) if m else 0
    assert phi==minus-correction
    return phi

def check_lifts():
    D=[24,150,206,96,17,1]
    W=[8,7,1]
    ts=[Q(6),Q(61,10),Q(25,4)]
    def triple(D,W,m): return [spectral(D,W,t,2,m) for t in ts]
    assert triple(D,W,1)==[Q(1,4),Q(4,15),Q(1,4)]
    for moves in ['A','B','AB','BAB']:
        d,w,m=D,W,1
        used=[]
        for move in moves:
            n=len(d)-1
            eps=min(divide(mul(inverse_mod(w,d),[2,t,1]),d)[1][-1] for t in ts)/10**5
            for exponent in range(2,31):
                L=Q(10**exponent)
                delta=L/2 if move=='A' else L**(7-2*n)/eps
                if L-delta<=d[-2]: continue  # trace bounds every existing node
                dp,wp=mul([L,1],d),mul([L-delta,1],w)
                try: a,b,c=triple(dp,wp,m+(move=='B'))
                except AssertionError: continue
                if b>max(a,c): break
            else: raise AssertionError((moves,move))
            used.append(str(L))
            d,w,m=dp,wp,m+(move=='B')
        print('lifts',moves,'(n,ell)',(len(d)-1,len(d)-1-m),'L',','.join(used))

def physical_energy_checks():
    count=0
    for n in range(4,9):
        a=[Q(i+3,i+1) for i in range(n-1)]
        b=[Q(2*i+3,i+2) for i in range(n-1)]
        h=Q(n+1,3)
        beta=[u*v for u,v in zip(a,b)]
        for ell in range(1,n+1):
            d=[aa+bb+h*(i==ell-1) for i,(aa,bb) in enumerate(zip([*a,0],[0,*b]))]
            D=continuant(d,beta)[0]
            H=continuant(d[:-1],beta[:-1])[0]
            m=n-ell
            assert gram_minimum(H/D,physical_moments(d,beta,m),m)==prod(a)/D
            count+=1
    print('physical q/D(0) equals the Gram minimum:',count,'models')

def previous_coordinate_checks():
    def values(x,ell):
        d0,d1,d2,d3,w,p,q=observations(x,ell)
        return [s**4+d3*s**3+d2*s**2+d1*s+d0 for s in range(4)]+[p,p*w,q]
    x=(1,2,3,4,5,6,7)
    expected=(-311040,-198720,-103680,-51840)
    for ell,target in enumerate(expected,1):
        # At four chambers each component is affine in each separate rate.
        assert jacobian(x,ell,values)==target
        assert -12*x[0]*x[1]*jacobian(x,ell)==target
    print('previous four-chamber coordinates:',*expected,'(factor -12p)')

def symmetric_family_checks():
    for n in range(4,13):
        T=Q(n)
        t=[j-Q(n+1,2) for j in range(1,n+1)]
        nodes=[T+x for x in t]
        tail=[T+j-Q(n,2) for j in range(2,n-1)]
        den=[prod(x-y for y in tail)*prod(x-y for y in nodes if y!=x) for x in nodes]
        v=-Q((n-3)*(n-1),4)
        def weights(u):
            return [(x*x+u*x+v)/d for x,d in zip(t,den)]
        lo,mid,hi=map(weights,(-1,0,1))
        assert all(x>=0 for x in lo+hi) and all(x>0 for x in mid)
        assert [i+1 for i,x in enumerate(lo) if x==0]==[2,n]
        assert [i+1 for i,x in enumerate(hi) if x==0]==[1,n-1]
        S=sum(mid)
        assert S==sum(lo)==sum(hi)
        c0=sum(1/d for d in den)
        assert c0<0
        moment_inv=sum(w/x for w,x in zip(mid,nodes))/S
        assert T*moment_inv>1
        assert c0*(1-T*moment_inv)/S!=0
    print('symmetric family: endpoint zeros, normalization and transverse derivatives for n=4..12')

if __name__=='__main__':
    one=(1,1,1,1,1,1,2)
    assert seed(one,(1,1,1,1,2,1,1),2)==(-1,2)
    A=(1,2,3,1,3,1,2,2,2)
    B=tuple(map(Q,('16/29','29/8','9/4','4/3','481/232','3/2','8/9','3','16/9')))
    assert seed(A,B,4)==(3456,-4698)
    # Independently find a rational witness for leak 1.
    seen={}
    for x in product(range(1,4),repeat=7):
        y=tuple(observations(x,1))
        if y in seen and jacobian(x,1) and jacobian(seen[y],1):
            seed(seen[y],x,1)
            print('leak 1 vectors',seen[y],x)
            break
        seen[y]=x
    else: raise AssertionError('missing seed')
    previous_coordinate_checks()
    physical_energy_checks()
    symmetric_family_checks()
    check_lifts()
