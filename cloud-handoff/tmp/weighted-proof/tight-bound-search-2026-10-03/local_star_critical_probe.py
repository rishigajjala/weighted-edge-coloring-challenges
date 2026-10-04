import mpmath as mp
mp.mp.dps=80
K=mp.mpf(4)/3

def values(a,b,du_extra=0,dv_extra=0,dx_extra=0):
 pu=mp.mpf('0.25')+mp.mpf('0.75')*(a+b+du_extra)
 pv=mp.mpf('0.25')+mp.mpf('0.75')*(a+dv_extra)
 px=mp.mpf('0.25')+mp.mpf('0.75')*(b+dx_extra)
 te=min(K*a/(pu*pv),12*a);tf=min(K*b/(pu*px),12*b)
 ze=zf=mp.mpf(0)
 for au in (0,1):
  for av in (0,1):
   for ax in (0,1):
    prob=(pu if au else 1-pu)*(pv if av else 1-pv)*(px if ax else 1-px)
    xe=te*au*av;xf=tf*au*ax
    denom=max(1,xe+xf)
    ze+=prob*xe/denom
    zf+=prob*xf/denom
 return ze/a,zf/b if b>0 else mp.nan

a0=mp.mpf(1)/3
for bstr in ['0.1','0.01','0.001','0.0001','0.000001','0.00000001','0.0000000001']:
 b=mp.mpf(bstr)
 for delta in [-b,0,b]:
  a=a0+delta
  print('b',bstr,'delta/a',mp.nstr(delta/b,3),'ratios',*[mp.nstr(x,30) for x in values(a,b)])
for bstr in ['0.01','0.001','0.000001']:
 b=mp.mpf(bstr)
 for dx in ['0','0.1','0.5','0.99']:
  print('leafextra',bstr,dx,*[mp.nstr(x,30) for x in values(a0,b,dx_extra=mp.mpf(dx))])
