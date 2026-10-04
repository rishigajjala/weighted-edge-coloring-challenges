import numpy as np

K=4/3
worst=(2,None)
for a in np.linspace(.0001,.9998,300):
 for b in np.linspace(.0001,1-a,220):
  pu=.25+.75*(a+b);ph=.25+.75*a;pv=.25+.75*b
  # u_L-h_R internal f, u_L-v_R external e.
  bf=min(K*a/(pu*ph),12*a)
  be=min(K*b/(pu*pv),12*b)
  exp_e=0.; exp_f=0.
  for au,ah,prob in [(0,0,1-pu),(1,0,pu-ph),(1,1,ph)]:
   for av,pv_state in [(0,1-pv),(1,pv)]:
    xf=bf*au*ah;xe=be*au*av
    lu=xf+xe
    zf=xf/max(1,lu,xf);ze=xe/max(1,lu,xe)
    exp_e+=prob*pv_state*ze
    exp_f+=prob*pv_state*zf
  ratio=min(exp_e/b,exp_f/a)
  if ratio<worst[0]:worst=(ratio,(a,b,exp_e/b,exp_f/a))
print(worst)
