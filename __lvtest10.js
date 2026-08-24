// 验证 36 关（竖屏 600×1000 归一化 schema）
'use strict';
const fs=require('fs'); const html=fs.readFileSync('index.html','utf8');
const s=html.indexOf('const LEVELS='); const e=html.indexOf('\n  ];', s)+'\n  ];'.length;
const LEVELS=new Function('return '+html.slice(s+'const LEVELS='.length,e))();
const CM={white:0,cyan:1,red:2,purple:3};
class V2{constructor(x=0,y=0){this.x=x;this.y=y;}add(v){return new V2(this.x+v.x,this.y+v.y);}sub(v){return new V2(this.x-v.x,this.y-v.y);}mul(k){return new V2(this.x*k,this.y*k);}
dot(v){return this.x*v.x+this.y*v.y;}cross(v){return this.x*v.y-this.y*v.x;}length(){return Math.hypot(this.x,this.y);}normalize(){const l=this.length();return l>1e-9?new V2(this.x/l,this.y/l):new V2(0,0);}
perp(){return new V2(-this.y,this.x);}rotate(r){const c=Math.cos(r),sn=Math.sin(r);return new V2(this.x*c-this.y*sn,this.x*sn+this.y*c);}reflect(n){const nn=n.normalize();return this.sub(nn.mul(2*this.dot(nn)));}}
class RC{static seg(O,D,A,B){const E=B.sub(A),M=A.sub(O),dn=D.cross(E);if(Math.abs(dn)<1e-9)return null;const t=M.cross(E)/dn,s2=M.cross(D)/dn;if(t<1e-4||s2<0||s2>1)return null;return t;}
static roots(O,D,C,r){const f=O.sub(C),b=f.dot(D),c=f.dot(f)-r*r,d=b*b-c;if(d<0)return null;const q=Math.sqrt(d);return{near:-b-q,far:-b+q};}
static circ(O,D,C,r){const rt=RC.roots(O,D,C,r);if(!rt)return null;if(rt.near>=1e-4)return rt.near;if(rt.far>=1e-4)return rt.far;return null;}
static tri(O,D,v){let mn=Infinity,mx=-Infinity,n=0;for(let i=0;i<3;i++){const t=RC.seg(O,D,v[i],v[(i+1)%3]);if(t!==null){n++;if(t<mn)mn=t;if(t>mx)mx=t;}}if(n<2)return null;return{tEntry:mn,tExit:mx};}
static cast(O0,D0,geo){const p1=RC.co(O0,D0,geo,new Set());return RC.co(O0,D0,geo,new Set(p1.gh));}
static co(O0,D0,geo,open){const SPLIT=20*Math.PI/180,act=new Set(),gh=new Set(),cnt=geo.crystals.length;
const tr=(O,D,c,budget)=>{while(true){let bt=Infinity,bo=null,ph=null;const cn=(t,o)=>{if(t!==null&&t<bt){bt=t;bo=o;}};
for(const m of geo.mirrors)cn(RC.seg(O,D,m.a,m.b),m);for(const h of geo.blackholes)cn(RC.circ(O,D,h.center,h.radius),h);for(const cr of geo.crystals)cn(RC.circ(O,D,cr.center,cr.radius),cr);for(const d of geo.dyes)cn(RC.seg(O,D,d.a,d.b),d);for(const w of geo.wormholes)cn(RC.circ(O,D,w.center,w.radius),w);for(const l of geo.lenses)cn(RC.circ(O,D,l.center,l.influence),l);for(const sd of geo.gateSensors)cn(RC.circ(O,D,sd.center,sd.radius),sd);for(const w of geo.gateWalls)cn(RC.seg(O,D,w.a,w.b),w);for(const p of geo.prisms){const r=RC.tri(O,D,p.verts);if(r&&r.tEntry<bt){bt=r.tEntry;bo=p;ph=r;}}
if(bo===null)return;const hit=O.add(D.mul(bt));
if(bo.kind==='crystal'){if(c===bo.mask)act.add(bo.id);else{const far=RC.roots(O,D,bo.center,bo.radius).far;O=O.add(D.mul(far+1e-3));continue;}return;}
if(bo.kind==='blackhole')return;if(bo.kind==='dye'){c=c|bo.mask;O=hit.add(D.mul(1e-3));continue;}
if(bo.kind==='wormhole'){if(budget<=0)return;budget--;O=bo.partner.add(D.mul(bo.radius+1e-3));continue;}
if(bo.kind==='lens'){if(budget<=0)return;budget--;D=D.rotate(bo.bend);O=hit.add(D.mul(bo.influence*2+1e-3));continue;}
if(bo.kind==='sensor'){gh.add(bo.gateId);return;}
if(bo.kind==='wall'){if(open.has(bo.gateId)){O=hit.add(D.mul(1e-3));continue;}return;}
if(bo.kind==='mirror'){if(budget<=0)return;budget--;D=D.reflect(bo.normal);O=hit.add(D.mul(1e-3));continue;}
if(bo.kind==='prism'){if(budget<=0)return;budget--;const exit=O.add(D.mul(ph.tExit));for(const k of[-1,1]){const cd=D.rotate(k*SPLIT);tr(exit.add(cd.mul(1e-3)),cd,c,budget);}return;}}};
tr(O0,D0,0,8);return{solved:act.size>=cnt&&cnt>0,gh:[...gh]};}}
const DEG=Math.PI/180, NX=x=>x*600, NY=y=>y*1000;
function build(lv,fold1,sol){
  const df={x1:0.5,y1:0.06,x2:0.5,y2:0.94};
  const fas=(lv.foldAxes&&lv.foldAxes.length===2)?lv.foldAxes:[lv.foldAxis||df, lv.foldAxis||df];
  const axes=fas.map(f=>({a:new V2(NX(f.x1),NY(f.y1)),b:new V2(NX(f.x2),NY(f.y2))}));
  const s1=fold1?-1:1;
  const fpt=(p,ax)=>{const ad=ax.b.sub(ax.a).normalize(), n=ad.perp(); const d=p.sub(ax.a).dot(n); return p.sub(n.mul(d*(1-s1)));};
  const fdt=(v,ax)=>{const ad=ax.b.sub(ax.a).normalize(), n=ad.perp(); return n.mul(s1*v.dot(n)).add(ad.mul(v.dot(ad))).normalize();};
  const fp=(p,f)=>{let o=p; if(f&1)o=fpt(o,axes[0]); if(f&2)o=fpt(o,axes[1]); return o;};
  const fv=(v,f)=>{let d=v; if(f&1)d=fdt(d,axes[0]); if(f&2)d=fdt(d,axes[1]); return d.normalize();};
  const geo={mirrors:[],blackholes:[],crystals:[],prisms:[],dyes:[],wormholes:[],lenses:[],gateSensors:[],gateWalls:[]}; let cid=0,gid=0;
  (lv.mirrors||[]).forEach((m,i)=>{ const so=sol.m&&sol.m[i]; let ang=so!==undefined?so:m.initialAngle;
    const c=fp(new V2(NX(m.x),NY(m.y)),m.fold||0); const v=new V2(Math.cos(ang*DEG),Math.sin(ang*DEG)); const t=fv(v,m.fold||0);
    geo.mirrors.push({kind:'mirror',a:c.sub(t.mul(m.half)),b:c.add(t.mul(m.half)),normal:t.perp()}); });
  (lv.sliders||[]).forEach((s,i)=>{ const so=sol.s&&sol.s[i]; let ang=so&&so.angle!==undefined?so.angle:s.initialAngle; let mx=so&&so.x!==undefined?so.x:NX(s.x); let my=so&&so.y!==undefined?so.y:NY(s.y);
    const c=fp(new V2(mx,my),s.fold||0); const v=new V2(Math.cos(ang*DEG),Math.sin(ang*DEG)); const t=fv(v,s.fold||0);
    geo.mirrors.push({kind:'mirror',a:c.sub(t.mul(s.half)),b:c.add(t.mul(s.half)),normal:t.perp()}); });
  (lv.prisms||[]).forEach(p=>{ const ang=p.angle*DEG,c=fp(new V2(NX(p.x),NY(p.y)),p.fold||0);
    const ap=fv(new V2(Math.cos(ang),Math.sin(ang)),p.fold||0); const verts=[];
    for(let k=0;k<3;k++)verts.push(c.add(ap.rotate(k*2*Math.PI/3).mul(p.r))); geo.prisms.push({kind:'prism',verts}); });
  (lv.blackHoles||[]).forEach(b=>geo.blackholes.push({kind:'blackhole',center:fp(new V2(NX(b.x),NY(b.y)),b.fold||0),radius:b.r}));
  (lv.dyes||[]).forEach(d=>{ const ang=d.angle*DEG,c=fp(new V2(NX(d.x),NY(d.y)),d.fold||0);
    const t=fv(new V2(Math.cos(ang),Math.sin(ang)),d.fold||0);
    geo.dyes.push({kind:'dye',a:c.sub(t.mul(d.half)),b:c.add(t.mul(d.half)),mask:CM[d.color]}); });
  (lv.portals||[]).forEach(w=>{ const pa=fp(new V2(NX(w.a.x),NY(w.a.y)),w.a.fold||0),pb=fp(new V2(NX(w.b.x),NY(w.b.y)),w.b.fold||0);
    geo.wormholes.push({kind:'wormhole',center:pa,radius:w.r,partner:pb}); geo.wormholes.push({kind:'wormhole',center:pb,radius:w.r,partner:pa}); });
  (lv.gravityWells||[]).forEach(g=>{ const c=fp(new V2(NX(g.x),NY(g.y)),g.fold||0); geo.lenses.push({kind:'lens',center:c,influence:g.influence,bend:g.bend*DEG}); });
  (lv.gates||[]).forEach(g=>{ const sc=fp(new V2(NX(g.sensor.x),NY(g.sensor.y)),g.sensor.fold||0), wc=fp(new V2(NX(g.wall.x),NY(g.wall.y)),g.wall.fold||0);
    const wt=fv(new V2(Math.cos(g.wall.angle*DEG),Math.sin(g.wall.angle*DEG)),g.wall.fold||0);
    geo.gateSensors.push({kind:'sensor',center:sc,radius:g.sensor.r,gateId:gid}); geo.gateWalls.push({kind:'wall',a:wc.sub(wt.mul(g.wall.half)),b:wc.add(wt.mul(g.wall.half)),gateId:gid}); gid++; });
  (lv.targets||[]).forEach(t=>geo.crystals.push({kind:'crystal',center:fp(new V2(NX(t.x),NY(t.y)),t.fold||0),radius:t.r,mask:CM[t.color||'white'],id:cid++}));
  return geo;
}
const SOL={1:{},2:{},3:{m:{0:-135}},4:{m:{0:-135,1:-135}},5:{m:{0:-135,1:-135}},6:{m:{0:-135}},7:{},8:{},9:{},10:{},11:{},12:{},13:{m:{0:-150,1:-75,2:-60}},14:{m:{0:-150,1:-30}},15:{s:{0:{x:415}}},16:{s:{0:{x:395}}},17:{m:{0:-45,1:-45}},18:{},19:{s:{0:{x:355}}},20:{},21:{s:{0:{x:415},1:{x:380}}},22:{s:{0:{x:340}}},23:{},24:{m:{0:-45}},25:{},26:{},27:{},28:{},29:{},30:{s:{0:{x:372}}},31:{m:{0:-150,1:-180}},32:{m:{0:-135}},33:{s:{0:{x:372}}},34:{m:{0:-135,1:-135}},35:{m:{0:-45}},36:{m:{0:-45}}};
let ok=true;
for(const lv of LEVELS){
  const L=new V2(NX(lv.emitter.x),NY(lv.emitter.y)),D=new V2(Math.cos(lv.emitter.angle*DEG),Math.sin(lv.emitter.angle*DEG));
  const sol=SOL[lv.id]||{};
  const solved=RC.cast(L,D,build(lv,lv.solution.f1,sol)).solved;
  let pass=solved===true;
  if(lv.solution.f1){ if(RC.cast(L,D,build(lv,false,{})).solved)pass=false; }
  const hasSol=(sol.m&&Object.keys(sol.m).length)||(sol.s&&Object.keys(sol.s).length);
  if(hasSol){ if(RC.cast(L,D,build(lv,true,{})).solved)pass=false; }
  if(!pass)ok=false;
  console.log(`关${String(lv.id).padStart(2)}「${lv.title}」 ${solved?'解':'✗未解'} ${pass?'PASS ✓':'FAIL ✗'}`);
}
console.log('\n总断言:',ok?'PASS ✓ (36/36)':'FAIL ✗');
process.exit(ok?0:1);
