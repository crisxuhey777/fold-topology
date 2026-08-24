// 读取 index.html 现有 36 关（归一化），翻译到 600×1000，重新求解 + 初始角偏移 + 非平凡性验证，输出归一化 LEVELS + SOL
'use strict';
const fs=require('fs');
const html=fs.readFileSync('index.html','utf8');
const s=html.indexOf('const LEVELS='), e=html.indexOf('\n  ];', s)+'\n  ];'.length;
const SRC=new Function('return '+html.slice(s+'const LEVELS='.length,e))();
const CM={white:0,cyan:1,red:2,purple:3};
const DEG=Math.PI/180;
class V2{constructor(x=0,y=0){this.x=x;this.y=y;}add(v){return new V2(this.x+v.x,this.y+v.y);}sub(v){return new V2(this.x-v.x,this.y-v.y);}mul(k){return new V2(this.x*k,this.y*k);}dot(v){return this.x*v.x+this.y*v.y;}cross(v){return this.x*v.y-this.y*v.x;}length(){return Math.hypot(this.x,this.y);}normalize(){const l=this.length();return l>1e-9?new V2(this.x/l,this.y/l):new V2(0,0);}perp(){return new V2(-this.y,this.x);}rotate(r){const c=Math.cos(r),sn=Math.sin(r);return new V2(this.x*c-this.y*sn,this.x*sn+this.y*c);}reflect(n){const nn=n.normalize();return this.sub(nn.mul(2*this.dot(nn)));}}
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
const NX=x=>x*600, NY=y=>y*1000;
function build(L,fold1,sol){
  const fa=L.foldAxis, ax={a:new V2(fa.x1,fa.y1),b:new V2(fa.x2,fa.y2)};
  const s1=fold1?-1:1, ad=ax.b.sub(ax.a).normalize(), n=ad.perp();
  const fp=p=>{const d=p.sub(ax.a).dot(n);return p.sub(n.mul(d*(1-s1)));};
  const fv=v=>n.mul(s1*v.dot(n)).add(ad.mul(v.dot(ad))).normalize();
  const geo={mirrors:[],blackholes:[],crystals:[],prisms:[],dyes:[],wormholes:[],lenses:[],gateSensors:[],gateWalls:[]}; let cid=0,gid=0;
  (L.mirrors||[]).forEach((m,i)=>{ const so=sol.m&&sol.m[i]; let ang=so!==undefined?so:m.angle;
    const c=m.fold?fp(new V2(m.x,m.y)):new V2(m.x,m.y); const v=new V2(Math.cos(ang*DEG),Math.sin(ang*DEG)); const t=m.fold?fv(v):v;
    geo.mirrors.push({kind:'mirror',a:c.sub(t.mul(m.half)),b:c.add(t.mul(m.half)),normal:t.perp()}); });
  (L.sliders||[]).forEach((s,i)=>{ const so=sol.s&&sol.s[i]; let ang=so&&so.angle!==undefined?so.angle:s.angle; let mx=so&&so.x!==undefined?so.x:s.x; let my=so&&so.y!==undefined?so.y:s.y;
    const c=s.fold?fp(new V2(mx,my)):new V2(mx,my); const v=new V2(Math.cos(ang*DEG),Math.sin(ang*DEG)); const t=s.fold?fv(v):v;
    geo.mirrors.push({kind:'mirror',a:c.sub(t.mul(s.half)),b:c.add(t.mul(s.half)),normal:t.perp()}); });
  (L.prisms||[]).forEach(p=>{ const ang=p.angle*DEG,c=p.fold?fp(new V2(p.x,p.y)):new V2(p.x,p.y);
    const ap=p.fold?fv(new V2(Math.cos(ang),Math.sin(ang))):new V2(Math.cos(ang),Math.sin(ang)); const verts=[];
    for(let k=0;k<3;k++)verts.push(c.add(ap.rotate(k*2*Math.PI/3).mul(p.r))); geo.prisms.push({kind:'prism',verts}); });
  (L.blackholes||[]).forEach(b=>geo.blackholes.push({kind:'blackhole',center:b.fold?fp(new V2(b.x,b.y)):new V2(b.x,b.y),radius:b.r}));
  (L.dyes||[]).forEach(d=>{ const ang=d.angle*DEG,c=d.fold?fp(new V2(d.x,d.y)):new V2(d.x,d.y);
    const t=d.fold?fv(new V2(Math.cos(ang),Math.sin(ang))):new V2(Math.cos(ang),Math.sin(ang));
    geo.dyes.push({kind:'dye',a:c.sub(t.mul(d.half)),b:c.add(t.mul(d.half)),mask:CM[d.color]}); });
  (L.portals||[]).forEach(w=>{ const pa=w.a.fold?fp(new V2(w.a.x,w.a.y)):new V2(w.a.x,w.a.y),pb=w.b.fold?fp(new V2(w.b.x,w.b.y)):new V2(w.b.x,w.b.y);
    geo.wormholes.push({kind:'wormhole',center:pa,radius:w.r,partner:pb}); geo.wormholes.push({kind:'wormhole',center:pb,radius:w.r,partner:pa}); });
  (L.gravityWells||[]).forEach(g=>{ const c=g.fold?fp(new V2(g.x,g.y)):new V2(g.x,g.y); geo.lenses.push({kind:'lens',center:c,influence:g.influence,bend:g.bend*DEG}); });
  (L.gates||[]).forEach(g=>{ const sc=g.sensor.fold?fp(new V2(g.sensor.x,g.sensor.y)):new V2(g.sensor.x,g.sensor.y), wc=g.wall.fold?fp(new V2(g.wall.x,g.wall.y)):new V2(g.wall.x,g.wall.y);
    const wt=g.wall.fold?fv(new V2(Math.cos(g.wall.angle*DEG),Math.sin(g.wall.angle*DEG))):new V2(Math.cos(g.wall.angle*DEG),Math.sin(g.wall.angle*DEG));
    geo.gateSensors.push({kind:'sensor',center:sc,radius:g.sensor.r,gateId:gid}); geo.gateWalls.push({kind:'wall',a:wc.sub(wt.mul(g.wall.half)),b:wc.add(wt.mul(g.wall.half)),gateId:gid}); gid++; });
  (L.targets||[]).forEach(t=>geo.crystals.push({kind:'crystal',center:t.fold?fp(new V2(t.x,t.y)):new V2(t.x,t.y),radius:t.r,mask:CM[t.color||'white'],id:cid++}));
  return geo;
}
function cast(L,fold1,sol){ const O=new V2(L.emitter.x,L.emitter.y),D=new V2(Math.cos(L.emitter.angle*DEG),Math.sin(L.emitter.angle*DEG)); return RC.cast(O,D,build(L,fold1,sol)); }
function solve(L,fold1,step=15){
  const nm=(L.mirrors||[]).length, ns=(L.sliders||[]).length;
  const angR=[]; for(let a=-180;a<=180;a+=step)angR.push(a);
  function recM(i,sol){ if(i===nm){ if(ns===0)return cast(L,fold1,sol).solved?sol:null;
    function recS(j,sol2){ if(j===ns)return cast(L,fold1,sol2).solved?sol2:null;
      const sl=L.sliders[j]; const axis=sl.track.axis; const min=sl.track.min, max=sl.track.max;
      for(let v=min;v<=max;v+=5){ const r=recS(j+1,{...sol2,s:{...sol2.s,[j]:axis==='x'?{x:v}:{y:v}}}); if(r)return r; }
      return null; }
    return recS(0,sol); }
    const m=L.mirrors[i]; if(m.locked) return recM(i+1,sol);
    for(const a of angR){ const r=recM(i+1,{...sol,m:{...sol.m,[i]:a}}); if(r)return r; }
    return null; }
  return recM(0,{});
}
// 翻译 SRC 到逻辑坐标
const LV=SRC.map(o=>{
  const fa=o.foldAxis||{x1:0.5,y1:0.05,x2:0.5,y2:0.95};
  const isH = Math.abs(fa.y1-fa.y2) < 1e-6;
  return {
    id:o.id, title:o.title, chapter:o.chapter, hint:o.hint, newFeature:o.newFeature, theme:o.theme, f1:o.solution.f1,
    foldAxis: isH ? {x1:NX(0.05),y1:NY(0.5),x2:NX(0.95),y2:NY(0.5)} : {x1:NX(0.5),y1:NY(0.06),x2:NX(0.5),y2:NY(0.94)},
    emitter:{x:NX(o.emitter.x),y:NY(o.emitter.y),angle:o.emitter.angle},
    mirrors:(o.mirrors||[]).map(m=>({x:NX(m.x),y:NY(m.y),fold:m.fold,angle:m.initialAngle,locked:!!m.isLocked,half:m.half||42})),
    sliders:(o.sliders||[]).map(s=>({x:NX(s.x),y:NY(s.y),fold:s.fold,angle:s.initialAngle,half:s.half||42,track:{axis:s.track.axis,min:NX(s.track.min),max:NX(s.track.max)}})),
    prisms:(o.prisms||[]).map(p=>({x:NX(p.x),y:NY(p.y),fold:p.fold,angle:p.angle,r:p.r||28})),
    blackholes:(o.blackHoles||[]).map(b=>({x:NX(b.x),y:NY(b.y),fold:b.fold,r:b.r})),
    dyes:(o.dyes||[]).map(d=>({x:NX(d.x),y:NY(d.y),fold:d.fold,angle:d.angle,half:d.half||24,color:d.color})),
    portals:(o.portals||[]).map(w=>({r:w.r,a:{x:NX(w.a.x),y:NY(w.a.y),fold:w.a.fold},b:{x:NX(w.b.x),y:NY(w.b.y),fold:w.b.fold}})),
    gravityWells:(o.gravityWells||[]).map(g=>({x:NX(g.x),y:NY(g.y),fold:g.fold,r:g.r,influence:g.influence,bend:g.bend})),
    gates:(o.gates||[]).map(g=>({sensor:{x:NX(g.sensor.x),y:NY(g.sensor.y),r:g.sensor.r,fold:g.sensor.fold},wall:{x:NX(g.wall.x),y:NY(g.wall.y),angle:g.wall.angle,half:g.wall.half,fold:g.wall.fold}})),
    targets:(o.targets||[]).map(t=>({x:NX(t.x),y:NY(t.y),fold:t.fold,r:t.r,color:t.color||'white'}))
  };
});
// ---- 修复在 600×1000 下失效的棱镜/引力/光门关卡（逻辑坐标） ----
const M2=(x,y,fold,angle,locked,half=42)=>({x,y,fold,angle,locked,half});
const T2=(x,y,fold,r=20,color='white')=>({x,y,fold,r,color});
const FIX={
  8:{mirrors:[M2(360,470,1,-135,true),M2(360,530,1,-45,true)],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],targets:[T2(319,356,1,18),T2(319,644,1,18)]},
  9:{mirrors:[],prisms:[],dyes:[{x:460,y:500,fold:1,angle:90,half:22,color:'cyan'}],targets:[T2(340,500,1,18,'cyan')]},
  10:{mirrors:[],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],dyes:[{x:370,y:477,fold:1,angle:90,half:22,color:'cyan'},{x:370,y:523,fold:1,angle:90,half:22,color:'red'}],targets:[T2(320,455,1,18,'cyan'),T2(320,545,1,18,'red')]},
  11:{mirrors:[],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],blackholes:[{x:250,y:500,fold:0,r:22}],targets:[T2(320,455,1,18),T2(320,545,1,18)]},
  12:{mirrors:[M2(440,500,1,-135,true)],blackholes:[{x:200,y:500,fold:0,r:22}],dyes:[{x:120,y:500,fold:0,angle:90,half:22,color:'cyan'}],targets:[T2(440,320,1,18,'cyan')]},
  13:{mirrors:[M2(460,500,1,0,false),M2(460,260,1,0,false),M2(300,260,1,0,false)],targets:[T2(300,140,1,18)]},
  14:{mirrors:[M2(360,470,1,0,false),M2(360,530,1,0,false)],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],dyes:[{x:320,y:455,fold:1,angle:90,half:22,color:'cyan'},{x:320,y:545,fold:1,angle:90,half:22,color:'red'}],targets:[T2(260,400,1,18,'cyan'),T2(260,600,1,18,'red')]},
  15:{mirrors:[],sliders:[{x:380,y:500,fold:1,angle:-135,half:42,track:{axis:'x',min:380,max:470}}],targets:[T2(430,300,1,18)]},
  16:{mirrors:[],sliders:[{x:360,y:500,fold:1,angle:-135,half:42,track:{axis:'x',min:360,max:450}}],targets:[T2(410,280,1,18)]},
  18:{mirrors:[],portals:[{r:14,a:{x:200,y:500,fold:0},b:{x:420,y:400,fold:1}}],blackholes:[{x:300,y:500,fold:0,r:22}],targets:[T2(300,400,1,18)]},
  19:{mirrors:[],sliders:[{x:350,y:500,fold:1,angle:-135,half:42,track:{axis:'x',min:350,max:380}}],portals:[{r:14,a:{x:200,y:500,fold:0},b:{x:380,y:500,fold:1}}],targets:[T2(370,300,1,18)]},
  20:{mirrors:[],portals:[{r:14,a:{x:200,y:500,fold:0},b:{x:420,y:500,fold:1}}],targets:[T2(320,500,1,18)]},
  21:{mirrors:[],sliders:[{x:380,y:500,fold:1,angle:-135,half:42,track:{axis:'x',min:380,max:470}},{x:380,y:300,fold:1,angle:-135,half:42,track:{axis:'x',min:380,max:470}}],targets:[T2(430,200,1,18)]},
  22:{mirrors:[],sliders:[{x:340,y:500,fold:1,angle:-135,half:42,track:{axis:'x',min:340,max:370}}],portals:[{r:14,a:{x:180,y:500,fold:0},b:{x:360,y:500,fold:1}}],targets:[T2(340,300,1,18)]},
  23:{mirrors:[],gravityWells:[{x:400,y:500,fold:1,r:20,influence:46,bend:35}],targets:[T2(344,633,0,18)]},
  24:{mirrors:[M2(300,610,1,0,false)],gravityWells:[{x:400,y:500,fold:1,r:20,influence:46,bend:35}],targets:[T2(240,700,1,18)]},
  26:{mirrors:[],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],gates:[{sensor:{x:250,y:470,r:16,fold:0},wall:{x:360,y:526,angle:250,half:30,fold:1}}],targets:[T2(315,543,1,18)]},
  27:{mirrors:[],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],gates:[{sensor:{x:240,y:460,r:16,fold:0},wall:{x:350,y:540,angle:250,half:30,fold:1}}],targets:[T2(310,560,1,18)]},
  36:{mirrors:[M2(315,543,1,0,false)],prisms:[{x:460,y:500,fold:1,angle:-90,r:28}],gates:[{sensor:{x:250,y:470,r:16,fold:0},wall:{x:360,y:526,angle:250,half:30,fold:1}}],targets:[T2(285,660,1,18)]},
};
for(const id in FIX){ const L=LV.find(x=>x.id===Number(id)); if(!L)continue;
  const f=FIX[id];
  for(const k of ['mirrors','sliders','prisms','blackholes','dyes','portals','gravityWells','gates','targets']) L[k]=f[k]||[];
  L.emitter=f.emitter||{x:100,y:500,angle:0};
}

const out=[], SOL={}; let fail=0;
for(const L of LV){
  const fold1=L.f1;
  let sol=solve(L,fold1);
  if(!sol){ console.log(`L${L.id} ${L.title}: NO SOLUTION`); fail++; continue; }
  if(L.f1 && cast(L,false,{}).solved){ console.log(`L${L.id} ${L.title}: UNFOLD SOLVES`); fail++; continue; }
  const outMirrors=(L.mirrors||[]).map((m,i)=>{ if(m.locked) return {x:m.x,y:m.y,angle:m.angle,half:m.half,fold:m.fold,locked:true};
    const sa=(sol.m&&sol.m[i]!==undefined)?sol.m[i]:m.angle;
    let ini=Math.round((sa+45)/15)*15; while(ini>180)ini-=360; while(ini<=-180)ini+=360;
    if(ini===Math.round(sa/15)*15) ini=Math.round((sa+60)/15)*15;
    return {x:m.x,y:m.y,angle:ini,half:m.half,fold:m.fold,locked:false}; });
  const outSliders=(L.sliders||[]).map((s,i)=>{ const solx=(sol.s&&sol.s[i]&&sol.s[i].x!==undefined)?sol.s[i].x:s.x;
    // 初始位置放到轨道另一端，保证初始不可解
    const iniX = (solx <= (s.track.min+s.track.max)/2) ? s.track.max : s.track.min;
    return {x:iniX,y:s.y,angle:s.angle,half:s.half,fold:s.fold,track:{axis:s.track.axis,min:s.track.min,max:s.track.max}}; });
  const NL={id:L.id,title:L.title,chapter:L.chapter,hint:L.hint,newFeature:L.newFeature,theme:L.theme,f1:L.f1,foldAxis:L.foldAxis,emitter:L.emitter,mirrors:outMirrors,sliders:outSliders,prisms:L.prisms,blackholes:L.blackholes,dyes:L.dyes,portals:L.portals,gravityWells:L.gravityWells,gates:L.gates,targets:L.targets};
  const sol2=solve(NL,fold1);
  if(!sol2){ console.log(`L${L.id} ${L.title}: RE-SOLVE FAIL`); fail++; continue; }
  if(sol2.m&&Object.keys(sol2.m).length||sol2.s&&Object.keys(sol2.s).length){ if(cast(NL,fold1,{}).solved){ console.log(`L${L.id} ${L.title}: INITIAL SOLVES (trivial)`); fail++; continue; } }
  SOL[L.id]=sol2; out.push(NL);
  console.log(`L${L.id} ${L.title}: OK sol=${JSON.stringify(sol2)}`);
}
console.log('\n==== ok', out.length, '/36 fail', fail, '====');
const norm=v=>+v.toFixed(4);
function ser(v){return JSON.stringify(v);}
let body='const LEVELS=[\n';
out.forEach((L,idx)=>{
  const fa=L.foldAxis;
  const parts=[`id:${L.id}`,`title:${ser(L.title)}`,`chapter:${ser(L.chapter)}`,`hint:${ser(L.hint)}`];
  if(L.newFeature)parts.push(`newFeature:${ser((L.newFeature+'').toUpperCase())}`); parts.push(`theme:${ser(L.theme)}`);
  parts.push(`foldAxis:{x1:${norm(fa.x1/600)},y1:${norm(fa.y1/1000)},x2:${norm(fa.x2/600)},y2:${norm(fa.y2/1000)}}`);
  parts.push(`emitter:{x:${norm(L.emitter.x/600)},y:${norm(L.emitter.y/1000)},angle:${L.emitter.angle}}`); parts.push(`solution:{f1:${L.f1}}`);
  const arrs=[];
  if(L.mirrors.length)arrs.push('mirrors:'+ser(L.mirrors.map(m=>({x:norm(m.x/600),y:norm(m.y/1000),initialAngle:m.angle,half:m.half,fold:m.fold,isLocked:m.locked}))));
  if(L.sliders.length)arrs.push('sliders:'+ser(L.sliders.map(s=>({x:norm(s.x/600),y:norm(s.y/1000),initialAngle:s.angle,half:s.half,fold:s.fold,isLocked:true,track:{axis:s.track.axis,min:norm(s.track.min/600),max:norm(s.track.max/600)}}))));
  if(L.prisms.length)arrs.push('prisms:'+ser(L.prisms.map(p=>({x:norm(p.x/600),y:norm(p.y/1000),angle:p.angle,r:p.r,fold:p.fold}))));
  if(L.blackholes.length)arrs.push('blackHoles:'+ser(L.blackholes.map(b=>({x:norm(b.x/600),y:norm(b.y/1000),r:b.r,fold:b.fold}))));
  if(L.dyes.length)arrs.push('dyes:'+ser(L.dyes.map(d=>({x:norm(d.x/600),y:norm(d.y/1000),angle:d.angle,half:d.half,color:d.color,fold:d.fold}))));
  if(L.portals.length)arrs.push('portals:'+ser(L.portals.map(w=>({r:w.r,a:{x:norm(w.a.x/600),y:norm(w.a.y/1000),fold:w.a.fold},b:{x:norm(w.b.x/600),y:norm(w.b.y/1000),fold:w.b.fold}}))));
  if(L.gravityWells.length)arrs.push('gravityWells:'+ser(L.gravityWells.map(g=>({x:norm(g.x/600),y:norm(g.y/1000),r:g.r,influence:g.influence,bend:g.bend,fold:g.fold}))));
  if(L.gates.length)arrs.push('gates:'+ser(L.gates.map(g=>({sensor:{x:norm(g.sensor.x/600),y:norm(g.sensor.y/1000),r:g.sensor.r,fold:g.sensor.fold},wall:{x:norm(g.wall.x/600),y:norm(g.wall.y/1000),angle:g.wall.angle,half:g.wall.half,fold:g.wall.fold}}))));
  if(L.targets.length)arrs.push('targets:'+ser(L.targets.map(t=>({x:norm(t.x/600),y:norm(t.y/1000),r:t.r,color:t.color,fold:t.fold}))));
  body+='    { '+parts.concat(arrs).join(', ')+' }'+(idx<out.length-1?',':'')+'\n';
});
body+='  ];';
fs.writeFileSync('__lv10out.txt', body+'\n\nSOL='+JSON.stringify(SOL));
console.log('written __lv10out.txt');
process.exit(fail?1:0);
