#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int lval;
typedef struct { void *f; lval v[3]; } *frame;
lval *memory; lval *memf; int memory_size; void print(lval);
lval lread(void *); lval evca(void *, lval); int dbgr(void *,int,lval,lval *);
struct symbol_init { const char *name; lval (*fun)(); int argc;
  lval (*setfun)(); int setargc; lval sym; };
extern struct symbol_init symi[];
lval *o2c(lval o) { return memory + o/4; }
lval c2o(lval *c) { return 4 * (c - memory) + 1; }
int cp(lval o) { return (o & 3) == 1; }
lval *o2a(lval o) { return memory + o/4; }
lval a2o(lval *a) { return 4 * (a - memory) + 2; }
int ap(lval o) { return (o & 3) == 2; }
lval *o2s(lval o) { return memory + o/4; }
char *o2z(lval o) { return (char*)(memory + o/4 + 2); }
lval s2o(lval *s) { return 4 * (s - memory) + 3; }
int sp(lval o) { return (o & 3) == 3; }
#define TRUE symi[1].sym
#define T g.v[2]
#define U g.v[3]
#define V g.v[4]
#define W g.v[5]
#define NF(n) struct { void *f; lval v[n+2]; } g={0,{n}}; g.f=f; g.v[1]=E;
#define E ((frame)f)->v[1]
#define NE g.v[1]
#define AR ((frame)f)->v[2]
#define A0 car(AR)
#define A0R cdr(AR)
#define A1 car(cdr(AR))
#define A1R cdr(cdr(AR))
#define A2 car(cddr(AR))
#define A3 cadr(cddr(AR))
lval car(lval c) { return (c & 3) == 1 ? o2c(c)[0] : 0; }
lval cdr(lval c) { return (c & 3) == 1 ? o2c(c)[1] : 0; }
lval caar(lval c) { return car(car(c)); }
lval cdar(lval c) { return cdr(car(c)); }
lval cadr(lval c) { return car(cdr(c)); }
lval cddr(lval c) { return cdr(cdr(c)); }
lval set_car(lval c, lval val) { return o2c(c)[0] = val; }
lval set_cdr(lval c, lval val) { return o2c(c)[1] = val; }
lval *binding(void *f, lval sym, int type, int *macro) { lval env; st:
  for (env = E; env; env = cdr(env)) { lval e = caar(env);
  if (type || cp(e) ? car(e) == sym && (cdr(e) >> 4) == type : e == sym) {
    if (macro) *macro = cp(e) && cdr(e) & 8; return o2c(car(env))+1; }}
  if (macro) *macro = (o2a(sym)[8] >> type) & 32; if (type > 2) {
    dbgr(f, type, sym, &sym); goto st; } return o2a(sym)+4+type; }
lval xvalues=8; lval dyns=0; jmp_buf top_jmp; lval pkg; lval pkgs; lval kwp=0;
void gcm(lval v) { lval *t; int i; st: t=memory+v/4; if (v&3 && !(t[0]&4)) {
  t[0]|=4; switch (v&3) { case 1: gcm(t[0]-4); v=t[1]; goto st; case 2:
 if (t[0]>>5) { for (i=1; i<t[0]>>5; i++) gcm(t[i+1]); v=t[i+1]; goto st; }}}}
lval gc(struct { void *f; lval v[6]; } *f) { int i; lval *m; int l; int u = 0; int ml;
  printf(";garbage collecting...\n"); while (memf) { lval *n = (lval*)memf[0];
  /*memf[0]=0; memf[1]=0;*/memset(memf, 0, 4*memf[1]);
 memf=(lval*)n; } gcm(xvalues); gcm(pkgs); gcm(dyns);
  for (; f->f; f = f->f) for (i = 1; i < f->v[0] + 2; i++) gcm(f->v[i]);
  memf = 0; m = memory; i = 0; while (m < memory + memory_size/4) {
    l = ((m[1] & 4 ? m[0] >> 5 : 0) + 1) & ~1; if (m[0] & 4) { if (u) {
      m[-ml] = (lval)memf; m[1-ml] = ml; memf = m-ml; u = 0; i += ml; }} else {
	if (!u) ml = 0; ml += l + 2; u = 1; } m[0] &= ~4; m += l + 2; }
  if (u) { m[-ml] = (lval)memf; m[1-ml] = ml; memf = m-ml; i += ml; }
  printf(";done. %d free.\n", i); return 0; }
lval *m0(void *g, int n) { lval *m = memf; lval *p = 0; n = (n + 1) & ~1;
 for (; m; m = (lval*)m[0]) { if (n <= m[1]) { if (m[1]==n)
   if (p) p[0] = m[0]; else memf = (lval*)m[0]; else { m[1] -= n; m += m[1]; }
 return m; } p = m; } return 0; }
lval *ma0(void *g, int n) { lval *m; st: m = m0(g, n+2);
 if (!m) { gc(g); goto st; } *m = n<<5; return m; }
lval *ms0(void *g, int n) { lval *m; st: m = m0(g, (n+12)/4);
 if (!m) { gc(g); goto st; } *m = (n+4)<<3; return m; }
lval ma(void *g,int n,...) { va_list v; int i; lval *m; st: va_start(v, n);
 m=m0(g,n+2); if (!m) {for (i=-1;i<n;i++) gcm(va_arg(v,lval)); gc(g); goto st;}
 *m = n<<5; for (i=-1; i < n; i++) m[2 + i] = va_arg(v, lval); return a2o(m); }
lval ms(void *g,int n,...) { va_list v; int i; lval *m; st: va_start(v, n);
 m = m0(g,n+2); if (!m) { gc(g); goto st; } *m = n<<5; for (i=-1; i < n; i++)
   m[2 + i] = va_arg(v, lval); return s2o(m); }
double o2d(lval o) { return sp(o) ? *(double*)(o2s(o) + 2) : o>>5; }
lval d2o(void *g, double d) { lval x = (lval)d<<5|16; lval *a; if (o2d(x) == d)
  return x; a = ma0(g, 2); a[1] = 84; *(double*)(a+2) = d; return s2o(a); }
int o2i(lval o) { return (int)o2d(o); }
unsigned o2u(lval o) { return (unsigned)o2d(o); }
lval cons(void *g, lval a, lval d) { lval *c = m0(g, 2); if (!c) { gcm(a);
 gcm(d); gc(g); c = m0(g, 2); } c[0] = a; c[1] = d; return c2o(c); }
int string_equal_do(lval a, lval b) { int i; for (i=0; i < o2s(a)[0]/8-4; i++)
  if (o2z(a)[i] != o2z(b)[i]) return 0; return 1; }
int string_equal(lval a, lval b) { return a == b || (sp(a) && sp(b) &&
  o2s(a)[1] == 20 && o2s(b)[1] == 20 && o2s(a)[0] == o2s(b)[0]
  && string_equal_do(a, b)); }
lval argi(lval a, lval *b) { if (cp(a)) { *b = cdr(a); return car(a); }
 *b = 0; return a; }
lval args(void *f, lval e, lval m, lval a) { NF(1) int t; lval k,l; st: t=0;
 T = cons(&g, m, a); while (cp(m)) { lval n = car(m); m = cdr(m);
 switch(cp(n) ? -1 : o2a(n)[7]>>3) { case 2: case 3: t=1; continue;
 case 4: t=2; continue; case 5: t=-2; continue; case 6: t=4; continue; default:
 switch (t) { case 0: if (!a) { dbgr(&g, 7, T, &a); m=car(T); goto st; }
 e=args(&g,e,n,car(a)); break; case 1: e=cons(&g,cons(&g,n,a),e);t=-1;continue;
 case 2: n=argi(n,&k); e=args(&g, e, n, a ? car(a) : evca(&g, k)); break;
 case -2: n=argi(n,&l); for (k=a; k; k=cddr(k))
   if (string_equal(o2a(n)[2], o2a(car(k))[2]) && o2a(car(k))[9] == kwp)
     {l=cadr(k); break;} e=args(&g, e, n, k ? l : evca(&g, l)); continue;
 case 4: e=cons(&g,cons(&g,n,cdr(T)),e); t=0; continue; }} a=cdr(a); } if (m)
   return cons(&g, cons(&g, m, a), e); if (a && t>=0) { dbgr(&g, 6, T, &a);
   m=car(T); goto st; } return e; }
lval eval_body(void *f, lval ex) { NF(1) T=0;
 for (; ex; ex=cdr(ex)) T = evca(&g, ex); return T; }
lval map_eval(void *f, lval ex) { NF(1) if (ex) { T = evca(&g, ex);
 return cons(&g, T, map_eval(&g, cdr(ex))); } else return 0; }
lval eval(void *f, lval expr) { NF(1) T=cons(&g, expr, 0); return evca(&g,T); }
lval rvalues(void *g, lval v) { return xvalues==8 ? cons(g, v, 0) : xvalues; }
lval mvalues(lval a) { xvalues = a; return car(a); }
lval call(void *f, lval fn, lval a) { NF(3) jmp_buf jmp; lval vs; g.v[2] = a;
 g.v[3] = fn; if (o2a(fn)[1]==20) fn=o2a(fn)[5]; if (o2a(fn)[2] == 992)
   NE=args(&g, o2a(fn)[3], o2a(fn)[4], a); V=cons(&g, dyns, ms(&g,1,20,&jmp));
 NE = cons(&g, cons(&g,cons(&g,o2a(fn)[6],64),V), NE); if (!(vs=setjmp(jmp))) {
   if (o2a(fn)[2] == 992) return eval_body(&g, o2a(fn)[5]);
   else return o2a(fn)[3] ? symi[o2a(fn)[2]>>3].setfun(&g)
    : symi[o2a(fn)[2]>>3].fun(&g); } else return mvalues(car(vs)); }
lval eval_quote(void *g, lval ex) { return car(ex); }
int specp(void *f, lval ex, lval s) { for (; ex; ex = cdr(ex))
  if (ap(caar(ex)) && o2a(caar(ex))[7] == 3<<3) { lval e = cdar(ex);
  for (; e; e = cdr(e)) if (o2a(caar(e))[7] == 4<<3) { lval sp = cdar(e);
  for (; sp; sp=cdr(sp)) if (car(sp) == s) return 1; }} else break; return 0; }
void unwind(void *f, lval c) { NF(0) lval e; for (; dyns != c; dyns=cdr(dyns))
  if (ap(car(dyns))) if (o2a(car(dyns))[1] == 52) { NE=o2a(car(dyns))[2];
  eval_body(&g,o2a(car(dyns))[3]); } else for (e=o2a(car(dyns))[2];e; e=cdr(e))
    o2a(caar(e))[4] = cdar(e); else o2s(car(dyns))[2] = 0; }
lval eval_let(void *f, lval ex) { NF(3) lval r = ma(&g, 1, 84, 0); U=E;
 dyns = cons(&g, r, dyns); for (T=car(ex); T; T=cdr(T)) { V=evca(&g, cdar(T));
 if (o2a(caar(T))[8] & 128 || specp(&g,cdr(ex),caar(T))) {
   o2a(r)[2] = cons(&g, cons(&g, caar(T), V), o2a(r)[2]); }
 else U = cons(&g, cons(&g,caar(T),V), U); } for (r = o2a(r)[2]; r; r=cdr(r)) {
   T = o2a(caar(r))[4]; o2a(caar(r))[4] = cdar(r); set_cdr(car(r), T);
   U = cons(&g, cons(&g,caar(r),-8), U); } NE = U; T = eval_body(&g, cdr(ex));
   unwind(f, cdr(dyns)); return T; }
lval eval_letm(void *f, lval ex) { NF(2) lval r = ma(&g, 1, 84, 0);
 dyns = cons(&g, r, dyns); for (T=car(ex); T; T=cdr(T)) { U = evca(&g,cdar(T));
 if (o2a(caar(T))[8] & 128 || specp(&g,cdr(ex),caar(T))) {
   o2a(r)[2] = cons(&g, cons(&g, caar(T), o2a(caar(T))[4]), o2a(r)[2]);
   o2a(caar(T))[4] = U; U=-8; } U = cons(&g, caar(T), U); NE=cons(&g, U, NE); }
 T = eval_body(&g, cdr(ex)); unwind(f, cdr(dyns)); return T; }
lval eval_progv(void *f, lval ex) { NF(2) lval r=ma(&g,1,84,0); T=evca(&g,ex);
 U=evca(&g,cdr(ex)); dyns=cons(&g, r, dyns); for (; T&&U; T=cdr(T), U=cdr(U)) {
   o2a(r)[2] = cons(&g, cons(&g, car(T), o2a(car(T))[4]), o2a(r)[2]);
   o2a(car(T))[4] = car(U); } T=eval_body(&g, cddr(ex)); unwind(f, cdr(dyns));
 return T; }
lval eval_flet(void *f, lval ex) { NF(4) U=E; for (T=car(ex); T; T=cdr(T)) {
  V=ma(&g,5,212,992,E,cadr(car(T)),cddr(car(T)),caar(T));W=cons(&g,caar(T),16);
  V=cons(&g, W, V); U=cons(&g, V, U); } NE=U; return eval_body(&g, cdr(ex)); }
lval eval_labels(void *f, lval ex) { NF(4) U=E; for (T=car(ex); T; T=cdr(T))
  U = cons(&g, 0, U); NE=U; for (T = car(ex); T; T = cdr(T), U = cdr(U)) {
    V=ma(&g,5,212,992,NE,cadr(car(T)),cddr(car(T)),caar(T)); W=cons(&g,caar(T),16);
    set_car(U, cons(&g, W, V)); } return eval_body(&g, cdr(ex)); }
lval eval_macrolet(void *f, lval ex) { NF(4) U=E; for (T=car(ex); T; T=cdr(T)){
  V=ma(&g,5,212,992,E,cadr(car(T)),cddr(car(T)),caar(T)); W=cons(&g,caar(T),24);
  V=cons(&g, W, V); U = cons(&g, V, U); } NE=U; return eval_body(&g,cdr(ex)); }
lval eval_symbol_macrolet(void *f, lval ex) { NF(3) U=E;
 for (T=car(ex); T; T=cdr(T)) { V=cons(&g,caar(T),8); V=cons(&g,V,cadr(car(T)));
 U = cons(&g, V, U); } NE=U; return eval_body(&g, cdr(ex)); }
lval eval_setq(void *f, lval ex) {
  return *binding(f, car(ex), 0, 0) = evca(f, cdr(ex)); }
lval eval_function(void *f, lval ex) { lval x; ex = car(ex); if (cp(ex))
  if(car(ex)==symi[75].sym) { lval n=0; x=cddr(ex);
  if (!cdr(x) && caar(x) == symi[23].sym) { x=car(x); n=cadr(x); x=cddr(x); }
  return ma(f,5,212,992,E,cadr(ex),x,n); }
  else x = *binding(f, cadr(ex), 2, 0); else x = *binding(f, ex, 1, 0);
 if (x != 8) return x; dbgr(f, 1, ex, &x); return x; }
lval eval_tagbody(void *f, lval ex) { NF(3) jmp_buf jmp; lval tag; lval e;
 V = ms(&g, 1, 52, &jmp); dyns = cons(&g, V, dyns); for (e=ex; e; e=cdr(e))
   if (ap(car(e))) { U = cons(&g, dyns, V);
   NE = cons(&g, cons(&g, cons(&g, car(e), 48), U), NE); } e = ex; again:
     if (!(tag=setjmp(jmp))) {for (;e;e=cdr(e)) if (!ap(car(e))) evca(&g,e); }
     else for (e=ex; e; e=cdr(e)) if (car(e) == tag) { e=cdr(e); goto again; }
     unwind(&g, cdr(dyns)); return 0; }
lval eval_go(void *f, lval ex) { lval b = *binding(f, car(ex), 3, 0);
 if (o2s(cdr(b))[2]) { unwind(f, car(b));
 longjmp(*(jmp_buf*)(o2s(cdr(b))[2]), car(ex)); } dbgr(f, 9, car(ex), &ex);
 longjmp(top_jmp, 1); }
lval eval_block(void *f, lval ex) { NF(2) jmp_buf jmp; lval vs;
 T = ms(&g, 1, 52, &jmp); U = cons(&g, dyns, T); dyns = cons(&g, T, dyns);
 NE=cons(&g, cons(&g, cons(&g, car(ex), 64), U), NE); if (!(vs=setjmp(jmp))) {
   T = eval_body(&g, cdr(ex)); unwind(&g, cdr(dyns)); return T; }
 else return mvalues(car(vs)); }
lval eval_return_from(void *f, lval ex) { NF(1) lval b=*binding(&g,car(ex),4,0);
 jmp_buf *jmp = (jmp_buf*)o2s(cdr(b))[2]; if (jmp) { unwind(&g, car(b));
 T = rvalues(&g, evca(&g, cdr(ex))); longjmp(*jmp, cons(&g, T, 0)); }
 dbgr(&g, 8, car(ex), &T); longjmp(top_jmp, 1); }
lval eval_catch(void *f, lval ex) { NF(2) jmp_buf jmp; lval vs; lval oc = dyns;
 U = evca(&g, ex); T = ms(&g, 1, 20, &jmp); T = cons(&g, U, T);
 dyns = cons(&g, T, dyns); if (!(vs=setjmp(jmp))) vs = eval_body(&g, cdr(ex));
 else vs = mvalues(car(vs)); dyns = oc; return vs; }
lval eval_throw(void *f, lval ex) { NF(1) lval c; T = evca(&g, ex); st:
  for (c = dyns; c; c = cdr(c)) if (cp(car(c)) && caar(c) == T) {
    unwind(&g, c); T = evca(&g, cdr(ex)); T = rvalues(&g, T);
    longjmp(*(jmp_buf*)(o2s(cdar(c))[2]), cons(&g, T, 0)); }
  dbgr(&g, 5, T, &T); goto st; }
lval eval_unwind_protect(void *f, lval ex) { NF(1) T = ma(&g,2,52,E,cdr(ex));
 dyns = cons(&g, T, dyns); T = evca(&g, ex); T = rvalues(&g, T);
 eval_body(&g, cdr(ex)); return mvalues(T); }
lval eval_if(void *f, lval ex) { return evca(f, evca(f,ex)?cdr(ex):cddr(ex)); }
lval append(lval a, lval b) { lval c; if (a) { for (c = a; cdr(c); c = cdr(c));
  set_cdr(c, b); return a; } return b; }
lval eval_multiple_value_call(void *f, lval ex) { NF(3) U=0; T = evca(&g, ex);
  for (ex = cdr(ex); ex; ex = cdr(ex)) { V = evca(&g, ex); V = rvalues(&g, V);
  U = append(U, V); } xvalues = 8; return call(&g, T, U); }
lval eval_multiple_value_prog1(void *f, lval ex) { NF(1) T = evca(&g, ex);
 T = rvalues(&g, T); eval_body(&g, cdr(ex)); return mvalues(T); }
lval eval_declare(void *f, lval ex) { return 0; }
lval l2(void *f, lval a, lval b) { return cons(f, a, cons(f, b, 0)); }
lval eval_setf(void *f, lval ex) { lval r; int m; ag: if (!cp(car(ex))) {
  r = *binding(f, car(ex), 0, &m); if (!m) return *binding(f, car(ex), 0, 0)
   = evca(f, cdr(ex)); set_car(ex, r); goto ag; } r = *binding(f,caar(ex),2,0);
 if (r==8) dbgr(f, 1, l2(f, symi[33].sym, caar(ex)), &r);
 return call(f, r, map_eval(f, cons(f, cadr(ex), cdar(ex)))); }
lval llist(void *f) { return AR; }
lval lvalues(void *f) { return mvalues(AR); }
lval lfuncall(void *f) { return call(f, A0, A0R); }
lval lapply(void *f) { lval fn = A0; lval a = A0R; if (cdr(a)) {
  lval b; for (b = a; cddr(b); b = cdr(b)); set_cdr(b, cadr(b)); }
 else a = car(a); return call(f, fn, a); }
lval leq(void *f) { return A0 == A1 ? TRUE : 0; }
lval lcons(void *f) { return cons(f, A0, A1); }
lval lcar(void *f) { return car(A0); }
lval setfcar(void *f) { return set_car(A1, A0); }
lval lcdr(void *f) { return cdr(A0); }
lval setfcdr(void *f) { return set_cdr(A1, A0); }
lval lequ(void *f) { double s = o2d(A0); lval l = A0R; for (; l; l = cdr(l))
  if (s != o2d(car(l))) return 0; return TRUE; }
lval lless(void *f) { double s = o2d(A0); lval l = A0R; for (; l; l = cdr(l))
  if (s < o2d(car(l))) s = o2d(car(l)); else return 0; return TRUE; }
lval lplus(void *f) { double s = 0; lval l; for (l = AR; l; l = cdr(l))
  s += o2d(car(l)); return d2o(f, s); }
lval lminus(void *f) { double s = o2d(A0); lval l = A0R; if (l)
  for (; l; l = cdr(l)) s -= o2d(car(l)); else s = -s; return d2o(f, s); }
lval ltimes(void *f) { double s = 1; lval l; for (l = AR; l; l = cdr(l))
  s *= o2d(car(l)); return d2o(f, s); }
lval ldivi(void *f) { double s = o2d(A0); lval l = A0R; if (l)
  for (; l; l = cdr(l)) s /= o2d(car(l)); else s = 1/s; return d2o(f, s); }
lval ldpb(void *f) { int s=o2i(car(A1)); int p=o2i(cdr(A1)); int m=(1<<s)-1;
 return d2o(f, (o2i(A0)&m)<<p | (o2i(A2) & ~(m<<p))); }
lval lldb(void *f) { int s = o2i(car(A0)); int p = o2i(cdr(A0));
 return d2o(f, o2i(A1)>>p & ((1<<s)-1)); }
lval lfloor(void *f) { double n = o2d(A0); double d = A0R ? o2d(A1) : 1.0;
 double q = floor(n/d); return mvalues(l2(f, d2o(f, q), d2o(f, n-q*d))); }
lval lvector(void *f) { int l=0; lval e; lval *r; for (e=AR; e; e=cdr(e)) l++;
 r=ma0(f,l); r[1]=116; l=2; for(e=AR;e;e=cdr(e)) r[l++]=car(e); return a2o(r); }
lval lmake_array(void *f) { lval *r = ma0(f, o2i(A0)); r[1] = 116;
 memset(r + 2, 0, 4*o2i(A0)); return a2o(r); }
int gensymc = 0;
lval lgensym(void *f) { lval *r = ms0(f, 4); r[1] = 20; sprintf((char*)(r+2),
  "g%3.3d", gensymc++); return ma(f,9,20,s2o(r),0,8,8,8,-8,16,0,0); }
lval lcode_char(void *f) { unsigned int c = o2u(A0); return c<256 ?32*c+24 :0;}
lval lchar_code(void *f) { return A0&~8; }
lval stringify(void *f, lval l) { int i; lval *r; lval t = l; AR = l;
 for (i=0; t; i++, t=cdr(t)); r = ms0(f, i); r[1] = 20; ((char*)r)[i+8] = 0;
 for (i=8; l; i++, l=cdr(l)) ((char*)r)[i]=car(l) >> 5; return s2o(r); }
lval lstring(void *f) { return stringify(f, AR); }
lval lmake_string(void *f) { lval *r = ms0(f, o2i(A0)); r[1] = 20;
 memset(r + 2, A2>>5, o2i(A0) + 1); return s2o(r); }
lval lival(void *f) { return d2o(f, A0); }
lval lmakei(void *f) { int i=2; lval l=A1R; lval *r=ma0(f, o2i(A0)); r[1]=A1|4;
 memset(r+2,0,4*o2i(A0)); for (; l; l=cdr(l), i++) r[i]=car(l);return a2o(r); }
lval liboundp(void *f) { return o2a(A0)[o2u(A1)]==8?0:TRUE; }
lval limakunbound(void *f) { o2a(A0)[o2u(A1)] = 8; return 0; }
lval liref(void *f) { return o2a(A0)[o2u(A1)] & ~4; }
lval setfiref(void *f) {int i=o2i(A2);return o2a(A1)[i]=i==1?A0|4:A0;}
lval laref(void *f) { lval i=A1; st: if (ap(A0)) { if (o2u(i) >= o2a(A0)[0]>>5)
  {if (dbgr(f, 2, AR, &i)) return i; goto st;} return o2a(A0)[o2u(i)+2]; }
 else {if (o2u(i) >= (o2s(A0)[0]>>3)-4) {if (dbgr(f, 2, AR, &i)) return i;
 goto st;} return o2z(A0)[o2u(i)] << 5 | 24; }}
lval setfaref(void *f) { lval i=A2; st: if (ap(A1)) {if (o2u(i)>=o2a(A1)[0]>>5)
  {if (dbgr(f, 2, AR, &i)) return i; goto st;}
 return o2a(A1)[o2u(i)+2] = A0;} else {if (o2u(i) >= (o2s(A1)[0]>>3)-4)
   {if (dbgr(f, 2, AR, &i)) return i; goto st;} o2z(A1)[o2u(i)] = A0 >> 5;
 return A0;}}
lval llength(void *f) { if (cp(A0)) { int i=0; lval e=A0; for (; e; e = cdr(e))
  i++; return d2o(f, i); } if (ap(A0)) return d2o(f, o2a(A0)[0]>>5);
 return d2o(f, (o2s(A0)[0]>>3)-4); }
lval lsubseq(void *f) { int i = 0; lval e = A0; int s = o2i(A1); lval *r;
 if (cp(A0)) { for (; e; e = cdr(e), i++) if (i >= s) { lval a2 = A2;
 lval t = AR = cons(f, AR, 0); for (; e && (!a2 || i < o2i(a2)); e=cdr(e), i++)
   { s = cons(f, car(e), 0); set_cdr(t, s); t=s; } return cdr(AR); } }
 if (ap(A0)) { e = A2 ? o2i(A2) : o2a(A0)[0] >> 5; r = ma0(f, e-s); r[1] = 116;
 for (i = s; i < e; i++) r[2+i-s] = o2a(A0)[2+i]; return a2o(r); }
 e = A2 ? o2i(A2) : (o2s(A0)[0]>>3)-4; r = ms0(f, e-s); r[1] = 20;
 for (i = s; i < e; i++) ((char*)r)[8+i-s] = o2z(A0)[i]; return s2o(r); }
lval seqiter(lval s) { return cp(s) ? s : 8; }
lval seqcond(lval s, lval i) { return cp(s) ? i : ap(s) ? i/8-1 < o2a(s)[0]>>5
				 : i/8-1 < (o2s(s)[0]>>3)-4; }
lval seqnext(lval s, lval i) { return cp(s) ? cdr(i) : i + 8; }
lval seqval(lval s, lval i) { if (cp(s)) return car(i); if (ap(s))
  return o2a(s)[i/8+1]; return o2z(s)[i/8-1] << 5 | 24; }
lval setfsubseq(void *f) {
  lval q = A0; lval d = seqiter(q); lval e; int i=0; int s = o2i(A2);
  if (cp(A1)) { for (e = A1; e; e = cdr(e), i++) if (i >= s) { lval a3 = A3;
  for (; e && (!a3 || i < o2i(a3)) && seqcond(q, d);
       e = cdr(e), i++, d = seqnext(q, d)) set_car(e, seqval(q, d)); break; }}
  else if (ap(A1)) { e = A3 ? o2i(A3) : o2a(A0)[0] >> 5;
  for (i = s; i < e && seqcond(q, d); i++, d = seqnext(q, d))
    o2a(A1)[2+i] = seqval(q, d); }
  else { e = A3 ? o2i(A3) : (o2s(A0)[0]>>3)-4;
  for (i = s; i < e && seqcond(q, d); i++, d = seqnext(q, d))
    o2z(A1)[i] = seqval(q, d) >> 5; } return A0;}
#ifdef _WIN32
#include <windows.h>
lval lmake_fs(void *f) { HANDLE fd = CreateFile(o2z(A0), A1 ? GENERIC_WRITE :
 GENERIC_READ, A1 ? FILE_SHARE_WRITE : FILE_SHARE_READ, NULL, OPEN_EXISTING,
 FILE_ATTRIBUTE_NORMAL, NULL); return ms(f, 4, 116, 1, fd, A1, 0); }
lval lclose_fs(void *f) { CloseHandle(o2s(A0)[3]); return 0; }
lval llisten_fs(void *f) {
  return WaitForSingleObject(o2s(A0)[3], 0) == WAIT_OBJECT_0 ? TRUE : 0; }
lval lread_fs(void *f) { int l = o2i(A2); if (!ReadFile(o2s(A0)[3], o2z(A1)+l,
 (o2s(A1)[0]>>3)-4 - l, &l, NULL)) return 0; return d2o(f, l); }
lval lwrite_fs(void *f) { int l=o2i(A2); if (!WriteFile(o2s(A0)[3], o2z(A1)+l,
 o2i(A3) - l, &l, NULL)) return 0; return d2o(f, l); }
lval lfinish_fs(void *f) { FlushFileBuffers(o2s(A0)[3]); return 0; }
#else
#include <sys/time.h>
#include <unistd.h>
lval lmake_fs(void *f) { int fd = open(o2z(A0), A1 ? O_WRONLY : O_RDONLY);
 return fd >= 0 ? ms(f, 4, 116, 1, fd, A1, 0) : d2o(f, errno); }
lval lclose_fs(void *f) { close(o2s(A0)[3]); return 0; }
lval llisten_fs(void *f) { fd_set r; struct timeval t; t.tv_sec=0; t.tv_usec=0;
 FD_ZERO(&r); FD_SET(o2s(A0)[3], &r);
 return select(o2s(A0)[3] + 1, &r, NULL, NULL, &t) ? TRUE : 0; }
lval lread_fs(void *f) { int l = o2i(A2); l = read(o2s(A0)[3], o2z(A1) + l,
 (o2s(A1)[0]>>3)-4 - l); return l < 0 ? cons(f, errno, 0) : d2o(f, l); }
lval lwrite_fs(void *f) { int l = o2i(A2); l = write(o2s(A0)[3], o2z(A1) + l,
 o2i(A3) - l); return l < 0 ? cons(f, errno, 0) : d2o(f, l); }
lval lfinish_fs(void *f) { fsync(o2s(A0)[3]); return 0; }
#endif
FILE *ins;
void load(void *f, char *s) { lval r; FILE *oldins = ins; ins = fopen(s, "r");
 if (ins) { do r = eval(f, lread(f)); while (r != 8); fclose(ins); }
 ins = oldins; }
lval lload(void *f) { load(f, o2z(A0)); return symi[1].sym; }
lval lstring_equal(void *f) { return string_equal(A0, A1) ? TRUE : 0; }
lval leval(void *f) { return eval(f, A0); }
void psym(lval p, lval n) { int i; if (!p) printf("#:"); else if (p != pkg) {
  lval m = car(o2a(p)[2]); for (i=0; i<o2s(m)[0]/8-4; i++) putchar(o2z(m)[i]);
  putchar(':'); } for (i = 0; i < o2s(n)[0]/8-4; i++) putchar(o2z(n)[i]); }
void print(lval x) { int i; switch (x & 3) { case 0: if (x) if (x&8)
  if (x>>5 < 256 && isgraph(x>>5)) printf("#\\%c", x>>5);
  else printf("#\\U+%d", x>>5); else printf("%d", x>>5); else printf("nil"); break; case 1: printf("(");
  print(car(x)); for (x=cdr(x); cp(x); x=cdr(x)) {printf(" "); print(car(x));}
  if (x) {printf(" . "); print(x);} printf(")"); break; case 2:
  switch (o2a(x)[1]) {case 212: printf("#<function "); print(o2a(x)[6]);
  printf(">"); break; case 20: psym(o2a(x)[9], o2a(x)[2]); break; case 116:
  printf("#("); for (i = 0; i < o2a(x)[0]>>5; i++) { if (i) printf(" ");
  print(o2a(x)[i+2]);} printf(")"); break; case 180: printf("#<package ");
  print(car(o2a(x)[2])); printf(">"); break; default: printf("#(");
  for (i=0; i <= o2a(x)[0]>>5; i++) print(o2a(x)[i+1]); printf(")"); } break;
  case 3: switch(o2s(x)[1]) { case 20: printf("\"");
  for (i=0; i < o2s(x)[0]/8-4; i++) { char c = o2z(x)[i];
  printf((c=='\\'||c=='\"' ? "\\%c" : "%c"), c);} printf("\""); break;
  case 84: printf("%g", o2d(x)); }}}
lval lprint(void *f) { print(A0); return A0; }
int ep(void *g, lval expr) { int i; lval v = rvalues(g, eval(g, expr));
 if (car(v) == 8) return 0; if (v) for (i = 0; v; v = cdr(v)) {
   printf(";%d: ", i++); print(car(v)); printf("\n"); }
 else printf(";no values\n"); return 1; }
char *exmsg[] = {"variable unbound", "function unbound",
 "array index out of bounds", "go tag not bound", "block name not bound",
 "catch tag not dynamically bound", "too many arguments", "too few arguments",
 "dynamic extent of block exited", "dynamic extent of tagbody exited"};
int dbgr(void *f, int x, lval val, lval *vp) { NF(0) lval ex; int i;
 lval *h=f; int l=0; printf(";exception: %s ", exmsg[x]); if (val) print(val);
  printf("\n;restarts:\n;[t]oplevel\n;[u]se <form> instead\n;[r]eturn <form> from function\n");
  while (1) { lval *j; printf(";%d> ", l);
  ex = lread(&g); if (ex == 8) longjmp(top_jmp, 1);
    if (sp(ex) && o2s(ex)[1] == 84) {
      for (h = f, l = i = o2i(ex); i; i--) { if (!h[2]) break; h = o2a(h[2]); }
    } else if (ap(ex) && o2a(ex)[1] == 20) {
      switch(o2z(o2a(ex)[2])[0]) {
      case 'b': printf(";backtrace:\n"); j = f; for (i = 0; j; i++) {
	printf(";%d: ", i); if(j[0]>>5 == 4) { print(o2a(j[5])[6]);
	printf(" "); print(j[4]);} printf("\n"); if (!j[2]) break; j=o2a(j[2]);
	} break;
      case 'r': *vp = eval(&g, lread(&g)); return 1;
      case 't': longjmp(top_jmp, 1);
      case 'u': *vp = eval(&g, lread(&g)); return 0;
      }
    } else ep(h, ex);
  }
}
lval evca(void *f, lval co) { lval ex=car(co); lval x=ex; int m; ag: xvalues=8;
 if (cp(ex)) { lval fn = 8; if (ap(car(ex)) && o2a(car(ex))[1] == 20) {
   fn = *binding(f, car(ex), 1, &m); if (m) { x = ex = call(f, fn, cdr(ex));
   set_car(co, ex); goto ag; }} st: if (fn==8) { if (dbgr(f,1,car(ex),&fn))
     return fn; else goto st; } ex = cdr(ex); if (o2a(fn)[2]>>3 < 34)
       return symi[o2a(fn)[2]>>3].fun(f, ex);
 ex = call(f, fn, map_eval(f, ex)); } else if (ap(ex) && o2a(ex)[1] == 20) {
   ex = *binding(f, ex, 0, &m); if (m) { x = ex; set_car(co, ex); goto ag; }
   if (ex == 8) dbgr(f, 0, x, &ex); } return ex == -8 ? o2a(x)[4] : ex; }
int getnws() { int c; do c = getc(ins); while (isspace(c)); return c; }
lval read_list(void *f) { NF(1) int c = getnws(); if (c == ')') return 0;
  if (c == '.') { lval r = lread(&g); getnws(); return r; }
  ungetc(c, ins); T = lread(&g); return cons(&g, T, read_list(&g)); }
lval read_string_list(void *g) {
  int c = getc(ins); if (c == '\"') return 0; if (c == '\\') c = getc(ins);
  return cons(g, (c << 5) | 24, read_string_list(g)); }
lval is(void *g, lval p, lval s) { lval m = o2a(p)[3]; for (; m; m=cdr(m)) {
  lval y=car(m); if (string_equal(o2a(y)[2], s)) return o2a(y)[7] ? y : 0; }
 m=ma(g, 9, 20, s, o2a(p)[3], 8, 8, 8, -8, 16, p, 0); if (p==kwp) o2a(m)[4]=m;
 o2a(p)[3] = cons(g, m, o2a(p)[3]); return m; }
lval read_symbol(void *g) { int c=getc(ins); if (isspace(c)||c==')'||c==EOF) {
  if (c!=EOF) ungetc(c, ins); return 0; }
 return cons(g, (c << 5) | 24, read_symbol(g)); }
lval list2(void *g, int a) { return l2(g, symi[a].sym, lread(g)); }
lval lread(void *g) { int c = getnws(); if (c == EOF) return 8; if (c == '(')
  return read_list(g); if (c == '\"') return stringify(g, read_string_list(g));
 if (c == '\'') return list2(g, 12); if (c == '#') { c=getnws(); if (c == '\'')
   return list2(g, 20); return 0; } if (c=='`') return list2(g,38); if (c==',')
     { c = getnws(); if (c == '@') return list2(g,40); ungetc(c,ins);
     return list2(g,39); } ungetc(c,ins); if (isdigit(c)) { double d;
     fscanf(ins, "%lf", &d); return d2o(g, d); } if (c==':') getnws();
     return is(g, c==':' ? kwp : pkg, stringify(g, read_symbol(g))); }
lval strf(void *f, const char *s) { int j = strlen(s); lval *str = ms0(f, j);
 str[1] = 20; for (j++; j; j--) ((char*)str)[7+j] = s[j-1]; return s2o(str); }
int main(int argc, char *argv[]) { struct { void *f; lval v[3]; } g = {0,{1}};
 int i; lval sym;
  memory_size = 2048*1024; memory = malloc(memory_size); memf = memory;
  memset(memory, 0, memory_size); memf[0] = 0; memf[1] = memory_size / 4;
  pkg = ma(&g, 3, 180, l2(&g, strf(&g, "cl"), strf(&g, "common-lisp")), 0, 0);
  for (i=0; i < 85; i++) { sym = is(&g, pkg, strf(&g, symi[i].name));
  if (i < 10) o2a(sym)[4] = sym; ins = stdin; symi[i].sym = sym;
  o2a(sym)[5] = ma(&g, 5, 212, i << 3, 0, 0, 0, sym); if (symi[i].setfun)
    o2a(sym)[6] = ma(&g, 5, 212, i<<3, 8, 0, 0, sym); o2a(sym)[7]=i<<3; }
  kwp = ma(&g, 3, 180, l2(&g, strf(&g, ""), strf(&g, "keyword")), 0, 0);
  o2a(symi[81].sym)[4] = pkgs = l2(&g, kwp, pkg);
#ifdef _WIN32
  o2a(symi[78].sym)[4] = ms(&g,3,116,1,GetStdHandle(STD_INPUT_HANDLE),0,0);
  o2a(symi[79].sym)[4] =ms(&g,3,116,1,GetStdHandle(STD_OUTPUT_HANDLE),TRUE,0);
  o2a(symi[80].sym)[4] =ms(&g,3,116,1,GetStdHandle(STD_ERROR_HANDLE),TRUE,0);
#else
  o2a(symi[78].sym)[4] = ms(&g, 3, 116, 1, 0, 0, 0);
  o2a(symi[79].sym)[4] = ms(&g, 3, 116, 1, 1, TRUE, 0);
  o2a(symi[80].sym)[4] = ms(&g, 3, 116, 1, 2, TRUE, 0);
#endif
  for (i=1; i<argc; i++) load(&g,argv[i]); printf("\t ___\t _,.--.,_\n      .-"
"~   ~--\"~-.   ._ \"-.\n     /      ./_    Y\t\"-. \\\n    Y\t    :~     !\t "
"    Y\n    lq p    |\t  /\t    .|\n _   \\. .-, l\t /\t    |j\n()\\___) |/   "
"\\_/\";\t    !\n \\._____.-~\\  .  ~\\.\t  ./\n\t    Y_ Y_. \"vr\"~  T\n\t   "
" (  (    |L    j\n\t    [nn[nn..][nn..]\n"); setjmp(top_jmp); do printf("? ");
 while (ep(&g, lread(&g))); return 0; }
struct symbol_init symi[] = {{"nil"}, {"t"}, {"&rest"}, {"&body"},
{"&optional"}, {"&key"}, {"&whole"}, {"&environment"}, {"&aux"},
{"&allow-other-keys"}, {"declare", eval_declare, -1}, {"special"},
{"quote", eval_quote, 1}, {"let", eval_let, -2}, {"let*", eval_letm, -2},
{"flet",eval_flet,-2},{"labels",eval_labels,-2},{"macrolet",eval_macrolet,-2},
{"symbol-macrolet", eval_symbol_macrolet, -2}, {"setq", eval_setq, 2},
{"function",eval_function,1}, {"tagbody",eval_tagbody,-1}, {"go",eval_go,1},
{"block", eval_block, -2}, {"return-from", eval_return_from, 2},
{"catch", eval_catch, -2}, {"throw", eval_throw, -2},
{"unwind-protect", eval_unwind_protect, -2}, {"if", eval_if, -3},
{"multiple-value-call", eval_multiple_value_call, -2},
{"multiple-value-prog1",eval_multiple_value_prog1,-2}, {"progn",eval_body,-1},
{"progv", eval_progv, -3}, {"setf", eval_setf, 2},
{"finish-file-stream", lfinish_fs, 1},{"makei",lmakei,2},{"dpb", ldpb, 3},
{"ldb", lldb, 2}, {"backquote"}, {"unquote"}, {"unquote-splicing"},
{"iboundp",liboundp,2},{"listen-file-stream",llisten_fs, 1},{"list",llist,-1},
{"values", lvalues, -1},
{"funcall",lfuncall,-2}, {"apply",lapply,-2}, {"eq",leq,2}, {"cons",lcons,2},
{"car", lcar, 1, setfcar, 2}, {"cdr", lcdr, 1, setfcdr, 2}, {"=", lequ, -2},
{"<", lless, -2}, {"+", lplus, -1}, {"-", lminus, -2}, {"*", ltimes, -1},
{"/", ldivi, -2}, {"make-file-stream", lmake_fs, 2}, {"vector", lvector, -1},
{"make-array",lmake_array,1}, {"gensym",lgensym,0}, {"string",lstring,-1},
{"make-string", lmake_string, 1}, {"aref", laref, -3, setfaref, -3},
{"length", llength, 1}, {"subseq", lsubseq, -3, setfsubseq, -3},
{"print", lprint, 1}, {"gc", gc, 0}, {"close-file-stream", lclose_fs, 1},
{"ival", lival, 1}, {"floor", lfloor, 1}, {"read-file-stream", lread_fs, 1},
{"write-file-stream", lwrite_fs, 2}, {"load", lload, 1},
{"iref", liref, 2, setfiref, 3}, {"lambda"}, {"code-char", lcode_char, 1},
{"char-code", lchar_code, 1},{"*standard-input*"}, {"*standard-output*"},
{"*error-output*"},{"*packages*"},{"string=",lstring_equal,2},
{"imakunbound",limakunbound,2},{"eval",leval,1}};
