#include <ctype.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int lval;
lval *o2c(lval o) { return (lval*)(o - 1); }
lval c2o(lval *c) { return (lval)c + 1; }
int cp(lval o) { return (o & 3) == 1; }
lval *o2a(lval o) { return (lval*)(o - 2); }
lval a2o(lval *a) { return (lval)a + 2; }
int ap(lval o) { return (o & 3) == 2; }
lval *o2s(lval o) { return (lval*)(o - 3); }
char *o2z(lval o) { return (char*)(o - 3 + 2*sizeof(lval)); }
lval s2o(lval *s) { return (lval)s + 3; }
int sp(lval o) { return (o & 3) == 3; }
struct symbol_init { const char *name; lval (*fun)(); int argc;
  lval (*setfun)(); int setargc; lval sym; };
extern struct symbol_init symbol_inits[];
#define TRUE symbol_inits[1].sym
#define T g[4]
#define U g[5]
#define V g[6]
#define W g[7]
#define NF(n) lval g[n+4] = {(n+2)<<5,44,a2o(f),f[3]};
#define E f[3]
#define NE g[3]
#define AR f[4]
#define A0 car(f[4])
#define A0R cdr(f[4])
#define A1 car(cdr(f[4]))
#define A2 car(cddr(f[4]))
#define A3 cadr(cddr(f[4]))
lval car(lval c) { return (c & 3) == 1 ? o2c(c)[0] : 0; }
lval cdr(lval c) { return (c & 3) == 1 ? o2c(c)[1] : 0; }
lval caar(lval c) { return car(car(c)); }
lval cdar(lval c) { return cdr(car(c)); }
lval cadr(lval c) { return car(cdr(c)); }
lval cddr(lval c) { return cdr(cdr(c)); }
lval set_car(lval c, lval val) { return o2c(c)[0] = val; }
lval set_cdr(lval c, lval val) { return o2c(c)[1] = val; }
lval *binding(lval *f, lval sym, int type, int *macro) { lval env; st:
  for (env = E; env; env = cdr(env)) { lval e = caar(env);
  if (type || cp(e) ? car(e) == sym && (cdr(e) >> 4) == type : e == sym) {
    if (macro) *macro = cp(e) && cdr(e) & 8; return o2c(car(env))+1; }}
  if (macro) *macro = (o2a(sym)[8] >> type) & 1; if (type > 2) {
    debugger(f, type, sym, &sym); goto st; } return o2a(sym)+4+type; }
lval lread(lval *); lval eval(lval *, lval); lval evca(lval *, lval);
lval call(lval *, lval, lval); void print(lval);
lval xvalues = 8; lval symbols = 0; lval dyns = 0; jmp_buf top_jmp;
void gcm(lval v) { lval p = 0, n, *t; int l; adv: t = (lval*)(v&~3);
 if (v & 3 && !(t[0] & 4)) { t[0] |= 4; switch (v & 3) {
 case 1: n = t[1]; t[1] = p + 4; p = v + 4; v = n; goto adv;
 case 2: t[1] &= ~4; l=t[0]>>5; n=t[l+1]; t[l+1]=p; p=v+4*(l+1); v=n; goto adv;
 }} retr: if (!p) return; n = v; v = p; t = (lval*)(v&~3); p = t[0];
 if (t[-1] & 4) if (p & 4) { t[0]=n; n=t[-1]; t[-1]=p-4; p=v; v=n; goto adv; }
 else { t[-1] = n+4; v -= 4; p -= 4; goto retr; } t[0] = n; if (t[-2] & 4) {
   t[-1] += 4; v -= 8; goto retr; } n=t[-1]; t[-1]=p; p=v-4; v=n; goto adv; }
lval *memory; lval *memf; int memory_size;
lval gc(lval *f) { int i; lval *m; int l; int u = 0; int ml;
  printf(";garbage collecting...\n"); while (memf) { lval *n = (lval*)memf[0];
  memf[0]=0; memf[1]=0; memf=(lval*)n; } gcm(xvalues); gcm(symbols); gcm(dyns);
  for (; f[2]; f = o2a(f[2])) for (i = 1; i < f[0]>>5; i++) gcm(f[i+2]);
  memf = 0; m = memory; while (m < memory + memory_size/4) {
    l = (m[1] & 4 ? m[0] >> 5 : 0) + 1 & ~1; if (m[0] & 4) { if (u) {
      m[-ml] = (lval)memf; m[1-ml] = ml; memf = m-ml; u = 0; }} else {
	if (!u) ml = 0; ml += l + 2; u = 1; } m[0] &= ~4; m += l + 2; }
  if (u) { m[-ml] = (lval)memf; m[1-ml] = ml; memf = m-ml; }
  printf(";done.\n"); return 0; }
lval *m0(lval *g, int n) { lval *m = memf; lval *p = 0; n = (n + 1) & ~1;
  for (; m; m = (lval*)m[0]) { if (n <= m[1]) { if (m[1]==n && p) p[0] = m[0];
  else { m[1] -= n; m += m[1]; } return m; } p = m; } return 0; }
lval *ma0(lval *g, int n) { lval *m; st: m = m0(g, n+2);
 if (!m) { gc(g); goto st; } *m = n<<5; return m; }
lval *ms0(lval *g, int n) { lval *m; st: m = m0(g, (n+11)/4);
 if (!m) { gc(g); goto st; } *m = (n+3)<<3; return m; }
lval ma(lval *g,int n,...) { va_list v; int i; lval *m; st: va_start(v, n);
 m = m0(g,n+2); if (!m) { for (i=-1; i<n; i++) gcm(va_arg(v, lval)); goto st; }
 *m = n<<5; for (i=-1; i < n; i++) m[2 + i] = va_arg(v, lval); return a2o(m); }
double o2d(lval o) { return *(double*)(o2s(o) + 2); }
lval d2o(lval *g, double d) { lval *a = ma0(g, 2); a[1] = 36;
 *(double*)(a+2) = d; return s2o(a); }
int o2i(lval o) { return (int)o2d(o); }
unsigned o2u(lval o) { return (unsigned)o2d(o); }
lval cons(lval *g, lval a, lval d) { lval *c = m0(g, 2); if (!c) { gcm(a);
 gcm(d); gc(g); c = m0(g, 2); } c[0] = a; c[1] = d; return c2o(c); }
lval args(lval *f, lval env, lval form, lval act) { NF(2) print(form); st:
  U = cons(g, form, act); while (form) { if (o2a(car(form))[7]==2<<3) {
    T=cons(g,cadr(form),act); return cons(g,T,env); }
  if (!act) { debugger(g, 7, U, &act); form = car(U); goto st; }
  T = cons(g, car(form), car(act)); env = cons(g, T, env); form = cdr(form);
  act = cdr(act); } if (act) { debugger(g, 6, U, &act); form = car(U);
  goto st; } return env; }
lval eval_body(lval *f, lval ex) { NF(1) T=0;
 for (; ex; ex=cdr(ex)) T = evca(g, ex); return T; }
lval map_eval(lval *f, lval ex) { NF(1) if (ex) { T = evca(g, ex);
 return cons(g, T, map_eval(g, cdr(ex))); } else return 0; }
lval eval_quote(lval *g, lval ex) { return car(ex); }
int specp(lval *f, lval ex, lval s) { for (; ex; ex = cdr(ex))
  if (ap(caar(ex)) && o2a(caar(ex))[7] == 3<<3) { lval e = cdar(ex);
  for (; e; e = cdr(e)) if (o2a(caar(e))[7] == 4<<3) { lval sp = cdar(e);
  for (; sp; sp=cdr(sp)) if (car(sp) == s) return 1; }} else break; return 0; }
void unwind(lval *f, lval c) { NF(0) lval e; for (; dyns != c; dyns=cdr(dyns))
  if (ap(car(dyns))) if (o2a(car(dyns))[1] == 20) { NE=o2a(car(dyns))[2];
  eval_body(g,o2a(car(dyns))[3]); } else for (e=o2a(car(dyns))[2]; e; e=cdr(e))
    o2a(caar(e))[4] = cdar(e); }
lval eval_let(lval *f, lval ex) { NF(3) lval r = ma(g, 1, 28, 0); U=E;
 dyns = cons(g, r, dyns); for (T=car(ex); T; T=cdr(T)) { V = evca(g, cdar(T));
 if (o2a(caar(T))[8] & 32 || specp(g,cdr(ex),caar(T))) {
   o2a(r)[2] = cons(g, cons(g, caar(T), V), o2a(r)[2]); }
 else U = cons(g, cons(g, caar(T), V), U); } for (r = o2a(r)[2]; r; r=cdr(r)) {
   T = o2a(caar(r))[4]; o2a(caar(r))[4] = cdar(r); set_cdr(car(r), T);
   U = cons(g, cons(g,caar(r),-8), U); } NE = U; T = eval_body(g, cdr(ex));
   unwind(f, cdr(dyns)); return T; }
lval eval_letm(lval *f, lval ex) { NF(2) lval r = ma(g, 1, 28, 0);
 dyns = cons(g, r, dyns); for (T=car(ex); T; T=cdr(T)) { U = evca(g, cdar(T));
 if (o2a(caar(T))[8] & 32 || specp(g,cdr(ex),caar(T))) {
   o2a(r)[2] = cons(g, cons(g, caar(T), o2a(caar(T))[4]), o2a(r)[2]);
   o2a(caar(T))[4] = U; U=-8; } U = cons(g, caar(T), U); NE = cons(g, U, NE); }
 T = eval_body(g, cdr(ex)); unwind(f, cdr(dyns)); return T; }
lval eval_flet(lval *f, lval ex) { NF(4) U=E; for (T=car(ex); T; T=cdr(T)) {
  V=ma(g,5,4,992,E,cadr(car(T)),cddr(car(T)),caar(T)); W=cons(g,caar(T),16);
  V = cons(g, W, V); U = cons(g, V, U); } NE=U; return eval_body(g, cdr(ex)); }
lval eval_labels(lval *f, lval ex) { NF(4) U=E; for (T=car(ex); T; T=cdr(T))
  U = cons(g, 0, U); NE=U; for (T = car(ex); T; T = cdr(T), U = cdr(U)) {
    V=ma(g,5,4,992,NE,cadr(car(T)),cddr(car(T)),caar(T)); W=cons(g,caar(T),16);
    set_car(U, cons(g, W, V)); } return eval_body(g, cdr(ex)); }
lval eval_macrolet(lval *f, lval ex) { NF(4) U=E; for (T=car(ex); T; T=cdr(T)){
  V=ma(g,5,4,992,E,cadr(car(T)),cddr(car(T)),caar(T)); W=cons(g,caar(T),24);
  V = cons(g, W, V); U = cons(g, V, U); } NE=U; return eval_body(g, cdr(ex)); }
lval eval_symbol_macrolet(lval *f, lval ex) { NF(2) U=E;
 for (T=car(ex); T; T=cdr(T)) { V=cons(g,caar(T),8); V=cons(g,V,cadr(car(T)));
 U = cons(g, V, U); } NE=U; return eval_body(g, cdr(ex)); }
lval eval_setq(lval *f, lval ex) {
  return *binding(f, car(ex), 0, 0) = evca(f, cdr(ex)); }
lval eval_function(lval *f, lval ex) { ex = car(ex); if (cp(ex))
  return ma(f,5,4,992,E,cadr(ex),cddr(ex),0); return *binding(f, ex, 1, 0); }
lval rvalues(lval *g, lval v) { return xvalues==8 ? cons(g, v, 0) : xvalues; }
lval mvalues(lval a) { xvalues = a; return car(a); }
lval eval_tagbody(lval *f, lval ex) { NF(3) jmp_buf jmp; lval tag; lval e;
 V = ma(g, 1, 20, &jmp) + 1; for (e = ex; e; e = cdr(e)) if (ap(car(e))) {
   U = cons(g, dyns, V); T = cons(g, car(e), 48); T = cons(g, T, U);
   NE = cons(g, T, NE); } e = ex; again: if (!(tag = setjmp(jmp))) {
     for (;e;e=cdr(e)) if (!ap(car(e))) evca(g,e); } else for (e=ex;e;e=cdr(e))
       if (car(e) == tag) { e = cdr(e); goto again; } return 0; }
lval eval_go(lval *f, lval ex) { lval b = *binding(f, car(ex), 3, 0);
 unwind(f, car(b)); longjmp(*(jmp_buf*)(o2s(cdr(b))[2]), car(ex)); }
lval eval_block(lval *f, lval ex) { NF(2) jmp_buf jmp; lval vs;
 T = ma(g, 1, 20, &jmp) + 1; T = cons(g, dyns, T); U = cons(g, car(ex), 64); 
 T = cons(g, U, T); NE = cons(g, T, NE); if (!(vs = setjmp(jmp)))
   return eval_body(g, cdr(ex)); else return mvalues(car(vs)); }
lval eval_return_from(lval *f, lval ex) { NF(1) lval b=*binding(g,car(ex),4,0);
 unwind(g, car(b)); T = evca(g, cdr(ex)); T = rvalues(g, T);
 longjmp(*(jmp_buf*)(o2s(cdr(b))[2]), cons(g, T, 0)); }
lval eval_catch(lval *f, lval ex) { NF(2) jmp_buf jmp; lval vs; lval oc = dyns;
 U = evca(g, ex); T = ma(g, 1, 20, &jmp) + 1; T = cons(g, U, T);
 dyns = cons(g, T, dyns); if (!(vs = setjmp(jmp))) vs = eval_body(g, cdr(ex));
 else vs = mvalues(car(vs)); dyns = oc; return vs; }
lval eval_throw(lval *f, lval ex) { NF(1) lval c; T = evca(g, ex); st:
  for (c = dyns; c; c = cdr(c)) if (cp(car(c)) && caar(c) == T) {
    unwind(g, c); T = evca(g, cdr(ex)); T = rvalues(g, T);
    longjmp(*(jmp_buf*)(o2s(cdar(c))[2]), cons(g, T, 0)); }
  debugger(g, 5, T, &T); goto st; }
lval eval_unwind_protect(lval *f, lval ex) { NF(1) T = ma(g,2,20,E,cdr(ex));
 dyns = cons(g, T, dyns); T = evca(g, ex); T = rvalues(g, T);
 eval_body(g, cdr(ex)); return mvalues(T); }
lval eval_if(lval *f, lval ex) { return evca(f, evca(f,ex)?cdr(ex):cddr(ex)); }
lval append(lval a, lval b) { lval c; if (a) { for (c = a; cdr(c); c = cdr(c));
  set_cdr(c, b); return a; } return b; }
lval eval_multiple_value_call(lval *f, lval ex) { NF(2) U = 0; T = evca(g, ex);
  for (ex = cdr(ex); ex; ex = cdr(ex)) { V = evca(g, ex); V = rvalues(g, V);
  U = append(U, V); } xvalues = 8; return call(g, T, U); }
lval eval_multiple_value_prog1(lval *f, lval ex) { NF(1) T = evca(g, ex);
 T = rvalues(g, T); eval_body(g, cdr(ex)); return mvalues(T); }
lval eval_defun(lval *f, lval ex) { o2a(car(ex))[5] =
  ma(f, 5, 4, 992, E, cadr(ex), cddr(ex), car(ex)); return car(ex); }
lval eval_defmacro(lval *f, lval ex) { o2a(car(ex))[5] = ma(f, 5, 4, 992, E,
  cadr(ex), cddr(ex), car(ex)); o2a(car(ex))[8] |= 2; return car(ex); }
lval eval_define_symbol_macro(lval *f, lval ex) {
  o2a(car(ex))[4] = cadr(ex); o2a(car(ex))[8] |= 1; return car(ex); }
lval eval_defvar(lval *f, lval ex) { if (o2a(car(ex))[4] == 8 && cdr(ex))
  o2a(car(ex))[4] = evca(f, cdr(ex)); o2a(car(ex))[8] |= 32; return car(ex); }
lval eval_defparameter(lval *f, lval ex) { o2a(car(ex))[4] = evca(f, cdr(ex));
 o2a(car(ex))[8] |= 32; return car(ex); }
lval eval_declare(lval *f, lval ex) { return 0; }
lval eval_setf(lval *f, lval ex) { lval b = *binding(f, caar(ex), 2, 0);
 return call(f, b, map_eval(f, cons(f, cadr(ex), cdar(ex)))); }
lval lvalues(lval *f) { return mvalues(AR); }
lval lfuncall(lval *f) { return call(f, A0, A0R); }
lval lapply(lval *f) { lval fn = A0; lval a = A0R; if (cdr(a)) {
  lval b; for (b = a; cddr(b); b = cdr(b)); set_cdr(b, cadr(b)); }
 else a = car(a); return call(f, fn, a); }
lval leq(lval *f) { return A0 == A1 ? TRUE : 0; }
lval lcons(lval *f) { return cons(f, A0, A1); }
lval lcar(lval *f) { return car(A0); }
lval setfcar(lval *f) { return set_car(A1, A0); }
lval lcdr(lval *f) { return cdr(A0); }
lval setfcdr(lval *f) { return set_cdr(A1, A0); }
lval lequ(lval *f) { double s = o2d(A0); lval l = A0R; for (; l; l = cdr(l))
  if (s != o2d(car(l))) return 0; return TRUE; }
lval lless(lval *f) { double s = o2d(A0); lval l = A0R; for (; l; l = cdr(l))
  if (s < o2d(car(l))) s = o2d(car(l)); else return 0; return TRUE; }
lval lplus(lval *f) { double s = 0; lval l; for (l = AR; l; l = cdr(l))
  s += o2d(car(l)); return d2o(f, s); }
lval lminus(lval *f) { double s = o2d(A0); lval l = A0R; if (l)
  for (; l; l = cdr(l)) s -= o2d(car(l)); else s = -s; return d2o(f, s); }
lval ltimes(lval *f) { double s = 1; lval l; for (l = AR; l; l = cdr(l))
  s *= o2d(car(l)); return d2o(f, s); }
lval ldivi(lval *f) { double s = o2d(A0); lval l = A0R; if (l)
  for (; l; l = cdr(l)) s /= o2d(car(l)); else s = 1/s; return d2o(f, s); }
lval larrayp(lval *f) { return ap(A0) && o2a(A0)[1] == 36
			  || sp(A0) && o2s(A0)[1] == 4 ? TRUE : 0; }
lval lvector(lval *f) { int l=0; lval e; lval *r; for (e=AR; e; e=cdr(e)) l++;
 r=ma0(f,l); r[1]=36; l=2; for(e=AR;e;e=cdr(e)) r[l++]=car(e); return a2o(r); }
lval lmake_array(lval *f) { lval *r = ma0(f, o2i(A0)); r[1] = 36;
 memset(r + 2, 0, 4*o2i(A0)); return a2o(r); } 
lval lstringp(lval *f) { return sp(A0) && o2s(A0)[1] == 4 ? TRUE : 0; }
lval lstring(lval *f) { return stringify(f, AR); }
lval lmake_string(lval *f) { lval *r = ms0(f, o2i(A0)); r[1] = 4;
 memset(r + 2, 0, o2i(A0)); return s2o(r); }
lval laref(lval *f) { lval i=A1; st: if (ap(A0)) { if (o2u(i) >= o2a(A0)[0]>>5)
  {if (debugger(f, 2, AR, &i)) return i; goto st;} return o2a(A0)[o2u(i)+2]; }
 else {if (o2u(i) >= (o2s(A0)[0]>>3)-3) {if (debugger(f, 2, AR, &i)) return i;
 goto st;} return o2z(A0)[o2u(i)] << 5 | 24; }}
lval setfaref(lval *f) { lval i=A2; st: if (ap(A1)) {if (o2u(i)>=o2a(A1)[0]>>5)
  {if (debugger(f, 2, AR, &i)) return i; goto st;}
 return o2a(A1)[o2u(i)+2] = A0;} else {if (o2u(i) >= (o2s(A1)[0]>>3)-3)
   {if (debugger(f, 2, AR, &i)) return i; goto st;} o2z(A1)[o2u(i)] = A0 >> 5;
 return A0;}}
lval llength(lval *f) { if (cp(A0)) { int i=0; lval e=A0; for (; e; e = cdr(e))
  i++; return d2o(f, i); } if (ap(A0)) return d2o(f, o2a(A0)[0]>>5);
 return d2o(f, (o2s(A0)[0]>>3)-3); }
lval lsubseq(lval *f) { int i = 0; lval e = A0; int s = o2i(A1); lval *r;
 if (cp(A0)) { for (; e; e = cdr(e), i++) if (i >= s) { lval a2 = A2;
 lval t = AR = cons(f, AR, 0); for (; e && (!a2 || i < o2i(a2)); e=cdr(e), i++)
   { s = cons(f, car(e), 0); set_cdr(t, s); t=s; } return cdr(AR); } }
 if (ap(A0)) { e = A2 ? o2i(A2) : o2a(A0)[0] >> 5; r = ma0(f, e-s); r[1] = 36;
 for (i = s; i < e; i++) r[2+i-s] = o2a(A0)[2+i]; return a2o(r); }
 e = A2 ? o2i(A2) : (o2s(A0)[0]>>3)-3; r = ms0(f, e-s); r[1] = 4;
 for (i = s; i < e; i++) ((char*)r)[8+i-s] = o2z(A0)[i]; return s2o(r); }
lval seqiter(lval s) { return cp(s) ? s : 8; }
lval seqcond(lval s, lval i) { return cp(s) ? i : ap(s) ? i/8-1 < o2a(s)[0]>>5
				 : i/8-1 < (o2s(s)[0]>>3)-3; }
lval seqnext(lval s, lval i) { return cp(s) ? cdr(i) : i + 8; }
lval seqval(lval s, lval i) { if (cp(s)) return car(i); if (ap(s))
  return o2a(s)[i/8+1]; return o2z(s)[i/8-1] << 5 | 24; }
lval setfsubseq(lval *f) {
  lval q = A0; lval d = seqiter(q); lval e; int i; int s = o2i(A2);
  if (cp(A1)) { for (e = A1; e; e = cdr(e), i++) if (i >= s) { lval a3 = A3;
  for (; e && (!a3 || i < o2i(a3)) && seqcond(q, d);
       e = cdr(e), i++, d = seqnext(q, d)) set_car(e, seqval(q, d)); break; }}
  else if (ap(A1)) { e = A3 ? o2i(A3) : o2a(A0)[0] >> 5;
  for (i = s; i < e && seqcond(q, d); i++, d = seqnext(q, d))
    o2a(A1)[2+i] = seqval(q, d); }
  else { e = A3 ? o2i(A3) : (o2s(A0)[0]>>3)-3;
  for (i = s; i < e && seqcond(q, d); i++, d = seqnext(q, d))
    o2z(A1)[i] = seqval(q, d) >> 5; } return A0;}
lval lprint(lval *f) { print(A0); return A0; }
struct symbol_init symbol_inits[] = {
  {"nil", 0, 0},
  {"t", 0, 0},
  {"&rest", 0, 0},
  {"declare", eval_declare, 0},
  {"special", 0, 0},
  {"quote", eval_quote, 1},
  {"let", eval_let, -2},
  {"let*", eval_letm, -2},
  {"flet", eval_flet, -2},
  {"labels", eval_labels, -2},
  {"macrolet", eval_macrolet, -2},
  {"symbol-macrolet", eval_symbol_macrolet, -2},
  {"setq", eval_setq, 2},
  {"function", eval_function, 1},
  {"tagbody", eval_tagbody, -1},
  {"go", eval_go, 1},
  {"block", eval_block, -2},
  {"return-from", eval_return_from, 2},
  {"catch", eval_catch, -2},
  {"throw", eval_throw, -2},
  {"unwind-protect", eval_unwind_protect, -2},
  {"if", eval_if, -3},
  {"multiple-value-call", eval_multiple_value_call, -2},
  {"multiple-value-prog1", eval_multiple_value_prog1, -2},
  {"progn", eval_body, -1},
  {"defun", eval_defun, -3},
  {"defmacro", eval_defmacro, -3},
  {"define-symbol-macro", eval_define_symbol_macro, 2},
  {"defvar", eval_defvar, -3},
  {"defparameter", eval_defparameter, 2},
  {"setf", eval_setf, 2},
  {"values", lvalues, -1},
  {"funcall", lfuncall, -2},
  {"apply", lapply, -2},
  {"eq", leq, 2},
  {"cons", lcons, 2},
  {"car", lcar, 1, setfcar, 2},
  {"cdr", lcdr, 1, setfcdr, 2},
  {"=", lequ, -2},
  {"<", lless, -2},
  {"+", lplus, -1},
  {"-", lminus, -2},
  {"*", ltimes, -1},
  {"/", ldivi, -2},
  {"arrayp", larrayp, 1},
  {"vector", lvector, -1},
  {"make-array", lmake_array, 1},
  {"stringp", lstringp, 1},
  {"string", lstring, -1},
  {"make-string", lmake_string, 1},
  {"aref", laref, -3, setfaref, -3},
  {"length", llength, 1},
  {"subseq", lsubseq, -3, setfsubseq, -3},
  {"print", lprint, 1},
  {"gc", gc, 0}
};
void ep(lval *g, lval expr) { int i; lval v = rvalues(g, eval(g, expr));
  if (v) for (i = 0; v; v = cdr(v)) { printf(";%d: ", i++); print(car(v));
  printf("\n"); } else printf(";no values\n"); }
char *exmsg[] = {"variable unbound", "function unbound",
 "array index out of bounds", "go tag not bound", "block name not bound",
 "catch tag not dynamically bound", "too many arguments", "too few arguments"};
int debugger(lval *f, int x, lval val, lval *vp) { NF(0) lval ex; int i;
 lval *h=f; int l=0; printf(";exception: %s ", exmsg[x]); if (val) print(val);
  printf("\n;restarts:\n;[t]oplevel\n;[u]se <form> instead\n;[r]eturn <form> from function\n");
  while (1) { lval *j; printf(";%d> ", l);
    ex = lread(g); if (sp(ex) && o2s(ex)[1] == 36) {
      for (h = f, l = i = o2d(ex); i; i--) { if (!h[2]) break; h = o2a(h[2]); }
    } else if (ap(ex) && o2a(ex)[1] == 12) {
      switch(o2z(o2a(ex)[2])[0]) {
      case 'b': printf(";backtrace:\n"); j = f; for (i = 0; j; i++) {
	printf(";%d: ", i); if(j[0]>>5 == 4) { print(o2a(j[5])[6]);
	printf(" "); print(j[4]);} printf("\n"); if (!j[2]) break; j=o2a(j[2]);
	} break;
      case 'r': *vp = eval(g, lread(g)); return 1;
      case 't': longjmp(top_jmp, 1);
      case 'u': *vp = eval(g, lread(g)); return 0;
      }
    } else ep(h, ex);
  }
}
lval call(lval *f, lval fn, lval a) { NF(2) g[4] = a; g[5] = fn;
 if (o2a(fn)[2] == 992) { NE = args(g, o2a(fn)[3], o2a(fn)[4], a);
 return eval_body(g, o2a(fn)[5]); } else return o2a(fn)[3]
 ? symbol_inits[o2a(fn)[2]>>3].setfun(g) : symbol_inits[o2a(fn)[2]>>3].fun(g);}
lval evca(lval *f, lval co) { lval ex=car(co); lval x=ex; int m; ag: xvalues=8;
 if (cp(ex)) {  lval fn = *binding(f, car(ex), 1, &m); if (m) {
   x = ex = call(f, fn, cdr(ex)); set_car(co, ex); goto ag; }
 st: if (fn == 8) if (debugger(f, 1, car(ex), &fn)) return fn; else goto st;
 ex = cdr(ex); if (o2a(fn)[2]>>3 < 31) return symbol_inits[o2a(fn)[2]>>3].fun(f, ex);
 ex = call(f, fn, map_eval(f, ex)); } else if (ap(ex) && o2a(ex)[1] == 12) {
   ex = *binding(f, ex, 0, &m); if (m) { x = ex; set_car(co, ex); goto ag; }
   if (ex == 8) debugger(f, 0, x, &ex); } return ex == -8 ? o2a(x)[4] : ex; }
lval eval(lval *f, lval expr) { return evca(f, cons(f, expr, 0)); }
void print(lval expr) { int i; switch (expr & 3) {
 case 0: if (expr) if (isgraph(expr>>5)) printf("#\\%c", expr>>5);
 else printf("#\\U+%d", expr >> 5); else printf("nil"); break;
 case 1: printf("("); print(car(expr));
   for (expr = cdr(expr); cp(expr); expr = cdr(expr)) {
     printf(" "); print(car(expr)); }
   if (expr) { printf(" . "); print(expr); } printf(")"); break;
 case 2: switch (o2a(expr)[1]) {
 case 4: printf("#<function "); print(o2a(expr)[6]); printf(">"); break;
 case 12: expr = o2a(expr)[2]; for (i = 0; i < o2s(expr)[0]/8-3; i++)
   printf("%c", o2z(expr)[i]); break;
 case 36: printf("#("); for (i = 0; i < o2a(expr)[0]>>5; i++) { if (i)
   printf(" "); print(o2a(expr)[i+2]); } printf(")"); break;
 default: printf("#("); for (i = 0; i <= o2a(expr)[0]>>5; i++)
   print(o2a(expr)[i+1]); printf(")"); } break;
 case 3: switch(o2s(expr)[1]) {
 case 4: printf("\""); for (i = 0; i < o2s(expr)[0]/8-3; i++) {
   char c = o2z(expr)[i]; printf((c=='\\'||c=='\"' ? "\\%c" : "%c"), c); }
   printf("\""); break;
 case 36: printf("%g", o2d(expr)); }}}
int getnws() { int c; do c = getchar(); while (isspace(c)); return c; }
lval read_list(lval *g) { int c = getnws(); if (c == ')') return 0;
  if (c == '.') { lval r = lread(g); getnws(); return r; }
  ungetc(c, stdin); c = lread(g); return cons(g, c, read_list(g)); }
lval stringify(lval *f, lval l) { int i; lval *r; lval t = l; AR = l;
  for (i = 0; t; i++, t = cdr(t)); r = ms0(f, i); r[1] = 4;
  for (i = 8; l; i++, l = cdr(l)) ((char*)r)[i] = car(l) >> 5; return s2o(r); }
lval read_string_list(lval *g) {
  int c = getchar(); if (c == '\"') return 0; if (c == '\\') c = getchar();
  return cons(g, (c << 5) | 24, read_string_list(g)); }
int string_equal_do(lval a, lval b) { int i; for (i=0; i < o2s(a)[0]/8-3; i++)
  if (o2z(a)[i] != o2z(b)[i]) return 0; return 1; }
int string_equal(lval a, lval b) { return a == b || (sp(a) && sp(b) &&
  o2s(a)[1] == 4 && o2s(b)[1] == 4 && o2s(a)[0] == o2s(b)[0]
  && string_equal_do(a, b)); }
lval intern(lval *g, lval name) { lval sym=symbols; for(; sym; sym=o2a(sym)[3])
  if (string_equal(o2a(sym)[2], name)) return o2a(sym)[7] ? sym : 0;
  return symbols = ma(g, 7, 12, name, symbols, 8, 8, 8, -1, 0); }
lval read_symbol(lval *g) { int c = getchar(); if (isspace(c) || c == ')') {
  ungetc(c, stdin); return 0; } return cons(g, (c << 5) | 24, read_symbol(g));}
lval lread(lval *g) { int c = getnws(); if (c == '(') return read_list(g);
  if (c == '\"') return stringify(g, read_string_list(g)); if (c == '\'')
    return cons(g, symbol_inits[5].sym, cons(g, lread(g), 0)); if (c == '#') {
      c = getnws(); if (c == '\'') return cons(g, symbol_inits[13].sym,
        cons(g, lread(g), 0)); return 0; } ungetc(c, stdin);
  if (isdigit(c)) { lval *a = ma0(g, 2); a[1] = 36; scanf("%lf", a + 2);
    return s2o(a); } return intern(g, stringify(g, read_symbol(g))); }
int main(int argc, char *argv[]) { lval g[4] = {2<<5,44}; int i, j; lval sym;
  memory_size = 65536; memory = malloc(memory_size); memf = memory;
  memset(memory, 0, memory_size); memf[0] = 0; memf[1] = memory_size / 4;
  for (i=0; i < 53; i++) { lval *str = ms0(g, j=strlen(symbol_inits[i].name));
  str[1] = 4; for (; j; j--) ((char*)str)[7 + j] = symbol_inits[i].name[j - 1];
  sym = intern(g, s2o(str)); if (i < 3) o2a(sym)[4] = sym;
  symbol_inits[i].sym = sym; o2a(sym)[5] = ma(g, 5, 4, i << 3, 0, 0, 0, sym);
  if (symbol_inits[i].setfun) o2a(sym)[6] = ma(g, 5, 4, i<<3, 8, 0, 0, sym);
  o2a(sym)[7] = i << 3; } setjmp(top_jmp); while (1) ep(g, lread(g)); }
