#include <ctype.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int lval;
lval *o2c(lval o) { return (lval*)(o - 1); }
lval c2o(lval *c) { return (lval)c + 1; }
lval *o2a(lval o) { return (lval*)(o - 2); }
lval a2o(lval *a) { return (lval)a + 2; }
lval *o2s(lval o) { return (lval*)(o - 3); }
char *o2z(lval o) { return (char*)(o - 3 + 2*sizeof(lval)); }
lval s2o(lval *s) { return (lval)s + 3; }
#define NF(n) lval g[n+4] = {n+2,40,a2o(f),f[3]};
#define S(s, n) lval s(lval *f) { lval g[n+4] = {n+2,40,a2o(f),f[3]};
#define X }
#define E f[3]
#define NE g[3]
#define AR f[4]
#define A0 car(f[4])
#define A0R cdr(f[4])
#define A1 car(cdr(f[4]))
lval car(lval c) { return (c & 3) == 1 ? o2c(c)[0] : 0; }
lval cdr(lval c) { return (c & 3) == 1 ? o2c(c)[1] : 0; }
lval caar(lval c) { return car(car(c)); }
lval cdar(lval c) { return cdr(car(c)); }
lval cadr(lval c) { return car(cdr(c)); }
lval cddr(lval c) { return cdr(cdr(c)); }
lval set_car(lval c, lval val) { return o2c(c)[0] = val; }
lval set_cdr(lval c, lval val) { return o2c(c)[1] = val; }
lval *get_binding(lval env, lval sym, int type) { for (; env; env = cdr(env))
  if (type ? car(caar(env))==sym&&(cdr(caar(env))>>3)==type : caar(env)==sym)
    return o2c(car(env))+1; return o2a(sym)+4+type; }
lval eval(lval *, lval); lval call(lval *, lval, lval); void print(lval);
lval *memory; lval xvalues; lval symbols; lval catches = 0; jmp_buf top_jmp;
lval *m0(lval *g, int n) { lval *m = memory; memory += n; return m; }
lval *ma0(lval *g, int n) { lval *m = m0(g, n + 2); *m = n; return m; }
lval *ms0(lval *g, int n) { lval *m = m0(g, (n+11)/4); *m = n; return m; }
lval ma(lval *g,int n,...) { va_list v; int i; lval *m=ma0(g,n); va_start(v,n);
 for (i = -1; i < n; i++) m[2 + i] = va_arg(v, lval); return a2o(m); }
double o2d(lval o) { return *(double*)(o2s(o) + 2); }
lval d2o(lval *g, double d) { lval *a = ma0(g, 2); a[1] = 32;
 *(double*)(a+2) = d; return s2o(a); }
lval cons(lval *g, lval car, lval cdr) {
  lval *c = m0(g, 2); c[0] = car; c[1] = cdr; return c2o(c); }
lval args(lval *g, lval env, lval form, lval act) {
  while (form) {
    if (o2a(car(form))[7] == 2) { env = cons(g, cons(g, cadr(form), act), env);
    break; } env = cons(g, cons(g, car(form), car(act)), env);
    form = cdr(form); act = cdr(act); } return env; }
lval eval_body(lval *g, lval exprs) { lval r=0; for (; exprs; exprs=cdr(exprs))
  r = eval(g, car(exprs)); return r; }
lval map_eval(lval *g, lval exprs) {
  return exprs ? cons(g, eval(g, car(exprs)), map_eval(g, cdr(exprs))) : 0; }
lval eval_quote(lval *g, lval exprs) { return car(exprs); }
lval eval_let(lval *f, lval exprs) { NF(0) lval b; lval env = E;
  for (b = car(exprs); b; b = cdr(b))
    env = cons(g, cons(g, caar(b), eval(g, car(cdar(b)))), env);
  NE = env; return eval_body(g, cdr(exprs)); }
lval eval_letm(lval *f, lval exprs) { NF(0) lval b;
  for (b = car(exprs); b; b = cdr(b))
    NE = cons(g, cons(g, caar(b), eval(g, car(cdar(b)))), NE);
  return eval_body(g, cdr(exprs)); }
lval eval_flet(lval *f, lval exprs) { NF(0) lval b; lval env = E;
  for (b = car(exprs); b; b = cdr(b))
    env = cons(g, cons(g, cons(g, caar(b), 8),
	       ma(g, 4, 0, 992, E, cadr(car(b)), cddr(car(b)), caar(b))), env);
  NE = env; return eval_body(g, cdr(exprs)); }
lval eval_labels(lval *f, lval exprs) { NF(0) lval env = E; lval b;
  for (b = car(exprs); b; b = cdr(b)) env = cons(g, 0, env); NE = env;
  for (b = car(exprs); b; b = cdr(b), env = cdr(env))
    set_car(env, cons(g, cons(g, caar(b), 8),
		      ma(g, 5, 0, 992, NE,cadr(car(b)),cddr(car(b)),caar(b))));
  return eval_body(g, cdr(exprs)); }
lval eval_setq(lval *f, lval exprs) {
  return *get_binding(E, car(exprs), 0) = eval(f, cadr(exprs)); }
lval eval_function(lval *f, lval exprs) { exprs = car(exprs);
 if ((exprs & 3) == 1) return ma(f, 5, 0, 992, E, cadr(exprs), cddr(exprs), 0);
 return *get_binding(E, exprs, 1); }
void unwind(lval *f, lval c) { NF(0)
  for (; catches != c; catches = cdr(catches))
    if ((car(catches) & 3) == 2) { NE = o2a(car(catches))[2];
      eval_body(g, o2a(car(catches))[3]); }}
lval rvalues(lval *g, lval v) { return xvalues==8 ? cons(g, v, 0) : xvalues; }
lval mvalues(lval a) { xvalues = a; return car(a); }
lval eval_tagbody(lval *f, lval exprs) { NF(0)
  jmp_buf jmp; lval tag; lval e; lval a = ma(g, 1, 16, &jmp) + 1;
  for (e = exprs; e; e = cdr(e)) if ((car(e) & 3) == 2)
    NE = cons(g, cons(g, cons(g, car(e), 24), cons(g, catches, a)), NE);
  e = exprs; again: if (!(tag = setjmp(jmp))) { for (; e; e = cdr(e))
    if ((car(e) & 3) != 2) eval(g, car(e)); }
  else for (e=exprs;e;e=cdr(e)) if (car(e) == tag) { e = cdr(e); goto again; }
  return 0; }
lval eval_go(lval *f, lval exprs) {
  lval b = *get_binding(E, car(exprs), 3); unwind(f, car(b));
  longjmp(*(jmp_buf*)(o2s(cdr(b))[2]), car(exprs)); }
lval eval_block(lval *f, lval exprs) { NF(0) jmp_buf jmp; lval vs; 
  NE = cons(g, cons(g, cons(g, car(exprs), 32),
		    cons(g, catches, ma(g, 1, 16, &jmp) + 1)), NE);
  if (!(vs = setjmp(jmp))) return eval_body(g, cdr(exprs));
  else return mvalues(car(vs)); }
lval eval_return_from(lval *f, lval exprs) {
  lval b = *get_binding(E, car(exprs), 4); unwind(f, car(b));
  longjmp(*(jmp_buf*)(o2s(cdr(b))[2]),
	  cons(f, rvalues(f, eval(f, cadr(exprs))), 0)); }
lval eval_catch(lval *f, lval exprs) {
  jmp_buf jmp; lval vs; lval oc = catches; lval tag = eval(f, car(exprs));
  catches = cons(f, cons(f, tag, ma(f, 1, 16, &jmp) + 1), catches);
  if (!(vs = setjmp(jmp))) vs = eval_body(f, cdr(exprs));
  else vs = mvalues(car(vs)); catches = oc; return vs; }
lval eval_throw(lval *f, lval exprs) {
  lval tag = eval(f, car(exprs)); lval c;
  for (c = catches; c; c = cdr(c)) if ((car(c) & 3) == 1 && caar(c) == tag) {
    unwind(f, c);
    longjmp(*(jmp_buf*)(o2s(cdar(c))[2]),
	    cons(f, rvalues(f, eval(f, cadr(exprs))), 0)); } return 0; }
lval eval_unwind_protect(lval *f, lval exprs) {
  lval r; catches = cons(f, ma(f, 2, 16, E, cdr(exprs)), catches);
  r = rvalues(f, eval(f, car(exprs))); eval_body(f, cdr(exprs));
  return mvalues(r); }
lval eval_if(lval *f, lval exprs) {
  return eval(f, eval(f, car(exprs)) ? cadr(exprs) : car(cddr(exprs))); }
lval append(lval a, lval b) { lval c; if (a) { for (c = a; cdr(c); c = cdr(c));
  set_cdr(c, b); return a; } return b; }
lval eval_multiple_value_call(lval *f, lval exprs) {
  lval fn = eval(f, car(exprs)); lval vs = 0;
  for (exprs = cdr(exprs); exprs; exprs = cdr(exprs))
    vs = append(vs, rvalues(f, eval(f, car(exprs))));
  xvalues = 8; return call(f, fn, vs); }
lval eval_multiple_value_prog1(lval *f, lval exprs) {
  lval v = rvalues(f, eval(f, car(exprs))); eval_body(f, cdr(exprs));
  return mvalues(v); }
lval eval_defun(lval *f, lval exprs) { o2a(car(exprs))[5] =
  ma(f,5,0,992, E, cadr(exprs), cddr(exprs), car(exprs)); return car(exprs); }
lval lvalues(lval *f) { return mvalues(AR); }
S(lfuncall,0) return call(g, A0, A0R); X
S(lapply,0) lval fn = A0; lval a = A0R; if (cdr(a)) {
  lval b; for (b = a; cddr(b); b = cdr(b)); set_cdr(b, cadr(b)); }
 else a = car(a); return call(g, fn, a); X
S(lcons,0) return cons(g, A0, A1); X
lval lcar(lval *f) { return car(A0); }
lval lcdr(lval *f) { return cdr(A0); }
lval lplus(lval *f) { double s = 0; lval l; for (l = AR; l; l = cdr(l))
  s += o2d(car(l)); return d2o(f, s); }
lval lminus(lval *f) { double s = o2d(A0); lval l = A0R; if (l)
  for (; l; l = cdr(l)) s -= o2d(car(l)); else s = -s; return d2o(f, s); }
lval ltimes(lval *f) { double s = 1; lval l; for (l = AR; l; l = cdr(l))
  s *= o2d(car(l)); return d2o(f, s); }
lval ldivi(lval *f) { double s = o2d(A0); lval l = A0R; if (l)
  for (; l; l = cdr(l)) s /= o2d(car(l)); else s = 1/s; return d2o(f, s); }
lval lprint(lval *f) { print(A0); return A0; }
struct symbol_init { const char *sym; lval (*fun)(); int argc;
} symbol_inits[] = {
  {"nil", 0, 0},
  {"t", 0, 0},
  {"&rest", 0, 0},
  {"quote", eval_quote, 1},
  {"let", eval_let, -2},
  {"let*", eval_letm, -2},
  {"flet", eval_flet, -2},
  {"labels", eval_labels, -2},
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
  {"values", lvalues, -1},
  {"funcall", lfuncall, -2},
  {"apply", lapply, -2},
  {"cons", lcons, 2},
  {"car", lcar, 1},
  {"cdr", lcdr, 1},
  {"+", lplus, -1},
  {"-", lminus, -1},
  {"*", ltimes, -1},
  {"/", ldivi, -1},
  {"print", lprint, 1}
};
void ep(lval *g, lval expr) { int i; lval v = rvalues(g, eval(g, expr));
  if (v) for (i = 0; v; v = cdr(v)) { printf(";%d: ", i++); print(car(v));
  printf("\n"); } else printf(";no values\n"); }
char *exmsg[] = {"variable unbound", "function unbound"};
int debugger(lval *f, int x, lval val, lval *vp) { lval ex; int i; lval *h = f;
  int l = 0; printf(";exception: %s ", exmsg[x]); if (val) print(val);
  printf("\n;restarts:\n;[t]oplevel\n;[u]se <form> instead\n;[r]eturn <form> from function\n");
  while (1) { lval *g; printf(";%d> ", l);
    ex = lread(f); if ((ex & 3) == 3 && o2s(ex)[1] == 32) {
      for (h = f, l = i = o2d(ex); i; i--) { if (!h[2]) break; h = o2a(h[2]); }
    } else if ((ex & 3) == 2 && o2a(ex)[1] == 8) {
      switch(o2z(o2a(ex)[2])[0]) {
      case 'b': printf(";backtrace:\n"); g = f; for (i = 0; g; i++) {
	printf(";%d: ", i); if(g[0] == 4) { print(o2a(g[5])[6]);
	printf(" "); print(g[4]);} printf("\n"); if (!g[2]) break; g=o2a(g[2]);
	} break;
      case 'r': *vp = eval(f, lread(f)); return 1;
      case 't': longjmp(top_jmp, 1);
      case 'u': *vp = eval(f, lread(f)); return 0;
      }
    } else ep(h, ex);
  }
}
lval call(lval *f, lval fn, lval a) { NF(2) g[4] = a; g[5] = fn;
  NE = args(g, o2a(fn)[3], o2a(fn)[4], a); return o2a(fn)[2] == 992
   ? eval_body(g, o2a(fn)[5]) : symbol_inits[o2a(fn)[2]].fun(g); }
lval eval(lval *f, lval expr) { lval x=expr; xvalues=8; if ((expr & 3) == 1) {
  lval fn = *get_binding(E, car(expr), 1);
  st: if (fn==8) if (debugger(f, 1, car(expr), &fn)) return fn; else goto st; expr = cdr(expr);
  if (o2a(fn)[2] < 22) return symbol_inits[o2a(fn)[2]].fun(f, expr);
  expr = call(f,fn,map_eval(f,expr)); } else if((expr&3)==2 && o2a(expr)[1]==8)
    expr = *get_binding(E, expr, 0); if (expr==8) debugger(f, 0, x, &expr);
  return expr; }
void print(lval expr) { int i; switch (expr & 3) {
 case 0: if (expr) printf("%d", expr >> 2); else printf("nil"); break;
 case 1: printf("("); print(car(expr));
   for (expr = cdr(expr); (expr&3) == 1; expr = cdr(expr)) {
     printf(" "); print(car(expr)); }
   if (expr) { printf(" . "); print(expr); } printf(")"); break;
 case 2: switch (o2a(expr)[1]) {
 case 0: printf("#<function "); print(o2a(expr)[6]); printf(">"); break;
 case 8: expr = o2a(expr)[2]; for (i = 0; i < o2s(expr)[0]; i++)
   printf("%c", o2z(expr)[i]); break;
 default: printf("#("); for (i = 0; i <= o2a(expr)[0]; i++)
   print(o2a(expr)[i+1]); printf(")"); } break;
 case 3: switch(o2s(expr)[1]) {
 case 0: printf("\""); for (i = 0; i < o2s(expr)[0]; i++) {
   char c = o2z(expr)[i]; printf((c=='\\'||c=='\"' ? "\\%c" : "%c"), c); }
   printf("\""); break;
 case 32: printf("%g", o2d(expr)); }}}
int getnws() { int c; do c = getchar(); while (isspace(c)); return c; }
lval lread();
lval read_list(lval *g) { int c = getnws(); if (c == ')') return 0;
  if (c == '.') { lval r = lread(); getnws(); return r; }
  ungetc(c, stdin); c = lread(); return cons(g, c, read_list(g)); }
lval stringify(lval *g, lval l) { int i; lval *r; lval t = l;
  for (i = 0; t; i++, t = cdr(t)); r = ms0(g, i); r[1] = 0;
  for (i = 8; l; i++, l = cdr(l)) ((char*)r)[i] = car(l) >> 4; return s2o(r); }
lval read_string_list(lval *g) {
  int c = getchar(); if (c == '\"') return 0; if (c == '\\') c = getchar();
  return cons(g, (c << 4) | 12, read_string_list(g)); }
int string_equal_do(lval a, lval b) { int i; for (i = 0; i < o2s(a)[0]; i++)
  if (o2z(a)[i] != o2z(b)[i]) return 0; return 1; }
int string_equal(lval a, lval b) { return a == b || (((a & 3) == 3) &&
  ((b & 3) == 3) && !o2s(a)[1] && !o2s(b)[1] && o2s(a)[0] == o2s(b)[0] &&
  string_equal_do(a, b)); }
lval intern(lval *g, lval name) {
  lval sym; for (sym = symbols; sym; sym = o2a(sym)[3])
    if (string_equal(o2a(sym)[2], name)) return o2a(sym)[7] ? sym : 0;
  return symbols = ma(g, 6, 8, name, symbols, 8, 8, 8, -1); }
lval read_symbol(lval *g) { int c = getchar(); if (isspace(c) || c == ')') {
  ungetc(c, stdin); return 0; } return cons(g, (c << 4) | 12, read_symbol(g));}
lval lread(lval *g) { int c = getnws(); if (c == '(') return read_list(g);
  if (c == '\"') return stringify(g, read_string_list(g)); ungetc(c, stdin);
  if (isdigit(c)) { lval *a = ma0(g, 2); a[1] = 32; scanf("%lf", a + 2);
    return s2o(a); } return intern(g, stringify(g, read_symbol(g))); }
int main(int argc, char *argv[]) {
  lval g[4] = {2,40};
  int i, j; lval *str; lval sym; memory = malloc(65536);
  for (i = 0; i < 33; i++) {
    str = ms0(g, j = strlen(symbol_inits[i].sym)); str[1] = 0;
    for (; j; j--) ((char*)str)[7 + j] = symbol_inits[i].sym[j - 1];
    sym = intern(g, s2o(str)); if (i < 3) o2a(sym)[4] = sym; 
    o2a(sym)[5] = ma(g, 5, 0, i, 0, 0, 0, sym);
    o2a(sym)[7] = i; } setjmp(top_jmp); while (1) ep(g, lread(g)); }
