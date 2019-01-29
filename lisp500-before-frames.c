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
#define A0 car(a)
#define A1 car(cdr(a))
lval car(lval c) { return (c & 3) == 1 ? o2c(c)[0] : 0; }
lval cdr(lval c) { return (c & 3) == 1 ? o2c(c)[1] : 0; }
lval caar(lval c) { return car(car(c)); }
lval cdar(lval c) { return cdr(car(c)); }
lval cadr(lval c) { return car(cdr(c)); }
lval cddr(lval c) { return cdr(cdr(c)); }
lval set_car(lval c, lval val) { return o2c(c)[0] = val; }
lval set_cdr(lval c, lval val) { return o2c(c)[1] = val; }
lval *get_binding(lval env, lval sym, int type) {
  for (; env; env = cdr(env))
    if (type ? car(caar(env))==sym&&(cdr(caar(env))>>3)==type : caar(env)==sym)
      return o2c(car(env))+1;
  return o2a(sym)+4+type;
}
lval *memory;
lval *make_array(int n) { lval *m = memory; *m = n;memory += n + 2; return m; }
lval *make_string(int n) { lval *m = memory;*m = n;memory+=(n+11)/4;return m; }
lval ma(int n, ...) { va_list v; int i; lval *m = make_array(n); va_start(v,n);
 for (i = -1; i < n; i++) m[2 + i] = va_arg(v, lval); return a2o(m); }
double o2d(lval o) { return *(double*)(o2s(o) + 2); }
lval d2o(double d) { lval *a = make_array(2); a[1] = 32; *(double*)(a+2) = d;
 return a2o(a); } 
lval cons(lval car, lval cdr) {
  lval *c = make_array(0); c[0] = car; c[1] = cdr; return c2o(c); }
lval args(lval env, lval form, lval act) {
  while ((form & 3) == 1) {
    env = cons(cons(car(form), car(act)), env);
    form = cdr(form);
    act = cdr(act);
  }
  if (form) env = cons(cons(form, act), env);
  return env;
}
lval xvalues;
lval eval(lval, lval); lval call(lval, lval); void print(lval);
lval eval_body(lval env, lval exprs) {
  lval r = 0; for (; exprs; exprs = cdr(exprs)) r = eval(env, car(exprs));
  return r; }
lval map_eval(lval env, lval exprs) {
  return exprs ? cons(eval(env, car(exprs)), map_eval(env, cdr(exprs))) : 0; }
lval eval_quote(lval env, lval exprs) { return car(exprs); }
lval eval_let(lval env, lval exprs) {
  lval b; lval nenv = env; for (b = car(exprs); b; b = cdr(b))
    nenv = cons(cons(caar(b), eval(env, car(cdar(b)))), nenv);
  return eval_body(nenv, cdr(exprs)); }
lval eval_letm(lval env, lval exprs) {
  lval b; for (b = car(exprs); b; b = cdr(b))
    env = cons(cons(caar(b), eval(env, car(cdar(b)))), env);
  return eval_body(env, cdr(exprs)); }
lval eval_flet(lval env, lval exprs) {
  lval b; lval nenv = env; for (b = car(exprs); b; b = cdr(b))
    nenv = cons(cons(cons(caar(b), 8),
		     ma(4, 0, 992, env, cadr(car(b)), cddr(car(b)))), nenv);
  return eval_body(nenv, cdr(exprs)); }
lval eval_labels(lval env, lval exprs) {
  lval nenv; lval b; for (b = car(exprs); b; b = cdr(b)) env = cons(0, env);
  nenv = env; for (b = car(exprs); b; b = cdr(b), env = cdr(env))
    set_car(env, cons(cons(caar(b), 8),
		      ma(4, 0, 992, env, cadr(car(b)), cddr(car(b)))));
  return eval_body(nenv, cdr(exprs)); }
lval eval_setq(lval env, lval exprs) {
  return *get_binding(env, car(exprs), 0) = eval(env, cadr(exprs)); }
lval eval_function(lval env, lval exprs) { exprs = car(exprs);
 if ((exprs & 3) == 1) return ma(4, 0, 992, env, cadr(exprs), cddr(exprs));
 return *get_binding(env, exprs, 1); }
lval catches = 0;
void unwind(lval c) {
  for (; catches != c; catches = cdr(catches))
    if ((car(catches) & 3) == 2)
      eval_body(o2a(car(catches))[2], o2a(car(catches))[3]); }
lval rvalues(lval v) { return xvalues == 8 ? cons(v, 0) : xvalues; }
lval lvalues(lval a) { xvalues = a; return car(a); }
lval eval_tagbody(lval env, lval exprs) {
  jmp_buf jmp; lval tag; lval e; lval nenv = env; lval a = ma(1, 16, &jmp) + 1;
  for (e = exprs; e; e = cdr(e)) if ((car(e) & 3) == 2)
      nenv = cons(cons(cons(car(e), 24), cons(catches, a)), nenv);
  e = exprs; again: if (!(tag = setjmp(jmp))) { for (; e; e = cdr(e))
    if ((car(e) & 3) != 2) eval(nenv, car(e)); }
  else for (e=exprs;e;e=cdr(e)) if (car(e) == tag) { e = cdr(e); goto again; }
  return 0; }
lval eval_go(lval env, lval exprs) {
  lval b = *get_binding(env, car(exprs), 3); unwind(car(b));
  longjmp(*(jmp_buf*)(o2s(cdr(b))[2]), car(exprs)); }
lval eval_block(lval env, lval exprs) {
  jmp_buf jmp; lval vs; lval a = ma(1, 16, &jmp) + 1;
  if (!(vs = setjmp(jmp))) return eval_body(cons(cons(cons(car(exprs), 32),
				       cons(catches, a)), env), cdr(exprs));
  else return lvalues(car(vs)); }
lval eval_return_from(lval env, lval exprs) {
  lval b = *get_binding(env, car(exprs), 4); unwind(car(b));
  longjmp(*(jmp_buf*)(o2s(cdr(b))[2]),cons(rvalues(eval(env,cadr(exprs))),0));}
lval eval_catch(lval env, lval exprs) {
  jmp_buf jmp; lval vs; lval oc = catches; lval tag = eval(env, car(exprs));
  lval a = ma(1, 16, &jmp) + 1; catches = cons(cons(tag, a), catches);
  if (!(vs = setjmp(jmp))) vs = eval_body(env, cdr(exprs));
  else vs = lvalues(car(vs)); catches = oc; return vs; }
lval eval_throw(lval env, lval exprs) {
  lval tag = eval(env, car(exprs)); lval c;
  for (c = catches; c; c = cdr(c)) if ((car(c) & 3) == 1 && caar(c) == tag) {
    unwind(c);
    longjmp(*(jmp_buf*)(o2s(cdar(c))[2]),
	    cons(rvalues(eval(env, cadr(exprs))), 0)); } return 0; }
lval eval_unwind_protect(lval env, lval exprs) {
  lval r; catches = cons(ma(2, 16, env, cdr(exprs)), catches);
  r = rvalues(eval(env, car(exprs))); eval_body(env, cdr(exprs));
  return lvalues(r); }
lval eval_if(lval env, lval exprs) {
  return eval(env, eval(env, car(exprs)) ? cadr(exprs) : car(cddr(exprs))); }
lval append(lval a, lval b) {
  lval c; if (a) { for (c = a; cdr(c); c = cdr(c)); set_cdr(c, b); return b; }
  else return c; }
lval eval_multiple_value_call(lval env, lval exprs) {
  lval fn = eval(env, car(exprs)); lval vs = 0;
  for (exprs = cdr(exprs); exprs; exprs = cdr(exprs))
    vs = append(vs, rvalues(eval(env, car(exprs))));
  return call(fn, vs); }
lval eval_multiple_value_prog1(lval env, lval exprs) {
  lval v = rvalues(eval(env, car(exprs))); eval_body(env, cdr(exprs));
  return lvalues(v); }
lval lfuncall(lval a) { return call(car(a), cdr(a)); }
lval lapply(lval a) { lval fn = car(a); a = cdr(a); if (cdr(a)) {
  lval b; for (b = a; cddr(b); b = cdr(b)); set_cdr(b, cadr(b)); }
 else a = car(a); return call(fn, a); }
lval lcons(lval a) { return cons(A0, A1); }
lval lcar(lval a) { return car(A0); }
lval lcdr(lval a) { return cdr(A0); }
lval lprint(lval a) { print(A0); return A0; }
struct symbol_init {
  const char *sym; lval (*fun)(); int argc;
} symbol_inits[] = {
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
  {"values", lvalues, -1},
  {"funcall", lfuncall, -2},
  {"apply", lapply, -2},
  {"cons", lcons, 2},
  {"car", lcar, 1},
  {"cdr", lcdr, 1},
  {"print", lprint, 1}
};
lval call(lval fn, lval a) { return o2a(fn)[2] == 992
  ? eval_body(args(o2a(fn)[3], o2a(fn)[4], a), o2a(fn)[5])
  : symbol_inits[o2a(fn)[2]].fun(a); }
lval eval(lval env, lval expr) {
  xvalues = 8;
  if ((expr & 3) == 1) {
    lval fn = *get_binding(env,car(expr),1); lval senv = env; expr = cdr(expr);
    if (o2a(fn)[2] < 18) return symbol_inits[o2a(fn)[2]].fun(env, expr);
    expr = call(fn, map_eval(env, expr)); env = senv;
  } else if ((expr&3)==2 && o2a(expr)[1]==8) expr = *get_binding(env,expr,0);
  return expr; }
void print(lval expr) { int i; switch (expr & 3) {
 case 0: if (expr) printf("%d", expr >> 2); else printf("nil"); break;
 case 1: printf("("); print(car(expr));
   for (expr = cdr(expr); (expr&3) == 1; expr = cdr(expr)) {
     printf(" "); print(car(expr)); }
   if (expr) { printf(" . "); print(expr); } printf(")"); break;
 case 2: switch (o2a(expr)[1]) {
 case 0: printf("#<function "); if (o2a(expr)[2] == 992) { print(o2a(expr)[4]);
 print(o2a(expr)[5]); } else printf("%s", symbol_inits[o2a(expr)[2]].sym);
   printf(">"); break;
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
lval read_list() {
  int c = getnws();
  if (c == ')') return 0;
  if (c == '.') { lval r = lread(); getnws(); return r; }
  ungetc(c, stdin); c = lread(); return cons(c, read_list()); }
lval stringify(lval l) {
  int i;lval *r;lval t = l;for (i = 0; t; i++, t = cdr(t)); r = make_string(i);
  r[1] = 0; for (i = 8; l; i++, l = cdr(l)) ((char*)r)[i] = car(l) >> 4;
  return s2o(r); }
lval read_string_list() {
  int c = getchar(); if (c == '\"') return 0; if (c == '\\') c = getchar();
  return cons((c << 4) | 12, read_string_list()); }
int string_equal_do(lval a, lval b) {
  int i;
  for (i = 0; i < o2s(a)[0]; i++) if (o2z(a)[i] != o2z(b)[i]) return 0;
  return 1; }
int string_equal(lval a, lval b) {
  return a == b || (((a & 3) == 3) && ((b & 3) == 3) && !o2s(a)[1]
		    && !o2s(b)[1] && o2s(a)[0] == o2s(b)[0]
		    && string_equal_do(a, b)); }
lval symbols;
lval intern(lval name) { lval sym; for (sym = symbols; sym; sym = o2a(sym)[3])
  if (string_equal(o2a(sym)[2], name)) return sym;
  return symbols = ma(4, 8, name, symbols, 8, 8); }
lval read_symbol() { int c = getchar(); if (isspace(c) || c == ')') {
  ungetc(c, stdin); return 0; } return cons((c << 4) | 12, read_symbol()); }
lval lread() { int c = getnws(); if (c == '(') return read_list();
  if (c == '\"') return stringify(read_string_list()); ungetc(c, stdin);
  if (isdigit(c)) { lval *a = make_array(2); a[1] = 32; scanf("%lf", a + 2);
    return s2o(a); } return intern(stringify(read_symbol())); }
int main(int argc, char *argv[]) {
  int i, j; lval *str; lval sym; memory = malloc(65536);
  for (i = 0; i < 25; i++) {
    str = make_string(j = strlen(symbol_inits[i].sym)); str[1] = 0;
    for (; j; j--) ((char*)str)[7 + j] = symbol_inits[i].sym[j - 1];
    sym = intern(s2o(str)); o2a(sym)[5] = ma(1, 0, i); }
  /* while (1) print(lread()); */
  while (1) print(eval(0, lread()));
}
