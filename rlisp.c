#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>

#include "mpc/mpc.h"

struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

enum {
	LERR_DIV_ZERO,
	LERR_BAD_OP,
	LERR_BAD_NUM
};

enum {
	LVAL_ERR,
	LVAL_NUM,
	LVAL_SYM,
	LVAL_SEXPR,
	LVAL_QEXPR,
	LVAL_FUN
};

typedef lval*(*lbuiltin)(lenv*, lval*);

typedef struct lval {
	int type;

	long number;
	char* error;
	char* symbol;

	lbuiltin builtin;
	lenv* env;
	lval* formals;
	lval* body;

	int count;
	struct lval** cell;
} lval;

lval* lval_number(long x)
{
	lval* val = malloc(sizeof(lval));
	val->type = LVAL_NUM;
	val->number = x;
	return val;
}

lval* lval_error(char* fmt, ...)
{
	lval* val = malloc(sizeof(lval));
	val->type = LVAL_ERR;

	va_list va;
  	va_start(va, fmt);

  	val->error = malloc(512);
  	vsnprintf(val->error, 511, fmt, va);
  	val->error = realloc(val->error, strlen(val->error)+1);

  	va_end(va);

	return val;
}

lval* lval_symbol(char* s)
{
	lval* val = malloc(sizeof(lval));
	val->type = LVAL_SYM;
	val->symbol = malloc(strlen(s) + 1);
	strcpy(val->symbol, s);
	return val;
}

lval* lval_sexpr(void)
{
	lval* val = malloc(sizeof(lval));
	val->type = LVAL_SEXPR;
	val->count = 0;
	val->cell = NULL;
	return val;
}

lval* lval_qexpr(void)
{
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_QEXPR;
	v->count = 0;
	v->cell = NULL;
	return v;
}

lval* lval_fun(lbuiltin func)
{
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_FUN;
	v->builtin = func;
	return v;
}

lenv* lenv_new(void);

lval* lval_lambda(lval* formals, lval* body)
{
	lval* v = malloc(sizeof(lval));
	v->type = LVAL_FUN;

	v->builtin = NULL;

	v->env = lenv_new();

	v->formals = formals;
	v->body = body;
	return v;
}

void lenv_del(lenv* e);

void lval_del(lval* v)
{

	switch (v->type) {
		case LVAL_NUM:
			break;

		case LVAL_ERR:
			free(v->error);
			break;

    		case LVAL_SYM:
    			free(v->symbol);
    			break;

		case LVAL_SEXPR:
		case LVAL_QEXPR:
			for (int i = 0; i < v->count; i++) {
				lval_del(v->cell[i]);
			}
			free(v->cell);
			break;

		case LVAL_FUN:
			if (!v->builtin) {
				lenv_del(v->env);
				lval_del(v->formals);
				lval_del(v->body);
  			}
			break;
	}

	free(v);
}

lval* lval_add(lval* v, lval* x)
{
	v->count++;
	v->cell = realloc(v->cell, sizeof(lval*) * v->count);
	v->cell[v->count-1] = x;
	return v;
}

lval* lval_pop(lval* v, int i)
{
	lval* x = v->cell[i];

	memmove(&v->cell[i], &v->cell[i+1],
	sizeof(lval*) * (v->count-i-1));

	v->count--;

	v->cell = realloc(v->cell, sizeof(lval*) * v->count);
	return x;
}

lval* lval_take(lval* v, int i)
{
	lval* x = lval_pop(v, i);
	lval_del(v);
	return x;
}

lval* lval_join(lval* x, lval* y)
{
	while (y->count) {
		x = lval_add(x, lval_pop(y, 0));
	}

	lval_del(y);
	return x;
}

void lval_print(lval* v);

void lval_expr_print(lval* v, char open, char close)
{
	putchar(open);
	for (int i = 0; i < v->count; i++) {
		lval_print(v->cell[i]);

		if (i != (v->count-1)) {
			putchar(' ');
		}
	}
	putchar(close);
}

void lval_print(lval* v)
{
	switch (v->type) {
		case LVAL_NUM:
			printf("%li", v->number);
			break;
		case LVAL_ERR:
			printf("Error: %s", v->error);
			break;
		case LVAL_SYM:
			printf("%s", v->symbol);
			break;
		case LVAL_SEXPR:
			lval_expr_print(v, '(', ')');
			break;
		case LVAL_QEXPR:
			lval_expr_print(v, '{', '}');
			break;
		case LVAL_FUN:
			if (v->builtin) {
				printf("<builtin>");
			} else {
				printf("(\\ "); lval_print(v->formals);
				putchar(' '); lval_print(v->body); putchar(')');
			}
			break;

	}
}

void lval_println(lval* v)
{
	lval_print(v);
	putchar('\n');
}

char* ltype_name(int t)
{
	switch(t) {
		case LVAL_FUN:
			return "Function";
		case LVAL_NUM:
			return "Number";
		case LVAL_ERR:
			return "Error";
		case LVAL_SYM:
			return "Symbol";
		case LVAL_SEXPR:
			return "S-Expression";
		case LVAL_QEXPR:
			return "Q-Expression";
		default:
			return "Unknown";
	}
}

lenv* lenv_copy(lenv* e);

lval* lval_copy(lval* v)
{
	lval* x = malloc(sizeof(lval));
	x->type = v->type;

	switch (v->type) {
		case LVAL_FUN:
			if (v->builtin) {
				x->builtin = v->builtin;
			} else {
				x->builtin = NULL;
				x->env = lenv_copy(v->env);
				x->formals = lval_copy(v->formals);
				x->body = lval_copy(v->body);
			}
			break;
		case LVAL_NUM: x->number = v->number;
			break;
		case LVAL_ERR:
      			x->error = malloc(strlen(v->error) + 1);
			strcpy(x->error, v->error);
			break;
		case LVAL_SYM:
			x->symbol = malloc(strlen(v->symbol) + 1);
			strcpy(x->symbol, v->symbol); break;
		case LVAL_SEXPR:
		case LVAL_QEXPR:
			x->count = v->count;
			x->cell = malloc(sizeof(lval*) * x->count);
			for (int i = 0; i < x->count; i++) {
				x->cell[i] = lval_copy(v->cell[i]);
			}
			break;
	}
	return x;
}

struct lenv {
	lenv* par;
	int count;
	char** syms;
	lval** vals;
};


lenv* lenv_new(void)
{
	lenv* e = malloc(sizeof(lenv));
	e->par = NULL;
	e->count = 0;
	e->syms = NULL;
	e->vals = NULL;
	return e;
}

void lenv_del(lenv* e)
{
	for (int i = 0; i < e->count; i++) {
		free(e->syms[i]);
		lval_del(e->vals[i]);
	}
	free(e->syms);
	free(e->vals);
	free(e);
}

lval* lenv_get(lenv* e, lval* k)
{
	for (int i = 0; i < e->count; i++) {
		if (strcmp(e->syms[i], k->symbol) == 0)
			return lval_copy(e->vals[i]);
	}

	if (e->par)
		return lenv_get(e->par, k);
	else
		return lval_error("Unbound Symbol '%s'", k->symbol);
}

void lenv_put(lenv* e, lval* k, lval* v)
{
	for (int i = 0; i < e->count; i++) {
		if (strcmp(e->syms[i], k->symbol) == 0) {
			lval_del(e->vals[i]);
			e->vals[i] = lval_copy(v);
			return;
		}
	}

	e->count++;
	e->vals = realloc(e->vals, sizeof(lval*) * e->count);
	e->syms = realloc(e->syms, sizeof(char*) * e->count);

	e->vals[e->count-1] = lval_copy(v);
	e->syms[e->count-1] = malloc(strlen(k->symbol)+1);
	strcpy(e->syms[e->count-1], k->symbol);
}

void lenv_def(lenv* e, lval* k, lval* v)
{
	while (e->par)
		e = e->par;
	lenv_put(e, k, v);
}

lenv* lenv_copy(lenv* e)
{
	lenv* n = malloc(sizeof(lenv));
	n->par = e->par;
	n->count = e->count;
	n->syms = malloc(sizeof(char*) * n->count);
	n->vals = malloc(sizeof(lval*) * n->count);
	for (int i = 0; i < e->count; i++) {
		n->syms[i] = malloc(strlen(e->syms[i]) + 1);
		strcpy(n->syms[i], e->syms[i]);
		n->vals[i] = lval_copy(e->vals[i]);
	}
	return n;
}





#define LASSERT(args, cond, fmt, ...) \
	if (!(cond)) { \
		lval* error = lval_error(fmt, ##__VA_ARGS__); \
		lval_del(args); \
		return error; \
	}

#define LASSERT_TYPE(func, args, index, expect) \
	LASSERT(args, args->cell[index]->type == expect, \
		"Function '%s' passed incorrect type for argument %i. Got %s, Expected %s.", \
		func, index, ltype_name(args->cell[index]->type), ltype_name(expect))

#define LASSERT_NUM(func, args, num) \
	LASSERT(args, args->count == num, \
		"Function '%s' passed incorrect number of arguments. Got %i, Expected %i.", \
		func, args->count, num)

#define LASSERT_NOT_EMPTY(func, args, index) \
	LASSERT(args, args->cell[index]->count != 0, \
		"Function '%s' passed {} for argument %i.", func, index);


lval* builtin_op(lenv* e, lval* a, char* op)
{
	for (int i = 0; i < a->count; i++) {
		LASSERT_TYPE(op, a, i, LVAL_NUM);
	}

	lval* x = lval_pop(a, 0);

	if ((strcmp(op, "-") == 0) && a->count == 0) {
		x->number = -x->number;
	}

	while (a->count > 0) {
		lval* y = lval_pop(a, 0);

		if (strcmp(op, "+") == 0)
			x->number += y->number;
		if (strcmp(op, "-") == 0)
			x->number -= y->number;
		if (strcmp(op, "*") == 0)
			x->number *= y->number;
		if (strcmp(op, "/") == 0) {
			if (y->number == 0) {
				lval_del(x); lval_del(y);
				x = lval_error("Division By Zero.");
				break;
			}
			x->number /= y->number;
		}

		lval_del(y);
	}

	lval_del(a);
	return x;
}

lval* builtin_add(lenv* e, lval* a)
{
	return builtin_op(e, a, "+");
}

lval* builtin_sub(lenv* e, lval* a)
{
	return builtin_op(e, a, "-");
}

lval* builtin_mul(lenv* e, lval* a)
{
	return builtin_op(e, a, "*");
}

lval* builtin_div(lenv* e, lval* a)
{
	return builtin_op(e, a, "/");
}

lval* builtin_head(lenv* e, lval* a)
{
	LASSERT_NUM("head", a, 1);
	LASSERT_TYPE("head", a, 0, LVAL_QEXPR);
	LASSERT_NOT_EMPTY("head", a, 0);

	lval* v = lval_take(a, 0);

	while (v->count > 1)
		lval_del(lval_pop(v, 1));

	return v;
}

lval* builtin_tail(lenv* e, lval* a)
{
	LASSERT_NUM("tail", a, 1);
	LASSERT_TYPE("tail", a, 0, LVAL_QEXPR);
	LASSERT_NOT_EMPTY("tail", a, 0);

	lval* v = lval_take(a, 0);

	lval_del(lval_pop(v, 0));
	return v;
}

lval* builtin_lambda(lenv* e, lval* a)
{
	LASSERT_NUM("\\", a, 2);
	LASSERT_TYPE("\\", a, 0, LVAL_QEXPR);
	LASSERT_TYPE("\\", a, 1, LVAL_QEXPR);

	for (int i = 0; i < a->cell[0]->count; i++) {
		LASSERT(a, (a->cell[0]->cell[i]->type == LVAL_SYM),
			"Cannot define non-symbol. Got %s, Expected %s.",
			ltype_name(a->cell[0]->cell[i]->type),ltype_name(LVAL_SYM));
	}

	lval* formals = lval_pop(a, 0);
	lval* body = lval_pop(a, 0);
	lval_del(a);

	return lval_lambda(formals, body);
}

lval* lval_eval(lenv* e, lval* v);

lval* builtin_list(lenv* e, lval* a)
{
	a->type = LVAL_QEXPR;
	return a;
}

lval* builtin_eval(lenv* e, lval* a)
{
	LASSERT_NUM("eval", a, 1);
	LASSERT_TYPE("eval", a, 0, LVAL_QEXPR);

	lval* x = lval_take(a, 0);
	x->type = LVAL_SEXPR;
	return lval_eval(e, x);
}

lval* builtin_join(lenv* e, lval* a)
{
	for (int i = 0; i < a->count; i++) {
		LASSERT_TYPE("join", a, i, LVAL_QEXPR);
	}

	lval* x = lval_pop(a, 0);

	while (a->count) {
		x = lval_join(x, lval_pop(a, 0));
	}

	lval_del(a);
	return x;
}

lval* builtin_var(lenv* e, lval* a, char* func)
{
	LASSERT_TYPE(func, a, 0, LVAL_QEXPR);

	lval* syms = a->cell[0];
	for (int i = 0; i < syms->count; i++) {
		LASSERT(a, (syms->cell[i]->type == LVAL_SYM),
			"Function '%s' cannot define non-symbol. "
			"Got %s, Expected %s.", func,
			ltype_name(syms->cell[i]->type),
			ltype_name(LVAL_SYM));
	}

	LASSERT(a, (syms->count == a->count-1),
		"Function '%s' passed too many arguments for symbols. "
		"Got %i, Expected %i.", func, syms->count, a->count-1);

	for (int i = 0; i < syms->count; i++) {
		if (strcmp(func, "def") == 0)
			lenv_def(e, syms->cell[i], a->cell[i+1]);

	if (strcmp(func, "=")   == 0)
		lenv_put(e, syms->cell[i], a->cell[i+1]);
	}

	lval_del(a);
	return lval_sexpr();
}

lval* builtin_def(lenv* e, lval* a)
{
	return builtin_var(e, a, "def");
}

lval* builtin_put(lenv* e, lval* a)
{
	return builtin_var(e, a, "=");
}


lval* builtin(lenv* e, lval* a, char* func) {
	if (strcmp("list", func) == 0)
		return builtin_list(e, a);
	if (strcmp("head", func) == 0)
		return builtin_head(e, a);
	if (strcmp("tail", func) == 0)
		return builtin_tail(e, a);
	if (strcmp("join", func) == 0)
		return builtin_join(e, a);
	if (strcmp("eval", func) == 0)
		return builtin_eval(e, a);
	if (strstr("+-/*", func))
		return builtin_op(e, a, func);

	lval_del(a);
	return lval_error("Unknown Function!");
}

void lenv_add_builtin(lenv* e, char* name, lbuiltin func)
{
	lval* k = lval_symbol(name);
	lval* v = lval_fun(func);
	lenv_put(e, k, v);
	lval_del(k); lval_del(v);
}

void lenv_add_builtins(lenv* e)
{
	lenv_add_builtin(e, "list", builtin_list);
	lenv_add_builtin(e, "head", builtin_head);
	lenv_add_builtin(e, "tail", builtin_tail);
	lenv_add_builtin(e, "eval", builtin_eval);
	lenv_add_builtin(e, "join", builtin_join);
	lenv_add_builtin(e, "def", builtin_def);
	lenv_add_builtin(e, "=",   builtin_put);
	lenv_add_builtin(e, "\\",   builtin_lambda);


	lenv_add_builtin(e, "+", builtin_add);
	lenv_add_builtin(e, "-", builtin_sub);
	lenv_add_builtin(e, "*", builtin_mul);
	lenv_add_builtin(e, "/", builtin_div);
}

lval* lval_call(lenv* e, lval* f, lval* a);

lval* lval_eval_sexpr(lenv* e, lval* v)
{
	for (int i = 0; i < v->count; i++)
		v->cell[i] = lval_eval(e, v->cell[i]);

	for (int i = 0; i < v->count; i++)
		if (v->cell[i]->type == LVAL_ERR)
			return lval_take(v, i);

	if (v->count == 0)
		return v;
	if (v->count == 1)
		return lval_eval(e, lval_take(v, 0));

	lval* f = lval_pop(v, 0);
	if (f->type != LVAL_FUN) {
		lval* err = lval_error(
			"S-Expression starts with incorrect type. "
			"Got %s, Expected %s.",
			ltype_name(f->type), ltype_name(LVAL_FUN));
		lval_del(f); lval_del(v);
		return err;
	}

	lval* result = lval_call(e, f, v);
	lval_del(f);
	return result;
}


lval* lval_eval(lenv* e, lval* v)
{
	if (v->type == LVAL_SYM) {
		lval* x = lenv_get(e, v);
		lval_del(v);
		return x;
	}

	if (v->type == LVAL_SEXPR)
		return lval_eval_sexpr(e, v);

	return v;
}

lval* lval_read_num(mpc_ast_t* t)
{
	errno = 0;
	long x = strtol(t->contents, NULL, 10);
	return errno != ERANGE ?
		lval_number(x) : lval_error("invalid number");
}

lval* lval_read(mpc_ast_t* t)
{
	if (strstr(t->tag, "number"))
		return lval_read_num(t);

	if (strstr(t->tag, "symbol"))
		return lval_symbol(t->contents);

	lval* x = NULL;
	if (strcmp(t->tag, ">") == 0)
		x = lval_sexpr();
	if (strstr(t->tag, "sexpr"))
		x = lval_sexpr();
	if (strstr(t->tag, "qexpr"))
		x = lval_qexpr();

	for (int i = 0; i < t->children_num; i++) {
		if (strcmp(t->children[i]->contents, "(") == 0)
			continue;
    		if (strcmp(t->children[i]->contents, ")") == 0)
    			continue;
		if (strcmp(t->children[i]->contents, "}") == 0)
			continue;
		if (strcmp(t->children[i]->contents, "{") == 0)
			continue;
		if (strcmp(t->children[i]->tag,  "regex") == 0)
			continue;

		x = lval_add(x, lval_read(t->children[i]));
	}

	return x;
}

lval* lval_call(lenv* e, lval* f, lval* a)
{
	if (f->builtin)
		return f->builtin(e, a);

	int given = a->count;
	int total = f->formals->count;

	while (a->count) {
		if (f->formals->count == 0) {
			lval_del(a);
			return lval_error("Function passed too many arguments. "
				"Got %i, Expected %i.", given, total);
		}

		lval* sym = lval_pop(f->formals, 0);
		if (strcmp(sym->symbol, "&") == 0) {
			if (f->formals->count != 1) {
				lval_del(a);
				return lval_error("Function format invalid. "
	  				"Symbol '&' not followed by single symbol.");
			}

			lval* nsym = lval_pop(f->formals, 0);
			lenv_put(f->env, nsym, builtin_list(e, a));
			lval_del(sym); lval_del(nsym);
			break;
		}

		lval* val = lval_pop(a, 0);
		lenv_put(f->env, sym, val);
		lval_del(sym); lval_del(val);
	}

	lval_del(a);

	if (f->formals->count > 0 && strcmp(f->formals->cell[0]->symbol, "&") == 0) {
		if (f->formals->count != 2) {
			return lval_error("Function format invalid. "
				"Symbol '&' not followed by single symbol.");
		}

		lval_del(lval_pop(f->formals, 0));

		lval* sym = lval_pop(f->formals, 0);
		lval* val = lval_qexpr();

		lenv_put(f->env, sym, val);
		lval_del(sym); lval_del(val);
	}

	if (f->formals->count == 0) {
		f->env->par = e;
		return builtin_eval(f->env,
			lval_add(lval_sexpr(), lval_copy(f->body)));
	} else {
		return lval_copy(f);
	}
}



int main(int argc, char** argv)
{
	mpc_parser_t* Number = mpc_new("number");
	mpc_parser_t* Symbol = mpc_new("symbol");
	mpc_parser_t* Sexpr = mpc_new("sexpr");
	mpc_parser_t* Qexpr = mpc_new("qexpr");
	mpc_parser_t* Expr = mpc_new("expr");
	mpc_parser_t* Rlisp = mpc_new("rlisp");

	mpca_lang(MPCA_LANG_DEFAULT,
		"                                                                \
			number   : /-?[0-9]+/ ;                                  \
			symbol   : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/;             \
			sexpr    : '(' <expr>* ')' ;                             \
			qexpr    : '{' <expr>* '}' ;                             \
			expr     : <number> | <symbol> | <sexpr> | <qexpr>;      \
			rlisp    : /^/ <expr>* /$/ ;                             \
		",
		Number, Symbol, Sexpr, Qexpr, Expr, Rlisp);

	puts("Rlisp Version 0.0");
	puts("Press Ctrl+c to Exit\n");

	lenv* e = lenv_new();
	lenv_add_builtins(e);

	while (1) {
		char* input = readline("rlisp> ");
		add_history(input);

		mpc_result_t r;

		if (mpc_parse("<stdin>", input, Rlisp, &r)) {
			lval* x = lval_eval(e, lval_read(r.output));
			lval_println(x);
			lval_del(x);
			mpc_ast_delete(r.output);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	lenv_del(e);
	mpc_cleanup(4, Number, Symbol, Sexpr, Qexpr, Expr, Rlisp);

	return 0;
}
