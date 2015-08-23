#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>

#include "mpc/mpc.h"

enum {
	LERR_DIV_ZERO,
	LERR_BAD_OP,
	LERR_BAD_NUM
};

enum {
	LVAL_ERR,
	LVAL_NUM,
	LVAL_SYM,
	LVAL_SEXPR
};

typedef struct lval {
	int type;
	long number;
	char* error;
	char* symbol;
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

lval* lval_error(char* m)
{
	lval* val = malloc(sizeof(lval));
	val->type = LVAL_ERR;
	val->error = malloc(strlen(m) + 1);
	strcpy(val->error, m);
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
			for (int i = 0; i < v->count; i++) {
				lval_del(v->cell[i]);
			}
			free(v->cell);
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
	}
}

void lval_println(lval* v)
{
	lval_print(v);
	putchar('\n');
}

lval* builtin_op(lval* a, char* op)
{
	for (int i = 0; i < a->count; i++) {
		if (a->cell[i]->type != LVAL_NUM) {
			lval_del(a);
			return lval_error("Cannot operate on non-number!");
		}
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

lval* lval_eval(lval* v);

lval* lval_eval_sexpr(lval* v) {
	for (int i = 0; i < v->count; i++) {
		v->cell[i] = lval_eval(v->cell[i]);
	}

	for (int i = 0; i < v->count; i++) {
		if (v->cell[i]->type == LVAL_ERR)
			return lval_take(v, i);
  	}

	if (v->count == 0)
		return v;

	if (v->count == 1)
		return lval_take(v, 0);

	lval* f = lval_pop(v, 0);
	if (f->type != LVAL_SYM) {
		lval_del(f); lval_del(v);
		return lval_error("S-expression Does not start with symbol.");
	}

	lval* result = builtin_op(v, f->symbol);
	lval_del(f);
	return result;
}

lval* lval_eval(lval* v) {
	if (v->type == LVAL_SEXPR)
		return lval_eval_sexpr(v);
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






int main(int argc, char** argv)
{
	mpc_parser_t* Number   = mpc_new("number");
	mpc_parser_t* Symbol = mpc_new("symbol");
	mpc_parser_t* Sexpr = mpc_new("sexpr");
	mpc_parser_t* Expr     = mpc_new("expr");
	mpc_parser_t* Rlisp    = mpc_new("rlisp");

	mpca_lang(MPCA_LANG_DEFAULT,
		"                                                           \
			number   : /-?[0-9]+/ ;                             \
			symbol : '+' | '-' | '*' | '/' ;                    \
			sexpr  : '(' <expr>* ')' ;                          \
			expr     : <number> | <symbol> | <sexpr> ;  \
			rlisp    : /^/ <expr>* /$/ ;               \
		",
		Number, Symbol, Sexpr, Expr, Rlisp);

	puts("Rlisp Version 0.0");
	puts("Press Ctrl+c to Exit\n");

	while (1) {
		char* input = readline("rlisp> ");
		add_history(input);

		mpc_result_t r;

		if (mpc_parse("<stdin>", input, Rlisp, &r)) {
			lval* x = lval_eval(lval_read(r.output));
			lval_println(x);
			lval_del(x);
			mpc_ast_delete(r.output);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	mpc_cleanup(4, Number, Symbol, Sexpr, Expr, Rlisp);

	return 0;
}
