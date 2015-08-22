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
	LVAL_NUM,
	LVAL_ERR
};

typedef struct {
	int type;
	long number;
	int error;
} lval;



lval lval_number(long x)
{
	lval val;
	val.type = LVAL_NUM;
	val.number = x;
	return val;
}

lval lval_error(int x)
{
	lval val;
	val.type = LVAL_ERR;
	val.error = x;
	return val;
}

void lval_print(lval v)
{
	switch (v.type) {
		case LVAL_NUM: printf("%li", v.number);
			break;

		case LVAL_ERR:
			if (v.error == LERR_DIV_ZERO)
				printf("Error: Division By Zero!");
			if (v.error == LERR_BAD_OP)
				printf("Error: Invalid Operator!");
			if (v.error == LERR_BAD_NUM)
				printf("Error: Invalid Number!");
			break;
	}
}

void lval_println(lval v)
{
	lval_print(v);
	putchar('\n');
}

lval eval_operation(lval x, char* op, lval y) {
	if (x.type == LVAL_ERR) {
		return x;
	}
	if (y.type == LVAL_ERR) {
		return y;
	}

	if (strcmp(op, "+") == 0)
		return lval_number(x.number + y.number);
	if (strcmp(op, "-") == 0)
		return lval_number(x.number - y.number);
	if (strcmp(op, "*") == 0)
		return lval_number(x.number * y.number);
	if (strcmp(op, "/") == 0) {
		return y.number == 0
		? lval_error(LERR_DIV_ZERO)
		: lval_number(x.number / y.number);
	}

	return lval_error(LERR_BAD_OP);
}

lval eval(mpc_ast_t* t) {
	if (strstr(t->tag, "number")) {
		errno = 0;
		long x = strtol(t->contents, NULL, 10);
		return errno != ERANGE ? lval_number(x) : lval_error(LERR_BAD_NUM);
	}

	char* operator = t->children[1]->contents;

	lval x = eval(t->children[2]);

	int i = 3;
	while (strstr(t->children[i]->tag, "expr")) {
		x = eval_operation(x, operator, eval(t->children[i]));
		i++;
	}

	return x;
}

int main(int argc, char** argv)
{
	mpc_parser_t* Number   = mpc_new("number");
	mpc_parser_t* Operator = mpc_new("operator");
	mpc_parser_t* Expr     = mpc_new("expr");
	mpc_parser_t* Rlisp    = mpc_new("rlisp");

	mpca_lang(MPCA_LANG_DEFAULT,
		"                                                   \
			number   : /-?[0-9]+/ ;                             \
			operator : '+' | '-' | '*' | '/' ;                  \
			expr     : <number> | '(' <operator> <expr>+ ')' ;  \
			rlisp    : /^/ <operator> <expr>+ /$/ ;             \
		",
		Number, Operator, Expr, Rlisp);

	puts("Rlisp Version 0.0");
	puts("Press Ctrl+c to Exit\n");

	while (1) {
		char* input = readline("rlisp> ");
		add_history(input);

		mpc_result_t r;

		if (mpc_parse("<stdin>", input, Rlisp, &r)) {
			lval result = eval(r.output);
			lval_println(result);
			mpc_ast_delete(r.output);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	mpc_cleanup(4, Number, Operator, Expr, Rlisp);

	return 0;
}
