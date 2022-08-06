# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

from . import ast


class WlangSemantics(object):
    def __init__(self):
        pass

    def start(self, prg, *args, **kwargs):
        if len(prg.stmts) == 1:
            return prg.stmts[0]
        return prg

    def stmt_list(self, stmts, *args, **kwargs):
        return ast.StmtList(stmts)

    def asgn_stmt(self, stmt, *args, **kwargs):
        return ast.AsgnStmt(stmt.lhs, stmt.rhs)

    def skip_stmt(self, stmt, *args, **kwargs):
        return ast.SkipStmt()

    def print_state_stmt(self, stmt, *args, **kwargs):
        return ast.PrintStateStmt()

    def if_stmt(self, if_stmt, *args, **kwargs):
        return ast.IfStmt(if_stmt.cond, if_stmt.then_stmt, if_stmt.else_stmt)

    def while_stmt(self, while_stmt, *args, **kwargs):
        return ast.WhileStmt(while_stmt.cond, while_stmt.body, while_stmt.inv)

    def assert_stmt(self, assert_stmt, *args, **kwargs):
        return ast.AssertStmt(assert_stmt.cond)

    def assume_stmt(self, assume_stmt, *args, **kwargs):
        return ast.AssumeStmt(assume_stmt.cond)

    def havoc_stmt(self, havoc_stmt, *args, **kwargs):
        assert len(havoc_stmt) >= 1
        return ast.HavocStmt(havoc_stmt.vars)

    def bool_const(self, const, *args, **kwargs):
        if str(const) == "true":
            val = True
        else:
            val = False
        return ast.BoolConst(val)

    def bexp(self, exp, *args, **kwargs):
        return self.bterm(exp, args, kwargs)

    def bterm(self, exp, *args, **kwargs):
        if exp.op is None:
            return exp.args
        assert len(exp.args) > 1
        return ast.BExp(str(exp.op), exp.args)

    def bfactor(self, exp, *args, **kwargs):
        if exp.op is not None:
            return ast.BExp(str(exp.op), [exp.arg])
        return exp.arg

    def rexp(self, exp, *args, **kwargs):
        return ast.RelExp(exp.lhs, str(exp.op), exp.rhs)

    def aexp(self, exp, *args, **kwargs):
        return exp

    def addition(self, exp, *args, **kwargs):
        return self.subtraction(exp, *args, **kwargs)

    def subtraction(self, exp, *args, **kwargs):
        return self.mult(exp, *args, **kwargs)

    def term(self, exp, *args, **kwargs):
        return exp

    def mult(self, exp, *args, **kwargs):
        return self.division(exp, *args, **kwargs)

    def division(self, exp, *args, **kwargs):
        return ast.AExp(str(exp.op), [exp.lhs, exp.rhs])

    def name(self, ident, *args, **kwargs):
        return ast.IntVar(ident)

    def number(self, ident, *args, **kwargs):
        return ast.IntConst(int(str(ident)))

    def neg_number(self, ident, *args, **kwargs):
        return ast.IntConst(-1 * ident.val)
