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

import sys
from functools import reduce
from io import StringIO

from . import ast


class State(object):
    def __init__(self):
        self.env = dict()

    def __repr__(self):
        return str(self)

    def __str__(self):
        buf = StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(": ")
            buf.write(str(v))
            buf.write("\n")

        return buf.getvalue()


class Interpreter(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        return self.visit(ast, state=state)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs["state"].env[node.name]

    def visit_Const(self, node, *args, **kwargs):
        return node.val

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs

        assert False

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return not kids[0]

        fn = None
        base = None
        if node.op == "and":
            fn = lambda x, y: x and y
            base = True
        elif node.op == "or":
            fn = lambda x, y: x or y
            base = False

        assert fn is not None
        return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return kwargs["state"]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs["state"])
        return kwargs["state"]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        st.env[node.lhs.name] = self.visit(node.rhs, *args, **kwargs)
        return st

    def visit_IfStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        if cond:
            return self.visit(node.then_stmt, *args, **kwargs)
        else:
            if node.has_else():
                return self.visit(node.else_stmt, *args, **kwargs)
            else:
                return kwargs["state"]

    def visit_WhileStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)

        if cond:
            # execute the body
            st = self.visit(node.body, *args, **kwargs)
            # execute the loop again
            kwargs["state"] = st
            return self.visit(node, *args, **kwargs)
        else:
            # loop condition is false, don't execute the body
            return kwargs["state"]

    def visit_AssertStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        if not cond:
            assert False, "Assertion error: " + str(node)
        return kwargs["state"]

    def visit_AssumeStmt(self, node, *args, **kwargs):
        return self.visit_AssertStmt(node, *args, **kwargs)

    def visit_StmtList(self, node, *args, **kwargs):
        st = kwargs["state"]

        nkwargs = dict(kwargs)
        for stmt in node.stmts:
            nkwargs["state"] = st
            st = self.visit(stmt, *args, **nkwargs)
        return st

    def visit_HavocStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        for v in node.vars:
            # assign 0 as the default value
            st.env[v.name] = 0
        return st


def _parse_args():
    import argparse

    ap = argparse.ArgumentParser(prog="int", description="WLang Interpreter")
    ap.add_argument("in_file", metavar="FILE", help="WLang program to run")
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = State()
    interp = Interpreter()
    interp.run(prg, st)
    return 0


if __name__ == "__main__":
    sys.exit(main())
