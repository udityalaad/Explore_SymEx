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
from io import StringIO


class Ast(object):
    """Base class of AST hierarchy"""

    def __str__(self):
        """Print AST as a string"""
        buf = StringIO()
        pv = PrintVisitor(out=buf)
        pv.visit(self)
        return buf.getvalue()

    def __repr__(self):
        return str(self)


class StmtList(Ast):
    """A list of statements"""

    def __init__(self, s):
        self.stmts = s

    def __eq__(self, other):
        return type(self) == type(other) and self.stmts == other.stmts


class Stmt(Ast):
    """A single statement"""

    pass


class SkipStmt(Stmt):
    """A skip statement"""

    def __eq__(self, other):
        return type(self) == type(other)


class PrintStateStmt(Stmt):
    """Print state"""

    def __eq__(self, other):
        return type(self) == type(other)


class AsgnStmt(Stmt):
    """An assignment statement"""

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __eq__(self, other):
        return (
            type(self) == type(other)
            and self.lhs == other.lhs
            and self.rhs == other.rhs
        )


class IfStmt(Stmt):
    """If-then-else statement"""

    def __init__(self, cond, then_stmt, else_stmt=None):
        self.cond = cond
        self.then_stmt = then_stmt
        self.else_stmt = else_stmt

    def has_else(self):
        return self.else_stmt is not None

    def __eq__(self, other):
        return (
            type(self) == type(other)
            and self.cond == other.cond
            and self.then_stmt == other.then_stmt
            and self.else_stmt == other.else_stmt
        )


class WhileStmt(Stmt):
    """While statement"""

    def __init__(self, cond, body, inv=None):
        self.cond = cond
        self.body = body
        self.inv = inv

    def __eq__(self, other):
        return (
            type(self) == type(other)
            and self.cond == other.cond
            and self.body == other.body
            and self.inv == other.inv
        )


class AssertStmt(Stmt):
    """Assert statement"""

    def __init__(self, cond):
        self.cond = cond

    def __eq__(self, other):
        return type(self) == type(other) and self.cond == other.cond


class AssumeStmt(Stmt):
    """Assume statement"""

    def __init__(self, cond):
        self.cond = cond

    def __eq__(self, other):
        return type(self) == type(other) and self.cond == other.cond


class HavocStmt(Stmt):
    """Havoc statement"""

    def __init__(self, var_list):
        self.vars = var_list

    def __eq__(self, other):
        return type(self) == type(other) and self.vars == other.vars


class Exp(Ast):
    """An expression"""

    def __init__(self, op, args):
        if isinstance(op, list):
            self.op = op[0]
        else:
            self.op = op
        self.args = args

    def __eq__(self, other):
        return (
            type(self) == type(other)
            and self.op == other.op
            and self.args == other.args
        )

    def arg(self, i):
        return self.args[i]

    def is_binary(self):
        return len(self.args) == 2

    def is_unary(self):
        return len(self.args) == 1


class BExp(Exp):
    """A Boolean expression"""

    def __init__(self, op, args):
        super(BExp, self).__init__(op, args)


class RelExp(BExp):
    """A relational comparison expression"""

    def __init__(self, lhs, op, rhs):
        super(RelExp, self).__init__(op, [lhs, rhs])


class AExp(Exp):
    """An arithmetic expression"""

    def __init__(self, op, args):
        super(AExp, self).__init__(op, args)


class Const(Ast):
    """A constant"""

    def __init__(self, val):
        self.val = val

    def __str__(self):
        return str(self.val)

    def __repr__(self):
        return repr(self.val)

    def __eq__(self, other):
        return type(self) == type(other) and self.val == other.val

    def __hash__(self):
        return hash(self.val)


class IntConst(Const):
    """An integer constant"""

    def __init__(self, val):
        super(IntConst, self).__init__(int(val))


class BoolConst(Const):
    """A Boolean constant"""

    def __init__(self, val):
        super(BoolConst, self).__init__(val)


class IntVar(Ast):
    """An integer variable"""

    def __init__(self, name):
        self.name = name

    def __str__(self):
        return str(self.name)

    def __repr__(self):
        return repr(self.name)

    def __eq__(self, other):
        return type(self) == type(other) and self.name == other.name

    def __hash__(self):
        return hash(self.name)


def parse_file(filename):
    with open(filename) as f:
        text = f.read()
    return parse_string(text, filename=filename)


def parse_string(v, filename="<builit-in>"):
    import wlang.parser as parser
    import wlang.semantics as sem

    p = parser.WhileLangParser(parseinfo=False)
    ast = p.parse(v, "start", filename=filename, semantics=sem.WlangSemantics())
    return ast


class AstVisitor(object):
    """Base class for AST visitor"""

    def __init__(self):
        pass

    def visit(self, node, *args, **kwargs):
        """Visit a node."""
        method = "visit_" + node.__class__.__name__
        visitor = getattr(self, method)
        return visitor(node, *args, **kwargs)

    def visit_BoolConst(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Const.__name__)
        return visitor(node, *args, **kwargs)

    def visit_IntConst(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Const.__name__)
        return visitor(node, *args, **kwargs)

    def visit_AExp(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Exp.__name__)
        return visitor(node, *args, **kwargs)

    def visit_BExp(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Exp.__name__)
        return visitor(node, *args, **kwargs)

    def visit_RelExp(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + BExp.__name__)
        return visitor(node, *args, **kwargs)

    def visit_IntVar(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + AExp.__name__)
        return visitor(node, *args, **kwargs)

    def visit_SkipStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_AsgnStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_IfStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_WhileStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_AssertStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_AssumeStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)

    def visit_HavocStmt(self, node, *args, **kwargs):
        visitor = getattr(self, "visit_" + Stmt.__name__)
        return visitor(node, *args, **kwargs)


class PrintVisitor(AstVisitor):
    """A printing visitor"""

    def __init__(self, out=None):
        super(PrintVisitor, self).__init__()
        if out is None:
            self.out = sys.stdout
        else:
            self.out = out

    def _indent(self, **kwargs):
        self._write(" " * kwargs["indent"])

    def _write(self, v):
        self.out.write(str(v))

    def _open_brkt(self, **kwargs):
        if not kwargs["no_brkt"]:
            self._write("(")

    def _close_brkt(self, **kwargs):
        if not kwargs["no_brkt"]:
            self._write(")")

    def visit(self, node, indent=0, no_brkt=False):
        super(PrintVisitor, self).visit(node, indent=indent, no_brkt=no_brkt)

    def visit_IntVar(self, node, *args, **kwargs):
        self._write(node.name)

    def visit_BoolConst(self, node, *args, **kwargs):
        if node.val:
            self._write("true")
        else:
            self._write("false")

    def visit_IntConst(self, node, *args, **kwargs):
        self._write(node.val)

    def visit_Exp(self, node, *args, **kwargs):
        if node.is_unary():
            self._write(node.op)
            self.visit(node.arg(0))
        else:
            self._open_brkt(**kwargs)
            self.visit(node.arg(0))
            for a in node.args[1:]:
                self._write(" ")
                self._write(node.op)
                self._write(" ")
                self.visit(a)
            self._close_brkt(**kwargs)

    def visit_SkipStmt(self, node, *args, **kwargs):
        self._write("skip")

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        self._write("print_state")

    def visit_StmtList(self, node, *args, **kwargs):
        if node.stmts is None or len(node.stmts) == 0:
            return

        indent_lvl = kwargs["indent"]
        if len(node.stmts) > 1:
            self._indent(**kwargs)
            self._write("{\n")
            indent_lvl = indent_lvl + 2

        self._indent(indent=indent_lvl)
        self.visit(node.stmts[0], indent=kwargs["indent"] + 2)

        if len(node.stmts) > 1:
            for s in node.stmts[1:]:
                self._write(";\n")
                self._indent(indent=indent_lvl)
                self.visit(s, indent=indent_lvl)

        if len(node.stmts) > 1:
            self._write("\n")
            self._indent(**kwargs)
            self._write("}")

    def visit_AsgnStmt(self, node, *args, **kwargs):
        self.visit(node.lhs)
        self._write(" := ")
        self.visit(node.rhs, no_brkt=True)

    def visit_AssertStmt(self, node, *args, **kwargs):
        self._write("assert ")
        self.visit(node.cond, no_brkt=True)

    def visit_AssumeStmt(self, node, *args, **kwargs):
        self._write("assume ")
        self.visit(node.cond, no_brkt=True)

    def visit_HavocStmt(self, node, *args, **kwargs):
        self._write("havoc ")
        assert len(node.vars) >= 1
        self.visit(node.vars[0])
        for v in node.vars[1:]:
            self._write(", ")
            self.visit(v)

    def visit_IfStmt(self, node, *args, **kwargs):
        self._write("if ")
        self.visit(node.cond, no_brkt=True)
        self._write(" then")
        self._write("\n")
        self._indent(indent=kwargs["indent"] + 2)
        self.visit(node.then_stmt, indent=kwargs["indent"] + 2)
        if node.has_else():
            self._write("\n")
            self._indent(**kwargs)
            self._write("else\n")
            self._indent(indent=kwargs["indent"] + 2)
            self.visit(node.else_stmt, indent=kwargs["indent"] + 2)

    def visit_WhileStmt(self, node, *args, **kwargs):
        self._write("while ")
        self.visit(node.cond, no_brkt=True)
        self._write(" do")
        self._write("\n")
        self._indent(indent=kwargs["indent"] + 2)
        self.visit(node.body, indent=kwargs["indent"] + 2)
