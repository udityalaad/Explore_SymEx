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

import io 
import z3

from . import ast, int, undef_visitor
from functools import reduce
from random import randint

class Dynamic_State(object):
    def __init__(self, solver=None):
        # sym_environment mapping variables to symbolic & concrete constants
        self.sym_env = dict()
        self.con_env = dict()

        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    # def pick_concrete(self):
    #     """Pick a concrete state consistent with the symbolic state.
    #        Return None if no such state exists"""
    #     res = self._solver.check()
    #     if res != z3.sat:
    #         return None
    #     model = self._solver.model()
    #     st = int.State()
    #     for (k, v) in self.sym_env.items():
    #         st.env[k] = model.eval(v)
    #     return st

    def pick_concrete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        con = dict()
        for (k, v) in self.sym_env.items():
            con[k] = model.eval(v, model_completion = True).as_long()
        return con

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = Dynamic_State()
        child.sym_env = dict(self.sym_env)
        child.con_env = dict(self.con_env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        buf.write('....sym:')

        for k, v in self.sym_env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')

        buf.write('....con:')
        for k, v in self.con_env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')

        buf.write('....pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class DynamicSymExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        kwargs = dict()
        kwargs["state"] = state
        kwargs["exec"] = "concrete"
        kwargs["cond"] = "false"

        args = []
        
        return [res["state"] for res in self.visit(ast, *args, **kwargs) if not res["state"].is_error()]
        

    def visit_IntVar(self, node, *args, **kwargs):
        # Symbolic Execution
        if (kwargs["exec"] == "symbolic"):
            return kwargs['state'].sym_env[node.name]
        
        # Concrete Execution
        else:
            return kwargs['state'].con_env[node.name]


    def visit_BoolConst(self, node, *args, **kwargs):
        # Symbolic Execution
        if (kwargs["exec"] == "symbolic"):
            return z3.BoolVal(node.val)

        # Concrete Execution
        else:
            return node.val


    def visit_IntConst(self, node, *args, **kwargs):
        # Symbolic Execution
        if (kwargs["exec"] == "symbolic"):
            return z3.IntVal(node.val)

        # Concrete Execution
        else:
            return node.val

        
    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)

        if node.op == "<=":
            return lhs <= rhs
        elif node.op == "<":
            return lhs < rhs
        elif node.op == "=":
            return lhs == rhs
        elif node.op == ">":
            return lhs > rhs
        elif node.op == ">=":
            return lhs >= rhs

        assert False


    def visit_BExp(self, node, *args, **kwargs):
        # Symbolic Execution
        if (kwargs["exec"] == "symbolic"):            
            kids = [self.visit(a, *args, **kwargs) for a in node.args]

            if node.op == "not":
                assert node.is_unary()
                assert len(kids) == 1
                return z3.Not(kids[0])

            fn = None
            if node.op == "and":
                fn = lambda x, y: z3.And(x, y)
            elif node.op == "or":
                fn = lambda x, y: z3.Or(x, y)

            assert fn is not None
            return reduce(fn, kids)

        # Concrete Execution
        else:
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
        if  kwargs["cond"] == "true"  and  any(ch in str(node) for ch in list(['*', '/'])):
            kwargs["exec"] = "concrete"

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
        return [kwargs]


    def visit_PrintStateStmt(self, node, *args, **kwargs):
        return [kwargs]


    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs["state"]

        sym_dict = kwargs.copy()
        sym_dict["exec"] = "symbolic"
        st.sym_env[node.lhs.name] = self.visit(node.rhs, *args, **sym_dict)

        con_dict = kwargs.copy()
        con_dict["exec"] = "concrete"
        st.con_env[node.lhs.name] = self.visit(node.rhs, *args, **con_dict)

        ret_dict = kwargs.copy()
        ret_dict["state"] = st
        return [ret_dict]


    def concretize (self, expr, *args, **kwargs):
        # print("Concretizze")
        # print(expr)
        st = kwargs["state"]

        uv = undef_visitor.UndefVisitor()
        uv.check(expr)
        pc_concretizations = []

        for e in uv.get_undefs():
            temp_str = str(e) + " = " + str(st.con_env[str(e)])
            str_ast_input = "assume " + temp_str
            
            ast_conc = ast.parse_string(str_ast_input)

            kwargs["exec"] = "symbolic"
            pc_concretizations.append(self.visit(ast_conc.cond, *args, **kwargs))

        return pc_concretizations


    def visit_IfStmt(self, node, *args, **kwargs):
        st = kwargs["state"]

        concrete_branch = None
        out = []

        st1, st2 = st.fork()
        
        # Concretize, if applicable
        if str(type(node.cond)) == "<class 'wlang.ast.RelExp'>":
            if any(ch in list(['*', '/'])  for ch in str(node.cond.args[0])):
                for pc_concretization in self.concretize(node.cond.args[0], *args, **kwargs):
                    st1.add_pc(pc_concretization)
                    st2.add_pc(pc_concretization)

                lhs_kwargs = kwargs.copy()
                lhs_kwargs["exec"] = "concrete"
                node.cond.args[0] = ast.parse_string("random := " + str(self.visit(node.cond.args[0], *args, **lhs_kwargs))).rhs

            if any(ch in list(['*', '/'])  for ch in str(node.cond.args[1])):
                for pc_concretization in self.concretize(node.cond.args[1], *args, **kwargs):
                    st1.add_pc(pc_concretization)
                    st2.add_pc(pc_concretization)

                rhs_kwargs = kwargs.copy()
                rhs_kwargs["exec"] = "concrete"
                node.cond.args[1] = ast.parse_string("random := " + str(self.visit(node.cond.args[1], *args, **rhs_kwargs))).rhs
                
        sym_dict = kwargs.copy()
        sym_dict["exec"] = "symbolic"
        sym_dict["cond"] = "true"
        sym_cond = self.visit(node.cond, *args, **sym_dict)

        st1.add_pc(sym_cond)
        st2.add_pc(z3.Not(sym_cond))


        # ---------------- Concrete Execution ------------------
        conc_dict = kwargs.copy()
        conc_dict["exec"] = "concrete"
        conc_cond = self.visit(node.cond, *args, **conc_dict)

        if conc_cond:
            concrete_branch = True

            dict_conc_if = kwargs.copy()
            dict_conc_if["state"] = st1
            
            out.extend(self.visit(node.then_stmt, *args, **dict_conc_if))
        else:
            concrete_branch = False

            dict_conc_else = kwargs.copy()
            dict_conc_else["state"] = st2

            if node.has_else():
                out.extend(self.visit(node.else_stmt, *args, **dict_conc_else))
            else:
                out.extend([dict_conc_else])


        # ---------------- Symbolic Execution ------------------
        # If concrete execution took the 'False' branch, then symbolic execution should take the 'True' branch
        if not concrete_branch:
            if not st1.is_empty():
                dict_if_true = kwargs.copy()
                dict_if_true["state"] = st1
                dict_if_true["state"].con_env = st1.pick_concrete()

                res_dict_if_true = self.visit(node.then_stmt, *args, **dict_if_true)

                out.extend(res_dict_if_true)
            else:
                st1.mk_error()

                dict_if_false = kwargs.copy()
                dict_if_false["state"] = st1

                out.extend([dict_if_false])
        
        else:   # If concrete execution took the 'True' branch, then symbolic execution takes the 'False' branch
            if not st2.is_empty():
                dict_else_true = kwargs.copy()
                dict_else_true["state"] = st2
                dict_else_true["state"].con_env = st2.pick_concrete()

                if node.has_else():
                    res_dict_else_true = self.visit(node.else_stmt, *args, **dict_else_true)
                    out.extend(res_dict_else_true)
                else:
                    out.extend([dict_else_true])
            else:
                st2.mk_error()

                dict_else_false = kwargs.copy()
                dict_else_false["state"] = st2

                out.extend([dict_else_false])

        return out


    def visit_WhileStmt(self, node, *args, **kwargs):
        st = kwargs["state"]

        concrete_branch = None
        out = []

        cnt = 0
        if len(args) != 0:
            cnt = args[0]

        sym_dict = kwargs.copy()
        sym_dict["exec"] = "symbolic"
        sym_dict["cond"] = "true"
        sym_cond = self.visit(node.cond, *args, **sym_dict)
        st1, st2 = st.fork()

        # Concretize, if applicable
        if str(type(node.cond)) == "<class 'wlang.ast.RelExp'>":
            if any(ch in list(['*', '/'])  for ch in str(node.cond.args[0])):
                for pc_concretization in self.concretize(node.cond.args[0], *args, **kwargs):
                    st1.add_pc(pc_concretization)
                    st2.add_pc(pc_concretization)

                lhs_kwargs = kwargs.copy()
                lhs_kwargs["exec"] = "concrete"
                node.cond.args[0] = ast.parse_string("random := " + str(self.visit(node.cond.args[0], *args, **lhs_kwargs))).rhs

            if any(ch in list(['*', '/'])  for ch in str(node.cond.args[1])):
                for pc_concretization in self.concretize(node.cond.args[1], *args, **kwargs):
                    st1.add_pc(pc_concretization)
                    st2.add_pc(pc_concretization)

                rhs_kwargs = kwargs.copy()
                rhs_kwargs["exec"] = "concrete"
                node.cond.args[1] = ast.parse_string("random := " + str(self.visit(node.cond.args[1], *args, **rhs_kwargs))).rhs

        st1.add_pc(sym_cond)
        st2.add_pc(z3.Not(sym_cond))

        # ---------------- Concrete Execution ------------------
        conc_dict = kwargs.copy()
        conc_dict["exec"] = "concrete"
        conc_cond = self.visit(node.cond, *args, **conc_dict)

        if conc_cond:
            concrete_branch = True
            
            if cnt < 10:
                dict_conc_if = kwargs.copy()
                dict_conc_if["state"] = st1

                # execute the body
                body_dict_conc_if_true = self.visit(node.body, 0, **dict_conc_if)

                # execute the loop again
                res_dict_conc_if_true = self.visit(node, cnt + 1, **body_dict_conc_if_true[0])

                out.extend(res_dict_conc_if_true)

        else:
            concrete_branch = False

            # loop condition is false, don't execute the body            
            dict_conc_else = kwargs.copy()
            dict_conc_else["state"] = st2

            out.extend([dict_conc_else])


        # ---------------- Symbolic Execution ------------------
        # if (node.inv != None):
        #     sta, stb = st.fork()

        #     inv = self.visit(node.inv, *args, **kwargs)
        #     sta.add_pc(inv)
        #     stb.add_pc(z3.Not(inv))

        #     if sta.is_empty():
        #         # print(st)
        #         print("Error: Invariant Assertion has failed for this state")
        #         sta.mk_error()

        #         return [sta], kwargs

        #     if not stb.is_empty():
        #         print("Note: Invariant Assertion can fail")
        #         stb.mk_error()

        #     st = sta
        
        # If concrete execution took the 'False' branch, then symbolic execution should take the 'True' branch
        if not concrete_branch:
            if not st1.is_empty()  and  cnt < 10:
                dict_if_true = kwargs.copy()
                dict_if_true["state"] = st1
                dict_if_true["state"].con_env = st1.pick_concrete()

                res_dict_if_true = self.visit(node.body, 0, **dict_if_true)
                
                sts_dict_new = []
                for i in range(len(res_dict_if_true)):
                    if not res_dict_if_true[i]["state"].is_error():
                        sts_dict_new.extend(self.visit_WhileStmt(node, cnt + 1, **res_dict_if_true[i]))
                
                res_dict_if_true = sts_dict_new
                
                out.extend(res_dict_if_true)
            else:
                st1.mk_error()

                dict_if_false = kwargs.copy()
                dict_if_false["state"] = st1

                out.extend([dict_if_false])

        else:   # If concrete execution took the 'True' branch, then symbolic execution should take the 'False' branch
            if not st2.is_empty():
                dict_else_true = kwargs.copy()
                dict_else_true["state"] = st2
                dict_else_true["state"].con_env = st2.pick_concrete()

                out.extend([dict_else_true])
            else:
                st2.mk_error()

                dict_else_false = kwargs.copy()
                dict_else_false["state"] = st2

                out.extend([dict_else_false])

        return out


    def visit_AssertStmt(self, node, *args, **kwargs):
        st = kwargs["state"]

        concrete_branch = None
        out = []
        
        sym_dict = kwargs.copy()
        sym_dict["exec"] = "symbolic"
        sym_dict["cond"] = "true"
        sym_cond = self.visit(node.cond, *args, **sym_dict)
        st1, st2 = st.fork()

        # Concretize, if applicable
        if str(type(node.cond)) == "<class 'wlang.ast.RelExp'>":
            if any(ch in list(['*', '/'])  for ch in str(node.cond.args[0])):
                for pc_concretization in self.concretize(node.cond.args[0], *args, **kwargs):
                    st1.add_pc(pc_concretization)
                    st2.add_pc(pc_concretization)

                lhs_kwargs = kwargs.copy()
                lhs_kwargs["exec"] = "concrete"
                node.cond.args[0] = ast.parse_string("random := " + str(self.visit(node.cond.args[0], *args, **lhs_kwargs))).rhs

            if any(ch in list(['*', '/'])  for ch in str(node.cond.args[1])):
                for pc_concretization in self.concretize(node.cond.args[1], *args, **kwargs):
                    st1.add_pc(pc_concretization)
                    st2.add_pc(pc_concretization)

                rhs_kwargs = kwargs.copy()
                rhs_kwargs["exec"] = "concrete"
                node.cond.args[1] = ast.parse_string("random := " + str(self.visit(node.cond.args[1], *args, **rhs_kwargs))).rhs

        st1.add_pc(sym_cond)
        st2.add_pc(z3.Not(sym_cond))


        # ---------------- Concrete Execution ------------------
        conc_dict = kwargs.copy()
        conc_dict["exec"] = "concrete"
        conc_cond = self.visit(node.cond, *args, **conc_dict)

        if conc_cond:
            concrete_branch = True

            dict_conc_if = kwargs.copy()
            dict_conc_if["state"] = st1
            
            out.extend([dict_conc_if])
        else:
            concrete_branch = False

            st2.mk_error()
            print("Assertion Can Fail: " + str(node))

            dict_conc_else = kwargs.copy()
            dict_conc_else["state"] = st2

            out.extend([dict_conc_else])


        # ---------------- Symbolic Execution ------------------
        # If concrete execution took the 'False' branch, then symbolic execution should take the 'True' branch
        if not concrete_branch:
            if not st1.is_empty():
                dict_if_true = kwargs.copy()
                dict_if_true["state"] = st1
                dict_if_true["state"].con_env = st1.pick_concrete()

                out.extend([dict_if_true])
            else:
                st1.mk_error()
                print("Assertion always Fails: " + str(node))

                dict_if_false = kwargs.copy()
                dict_if_false["state"] = st1

                out.extend([dict_if_false])
        
        else:   # If concrete execution took the 'True' branch, then symbolic execution takes the 'False' branch
            if not st2.is_empty():
                st2.mk_error()
                print("Assertion Can Fail: " + str(node))

                dict_else_true = kwargs.copy()
                dict_else_true["state"] = st2
                out.extend([dict_else_true])

        return out


    def visit_AssumeStmt(self, node, *args, **kwargs):
        return self.visit_AssertStmt(node, *args, **kwargs)
        

    def visit_HavocStmt(self, node, *args, **kwargs):
        st = kwargs["state"]

        for v in node.vars:
            st.con_env[v.name] = randint(0, 50)
            st.sym_env[v.name] = z3.FreshInt(str(v.name).upper())

        ret_dict = kwargs.copy()
        ret_dict["state"] = st
        return [ret_dict]


    def visit_StmtList(self, node, *args, **kwargs):
        temp_kwargs = kwargs.copy()
        sts_dict = [temp_kwargs]

        if node.stmts is None:
            return
        
        for stmt in node.stmts:
            sts_dict_new = []

            for i in range(len(sts_dict)):
                if not sts_dict[i]["state"].is_error():
                    sts_dict_new.extend(self.visit(stmt, *args, **sts_dict[i]))

                    # print("-------------------------")
                    # print(stmt)
                    # print("-------------------------")
                    # print(temp_kwargs["state"])
                    
            sts_dict = sts_dict_new
        
        return [elem for elem in sts_dict if not elem["state"].is_error()]