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

import unittest

import json
import os

from tatsu.util import asjson
from numpy import atleast_1d

from . import ast, int, parser

class TestInt(unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; print_state"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 10
        self.assertEquals(st.env["x"], 10)
        # no other variables in the state
        self.assertEquals(len(st.env), 1)

    # ------------------------------------------------------------------
    #                       Test Interpreter
    # ------------------------------------------------------------------
    def test_State (self):
        prg1 = "a := 1 ; print_state"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # __repr__
        outRepr = repr(st)

        # a is defined
        self.assertIn("a", st.env)

        # a
        self.assertEquals(st.env["a"], 1)

        # number of variables in the state
        self.assertEquals(len(st.env), 1)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

    
    def test_visit_IntVar (self):
        prg1 = "a := 1 ; b := a"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # a
        self.assertEquals(st.env["a"], 1)

        # b
        self.assertEquals(st.env["b"], 1)

        # number of variables in the state
        self.assertEquals(len(st.env), 2)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

    def test_visit_RelExp (self):
        # Success
        prg1 = "a := 1 ; if a > 0 or a < 1 then b := 0 else b := 1 ; if a >= 2 and a <= 5 then c := 1; if a = 1 then c := 0"
        # test parser
        ast1 = ast.parse_string(prg1)

        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # c is defined
        self.assertIn("c", st.env)

        # a
        self.assertEquals(st.env["a"], 1)

        # b
        self.assertEquals(st.env["b"], 0)

        # c
        self.assertEquals(st.env["c"], 0)

        # number of variables in the state
        self.assertEquals(len(st.env), 3)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))


        # Failure
        prg1 = "if 2 > 0 then b := 0 else b := 1"
        ast1 = ast.parse_string(prg1)

        ast1.cond.op = "=="
        cond = ast1.cond

        interp = int.Interpreter()

        with self.assertRaises(Exception) as context:
            interp.visit_RelExp(cond)



    def test_visit_BExp (self):
        prg1 = "a := 1 ; if a > 0 or a < 1 then b := 0 else b := 1 ; if a >= 2 and a <= 5 then c := 1; if not a = 0 then c := 0"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # c is defined
        self.assertIn("c", st.env)

        # a
        self.assertEquals(st.env["a"], 1)

        # b
        self.assertEquals(st.env["b"], 0)

        # c
        self.assertEquals(st.env["c"], 0)

        # number of variables in the state
        self.assertEquals(len(st.env), 3)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))


        # Failure
        prg1 = "if 2 > 0 and 1 < 2 then b := 0 else b := 1"
        ast1 = ast.parse_string(prg1)

        ast1.cond.op = "one"
        cond = ast1.cond

        with self.assertRaises(Exception) as context:
            interp.visit_BExp(cond)


    def test_visit_AExp (self):
        prg1 = "a := 2 ; b := 1 ; c := a + b ; d := a - b ; e := a * b ; f := a / b "
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # c is defined
        self.assertIn("c", st.env)

        # d is defined
        self.assertIn("d", st.env)

        # e is defined
        self.assertIn("e", st.env)

        # f is defined
        self.assertIn("f", st.env)

        # a
        self.assertEquals(st.env["a"], 2)

        # b
        self.assertEquals(st.env["b"], 1)

        # c
        self.assertEquals(st.env["c"], 3)

        # d
        self.assertEquals(st.env["d"], 1)

        # e
        self.assertEquals(st.env["e"], 2)

        # f
        self.assertEquals(st.env["f"], 2)

        # number of variables in the state
        self.assertEquals(len(st.env), 6)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))


        # Failure
        prg1 = "x := 2 * 4"
        ast1 = ast.parse_string(prg1)

        ast1.rhs.op = "$"
        rhs = ast1.rhs

        with self.assertRaises(Exception) as context:
            interp.visit_AExp(rhs)


    def test_IfStmt (self):
        prg1 = "a := 1 ; if a = 1 then b := 0; if false then c := 0 else c:= 1 ; if c = 10 then b := 1"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # c is defined
        self.assertIn("c", st.env)

        # a
        self.assertEquals(st.env["a"], 1)

        # b
        self.assertEquals(st.env["b"], 0)

        # c
        self.assertEquals(st.env["c"], 1)

        # number of variables in the state
        self.assertEquals(len(st.env), 3)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

    def test_WhileStmt (self):
        prg1 = "a := 4 ; b := 0; while (a > 0) inv a > 0 do { b := 1 ; a := a - 1 }"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # a
        self.assertEquals(st.env["a"], 0)

        # b
        self.assertEquals(st.env["b"], 1)

        # number of variables in the state
        self.assertEquals(len(st.env), 2)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

    def test_AssertStmt (self):
        prg1 = "a := 0 ; b := 0 ; assert a = b ; assert a = b"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # a
        self.assertEquals(st.env["a"], 0)

        # b
        self.assertEquals(st.env["b"], 0)

        # number of variables in the state
        self.assertEquals(len(st.env), 2)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

        # Exception
        prg1 = "a := 0 ; b := 0 ; assert a < b"
        # test parser
        ast1 = ast.parse_string(prg1)

        interp = int.Interpreter()
        st = int.State()

        with self.assertRaises(Exception) as context:
            st = interp.run(ast1, st)

    def test_AssumeStmt (self):
        prg1 = "a := -1 ; b := -1; assume a = b"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # a
        self.assertEquals(st.env["a"], -1)

        # b
        self.assertEquals(st.env["b"], -1)

        # number of variables in the state
        self.assertEquals(len(st.env), 2)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

    def test_StmtList (self):
        prg1 = "a := 0 ; b := 0"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # a
        self.assertEquals(st.env["a"], 0)

        # b
        self.assertEquals(st.env["b"], 0)

        # number of variables in the state
        self.assertEquals(len(st.env), 2)


    def test_HavocStmt (self):
        prg1 = "havoc a , b , c"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # b is defined
        self.assertIn("b", st.env)

        # c is defined
        self.assertIn("c", st.env)

        # a
        self.assertEquals(st.env["a"], 0)

        # b
        self.assertEquals(st.env["b"], 0)

        # c
        self.assertEquals(st.env["c"], 0)

        # number of variables in the state
        self.assertEquals(len(st.env), 3)

        ast2 = ast.parse_string(prg1)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))


    def test_SkipStmt_and_PrintStateStmt_and_AsgnStmt (self):
        prg1 = "a := 2 ; print_state ; skip "
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # a is defined
        self.assertIn("a", st.env)

        # a
        self.assertEquals(st.env["a"], 2)

        # number of variables in the state
        self.assertEquals(len(st.env), 1)


    def test_int_main_fun_1 (self):
        with self.assertRaises(SystemExit) as context:
            int.main()







    # ------------------------------------------------------------------
    #                       Test AST
    # ------------------------------------------------------------------
    def test_ast_class_Ast (self):
        program = "skip"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        # __str__
        self.assertEquals(str(ast1), str(ast1))

        # __repr__
        self.assertEquals(repr(ast1), repr(ast1))


    def test_ast_class_StmtList (self):
        program1 = "x := 201; print_state"
        
        # test parser
        ast1 = ast.parse_string(program1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

        program2 = "x := 201; print_state"
        # test parser
        ast2 = ast.parse_string(program2)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast2, st)
        self.assertIsNotNone(st)

        # __eq__
        self.assertTrue(ast.StmtList (ast1.stmts) == ast.StmtList (ast2.stmts))


    def test_ast_class_SkipStmt (self):
        program = "skip; skip"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[0] == list_stmts[1])


    def test_ast_class_PrintStateStmt (self):
        program = "print_state; print_state"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[0] == list_stmts[1])


    # def test_ast_class_AsgnStmt (self):
    #     program = "a := 26; a := 26"
        
    #     # test parser
    #     ast1 = ast.parse_string(program)
    #     interp = int.Interpreter()
    #     st = int.State()
    #     st = interp.run(ast1, st)
    #     self.assertIsNotNone(st)
        
    #     list_stmts = list(ast1.stmts)

    #     # __eq__
    #     self.assertTrue(list_stmts[0] == list_stmts[1])


    def test_ast_class_IfStmt (self):
        program = "a := 1 ; if true then b := 1 else b := 0"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # # has_else
        # self.assertTrue(list_stmts[1].has_else())

        # __eq__
        self.assertTrue(list_stmts[1] == list_stmts[1])

        ast2 = ast.parse_string(program)
        # PrintVisitor (in AST)
        self.assertTrue(str(ast1) == str(ast2))

    def test_ast_class__WhileStmt (self):
        program = "a := 1 ; while a = 1 do { b := 1 ; a := 0 }"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[1] == list_stmts[1])

    def test_ast_class__AssertStmt (self):
        program = "a := 1 ; assert a = 1"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[1] == list_stmts[1])


    def test_ast_class__AssumeStmt (self):
        program = "a := 1 ; assume a = 1"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[1] == list_stmts[1])

    
    def test_ast_class__HavocStmt (self):
        program = "a := 1 ; havoc a"
        
        # test parser
        ast1 = ast.parse_string(program)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[1] == list_stmts[1])


    def test_parse_file (self):
        filename = "wlang/test1.prg"
        
        # test parser
        ast1 = ast.parse_file(filename)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        list_stmts = list(ast1.stmts)

        # __eq__
        self.assertTrue(list_stmts[1] == list_stmts[1])

    
    def test_ast_class_Const (self):
        program = "1"

        # __str__
        self.assertEquals(str(ast.Const(program)), "1")

        # __repr__
        self.assertEquals(repr(ast.Const(program)), "'1'")

        # __hash__
        self.assertEquals(hash(ast.Const(program)), hash(ast.Const(program)))


    def test_ast_class_IntVar (self):
        program = "a"

        # __str__
        self.assertEquals(str(ast.IntVar(program)), "a")

        # __repr__
        self.assertEquals(repr(ast.IntVar(program)), "'a'")


    def test_ast_class_Exp (self):
        program = "a  b + c"
        exp = ast.Exp(["+", "+"], [ast.IntVar('a'), ast.IntVar('b'), ast.IntVar('c')])

        # __str__
        self.assertFalse(exp.is_binary())


    def test_ast_class_AstVisitor (self):
        program = "a  b + c"
        astVisitor = ast.AstVisitor()

        with self.assertRaises(Exception) as context:
            astVisitor.visit_IntVar(ast.IntVar('a'))

        with self.assertRaises(Exception) as context:
            astVisitor.visit_AsgnStmt(ast.AsgnStmt(ast.IntVar('a'), ast.Exp(["+", "+"], [ast.IntVar('a'), ast.IntVar('b'), ast.IntVar('c')])))

        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string("if x < 2 then y := 2")
            astVisitor.visit_IfStmt(ast1)

        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string("while x < 2 do y := 2")
            astVisitor.visit_WhileStmt(ast1)

        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string("assert x < 2")
            astVisitor.visit_AssertStmt(ast1)

        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string("assume x < 2")
            astVisitor.visit_AssumeStmt(ast1)

        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string("havoc a, b")
            astVisitor.visit_HavocStmt(ast1)
        

    def test_ast_class_PrintVisitor_None_Stmts(self):
        prg1 = "x := 1"
        ast1 = ast.parse_string(prg1)

        ast1.stmts = None

        printVisitor = ast.PrintVisitor()

        self.assertEquals(printVisitor.visit_StmtList(ast1), None)
        
        
    def test_visit_PrintVisitor (self):
        prg1 = "skip"
        # test parser
        ast1 = ast.parse_string(prg1)

        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        pv = ast.PrintVisitor()
        pv.visit(ast1)

    def test_visit_PrintVisitor_visit_Stmts (self):
        prg1 = "skip; skip"
        # test parser
        ast1 = ast.parse_string(prg1)

        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        
        pv = ast.PrintVisitor()
        pv.visit(ast1)

        ast1.stmts = [ast1.stmts[0]]

        pv = ast.PrintVisitor()
        # Returns to standard ouput 
        self.assertEquals(pv.visit_StmtList(ast1, indent=0, no_brkt=False), None)

    def test_ast_class_AstVisitor_SomeVisitor_child (self):
        astVisitor = SomeVisitor()
        
        astVisitor.visit_IntVar(ast.IntVar('a'))
        astVisitor.visit_AsgnStmt(ast.AsgnStmt(ast.IntVar('a'), ast.Exp(["+", "+"], [ast.IntVar('a'), ast.IntVar('b'), ast.IntVar('c')])))
        
        ast1 = ast.parse_string("if x < 2 then y := 2")
        self.assertTrue(astVisitor.visit_IfStmt(ast1) == None)
        
        ast1 = ast.parse_string("while x < 2 do y := 2")
        self.assertTrue(astVisitor.visit_WhileStmt(ast1) == None)
        
        ast1 = ast.parse_string("assert x < 2; skip")
        self.assertTrue(astVisitor.visit_AssertStmt(ast1) == None)
        
        ast1 = ast.parse_string("assume x < 2")
        self.assertTrue(astVisitor.visit_AssumeStmt(ast1) == None)
        
        ast1 = ast.parse_string("havoc a, b")
        self.assertTrue(astVisitor.visit_HavocStmt(ast1) == None)
    # ------------------------------------------------------------------
    # ------------------------------------------------------------------









    # ------------------------------------------------------------------
    #                       Test Parser
    # ------------------------------------------------------------------
    def test_parser_WhileLangSemantics (self):
        p = parser.WhileLangParser(parseinfo=False, keywords = {}) 

        prg1 = "a := 1 ; x := true; if true or a < 1 then b := 0 else b := 1 ; if a >= 2 and a <= 5 then c := 1; if a = 1 then c := 0"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        prg1 = "a := 4 ; b := 0; while (a > 0) inv a > 0 do { b := 1 ; a := a - 1 }"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        prg1 = "a := 2 ; b := -1 ; c := a + b ; d := a - b ; e := a * b ; f := a / b"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        prg1 = "skip ; print_state"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        prg1 = "a := -1 ; b := -1; assume a = b"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        prg1 = "a := 0 ; b := 0 ; assert a = b ; assert a = b"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        prg1 = "havoc a , b , c"
        ast1 = p.parse(prg1, "start", filename="<built-in>", semantics=parser.WhileLangSemantics())
        self.assertTrue(str(ast1) != None)

        
    def test_WhileLangBuffer (self):
        prg1 = "a ade "
        # test parser
        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string(prg1)

        prg1 = "if (a < q) or (b) or (c) and f then skip"
        # test parser
        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string(prg1)


    def test_parser_main_fun (self):
        ast1 = parser.main(filename = "wlang/test1.prg")
        ast2 = parser.main(filename = "wlang/test1.prg", start='start')
        self.assertTrue(str(ast1) == str(ast2))




class SomeVisitor(ast.AstVisitor):
    def __init__(self):
        pass
    
    # def visit_StmtList(self, node, *args, **kwargs):
    #     if node.stmts is None:
    #         return

    #     for s in node.stmts:
    #         self.visit(s, *args)

    #     return None

    def visit_IntVar(self, node, *args, **kwargs):
        pass

    # def visit_Const(self, node, *args, **kwargs):
    #     pass

    def visit_Stmt(self, node, *args, **kwargs):
        pass

    # def visit_Exp(self, node, *args, **kwargs):
    #     pass