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

from . import DSE, SSE, SeSE_v1, SeSE_v2, ast
import z3


class TestSym (unittest.TestCase):
    def test_compare_1(self):
        prg1 = '''  havoc x, y;
                    z := x + 1;

                    if (z*z >= y) then
                        {
                         if 14 > z then
                            skip
                        }
                    else
                        if (y < 100) then
                            skip
                '''
        
        # Static Symbolic Execution
        SSE_ast = ast.parse_string(prg1)
        SSE_engine = SSE.SymExec()
        SSE_st = SSE.SymState()
        SSE_out = [s for s in SSE_engine.run(SSE_ast, SSE_st)]
        self.assertEquals(len(SSE_out), 4)
        # print("--------\nSSE\n--------")
        # print(SSE_out)

        # Dynamic Symbolic Execution
        DSE_ast = ast.parse_string(prg1)
        DSE_engine = DSE.DynamicSymExec()
        DSE_st = DSE.Dynamic_State()
        DSE_out = [s for s in DSE_engine.run(DSE_ast, DSE_st)]
        self.assertTrue(len(DSE_out) == 2  or  len(DSE_out) == 3)

        # Selective Symbolic Execution - Version 1
        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast)]
        self.assertEquals(len(SeSE_out), 4)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[2].then_stmt)]
        self.assertTrue(len(SeSE_out) == 1  or  len(SeSE_out) == 2)

        # Selective Symbolic Execution - Version 2
        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v2.SelectiveSymExec()
        SeSE_st = SeSE_v2.SeSE_V2_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast)]
        self.assertEquals(len(SeSE_out), 4)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v2.SelectiveSymExec()
        SeSE_st = SeSE_v2.SeSE_V2_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[2].then_stmt)]
        self.assertTrue(len(SeSE_out) == 1  or  len(SeSE_out) == 2)

    
    def test_compare_2 (self):
        prg1 = '''  havoc x, y;
                    if x + y > 15 then
                        { x := x + 7; y := y - 12}
                    else
                        { y := y + 10; x := x - 2 };
                    
                    x := x + 2;
                    if 2 * (x + y) > 21 then
                        {
                            x := x * 3;
                            y := y * 2
                        }
                    else
                        {
                            x := x * 4;
                            y := y * 3 + x
                        };
                    skip
                '''

        # Static Symbolic Execution
        SSE_ast = ast.parse_string(prg1)
        SSE_engine = SSE.SymExec()
        SSE_st = SSE.SymState()
        SSE_out = [s for s in SSE_engine.run(SSE_ast, SSE_st)]
        self.assertEquals(len(SSE_out), 3)

        # Dynamic Symbolic Execution
        DSE_ast = ast.parse_string(prg1)
        DSE_engine = DSE.DynamicSymExec()
        DSE_st = DSE.Dynamic_State()
        DSE_out = [s for s in DSE_engine.run(DSE_ast, DSE_st)]
        self.assertTrue(len(DSE_out) == 2)

        # Selective Symbolic Execution - Version 1
        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast)]
        self.assertEquals(len(SeSE_out), 3)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[1])]
        self.assertEquals(len(SeSE_out), 3)


        # Selective Symbolic Execution - Version 2
        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v2.SelectiveSymExec()
        SeSE_st = SeSE_v2.SeSE_V2_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast)]
        self.assertEquals(len(SeSE_out), 3)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v2.SelectiveSymExec()
        SeSE_st = SeSE_v2.SeSE_V2_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[1])]
        self.assertEquals(len(SeSE_out), 2)


    def test_compare_3 (self):
        prg1 =  ''' r := 0;
                    havoc x;

                    if x > 8 then {
                        havoc x;
                        r := x - 7
                    };
                    
                    if x / 1 < 5 then
                        r := x - 2
                '''

        # Static Symbolic Execution
        SSE_ast = ast.parse_string(prg1)
        SSE_engine = SSE.SymExec()
        SSE_st = SSE.SymState()
        SSE_out = [s for s in SSE_engine.run(SSE_ast, SSE_st)]
        self.assertEquals(len(SSE_out), 4)

        # Dynamic Symbolic Execution
        DSE_ast = ast.parse_string(prg1)
        DSE_engine = DSE.DynamicSymExec()
        DSE_st = DSE.Dynamic_State()
        DSE_out = [s for s in DSE_engine.run(DSE_ast, DSE_st)]
        self.assertTrue(len(DSE_out) == 2)

        # Selective Symbolic Execution - Version 1
        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast)]
        self.assertEquals(len(SeSE_out), 4)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[3])]
        self.assertEquals(len(SeSE_out), 2)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v1.SelectiveSymExec()
        SeSE_st = SeSE_v1.SeSE_V1_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[2])]
        self.assertTrue(len(SeSE_out) == 4)

        # Selective Symbolic Execution - Version 2
        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v2.SelectiveSymExec()
        SeSE_st = SeSE_v2.SeSE_V2_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast)]
        self.assertEquals(len(SeSE_out), 4)

        SeSE_ast = ast.parse_string(prg1)
        SeSE_engine = SeSE_v2.SelectiveSymExec()
        SeSE_st = SeSE_v2.SeSE_V2_State()
        SeSE_out = [s for s in SeSE_engine.run(SeSE_ast, SeSE_st, SeSE_ast.stmts[2])]
        self.assertEquals(len(SeSE_out), 2)

        

