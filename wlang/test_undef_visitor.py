import unittest

from . import ast, undef_visitor


class TestUndefVisitor(unittest.TestCase):
    def test1(self):
        prg1 = "x := 10; y := x + z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())


    def test2(self):
        prg1 = "havoc x; if x > 10 then y := x + 1 else z := 10; x := z + 1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())

    def test3(self):
        prg1 = "havoc x; if x > 10 then y := z + 1 else z := 10; y := x + 1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())

    def test4(self):
        prg1 = "x := 1; while x > 10 do y := x + 1; z := y + 1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('y')]), uv.get_undefs ())


    def test5(self):
        prg1 = "x := 1; assert x = 1; assume y > 2"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('y')]), uv.get_undefs ())

        prg1 = "x := 1; assert z > y"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('z'), ast.IntVar('y')]), uv.get_undefs ())


    def test6(self):
        prg1 = "x := 1; while not x > 10 do y := x + 1; z := y + 1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('y')]), uv.get_undefs ())


    def test7(self):
        prg1 = "x := 1"
        ast1 = ast.parse_string(prg1)

        ast1.stmts = None

        uv = undef_visitor.UndefVisitor()
        self.assertEquals(uv.visit_StmtList(ast1), None)
        self.assertEquals(uv.visit_Stmt(None), None)

    def test_multiple_functionalities(self):
        prg1 = "x := 10; y := 12"
        prg1 += "; z := x + b + y + 10; if true then x := 11"
        prg1 += "; if (not x < z) or b < c then {d := 20; e := var1} else f := 1"
        prg1 += "; if g > 1 then {if true then h := d else i := f + b} else {j := k + l}"
        prg1 += "; while x < i or l < m do n := ran"
        prg1 += "; can := o; r := o + p; while x < 20 or o < p or n < can do {while true do p := 22}"
        prg1 += "; assume (q > 20 and r < p) or (x = y)"
        prg1 += "; assert (u > t or can < 10) and (v = s)"
        prg1 += "; havoc wa"
        prg1 += "; havoc xa, ya, za"
        
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('b'),
                                ast.IntVar('c'),
                                ast.IntVar('var1'),
                                ast.IntVar('g'),
                                ast.IntVar('d'),
                                ast.IntVar('f'),
                                ast.IntVar('k'),
                                ast.IntVar('l'),
                                ast.IntVar('i'),
                                ast.IntVar('m'),
                                ast.IntVar('ran'),
                                ast.IntVar('o'),
                                ast.IntVar('p'),
                                ast.IntVar('n'),
                                ast.IntVar('q'),
                                ast.IntVar('s'),
                                ast.IntVar('t'),
                                ast.IntVar('u'),
                                ast.IntVar('v'),
                            ]), uv.get_undefs ())


    def test_nested_loops(self):
        prg1 = "z := t + b + y + 10; if true then x := 11 ; q := x ; z := p"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('t'),
                                ast.IntVar('b'),
                                ast.IntVar('y'),
                                ast.IntVar('p'),
                                ast.IntVar('x')
                            ]), uv.get_undefs ())


        prg1 = "z := t + b + y + 10; if true then {x := 11 ; q := x ; z := p}"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('t'),
                                ast.IntVar('b'),
                                ast.IntVar('y'),
                                ast.IntVar('p')
                            ]), uv.get_undefs ())

        prg1 = "if (not x < z) or b < 2 then {d := 20; e := d ; while e < 2 do {s := 0 ; t := s + a} } else {f := 1 ; if f > g then j := 1}"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('x'),
                                ast.IntVar('z'),
                                ast.IntVar('b'),
                                ast.IntVar('a'),
                                ast.IntVar('g')
                            ]), uv.get_undefs ())

        prg1 = "if (not x < z) or b < 2 then {d := 20; e := d ; while e < 2 do {s := 0 ; t := s + a} } else {f := s ; if f > g then j := 1}"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('x'),
                                ast.IntVar('z'),
                                ast.IntVar('b'),
                                ast.IntVar('a'),
                                ast.IntVar('g'),
                                ast.IntVar('s')
                            ]), uv.get_undefs ())


        prg1 = "if (not x < z) or b < 2 then {d := 20; e := d ; while e < 2 do {s := 0 ; t := s + a} } else {f := s ; if f > g then j := 1}; k := t"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('x'),
                                ast.IntVar('z'),
                                ast.IntVar('b'),
                                ast.IntVar('a'),
                                ast.IntVar('g'),
                                ast.IntVar('s'),
                                ast.IntVar('t')
                            ]), uv.get_undefs ())


        prg1 = "while x < 1 or l < m do {n := 1 ; r := n ; r := y ; while r = 1 do {s := 2; havoc a ; t := a; y := q}; if (1 > 2) then {f := 2 ; g := 1}}"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('x'),
                                ast.IntVar('l'),
                                ast.IntVar('m'),
                                ast.IntVar('y'),
                                ast.IntVar('q')
                            ]), uv.get_undefs ())


        prg1 = "k := 0 ; while x < 1 or l < m do {n := 1 ; r := n ; r := y ; while r = 1 do {s := 2; havoc a ; t := a; y := q}; if (1 > 2) then {f := a ; g := 1}}; w := s ; u := k"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('x'),
                                ast.IntVar('l'),
                                ast.IntVar('m'),
                                ast.IntVar('y'),
                                ast.IntVar('q'),
                                ast.IntVar('a'),
                                ast.IntVar('s')
                            ]), uv.get_undefs ())


