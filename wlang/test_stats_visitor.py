import unittest

from . import ast, stats_visitor


class TestStatsVisitor(unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 2)
        self.assertEquals(sv.get_num_vars(), 1)


    def test_assignment_and_havoc(self):
        prg1 = "a := 10; havoc c , b; d := a ; havoc x ; x := 1"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 5)
        self.assertEquals(sv.get_num_vars(), 5)


    def test_IfStmt (self):
        prg1 = "skip ; a := 10; a := 11 ; b := 5 ; if (not b < 5) or true then c := 0 else c := 1"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 7)
        self.assertEquals(sv.get_num_vars(), 3)

    def test_WhileStmt(self):
        prg1 = "a := 10 ; print_state ; b := 5 ; while b < 5 do {c := 0 ; b := b - 1} ; b := 5"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 7)
        self.assertEquals(sv.get_num_vars(), 3)

    def test_assert_and_assume(self):
        prg1 = "a := 10 ; b := 5 ; assume b < 5; assert (b = 5); a := 11 ; b := 1"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 6)
        self.assertEquals(sv.get_num_vars(), 2)

    def test_visit_StmtList(self):
        prg1 = "x := 1"
        ast1 = ast.parse_string(prg1)
        
        ast1.stmts = None
        
        sv = stats_visitor.StatsVisitor()
        self.assertEquals(sv.visit_StmtList(ast1), None)

    def test_multiple_functionalities(self):
        prg1 = "x := 10; y := 12"
        prg1 += "; z := x + b; if true then x := 11"
        prg1 += "; if x < 20 or b < c then {d := 20; e := 10} else f := 1"
        prg1 += "; if g > 1 then {if true then h := 2 else i := a + b} else {j := k + l}"
        prg1 += "; while x < 20 or l < m do n := 20"
        prg1 += "; while x < 20 or o < p do {while true do p := 22}"
        prg1 += "; assume (q > 20 and r < 10) or (s = t)"
        prg1 += "; assert (u > 20 or x < 10) and (v = s)"
        prg1 += "; havoc w"
        prg1 += "; havoc x, y, z"

        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 23)
        self.assertEquals(sv.get_num_vars(), 26)


    def test_int_main_fun_stats_visitor_1 (self):
        with self.assertRaises(Exception) as context:
            stats_visitor.main()
