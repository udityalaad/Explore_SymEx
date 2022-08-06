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


# def hash_cons(exp):
#     table = dict()
#     return _hash_cons_rec(exp, table)


# def hash_cons_list(exp_list):
#     table = dict()
#     return [_hash_cons_rec(a, table) for a in exp_list]


# def _hash_cons_rec(exp, table):
#     if isinstance(exp, ast.Const):
#         key = exp.val
#     elif isinstance(exp, ast.IntVar):
#         key = exp.name
#     elif isinstance(exp, ast.Exp):
#         # process all the children recursively
#         exp.args = [_hash_cons_rec(a, table) for a in exp.args]
#         key = [exp.op]
#         key.extend(map(id, exp.args))
#         # list is not hashable
#         key = tuple(key)
#     else:
#         return exp

#     if key not in table:
#         table[key] = exp

#     return table[key]


# def test():
#     x1 = ast.IntVar("x")
#     n1 = ast.IntConst(5)
#     e1 = ast.AExp("+", [x1, n1])

#     x2 = ast.IntVar("x")
#     n2 = ast.IntConst(5)
#     e2 = ast.AExp("+", [x2, n2])

#     print("e1 is e2:", e1 is e2, "e1 == e2", e1 == e2)

#     el = hash_cons_list([e1, e2])

#     print("e1 is e2:", el[0] is el[1], "e1 == e2", el[0] == el[1])

#     print(hash_cons(e1) is e1)
#     print(hash_cons(5) == 5)


# if __name__ == "__main__":
#     test()
