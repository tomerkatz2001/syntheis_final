import unittest

from z3 import And, simplify, Implies, Or

from wp import synthesize, synthesizeAndVerify


class Feature1NoVer(unittest.TestCase):

    def test_simpleConstHole(self):
        program = '''a := ?? '''
        res = synthesize(program, {}, {"a":6}, False).strip()
        self.assertEqual("a := 6", res)

    def test_doubleConstHole(self):
        program = '''a := ??;b := ??'''
        res = synthesize(program, {}, {"a":6, "b":123}, False).strip()
        self.assertEqual("a := 6;b := 123",res)

    def test_doubleConstHoleSameVar(self):
        program = '''a := ??;a := ??'''
        res = synthesize(program, {}, {"a":6}, False).strip()
        self.assertEqual("a := 0;a := 6",res) # 0 is default value for every variable can be assigned with any value

    def test_doubleConstHoleSameVar2(self):
        program = '''a := ??;b := a + a;a := ??'''
        res = synthesize(program, {}, {"a":6, "b":6}, False).strip()
        self.assertEqual("a := 3;b := a + a;a := 6",res)

    def test_noSol(self):
        program = '''a := ??;b := a + a'''
        res = synthesize(program, {}, {"a":6, "b":6}, False).strip()
        self.assertEqual("solution can't be found",res)

    def test_beforeWhile(self):
        program = '''a := ??;b:=2;while b >0 do (n:=b; b:= b - 1)'''
        res = synthesize(program, {}, {"a":6}, False).strip()
        self.assertEqual('''a := 6;b:=2;while b >0 do (n:=b; b:= b - 1)''',res)

    def test_insideWhile(self):
        program = '''b:=2;while b >0 do (a:=??; b:= b - 1)'''
        res = synthesize(program, {}, {"a":6}, False).strip()
        self.assertEqual('''b:=2;while b >0 do (a:=6; b:= b - 1)''',res)

    def test_afterWhile(self):
        program = '''b:=2;while b >0 do (b:= b - 1);a:=??'''
        res = synthesize(program, {}, {"a": 12}, False).strip()
        self.assertEqual('''b:=2;while b >0 do (b:= b - 1);a:=12''', res)

    def test_numOfIterationsWhile(self):
        program = '''a := ??;n:=2;while a >0 do (n:= n + 1; a:= a - 1)'''
        res = synthesize(program, {}, {"n": 9, "a":0}, False).strip()
        self.assertEqual('''a := 7;n:=2;while a >0 do (n:= n + 1; a:= a - 1)''', res)



class Feature1WithVer(unittest.TestCase):

    def test1(self):
        '''
        synth somthing that will be verified
        '''
        program = "b:=??;while a > 0 do a := a - 1 "
        P = lambda d: d['a'] >= 0
        Q = lambda d: d['a'] == 0 and d['b'] == 0
        linv = lambda d: d['a'] >= 0
        (new_prog, res) = synthesizeAndVerify(program, {}, {"b":0},P, Q, linv, False)
        self.assertEqual(True, res)

    def test2(self):
        '''
        synth somthing that will not be verified
        '''
        program = "b:=??;while a > 0 do a := a - 1 "
        P = lambda d: d['a'] >= 0
        Q = lambda d:  And(d['a'] == 0 , d['b'] != 0)
        linv = lambda d: d['a'] >= 0
        (new_prog, res) = synthesizeAndVerify(program, {}, {"b":0},P, Q, linv, False)
        self.assertEqual(False, res)

    def test3(self):
        '''
        synthesize the number of iterations for the loop
        '''
        program = "i:=0; n:= ??; a := b - 1 ; while i < n do ( a := a + 1 ; i := i + 1 )"
        P = lambda _: True
        Q = lambda d: d['a'] == d['b']
        linv = lambda d: And(d['a'] + d['n'] == d['b'] + d['i'], d['i'] <= d['n'])
        (new_prog, res) = synthesizeAndVerify(program, {}, {"n": 1}, P, Q, linv, False)
        self.assertEqual("i:=0; n:= 1; a := b - 1 ; while i < n do ( a := a + 1 ; i := i + 1 )", new_prog)
        self.assertEqual(True, res)

    def test4(self):
        '''
        infinite loop
        '''
        program = "y := ?? ; while y > 0 do  y := y + 1"  # classic infinite loop
        P = lambda d: d['y'] > 0
        Q = lambda d: False
        linv = lambda d: d['y'] > 0
        (new_prog, res) = synthesizeAndVerify(program, {}, {"y": 1}, P, Q, linv, False)
        self.assertEqual("y := 1 ; while y > 0 do  y := y + 1", new_prog)
        self.assertEqual(True, res)

    def test5(self):
        '''
        infinite loop that after synth is not taken
        '''
        program = "y := ?? ; while y > 0 do  y := y + 1"  # classic infinite loop
        P = lambda d: d['y'] > 0
        Q = lambda d: True
        linv = lambda d: d['y'] > 0
        (new_prog, res) = synthesizeAndVerify(program, {}, {"y": -5}, P, Q, linv, False)
        self.assertEqual("y := -5 ; while y > 0 do  y := y + 1", new_prog)
        self.assertEqual(True, res)

class Feature2NoVer(unittest.TestCase):

    def test_simpleProgram(self):
        program = '''a := ?? ;assert a = 2'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''a := 2 ;assert a = 2''', res)

    def test_variableUsed(self):
        program = '''a := ??; b:= a + 2;assert b = 10'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''a := 8; b:= a + 2;assert b = 10''', res)

    def test_aBitMoreComplexProgram(self):
        program = '''b:=1; a := b + ?? ;assert a = 2'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''b:=1; a := b + 1 ;assert a = 2''', res)

    def test_aaBitMoreComplexProgram2(self):
        program = '''b := 2 ; c := 3 ; a := (b + c) + ?? ; assert a = 2'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''b := 2 ; c := 3 ; a := (b + c) + -3 ; assert a = 2''', res)

    def test_doubleConstHoleSameVar(self):
        program = '''a := ??;a := ??; assert a = 6'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''a := 0;a := 6; assert a = 6''',res) # 0 is default value for every variable can be assigned with any value

    def test_doubleConstHoleSameVar2(self):
        program = '''a := ??;b := a + a;a := ??; assert a = 6; assert b = 6'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''a := 3;b := a + a;a := 6; assert a = 6; assert b = 6''',res)

    def test_noSol(self):
        program = '''a := ??;b := a + a; assert a =6; assert b = 6'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual("solution can't be found",res)

    def test_beforeWhile(self):
        program = '''a := ??;b:=2;while b >0 do (n:=b; b:= b - 1); assert a =6'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''a := 6;b:=2;while b >0 do (n:=b; b:= b - 1); assert a =6''',res)

    def test_insideWhile(self):
        program = '''b:=2;while b >0 do (a:=??; b:= b - 1); assert a = 6'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''b:=2;while b >0 do (a:=6; b:= b - 1); assert a = 6''',res)

    def test_afterWhile(self):
        program = '''b:=2;while b >0 do (b:= b - 1);a:=??;assert a =12'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''b:=2;while b >0 do (b:= b - 1);a:=12;assert a =12''', res)

    def test_numOfIterationsWhile(self):
        program = '''a := ??;n:=2;while a >0 do (n:= n + 1; a:= a - 1);assert n=9;assert a = 0'''
        res = synthesize(program, {}, {}, False).strip()
        self.assertEqual('''a := 7;n:=2;while a >0 do (n:= n + 1; a:= a - 1);assert n=9;assert a = 0''', res)
class AdditionalFeature2And5(unittest.TestCase):
    def test_var(self):
        program = '''a:=1  ; c:= ?? ; assert c=b'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertEqual('a:=1  ; c:= b ; assert c=b', res)

    def test_sum(self):
        program = '''a:=1  ; c:= ?? ; assert c= (b + 1)'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertIn(res, ['a:=1  ; c:= b + a ; assert c= (b + 1)', "a:=1  ; c:= 1 + b ; assert c= (b + 1)"] )

    def test_mul(self):
        program = '''a:=2  ; c:= ?? ; assert c= (b * 2)'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertEqual('a:=2  ; c:= 2*b ; assert c= (b * 2)', res)

    def test_div(self):
        program = '''a:=x  ; c:= ?? ; assert c= (x / 2)'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertIn(res, ['a:=x  ; c:= a/2 ; assert c= (x / 2)', 'a:=x  ; c:= x/2 ; assert c= (x / 2)'])

    def test_if(self):
        program = '''a:=??  ; if (a <1) then (c:=1) else (c:=2) ; assert c = 2'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertEqual('a:=1  ; if (a <1) then (c:=1) else (c:=2) ; assert c = 2', res)

    def test_if2(self):
        program = '''a:=??  ; if (a != c) then (c:=1) else (c:=2) ; assert c = 2'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertEqual('a:=c  ; if (a != c) then (c:=1) else (c:=2) ; assert c = 2', res)

    def test_loop_unroll(self):

        program = '''
        b:=2;
        d:=c;
        while b >0 do (
            d:= d + 1 ;
            b:= b - 1);
        a:= ?? ;
        assert a = (d + 2)'''
        res = synthesize(program, {}, {}, True).strip()

        self.assertIn(''.join(res.split()), ["".join('''b:=2;
        d:=c;
        while b >0 do (
            d:= d + 1 ;
            b:= b - 1);
        a:= 4 + c ;
        assert a = (d + 2)'''.split()),
                        "".join(
                       '''b:=2;
                       d:=c;
                       while b >0 do (
                           d:= d + 1 ;
                           b:= b - 1);
                       a:= 2 + d ;
                       assert a = (d + 2)'''.split())
                       ],)

    def test_loop_unroll_cond(self):
            program = '''
            a:=c;
            b:=??;
            while b >0 do (
                a:= a + 1 ;
                b:= b - 1);
            assert a = (c + 2)'''
            res = synthesize(program, {}, {}, True).strip()
            self.assertEqual('''a:=c;
            b:=2;
            while b >0 do (
                a:= a + 1 ;
                b:= b - 1);
            assert a = (c + 2)''', res)

    def test_loop_unroll_cond2(self):
        program = '''a:=c;
                b:=??;
                while b >0 do (
                    a:= a + 1 ;
                    b:= b+ ??);
                assert a = (c + 2)'''
        res = synthesize(program, {}, {}, True).strip()
        self.assertEqual('''a:=c;
                b:=2;
                while b >0 do (
                    a:= a + 1 ;
                    b:= b+ -1);
                assert a = (c + 2)''', res)

    def test_loop_unroll_cond3(self):
            program = '''a:=c;
                    b:=2;
                    while b >0 do (
                        a:= a + 1 ;
                        b:= ??);
                    assert a = (c + 2)'''
            res = synthesize(program, {}, {}, True).strip()
            self.assertEqual('''a:=c;
                    b:=2;
                    while b >0 do (
                        a:= a + 1 ;
                        b:= -1 + b);
                    assert a = (c + 2)''', res)

    def test_loop_unroll_cond4(self):
            program = '''a:=c;
                    b:=??;
                    while b >0 do (
                        a:= a + 1 ;
                        b:= ??);
                    assert a = (c + 2)'''
            res = synthesize(program, {}, {}, True).strip()
            self.assertEqual('''a:=c;
                    b:=2;
                    while b >0 do (
                        a:= a + 1 ;
                        b:= -1 + b);
                    assert a = (c + 2)''', res)

    def test_fib(self):
        #"a:=1; b:= 1; i := 0 ; n:= 5" \
                  #" while i < n do ( tmp:= a; a := a + b; b:= tmp)"
        program = "a:=1; b:= 1; i := 0 ; n:= 5;" \
                  " while i < n do ( tmp:= ?? ; a := a + b; b:= tmp; i:= i + 1)"
        new_prog = synthesize(program, {}, {"a": 13 }, True)
        print(new_prog)
        self.assertEqual("a:=1; b:= 1; i := 0 ; n:= 5;" \
                  " while i < n do ( tmp:= a ; a := a + b; b:= tmp; i:= i + 1)", new_prog)

    def test_fib_harder(self):
        #"a:=1; b:= 1; i := 0 ; n:= 5" \
                  #" while i < n do ( tmp:= a; a := a + b; b:= tmp)"
        program = "a:=1; b:= 1; i := 0 ; n:= 5;" \
                  " while i < n do ( tmp:= ?? ; a := a + b; b:= ??; i:= i + 1)"
        new_prog = synthesize(program, {}, {"a": 13 }, True)
        print(new_prog)
        self.assertEqual("a:=1; b:= 1; i := 0 ; n:= 5;" \
                  " while i < n do ( tmp:= a ; a := a + b; b:= tmp; i:= i + 1)", new_prog)

class SynthFailed(unittest.TestCase):
    def test_numOfIterationsWhile2(self):
        program = "i:=??; n:= 1; a := b - 1 ;" \
                  " while i < n do ( a := a + 1 ; i := i + 1 )"
        new_prog = synthesize(program, {}, {"n": 0}, False)
        print(new_prog)
        self.assertEqual("solution can't be found", new_prog)




if __name__ == '__main__':
    unittest.main()
