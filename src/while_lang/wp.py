import multiprocessing
from while_lang.syntax import WhileParser
import adt.tree
import operator
from z3 import Int, ForAll, Implies, Not, And, Or, Solver, unsat, sat
from copy import copy, deepcopy
from functools import partial
from itertools import product


def signal_handler(signum, frame):
    raise Exception("Timed out!")

class LazyDict(dict):
    def __init__(self, *args, **kwds) -> None:
        super().__init__(*args, **kwds)

    def __getitem__(self, __key):
        ret = super().__getitem__(__key)

        if callable(ret):
            ret = ret(self)
            self[__key] = ret
            return ret
        return ret


OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.floordiv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}


def mk_env(pvars):
    return LazyDict({v: Int(v) for v in pvars})


def getVars(program: str):
    ast = WhileParser()(program)
    return find_all_vars(ast)


def upd(d, k, v):
    d = copy(d)
    d[k] = v
    return d


def get_assigned_vars(ast):
    assignedVars = []
    if ast.root == ':=':
        return ast.subtrees[0].subtrees[0].root  # varName
    else:
        for sub_ast in ast.subtrees:
            assignedVars += get_assigned_vars(sub_ast)
    return assignedVars


def find_all_vars(ast):
    sons_vars = []
    if ast.root == 'id':
        return [ast.subtrees[0].root]
    for sub_ast in ast.subtrees:
        sons_vars += find_all_vars(sub_ast)
    return list(set(sons_vars))


def solve(formulas):
    s = Solver()
    s.add(formulas)
    if s.check() == sat:
        return s.model()


def encode_expr(ast, env):
    if ast.root == 'id':
        return env[ast.subtrees[0].root]
    elif ast.root == 'num':
        return ast.subtrees[0].root
    elif ast.root in OP:
        return OP[ast.root](encode_expr(ast.subtrees[0], env), encode_expr(ast.subtrees[1], env))
    else:
        raise SyntaxError


def get_wp(ast, Q, linv):
    if ast.root == ';':
        def concat_lambda(e):
            wp_second = get_wp(ast.subtrees[1], Q, linv)  # assert a==2
            wp_first = get_wp(ast.subtrees[0], wp_second, linv)  # a := 1
            return wp_first(e)

        return concat_lambda

    elif ast.root == 'skip':
        return Q

    elif ast.root == ":=":
        def assignment_lambda(e):
            var_name = ast.subtrees[0].subtrees[0].root
            right = ast.subtrees[1]
            expr = encode_expr(right, e)
            return Q(upd(e, var_name, expr))

        return assignment_lambda

    elif ast.root == 'if':
        def if_lambda(e):
            wp_then = get_wp(ast.subtrees[1], Q, linv)
            wp_else = get_wp(ast.subtrees[2], Q, linv)
            cond = encode_expr(ast.subtrees[0], e)
            return Or(And(cond, wp_then(e)), And(Not(cond), wp_else(e)))

        return if_lambda

    elif ast.root == 'while':
        def lambda_while(e):

            new_env = mk_env(list(e.keys()))
            unassigned_vars = [v for v in e.keys() if v not in get_assigned_vars(ast)]
            for var in unassigned_vars:
                new_env = upd(new_env, var, e[var])
            wp = get_wp(ast.subtrees[1], linv, linv)
            cond = encode_expr(ast.subtrees[0], new_env)
            first_cond = encode_expr(ast.subtrees[0], e)
            return And(Implies(first_cond, And(linv(e), ForAll([new_env[v] for v in get_assigned_vars(ast)],
                                                               And(Implies(And(linv(new_env), cond), wp(new_env)),
                                                                   Implies(And(linv(new_env), Not(cond)), Q(new_env)))
                                                               ))),
                       Implies(Not(first_cond), Q(e)))

        return lambda_while

    elif ast.root == 'assert':
        def lambda_assert(e):
            return And(encode_expr(ast.subtrees[0], e), Q(e))

        return lambda_assert


def verify(P, ast, Q, linv=None):
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """
    env = mk_env(find_all_vars(ast))
    wp = get_wp(ast, Q, linv)
    print(wp(env))
    sol = solve([P(env), Not(wp(env))])
    if sol is not None:
        print("there is a counter example:")
        print(sol)
        return False
    else:
        print("successfully verified")
        return True
    # ...


def get_id_ast(name):
    return adt.tree.Tree('id', [
        adt.tree.Tree(name, [])])


def find_and_replace_holes(tree, new_names: list):
    if tree.root == '??':
        new_name = f'hole{len(new_names)}'
        new_names.append(new_name)
        return get_id_ast(new_name)
    for i, subtree in enumerate(tree.subtrees):
        tree.subtrees[i] = find_and_replace_holes(subtree, new_names)
    return tree


def replace_holes_with_sol(program, hole_names, sol, env):
    # Input string and list
    replacement_list = [str(sol.eval(env[hole])) for hole in hole_names]

    # Use string formatting to replace "??" with list values
    fixed_program = program.replace("??", "{}").format(*replacement_list)
    print(fixed_program)
    return fixed_program


def unroll(while_ast, num=7):
    cond = while_ast.subtrees[0]
    body = while_ast.subtrees[1]

    root = adt.tree.Tree("if", [cond, adt.tree.Tree(';', [body, while_ast]), adt.tree.Tree("skip", [])])
    for i in range(num - 1):
        root = adt.tree.Tree("if", [cond, adt.tree.Tree(';', [body, root]), adt.tree.Tree("skip", [])])
    return root
    """
    while 1<10 do i+=1
    ->
    if i<10 then (i+=1; if i<10 then ) else skip
    ...
    if i<10 then i+=1 else skip
    while 1<10 do i+=1
    """
    adt.tree.Tree(';', [
        adt.tree.Tree(name, [])])


def preProcess(ast):
    if ast.root == 'while':
        return unroll(ast)
    for i, subtree in enumerate(ast.subtrees):
        ast.subtrees[i] = preProcess(subtree)
    return ast


def find_sol(P, ast, Q, linv, env, original_names):
    wp = get_wp(ast, Q, linv)
    sol = solve([ForAll([env[n] for n in original_names], Implies(P(env), wp(env)))])
    return sol


def create_first_phase(orig_names, hole_names, i):
    f = lambda name, e: e[name]
    possible_hole_expr = []
    for hole_name in hole_names:
        possible_hole_expr.append([partial(f, name) for name in orig_names] + [lambda e: Int(f'{hole_name}_{i}')])
    return tuple(product(*possible_hole_expr))


def create_next_phase(past_phase, orig_names, hole_name, phase_num):
    phase = []
    for vals1 in past_phase:
        for vals2 in create_first_phase(orig_names, hole_name, phase_num):
            phase.append(tuple(map(lambda vals:
                                   partial(lambda val1, val2, e: val1(e) + val2(e), vals[0], vals[1]),
                                   zip(vals1, vals2)))
                         )
            phase.append(tuple(map(lambda vals:
                                   partial(lambda val1, val2, e: val1(e) - val2(e), vals[0], vals[1]),
                                   zip(vals1, vals2)))
                         )
            phase.append(tuple(map(lambda vals:
                                   partial(lambda val1, val2, e: val1(e) * val2(e), vals[0], vals[1]),
                                   zip(vals1, vals2)))
                         )

            # phase.append(partial(lambda val1, val2, e:val1(e) / val2(e),val1,val2))
    return phase


def gen_holes(P, ast, Q, linv, program):
    original_names = find_all_vars(ast)
    hole_names = []
    ast = find_and_replace_holes(ast, hole_names)
    ast = preProcess(ast)
    env = mk_env(original_names + hole_names)
    sol = None

    current_phase = create_first_phase(original_names, hole_names, 0)
    i = 0
    phase_num = 0
    while sol is None:
        if i == len(current_phase):
            i = 0
            phase_num += 1
            current_phase = create_next_phase(current_phase, original_names, hole_names, phase_num)
        env = mk_env(original_names + hole_names)
        for hole, val in zip(hole_names, current_phase[i]):
            env[hole] = val
        sol = find_sol(P, ast, Q, linv, env, original_names)
        i += 1
    for hole in hole_names:
        print(f'\n{hole} = {sol.eval(env[hole])}\n')
    if sol is not None:
        print("there is an assignment:")
        print(sol)
        return replace_holes_with_sol(program, hole_names, sol, env)
    else:
        print("i cant fill your holes")
        return False


def synthesize(program, inputs, outputs):
    print(f'{program=}')
    print(f'{inputs=}')
    print(f'{outputs=}')
    P = lambda d: And(*[d[k] == v for k, v in inputs.items()])
    Q = lambda d: And(*[d[k] == v for k, v in outputs.items()])
    linv = lambda d: True

    ast = WhileParser()(program)
    P({"x":3})
    fixed_program = gen_holes(P, ast, Q, linv, program)
    return fixed_program






if __name__ == '__main__':

    # example program
    pvars = ['a', 'b', 'i', 'n']
    program = '''b := 2 ; assert c = 3 ; a := (b + c) + ?? ; assert a = 2 '''
    program = '''
    a := ?? ; 
    n := 3;
    while n > 0 do (  n := n - 1 ; a := a + 1);
    assert n <= 0;
    assert a = 1
    '''

    "a := (b + 1) + ?? "
    P = lambda d: True
    Q = lambda d: True
    linv = lambda d: True

    # # example program
    # pvars = ['a', 'b', 'i', 'n']
    # program = "a := b ; while i < 0 do ( b := b + 1 )"
    # P = lambda _: True
    # Q = lambda d: d['a'] == d['b']
    # linv = lambda d: d['a'] == d['b']

    #
    # Following are other programs that you might want to try
    #

    ## Program 1
    # pvars = ['x', 'i', 'y']
    # program = "y := 0 ; while y < i do ( x := x + y ; if (x * y) < 10 then y := y + 1 else skip )"
    # P = lambda d: d['x'] > 0
    # Q = lambda d: d['x'] > 0
    # linv = lambda d: d['x'] > 0

    ## Program 2
    # pvars = ['a', 'b']
    # program = "while a != b do if a > b then a := a - b else b := b - a"
    # P = lambda d: And(d['a'] > 0, d['b'] > 0)
    # Q = lambda d: And(d['a'] > 0, d['a'] == d['b'])
    # linv = lambda d: And(d['a'] > 0, d['b'] > 0)

    ast = WhileParser()(program)
    if ast:
        print(">> Valid program.")
        # Your task is to implement "verify"
        print(gen_holes(P, ast, Q, linv))
        exit()
        verify(P, ast, Q, linv=None)
    else:
        print(">> Invalid program.")
