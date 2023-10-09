import multiprocessing
from while_lang.syntax import WhileParser
import adt.tree
import operator
from z3 import Int, ForAll, Implies, Not, And, Or, Solver, unsat, sat, simplify, z3printer
from copy import copy, deepcopy
from functools import partial
from itertools import product


def signal_handler(signum, frame):
    raise Exception("Timed out!")


z3printer


class LazyDict(dict):
    def __init__(self, *args, **kwds) -> None:
        super().__init__(*args, **kwds)

    def __getitem__(self, __key):
        ret = super().__getitem__(__key)

        if callable(ret):
            ret = ret(self)
            # self[__key] = ret
            return ret
        return ret


OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.truediv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}

generated_div_non_zero_div_cond = [True]


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
        return [ast.subtrees[0].subtrees[0].root]  # varName
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
    # print((formulas[0]))
    s = Solver()
    s.add(formulas)
    if s.check() == sat:
        return s.model()


def encode_expr(ast, env):
    global generated_div_non_zero_div_cond
    if ast.root == 'id':
        generated_div_non_zero_div_cond[0] = True
        return env[ast.subtrees[0].root], generated_div_non_zero_div_cond[0]
    elif ast.root == 'num':
        return ast.subtrees[0].root, True
    elif ast.root in OP:
        left_expr, zero_div_cond1 = encode_expr(ast.subtrees[0], env)
        right_expr, zero_div_cond2 = encode_expr(ast.subtrees[1], env)
        if zero_div_cond1 is True and zero_div_cond2 is True:
            zero_div_cond = True
        elif zero_div_cond1 is True:
            zero_div_cond = zero_div_cond2
        elif zero_div_cond2 is True:
            zero_div_cond = zero_div_cond1
        else:
            zero_div_cond = And(zero_div_cond2, zero_div_cond1)
        if '/' == ast.root:
            zero_div_cond = And(zero_div_cond, right_expr != 0)
        return OP[ast.root](left_expr, right_expr), zero_div_cond
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

            expr, zero_div = encode_expr(right, e)
            return And(zero_div, Q(upd(e, var_name, expr)))

        return assignment_lambda

    elif ast.root == 'if':
        def if_lambda(e):
            wp_then = get_wp(ast.subtrees[1], Q, linv)
            wp_else = get_wp(ast.subtrees[2], Q, linv)
            cond, zero_div = encode_expr(ast.subtrees[0], e)
            if zero_div is True:
                return Or(And(cond, wp_then(e)), And(Not(cond), wp_else(e)))
            return And(zero_div, Or(And(cond, wp_then(e)), And(Not(cond), wp_else(e))))

        return if_lambda

    elif ast.root == 'while':
        def lambda_while(e):

            new_env = mk_env(list(e.keys()))
            unassigned_vars = [v for v in e.keys() if v not in get_assigned_vars(ast)]
            for var in unassigned_vars:
                new_env = upd(new_env, var, e[var])
            wp = get_wp(ast.subtrees[1], linv, linv)
            cond, zero_div = encode_expr(ast.subtrees[0], new_env)
            first_cond, first_zero_div = encode_expr(ast.subtrees[0], e)
            return And(Implies(first_cond, And(linv(e),
                                               ForAll([new_env[v] for v in get_assigned_vars(ast)],
                                                      And(
                                                          Implies(And(linv(new_env), cond), wp(new_env)),
                                                          Implies(And(linv(new_env), Not(cond)), Q(new_env)),
                                                          Implies(linv(new_env), zero_div)
                                                      )
                                                      ))),
                       Implies(Not(first_cond), Q(e)),
                       first_zero_div)

        return lambda_while

    elif ast.root == 'assert':
        def lambda_assert(e):
            expr, zero_div = encode_expr(ast.subtrees[0], e)
            if zero_div is True:
                return And(expr, Q(e))
            return And(zero_div, expr, Q(e))

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
    # print(wp(env))
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
    replacement_list = ['0' if x.startswith("hole") else x for x in
                        replacement_list]  # default value for all unbonded holes
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
        possible_hole_expr.append(
            [partial(lambda n, e: Int(f'{n}_{i}'), hole_name)] + [partial(f, name) for name in orig_names])
    return tuple(product(*possible_hole_expr))


def div_phase(val1, val2, e):
    global generated_div_non_zero_div_cond
    under = val2(e)
    generated_div_non_zero_div_cond[0] = And(under != 0, generated_div_non_zero_div_cond[0])
    return val1(e) / val2(e)


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
            phase.append(tuple(map(lambda vals:
                                   partial(div_phase,vals[0],vals[1]),
                                   zip(vals1, vals2)))
                )

    return phase


def gen_holes(P, ast, Q, linv, program, withExprs=True):
    original_names = find_all_vars(ast)
    hole_names = []
    ast = find_and_replace_holes(ast, hole_names)
    ast = preProcess(ast)

    env = mk_env(original_names + hole_names)

    sol = None

    current_phase = create_first_phase(original_names, hole_names, 0)
    i = 0
    phase_num = 0
    while sol is None and phase_num < 10:

        env = mk_env(original_names + hole_names)
        if withExprs:
            if i == len(current_phase):
                i = 0
                phase_num += 1

                current_phase = create_next_phase(current_phase, original_names, hole_names, phase_num)

            for hole, val in zip(hole_names, current_phase[i]):
                env[hole] = val

        try:
            sol = find_sol(P, ast, Q, linv, env, original_names)
        except Exception as e:
            sol = None
            # print("fake none")
        # print(sol)
        i += 1
        if not withExprs:  # if no expr and sol not found on first time there is no sol
            break
    if sol is None and withExprs:
        return "timeout"
    if sol is None and not withExprs:
        return "solution can't be found"
    if sol is not None:
        print("there is an assignment:")
        print(sol)
        return replace_holes_with_sol(program, hole_names, sol, env)
    else:
        print("i cant fill your holes")
        return False


def synthesize(program, inputs, outputs, withExprs=True):
    P = lambda d: And(*[d[k] == v for k, v in inputs.items()]) if isinstance(inputs,dict) else inputs
    Q = lambda d: And(*[d[k] == v for k, v in outputs.items()]) if isinstance(outputs,dict) else outputs
    linv = lambda d: True

    ast = WhileParser()(program)
    fixed_program = gen_holes(P, ast, Q, linv, program, withExprs)

    return fixed_program


def synthesizeAndVerify(program, inputs, outputs, P, Q, linv, withExprs=True):
    inp = lambda d: And(*[d[k] == v for k, v in inputs.items()])
    out = lambda d: And(*[d[k] == v for k, v in outputs.items()])
    ast = WhileParser()(program)
    inp({"x": 3})
    fixed_program = gen_holes(inp, ast, out, linv, program, withExprs)
    new_ast = WhileParser()(fixed_program)
    if new_ast:
        verify_result = verify(P, new_ast, Q, linv=linv)
        return (fixed_program, verify_result)
    return (fixed_program, False)

