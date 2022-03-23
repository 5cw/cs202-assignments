from ast import *

from collections import OrderedDict, defaultdict
from typing import List, Set, Dict, Tuple, DefaultDict, Any
import itertools
import sys
import traceback

from cs202_support.base_ast import AST, print_ast

import cs202_support.x86exp as x86
import cif
import constants

gensym_num = 0

# Generates a new unique symbol
def gensym(x):
    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'

# Returns the "simple" name of an object's type
def name_of(op):
    return type(op).__name__

##################################################
# typecheck
##################################################



TEnv = Dict[str, type]

class CompileError(Exception):
    pass

class TypeCheckError(CompileError):
    pass

def typecheck(program: Module) -> Module:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param e: The Lif program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        'Add':   [int, int],
        'Sub': [int, int],
        'USub': [int],
        'Not': [bool],
        'Or':  [bool, bool],
        'And':  [bool, bool],
        'Gt':   [int, int],
        'GtE':  [int, int],
        'Lt':   [int, int],
        'LtE':  [int, int],
    }

    prim_output_types = {
        'Add':   int,
        'Sub': int,
        'USub': int,
        'Not': bool,
        'Or':  bool,
        'And':  bool,
        'Gt':   bool,
        'GtE':  bool,
        'Lt':   bool,
        'LtE':  bool,
    }

    builtin_arg_types = {
        'print': [int | bool], #the function is called "print_int" but the online compiler lets you print True
        #'input_int': [],
    }

    builtin_output_types = {
        'print': None,
        #'input_int': int
    }


    def check_expr(exp: expr, env: TEnv) -> type:
        match exp:
            case Constant(val):
                t = type(val)
                if t != int and t != bool:
                    raise TypeCheckError(f'Unexpected type "{t}".')
            case Name(id):
                return env[id]
            case BoolOp(operator, [left, right]) | BinOp(left, operator, right) | Compare(left, [operator], [right]):
                check_types = [check_expr(left, env), check_expr(right, env)]
                match operator:
                    case Eq() | NotEq():
                        if check_types[0] == check_types[1]:
                            return bool
                        else:
                            raise TypeCheckError(f'Cannot compare equality of types {check_types[0]} and {check_types[1]}.')
                name = name_of(operator)
                expected_types = prim_arg_types[name]
                if check_types != expected_types:
                    raise TypeCheckError(f'{check_types[0]} and {check_types[1]} are not valid types for {name}.\n'
                                         f'{name} requires types {expected_types[0]} and {expected_types[1]}.')
                return prim_output_types[name]

            case UnaryOp(operator, operand):
                check_type = check_expr(operand, env)
                name = name_of(operator)
                if check_type != prim_arg_types[name][0]:
                    raise TypeCheckError(f'{name} cannot be applied to type {check_type}.\n'
                                         f'{name} requires type {prim_arg_types[name][0]}')
                return prim_output_types[name]

            case Call(Name(name), args):
                if name not in builtin_arg_types.keys():
                    raise CompileError(f'Cannot call "{name}" because it does not exist.')
                arg_types = [check_expr(arg, env) for arg in args]
                if any([not issubclass(at, bat) for at, bat in zip(arg_types, builtin_arg_types[name])]):
                    raise TypeCheckError(f'Cannot call "{name}" on type(s) {arg_types}.\n'
                                         f'That call requires type(s) {builtin_arg_types[name]}.')
                return builtin_output_types[name]

            case _:
                raise CompileError(f'Unexpected token {print_ast(exp)}.')

    def check_stmt(statement: stmt, env):
        match statement:
            case Assign([Name(var)], value):
                val_type = check_expr(value, env)
                if val_type is None:
                    raise TypeCheckError(f'Cannot assign "{var}" to an operation which doesn\'t return anything')
                if var in env.keys():
                    if env[var] != val_type:
                        raise TypeCheckError(f'Variable "{var}" cannot be assigned type {val_type}, '
                                             f'it\'s already type {env[var]}')
                else:
                    env[var] = val_type

            case If(condition, if_true, if_false):
                if check_expr(condition, env) != bool:
                    raise TypeCheckError(f'If condition must be type bool.')
                for s in if_true:
                    check_stmt(s, env)
                for s in if_false:
                    check_stmt(s, env)
            case Expr(expression):
                exp_type = check_expr(expression, env)
                if exp_type is not None:
                    print(f'Warning! You have an unused expression of type "{exp_type}".')
            case _:
                raise CompileError(f'Unexpected token {print_ast(statement)}.')

    env = {}
    for statement in program.body:
        check_stmt(statement, env)

    return program


##################################################
# remove-complex-opera*
##################################################

def rco(prog: Module) -> Module:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lvar program
    :return: An Lvar program with atomic operator arguments.
    """

    def rco_exp(exp: expr, top: bool) -> Tuple[list[stmt], expr]:
        statements = []
        match exp:
            case Constant(_) | Name(_):
                return [], exp
            case Call(Name(n), args):
                new_args = []
                for arg in args:
                    new_statements, new_arg = rco_exp(arg, False)
                    new_args.append(new_arg)
                    statements.extend(new_statements)
                exp = Call(Name(n), new_args)
            case UnaryOp(op, i):
                statements, i = rco_exp(i, False)
                exp = UnaryOp(op, i)
            case BinOp(left, op, right) | BoolOp(op, [left, right]) | Compare(left, [op], [right]):
                statements, left = rco_exp(left, False)
                statements2, right = rco_exp(right, False)
                statements.extend(statements2)
                match exp:
                    case BinOp(_):
                        exp = BinOp(left, op, right)
                    case BoolOp(_):
                        exp = BoolOp(op, [left, right])
                    case Compare(_):
                        exp = Compare(left, [op], right)
            case _:
                raise Exception("rco/rco_exp")

        if not top:
            tmp = Name(gensym("(tmp)"))  # use parentheses because they are not allowed in normal variable names.
            statements.append(Assign([tmp], exp))
            exp = tmp
        return statements, exp

    def rco_stmt(statement: stmt) -> list[stmt]:
        match statement:
            case Expr(exp):
                new_statements, exp = rco_exp(exp, True)
                new_statements.append(Expr(exp))
            case Assign([var], exp):
                new_statements, exp = rco_exp(exp, True)
                new_statements.append(Assign([var], exp))
            case If(condition, if_true, if_false):
                match condition:
                    case Compare(left, [op], right):
                        new_statements, left = rco_exp(left, False)
                        new_statements2, right = rco_exp(right, False)
                        new_statements.extend(new_statements2)
                        condition = Compare(left, [op], right)
                    case _:
                        new_statements, condition = rco_exp(condition, False) # we cannot have any operations in conditional.
                new_true = new_false = []
                for s in if_true:
                    new_true.extend(rco_stmt(s))
                for s in if_false:
                    new_false.extend(rco_stmt(s))
                new_statements.append(If(condition, new_true, new_false))
            case _:
                raise CompileError(f"unexpected token {statement}")
        return new_statements

    new_prog = []
    for statement in prog.body:
        new_prog.extend(rco_stmt(statement))

    return Module(new_prog)



##################################################
# explicate-control
##################################################

def explicate_control(prog: Module) -> cif.CProgram:
    """
    Transforms an Lif Expression into a Cif program.
    :param e: An Lif Expression
    :return: A Cif Program
    """

    # the basic blocks of the program
    basic_blocks: Dict[str, List[cif.Stmt]] = {}

    builtin_cif_instructions = {
        'print': cif.Print
    }

    def explicate_expr(exp: expr) -> cif.Exp:
        match exp:
            case Name(name):
                return cif.AtmExp(cif.Name(name))
            case Constant(val):
                if type(val) == int:
                    return cif.AtmExp(cif.ConstantInt(val))
                else:
                    return cif.AtmExp(cif.ConstantBool(val))
            case UnaryOp(op, operand):
                return cif.UnaryOp(op, explicate_expr(operand))
            case BinOp(left, op, right) | BoolOp(op, [left, right]):
                return cif.BinOp(explicate_expr(left), op, explicate_expr(right))
            case Compare(left, [op], [right]):
                return cif.Compare(explicate_expr(left), op, explicate_expr(right))
            case Call(Name(name), args):
                return builtin_cif_instructions[name](*[explicate_expr(arg) for arg in args])
            case _:
                raise CompileError(f"unexpected token {exp}")

    def explicate_stmt(statement: stmt, blocks: Dict[str, List[cif.Stmt]], current: str) -> str:
        if current not in blocks.keys():
            blocks[current] = []
        new_current = current
        match statement:
            case Expr(exp):
                blocks[current].append(explicate_expr(exp))
            case Assign([var], exp):
                blocks[current].append(cif.Assign(var, explicate_expr(exp)))
            case If(condition, if_true, if_false):
                match condition:
                    case Constant(_) | Name(_):
                        condition = cif.Compare(explicate_expr(condition), Eq(),
                                                cif.AtmExp(cif.ConstantBool(True)))
                    case Compare(left, [op], right):
                        condition = cif.Compare(explicate_expr(left), op, explicate_expr(right))
                true_label = gensym("label")
                false_label = gensym("label")
                new_current = gensym("label")

                for s in if_true:
                    explicate_stmt(s, blocks, true_label)
                blocks[true_label].append(cif.Goto(new_current))
                if len(if_false) == 0: #if there is no else, we can jump right back to where we came from
                    false_label = new_current
                else:
                    for s in if_false:
                        explicate_stmt(s, blocks, false_label)
                    blocks[false_label].append(cif.Goto(new_current))
                blocks[current].append(cif.If(condition, cif.Goto(true_label), cif.Goto(false_label)))
            case _:
                raise CompileError(f"unexpected token {statement}")
        return new_current

    current_label = "start"
    for statement in prog.body:
        current_label = explicate_stmt(statement, basic_blocks, current_label)
    basic_blocks[current_label].append(cif.Goto("conclusion"))
    return cif.CProgram(basic_blocks)




##################################################
# select-instructions
##################################################

def select_instructions(p: cif.CProgram) -> x86.Program:
    """
    Transforms a Cif program into a pseudo-x86 assembly program.
    :param p: a Cif program
    :return: a pseudo-x86 program
    """

    op_cc = {
        'Eq': 'e',
        'Gt': 'g',
        'GtE': 'ge',
        'Lt': 'l',
        'LtE': 'le',
    }

    binop_instrs = {
        'And': 'andq',
        'Or': 'orq',
        'Add': 'addq',
        'Sub': 'subq'
    }

    def si_atm(atm: cif.Atm) -> x86.Arg:
        match atm:
            case cif.Name(name):
                return x86.Var(name)
            case cif.ConstantInt(i) | cif.ConstantBool(i):
                return x86.Immediate(int(i))

    def si_stmt(statement: cif.Stmt) -> [x86.Instr]:
        match statement:
            case cif.Assign(var, exp):
                dest = x86.Var(var)
                def move_to_var(atm):
                    return x86.NamedInstr("movq", [si_atm(atm), dest])
                match exp:
                    case cif.AtmExp(atm):
                        return [move_to_var(atm)]
                    case cif.UnaryOp(op, cif.AtmExp(atm)):
                        match op:
                            case USub():
                                return [move_to_var(atm),
                                        x86.NamedInstr("negq", [dest])]
                            case Not():
                                return [move_to_var(atm),
                                        x86.NamedInstr("xorq", [x86.Immediate(1), dest])]
                    case cif.BinOp(cif.AtmExp(atm1), op, cif.AtmExp(atm2)):
                        return [move_to_var(atm1),
                                x86.NamedInstr(binop_instrs[name_of(op)], [si_atm(atm2), dest])]
                    case cif.Compare(cif.AtmExp(atm1), op, cif.AtmExp(atm2)):
                        return [x86.NamedInstr("cmpq", [si_atm(atm1), si_atm(atm2)]),
                                x86.Set(op_cc[name_of(op)], x86.ByteReg("al")),
                                x86.NamedInstr("movzbq", [x86.ByteReg("al"), dest])]
            case cif.If(cif.Compare(cif.AtmExp(atm1), op, cif.AtmExp(atm2)),
                        cif.Goto(true_label), cif.Goto(false_label)):
                return [x86.NamedInstr("cmpq", [si_atm(atm1), si_atm(atm2)]),
                        x86.JmpIf(op_cc[name_of(op)], true_label),
                        x86.Jmp(false_label)]
            case cif.Goto(label):
                return [x86.Jmp(label)]
            case cif.Print(cif.AtmExp(atm)):
                return [x86.NamedInstr("movq", [x86.Reg("rdi")]),
                        x86.Callq("print_int")]





    pass


##################################################
# uncover-live
##################################################

def uncover_live(program: x86.Program) -> Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]:
    """
    Performs liveness analysis. Returns the input program, plus live-after sets
    for its blocks.
    :param program: a pseudo-x86 assembly program
    :return: A tuple. The first element is the same as the input program. The
    second element is a dict of live-after sets. This dict maps each label in
    the program to a list of live-after sets for that label. The live-after
    sets are in the same order as the label's instructions.
    """

    pass


##################################################
# build-interference
##################################################

class InterferenceGraph:
    """
    A class to represent an interference graph: an undirected graph where nodes
    are x86.Arg objects and an edge between two nodes indicates that the two
    nodes cannot share the same locations.
    """
    graph: DefaultDict[x86.Arg, Set[x86.Arg]]

    def __init__(self):
        self.graph = defaultdict(lambda: set())

    def add_edge(self, a: x86.Arg, b: x86.Arg):
        if a != b:
            self.graph[a].add(b)
            self.graph[b].add(a)

    def neighbors(self, a: x86.Arg) -> Set[x86.Arg]:
        if a in self.graph:
            return self.graph[a]
        else:
            return set()

    def __str__(self):
        pairs = set()
        for k in self.graph.keys():
            new_pairs = set((k, v) for v in self.graph[k])
            pairs = pairs.union(new_pairs)

        for a, b in list(pairs):
            if (b, a) in pairs:
                pairs.remove((a, b))

        strings = [print_ast(a) + ' -- ' + print_ast(b) for a, b in pairs]
        return 'InterferenceGraph{\n ' + ',\n '.join(strings) + '\n}'


def build_interference(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> \
        Tuple[x86.Program, InterferenceGraph]:
    """
    Build the interference graph.
    :param inputs: A Tuple. The first element is a pseudo-x86 program. The
    second element is the dict of live-after sets produced by the uncover-live
    pass.
    :return: A Tuple. The first element is the same as the input program. The
    second is a completed interference graph.
    """

    pass


##################################################
# allocate-registers
##################################################

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]


def allocate_registers(inputs: Tuple[x86.Program, InterferenceGraph]) -> \
        Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param inputs: A Tuple. The first element is the pseudo-x86 program. The
    second element is the completed interference graph.
    :return: A Tuple. The first element is an x86 program (with no variable
    references). The second element is the number of bytes needed in stack
    locations.
    """

    pass


##################################################
# patch-instructions
##################################################

def patch_instructions(inputs: Tuple[x86.Program, int]) -> Tuple[x86.Program, int]:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param inputs: A Tuple. The first element is an x86 program. The second element is the
    stack space in bytes.
    :return: A Tuple. The first element is the patched x86 program. The second element is
    the stack space in bytes.
    """

    pass


##################################################
# print-x86
##################################################

def print_x86(inputs: Tuple[x86.Program, int]) -> str:
    """
    Prints an x86 program to a string.
    :param inputs: A Tuple. The first element is the x86 program. The second element
    is the stack space in bytes.
    :return: A string, ready for gcc.
    """

    pass


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'uncover live': uncover_live,
    'build interference': build_interference,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'print x86': print_x86
}


def run_compiler(s, logging=False):
    current_program = parse(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print(print_ast(current_program))

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print(print_ast(current_program))

    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())

