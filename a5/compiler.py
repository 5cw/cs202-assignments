import random
from ast import *

from dataclasses import dataclass
from collections import OrderedDict, defaultdict
from functools import reduce
from typing import List, Set, Dict, Tuple, DefaultDict
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

# A "begin expression" for Python
# Runs the list of statements, then evaluates to the value of the expression
class Begin(expr):
    _fields = ('stmts', 'exp')
    __match_args__ = _fields

    def __init__(self, stmts, exp):
        self.stmts = stmts
        self.exp = exp

class CompileError(Exception):
    def __init__(self, ast):
        super().__init__(f"Unexpected token: {print_ast(ast)}")


class TypeCheckError(Exception):
    pass

##################################################
# typecheck
##################################################

TEnv = Dict[str, type]

def typecheck(program: Module) -> Module:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param e: The Lif program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        'Add': [int, int],
        'Sub': [int, int],
        'Mult': [int, int],
        'USub': [int],
        'Not': [bool],
        'Or': [bool, bool],
        'And': [bool, bool],
        'Gt': [int, int],
        'GtE': [int, int],
        'Lt': [int, int],
        'LtE': [int, int],
    }

    prim_output_types = {
        'Add': int,
        'Sub': int,
        'Mult': int,
        'USub': int,
        'Not': bool,
        'Or': bool,
        'And': bool,
        'Gt': bool,
        'GtE': bool,
        'Lt': bool,
        'LtE': bool,
    }

    builtin_arg_types = {
        'print': [int | bool],  # the function is called "print_int" but the online compiler lets you print True
        # 'input_int': [],
    }

    builtin_output_types = {
        'print': None,
        # 'input_int': int
    }

    def tc_expr(exp: expr, env: TEnv) -> type:
        match exp:
            case Constant(val):
                t = type(val)
                if t != int and t != bool:
                    raise TypeCheckError(f'Unexpected type "{t}".')
                return t
            case Name(id):
                return env[id]
            case BoolOp(operator, [left, right]) | BinOp(left, operator, right) | Compare(left, [operator], [right]):
                check_types = [tc_expr(left, env), tc_expr(right, env)]
                match operator:
                    case Eq() | NotEq():
                        if check_types[0] == check_types[1]:
                            return bool
                        else:
                            raise TypeCheckError(
                                f'Cannot compare equality of types {check_types[0]} and {check_types[1]}.')
                name = name_of(operator)
                expected_types = prim_arg_types[name]
                if check_types != expected_types:
                    raise TypeCheckError(f'{check_types[0]} and {check_types[1]} are not valid types for {name}.\n'
                                         f'{name} requires types {expected_types[0]} and {expected_types[1]}.')
                return prim_output_types[name]

            case UnaryOp(operator, operand):
                check_type = tc_expr(operand, env)
                name = name_of(operator)
                if check_type != prim_arg_types[name][0]:
                    raise TypeCheckError(f'{name} cannot be applied to type {check_type}.\n'
                                         f'{name} requires type {prim_arg_types[name][0]}')
                return prim_output_types[name]

            case Call(Name(name), args):
                if name not in builtin_arg_types.keys():
                    raise CompileError(f'Cannot call "{name}" because it does not exist.')
                arg_types = [tc_expr(arg, env) for arg in args]
                if len(arg_types) != len(builtin_arg_types) | \
                        any([not issubclass(at, bat) for at, bat in zip(arg_types, builtin_arg_types[name])]):

                    raise TypeCheckError(f'Cannot call "{name}" on type(s) {arg_types}.\n'
                                         f'That call requires type(s) {builtin_arg_types[name]}.')
                return builtin_output_types[name]

            case _:
                raise CompileError(exp)

    def tc_stmt(statement: stmt, env):
        match statement:
            case Assign([Name(var)], value):
                val_type = tc_expr(value, env)
                if val_type is None:
                    raise TypeCheckError(f'Cannot assign "{var}" to an operation which doesn\'t return anything')
                if var in env.keys():
                    if env[var] != val_type:
                        raise TypeCheckError(f'Variable "{var}" cannot be assigned type {val_type}, '
                                             f'it\'s already type {env[var]}')
                else:
                    env[var] = val_type

            case If(condition, if_true, if_false):
                if tc_expr(condition, env) != bool:
                    raise TypeCheckError(f'If condition must be type bool.')
                for s in if_true:
                    tc_stmt(s, env)
                for s in if_false:
                    tc_stmt(s, env)

            case While(condition, body, []):
                if tc_expr(condition, env) != bool:
                    raise TypeCheckError(f'While condition must be type bool.')
                for s in body:
                    tc_stmt(s, env)

            case Expr(expression):
                exp_type = tc_expr(expression, env)
                if exp_type is not None:
                    print(f'Warning! You have an unused expression of type "{exp_type}".')
            case _:
                raise CompileError(statement)

    env = {}
    for statement in program.body:
        tc_stmt(statement, env)

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

    def rco_expr(exp: expr, top: bool, temps: dict[str, expr]) -> expr:
        match exp:
            case Constant(_) | Name(_):
                return exp
            case Call(Name(n), args):
                new_args = []
                for arg in args:
                    new_arg = rco_expr(arg, False, temps)
                    new_args.append(new_arg)
                exp = Call(Name(n), new_args)
            case UnaryOp(op, i):
                i = rco_expr(i, False, temps)
                exp = UnaryOp(op, i)
            case BinOp(left, op, right) | BoolOp(op, [left, right]) | Compare(left, [op], [right]):
                left = rco_expr(left, False, temps)
                right = rco_expr(right, False, temps)
                match exp:
                    case BinOp(_):
                        exp = BinOp(left, op, right)
                    case BoolOp(_):
                        exp = BoolOp(op, [left, right])
                    case Compare(_):
                        exp = Compare(left, [op], [right])
            case _:
                raise CompileError(exp)

        if not top:
            tmp = gensym("(tmp)")  # use parentheses because they are not allowed in normal variable names.
            temps[tmp] = exp
            exp = Name(tmp)
        return exp


    def rco_stmt(statement: stmt) -> list[stmt]:

        def temps_to_stmts(temps: dict[str, expr]) -> list[stmt]:
            new_stmts = []
            for temp, value in temps.items():
                new_stmts.append(Assign([Name(temp)], value))
            return new_stmts

        temps = {}
        match statement:
            case Expr(exp):
                new_stmt = Expr(rco_expr(exp, True, temps))
            case Assign([var], exp):
                exp = rco_expr(exp, True, temps)
                new_stmt = Assign([var], rco_expr(exp, True, temps))
            case If(condition, if_true, if_false):
                new_true = []
                new_false = []
                for s in if_true:
                    new_true.extend(rco_stmt(s))
                for s in if_false:
                    new_false.extend(rco_stmt(s))
                new_stmt = If(rco_expr(condition, True, temps), new_true, new_false)
            case While(condition, body, []):
                new_body = []
                for s in body:
                    new_body.extend(rco_stmt(s))
                before_temps = {}
                new_expr = rco_expr(condition, True, before_temps)
                new_stmt = While(Begin(temps_to_stmts(before_temps), new_expr), new_body, [])
            case _:
                raise CompileError(statement)
        new_stmts = temps_to_stmts(temps)
        new_stmts.append(new_stmt)
        return new_stmts


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

    def add_stmt(label: str, s: cif.Stmt):
        if label not in basic_blocks:
            basic_blocks[label] = []

        basic_blocks[label].append(s)


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
            case _:
                raise CompileError(exp)

    def explicate_stmt(statement: stmt, blocks: Dict[str, List[cif.Stmt]], current: str) -> str:
        new_current = current
        match statement:
            case Expr(Call(Name(name), args)):
                call = builtin_cif_instructions[name](*[explicate_expr(arg) for arg in args])
                add_stmt(current, call)
            case Assign([var], exp):
                add_stmt(current, cif.Assign(var, explicate_expr(exp)))
            case If(condition, if_true, if_false):
                match condition:
                    case Constant(_) | Name(_):
                        condition = cif.Compare(explicate_expr(condition), Eq(),
                                                cif.AtmExp(cif.ConstantBool(True)))
                    case Compare(left, [op], [right]):
                        condition = cif.Compare(explicate_expr(left), op, explicate_expr(right))
                    case _:
                        raise CompileError(condition)
                true_label = gensym("label")
                false_label = gensym("label")
                new_current = gensym("label")

                explicate_block(if_true, blocks, true_label, new_current)
                if len(if_false) == 0:  # if there is no else, we can jump right back to where we came from
                    false_label = new_current
                else:
                    explicate_block(if_false, blocks, false_label, new_current)
                add_stmt(current, cif.If(condition, cif.Goto(true_label), cif.Goto(false_label)))
            case While(begin, body, []):
                match begin:
                    case Begin(begin_stmts, condition):
                        pass
                    case _:
                        raise CompileError(begin)
                match condition:
                    case Constant(_) | Name(_):
                        condition = cif.Compare(explicate_expr(condition), Eq(),
                                                cif.AtmExp(cif.ConstantBool(True)))
                    case Compare(left, [op], [right]):
                        condition = cif.Compare(explicate_expr(left), op, explicate_expr(right))
                    case _:
                        raise CompileError(condition)
                begin_label = gensym("label")
                check_label = gensym("label")
                body_label = gensym("label")
                new_current = gensym("label")
                add_stmt(current, cif.Goto(begin_label))
                explicate_block(begin_stmts, blocks, begin_label, check_label)
                add_stmt(check_label, cif.If(condition, cif.Goto(body_label), cif.Goto(new_current)))
                explicate_block(body, blocks, body_label, begin_label)
            case _:
                raise CompileError(statement)
        return new_current

    def explicate_block(statements: [stmt], blocks, start, end):
        current_label = start
        for statement in statements:
            current_label = explicate_stmt(statement, blocks, current_label)
        add_stmt(current_label, cif.Goto(end))

    explicate_block(prog.body, basic_blocks, "start", "conclusion")

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
        'Sub': 'subq',
        'Mult':  'imulq'
    }

    def si_atm(atm: cif.Atm) -> x86.Arg:
        match atm:
            case cif.Name(name):
                return x86.Var(name)
            case cif.ConstantInt(i) | cif.ConstantBool(i):
                return x86.Immediate(int(i))
            case _:
                raise CompileError(atm)

    def si_stmt(statement: cif.Stmt) -> [x86.Instr]:
        match statement:
            case cif.Assign(Name(var), exp):
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
                        return [x86.NamedInstr("cmpq", [si_atm(atm2), si_atm(atm1)]),
                                x86.Set(op_cc[name_of(op)], x86.ByteReg("al")),
                                x86.NamedInstr("movzbq", [x86.ByteReg("al"), dest])]
            case cif.If(cif.Compare(cif.AtmExp(atm1), op, cif.AtmExp(atm2)),
                        cif.Goto(true_label), cif.Goto(false_label)):
                return [x86.NamedInstr("cmpq", [si_atm(atm2), si_atm(atm1)]),
                        x86.JmpIf(op_cc[name_of(op)], true_label),
                        x86.Jmp(false_label)]
            case cif.Goto(label):
                return [x86.Jmp(label)]
            case cif.Print(cif.AtmExp(atm)):
                return [x86.NamedInstr("movq", [si_atm(atm), x86.Reg("rdi")]),
                        x86.Callq("print_int")]
            case _:
                raise CompileError(statement)

    return x86.Program({
        label: reduce(
            lambda l1, l2: l1 + l2,
            [si_stmt(statement) for statement in block]
        ) for label, block in p.blocks.items()
    })


def reads_writes(instruction: x86.Instr) -> Tuple[Set[x86.Var], Set[x86.Var]]:
    match instruction:
        case x86.NamedInstr("movq", [read, write]):
            reads, writes = {read}, {write}
        case x86.NamedInstr("addq" | "subq" | "andq" | "orq" | "xorq", [read, readwrite]):
            reads, writes = {read, readwrite}, {readwrite}
        case x86.NamedInstr("cmpq", [read, read2]):
            reads, writes = {read, read2}, set()
        case x86.NamedInstr("negq", [readwrite]):
            reads, writes = {readwrite}, {readwrite}
        case x86.NamedInstr("pushq", [read]):
            reads, writes = {read}, set()
        case x86.NamedInstr("popq", [write]) | x86.NamedInstr("movzbq", [_, write]):
            reads, writes = set(), {write}
        case _:
            reads, writes = set(), set()

    def is_var(arg: x86.Arg) -> bool:
        match arg:
            case x86.Var(_):
                return True
            case _:
                return False

    return {read for read in reads if is_var(read)}, \
           {write for write in writes if is_var(write)}



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

    live_before_per_block = {}

    graph_forward = {}
    graph_backward = {}

    def ul_instr(instruction: x86.Instr, before) -> Set[x86.Var]:
        reads, writes = reads_writes(instruction)
        before.difference_update(writes)
        before.update(reads)
        return before.copy()

    def ul_block(instructions: List[x86.Instr], label, input) -> List[Set[x86.Var]]:
        live_after = []
        for instruction in reversed(instructions):
            live_after.insert(0, input)
            input = ul_instr(instruction, input)
        for from_label in graph_backward[label]:
            live_before_per_block[label] = input.copy()
        return live_after

    def populate_graphs(blocks):
        for label in blocks.keys():
            graph_backward[label] = []
            graph_forward[label] = []
        def add_to_graphs(from_label, to_label):
            if to_label in blocks.keys() and from_label in blocks.keys():
                graph_backward[to_label].append(from_label)
                graph_forward[from_label].append(to_label)
        for from_label, block in blocks.items():
            match block[-1]:
                case x86.Jmp(to_label):
                    add_to_graphs(from_label, to_label)
                case e:
                    raise CompileError(e)
            if len(block) > 1:
                match block[-2]:
                    case x86.JmpIf(_, to_label):
                        add_to_graphs(from_label, to_label)

    def analyze_dataflow(blocks) -> dict[str, list[set[x86.Var]]]:
        populate_graphs(blocks)
        live_after_sets = {}
        worklist = [label for label in blocks.keys()]
        for label in worklist:
            live_before_per_block[label] = set()
        while worklist:
            current = worklist.pop(0)
            input = set()
            for to_label in graph_forward[current]:

                input.update(live_before_per_block[to_label])
            old = live_before_per_block[current].copy()
            live_after_sets[current] = ul_block(blocks[current], current, input)
            if live_before_per_block[current] != old:
                worklist.extend(graph_backward[current])
        return live_after_sets

    match program:
        case x86.Program(blocks):
            return program, analyze_dataflow(blocks)


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
    graph = InterferenceGraph()

    def bi_instr(instruction: x86.Instr, live_after: Set[x86.Var]):
        match instruction:
            case x86.NamedInstr("movq", [source, x86.Var(dest_name)]):
                for live in live_after:
                    if live != source and live != x86.Var(dest_name):
                        graph.add_edge(x86.Var(dest_name), live)
            case _:
                match reads_writes(instruction):
                    case _, writes:
                        for write in writes:
                            for live in live_after:
                                if write != live:
                                    graph.add_edge(write, live)

    def bi_block(instructions: [x86.Instr], live_after_sets: [Set[x86.Var]]):
        for instruction, live_after in zip(instructions, live_after_sets):
            bi_instr(instruction, live_after)

    match inputs:
        case x86.Program(blocks), live_dict:
            for key in blocks.keys():
                bi_block(blocks[key], live_dict[key])
            return x86.Program(blocks), graph


##################################################
# allocate-registers
##################################################

Color = int
Coloring = dict[x86.Var, Color]
Saturation = set[Color]
SatMap = dict[x86.Var, Saturation]

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
    register_order = constants.caller_saved_registers + constants.callee_saved_registers

    def ar_select(sat: SatMap) -> x86.Var:
        max = 0
        possible = []
        for var, s in sat.items():
            if var not in coloring.keys():
                if len(s) > max:
                    possible = [var]
                    max = len(s)
                elif len(s) == max:
                    possible.append(var)
        return random.choice(possible)

    num_colors = 0
    prog, interference = inputs
    saturation_map = SatMap()
    for var in interference.graph.keys():
        saturation_map[var] = Saturation()

    coloring = Coloring()

    while len(interference.graph) > len(coloring):
        var = ar_select(saturation_map)
        if len(saturation_map[var]) >= num_colors:
            color = num_colors
            num_colors += 1
        else:
            color = min(set(range(num_colors)) - saturation_map[var])
        coloring[var] = color
        for neighbor in interference.neighbors(var):
            saturation_map[neighbor].add(color)

    mapping: list[x86.Arg] = [x86.Reg(reg) for reg in register_order]
    if len(register_order) > num_colors:
        stack_size = 0
    else:
        num_vars = num_colors - len(register_order)
        extension = [x86.Deref("rbp", -(8 * i)) for i in range(1, num_vars + 1)]
        stack_size = num_vars * 8
        stack_size = stack_size if stack_size % 16 == 0 else stack_size + 8
        mapping.extend(extension)

    def ar_arg(arg: x86.Arg) -> x86.Arg:

        match arg:
            case x86.Var(_):
                if arg not in coloring.keys():
                    return mapping[0]
                return mapping[coloring[arg]]
            case _:
                return arg

    def ar_instr(instruction: x86.Instr) -> x86.Instr:
        print_ast(instruction)
        match instruction:
            case x86.NamedInstr(name, args):
                return x86.NamedInstr(name, [ar_arg(arg) for arg in args])
            case _:
                return instruction

    def ar_block(block: list[x86.Instr]) -> list[x86.Instr]:
        return [ar_instr(instruction) for instruction in block]

    return x86.Program({
        key: ar_block(block) for key, block in prog.blocks.items()
    }), stack_size


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

    label_patches = {}

    def patch_instruction(instruction: x86.Instr) -> [x86.Instr]:
        match instruction:
            case x86.NamedInstr("movq", [loc1, loc2]) if loc1 == loc2:
                return []
            case x86.NamedInstr(name, [x86.Deref(reg1, off1), x86.Deref(reg2, off2)]):
                return [
                    x86.NamedInstr("movq", [x86.Deref(reg1, off1), x86.Reg("rax")]),
                    x86.NamedInstr(name, [x86.Reg("rax"), x86.Deref(reg2, off2)])
                ]
            case x86.NamedInstr("cmpq", [x86.Immediate(i1), x86.Immediate(i2)]):
                return [
                    x86.NamedInstr("movq", [x86.Immediate(i1), x86.Reg("rax")]),
                    x86.NamedInstr("cmpq", [x86.Immediate(i2), x86.Reg("rax")])
                ]
            case x86.Jmp(label):
                if label in label_patches.keys():
                    return [x86.Jmp(label_patches[label])]
            case x86.JmpIf(cc, label):
                if label in label_patches.keys():
                    return [x86.JmpIf(cc, label_patches[label])]

        return [instruction]

    def patch_block(block: [x86.Instr]):
        new_block = []
        for instruction in block:
            new_block.extend(patch_instruction(instruction))
        return new_block

    match inputs[0]:
        case x86.Program(blocks):
            pass
        case _:
            raise CompileError(inputs[0])

    def patch_labels():
        label_patches.clear()
        for label, block in blocks.items():
            if len(block) == 1:
                match block[0]:
                    case x86.Jmp(next_label):
                        label_patches[label] = next_label

        for label in label_patches.keys():
            next_label = label_patches[label]
            while next_label in label_patches.keys():
                next_label = label_patches[next_label]
            label_patches[label] = next_label
            del blocks[label]

    while True:
        patch_labels()
        blocks = {
            key: patch_block(block) for key, block in blocks.items()
        }
        if len(label_patches) == 0:
            break

    return x86.Program(blocks), inputs[1]


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


    def print_program(program: x86.Program) -> str:
        match program:
            case x86.Program(blocks):
                body = ""
                for name, block in blocks.items():
                    body += f"{name}:\n"
                    for instruction in block:
                        body += f"    {print_instruction(instruction)}\n"
                return body
            case _:
                raise CompileError(program)

    def print_instruction(instruction: x86.Instr) -> str:
        match instruction:
            case x86.NamedInstr(name, args):
                args_str = ", ".join([print_arg(arg) for arg in args])
                return f"{name} {args_str}"
            case x86.Callq(label):
                return f"callq {label}"
            case x86.Jmp(label):
                return f"jmp {label}"
            case x86.JmpIf(cc, label):
                return f"j{cc} {label}"
            case x86.Set(cc, reg):
                return f"set{cc} {print_arg(reg)}"
            case x86.Retq():
                return "retq"
            case _:
                raise CompileError(instruction)

    def print_arg(arg: x86.Arg) -> str:
        match arg:
            case x86.Immediate(i):
                return f"${i}"
            case x86.Reg(name) | x86.ByteReg(name):
                return f"%{name}"
            case x86.Deref(name, off):
                return f"{off}(%{name})"
            case _:
                raise CompileError(arg)

    program = None
    main = [
        x86.NamedInstr("pushq", [x86.Reg("rbp")]),
        x86.NamedInstr("movq", [x86.Reg("rsp"), x86.Reg("rbp")]),
        x86.NamedInstr("subq", [x86.Immediate(inputs[1]), x86.Reg("rsp")]),
        x86.Jmp("start")
    ]
    conclusion = [
        x86.NamedInstr("movq", [x86.Immediate(0), x86.Reg("rax")]),
        x86.NamedInstr("addq", [x86.Immediate(inputs[1]), x86.Reg("rsp")]),
        x86.NamedInstr("popq", [x86.Reg("rbp")]),
        x86.Retq()
    ]
    if inputs[1] == 0:
        del main[2]
        del conclusion[1]

    match inputs[0]:
        case x86.Program(blocks):
            new_blocks = {
                "main": main
            }
            new_blocks.update(blocks)
            new_blocks["conclusion"] = conclusion
            program = x86.Program(new_blocks)

    return ".globl main\n" + print_program(program)


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

