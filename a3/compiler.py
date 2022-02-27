from ast import *

from collections import defaultdict

from typing import List, Set, Dict, Tuple, DefaultDict, Optional
import sys
import itertools
import traceback

from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86
import constants

gensym_num = 0


def gensym(x):
    """
    Constructs a new variable name guaranteed to be unique.
    :param x: A "base" variable name (e.g. "x")
    :return: A unique variable name (e.g. "x_1")
    """

    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


valid_calls = {
    'print': 'print_int',
    'input_int': 'read_int'
}
call_arity = {
    'print_int': 1,
    'input_int': 0
}
call_registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
caller_saved = ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"]
callee_saved = ["rsp", "rbp", "rbx", "r12", "r13", "r14", "r15"]


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
            case BinOp(left, op, right):
                statements, left = rco_exp(left, False)
                statements2, right = rco_exp(right, False)
                statements.extend(statements2)
                exp = BinOp(left, op, right)
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
            case _:
                raise Exception("rco")
        return new_statements

    new_prog = []
    for statement in prog.body:
        new_prog.extend(rco_stmt(statement))

    return Module(new_prog)


##################################################
# select-instructions
##################################################

def select_instructions(prog: Module) -> x86.Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """

    def atom_to_arg(exp: expr) -> x86.Arg:
        match exp:
            case Constant(i):
                return x86.Immediate(i)
            case Name(n):
                return x86.Var(n)
            case _:
                raise Exception("select_instructions/atom_to_arg")

    def translate_expression(expression: expr, destination: Optional[x86.Arg]) -> list[x86.Instr]:

        match expression:
            case Call(Name(name), args):
                instructions = []
                if name not in valid_calls.keys() or \
                        len(args) != call_arity[valid_calls[name]]:
                    raise Exception("select_instructions/call_builtin")
                for atom, reg in zip(args, call_registers):
                    instructions.append(x86.NamedInstr("movq", [atom_to_arg(atom), x86.Reg(reg)]))
                instructions.append(x86.Callq(valid_calls[name]))
                if destination is not None:
                    instructions.append(x86.NamedInstr("movq", [x86.Reg("rax"), destination]))
                return instructions
            case _:
                if destination is None:
                    return []  # if it's not a call, and it's not stored anywhere, there's no need to do it.

        match expression:
            case UnaryOp(op, exp):
                match op:
                    case USub():
                        return [
                            x86.NamedInstr("movq", [atom_to_arg(exp), destination]),
                            x86.NamedInstr("negq", [destination])
                        ]
                    case _:
                        raise Exception('select_instructions/unary_operation')
            case BinOp(left, op, right):
                match op:
                    case Add():
                        instr_name = "addq"
                    case Sub():
                        instr_name = "subq"
                    case _:
                        raise Exception('select_instructions/binary_operation')
                return [
                    x86.NamedInstr("movq", [atom_to_arg(left), destination]),
                    x86.NamedInstr(instr_name, [atom_to_arg(right), destination])
                ]
            case Constant(_) | Name(_):
                return [
                    x86.NamedInstr("movq", [atom_to_arg(expression), destination])
                ]
            case _:
                raise Exception("select_instructions")

    def translate_statement(statement: stmt) -> list[x86.Instr]:
        match statement:
            case Expr(exp):
                return translate_expression(exp, None)
            case Assign([Name(n)], exp):
                return translate_expression(exp, atom_to_arg(Name(n)))
            case _:
                raise Exception("select_instructions/translate_statement")

    instructions: list[x86.Instr] = []
    for statement in prog.body:
        instructions.extend(translate_statement(statement))
    instructions.append(x86.Jmp("conclusion"))

    return x86.Program({
        "start": instructions
    })

def reads_writes(instruction: x86.Instr) -> Tuple[Set[x86.Var], Set[x86.Var]]:

    match instruction:
        case x86.NamedInstr("movq", [read, write]):
            reads, writes = {read}, {write}
        case x86.NamedInstr("addq", [read, readwrite]) | x86.NamedInstr("subq", [read, readwrite]):
            reads, writes = {read, readwrite}, {readwrite}
        case x86.NamedInstr("negq", [readwrite]):
            reads, writes =  {readwrite}, {readwrite}
        case x86.NamedInstr("pushq", [read]):
            reads, writes = {read}, set()
        case x86.NamedInstr("popq", [write]):
            reads, writes = set(), {write}
        case _:
            reads, writes = set(), set()

    return {read for read in reads if isinstance(read, x86.Var)}, \
           {write for write in writes if isinstance(writes, x86.Var)}



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
    before = set({})

    def ul_instr(instruction: x86.Instr) -> Set[x86.Var]:
        global before
        after = before
        reads, writes = reads_writes(instruction)
        before = (before - writes) + reads
        return after

    def ul_block(instructions: List[x86.Instr]) -> List[Set[x86.Var]]:
        return [ul_instr(instruction) for instruction in instructions]

    match program:
        case x86.Program(blocks):
            return program, {label: ul_block(instructions) for label, instructions in blocks}


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


def build_interference(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Arg]]]]) -> \
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

    def bi_instr(instruction: x86.Instr, live_after: Set[x86.Arg]):
        match instruction:
            case x86.NamedInstr("movq", [source, dest]):
                for live in live_after:
                    if live != source and live != dest:
                        graph.add_edge(dest, live)
            case _:
                match reads_writes(instruction):
                    case _, writes:
                        for write in writes:
                            for live in live_after:
                                if write != live:
                                    graph.add_edge(write, live)

    def bi_block(instructions: [x86.Instr], live_after_sets: [Set[x86.Arg]]):
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
    register_order = ["rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "rbx", "r12", "r13", "r14", "r15"]


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

    def patch_instruction(instruction: x86.Instr) -> [x86.Instr]:
        match instruction:
            case x86.NamedInstr("movq", [loc1, loc2]):
                if loc1 == loc2:
                    return []
        match instruction:
            case x86.NamedInstr(name, [x86.Deref(reg1, off1), x86.Deref(reg2, off2)]):
                return [
                    x86.NamedInstr("movq", [x86.Deref(reg1, off1), x86.Reg("rax")]),
                    x86.NamedInstr(name, [x86.Reg("rax"), x86.Deref(reg2, off2)])
                ]
            case _:
                return [instruction]

    new_instructions = []
    match inputs[0]:
        case x86.Program({"start": instructions}):
            for instruction in instructions:
                new_instructions.extend(patch_instruction(instruction))

    return x86.Program({
        "start": new_instructions
    }), inputs[1]


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
    'remove complex opera*': rco,
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
