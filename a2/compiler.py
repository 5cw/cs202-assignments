from ast import *

from typing import List, Set, Dict, Tuple
import sys
import traceback
from dataclasses import dataclass

from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86

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

    def simplify_expr(exp: expr, top: bool) -> ([stmt], expr):
        statements = []
        match exp:
            case Constant(_) | Name(_):
                return [], exp
            case Call(Name(n), args):
                new_args = []
                for arg in args:
                    new_statements, new_arg = simplify_expr(arg, False)
                    new_args.append(new_arg)
                    statements.extend(new_statements)
                exp = Call(Name(n), new_args)
            case UnaryOp(op, i):
                statements, i = simplify_expr(i, False)
                exp = UnaryOp(op, i)
            case BinOp(left, op, right):
                statements, left = simplify_expr(left, False)
                statements2, right = simplify_expr(right, False)
                statements.extend(statements2)
                exp = BinOp(left, op, right)
            case _:
                raise Exception("rco/simplify_expr")

        if not top:
            tmp = Name(gensym("tmp"))
            statements.append(Assign([tmp], exp))
            exp = tmp
        return statements, exp

    new_prog = Module([])
    for statement in prog.body:
        match statement:
            case Expr(exp):
                new_statements, exp = simplify_expr(exp, True)
                new_prog.body.extend(new_statements)
                new_prog.body.append(Expr(exp))
            case Assign([var], exp):
                new_statements, exp = simplify_expr(exp, True)
                new_prog.body.extend(new_statements)
                new_prog.body.append(Assign([var], exp))
            case _:
                raise Exception("rco")
    return new_prog


##################################################
# select-instructions
##################################################



def select_instructions(prog: Module) -> x86.Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """

    valid_calls = {
        'print': {
            'name': 'print_int',
            'args': 1,
        },
        'input_int': {
            'name': 'read_int',
            'args': 0,
        }
    }

    def atom_to_arg(exp: expr) -> x86.Arg:
        match exp:
            case Constant(i):
                return x86.Immediate(i)
            case Name(n):
                return x86.Var(n)
            case _:
                raise Exception("select_instructions/atom_to_arg")

    def translate_expression(expression: expr) -> [x86.Instr]:

        def move_to_rax(exp: expr) -> x86.Instr:
            return x86.NamedInstr("movq",
                                  [atom_to_arg(exp), x86.Reg("rax")]
                                  )

        instructions = []
        match expression:
            case Call(Name(name), args):
                if name not in valid_calls.keys() or \
                        len(args) != valid_calls[name]['args']:
                    raise Exception("select_instructions/call_builtin")
                if len(args) == 1:
                    instructions.append(x86.NamedInstr("movq", [atom_to_arg(args[0]), x86.Reg("rdi")]))
                instructions.append(x86.Callq(valid_calls[name]["name"]))
                return instructions
            case UnaryOp(op, exp):
                match op:
                    case USub():
                        instructions = [
                            move_to_rax(exp),
                            x86.NamedInstr("negq",
                                           [x86.Reg("rax")]
                                           )
                        ]
            case BinOp(left, op, right):
                def bin_math(instr_name: str) -> [x86.Instr]:
                    return [
                        move_to_rax(left),
                        x86.NamedInstr(instr_name,
                                       [atom_to_arg(right), x86.Reg("rax")]
                                       )
                    ]
                match op:
                    case Add():
                        return bin_math("addq")
                    case Sub():
                        return bin_math("subq")
            case Constant(_) | Name(_):
                return [
                    move_to_rax(expression)
                ]

    def translate_statement(statement: stmt) -> [x86.Instr]:
        match statement:
            case Expr(exp):
                return translate_expression(exp)
            case Assign([Name(n)], exp):
                instructions = translate_expression(exp)
                instructions.append(
                    x86.NamedInstr("movq",
                                   [x86.Reg("rax"), atom_to_arg(Name(n))]
                                   )
                )
                return instructions
            case _:
                raise Exception("select_instructions/translate_statement")

    instructions = []
    for statement in prog.body:
        instructions.extend(translate_statement(statement))

    return x86.Program({
        "start": instructions
    })



##################################################
# assign-homes
##################################################

def assign_homes(program: x86.Program) -> Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocates a stack location for each
    variable in the program.
    :param program: An x86 program.
    :return: A Tuple. The first element is an x86 program (with no variable references).
    The second element is the number of bytes needed in stack locations.
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
    'remove complex opera*': rco,
    'select instructions': select_instructions,
    'assign homes': assign_homes,
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
