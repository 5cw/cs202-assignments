import os
from ast import *
from typing import List, Set, Dict, Tuple
import sys

from cs202_support.base_ast import print_ast

import cs202_support.x86exp as x86


##################################################
# select-instructions
##################################################

class SelectionError(Exception):
    pass

class PrintError(Exception):
    pass

def select_instructions(program: Module) -> x86.Program:
    """
    Transforms a Lmin program into a pseudo-x86 assembly program.
    :param program: a Lmin program
    :return: a pseudo-x86 program
    """
    match program:
        case Module(
            [
                Expr(
                    Call(
                        Name("print", Load()),
                    [
                        Constant(
                            n, None
                        )
                    ], []))
            ]):
            p = x86.Program({
                'start':
                [
                    x86.NamedInstr(
                        "movq",
                        [
                            x86.Immediate(n),
                            x86.Reg("rdi")
                        ]
                    ),
                    x86.Callq("print_int"),
                    x86.Jmp("conclusion")
                ]
            })
            return p
        case _:
            raise SelectionError(program)




##################################################
# print-x86
##################################################

def print_x86(program: x86.Program) -> str:
    """
    Prints an x86 program to a string.
    :param program: An x86 program.
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
                raise PrintError(program)

    def print_instruction(instruction: x86.Instr) -> str:
        match instruction:
            case x86.NamedInstr(name, args):
                args_str = ", ".join([print_arg(arg) for arg in args])
                return f"{name} {args_str}"
            case x86.Callq(label):
                return f"callq {label}"
            case x86.Jmp(label):
                return f"jmp {label}"
            case x86.Retq():
                return "retq"
            case _:
                raise PrintError(instruction)

    def print_arg(arg: x86.Arg) -> str:
        match arg:
            case x86.Immediate(i):
                return f"${i}"
            case x86.Reg(name):
                return f"%{name}"

    globl = "    .globl main\n"
    program.blocks["main"] = [
        x86.NamedInstr("pushq", [x86.Reg("rbp")]),
        x86.NamedInstr("movq", [x86.Reg("rsp"), x86.Reg("rbp")]),
        x86.Jmp("start")
    ]
    program.blocks["conclusion"] = [
        x86.NamedInstr("movq", [x86.Immediate(0), x86.Reg("rax")]),
        x86.NamedInstr("popq", [x86.Reg("rbp")]),
        x86.Retq()
    ]

    return globl + print_program(program)


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'select instructions': select_instructions,
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
    print(os.getcwd())
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                input_program = f.read()
                x86_program = run_compiler(input_program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except Exception as e:
                raise Exception('Error during compilation:', e)
