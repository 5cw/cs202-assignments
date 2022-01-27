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
    head = """    .globl main
main:
    pushq %rbp
    movq %rsp, %rbp
    jmp start
"""
    foot = """conclusion:
    movq $0, %rax
    popq %rbp
    retq
"""
    def program_to(program: x86.Program) -> str:
        pass
    def instruction_to(instruction: x86.Instr)
    
    body = ""
    for block, instructions in program.blocks.items():
        body += f"{block}:\n"
        for instruction in instructions:
            match instruction:
                case x86.NamedInstr(name, registers):
                    body += f"    {name}"
                    for register in registers:
                        match register:
                            case x86.Immediate(n):
                                body += f" ${n}"
                            case x86.Reg(s):
                                body += f" %{s}"
                            case _:
                                raise PrintError(program)
                case x86.Callq(label):
                    body += f"    callq {label}"
                case x86.Jmp(label):
                    body += f"    jmp {label}"
                case _:
                    raise PrintError(program)
            body += "\n"

    return head + body + foot


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
