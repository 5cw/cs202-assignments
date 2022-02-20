import math
from ast import *

from typing import List, Set, Dict, Tuple, Optional, Union
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


def eval_partial(prog: Module) -> Module:
    vals = {}

    def eval_expr(exp: expr) -> expr:
        match exp:
            case Name(n):
                if n in vals.keys():
                    return vals[n]
                else:
                    return Name(n)
            case UnaryOp(USub(), e):
                e = eval_expr(e)
                match e:
                    case Constant(i):
                        return Constant(-i)
            case BinOp(e1, op, e2): #some algebraic manipulation must take place to separate constants and bring them along for the ride.
                def separate_binop(exp: expr) -> Tuple[Optional[expr], Optional[int], bool]:
                    match exp:
                        case BinOp(Constant(i), Add(), other) | BinOp(other, Add(), Constant(i)):
                            return other, i, True
                        case BinOp(Constant(i), Sub(), other):
                            return other, i, False
                        case BinOp(other, Sub(), Constant(i)):
                            return other, -i, True
                        case Constant(i):
                            return None, i, True
                        case _:
                            return exp, None, True
                    pass
                e1 = eval_expr(e1)
                e2 = eval_expr(e2)
                irr1, c1, pos1 = separate_binop(e1)
                irr2, c2, pos2 = separate_binop(e2)
                match op:
                    case Sub():
                        if c2:
                            c2 *= -1
                        if irr2:
                            pos2 = not pos2
                match c1, c2:
                    case int(i1), int(i2):
                        constant = Constant(i1 + i2)
                    case (int(i), None) | (None, int(i)):
                        constant = Constant(i)
                    case _:
                        return exp
                match irr1, irr2:
                    case None, None:
                        return constant
                    case (i, None) | (None, i):
                        pos = pos1 and pos2 #None will always be positive
                        return BinOp(constant, Add() if pos else Sub(), i)
                    case e1, e2:
                        first = Add() if pos1 else Sub()
                        second = Add() if pos1 == pos2 else Sub() #Subtract if e1 is positive and e2 is negative,
                                                                # or if e1 is negative and e2 is positive.
                                                                #(the two subtracts will cancel)
                        return BinOp(constant, first, BinOp(e1, second, e2))
            case Call(name, args):
                return Call(name, [eval_expr(arg) for arg in args])
        return exp

    def eval_stmt(statement: stmt) -> Optional[stmt]:
        match statement:
            case Expr(e):
                return Expr(eval_expr(e))
            case Assign([Name(n)], e):
                e = eval_expr(e)
                match e:
                    case Constant(_) | BinOp(Constant(_), _, _):
                        vals[n] = e
                        return None
                    case _:
                        return Assign([Name(n)], e)

    return Module(list(filter(lambda x: x is not None, [eval_stmt(statement) for statement in prog.body])))




    pass


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

    new_prog = Module([])
    for statement in prog.body:
        new_prog.body.extend(rco_stmt(statement))

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

    def translate_expression(expression: expr) -> list[x86.Instr]:

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
                    move_to_rax(left),
                    x86.NamedInstr(instr_name,
                                   [atom_to_arg(right), x86.Reg("rax")]
                                   )
                ]
            case Constant(_) | Name(_):
                return [
                    move_to_rax(expression)
                ]
            case _:
                raise Exception("select_instructions")

    def translate_statement(statement: stmt) -> list[x86.Instr]:
        match statement:
            case Expr(exp):
                return translate_expression(exp)
            case Assign([Name(n)], exp):
                instructions = translate_expression(exp)
                match instructions:
                    case [x86.NamedInstr("movq", [x86.Immediate(i), x86.Reg("rax")])]:
                        return [x86.NamedInstr("movq",
                                               [x86.Immediate(i), atom_to_arg(Name(n))]
                                               )
                                ]
                    case _:
                        instructions.append(
                            x86.NamedInstr("movq",
                                           [x86.Reg("rax"), atom_to_arg(Name(n))]
                                           )
                        )
                        return instructions
            case _:
                raise Exception("select_instructions/translate_statement")

    instructions: list[x86.Instr] = []
    for statement in prog.body:
        instructions.extend(translate_statement(statement))
    instructions.append(x86.Jmp("conclusion"))

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
    vars = {
        "(num_vars)": 0
    }

    def replace_var(var: x86.Arg) -> x86.Arg:
        match var:
            case x86.Var(name):
                if name not in vars.keys():
                    vars["(num_vars)"] += 1
                    vars[name] = vars["(num_vars)"] * -8
                return x86.Deref("rbp", vars[name])
            case _:
                return var

    def replace_instr(instruction: x86.Instr) -> x86.Instr:
        match instruction:
            case x86.NamedInstr(name, args):
                return x86.NamedInstr(name, [replace_var(arg) for arg in args])
            case _:
                return instruction

    new_instructions = []
    match program:
        case x86.Program({"start": instructions}):
            for instruction in instructions:
                new_instructions.append(replace_instr(instruction))

    def calc_stack(num_vars: int) -> int:
        return (num_vars if num_vars % 2 == 0 else num_vars + 1) * 8

    return x86.Program({
        "start": new_instructions
    }), calc_stack(vars["(num_vars)"])


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
            case x86.NamedInstr(name, [x86.Deref("rbp", off1), x86.Deref("rbp", off2)]):
                return [
                    x86.NamedInstr("movq", [x86.Deref("rbp", off1), x86.Reg("rax")]),
                    x86.NamedInstr(name, [x86.Reg("rax"), x86.Deref("rbp", off2)])
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
                raise Exception("print_x86/print_program")

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
                raise Exception("print_x86/print_instruction")

    def print_arg(arg: x86.Arg) -> str:
        match arg:
            case x86.Immediate(i):
                return f"${i}"
            case x86.Reg(name):
                return f"%{name}"
            case x86.Deref(name, off):
                return f"{off}(%{name})"
            case _:
                raise Exception("print_x86/print_arg")

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
        case x86.Program({"start": body}):
            program = x86.Program({
                "main": main,
                "start": body,
                "conclusion": conclusion
            })

    return ".globl main\n" + print_program(program)


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'partial reduce': eval_partial,
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
