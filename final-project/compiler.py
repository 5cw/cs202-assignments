import ast
import random
import types
from ast import *

from dataclasses import dataclass
from collections import OrderedDict, defaultdict
from functools import reduce
from typing import List, Set, Dict, Tuple as TupleType, DefaultDict, get_args, get_origin, TypeVar, NewType, Optional
import itertools
import sys
import traceback

from cs202_support.base_ast import AST, print_ast

import cs202_support.x86exp as x86
import cstr
import constants

import sys

argument_registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]

TUPLE_REG = x86.Reg("r11")
STR_REG = x86.Reg("r12")
TOP_OF_STACK = x86.Reg("r15")
MAX_ELEMENTS = 50
MEMORY_SIZE = 16384

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
    _fields = ['stmts', 'exp']
    __match_args__ = tuple(_fields)

    def __init__(self, stmts, exp):
        self.stmts = stmts
        self.exp = exp


# An "allocate expression" for Python
# allocates memory for Tuples
class Allocate(expr):
    _fields = ['num_bytes', 'tuple_type']
    __match_args__ = tuple(_fields)

    def __init__(self, num_bytes, tuple_type):
        self.num_bytes = num_bytes
        self.tuple_type = tuple_type


# A "global value expression" for Python
# references global values used by the compiler
class GlobalValue(expr):
    _fields = ['name']
    __match_args__ = tuple(_fields)

    def __init__(self, name):
        self.name = name


# A "collect statement" for Python
# runs the garbage collector
class Collect(expr):
    _fields = ['num_bytes']
    __match_args__ = tuple(_fields)

    def __init__(self, num_bytes):
        self.num_bytes = num_bytes


class CompileError(Exception):
    def __init__(self, ast):
        super().__init__(f"Unexpected token: {print_ast(ast)}")


class TypeCheckError(Exception):
    pass


class UnassignedVariable:
    pass


# Assigns e the type t and returns e
def with_type(t, e):
    e.has_type = t
    return e


##################################################
# typecheck
##################################################

TEnv = Dict[str, type]


def typecheck(program: Module) -> Module:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param e: The Lstr program to typecheck
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
        'print': [int | bool | str],
        # the function is called "print_int" but the online compiler lets you print True
        'ord': [str],
        'chr': [int],
        'len': [str | tuple],
        # 'input_int': [],
    }

    builtin_output_types = {
        'print': None,
        'ord': int,
        'chr': str,
        'len': int
        # 'input_int': int
    }

    valid_constant_types = (int, str, bool)

    def print_indices(exp: expr) -> str:
        match exp:
            case Subscript(item, Constant(index)):
                return print_indices(item) + f"[{index}]"
            case Name(name):
                return name
            case Tuple(vals):
                return str(tuple(vals))

    def tc_expr(exp: expr, env: TEnv) -> type:
        exp.has_type = tc_expr_(exp, env)
        return exp.has_type

    def tc_expr_(exp: expr, env: TEnv) -> type:
        match exp:
            case Constant(val):
                t = type(val)
                if t and t not in valid_constant_types:
                    raise TypeCheckError(f'Unexpected type "{t}".')
                if t == str:
                    if not val.isascii():
                        raise TypeCheckError(f'Please use only ASCII characters.')
                return t

            case Name(id):
                return env.get(id) or UnassignedVariable

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
                arg_types = [get_origin(arg) or arg for arg in arg_types]
                if name == "print":
                    if not issubclass(arg_types[0], builtin_arg_types[name][0]):
                        raise TypeCheckError(f'Can only print int, str, or bool.')
                    else:
                        types = [Constant(arg) for arg in arg_types]
                        for t in types:
                            t.has_type = type
                        args.extend(types)
                elif name == "len":
                    if not issubclass(arg_types[0], builtin_arg_types[name][0]):
                        raise TypeCheckError(f'Can only check length of tuples and strings.')
                elif arg_types != builtin_arg_types[name]:
                        raise TypeCheckError(f'Cannot call "{name}" on type(s) {arg_types}.\n'
                                             f'That call requires type(s) {builtin_arg_types[name]}.')

                return builtin_output_types[name]


            case Tuple(elements):
                if len(elements) > MAX_ELEMENTS:
                    raise TypeCheckError(f'Tuple cannot have more than {MAX_ELEMENTS} elements.')
                exp.has_type = tuple[tuple(tc_expr(e, env) for e in elements)]
                return exp.has_type

            case Subscript(item, ss):
                item_tc = tc_expr(item, env)
                item_type = get_origin(item_tc)
                item_args = get_args(item_tc)
                ss_tc = tc_expr(ss, env)
                if ss_tc != int:
                    raise TypeCheckError(f'Cannot subscript with non-int value {ss}.')

                if item_type == tuple:
                    item_len = len(item_args)
                    match ss:
                        case Constant(int(index)):
                            pass
                        case _:
                            raise TypeCheckError(f'Cannot subscript tuple with non-constant.')
                    out = item_args[ss]
                elif item_tc == str:
                    return str
                else:
                    raise TypeCheckError(f'Cannot subscript type {item_type}.')
                if index < 0 or index >= item_len:
                    raise TypeCheckError(f"Index out of bounds for {print_indices(item)}: {index}.")
                return out
            case _:
                raise CompileError(exp)

    def tc_stmt(statement: stmt, env):
        match statement:
            case Assign([lhs], value):
                lhs_type = tc_expr(lhs, env)
                val_type = tc_expr(value, env)
                if val_type is None:
                    raise TypeCheckError(
                        f'Cannot assign "{print_indices(lhs)}" to an operation which doesn\'t return anything')

                if lhs_type == UnassignedVariable:
                    match lhs:
                        case Name(name):
                            env[name] = val_type
                            lhs.has_type = val_type
                        case _:
                            CompileError(lhs)
                elif lhs_type != val_type:
                    raise TypeCheckError(f'Variable "{print_indices(lhs)}" cannot be assigned type {val_type}, '
                                         f'it\'s already type {lhs_type}')

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
                    raise TypeCheckError(f'You have an unused expression of type "{exp_type}".')
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
        has_type = exp.has_type
        match exp:
            case Constant(str(_)):
                pass
            case Constant(_) | Name(_):
                return exp
            case _:
                exp = rco_expr_(exp, temps)
        if not top:
            tmp = gensym("(tmp)")  # use parentheses because they are not allowed in normal variable names.
            exp.has_type = has_type
            temps[tmp] = exp
            exp = Name(tmp)
        exp.has_type = has_type
        return exp

    def rco_expr_(exp: expr, temps: dict[str, expr]) -> expr:
        match exp:
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
            case Tuple(elements):
                exp = Tuple([rco_expr(e, False, temps) for e in elements])
            case Subscript(item, index):
                exp = Subscript(rco_expr(item, False, temps), rco_expr(index, False, temps))
            case _:
                raise CompileError(exp)

        return exp

    def rco_stmt(statement: stmt) -> list[stmt]:

        def temps_to_stmts(temps: dict[str, expr]) -> list[stmt]:
            new_stmts = []
            for temp, value in temps.items():
                name = Name(temp)
                name.has_type = value.has_type
                new_stmts.append(Assign([name], value))
            return new_stmts

        temps = {}
        match statement:
            case Expr(exp):
                new_stmt = Expr(rco_expr(exp, True, temps))
            case Assign([var], exp):
                exp_can_operate = True
                match var, exp:
                    case Subscript(_, _), s:
                        if isinstance(s, Subscript) or s.has_type == str:
                            exp_can_operate = False
                new_stmt = Assign([rco_expr(var, True, temps)], rco_expr(exp, exp_can_operate, temps))
            case If(condition, if_true, if_false):
                new_true = []
                new_false = []
                for s in if_true:
                    new_true.extend(rco_stmt(s))
                for s in if_false:
                    new_false.extend(rco_stmt(s))
                no_reduce = isinstance(condition, Compare)
                new_stmt = If(rco_expr(condition, no_reduce, temps), new_true, new_false)
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
# expose-allocation
##################################################

def expose_alloc(prog: Module) -> Module:
    """
    Exposes allocations in an Lstr program. Replaces Tuple(...) with explicit
    allocation.
    :param prog: An Lstr program
    :return: An Lstr program, without Tuple constructors
    """



    def ea_stmt(statement: stmt) -> [stmt]:
        def find_name(lhs):
            match lhs:
                case Name(name):
                    return name
                case Subscript(l, _):
                    return find_name(l)

        match statement:
            case Assign([lhs], exp):
                end = []
                match exp:
                    case Tuple(elements):
                        exp_type = exp.has_type
                        exp_bytes = (len(elements) + 1) * 8
                        for index, element in enumerate(elements):
                            e = Subscript(lhs, Constant(index))
                            e.has_type = get_args(exp_type)[index]
                            end.append(Assign([e], element))
                    case Constant(str(s)):
                        exp_bytes = (len(s) + 1 + 8)  # 1 null character, 8 tag bytes
                        if exp_bytes % 8 != 0:
                            exp_bytes += 8 - (exp_bytes % 8)  # align to boundary
                        exp_type = str
                        end = [statement]
                    case Subscript(sub, _) if sub.has_type == str:
                        exp_bytes = 16
                        exp_type = str
                        end = [statement]
                    case Call(Name("chr"), _):
                        exp_bytes = 16
                        exp_type = str
                        end = [statement]
                    case _:
                        return [statement]
                temp_free_ptr = gensym("(alloc)")
                return [
                           Assign([Name(temp_free_ptr)],
                                  BinOp(GlobalValue("free_ptr"), Add(), Constant(exp_bytes))),
                           If(
                               Compare(Name(temp_free_ptr), [Lt()],
                                       [GlobalValue("fromspace_end")]),
                               [],
                               [Collect(exp_bytes)]),
                           Assign([lhs], Allocate(exp_bytes, exp_type))
                       ] + end
            case If(condition, if_true, if_false):
                return [If(
                    condition,
                    ea_stmts(if_true),
                    ea_stmts(if_false)
                )]
            case While(Begin(begin, condition), body, []):
                return [While(
                    Begin(
                        ea_stmts(begin),
                        condition
                    ),
                    ea_stmts(body),
                    []
                )]
            case _:
                return [statement]

    def ea_stmts(statements: [stmt]) -> [stmt]:
        return reduce(lambda x, y: x + y, [ea_stmt(statement) for statement in statements]) if statements else []

    return Module(
        ea_stmts(prog.body)
    )


##################################################
# explicate-control
##################################################

def explicate_control(prog: Module) -> cstr.CProgram:
    """
    Transforms an Lstr Expression into a Ctup program.
    :param e: An Lstr Expression
    :return: A Cstr Program
    """

    # the basic blocks of the program
    basic_blocks: Dict[str, List[cstr.Stmt]] = {}
    data: list[str] = []

    def add_stmt(label: str, s: cstr.Stmt):
        if label not in basic_blocks:
            basic_blocks[label] = []
        basic_blocks[label].append(s)

    builtin_cif_instructions = {
        'print': cstr.Print,
        'ord': cstr.Ord,
        'chr': cstr.Chr,
        'len': cstr.Len
    }

    def explicate_atm(exp: expr) -> cstr.Atm:
        match exp:
            case Name(name):
                return cstr.Name(name)
            case Constant(val):
                match val:
                    case int(i):
                        return cstr.ConstantInt(i)
                    case bool(b):
                        return cstr.ConstantBool(b)
                    case str(s):
                        index = len(data)
                        data.append(s)
                        return cstr.StringIndex(index)
                    case t:
                        return t

            case GlobalValue(name):
                return cstr.GlobalValue(name)
            case Subscript(sub_of, index):
                match sub_of:
                    case Name(item):
                        pass
                    case _:
                        raise CompileError(sub_of)
                t = get_origin(sub_of.has_type)
                if t == tuple:
                    match index:
                        case Constant(i):
                            pass
                        case _:
                            raise CompileError(index)
                    return cstr.Subscript(item, i)
                elif sub_of.has_type == str:
                    return cstr.CharAt(item, explicate_atm(index))
                else:
                    raise CompileError(sub_of.has_type)
            case _:
                raise CompileError(exp)

    def explicate_expr(exp: expr) -> cstr.Exp:
        match exp:
            case Allocate(num_bytes, tuple_type):
                return cstr.Allocate(num_bytes, tuple_type)
            case UnaryOp(op, operand):
                return cstr.UnaryOp(op, explicate_expr(operand))
            case BinOp(left, op, right) | BoolOp(op, [left, right]):
                return cstr.BinOp(explicate_expr(left), op, explicate_expr(right))
            case Compare(left, [op], [right]):
                return cstr.Compare(explicate_expr(left), op, explicate_expr(right))
            case Call(Name(name), args):
                call = builtin_cif_instructions[name](*[explicate_atm(arg) for arg in args])
                return call
            case _:
                return cstr.AtmExp(explicate_atm(exp))

    def explicate_stmt(statement: stmt, blocks: Dict[str, List[cstr.Stmt]], current: str) -> str:
        new_current = current
        match statement:
            case Expr(Call(Name(name), args)):
                call = builtin_cif_instructions[name](*[explicate_expr(arg) for arg in args])
                add_stmt(current, call)
            case Assign([var], exp):
                lhs = explicate_atm(var)
                match exp:
                    case Constant(str(s)):
                        add_stmt(current, cstr.AssignString(lhs, explicate_atm(exp)))
                    case _:
                        add_stmt(current, cstr.Assign(lhs, explicate_expr(exp)))
            case Collect(num_bytes):
                add_stmt(current, cstr.Collect(num_bytes))
            case If(condition, if_true, if_false):
                match condition:
                    case Constant(_) | Name(_):
                        condition = cstr.Compare(explicate_expr(condition), Eq(),
                                                 cstr.AtmExp(cstr.ConstantBool(True)))
                    case Compare(left, [op], [right]):
                        condition = cstr.Compare(explicate_expr(left), op, explicate_expr(right))
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
                add_stmt(current, cstr.If(condition, cstr.Goto(true_label), cstr.Goto(false_label)))
            case While(begin, body, []):
                match begin:
                    case Begin(begin_stmts, condition):
                        pass
                    case _:
                        raise CompileError(begin)
                match condition:
                    case Constant(_) | Name(_):
                        condition = cstr.Compare(explicate_expr(condition), Eq(),
                                                 cstr.AtmExp(cstr.ConstantBool(True)))
                    case Compare(left, [op], [right]):
                        condition = cstr.Compare(explicate_expr(left), op, explicate_expr(right))
                    case _:
                        raise CompileError(condition)
                begin_label = gensym("label")
                check_label = gensym("label")
                body_label = gensym("label")
                new_current = gensym("label")
                add_stmt(current, cstr.Goto(begin_label))
                explicate_block(begin_stmts, blocks, begin_label, check_label)
                add_stmt(check_label, cstr.If(condition, cstr.Goto(body_label), cstr.Goto(new_current)))
                explicate_block(body, blocks, body_label, begin_label)
            case _:
                raise CompileError(statement)
        return new_current

    def explicate_block(statements: [stmt], blocks, start, end):
        current_label = start
        for statement in statements:
            current_label = explicate_stmt(statement, blocks, current_label)
        add_stmt(current_label, cstr.Goto(end))

    explicate_block(prog.body, basic_blocks, "start", "conclusion")

    return cstr.CProgram(basic_blocks, data)


##################################################
# select-instructions
##################################################

def select_instructions(p: cstr.CProgram) -> x86.Program:
    """
    Transforms a Cstr program into a pseudo-x86 assembly program.
    :param p: a Cstr program
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
        'Add': 'addq',
        'Sub': 'subq',
        'Mult': 'imulq',
        'And': 'andq',
        'Or': 'orq',
    }

    type_of = {

    }

    panic = False

    def si_atm(atm: cstr.Atm, dest=None) -> x86.Arg:

        match atm:
            case cstr.Name(name):
                t = type_of.get(name)
                if get_origin(t) == tuple or t == str:
                    out = x86.VecVar(name)
                else:
                    out = x86.Var(name)
            case cstr.ConstantInt(i):
                out = x86.Immediate(i)
                t = int
            case cstr.ConstantBool(i):
                out = x86.Immediate(int(i))
                t = bool
            case cstr.GlobalValue(name):
                out = x86.GlobalVal(name)
                t = x86.GlobalVal
            case _:
                raise CompileError(atm)
        match dest:
            case x86.Var(var):
                if var not in type_of.keys():
                    type_of[var] = t
        return out

    def si_exp(exp: cstr.Exp, dest: x86.Arg) -> [x86.Instr]:

        def move_to_var(atm):
            return x86.NamedInstr("movq", [si_atm(atm, dest), dest])

        match exp:
            case cstr.AtmExp(cstr.Subscript(name, index)):
                match dest:
                    case x86.Var(var):
                        type_of[var] = get_args(type_of[name])[index]
                        if get_origin(type_of[var]) == tuple or type_of[var] == str:
                            dest = x86.VecVar(var)
                    case _:
                        raise CompileError(dest)

                return [x86.NamedInstr("movq", [x86.VecVar(name), TUPLE_REG]),
                        x86.NamedInstr("movq", [x86.Deref(TUPLE_REG.val, ((index + 1) * 8)), dest])]
            case cstr.AtmExp(cstr.CharAt(name, index)):
                match dest:
                    case x86.Var(var):
                        type_of[var] = str
                        dest = x86.VecVar(var)
                    case _:
                        raise CompileError(dest)
                return [
                            x86.NamedInstr("movq", [dest, x86.Reg(argument_registers[0])]),
                            x86.NamedInstr("movq", [x86.VecVar(name), x86.Reg(argument_registers[1])]),
                            x86.NamedInstr("movq", [si_atm(index), x86.Reg(argument_registers[2])]),
                            x86.Callq("take_char"),
                            x86.NamedInstr("cmpq", [x86.Immediate(0), x86.Reg("rax")]),
                            x86.JmpIf("z", "conclusion")
                        ]
            case cstr.AtmExp(atm):
                return [move_to_var(atm)]
            case cstr.UnaryOp(op, cstr.AtmExp(atm)):
                match op:
                    case USub():
                        return [move_to_var(atm),
                                x86.NamedInstr("negq", [dest])]
                    case Not():
                        return [move_to_var(atm),
                                x86.NamedInstr("xorq", [x86.Immediate(1), dest])]
            case cstr.BinOp(cstr.AtmExp(atm1), op, cstr.AtmExp(atm2)):
                return [move_to_var(atm1),
                        x86.NamedInstr(binop_instrs[name_of(op)], [si_atm(atm2), dest])]
            case cstr.Compare(cstr.AtmExp(atm1), op, cstr.AtmExp(atm2)):
                return [x86.NamedInstr("cmpq", [si_atm(atm2), si_atm(atm1)]),
                        x86.Set(op_cc[name_of(op)], x86.ByteReg("al")),
                        x86.NamedInstr("movzbq", [x86.ByteReg("al"), dest])]
            case cstr.Ord(ord_of):
                match dest:
                    case x86.Var(var):
                        type_of[var] = int
                    case _:
                        raise CompileError(dest)
                match ord_of:
                    case cstr.StringIndex(index):
                        first = [x86.NamedInstr("leaq", [x86.GlobalVal(f"LC{index}"), STR_REG])]
                    case _:
                        first = [x86.NamedInstr("movq", [si_atm(ord_of), STR_REG]),
                                 x86.NamedInstr("addq", [x86.Immediate(8), STR_REG])]
                return first + [
                    x86.NamedInstr("movq", [x86.Deref(STR_REG.val, 0), x86.Reg("rax")]),
                    x86.NamedInstr("movzbq", [x86.ByteReg("al"), dest])
                ]

            case cstr.Chr(chr_of):
                match dest:
                    case x86.Var(var):
                        type_of[var] = str
                        dest = x86.VecVar(var)
                    case _:
                        raise CompileError(dest)
                return [x86.NamedInstr("movq", [dest, STR_REG]),
                        x86.NamedInstr("movq", [si_atm(chr_of), x86.Reg("rax")]),
                        x86.NamedInstr("movb", [x86.ByteReg("al"), x86.Deref(STR_REG.val, 8)]),
                        x86.NamedInstr("movb", [x86.Immediate(0), x86.Deref(STR_REG.val, 9)])]
            case cstr.Len(len_of):
                match dest:
                    case x86.Var(var):
                        type_of[var] = int
                match len_of:
                    case cstr.StringIndex(index):
                        return [x86.NamedInstr("movq", [x86.Immediate(len(p.data[index])), dest])]
                    case _:
                        return [x86.NamedInstr("movq", [si_atm(len_of), x86.Reg(argument_registers[0])]),
                                x86.NamedInstr("addq", [x86.Immediate(8), x86.Reg(argument_registers[0])]),
                                x86.Callq("strlen"),
                                x86.NamedInstr("movq", [x86.Reg("rax"), dest])]

            case cstr.Allocate(num_bytes, tuple_type):
                match dest:
                    case x86.Var(var):
                        dest = x86.VecVar(var)
                        type_of[var] = tuple_type
                    case _:
                        raise CompileError(dest)

                def tag_from(tt: type):
                    pointer_mask = 0
                    vector_length = (num_bytes // 8) - 1
                    if get_origin(tt) == tuple:
                        types = get_args(tt)
                        for t in types:
                            if get_origin(t) == tuple:
                                pointer_mask += 1
                            pointer_mask = pointer_mask << 1
                    return (pointer_mask << 6) + (vector_length << 1) + 1

                return [x86.NamedInstr("movq", [x86.GlobalVal("free_ptr"), dest]),
                        x86.NamedInstr("addq", [x86.Immediate(num_bytes), x86.GlobalVal("free_ptr")]),
                        x86.NamedInstr("movq", [dest, TUPLE_REG]),
                        x86.NamedInstr("movq", [x86.Immediate(tag_from(tuple_type)), x86.Deref(TUPLE_REG.val, 0)])]

    def si_stmt(statement: cstr.Stmt) -> [x86.Instr]:
        match statement:
            case cstr.Assign(lhs, exp):
                match lhs:
                    case cstr.Subscript(name, index):
                        return [
                                   x86.NamedInstr("movq", [x86.VecVar(name), TUPLE_REG])
                               ] + si_exp(exp, x86.Deref(TUPLE_REG.val, ((index + 1) * 8)))
                    case cstr.CharAt(lhs_name, index):
                        match exp:
                            case cstr.AtmExp(cstr.Name(exp_name)):
                                pass
                            case _:
                                raise CompileError(exp)
                        return [
                            x86.NamedInstr("movq", [x86.VecVar(lhs_name), x86.Reg(argument_registers[0])]),
                            x86.NamedInstr("movq", [x86.VecVar(exp_name), x86.Reg(argument_registers[1])]),
                            x86.NamedInstr("movq", [si_atm(index), x86.Reg(argument_registers[2])]),
                            x86.Callq("put_char"),
                            x86.NamedInstr("cmpq", [x86.Immediate(0), x86.Reg("rax")]),
                            x86.JmpIf("z", "conclusion")
                        ]

                    case cstr.Name(var):
                        return si_exp(exp, x86.Var(var))
            case cstr.AssignString(name, cstr.StringIndex(index)):
                return [x86.NamedInstr("movq", [x86.VecVar(name.var), x86.Reg("rdi")]),
                        x86.NamedInstr("addq", [x86.Immediate(8), x86.Reg("rdi")]),
                        x86.NamedInstr("leaq", [x86.GlobalVal(f"LC{index}"), x86.Reg("rsi")]),
                        x86.NamedInstr("movq", [x86.Immediate(len(p.data[index]) + 1), x86.Reg("rcx")]),
                        x86.NamedInstr("cld", []),
                        x86.Rep(x86.NamedInstr("movsb", []))
                        ]
            case cstr.If(cstr.Compare(cstr.AtmExp(atm1), op, cstr.AtmExp(atm2)),
                         cstr.Goto(true_label), cstr.Goto(false_label)):
                return [x86.NamedInstr("cmpq", [si_atm(atm2), si_atm(atm1)]),
                        x86.JmpIf(op_cc[name_of(op)], true_label),
                        x86.Jmp(false_label)]
            case cstr.Goto(label):
                return [x86.Jmp(label)]
            case cstr.Print(cstr.AtmExp(atm), cstr.AtmExp(print_type)):
                return [x86.NamedInstr("movq", [si_atm(atm), x86.Reg(argument_registers[0])]),
                        x86.Callq(f"print_{print_type.__name__}")]
            case cstr.Collect(num_bytes):
                return [x86.NamedInstr("movq", [TOP_OF_STACK, x86.Reg(argument_registers[0])]),
                        x86.NamedInstr("movq", [x86.Immediate(num_bytes), x86.Reg(argument_registers[1])]),
                        x86.Callq("collect")]
            case _:
                raise CompileError(statement)

    return x86.Program({
        label: reduce(
            lambda l1, l2: l1 + l2,
            [si_stmt(statement) for statement in block]
        ) for label, block in p.blocks.items()
    }, {
        f"LC{i}": s for i, s in enumerate(p.data)
    })


def reads_writes(instruction: x86.Instr) -> tuple[Set[x86.Var], Set[x86.Var]]:
    num_args = {
        "print_int": 1,
        "print_bool": 1,
        "print_str": 1,
        "strlen": 1,
        "take_char": 3,
        "put_char": 3,
        "collect": 2
    }
    match instruction:
        case x86.NamedInstr("movq" | "movb", [read, write]):
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
        case x86.Callq(name):
            reads, writes = set(x86.Reg(reg) for reg in argument_registers[:num_args[name]]), \
                            set(x86.Reg(reg) for reg in constants.caller_saved_registers)
        case x86.Rep(_):
            reads, writes = {x86.Reg("rdi"), x86.Reg("rsi"), x86.Reg("rcx")}, set()
        case _:
            reads, writes = set(), set()

    def is_valid(arg):
        match arg:
            case x86.Var(_) | x86.VecVar(_) | x86.Reg(_):
                return True
            case _:
                return False

    return {read for read in reads if is_valid(read)}, {write for write in writes if is_valid(write)}


graph_forward = {}
graph_backward = {}


##################################################
# uncover-live
##################################################

def uncover_live(program: x86.Program) -> TupleType[x86.Program, Dict[str, List[Set[x86.Var]]]]:
    """
    Performs liveness analysis. Returns the input program, plus live-after sets
    for its blocks.
    :param program: a pseudo-x86 assembly program
    :return: A tuple. The first element is the same as the input program. The
    second element is a dict of live-after sets. This dict maps each label in
    the program to a list of live-after sets for that label. The live-after
    sets are in the same order as the label's instructions.
    """

    blocks = program.blocks

    live_before_per_block = {}

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
            if from_label in live_before_per_block.keys():
                live_before_per_block[from_label].update(input.copy())
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
            input = live_before_per_block[current].copy()
            old = live_after_sets.copy()
            live_after_sets[current] = ul_block(blocks[current], current, input)
            if live_after_sets != old:
                worklist.extend(graph_backward[current])
        return live_after_sets

    match program:
        case x86.Program(blocks, data):
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


def build_interference(inputs: TupleType[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> \
        TupleType[x86.Program, InterferenceGraph]:
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
            case x86.NamedInstr("movq", [source, dest]):
                for live in live_after:
                    if live != source and live != dest:
                        graph.add_edge(dest, live)
            case _:
                collect = False
                match instruction:
                    case x86.Callq("collect"):
                        collect = True
                _, writes = reads_writes(instruction)
                for live in live_after:
                    if not isinstance(live, x86.Reg):
                        for write in writes:
                            if write != live:
                                graph.add_edge(write, live)
                        if collect:
                            for callee in constants.callee_saved_registers:
                                graph.add_edge(x86.Reg(callee), live)
                        for live2 in live_after:
                            if live != live2:
                                graph.add_edge(live, live2)

    def bi_block(instructions: [x86.Instr], live_after_sets: [Set[x86.Var]]):
        for instruction, live_after in zip(instructions, live_after_sets):
            bi_instr(instruction, live_after)

    match inputs:
        case x86.Program(blocks), live_dict:
            for key in blocks.keys():
                bi_block(blocks[key], live_dict[key])
            return inputs[0], graph


##################################################
# allocate-registers
##################################################

Color = int
Coloring = dict[x86.Var, Color]
Saturation = set[Color]
SatMap = dict[x86.Arg, Saturation]


def allocate_registers(inputs: TupleType[x86.Program, InterferenceGraph]) -> \
        TupleType[x86.Program, int, int]:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param inputs: A Tuple. The first element is the pseudo-x86 program. The
    second element is the completed interference graph.
    :return: A Tuple. The first element is an x86 program (with no variable
    references). The second element is the number of bytes needed in stack
    locations. The third element is the root stack space in bytes.
    """

    # Defines the set of registers to use
    register_locations = [x86.Reg(r) for r in
                          constants.caller_saved_registers + constants.callee_saved_registers]

    def ar_select(sat: SatMap) -> x86.Arg:
        max = 0
        possible = []
        for var, s in sat.items():
            if len(s) > max:
                possible = [var]
                max = len(s)
            elif len(s) == max:
                possible.append(var)
        return random.choice(possible)

    num_colors = 0
    prog, interference = inputs
    saturation_map = SatMap()
    coloring = Coloring()
    register_order = []
    for var in interference.graph.keys():
        match var:
            case x86.Reg(_):
                if var in register_locations:
                    color = num_colors
                    num_colors += 1
                    coloring[var] = color
                    register_order.append(var)
            case _:
                saturation_map[var] = Saturation()

    for live_reg in register_order:
        for neighbor in interference.neighbors(live_reg):
            if neighbor in saturation_map.keys():
                saturation_map[neighbor].add(coloring[live_reg])

    num_vec_colors = 0
    while len(saturation_map) > 0:
        var = ar_select(saturation_map)
        is_vec = isinstance(var, x86.VecVar)
        if is_vec and num_colors >= len(register_locations):
            possible_colors = set(range(len(register_locations))) - saturation_map[var]
        else:
            possible_colors = set(range(num_colors)) - saturation_map[var]
        if not possible_colors:
            if is_vec:
                num_vec_colors += 1
                color = -num_vec_colors  # use negative color for tuple type variables.
            else:
                color = num_colors
                num_colors += 1
        else:
            color = min(possible_colors)
        coloring[var] = color
        for neighbor in interference.neighbors(var):
            if neighbor in saturation_map:
                saturation_map[neighbor].add(color)
        del saturation_map[var]

    mapping: list[x86.Arg] = register_order.copy()
    mapping.extend([reg for reg in register_locations if reg not in register_order])
    if len(mapping) >= num_colors:
        stack_size = 0
    else:
        num_vars = num_colors - len(register_order)
        extension = [x86.Deref("rbp", -(8 * i)) for i in range(1, num_vars + 1)]
        stack_size = num_vars * 8
        stack_size = stack_size if stack_size % 16 == 0 else stack_size + 8
        mapping.extend(extension)

    vec_stack_size = (num_vec_colors * 8)

    if num_vec_colors > 0:
        extension = [x86.Deref(TOP_OF_STACK.val, -(8 * i)) for i in range(num_vec_colors)]
        mapping.extend(extension)  # negative indices in python access from end

    def ar_arg(arg: x86.Arg) -> x86.Arg:
        match arg:
            case x86.Var(name):
                if arg not in coloring.keys():
                    ret = mapping[0]
                else:
                    ret = mapping[coloring[arg]]
                return ret
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
    }, prog.data), stack_size, vec_stack_size


##################################################
# patch-instructions
##################################################

def patch_instructions(inputs: TupleType[x86.Program, int, int]) -> TupleType[x86.Program, int, int]:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param inputs: A Tuple. The first element is an x86 program. The second element is the
    stack space in bytes. The third element is the root stack space in bytes.
    :return: A Tuple. The first element is the patched x86 program. The second element is
    the stack space in bytes. The third element is the root stack space in bytes.
    """

    def patch_instruction(instruction: x86.Instr) -> [x86.Instr]:
        match instruction:
            case x86.NamedInstr("movq", [loc1, loc2]) if loc1 == loc2:
                return []
            case x86.NamedInstr(name, [loc1, loc2]) if isinstance(loc1, x86.Deref | x86.GlobalVal) and \
                                                       isinstance(loc2, x86.Deref | x86.GlobalVal):
                return [
                    x86.NamedInstr("movq", [loc1, x86.Reg("rax")]),
                    x86.NamedInstr(name, [x86.Reg("rax"), loc2])
                ]
            case x86.NamedInstr('movzbq', [loc, x86.Deref(reg, off)]):
                return [x86.NamedInstr('movzbq', [loc, x86.Reg('rax')]),
                        x86.NamedInstr('movq', [x86.Reg('rax'), x86.Deref(reg, off)])]
            case x86.NamedInstr("cmpq", [loc, x86.Immediate(i)]):
                return [
                    x86.NamedInstr("movq", [x86.Immediate(i), x86.Reg("rax")]),
                    x86.NamedInstr("cmpq", [loc, x86.Reg("rax")])
                ]
        return [instruction]

    def patch_block(block: [x86.Instr]):
        new_block = []
        for instruction in block:
            new_block.extend(patch_instruction(instruction))
        return new_block

    match inputs[0]:
        case x86.Program(blocks, data):
            pass
        case _:
            raise CompileError(inputs[0])

    def patch_blocks(blocks):
        empty_labels = {}
        label_joins = {}
        for label, block in blocks.items():
            match block[-1]:
                case x86.Jmp(next_label):
                    if len(block) == 1:
                        empty_labels[label] = next_label

            if len(graph_forward[label]) == 1:
                to_label = graph_forward[label][0]
                if len(graph_backward[to_label]) == 1:
                    label_joins[label] = to_label

        for label in empty_labels.keys():
            next_label = empty_labels[label]
            while next_label in empty_labels.keys():
                next_label = empty_labels[next_label]
            empty_labels[label] = next_label
            label_joins.pop(label, None)
            del blocks[label]

        for label in blocks.keys():
            match blocks[label][-1]:
                case x86.Jmp(next_label):
                    if next_label in empty_labels.keys():
                        blocks[label][-1] = x86.Jmp(empty_labels[next_label])
            match blocks[label][-2]:
                case x86.JmpIf(cc, next_label):
                    if next_label in empty_labels.keys():
                        blocks[label][-2] = x86.JmpIf(cc, empty_labels[next_label])
        for from_label, to_label in label_joins.items():
            if to_label in blocks.keys():
                while to_label is not None:
                    if to_label in empty_labels.keys():
                        to_label = empty_labels[to_label]
                    blocks[from_label] = blocks[from_label][:-1]
                    blocks[from_label].extend(blocks[to_label])
                    del blocks[to_label]
                    to_label = label_joins.get(to_label)

        return blocks

    blocks = {
        key: patch_block(block) for key, block in blocks.items() if block is not None
    }
    blocks = patch_blocks(blocks)

    return x86.Program(blocks, data), inputs[1], inputs[2]


##################################################
# print-x86
##################################################

def print_x86(inputs: TupleType[x86.Program, int, int]) -> str:
    """
    Prints an x86 program to a string.
    :param inputs: A Tuple. The first element is the x86 program. The second element
    is the stack space in bytes. The third element is the root stack space in bytes.
    :return: A string, ready for gcc.
    """

    def print_program(program: x86.Program) -> str:
        match program:
            case x86.Program(blocks, data):
                body = ""
                if data:
                    body += ".section .rodata\n"
                    for key, string in data.items():
                        body += f"{key}:\n"
                        body += f'    .asciz "{string}"\n'
                    body += ".text\n"
                body += ".globl main\n"
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
            case x86.Rep(instr):
                return f"rep {print_instruction(instr)}"
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
            case x86.GlobalVal(name):
                return f"{name}(%rip)"
            case _:
                raise CompileError(arg)

    program = None
    main = [
        x86.NamedInstr("pushq", [x86.Reg("rbp")]),
        x86.NamedInstr("movq", [x86.Reg("rsp"), x86.Reg("rbp")]),
        x86.NamedInstr("subq", [x86.Immediate(inputs[1]), x86.Reg("rsp")]),
        x86.NamedInstr("movq", [x86.Immediate(MEMORY_SIZE), x86.Reg(argument_registers[0])]),
        x86.NamedInstr("movq", [x86.Immediate(MEMORY_SIZE), x86.Reg(argument_registers[1])]),
        x86.Callq("initialize"),
        x86.NamedInstr("movq", [x86.GlobalVal("rootstack_begin"), TOP_OF_STACK])
    ]
    main.extend([
                    x86.NamedInstr("movq", [x86.Immediate(0), x86.Deref(TOP_OF_STACK.val, 0)]),
                    x86.NamedInstr("addq", [x86.Immediate(8), TOP_OF_STACK])
                ] * (inputs[2] // 8))
    main.append(x86.Jmp("start"))
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
        case x86.Program(blocks, data):
            new_blocks = {
                "main": main
            }
            new_blocks.update(blocks)
            new_blocks["conclusion"] = conclusion
            program = x86.Program(new_blocks, data)

    return print_program(program)


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'expose allocation': expose_alloc,
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
