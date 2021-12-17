# encoding: utf-8

from __future__ import annotations

import math
import functools
import itertools
import random

from typing import Type, TypeVar, Tuple, Set, Mapping, MutableMapping, Sequence, Generic, Callable, List, Union, Any, Iterator, Iterable

Clue = Tuple[int, int]
# Predicat head symbol, place
# place starts at 0

def raise_e(obj):
	raise obj

G = TypeVar("G", bound="Set")

def get_any(obj: Set[G]) -> G:

	for e in obj:
		return e

	return e # to appease the mypy gods

H = TypeVar("H")
J = TypeVar("J")

class EqDict(Generic[H, J]):

	def __init__(self, data: List[Tuple[H, J]] = None):

		if data	is None:
			self.data: List[Tuple[H, J]] = []

		else:
			self.data = data

	def __getitem__(self, key: H) -> J:

		for k, v in self.data:
			if k == key:
				return v

		raise KeyError

	def __setitem__(self, key: H, val: J):

		for i, (k, v) in enumerate(self.data):
			if k == key:
				self.data.pop(i)
				self.data.insert(i, (key, val))
				return

		self.data.append((key, val))

	def items(self) -> Iterator[Tuple[H, J]]:
		return (e for e in self.data)

class NotSpecified(Exception): pass

class TypeInfo:

	def __init__(self, clues: Set[Clue]):

		self.clues = clues

	def __or__(self, other: TypeInfo) -> TypeInfo:
		return TypeInfo(self.clues | other.clues)

	@property
	def elements(self) -> Set[Clue]:
		return self.clues

	def add(self, clue: Clue):
		self.clues.add(clue)

	def get_str(self, names: Names) -> str:
		return ", ".join(f"{names.get(phs)} {place}" for phs, place in self.clues)

	@classmethod
	def str_infos(self, names: Names, type_infos: Mapping[int, TypeInfo]) -> str:
		return "\n".join(f" {names.get(sym)} : {t.get_str(names)}" for sym, t in type_infos.items())

	@classmethod
	def str_power_infos(self, names: Names, power_infos: EqDict[Formulae, TypeInfo]) -> str:
		return "\n".join(f" {formulae.get_str(names)} : {t.get_str(names)}" for formulae, t in power_infos.items())

class Names:

	main: Names # only use in front end syntax sugar!

	def __init__(self, symbol_table: MutableMapping[int, str]):

		self.symbol_table = symbol_table
		Names.main = self

	@classmethod
	def new(cls) -> Names:
		return cls(symbol_table={})

	def sym(self, name: str) -> int:

		n = 0
		while (n := n + 1) in self.symbol_table:
			continue

		self.symbol_table[n] = name
		return n

	def get(self, n: int) -> str:

		try:
			return self.symbol_table[n]

		except KeyError:
			return f"?{n}"

	def get_l(self, l: Sequence[int]) -> Sequence[str]:
		return tuple(self.get(e) for e in l)

	def get_str(self) -> str:
		return str(self.symbol_table)

def paren_if(txt: str, v: bool) -> str:

	if v:
		return f"({txt})"

	else:
		return txt

class Formulae:

	level: float = 0
	
	def __eq__(self, other):
		return NotImplemented

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		raise NotSpecified(f"{type(self)} {self}")

	def get_str(self, names: Names) -> str:
		raise NotSpecified(f"{type(self)} {self}")

	def replaced(self, a: Formulae, b: Formulae) -> Formulae:
		"""

			returns formulae tree with sub formulae a replaced by sub forumulae b

		"""
		raise NotSpecified(f"{type(self)} {self}")

	def get_symbols(self) -> Set[int]:
		raise NotSpecified(f"{type(self)} {self}")

	def free_symbols(self) -> Set[int]:
		raise NotSpecified(f"{type(self)} {self}")

	def bound_symbols(self) -> Set[int]:
		raise NotSpecified(f"{type(self)} {self}")

	def __neg__(self) -> Not:
		return Not(self)

	def get_eval(self, context: Context) -> Any:
		raise NotSpecified(f"{type(self)} {self}")

	def get_power_infos(self) -> EqDict[Formulae, TypeInfo]:
		raise NotSpecified(f"{type(self)} {self}")

def merged(a: Mapping[int, TypeInfo], b: Mapping[int, TypeInfo]) -> MutableMapping[int, TypeInfo]:

	ans: MutableMapping[int, TypeInfo] = {}

	for type_infos in (a, b):

		for symbol, type_info in type_infos.items():

			try:
				ans[symbol] |= type_info

			except KeyError:
				ans[symbol] = type_info

	return ans

def merged_power(a: EqDict[Formulae, TypeInfo], b: EqDict[Formulae, TypeInfo]) -> EqDict[Formulae, TypeInfo]:

	ans: EqDict[Formulae, TypeInfo] = EqDict()

	for type_infos in (a, b):

		for formulae, type_info in type_infos.items():

			try:
				ans[formulae] |= type_info

			except KeyError:
				ans[formulae] = type_info

	return ans

def get_type_infos(l: Sequence[Formulae]) -> Mapping[int, TypeInfo]:
	
	ans: Mapping[int, TypeInfo] = {}

	for formulae in l:

		type_infos = formulae.get_type_infos()
		ans = merged(ans, type_infos)

	return ans

def get_power_infos(l: Sequence[Formulae]) -> EqDict[Formulae, TypeInfo]:

	ans: EqDict[Formulae, TypeInfo] = EqDict()

	for formulae in l:

		power_infos = formulae.get_power_infos()
		ans = merged_power(ans, power_infos)

	return ans

class Identifier(Formulae):

	level: float = 100

	def __init__(self, symbol: int):

		self.symbol = symbol

	def __call__(self, *tail: Union[Identifier, Predicat]):
		return Predicat(head=self, tail=tail)

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.symbol == other.symbol

	def free_symbols(self) -> Set[int]:
		return {self.symbol}

	def bound_symbols(self) -> Set[int]:
		return set()

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		return {}

	def get_power_infos(self) -> EqDict[Formulae, TypeInfo]:
		return EqDict()

	def get_str(self, names: Names) -> str:
		return names.get(self.symbol)

	def __hash__(self) -> int:
		return self.symbol

	def replaced(self, a: Formulae, b: Formulae) -> Formulae:

		if a == self:
			return b

		else:
			return self

	def get_symbols(self) -> Set[int]:
		return {self.symbol}

	def get_eval(self, context: Context) -> Any:
		return context.domain(self.symbol)

class Predicat(Formulae):

	level: float = 100

	def __init__(self, head: Identifier, tail: Sequence[Union[Identifier, Predicat]]):

		self.head = head
		self.tail = tail

	@property
	def arity(self) -> int:
		return len(self.tail)

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and\
		self.head == other.head and\
		self.arity == other.arity and\
		all(a == b for a, b in zip(self.tail, other.tail))

	def free_symbols(self) -> Set[int]:
		return functools.reduce(set.union, (e.free_symbols() for e in self.tail), set())

	def bound_symbols(self) -> Set[int]:
		return set()

	def get_type_infos(self) -> Mapping[int, TypeInfo]:

		ans: MutableMapping[int, TypeInfo] = {}
		
		for place, sub_formulae in enumerate(self.tail, 0):

			if isinstance(sub_formulae, Identifier):

				try:
					ans[sub_formulae.symbol].add((self.head.symbol, place))

				except KeyError:
					ans[sub_formulae.symbol] = TypeInfo({(self.head.symbol, place),})

			elif isinstance(sub_formulae, Predicat):
				ans = merged(ans, sub_formulae.get_type_infos())

			else:
				raise Exception(sub_formulae)

		return ans

	def get_power_infos(self) -> EqDict[Formulae, TypeInfo]:

		ans: EqDict[Formulae, TypeInfo] = EqDict()

		for place, sub_formulae in enumerate(self.tail, 0):

			if isinstance(sub_formulae, Identifier):

				try:
					ans[sub_formulae].add((self.head.symbol, place))

				except KeyError:
					ans[sub_formulae] = TypeInfo({(self.head.symbol, place),})

			elif isinstance(sub_formulae, Predicat):

				try:
					ans[sub_formulae].add((self.head.symbol, place))

				except KeyError:
					ans[sub_formulae] = TypeInfo({(self.head.symbol, place),})

				ans = merged_power(ans, sub_formulae.get_power_infos())

			else:
				raise Exception(sub_formulae)

		return ans

	def replaced(self, a: Formulae, b: Formulae) -> Formulae:

		if a == self:
			return b

		else:

			new_head = self.head.replaced(a, b)
			new_tail = []

			for e in (e.replaced(a, b) for e in self.tail):

				if isinstance(e, (Identifier, Predicat)):
					new_tail.append(e)

				else:
					raise Exception(f"Trying to replace predicat argument with non identifier and non predicat")

			if isinstance(new_head, Identifier):
				return Predicat(new_head, new_tail)

			else:
				raise Exception(f"Trying to replace predicat head with non identifer")

	def get_str(self, names: Names) -> str:
		return f"{self.head.get_str(names)}({', '.join(e.get_str(names) for e in self.tail)})"

	def get_symbols(self) -> Set[int]:
		return functools.reduce(set.union, (e.get_symbols() for e in self.tail))

	def get_eval(self, context: Context) -> Any:
		return self.head.get_eval(context)(*[ident.get_eval(context) for ident in self.tail])

class Unary(Formulae):

	level: float = 100

	def __init__(self, a: Formulae):

		self.a = a

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.a == other.a

	def free_symbols(self) -> Set[int]:
		return self.a.free_symbols()

	def bound_symbols(self) -> Set[int]:
		return self.a.bound_symbols()

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		return self.a.get_type_infos()

	def get_power_infos(self) -> EqDict[Formulae, TypeInfo]:
		return self.a.get_power_infos()

	def replaced(self, a: Formulae, b: Formulae) -> Formulae:

		if a == self:
			return b

		else:
			return self.__class__(self.a.replaced(a, b))

	def get_symbols(self) -> Set[int]:
		return self.a.get_symbols()

	def get_eval(self, context: Context) -> Any:
		return self.a.get_eval(context)

class Not(Unary):
	
	def get_str(self, names: Names) -> str:
		return f"¬{paren_if(self.a.get_str(names), self.a.level > self.level)}"

	def get_eval(self, context: Context) -> Any:
		return not bool(self.a.get_eval(context))

class QuantifierEval(Exception): pass

class Quantifier(Formulae):

	level: float = math.inf
	
	def __init__(self, bound_identifiers: Set[Identifier], formulae: Formulae):

		self.bound_identifiers = bound_identifiers
		self.formulae = formulae
		self.bound_identifiers_free_symbols = set()

		for e in self.bound_identifiers:
			self.bound_identifiers_free_symbols |= e.free_symbols()

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.bound_identifiers == other.bound_identifiers and self.formulae == other.formulae

	def free_symbols(self) -> Set[int]:
		return self.formulae.free_symbols() - self.bound_identifiers_free_symbols

	def bound_symbols(self) -> Set[int]:
		return {ident.symbol for ident in self.bound_identifiers}

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		return {k: v for k, v in self.formulae.get_type_infos().items() if not any(k == e.symbol for e in self.bound_identifiers)}

	def get_power_infos(self) -> EqDict[Formulae, TypeInfo]:
		return EqDict([(formulae, infos) for formulae, infos in self.formulae.get_power_infos().items() if not any(formulae == e for e in self.bound_identifiers)])

	def get_symbols(self) -> Set[int]:
		return self.formulae.get_symbols() # ignoring bound_identifiers since they will be either in formulae or useless

	def replaced(self, a: Formulae, b: Formulae) -> Formulae:

		if a == self:
			return b

		else:

			new_bound_identifiers = set()

			for e in (e.replaced(a, b) for e in self.bound_identifiers):

				if isinstance(e, Identifier):
					new_bound_identifiers.add(e)

				else:
					raise Exception(f"Trying to replace bound identifier by non identifier")

			return self.__class__(new_bound_identifiers, self.formulae.replaced(a, b))

	def get_eval(self, context: Context) -> Any:
		raise QuantifierEval

class ForAll(Quantifier):

	def get_str(self, names: Names) -> str:
		return f"∀{','.join(e.get_str(names) for e in self.bound_identifiers)}.{self.formulae.get_str(names)}"

class Exists(Quantifier):

	def get_str(self, names: Names) -> str:
		return f"∃{','.join(e.get_str(names) for e in self.bound_identifiers)}.{self.formulae.get_str(names)}"

class Binary(Formulae):

	level: float = 200

	def __init__(self, a: Formulae, b: Formulae):

		self.a = a
		self.b = b

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.a == other.a and self.b == other.b

	def free_symbols(self) -> Set[int]:
		return self.a.free_symbols() | self.b.free_symbols()

	def bound_symbols(self) -> Set[int]:
		return self.a.bound_symbols() | self.b.bound_symbols()

	def get_type_infos(self) -> Mapping[int, TypeInfo]:

		a: MutableMapping[int, TypeInfo] = {**self.a.get_type_infos()}
		b = self.b.get_type_infos()
		
		for symbol, t in b.items():

			try:
				a[symbol] |= t

			except KeyError:
				a[symbol] = t

		return a

	def get_power_infos(self) -> EqDict[Formulae, TypeInfo]:

		a: EqDict[Formulae, TypeInfo] = self.a.get_power_infos()
		b = self.b.get_power_infos()

		for formulae, t in b.items():

			try:
				a[formulae] |= t

			except KeyError:
				a[formulae] = t

		return a

	def replaced(self, a: Formulae, b: Formulae) -> Formulae:

		if a == self:
			return b

		else:
			return self.__class__(self.a.replaced(a, b), self.b.replaced(a, b))

	def get_symbols(self) -> Set[int]:
		return self.a.get_symbols() | self.b.get_symbols()

class And(Binary):
	
	def get_str(self, names: Names) -> str:
		return f"{paren_if(self.a.get_str(names), self.a.level > self.level)}∧{paren_if(self.b.get_str(names), self.b.level > self.level)}"

	def get_eval(self, context: Context) -> Any:
		return bool(self.a.get_eval(context)) and bool(self.b.get_eval(context))

class Or(Binary):
	
	def get_str(self, names: Names) -> str:
		return f"{paren_if(self.a.get_str(names), self.a.level > self.level)}∨{paren_if(self.b.get_str(names), self.b.level > self.level)}"

	def get_eval(self, context: Context) -> Any:
		return bool(self.a.get_eval(context)) or bool(self.b.get_eval(context))

class Imply(Binary):

	level: float = 300
	
	def get_str(self, names: Names) -> str:
		return f"{paren_if(self.a.get_str(names), self.a.level > self.level)}→{paren_if(self.b.get_str(names), self.b.level > self.level)}"

	def get_eval(self, context: Context) -> Any:
		return (not bool(self.a.get_eval(context))) or bool(self.b.get_eval(context))

class Sequent:

	def __init__(self, antesequent: Tuple[Formulae], consequent: Tuple[Formulae]):

		self.antesequent = antesequent
		self.consequent = consequent

	def get_str(self, names: Names) -> str:
		return f"{', '.join(e.get_str(names) for e in self.antesequent)} ⊢ {', '.join(e.get_str(names) for e in self.consequent)}"

	def get_symbols(self) -> Set[int]:

		a = functools.reduce(set.union, (e.get_symbols() for e in self.antesequent))
		b = functools.reduce(set.union, (e.get_symbols() for e in self.consequent))
		return a|b

class Context:

	def __init__(self, domain: Callable[[int], Any]):

		self.domain = domain

class ProofDone(Exception): pass

class Prover:

	def __init__(self,
		goal: Sequent,
		goal_stack: List[Sequent],
		unprovable: List[Sequent],
		type_infos: Mapping[int, TypeInfo],
		power_infos: EqDict[Formulae, TypeInfo],
	):

		self.goal = goal
		self.goal_stack = goal_stack
		self.unprovable = unprovable
		self.type_infos = type_infos
		self.power_infos = power_infos
		self.symbols = self.goal.get_symbols()

	@classmethod
	def new(cls, goal: Sequent) -> Prover:
		return Prover(
			goal=goal,
			goal_stack=[goal,],
			unprovable=[],
			type_infos=get_type_infos(goal.antesequent + goal.consequent),
			power_infos=get_power_infos(goal.antesequent + goal.consequent),
		)

	@property
	def proved(self) -> bool:
		return not self.goal_stack and not self.unprovable

	def get_debug(self, names: Names) -> str:

		goal_stack_txt = '\n - '.join(e.get_str(names) for e in self.goal_stack)
		unprovable_txt = '\n - '.join(e.get_str(names) for e in self.unprovable)
		return f"{self.goal.get_str(names)}:\ngoal stack:\n - {goal_stack_txt}\nunprovable:\n - {unprovable_txt}\nproved: {self.proved}"

	def prove(self):

		try:
			while True:
				self.next_step()

		except ProofDone:
			return self

	def next_step(self):

		try:
			sequent = self.goal_stack.pop()

		except IndexError:
			raise ProofDone

		if (not sequent.antesequent) and (not sequent.consequent):
			self.unprovable.append(sequent)
			return

		for antesequent in sequent.antesequent:
			for consequent in sequent.consequent:
				if antesequent == consequent:
					return

		for n in range(len(sequent.antesequent)):

			formulae = sequent.antesequent[n]
			gamma = tuple(sequent.antesequent[i] for i in range(len(sequent.antesequent)) if i != n)

			if type(formulae) is Imply:

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(gamma, (a,) + sequent.consequent))
				self.goal_stack.append(Sequent(gamma + (b,), sequent.consequent))
				return

			elif type(formulae) is Or:

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(gamma + (a,), sequent.consequent))
				self.goal_stack.append(Sequent(gamma + (b,), sequent.consequent))
				return

			elif type(formulae) is And:

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(gamma + (a, b), sequent.consequent))
				return

			elif type(formulae) is Not:

				a = formulae.a
				self.goal_stack.append(Sequent(gamma, sequent.consequent + (a,)))
				return

			elif type(formulae) is ForAll:

				new_formulae = formulae.formulae
				local_power_infos = new_formulae.get_power_infos()

				for bound_identifier in formulae.bound_identifiers:
					for target_formulae, infos in self.power_infos.items():
						if local_power_infos[bound_identifier].elements & self.power_infos[target_formulae].elements:
							
							if isinstance(target_formulae, Identifier):
								if target_formulae.symbol not in new_formulae.formulae.bound_symbols():
									break

							else:
								break

					else:
						continue

					new_formulae = new_formulae.replaced(bound_identifier, target_formulae)

				if new_formulae is formulae.formulae:
					continue

				self.goal_stack.append(Sequent(gamma + (new_formulae,), sequent.consequent))
				return

			elif type(formulae) is Exists:

				bound_syms: Set[int] = set()

				for bound_identifier in formulae.bound_identifiers:
					for bound_sym in bound_identifier.get_symbols():
						bound_syms.add(bound_sym)

				if not (bound_syms & functools.reduce(set.union, (e.free_symbols() for e in gamma + sequent.consequent))):
					self.goal_stack.append(Sequent(gamma + (formulae.formulae,), sequent.consequent))
					return

				continue

			elif type(formulae) is Predicat:
				continue

			else:
				raise Exception(formulae)

		for n in range(len(sequent.consequent)):

			formulae = sequent.consequent[n]
			delta = tuple(sequent.consequent[i] for i in range(len(sequent.consequent)) if i != n)

			if type(formulae) is Imply:

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(sequent.antesequent + (a,), delta + (b,)))
				return

			elif type(formulae) is Or:

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(sequent.antesequent, delta + (a, b)))
				return

			elif type(formulae) is And:

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(sequent.antesequent, delta + (a,)))
				self.goal_stack.append(Sequent(sequent.antesequent, delta + (b,)))
				return

			elif type(formulae) is Not:

				a = formulae.a
				self.goal_stack.append(Sequent(sequent.antesequent + (a,), delta))
				return

			elif type(formulae) is Exists:

				new_formulae = formulae.formulae
				local_power_infos = new_formulae.get_power_infos()

				for bound_identifier in formulae.bound_identifiers:
					for target_formulae, infos in self.power_infos.items():
						if local_power_infos[bound_identifier].elements & self.power_infos[target_formulae].elements:
							
							if isinstance(target_formulae, Identifier):
								if target_formulae.symbol not in new_formulae.formulae.bound_symbols():
									break

							else:
								break

					else:
						continue

					new_formulae = new_formulae.replaced(bound_identifier, target_formulae)

				if new_formulae is formulae.formulae:
					continue

				self.goal_stack.append(Sequent(sequent.antesequent, delta + (new_formulae,)))
				return

			elif type(formulae) is ForAll:

				bound_syms: Set[int] = set()

				for bound_identifier in formulae.bound_identifiers:
					for bound_sym in bound_identifier.get_symbols():
						bound_syms.add(bound_sym)

				if not (bound_syms & functools.reduce(set.union, (e.free_symbols() for e in delta + sequent.antesequent))):
					self.goal_stack.append(Sequent(sequent.antesequent, delta + (formulae.formulae,)))
					return

				continue

			elif type(formulae) is Predicat:
				continue

			else:
				raise Exception(formulae)

		self.unprovable.append(sequent)

T = TypeVar("T")

class Infix(Generic[T]):

	def __init__(self, function):

		self.function = function

	def __ror__(self, other):
		return Infix(lambda x, self=self, other=other: self.function(other, x))

	def __or__(self, other) -> T:
		return self.function(other)

	def __call__(self, value1, value2):
		return self.function(value1, value2)

def pred(head: Identifier, *tail: Identifier) -> Predicat:
	return Predicat(head, tail)

def v(name: str) -> Identifier:
	return Identifier(Names.main.sym(name))

lor: Infix[Or] = Infix(lambda a, b: Or(a, b))
land: Infix[And] = Infix(lambda a, b: And(a, b))
imply: Infix[Imply] = Infix(lambda a, b: Imply(a, b))

def no(a: Formulae) -> Not:
	return Not(a)

def forall(identifiers: Set[Identifier], formulae: Formulae) -> ForAll:
	return ForAll(identifiers, formulae)

def exists(identifiers: Set[Identifier], formulae: Formulae) -> Exists:
	return Exists(identifiers, formulae)

def main():

	names = Names.new()
	n = v("n")
	p = v("P")
	q = v("Q")
	a = v("a")
	i = v("i")
	print(names.get_str())

	print("=== Axioms ===")
	axioms = [
		forall({n}, p(n) |imply| q(n)),
		p(i(a)),
	]

	for axiom in axioms:
		print(" - " + axiom.get_str(names))
		print(f"free symbols: {', '.join(names.get_l(axiom.free_symbols()))}")
		print(f"bound symbols: {', '.join(names.get_l(axiom.bound_symbols()))}")

	print("/// Type infos:")
	print(TypeInfo.str_infos(names, get_type_infos(axioms)))
	print("///")
	print(TypeInfo.str_power_infos(names, get_power_infos(axioms)))

	print("=== Situation ===")
	situation = [
	]

	for e in situation:
		print(" - " + e.get_str(names))
		print(f"free symbols: {', '.join(names.get_l(e.free_symbols()))}")
		print(f"bound symbols: {', '.join(names.get_l(e.bound_symbols()))}")

	print("/// Type infos:")
	print(TypeInfo.str_infos(names, get_type_infos(situation)))
	print("///")
	print(TypeInfo.str_power_infos(names, get_power_infos(situation)))

	print("=== Question ===")
	question = q(i(a))

	domain_vals = {
		#eq.symbol: lambda a, b: a == b,
		#add.symbol: lambda a, b: a + b,
		#s.symbol: lambda n: n + 1,
		#zero.symbol: lambda: 0,
	}
	context = Context(
		domain=domain_vals.get,
	)

	print(question.get_str(names))
	#print(f"eval: {question.get_eval(context)}")
	print(f"free_symbols: {', '.join(names.get_l(question.free_symbols()))}")
	print(f"bound symbols: {', '.join(names.get_l(question.bound_symbols()))}")
	print("/// Type infos:")
	print(TypeInfo.str_infos(names, get_type_infos([question])))
	print("///")
	print(TypeInfo.str_power_infos(names, get_power_infos([question])))
	sequent = Sequent(tuple(axioms + situation), (question,))
	print("=== Proving ===")
	prover = Prover.new(sequent)
	prover.prove()
	print(prover.get_debug(names))

if __name__ == "__main__":
	main()
