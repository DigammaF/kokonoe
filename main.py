# encoding: utf-8

from __future__ import annotations

import math
import functools
import itertools

from typing import Type, TypeVar, Tuple, Set, Mapping, MutableMapping, Sequence, Generic, Callable, List

Clue = Tuple[int, int]
# Predicat head symbol, place
# place starts at 0

G = TypeVar("G", bound="Set")

def get_any(obj: Set[G]) -> G:

	for e in obj:
		return e

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
		return (self.get(e) for e in l)

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

	def replaced(self, a: int, b: int) -> Formulae:
		"""

			returns same formulae with a replaced by b

		"""
		raise NotSpecified(f"{type(self)} {self}")

	def get_symbols(self) -> Set[int]:
		raise NotSpecified(f"{type(self)} {self}")

	def free_symbols(self) -> Set[int]:
		raise NotSpecified(f"{type(self)} {self}")

	def __neg__(self) -> Not:
		return Not(self)

def get_type_infos(l: Sequence[Formulae]) -> Mapping[int, TypeInfo]:
	
	ans: MutableMapping[int, TypeInfo] = {}

	for formulae in l:

		type_infos = formulae.get_type_infos()

		for symbol, type_info in type_infos.items():

			try:
				ans[symbol] |= type_info

			except KeyError:
				ans[symbol] = type_info

	return ans

class Identifier(Formulae):

	level: float = 100

	def __init__(self, symbol: int):

		self.symbol = symbol

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.symbol == other.symbol

	def free_symbols(self) -> Set[int]:
		return {self.symbol}

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		return {}

	def get_str(self, names: Names) -> str:
		return names.get(self.symbol)

	def __hash__(self) -> int:
		return self.symbol

	def replaced(self, a: int, b: int) -> Identifier:

		if a == self.symbol:
			return Identifier(b)

		else:
			return Identifier(self.symbol)

	def get_symbols(self) -> Set[int]:
		return {self.symbol}

class Predicat(Formulae):

	level: float = 100

	def __init__(self, head: Identifier, tail: Sequence[Identifier]):

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
		return functools.reduce(set.union, (e.free_symbols() for e in self.tail))

	def get_type_infos(self) -> Mapping[int, TypeInfo]:

		ans: MutableMapping[int, TypeInfo] = {}
		
		for place, identifier in enumerate(self.tail, 0):

			try:
				ans[identifier.symbol].add((self.head.symbol, place))

			except KeyError:
				ans[identifier.symbol] = TypeInfo({(self.head.symbol, place),})

		return ans

	def replaced(self, a: int, b: int) -> Predicat:
		return Predicat(self.head.replaced(a, b), [e.replaced(a, b) for e in self.tail])

	def get_str(self, names: Names) -> str:
		return f"{self.head.get_str(names)}({', '.join(e.get_str(names) for e in self.tail)})"

	def get_symbols(self) -> Set[int]:
		return functools.reduce(set.union, (e.get_symbols() for e in self.tail))

class Unary(Formulae):

	level: float = 100

	def __init__(self, a: Formulae):

		self.a = a

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.a == other.a

	def free_symbols(self) -> Set[int]:
		return self.a.free_symbols()

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		return self.a.get_type_infos()

	def replaced(self, a: int, b: int) -> Unary:
		return self.__class__(self.a.replaced(a, b))

	def get_symbols(self) -> Set[int]:
		return self.a.get_symbols()

class Not(Unary):
	
	def get_str(self, names: Names) -> str:
		return f"¬{paren_if(self.a.get_str(names), self.a.level > self.level)}"

class ForAll(Formulae):
	"""

		only use once at the root of a formulae!

	"""

	level: float = math.inf
	
	def __init__(self, bound_identifiers: Set[Identifier], formulae: Formulae):

		self.bound_identifiers = bound_identifiers
		self.formulae = formulae

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.bound_identifiers == other.bound_identifiers and self.formulae == other.formulae

	def free_symbols(self) -> Set[int]:
		return self.formulae.free_symbols() - functools.reduce(set.union, (e.free_symbols() for e in self.bound_identifiers))

	def get_type_infos(self) -> Mapping[int, TypeInfo]:
		return self.formulae.get_type_infos()

	def get_str(self, names: Names) -> str:
		return f"∀{','.join(e.get_str(names) for e in self.bound_identifiers)}.{self.formulae.get_str(names)}"

	def get_symbols(self) -> Set[int]:
		return self.formulae.get_symbols() # ignoring bound_identifiers since they will be either in formulae or useless

	def replaced(self, a: int, b: int) -> ForAll:
		return ForAll({e.replaced(a, b) for e in self.bound_identifiers}, self.formulae.replaced(a, b))

class Binary(Formulae):

	level: float = 200

	def __init__(self, a: Formulae, b: Formulae):

		self.a = a
		self.b = b

	def __eq__(self, other) -> bool:
		return type(self) is type(other) and self.a == other.a and self.b == other.b

	def free_symbols(self) -> Set[int]:
		return self.a.free_symbols() | self.b.free_symbols()

	def get_type_infos(self) -> Mapping[int, TypeInfo]:

		a: MutableMapping[int, TypeInfo] = {**self.a.get_type_infos()}
		b = self.b.get_type_infos()
		
		for symbol, t in b.items():

			try:
				a[symbol] |= t

			except KeyError:
				a[symbol] = t

		return a

	def replaced(self, a: int, b: int) -> Binary:
		return self.__class__(self.a.replaced(a, b), self.b.replaced(a, b))

	def get_symbols(self) -> Set[int]:
		return self.a.get_symbols() | self.b.get_symbols()

class And(Binary):
	
	def get_str(self, names: Names) -> str:
		return f"{paren_if(self.a.get_str(names), self.a.level > self.level)}∧{paren_if(self.b.get_str(names), self.b.level > self.level)}"

class Or(Binary):
	
	def get_str(self, names: Names) -> str:
		return f"{paren_if(self.a.get_str(names), self.a.level > self.level)}∨{paren_if(self.b.get_str(names), self.b.level > self.level)}"

class Imply(Binary):

	level: float = 300
	
	def get_str(self, names: Names) -> str:
		return f"{paren_if(self.a.get_str(names), self.a.level > self.level)}→{paren_if(self.b.get_str(names), self.b.level > self.level)}"

class Sequent:

	def __init__(self, antesequent: Tuple[Formulae], consequent: Tuple[Formulae]):

		self.antesequent = antesequent
		self.consequent = consequent

	def get_str(self, names: Names) -> str:
		return f"{', '.join(e.get_str(names) for e in self.antesequent)} ⊢ {', '.join(e.get_str(names) for e in self.consequent)}"

"""
def make_goal(axioms: List[Formulae], situation: List[Formulae], question: Formulae) -> Sequent:

	involved: List[Formulae] = situation + [question]
	axiom_type_infos = get_type_infos(axioms)
	involved_type_infos = get_type_infos(involved)
	actual_axioms = []

	for axiom in axioms:
		match axiom:
			case ForAll(identifiers=identifiers, formulae=formulae):

				axiom_symbols = list(axiom.get_symbols())
				candidate_symbols = []

				for axiom_symbol in axiom_symbols:

					axiom_symbol_type = axiom_type_infos[axiom_symbol]
					candidate_symbols.append(
						[
							s
							for s, t in involved_type_infos.items()
							if t.elements & axiom_symbol_type.elements
						]
					)

				for binding in itertools.product(*candidate_symbols):
					for axiom_symbol, involved_symbol in zip(axiom_symbols, binding):
						actual_axioms.append(formulae.replaced(axiom_symbol, involved_symbol))

			case formulae:
				actual_axioms.append(formulae)

	return Sequent(tuple(actual_axioms + situation), (question,))
"""

class ProofDone(Exception): pass

class Prover:

	def __init__(self,
		goal: Sequent,
		goal_stack: List[Sequent],
		unprovable: List[Sequent],
		type_infos: Mapping[int, TypeInfo],
	):

		self.goal = goal
		self.goal_stack = goal_stack
		self.unprovable = unprovable
		self.type_infos = type_infos

	@classmethod
	def new(cls, goal: Sequent) -> Prover:
		return Prover(
			goal=goal,
			goal_stack=[goal,],
			unprovable=[],
			type_infos=get_type_infos(goal.antesequent + goal.consequent),
		)

	@property
	def proved(self) -> bool:
		return not self.goal_stack and not self.unprovable

	def get_debug(self, names: Names) -> str:

		goal_stack_txt = '\n - '.join(e.get_str(names) for e in self.goal_stack)
		unprovable_txt = '\n - '.join(e.get_str(names) for e in self.unprovable)
		return f"{self.goal.get_str(names)}:\ngoal stack:\n{goal_stack_txt}\nunprovable:\n{unprovable_txt}\nproved: {self.proved}"

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

			if isinstance(formulae, Imply):

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(gamma, (a,) + sequent.consequent))
				self.goal_stack.append(Sequent(gamma + (b,), sequent.consequent))
				return

			elif isinstance(formulae, Or):

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(gamma + (a,), sequent.consequent))
				self.goal_stack.append(Sequent(gamma + (b,), sequent.consequent))
				return

			elif isinstance(formulae, And):

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(gamma + (a, b), sequent.consequent))
				return

			elif isinstance(formulae, Not):

				a = formulae.a
				self.goal_stack.append(Sequent(gamma, sequent.consequent + (a,)))
				return

			elif isinstance(formulae, ForAll):

				new_formulae = formulae

				for bound_identifier in formulae.bound_identifiers:
					for bound_sym in bound_identifier.get_symbols():

						for target_sym in functools.reduce(set.union, (e.free_symbols() for e in sequent.consequent)):
							if self.type_infos[bound_sym].elements & self.type_infos[target_sym].elements:
								break

						else:
							continue

						new_formulae = new_formulae.replaced(bound_sym, target_sym)

				if new_formulae is formulae:
					continue

				self.goal_stack.append(Sequent(gamma + (new_formulae,), sequent.consequent))
				return

			elif isinstance(formulae, Predicat):
				continue

			else:
				raise Exception(formulae)

		for n in range(len(sequent.consequent)):

			formulae = sequent.consequent[n]
			delta = tuple(sequent.consequent[i] for i in range(len(sequent.consequent)) if i != n)

			if isinstance(formulae, Imply):

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(sequent.antesequent + (a,), delta + (b,)))
				return

			elif isinstance(formulae, Or):

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(sequent.antesequent, delta + (a, b)))
				return

			elif isinstance(formulae, And):

				a, b = formulae.a, formulae.b
				self.goal_stack.append(Sequent(sequent.antesequent, delta + (a,)))
				self.goal_stack.append(Sequent(sequent.antesequent, delta + (b,)))
				return

			elif isinstance(formulae, Not):

				a = formulae.a
				self.goal_stack.append(Sequent(sequent.antesequent + (a,), delta))
				return

			elif isinstance(formulae, Predicat):
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

def main():

	names = Names.new()
	x = v("x")
	y = v("Y")
	c = v("C")
	h = v("H")
	b = v("b")
	human = v("Human")
	print(names.get_str())

	print("=== Axioms ===")
	axioms = [
		pred(human, x),
		forall([x], (pred(c, x) |land| pred(y, x)) |imply| pred(h, x)),
	]

	for axiom in axioms:
		print(" - " + axiom.get_str(names))
		print(f"free symbols: {', '.join(names.get_l(axiom.free_symbols()))}")

	print(TypeInfo.str_infos(names, get_type_infos(axioms)))

	print("=== Situation ===")
	situation = [
		pred(y, b),
		pred(c, b),
	]

	for e in situation:
		print(" - " + e.get_str(names))
		print(f"free symbols: {', '.join(names.get_l(e.free_symbols()))}")

	print(TypeInfo.str_infos(names, get_type_infos(situation)))

	print("=== Question ===")
	question = pred(h, b)
	print(question.get_str(names))
	print(f"free_symbols: {', '.join(names.get_l(question.free_symbols()))}")
	print(TypeInfo.str_infos(names, get_type_infos([question])))
	print("================")
	sequent = Sequent(tuple(axioms + situation), (question,))
	print(sequent.get_str(names))
	prover = Prover.new(sequent)
	prover.prove()
	print(prover.get_debug(names))

if __name__ == "__main__":
	main()
