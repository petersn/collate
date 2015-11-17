#!/usr/bin/python

import byte_code

def read(path):
	with open(path) as f:
		return f.read()

def compile(input_text):
	lines = input_text.split("\n")
	for line in lines:
		line = line.split("#")[0].strip()
		if not line: continue

class GenericType:
	def __init__(self):
		raise Exception("Abstract base class GenericType should never be instantiated.")

	def entails(self, other):
		raise NotImplementedError("Abstract base class method shouldn't be called.")
		return False

	def unary(self, operation):
		raise NotImplementedError("Abstract base class method shouldn't be called.")

	def __repr__(self):
		return str(self)

"""
	def merge(self, other, certainty):
		if certainty == Certainty.yes:
			return other
		if certianty == Certainty.no:
			return self
		if isinstance(other, TypeUnion):
			return TypeUnion().fill([self, other])
"""

class WillCrash(GenericType):
	def __eq__(self, other):
		return isinstance(other, WillCrash)

	def entails(self, other):
		return self == other

	def unary(self, operation):
		return self

class TypeUnion(GenericType):
	MAX_UNION_SIZE = 16

	def __init__(self):
		self.types = []

	def __str__(self):
		return "(%s)" % " | ".join(str(t) for t in self.types)

	def __eq__(self, other):
		if not isinstance(other, TypeUnion):
			return False
		if len(self.types) != len(other.types):
			return False
		# Compare the types, lined up.
		return all(i == j for i, j in zip(self.types, other.types))

	def entails(self, other):
		# To entail a TypeUnion we must entail all of its types.
		if isinstance(other, TypeUnion):
			return all(self.entails(t) for t in other.types)
		# Otherwise, we must have at least one type that entails the given type.
		for t in self.types:
			if t.entails(other):
				return True
		return False

	def unary(self, operation):
		return TypeUnion().fill([t.unary(operation) for t in self.types])

	def fill(self, types):
		# Flatten nested TypeUnions.
		to_build_from = []
		for t in types:
			if isinstance(t, TypeUnion):
				to_build_from.extend(t.types)
			else:
				to_build_from.append(t)
		# Deduplicate the types.
		self.types = []
		for t in to_build_from:
			# If a union contains Polymorphic, then it's completely polymorphic.
			if isinstance(t, Polymorphic):
				return t
			if t not in self.types:
				self.types.append(t)
		# Find when one type is simply a refinement of another.
		to_remove = []
		for t1 in self.types:
			for t2 in self.types:
				if t1 is t2:
					continue
				if t1.entails(t2):
					to_remove.append(t2)
		self.types = [t for t in self.types if t not in to_remove]
		# Do some sanity checking.
		assert len(self.types) > 0, "Can't have a TypeUnion over no types."
		# Simplify type unions over a single type.
		if len(self.types) == 1:
			return self.types[0]
		# If we're tracking over self.MAX_UNION_SIZE different types, then become totally generic.
		if len(self.types) > self.MAX_UNION_SIZE:
			return Polymorphic()
		# Sort to guarantee nice deterministic comparisons.
		self.types.sort(key=str)
		return self

class Polymorphic(GenericType):
	def __init__(self):
		pass

	def __str__(self):
		return "?"

	def __eq__(self, other):
		return isinstance(other, Polymorphic)

	def entails(self, other):
		# The most polymorphic type entails every other type.
		return True

	def unary(self, operation):
		# The to_bool operation is basically the only one we can be certain of the outcome from.
		if operation == Operations.to_boolean:
			return any_boolean
		return Polymorphic()

class Integer(GenericType):
	def __init__(self, value=None):
		self.value = value

	def entails(self, other):
		return isinstance(other, Integer) and ((other.value != None and self.value == None) or self.value == other.value)

	def unary(self, operation):
		if operation in (Operations.to_boolean, Operations.boolean_not):
			# If we don't know what integer we are yet, then we could become either bool.
			if self.value == None:
				return any_boolean
			# If we have a specific value, then we become one if we're nonzero, zero otherwise.
			if self.value == 0:
				return Integer(0 ^ (operation == Operations.boolean_not))
			return Integer(1 ^ (operation == Operations.boolean_not))
		elif operation == Operations.negate:
			if self.value == None:
				return self
			return Integer(-self.value)
		elif operation == Operations.length:
			return WillCrash()
		raise NotImplementedError

	def __str__(self):
		if self.value == None:
			return "int"
		return str(self.value)

	def __eq__(self, other):
		return isinstance(other, Integer) and self.value == other.value

class String(GenericType):
	def __init__(self, value=None):
		self.value = value

	def entails(self, other):
		return isinstance(other, String) and ((other.value != None and self.value == None) or self.value == other.value)

	def unary(self, operation):
		if operation == Operations.to_boolean:
			if self.value == None:
				return any_boolean
			if self.value == "":
				return Integer(0)
			return Integer(1)
		elif operation == Operations.boolean_not:
			return self.unary(Operations.to_boolean).unary(Operations.boolean_not)
		elif operation == Operations.negate:
			return WillCrash()
		elif operation == Operations.length:
			if self.value != None:
				return Integer(len(self.value))
			return Integer()
		raise NotImplementedError

	def __str__(self):
		if self.value == None:
			return "str"
		return repr(self.value)

	def __eq__(self, other):
		return isinstance(other, String) and self.value == other.value

class Array(GenericType):
	def __init__(self):
		self.contents = []
		self.homogeneous_type = Polymorphic()

	def fill(self, contents=None, homogeneous_type=None):
		self.contents = [] if contents is None else contents
		self.homogeneous_type = homogeneous_type
		# If an array has any entries that will raise an exception, then the entire thing will.
		if any(isinstance(t, WillCrash) for t in self.contents) or isinstance(self.homogeneous_type, WillCrash):
			return WillCrash()
		return self

	def entails(self, other):
		if not isinstance(other, Array):
			return False
		# Some casework.
		# Case 1: We're both of known length.
		if self.homogeneous_type == other.homogeneous_type == None:
			return len(self.contents) == len(other.contents) and all(i.entails(j) for i, j in zip(self.contents, other.contents))
		# Case 2: We're homogeneous, but they aren't, then we must entail all their types.
		if self.homogeneous_type != None and other.homogeneous_type == None:
			return all(self.homogeneous_type.entails(t) for t in other.contents)
		# Case 3: We're both homogeneous.
		if self.homogeneous_type != None and other.homogeneous_type != None:
			return self.homogeneous_type.entails(other.homogeneous_type)
		# In the final case (they're homogeneous, we're fixed), then we can't possibly entail them.
		return False

	def unary(self, operation):
		if operation == Operations.to_boolean:
			# Arrays of unknown length may or may not be true.
			if self.homogeneous_type != None:
				return any_boolean
			return Integer(int(bool(self.contents)))
		elif operation == Operations.boolean_not:
			return self.unary(Operations.to_boolean).unary(Operations.boolean_not)
		elif operation == Operations.negate:
			return WillCrash()
		elif operation == Operations.length:
			if self.homogeneous_type != None:
				return Integer()
			return Integer(len(self.contents))
		raise NotImplementedError
		#return Array().fill(contents=None, homogeneous_type=self.homogeneous_type.unary(operation))
		#return Array().fill([t.unary(operation) for t in self.contents])

	def __str__(self):
		if self.homogeneous_type != None:
			return "[%s...]" % self.homogeneous_type
		return "[%s]" % ", ".join(str(t) for t in self.contents)

	def __eq__(self, other):
		if not isinstance(other, Array):
			return False
		# If we're both homogeneous arrays, make sure we're a compatible kind.
		if self.homogeneous_type != None and other.homogeneous_type != None:
			return self.homogeneous_type == other.homogeneous_type
		return isinstance(other, Array) and all(i == j for i, j in zip(self.contents, other.contents))

class Operations:
	# Unary.
	to_boolean = 0
	boolean_not = 1
	negate = 2
	length = 3

	# Binary.
	add = 4
	subtract = 5
	multiply = 6
	divide = 7
	modulo = 8
	binary_and = 9
	binary_or = 10

class Certainty:
	no = 0
	maybe = 1
	yes = 2

	@staticmethod
	def from_value(b):
		b = b.unary(Operations.to_boolean)
		if isinstance(b, Integer):
			assert b.value != None
			if b.value == 1:
				return Certainty.yes
			elif b.value == 0:
				return Certainty.no
			assert False, "BUGBUGBUG: .unary(Operations.to_boolean) gave an Integer whose value was neither 0 or 1."
		if isinstance(b, TypeUnion):
			assert b == anybool, "BUGBUGBUG: .unary(Operations.to_boolean) gave a TypeUnion that wasn't just (0 | 1)."
			return Certainty.maybe

any_boolean = TypeUnion().fill([Integer(0), Integer(1)])

class VariableContext:
	def __init__(self):
		self.types, self.parents = {}, []

	def __contains__(self, name):
		if name in self.types:
			return True
		return any(name in parent for parent in self.parents)

	def copy(self):
		vc = VariableContext()
		vc.types = self.types.copy()
		vc.parents = self.parents
		return vc

	def lookup(self, name):
		if name in self.types:
			return self.types[name]
		for parent in self.parents:
			if name in parent:
				return parent.lookup(name)

	def evaluate(self, bytecode):
		for code in bytecode:
			opcode, args = code[0], code[1:]
			if opcode == "MOVE":
				self.types[args[0]] = self.lookup(args[1])
			elif opcode == "INT_LITERAL":
				self.types[args[0]] = Integer(args[1])
			elif opcode == "STR_LITERAL":
				self.types[args[0]] = String(args[1])
			elif opcode == "IF":
				condition = Certainty.from_value(self.lookup(args[0]))
				if condition == Certainty.yes:
					# If we certainly execute the inner code, just do it in the current scope.
					self.evaluate(args[1])
				elif condition == Certainty.maybe:
					# If we can't be sure if we execute the inner code or not, then we have to do type unions.
					inner_vc = self.copy()
					inner_vc.evaluate(args[1])
					# Merge up the values.
					for k, v in inner_vc.types:
						if k not in self.types:
							self.types[k] = v
						else:
							self.types[k] = TypeUnion().fill([self.types[k], v])
			else:
				raise NotImplementedError("Missing opcode: %r" % code)

bc = byte_code.parse_bytecode(read("src/bc1.collate"))

vc = VariableContext()
vc.evaluate(bc)

print vc.types

