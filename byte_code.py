#!/usr/bin/python

valid_opcodes = {
	"MOVE": 2,
	"INT_LITERAL": 2,
	"STR_LITERAL": 2,
	"UNARY": 3,
	"BINARY": 4,
	"IF": 1,
	"END": 0,
}

def decode_string_literal(s):
	if s.startswith("hex:"):
		return s[4:].decode("hex")
	elif s.startswith("b64:"):
		return s[4:].decode("base64")
	else:
		return s

def parse_bytecode(input_text):
	bytecode = []
	stack = [bytecode]
	lines = input_text.split("\n")
	for line in lines:
		line = line.split("#")[0].strip()
		if not line:
			continue
		line = line.replace("\t", " ")
		while "  " in line:
			line = line.replace("  ", " ")
		line = line.split(" ")
		opcode = line[0]
		assert opcode in valid_opcodes, "Invalid opcode: %r" % opcode
		assert len(line) - 1 == valid_opcodes[opcode], "Wrong number of operands to %r (was %i, should have been %i)" % (opcode, len(line) - 1, valid_opcodes[opcode])
		if opcode == "INT_LITERAL":
			line[2] = int(line[2])
		elif opcode == "STR_LITERAL":
			line[2] = decode_string_literal(line[2])
		elif opcode in ("IF", "WHILE"):
			line.append([])
			stack[-1].append(line)
			stack.append(line[-1])
			continue
		elif opcode == "END":
			stack.pop()
			continue
		stack[-1].append(line)
	return bytecode

