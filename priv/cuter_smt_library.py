# -*- coding: utf-8 -*-

# =================
# struct -> smtlib: serialize
# smtlib -> struct: unserialize
# -----------------
# struct -> python: parse
# python -> struct: build
# -----------------
# struct -> erlang: encode
# erlang -> struct: decode
# =================


# ------------------------
# convert from & to smtlib
# ------------------------

def serialize(expr):
	"""
	Serialize a structured list to an SMTLIB string.
	"""
	if isinstance(expr, list):
		return "(" + " ".join(list(map(serialize, expr))) + ")"
	else:
		return expr

def unserialize(smt, cur = None):
	"""
	Unserialize an SMTLIB string to a structured list.
	"""
	if cur is None:
		return unserialize(smt, 0)[0]
	while smt[cur].isspace():
		cur += 1
	if smt[cur] == "(":
		nodes = []
		beg = cur
		cur += 1
		while True:
			while smt[cur].isspace():
				cur += 1
			if smt[cur] == ")":
				break
			node = unserialize(smt, cur)
			nodes.append(node[0])
			cur = node[2]
		end = cur + 1
		return (nodes, beg, end)
	else:
		beg = cur
		while smt[cur] != ")" and not smt[cur].isspace():
			cur += 1
		end = cur
		return (smt[beg:end], beg, end)

# ------------------------
# convert from & to python
# ------------------------

def parse_int(expr):
	if isinstance(expr, list):
		if expr[0] == "-" and len(expr) == 2:
			return -parse_int(expr[1])
	else:
		return int(expr)
	assert False, "parse_int({})".format(str(expr))

def parse_real(expr):
	if isinstance(expr, list):
		if expr[0] == "-" and len(expr) == 2:
			return -parse_real(expr[1])
		if expr[0] == "/" and len(expr) == 3:
			return parse_real(expr[1]) / parse_real(expr[2])
	else:
		return float(expr)
	clg.debug_info()
	assert False, "parse_real({})".format(str(expr))

def expand_lets(expr, lets = {}):
	if not isinstance(expr, list):
		if expr in lets:
			return lets[expr]
		else:
			return expr
	elif not expr:
		return []
	elif expr[0] == "let":
		assert len(expr) == 3, "expand_lets({})".format(str(expr))
		lets_copy = lets.copy()
		for var in expr[1]:
			assert len(var) == 2 and not isinstance(var[0], list), "expand_lets({})".format(str(expr))
			lets_copy[var[0]] = expand_lets(var[1], lets)
		return expand_lets(expr[2], lets_copy)
	else:
		return [expand_lets(item, lets) for item in expr]

def build_int(num):
	if num < 0:
		return ["-", str(-num)]
	else:
		return str(num)

def build_real(num):
	if num < 0:
		return ["-", str(-num)]
	else:
		return str(num)

def build_tlist(items):
	tlist = "tn"
	for item in reversed(items):
		tlist = ["tc", item, tlist]
	return tlist

def build_ilist(items):
	ilist = "in"
	for item in reversed(items):
		ilist = ["ic", build_int(item), ilist]
	return ilist

def build_slist(items):
	slist = "sn"
	for item in reversed(items):
		slist = ["sc", "true" if item else "false", slist]
	return slist


# ------------------------
# convert from & to erlang
# ------------------------

# encode and decode are implemented in 'Private Methods' section of class ErlangSMT


# ----------------
# useful constants
# ----------------

false = ["atom", build_ilist(list(map(ord, "false")))]

true = ["atom", build_ilist(list(map(ord, "true")))]

datatypes = [
	[
		"Term",
		["int", ["iv", "Int"]],
		["real", ["rv", "Real"]],
		["list", ["lv", "TList"]],
		["tuple", ["tv", "TList"]],
		["atom", ["av", "IList"]],
		["str", ["sv", "SList"]],
		["fun", ["fv", "Int"]],
	],
	[
		"TList",
		["tn"],
		["tc", ["th", "Term"], ["tt", "TList"]],
	],
	[
		"IList",
		["in"],
		["ic", ["ih", "Int"], ["it", "IList"]],
	],
	[
		"SList",
		["sn"],
		["sc", ["sh", "Bool"], ["st", "SList"]],
	],
	[
		"FList",
		["fn"],
		["fc", ["fx", "TList"], ["fy", "Term"], ["ft", "FList"]],
	],
]


# --------------------
# simple SMTLIB macros
# --------------------

def And(*expr):
	ret = ["and"]
	ret.extend(expr)
	return ret

def Or(*expr):
	ret = ["or"]
	ret.extend(expr)
	return ret

def IsBool(expr):
	return [
		"or",
		["=", expr, true],
		["=", expr, false],
	]

def BoolToAtom(expr):
	return ["ite", expr, true, false]

def AtomToBool(expr):
	return ["=", expr, true]

def NumBinOp(operator, t0, t1, t2):
	"""
	Return whether t0 == t1 <op> t2.
	"""
	return [
		"and",
		["or", ["is-int", t1], ["is-real", t1]],
		["or", ["is-int", t2], ["is-real", t2]],
		[
			"ite",
			["and", ["is-int", t1], ["is-int", t2]],
			["=", t0, ["int", [operator, ["iv", t1], ["iv", t2]]]],
			[
				"=",
				t0,
				[
					"real",
					[
						operator,
						["ite", ["is-int", t1], ["to_real", ["iv", t1]], ["rv", t1]],
						["ite", ["is-int", t2], ["to_real", ["iv", t2]], ["rv", t2]]
					]
				]
			]
		],
	]

def IsFunction(f):
	"""
	f is a mathematical function.
	iff x1 == x2 => f(x1) == f(x2)
	"""
	return ["forall",
		[["tl", "TList"]],
		["fu", ["fm", ["fv", f]], "tl"],
	]

# --------------------------
# SMTLIB recursive functions
# --------------------------

def IntAnd(n, n1, n2, esmt = None):
	"""
	int-and returns whether n == n1 & n2
	"""
	if esmt is not None and "int-and" not in esmt.library:
		esmt.library.append("int-and")
		esmt.commands.append(["define-fun-rec", "int-and-rec", [["n", "Int"], ["n1", "Int"], ["n2", "Int"]], "Bool", [
			"or",
			["=", "n1", "n", "0"],
			["=", "n2", "n", "0"],
			["=", "n1", "n2", "n", ["-", "1"]],
			[
				"and",
				["=", ["and", ["not", ["=", ["mod", "n1", "2"], "0"]], ["not", ["=", ["mod", "n2", "2"], "0"]]], ["not", ["=", ["mod", "n", "2"], "0"]]],
				["int-and-rec", ["div", "n", "2"], ["div", "n1", "2"], ["div", "n2", "2"]],
			],
		]])
		esmt.commands.append(["define-fun", "int-and", [["n", "Int"], ["n1", "Int"], ["n2", "Int"]], "Bool", [
			"and",
			["=>", [">=", "n1", "0"], ["<=", "0", "n", "n1"]],
			["=>", [">=", "n2", "0"], ["<=", "0", "n", "n2"]],
			["=>", ["and", ["<", "n1", "0"], ["<", "n2", "0"]], ["<", ["+", "n1", "n2"], "n", "0"]],
			["=>", ["<", "n", "0"], ["and", ["<", "n1", "0"], ["<=", "n", "n1"], ["<", "n2", "0"], ["<=", "n", "n2"]]],
			["int-and-rec", "n", "n1", "n2"],
		]])
	return ["int-and", n, n1, n2]

def IntOr(n, n1, n2, esmt = None):
	"""
	int-or returns whether n == n1 | n2
	"""
	if esmt is not None and "int-or" not in esmt.library:
		esmt.library.append("int-or")
		esmt.commands.append(["define-fun-rec", "int-or-rec", [["n", "Int"], ["n1", "Int"], ["n2", "Int"]], "Bool", [
			"or",
			["=", "n1", "n", ["-", "1"]],
			["=", "n2", "n", ["-", "1"]],
			["=", "n1", "n2", "n", "0"],
			[
				"and",
				["=", ["or", ["not", ["=", ["mod", "n1", "2"], "0"]], ["not", ["=", ["mod", "n2", "2"], "0"]]], ["not", ["=", ["mod", "n", "2"], "0"]]],
				["int-or-rec", ["div", "n", "2"], ["div", "n1", "2"], ["div", "n2", "2"]],
			],
		]])
		esmt.commands.append(["define-fun", "int-or", [["n", "Int"], ["n1", "Int"], ["n2", "Int"]], "Bool", [
			"and",
			["=>", ["<", "n1", "0"], ["and", ["<=", "n1", "n"], ["<", "n", "0"]]],
			["=>", ["<", "n2", "0"], ["and", ["<=", "n2", "n"], ["<", "n", "0"]]],
			["=>", ["and", [">=", "n1", "0"], [">=", "n2", "0"]], ["<=", "0", "n", ["+", "n1", "n2"]]],
			["=>", [">=", "n", "0"], ["and", ["<=", "0", "n1", "n"], ["<=", "0", "n2", "n"]]],
			["int-or-rec", "n", "n1", "n2"],
		]])
	return ["int-or", n, n1, n2]

def IntXor(n, n1, n2, esmt = None):
	"""
	int-xor returns whether n == n1 ^ n2
	"""
	if esmt is not None and "int-xor" not in esmt.library:
		esmt.library.append("int-xor")
		esmt.commands.append(["define-fun-rec", "int-xor", [["n", "Int"], ["n1", "Int"], ["n2", "Int"]], "Bool", [
			"or",
			["and", ["=", "n", "0"], ["=", "n1", "n2"]],
			["and", ["=", "n1", "0"], ["=", "n2", "n"]],
			["and", ["=", "n2", "0"], ["=", "n", "n1"]],
			["and", ["=", "n", ["-", "1"]], ["=", ["+", "n1", "n2"], ["-", "1"]]],
			["and", ["=", "n1", ["-", "1"]], ["=", ["+", "n2", "n"], ["-", "1"]]],
			["and", ["=", "n2", ["-", "1"]], ["=", ["+", "n", "n1"], ["-", "1"]]],
			[
				"and",
				["=", ["not", ["=", ["mod", "n", "2"], "0"]], ["xor", ["not", ["=", ["mod", "n1", "2"], "0"]], ["not", ["=", ["mod", "n2", "2"], "0"]]]],
				["int-xor", ["div", "n", "2"], ["div", "n1", "2"], ["div", "n2", "2"]],
			],
		]])
	return ["int-xor", n, n1, n2]

def RealPow(p, b, e, esmt = None):
	"""
	real-pow returns whether p == b ** e
	"""
	# real-pow isn't efficient when having to calculate the e-root of p or a large e-power of b.
	if esmt is not None and "real-pow" not in esmt.library:
		esmt.library.append("real-pow")
		esmt.commands.append(["define-fun-rec", "real-pow", [["p", "Real"], ["b", "Real"], ["e", "Int"]], "Bool", [
			"or",
			["and", ["=", "b", "0"], ["not", ["=", "e", "0"]], ["=", "p", "0"]],
			["and", ["=", "b", "1"], ["=", "p", "1"]],
			["and", ["=", "b", ["-", "1"]], ["=", ["mod", "e", "2"], "0"], ["=", "p", "1"]],
			["and", ["=", "b", ["-", "1"]], ["=", ["mod", "e", "2"], "1"], ["=", "p", ["-", "1"]]],
			["and", [">", "e", "1"], ["<", "1", "b", "p"], ["real-pow", ["/", "p", "b"], "b", ["-", "e", "1"]]],
			["and", [">", "e", "1"], ["<", "0", "p", "b", "1"], ["real-pow", ["/", "p", "b"], "b", ["-", "e", "1"]]],
			["and", [">", "e", "1"], ["=", ["mod", "e", "2"], "0"], ["<", ["-", "1"], "b", "0", "p", ["-", "b"], "1"], ["real-pow", ["/", "p", "b"], "b", ["-", "e", "1"]]],
			["and", [">", "e", "1"], ["=", ["mod", "e", "2"], "0"], ["<", "b", ["-", "1"], "1", ["-", "b"], "p"], ["real-pow", ["/", "p", "b"], "b", ["-", "e", "1"]]],
			["and", [">", "e", "1"], ["=", ["mod", "e", "2"], "1"], ["<", ["-", "1"], "b", "p", "0"], ["real-pow", ["/", "p", "b"], "b", ["-", "e", "1"]]],
			["and", [">", "e", "1"], ["=", ["mod", "e", "2"], "1"], ["<", "p", "b", ["-", "1"]], ["real-pow", ["/", "p", "b"], "b", ["-", "e", "1"]]],
			["and", ["=", "e", "1"], ["=", "b", "p"]],
			["and", ["=", "e", "0"], ["not", ["=", "b", "0"]], ["=", "p", "1"]],
			["and", ["=", "e", ["-", "1"]], ["=", ["*", "b", "p"], "1"]],
			["and", ["<", "e", ["-", "1"]], ["<", "0", "p", "1", "b"], ["real-pow", ["*", "p", "b"], "b", ["+", "e", "1"]]],
			["and", ["<", "e", ["-", "1"]], ["<", "0", "b", "1", "p"], ["real-pow", ["*", "p", "b"], "b", ["+", "e", "1"]]],
			["and", ["<", "e", ["-", "1"]], ["=", ["mod", "e", "2"], "0"], ["<", ["-", "1"], "b", "0", ["-", "b"], "1", "p"], ["real-pow", ["*", "p", "b"], "b", ["+", "e", "1"]]],
			["and", ["<", "e", ["-", "1"]], ["=", ["mod", "e", "2"], "0"], ["<", "b", ["-", "1"], "0", "p", "1", ["-", "b"]], ["real-pow", ["*", "p", "b"], "b", ["+", "e", "1"]]],
			["and", ["<", "e", ["-", "1"]], ["=", ["mod", "e", "2"], "1"], ["<", "p", ["-", "1"], "b", "0"], ["real-pow", ["*", "p", "b"], "b", ["+", "e", "1"]]],
			["and", ["<", "e", ["-", "1"]], ["=", ["mod", "e", "2"], "1"], ["<", "b", ["-", "1"], "p", "0"], ["real-pow", ["*", "p", "b"], "b", ["+", "e", "1"]]],
		]])
	return ["real-pow", p, b, e]

def SListSpec(l, n, esmt = None):
	"""
	slist-spec returns whether len(l) % n == r
	"""
	# slist-spec is efficient when n is a given integer constant
	if esmt is not None and "slist-spec" not in esmt.library:
		esmt.library.append("slist-spec")
		esmt.commands.append(["define-fun-rec", "slist-spec", [["l", "SList"], ["n", "Int"], ["r", "Int"]], "Bool", [
			"or",
			["and", ["is-sn", "l"], ["=", "r", "0"]],
			["and", ["is-sc", "l"], ["slist-spec", ["st", "l"], "n", ["-", ["ite", ["=", "r", "0"], "n", "r"], "1"]]],
		]])
	return ["slist-spec", l, n, "0"]

def FListEquals(f, x, y, d, esmt):
	"""
	flist-equals return whether f(x) = y with depth at most d
	"""
	if esmt is not None and "flist-equals" not in esmt.library:
		esmt.library.append("flist-equals")
		esmt.commands.append(["define-fun-rec", "flist-equals", [["f", "FList"], ["x", "TList"], ["y", "Term"], ["d", "Int"]], "Bool", [
			"or",
			["and", [">=", "d", "0"], ["is-fc", "f"], ["=", ["fx", "f"], "x"], ["=", ["fy", "f"], "y"]],
			["and", [">", "d", "0"], ["is-fc", "f"], ["not", ["=", ["fx", "f"], "x"]], ["flist-equals", ["ft", "f"], "x", "y", ["-", "d", "1"]]],
		]])
	return ["flist-equals", f, x, y, d]
