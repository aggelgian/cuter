# -*- coding: utf-8 -*-

import cuter_generic_solver as cgs
import cuter_common as cc
import cuter_logger as clg
import smt


false = [102, 97, 108, 115, 101]
true = [116, 114, 117, 101]


def calculate_int(obj):
	if isinstance(obj, list):
		if obj[0] == "-" and len(obj) == 2:
			i0 = calculate_int(obj[1])
			return -i0
	else:
		return int(obj)
	clg.debug_info("calculate_int: unknown operation " + str(obj))
	assert False


def calculate_real(obj):
	if isinstance(obj, list):
		if obj[0] == "-" and len(obj) == 2:
			r0 = calculate_real(obj[1])
			return -r0
		if obj[0] == "/" and len(obj) == 3:
			r1 = calculate_real(obj[1])
			r2 = calculate_real(obj[2])
			return r1 / r2
	else:
		return float(obj)
	clg.debug_info("calculate_real: unknown operation " + str(obj))
	assert False


class ErlangSMT(cgs.AbstractErlangSolver):

	def __init__(self):
		self.declarations = []

		self.declarations.append(["declare-datatypes", [], [
			[
				"Term",
				["bool", ["bval", "Bool"]],
				["int", ["ival", "Int"]],
				["real", ["rval", "Real"]],
				["list", ["lval", "TList"]],
				["tuple", ["tval", "TList"]],
				["atom", ["aval", "IList"]],
				["str", ["sval", "SList"]],
				["fun", ["fval", "Int"]],
			],
			[
				"TList",
				["nil"],
				["cons", ["hd", "Term"], ["tl", "TList"]],
			],
			[
				"IList",
				["inil"],
				["icons", ["ihd", "Int"], ["itl", "IList"]],
			],
			[
				"SList",
				["snil"],
				["scons", ["shd", "Bool"], ["stl", "SList"]],
			],
		]])
		self.declarations.append(["declare-fun", "fmap", ["Int"], ["Array", "TList", "Term"]])
		self.declarations.append(["declare-fun", "arity", ["Int"], "Int"])

		# slist_longer(l, n) returns whether length(l) >= n
		self.declarations.append(["define-fun-rec", "slist_longer", [["l", "SList"], ["n", "Int"]], "Bool", [
			"or",
			["=", "n", "0"],
			[
				"and",
				["not", ["is-snil", "l"]],
				["slist_longer", ["stl", "l"], ["-", "n", "1"]],
			],
		]])

		# slist_spec(l, m, n) returns whether len(l) >= m and (len(l) - m) % n == 0
		# slist_spec is efficient when n and m are given integer constants
		self.declarations.append(["define-fun-rec", "slist_spec_aux", [["l", "SList"], ["n", "Int"], ["r", "Int"]], "Bool", [
			"ite",
			["is-snil", "l"],
			["=", "r", "0"],
			["slist_spec_aux", ["stl", "l"], "n", ["-", ["ite", ["=", "r", "0"], "n", "r"], "1"]]
		]])
		self.declarations.append(["define-fun-rec", "slist_spec", [["l", "SList"], ["m", "Int"], ["n", "Int"]], "Bool", [
			"ite",
			["=", "m", "0"],
			[
				"ite",
				["=", "n", "0"],
				["is-snil", "l"],
				["slist_spec_aux", "l", "n", "0"]
			],
			["and", ["not", ["is-snil", "l"]], ["slist_spec", ["stl", "l"], ["-", "m", "1"], "n"],]
		]])

		self.declarations.append(["define-fun-rec", "slist_from_pair_aux", [["n", "Int"], ["b", "Int"], ["a", "SList"]], "SList", [
			"ite",
			["=", "b", "0"],
			"a",
			[
				"slist_from_pair_aux",
				["div", "n", "2"],
				["-", "b", "1"],
				["scons", ["=", ["mod", "n", "2"], "1"], "a"]
			]
		]])
		self.declarations.append(["define-fun", "slist_from_pair", [["n", "Int"], ["b", "Int"]], "SList", [
			"slist_from_pair_aux", "n", "b", "snil"
		]])

		self.declarations.append(["define-fun-rec", "slist_concat_aux", [["l1", "SList"], ["l1inv", "SList"], ["l2", "SList"]], "SList", [
			"ite",
			["is-snil", "l1"],
			[
				"ite",
				["is-snil", "l1inv"],
				"l2",
				["slist_concat_aux", "l1", ["stl", "l1inv"], ["scons", ["shd", "l1inv"], "l2"]],
			],
			["slist_concat_aux", ["stl", "l1"], ["scons", ["shd", "l1"], "l1inv"], "l2"]
		]])
		self.declarations.append(["define-fun", "slist_concat", [["l1", "SList"], ["l2", "SList"]], "SList", ["slist_concat_aux", "l1", "snil", "l2"]])

		self.declarations.append(["define-fun-rec", "slist_match", [["l1", "SList"], ["l2", "SList"]], "Bool", [
			"or",
			["is-snil", "l1"],
			[
				"and",
				["not", ["is-snil", "l2"]],
				["=", ["shd", "l1"], ["shd", "l2"]],
				["slist_match", ["stl", "l1"], ["stl", "l2"]],
			],
		]])

		# int-and returns whether n1 & n2 == n
		self.declarations.append(["define-fun-rec", "int-and-rec", [["n1", "Int"], ["n2", "Int"], ["n", "Int"]], "Bool", [
			"or",
			["=", "n1", "n", "0"],
			["=", "n2", "n", "0"],
			["=", "n1", "n2", "n", "-1"],
			[
				"and",
				["=", ["and", ["not", ["=", ["mod", "n1", "2"], "0"]], ["not", ["=", ["mod", "n2", "2"], "0"]]], ["not", ["=", ["mod", "n", "2"], "0"]]],
				["int-and-rec", ["div", "n1", "2"], ["div", "n2", "2"], ["div", "n", "2"]],
			],
		]])
		self.declarations.append(["define-fun", "int-and", [["n1", "Int"], ["n2", "Int"], ["n", "Int"]], "Bool", [
			"and",
			["implies", [">=", "n1", "0"], ["<=", "0", "n", "n1"]],
			["implies", [">=", "n2", "0"], ["<=", "0", "n", "n2"]],
			["implies", ["and", ["<", "n1", "0"], ["<", "n2", "0"]], ["<", ["+", "n1", "n2"], "n", "0"]],
			["implies", ["<", "n", "0"], ["and", ["<", "n1", "0"], ["<=", "n", "n1"], ["<", "n2", "0"], ["<=", "n", "n2"]]],
			["int-and-rec", "n1", "n2", "n"],
		]])

		# int-or returns whether n1 | n2 == n
		self.declarations.append(["define-fun-rec", "int-or-rec", [["n1", "Int"], ["n2", "Int"], ["n", "Int"]], "Bool", [
			"or",
			["=", "n1", "n", "-1"],
			["=", "n2", "n", "-1"],
			["=", "n1", "n2", "n", "0"],
			[
				"and",
				["=", ["or", ["not", ["=", ["mod", "n1", "2"], "0"]], ["not", ["=", ["mod", "n2", "2"], "0"]]], ["not", ["=", ["mod", "n", "2"], "0"]]],
				["int-or-rec", ["div", "n1", "2"], ["div", "n2", "2"], ["div", "n", "2"]],
			],
		]])
		self.declarations.append(["define-fun", "int-or", [["n1", "Int"], ["n2", "Int"], ["n", "Int"]], "Bool", [
			"and",
			["implies", ["<", "n1", "0"], ["and", ["<=", "n1", "n"], ["<", "n", "0"]]],
			["implies", ["<", "n2", "0"], ["and", ["<=", "n2", "n"], ["<", "n", "0"]]],
			["implies", ["and", [">=", "n1", "0"], [">=", "n2", "0"]], ["<=", "0", "n", ["+", "n1", "n2"]]],
			["implies", [">=", "n", "0"], ["and", ["<=", "0", "n1", "n"], ["<=", "0", "n2", "n"]]],
			["int-or-rec", "n1", "n2", "n"],
		]])

		self.vars = []
		self.aux_vars = []
		self.fun_rec_cnt = 0
		self.const_bv_cnt = 0
		self.const_slist_cnt = 0
		self.funspec = "true"
		self.cmds = []
		self.aux_cmds = []
		self.model = None

	# =========================================================================
	# Public API.
	# =========================================================================

	def fix_parameter(self, p, v):
		"""
		Fixes a symbolic variable to a specific value.
		"""
		p = self.decode(p)
		v = self.decode(v)
		self.aux_cmds.append(["assert", ["=", p, v]])

	def reset_solver(self):
		"""
		Resets the solver.
		"""
		self.model = None

	def add_axioms(self):
		"""
		Adds the axioms from memory to the solver.
		"""
		pass

	def solve(self):
		"""
		Solves a constraint set and returns the result.
		"""
		spec = ["define-fun", "spec", [["f", "Int"], ["l", "TList"]], "Bool", self.funspec]
		tpl = smt.SolverZ3().solve(self.declarations + [spec] + self.cmds + self.aux_cmds)
		check_sat = tpl[0]
		if check_sat == "sat":
			get_model = tpl[1]
			assert isinstance(get_model, list)
			assert len(get_model) > 0
			assert get_model[0] == "model"
			self.model = {}
			for define_fun in get_model[1:]:
				assert len(define_fun) == 5
				assert define_fun[0] == "define-fun"
				assert not isinstance(define_fun[1], list)
				self.model[define_fun[1]] = define_fun[4]
			return cc.mk_sat()
		elif check_sat == "unsat":
			return cc.mk_unsat()
		elif check_sat == "unknown":
			return cc.mk_unknown()
		else:
			clg.debug_info("solve: " + check_sat)

	def encode_model(self):
		"""
		Encodes the resulting model.
		"""
		entries = []
		for var in self.vars:
			if var in self.model:
				val = self.encode(self.model[var])
			else:
				val = cc.mk_any()
			entries.append(cc.mk_model_entry(cc.mk_symb(var[1:-1]), val))
		return cc.mk_model_data(cc.mk_model(entries))

	# =========================================================================
	# Private Methods.
	# =========================================================================

	def assertion(self, assertion):
		self.cmds.append(["assert", assertion])

	def decode(self, data):
		"""
		Decodes a term to its SMT representation
		"""
		if cc.is_symb(data):
			s = "|{}|".format(cc.get_symb(data))
			if s not in self.vars and s not in self.aux_vars:
				self.aux_vars.append(s)
				self.declarations.append(["declare-const", s, "Term"])
			return s
		elif cc.is_int(data):
			return ["int", str(cc.get_int(data))]
		elif cc.is_float(data):
			return ["real", str(cc.get_float(data))]
		elif cc.is_atom(data):
			atom = cc.get_atom_chars(data)
			if atom == true:
				return ["bool", "true"]
			elif atom == false:
				return ["bool", "false"]
			else:
				return ["atom", self.value2ilist(atom)]
		elif cc.is_list(data):
			return ["list", self.value2tlist(cc.get_list_subterms(data))]
		elif cc.is_tuple(data):
			return ["tuple", self.value2tlist(cc.get_tuple_subterms(data))]
		elif cc.is_bitstring(data):
			return ["str", self.value2slist(cc.get_bits(data))]
		clg.debug_info("decoding failed: " + str(data))
		assert False

	def value2tlist(self, value):
		if not value:
			return "nil"
		else:
			return ["cons", self.decode(value[0]), self.value2tlist(value[1:])]

	def value2ilist(self, value):
		if not value:
			return "inil"
		else:
			return ["icons", str(value[0]), self.value2ilist(value[1:])]

	def value2slist(self, value):
		if not value:
			return "snil"
		else:
			return ["scons", "true" if value[0] else "false", self.value2slist(value[1:])]

	def encode(self, data, lets = {}, funs = []):
		if data[0] == "bool":
			if data[1] == "true":
				return cc.mk_atom(true)
			else:
				return cc.mk_atom(false)
		elif data[0] == "int":
			return cc.mk_int(calculate_int(data[1]))
		elif data[0] == "real":
			return cc.mk_float(calculate_real(data[1]))
		elif data[0] == "atom":
			node = data[1]
			v = []
			while node != "inil":
				if isinstance(node, str) and node in lets:
					node = lets[node]
				if isinstance(node[1], str) and node[1] in lets:
					node[1] = lets[node[1]]
				v.append(int(node[1]))
				node = node[2]
			return cc.mk_atom(v)
		elif data[0] == "list":
			node = data[1]
			v = []
			while node != "nil":
				if isinstance(node, str) and node in lets:
					node = lets[node]
				if isinstance(node[1], str) and node[1] in lets:
					node[1] = lets[node[1]]
				v.append(self.encode(node[1], lets, funs))
				node = node[2]
			return cc.mk_list(v)
		elif data[0] == "tuple":
			node = data[1]
			v = []
			while node != "nil":
				if isinstance(node, str) and node in lets:
					node = lets[node]
				if isinstance(node[1], str) and node[1] in lets:
					node[1] = lets[node[1]]
				v.append(self.encode(node[1], lets, funs))
				node = node[2]
			return cc.mk_tuple(v)
		elif data[0] == "str":
			node = data[1]
			v = []
			while node != "snil":
				if isinstance(node, str) and node in lets:
					node = lets[node]
				if isinstance(node[1], str) and node[1] in lets:
					node[1] = lets[node[1]]
				v.append(node[1] == "true")
				node = node[2]
			return cc.mk_bitstring(v)
		elif data[0] == "let":
			lets = lets.copy()
			for var in data[1]:
				lets[var[0]] = var[1]
			ret = self.encode(data[2], lets, funs)
			return ret
		elif data[0] == "fun":
			fval = int(data[1])
			# if a cycle (a function calling itself recursively) is found,
			# it is obvious that the solver has selected an arbitrary term as a value
			if fval in funs:
				return cc.mk_any()
			funs = funs[:]
			funs.append(fval)
			# get return value of arity(fval)
			if "arity" in self.model:
				ite = self.model["arity"]
				while isinstance(ite, list) and len(ite) == 4 and ite[0] == "ite":
					if int(ite[1][2]) == fval:
						ite = ite[2]
					else:
						ite = ite[3]
				arity = int(ite)
				# if arity is greater than 255, we assume it is an arbitrary value selected by the solver
				# because there is no constraint limiting the function's arity; thus, we set it to zero
				if arity > 255:
					arity = 0
			else:
				arity = 0
			entries = []
			if "fmap" in self.model:
				# get return value of fmap(fval)
				ite = self.model["fmap"]
				while ite[0] in self.model:
					ite = self.model[ite[0]]
				while isinstance(ite, list) and len(ite) == 4 and ite[0] == "ite":
					if int(ite[1][2]) == fval:
						ite = ite[2]
					else:
						ite = ite[3]
				assert isinstance(ite, list) and len(ite) == 3 and ite[0] == "_" and ite[1] == "as-array"
				# return actual function
				ite = self.model[ite[2]]
				while ite[0] in self.model:
					ite = self.model[ite[0]]
				while isinstance(ite, list) and len(ite) == 4 and ite[0] == "ite":
					args = cc.get_list_subterms(self.encode(["list", ite[1][2]], lets, funs))
					if len(args) == arity:
						value = self.encode(ite[2], lets, funs)
						entries.append(cc.mk_fun_entry(args, value))
					ite = ite[3]
				otherwise = self.encode(ite, lets, funs)
			else:
				otherwise = cc.mk_any()
			return cc.mk_fun(arity, entries, otherwise)
		clg.debug_info("encoding failed: " + str(data))
		assert False

	# -------------------------------------------------------------------------
	# Parse internal commands.
	# -------------------------------------------------------------------------

	def mfa_params(self, *args):
		"""
		Stores the entry point MFA's symbolic parameters.
		"""
		self.vars = []
		for arg in args:
			s = "|{}|".format(cc.get_symb(arg))
			self.vars.append(s)
			self.declarations.append(["declare-const", s, "Term"])

	def mfa_spec(self, spec):
		"""
		Stores the spec of the entry point MFA.
		"""
		p = cc.get_spec_clauses(spec)[0]
		pms = cc.get_parameters_from_complete_funsig(p)
		for item in zip(self.vars, pms):
			self.assertion(self.build_spec(item[1], item[0]))

	def fun_rec(self, inner_spec):
		name = "fn" + str(self.fun_rec_cnt)
		self.fun_rec_cnt += 1
		self.declarations.append(["define-fun-rec", name, [["l", "TList"]], "Bool", [
			"or",
			["is-nil", "l"],
			[
				"and",
				["is-cons", "l"],
				inner_spec,
				[name, ["tl", "l"]],
			],
		]])
		return name

	def build_spec(self, spec, var):
		if cc.is_type_any(spec):
			return "true"
		elif cc.is_type_float(spec):
			return ["is-real", var]
		elif cc.is_type_integer(spec):
			return ["is-int", var]
		elif cc.is_type_list(spec):
			inner_spec = self.build_spec(cc.get_inner_type_from_list(spec), ["hd", "l"])
			name = self.fun_rec(inner_spec)
			return [
				"and",
				["is-list", var],
				[name, ["lval", var]],
			]
		elif cc.is_type_nonempty_list(spec):
			inner_spec = self.build_spec(cc.get_inner_type_from_nonempty_list(spec), ["hd", "l"])
			name = self.fun_rec(inner_spec)
			return [
				"and",
				["is-list", var],
				["is-cons", ["lval", var]],
				[name, ["lval", var]],
			]
		elif cc.is_type_tupledet(spec):
			inner_types = cc.get_inner_types_from_tupledet(spec)
			ret = ["and", ["is-tuple", var]]
			tlist = ["tval", var]
			for inner_type in inner_types:
				ret.append(["and", ["is-cons", tlist], self.build_spec(inner_type, ["hd", tlist])])
				tlist = ["tl", tlist]
			ret.append(["is-nil", tlist])
			return ret
		elif cc.is_type_tuple(spec):
			return ["is-tuple", var]
		elif cc.is_type_union(spec):
			ret = ["or"]
			for inner_type in cc.get_inner_types_from_union(spec):
				ret.append(self.build_spec(inner_type, var))
			return ret
		elif cc.is_type_range(spec):
			ret = ["and", ["is-int", var]]
			limits = cc.get_range_bounds_from_range(spec)
			if cc.has_lower_bound(limits):
				ret.append([">=", ["ival", var], str(cc.get_lower_bound(limits))])
			if cc.has_upper_bound(limits):
				ret.append(["<=", ["ival", var], str(cc.get_upper_bound(limits))])
			return ret
		elif cc.is_type_atom(spec):
			return ["is-atom", var]
		elif cc.is_type_bitstring(spec):
			segment_size = cc.get_segment_size_from_bitstring(spec)
			return ["and", ["is-str", var], ["slist_spec", ["sval", var], segment_size.m, segment_size.n]]
		elif cc.is_type_complete_fun(spec):
			params_spec = cc.get_parameters_from_complete_fun(spec)
			# TODO function arguments spec in list of functions etc
			# TODO if a function is to be called with wrong arguments, program must crash
			argspec = ["and"]
			tlist = "l"
			tlist_length = 0
			for param_spec in params_spec:
				argspec.append(["and", ["is-cons", "l"], self.build_spec(param_spec, ["hd", tlist])])
				tlist = ["tl", tlist]
				tlist_length += 1
			argspec.append(["is-nil", tlist])
			retspec = self.build_spec(cc.get_rettype_from_fun(spec), ["select", ["fmap", ["fval", var]], "l"])
			self.funspec = ["ite", ["=", "f", ["fval", var]], argspec, self.funspec]
			return [
				"and",
				["is-fun", var],
				["=", ["arity", ["fval", var]], str(tlist_length)],
				["forall", [["l", "TList"]], retspec],
			]
		elif cc.is_type_generic_fun(spec):
			ret_spec = cc.get_rettype_from_fun(spec)
			ret_val = ["select", ["fmap", ["fval", var]], "l"]
			return [
				"and",
				["is-fun", var],
				["forall", [["l", "TList"]], self.build_spec(ret_spec, ret_val)],
			]
		elif cc.is_type_atomlit(spec):
			return ["=", var, self.decode(cc.get_literal_from_atomlit(spec))]
		elif cc.is_type_integerlit(spec):
			literal = cc.get_literal_from_integerlit(spec)
			return ["=", var, self.decode(cc.get_literal_from_integerlit(spec))]
		clg.debug_info("unknown spec: " + str(spec))
		assert False

	def unfold_tuple(self, *terms):
		"""
		Unfolds a symbolic tuple.
		"""
		t = self.decode(terms[0])
		self.assertion(["is-tuple", t])
		c = ["tval", t]
		for x in terms[1:]:
			self.assertion(["is-cons", c])
			s = "|{}|".format(cc.get_symb(x))
			if s not in self.vars and s not in self.aux_vars:
				self.aux_vars.append(s)
				self.declarations.append(["declare-const", s, "Term"])
			self.assertion(["=", s, ["hd", c]])
			c = ["tl", c]
		self.assertion(["is-nil", c])

	def make_bitstr(self, symb, encodedValue, size):
		"""
		Makes a bitstring by encoding an appropriate term.
		"""
		t = self.decode(symb)
		n = self.decode(encodedValue)
		b = self.decode(size)
		self.assertion([
			"and",
			["is-int", n],
			["is-int", b],
			["=", t, ["str", ["slist_from_pair", ["ival", n], ["ival", b]]]],
		])

	def concat_segs(self, *terms):
		"""
		Concatenates many bitstrings into a large binary.
		"""
		t = self.decode(terms[0])
		r = self.decode(terms[1])
		v = ["sval", r]
		l = [
			"and",
			["is-str", t],
			["is-str", r],
		]
		for term in reversed(terms[2:]):
			b = self.decode(term)
			l.append(["is-bool", b])
			v = ["scons", ["bval", b], v]
		l.append(["=", ["sval", t], v])
		self.assertion(l)

	def fresh_closure(self, tFun, tArity):
		"""
		Asserts that tFun is a closure with arity tArity.
		"""
		f = self.decode(tFun)
		a = self.decode(tArity)
		self.assertion([
			"and",
			["is-fun", f],
			["is-int", a],
			["=", ["arity", ["fval", f]], ["ival", a]],
		])

	def evaluated_closure(self, *args):
		"""
		Asserts that the evaluation of a closure returns some specific terms.
		"""
		self.erl_lambda(*args)

	# -------------------------------------------------------------------------
	# Constraints.
	# -------------------------------------------------------------------------

	def erl_lambda(self, *args):
		"""
		Asserts that a lambda application has succeeded.
		"""
		ret = self.decode(args[0])
		fun = self.decode(args[1])
		tlist = "nil"
		tlist_length = 0
		for arg in reversed(args[2:]):
			tlist = ["cons", self.decode(arg), tlist]
			tlist_length += 1
		self.assertion([
			"and",
			["is-fun", fun],
			["=", ["arity", ["fval", fun]], str(tlist_length)],
			["spec", ["fval", fun], tlist],
			["=", ["select", ["fmap", ["fval", fun]], tlist], ret],
		])

	def erl_lambda_reversed(self, *args): # TODO is this the opposite of erl_lambda?
		"""
		Asserts that a lambda application has failed.
		"""
		t_fun = self.decode(args[1])
		self.assertion(["not", ["is-fun", t_fun]])

	def guard_true(self, term):
		"""
		Asserts the predicate: term == true
		"""
		t = self.decode(term)
		self.assertion(["=", t, ["bool", "true"]])

	def guard_true_reversed(self, term):
		"""
		Asserts the predicate: Not (term == true)
		"""
		t = self.decode(term)
		self.assertion(["not", ["=", t, ["bool", "true"]]])

	def guard_false(self, term):
		"""
		Asserts the predicate: term == false
		"""
		t = self.decode(term)
		self.assertion(["=", t, ["bool", "false"]])

	def guard_false_reversed(self, term):
		"""
		Asserts the predicate: Not (term == false)
		"""
		t = self.decode(term)
		self.assertion(["not", ["=", t, ["bool", "false"]]])

	def match_equal(self, term1, term2):
		"""
		Asserts the predicate: term1 == term2
		"""
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["=", t1, t2])

	def match_equal_reversed(self, term1, term2):
		"""
		Asserts the predicate: Not (term1 == term2)
		"""
		self.match_not_equal(term1, term2)

	def match_not_equal(self, term1, term2):
		"""
		Asserts the predicate: term1 != term2
		"""
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["not", ["=", t1, t2]])

	def match_not_equal_reversed(self, term1, term2):
		"""
		Asserts the predicate: Not (term1 != term2)
		"""
		self.match_equal(term1, term2)

	def list_nonempty(self, term):
		"""
		Asserts that: term is a nonempty list.
		"""
		t = self.decode(term)
		self.assertion(["and", ["is-list", t], ["is-cons", ["lval", t]]])

	def list_nonempty_reversed(self, term):
		"""
		Asserts that: Not(term is a nonempty list).
		"""
		t = self.decode(term)
		self.assertion(["not", ["and", ["is-list", t], ["is-cons", ["lval", t]]]])

	def list_empty(self, term):
		"""
		Asserts that: term is an empty list.
		"""
		t = self.decode(term)
		self.assertion(["=", t, ["list", "nil"]])

	def list_empty_reversed(self, term):
		"""
		Asserts that: Not(term is an empty list).
		"""
		t = self.decode(term)
		self.assertion(["not", ["=", t, ["list", "nil"]]])

	def list_not_lst(self, term):
		"""
		Asserts that: term is not list.
		"""
		t = self.decode(term)
		self.assertion(["not", ["is-list", t]])

	def list_not_lst_reversed(self, term):
		"""
		Asserts that: Not (term is not list).
		"""
		t = self.decode(term)
		self.assertion(["is-list", t])

	def tuple_sz(self, term, num):
		"""
		Asserts that: term is a tuple of size num.
		"""
		t = self.decode(term)
		n = cc.get_int(num)
		l = ["and", ["is-tuple", t]]
		c = ["tval", t]
		while n > 0:
			l.append(["is-cons", c])
			c = ["tl", c]
			n -= 1
		l.append(["is-nil", c])
		self.assertion(l)

	def tuple_sz_reversed(self, term, num):
		"""
		Asserts that: term is not a tuple of size num.
		"""
		self.tuple_not_sz(term, num)

	def tuple_not_sz(self, term, num):
		"""
		Asserts that: term is not a tuple of size num.
		"""
		t = self.decode(term)
		n = cc.get_int(num)
		l = ["and", ["is-tuple", t]]
		c = ["tval", t]
		while n > 0:
			l.append(["is-cons", c])
			c = ["tl", c]
			n -= 1
		l.append(["is-nil", c])
		self.assertion(["not", l])

	def tuple_not_sz_reversed(self, term, num):
		"""
		Asserts that: Not (term is not a tuple of size num).
		"""
		self.tuple_sz(term, num)

	def tuple_not_tpl(self, term, num): # TODO why is num over here?
		"""
		Asserts that: term is not a tuple.
		"""
		t = self.decode(term)
		self.assertion(["not", ["is-tuple", t]])

	def tuple_not_tpl_reversed(self, term, num): # TODO why is num over here?
		"""
		Asserts that: Not (term is not a tuple).
		"""
		t = self.decode(term)
		self.assertion(["is-tuple", t])

	def empty_bitstr(self, term):
		"""
		Asserts that: term is an empty bitstring.
		"""
		t = self.decode(term)
		self.assertion([
			"and",
			["is-str", t],
			["is-snil", ["sval", t]]
		])

	def empty_bitstr_reversed(self, term):
		"""
		Asserts that: Not (term is an empty bitstring).
		"""
		t = self.decode(term)
		self.assertion([
			"not",
			[
				"and",
				["is-str", t],
				["is-snil", ["sval", t]]
			]
		])

	def nonempty_bitstr(self, term1, term2, term):
		"""
		Asserts that: term is an nonempty bitstring.
		"""
		t = self.decode(term)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion([
			"and",
			["is-str", t],
			["is-scons", ["sval", t]],
			["is-bool", t1],
			["=", ["bval", t1], ["shd", ["sval", t]]],
			["is-str", t2],
			["=", ["sval", t2], ["stl", ["sval", t]]],
		])

	def nonempty_bitstr_reversed(self, term1, term2, term):
		"""
		Asserts that: Not (term is a nonempty bitstring).
		"""
		t = self.decode(term)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion([
			"not",
			[
				"and",
				["is-str", t],
				["is-scons", ["sval", t]]
			]
		])

	def const_slist(self, expr):
		name = "slist" + str(self.const_slist_cnt)
		self.declarations.append(["declare-const", name, "SList"])
		self.cmds.append(["assert", ["=", name, expr]])
		self.const_slist_cnt += 1
		return name

	def bitmatch_const_true(self, termRest, cnstValue, size, termBitstr):
		"""
		Asserts that: termBitstr == <<cnstValue/size, termRest>>.
		"""
		r = self.decode(termRest)
		n = self.decode(cnstValue)
		b = self.decode(size)
		t = self.decode(termBitstr)
		self.cmds.append(["assert", ["and",
			["is-str", r],
			["is-int", n],
			["is-int", b],
			["is-str", t],
		]])
		slist_nb = self.const_slist(["slist_from_pair", ["ival", n], ["ival", b]])
		slist_r = self.const_slist(["sval", r])
		slist_t = self.const_slist(["sval", t])
		self.assertion(["=", ["slist_concat", slist_nb, slist_r], slist_t])

	def bitmatch_const_true_reversed(self, termRest, cnstValue, size, termBitstr): # TODO not exact negation
		"""
		Asserts that: Not (termBitstr == <<cnstValue/size, termRest>>).
		"""
		r = self.decode(termRest)
		n = self.decode(cnstValue)
		b = self.decode(size)
		t = self.decode(termBitstr)
		self.cmds.append(["assert", ["and",
			["is-str", r],
			["is-int", n],
			["is-int", b],
			["is-str", t],
		]])
		slist_nb = self.const_slist(["slist_from_pair", ["ival", n], ["ival", b]])
		slist_r = self.const_slist(["sval", r])
		slist_t = self.const_slist(["sval", t])
		self.assertion(["not", ["=", ["slist_concat", slist_nb, slist_r], slist_t]])

	def bitmatch_const_false(self, cnstValue, size, termBitstr):
		"""
		Asserts that: termBitstr =/= <<cnstValue/size, termRest>>.
		"""
		n = self.decode(cnstValue)
		b = self.decode(size)
		t = self.decode(termBitstr)
		self.cmds.append(["assert", ["and",
			["is-int", n],
			["is-int", b],
			["is-str", t],
		]])
		slist_nb = self.const_slist(["slist_from_pair", ["ival", n], ["ival", b]])
		self.assertion(["not", ["slist_match", slist_nb, ["sval", t]]])

	def bitmatch_const_false_reversed(self, cnstValue, size, termBitstr): # TODO not exact negation
		"""
		Asserts that: Not (termBitstr =/= <<cnstValue/size, termRest>>).
		"""
		n = self.decode(cnstValue)
		b = self.decode(size)
		t = self.decode(termBitstr)
		self.cmds.append(["assert", ["and",
			["is-int", n],
			["is-int", b],
			["is-str", t],
		]])
		slist_nb = self.const_slist(["slist_from_pair", ["ival", n], ["ival", b]])
		self.assertion(["slist_match", slist_nb, ["sval", t]])

	def bitmatch_var_true(self, term1, term2, size, termBitstr):
		"""
		Asserts that: termBitstr == <<term1/size, term2>>.
		"""
		self.bitmatch_const_true(term2, term1, size, termBitstr)

	def bitmatch_var_true_reversed(self, term1, term2, size, termBitStr):
		"""
		Asserts that: Not (termBitstr == <<term1/size, term2>>).
		"""
		self.bitmatch_const_true_reversed(term2, term1, size, termBitStr)

	def bitmatch_var_false(self, size, termBitstr):
		"""
		Asserts that: termBitstr =/= <<term1/size, term2>>.
		"""
		b = self.decode(size)
		t = self.decode(termBitstr)
		self.assertion([
			"not",
			[
				"and",
				["is-int", b],
				["is-str", t],
				["slist_longer", ["sval", t], ["ival", b]],
			]
		])

	def bitmatch_var_false_reversed(self, size, termBitstr):
		"""
		Asserts that: Not (termBitstr =/= <<term1/size, term2>>).
		"""
		b = self.decode(size)
		t = self.decode(termBitstr)
		self.assertion([
			"and",
			["is-int", b],
			["is-str", t],
			["slist_longer", ["sval", t], ["ival", b]],
		])

	def lambda_with_arity(self, tFun, tArity):
		"""
		Asserts that: tFun is a function with arity tArity.
		"""
		f = self.decode(tFun)
		a = self.decode(tArity)
		self.assertion([
			"and",
			["is-fun", f],
			["is-int", a],
			["=", ["arity", ["fval", f]], ["ival", a]]
		])

	def not_lambda_with_arity_reversed(self, tFun, tArity):
		"""
		Asserts that: Not (tFun is not a function with arity tArity).
		"""
		self.lambda_with_arity(tFun, tArity)

	# -------------------------------------------------------------------------
	# Erlang BIFs or MFAs treated as BIFs.
	# -------------------------------------------------------------------------

	def head(self, term0, term1):
		"""
		Asserts that: term0 == hd(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["is-list", t1])
		self.assertion(["is-cons", ["lval", t1]])
		self.assertion(["=", t0, ["hd", ["lval", t1]]])

	def tail(self, term0, term1):
		"""
		Asserts that: term0 == tl(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["is-list", t1])
		self.assertion(["is-cons", ["lval", t1]])
		self.assertion(["=", t0, ["list", ["tl", ["lval", t1]]]])

	def cons(self, term0, term1, term2):
		"""
		Asserts that: term0 = [term1 | term2].
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["is-list", t2])
		self.assertion(["=", t0, ["list", ["cons", t1, ["lval", t2]]]])

	def is_boolean(self, term0, term1):
		"""
		Asserts that: term0 == is_boolean(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-bool", t1]]])

	def is_integer(self, term0, term1):
		"""
		Asserts that: term0 == is_integer(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-int", t1]]])

	def is_float(self, term0, term1):
		"""
		Asserts that: term1 == is_float(term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-real", t1]]])

	def is_list(self, term0, term1):
		"""
		Asserts that: term0 == is_list(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-list", t1]]])

	def is_tuple(self, term0, term1):
		"""
		Asserts that: term0 == is_tuple(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-tuple", t1]]])

	def is_atom(self, term0, term1):
		"""
		Asserts that: term0 == is_atom(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["or", ["is-bool", t1], ["is-atom", t1]]]])

	def is_bitstring(self, term0, term1):
		"""
		Asserts that: term0 == is_bitstring(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-str", t1]]])

	def is_fun(self, term0, term1):
		"""
		Asserts that: term0 == is_function(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["is-fun", t1]]])

	def is_fun_with_arity(self, r, t, a):
		"""
		Asserts that: r == is_function(t, a).
		"""
		r = self.decode(r)
		t = self.decode(t)
		a = self.decode(a)
		self.assertion(["=", r, ["bool", ["and", ["is-fun", t], ["is-int", a], ["=", ["arity", ["fval", t]], ["ival", a]]]]])

	def is_number(self, term0, term1):
		"""
		Asserts that: term0 == is_number(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["=", t0, ["bool", ["or", ["is-int", t1], ["is-real", t1]]]])

	def _binary_operation(self, operator, term0, term1, term2):
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["or", ["is-int", t1], ["is-real", t1]])
		self.assertion(["or", ["is-int", t2], ["is-real", t2]])
		self.assertion([
			"ite",
			["and", ["is-int", t1], ["is-int", t2]],
			["=", t0, ["int", [operator, ["ival", t1], ["ival", t2]]]],
			[
				"=",
				t0,
				[
					"real",
					[
						operator,
						["ite", ["is-int", t1], ["to_real", ["ival", t1]], ["rval", t1]],
						["ite", ["is-int", t2], ["to_real", ["ival", t2]], ["rval", t2]]
					]
				]
			]
		])

	def plus(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 + term2.
		"""
		self._binary_operation("+", term0, term1, term2)

	def minus(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 - term2.
		"""
		self._binary_operation("-", term0, term1, term2)

	def times(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 * term2.
		"""
		self._binary_operation("*", term0, term1, term2)

	def idiv_nat(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 // term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion([
			"and",
			["is-int", t1],
			["is-int", t2],
			[">=", ["ival", t1], "0"],
			[">", ["ival", t2], "0"],
			["=", t0, ["int", ["div", ["ival", t1], ["ival", t2]]]],
		])

	def unary(self, term0, term1):
		"""
		Asserts that: term0 = - term1.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion([
			"and",
			["or", ["is-int", t1], ["is-real", t1]],
			[
				"ite",
				["is-int", t1],
				["=", t0, ["int", ["-", ["ival", t1]]]],
				["=", t0, ["real", ["-", ["rval", t1]]]]
			],
		])

	def trunc(self, term0, term1):
		"""
		Asserts that: term0 is term1 truncated.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["or", ["is-int", t1], ["is-real", t1]])
		self.assertion([
			"=",
			t0,
			[
				"ite",
				["is-int", t1],
				t1,
				[
					"int",
					[
						"ite",
						[">=", ["rval", t1], "0.0"],
						["to_int", ["rval", t1]],
						["-", ["to_int", ["-", ["rval", t1]]]]
					]
				]
			]
		])

	def equal(self, term0, term1, term2):
		"""
		Asserts that: term0 = (term1 == term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["=", t0, ["bool", ["=", t1, t2]]])

	def lt_integers(self, term0, term1, term2):
		"""
		Asserts that: term0 = (term1 < term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["is-int", t1])
		self.assertion(["is-int", t2])
		self.assertion(["=", t0, ["bool", ["<", ["ival", t1], ["ival", t2]]]])

	def lt_floats(self, term0, term1, term2):
		"""
		Asserts that: term0 = (term1 < term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.assertion(["is-real", t1])
		self.assertion(["is-real", t2])
		self.assertion(["=", t0, ["bool", ["<", ["rval", t1], ["rval", t2]]]])

	### Type conversions.

	def to_float(self, term0, term1):
		"""
		Asserts that: term0 = float(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.assertion(["or", ["is-int", t1], ["is-real", t1]])
		self.assertion(["=", t0, ["real", ["ite", ["is-int", t1], ["to_real", ["ival", t1]], ["rval", t1]]]])

	### Bitwise Operations.

	def const_bv(self, t):
		"""
		Associates a new bitvector with a decoded integer term t.
		"""
		l = 128 # TODO max bv size set to 128; increase timeout for a bigger limit
		m = 2 ** (l - 1)
		name = "bv" + str(self.const_bv_cnt)
		self.declarations.append(["declare-const", name, ["_", "BitVec", str(l)]])
		self.cmds.append(["assert", ["is-int", t]])
		self.cmds.append(["assert", [
			"or",
			[
				"and",
				[">=", ["ival", t], "0"],
				["<", ["ival", t], str(m)],
				["=", ["ival", t], ["bv2int", name]],
			],
			[
				"and",
				["<", ["ival", t], "0"],
				[">=", ["ival", t], str(-m)],
				["=", ["-", ["ival", t]], ["+", ["bv2int", ["bvnot", name]], "1"]],
			],
		]])
		self.const_bv_cnt += 1
		return name

	def bitwise_operation(self, operation, term0, term1, term2):
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		bv0 = self.const_bv(t0)
		bv1 = self.const_bv(t1)
		bv2 = self.const_bv(t2)
		self.assertion(["=", bv0, [operation, bv1, bv2]])

	def band(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 & term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.cmds.append(["assert", ["int-and", ["ival", t1], ["ival", t2], ["ival", t0]]])

	def bxor(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 ^ term2.
		"""
		self.bitwise_operation("bvxor", term0, term1, term2)

	def bor(self, term0, term1, term2):
		"""
		Asserts that: term0 = term1 | term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.cmds.append(["assert", ["int-or", ["ival", t1], ["ival", t2], ["ival", t0]]])
