# -*- coding: utf-8 -*-

import cuter_generic_solver as cgs
import cuter_common as cc
import cuter_logger as clg

import cuter_smt_process
from cuter_smt_library import *


class ErlangSMT(cgs.AbstractErlangSolver):

	def __init__(self, timeout):
		self.library = []
		self.commands = []
		self.commands.append(["set-option", ":produce-models", "true"])
		self.commands.append(["declare-datatypes", [], datatypes])
		self.commands.append(["declare-fun", "fa", ["Int"], "Int"])
		self.commands.append(["declare-fun", "fm", ["Int"], "FList"])
		# fnp(f, t) = true => t is not defined for f.
		self.commands.append([
			"define-fun-rec",
			"fnp",
			[["f", "FList"], ["t", "TList"]],
			"Bool",
			["or",
				["is-fn", "f"],
				["and",
					["is-fc", "f"],
					["not", ["=", ["fx", "f"], "t"]],
 					["fnp", ["ft", "f"], "t"],
				],
			],
 		])
		# fu(f, t) = true => t is defined at most once for f.
		self.commands.append([
			"define-fun-rec",
			"fu",
			[["f", "FList"], ["t", "TList"]],
			"Bool",
			["or",
				["is-fn", "f"],
				["and",
					["is-fc", "f"],
					["or",
						["and",
							["not", ["=", ["fx", "f"], "t"]],
							["fu", ["ft", "f"], "t"],
						],
						["and",
							["=", ["fx", "f"], "t"],
							["fnp", ["ft", "f"], "t"],
						],
					],
					["fu", ["ft", "f"], "t"],
				],
			],
 		])
		self.setSolver = lambda: cuter_smt_process.SolverZ3(timeout)
		self.solver = self.setSolver()
		self.define_funs_rec = []

	# =========================================================================
	# Public API.
	# =========================================================================

	def reset_solver(self):
		"""
		Reset the solver.
		"""
		self.solver.kill()
		self.solver = self.setSolver()

	def add_axioms(self):
		"""
		Add the axioms from memory to the solver.
		"""
		for command in self.commands:
			self.solver.write(command)

	def solve(self):
		"""
		Solve a constraint set and returns the result.
		"""
		status = self.solver.check_sat()
		if status == "sat":
			return cc.mk_sat()
		elif status == "unsat":
			self.solver.exit()
			return cc.mk_unsat()
		elif status == "unknown":
			return cc.mk_unknown()
		elif status == "timeout":
			return cc.mk_timeout()
		clg.debug_info("solve: " + str(status))
		assert False

	def fix_parameter(self, p, v):
		"""
		Fix a symbolic variable to a specific value.
		"""
		p = self.decode(p)
		v = self.decode(v)
		self.solver.write(["assert", ["=", p, v]])

	def encode_model(self):
		"""
		Encode the resulting model.
		"""
		entries = []
		for var in self.vars:
			val = self.solver.get_value(var)
			assert isinstance(val, list) and len(val) == 1
			val = val[0]
			assert isinstance(val, list) and len(val) == 2
			val = self.encode(expand_lets(val[1]))
			entries.append(cc.mk_model_entry(cc.mk_symb(var[1:-1]), val))
		self.solver.exit()
		return cc.mk_model_data(cc.mk_model(entries))

	# =========================================================================
	# Private Methods.
	# =========================================================================

	def decode(self, data, shared = None):
		"""
		Decode a term to its SMT representation.
		"""
		if cc.is_symb(data):
			s = "|{}|".format(cc.get_symb(data))
			if s not in self.vars and s not in self.aux_vars:
				self.aux_vars.append(s)
				self.commands.append(["declare-const", s, "Term"])
			return s
		elif cc.is_int(data):
			return ["int", build_int(cc.get_int(data))]
		elif cc.is_float(data):
			return ["real", build_real(cc.get_float(data))]
		elif cc.is_atom(data):
			return ["atom", build_ilist(cc.get_atom_chars(data))]
		elif cc.is_list(data):
			items = cc.get_list_subterms(data)
			if shared is None:
				shared = cc.get_shared(data)
			return ["list", build_tlist([self.decode(item, shared) for item in items])]
		elif cc.is_tuple(data):
			items = cc.get_tuple_subterms(data)
			if shared is None:
				shared = cc.get_shared(data)
			return ["tuple", build_tlist([self.decode(item, shared) for item in items])]
		elif cc.is_bitstring(data):
			return ["str", build_slist(cc.get_bits(data))]
		elif cc.is_alias(data):
			return self.decode(shared[cc.get_alias(data)], shared)
		clg.debug_info("decoding failed: " + str(data))
		assert False

	def encode(self, data, funs = []):
		# TODO description
		if data[0] == "int":
			return cc.mk_int(parse_int(data[1]))
		elif data[0] == "real":
			return cc.mk_float(parse_real(data[1]))
		elif data[0] == "atom":
			node = data[1]
			v = []
			while node != "in":
				v.append(parse_int(node[1]))
				node = node[2]
			return cc.mk_atom(v)
		elif data[0] == "list":
			node = data[1]
			v = []
			while node != "tn":
				v.append(self.encode(node[1], funs))
				node = node[2]
			return cc.mk_list(v)
		elif data[0] == "tuple":
			node = data[1]
			v = []
			while node != "tn":
				v.append(self.encode(node[1], funs))
				node = node[2]
			return cc.mk_tuple(v)
		elif data[0] == "str":
			node = data[1]
			v = []
			while node != "sn":
				v.append(node[1] == "true")
				node = node[2]
			return cc.mk_bitstring(v)
		elif data[0] == "fun":
			# TODO function decoding and encoding
			assert isinstance(data, list) and len(data) == 2
			fv = parse_int(data[1])
			# if a cycle (a function calling itself recursively) is found,
			# it is obvious that the solver has selected an arbitrary term as a value
			if fv in funs:
				return cc.mk_any()
			funs = funs[:]
			funs.append(fv)
			# get function info from solver
			# TODO save function arity and entries to an array
			val = self.solver.get_value(["fa", data[1]], ["fm", data[1]])
			assert isinstance(val, list) and len(val) == 2
			assert isinstance(val[0], list) and len(val[0]) == 2
			arity = parse_int(expand_lets(val[0][1]))
			# if arity is less than or greater than 255, we assume it is an arbitrary value selected by the solver
			# because there is no constraint limiting the function's arity; thus, we set it to zero
			if arity < 0 or arity > 255:
				arity = 0
			assert isinstance(val[1], list) and len(val[1]) == 2
			node = expand_lets(val[1][1])
			entries = []
			otherwise = None
			while node != "fn":
				assert isinstance(node, list) and len(node) == 4 and node[0] == "fc"
				x = cc.get_list_subterms(self.encode(["list", node[1]], funs))
				# keep only entries with argument length equal to arity
				if len(x) == arity:
					y = self.encode(node[2], funs)
					if otherwise is None:
						otherwise = y
					else:
						entries.append(cc.mk_fun_entry(x, y))
				node = node[3]
			if otherwise is None:
				otherwise = cc.mk_any()
			return cc.mk_fun(arity, entries, otherwise)
		clg.debug_info("encoding failed: " + str(data))
		assert False

	# -------------------------------------------------------------------------
	# Parse internal commands.
	# -------------------------------------------------------------------------

	def mfa_params(self, *args):
		"""
		Store the entry point MFA's symbolic parameters.
		"""
		self.vars = []
		self.aux_vars = []
		for arg in args:
			self.decode(arg)
		self.vars = self.aux_vars
		self.aux_vars = []

	def mfa_spec(self, spec):
		"""
		Store the spec of the entry point MFA.
		"""
		typedefs = cc.get_type_defs_of_spec(spec)
		if len(typedefs) > 0:
			for tdf in typedefs:
				tname = cc.get_typedef_name(tdf)
				tdefinition = cc.get_typedef_definition(tdf)
				body = self.build_spec(tdefinition, "t")
				self.define_funs_rec.append(("|{}|".format(tname), [["t", "Term"]], body))
		# Build the define-funs-rec definition for the type definitions, if needed.
		self.assert_typedef_funs()
		p = cc.get_spec_clauses(spec)[0]
		pms = cc.get_parameters_from_complete_funsig(p)
		for item in zip(self.vars, pms):
			self.commands.append(["assert", self.build_spec(item[1], item[0])])

	def assert_typedef_funs(self):
		if len(self.define_funs_rec) > 0:
			[names, args, bodies] = zip(*self.define_funs_rec)
			n = len(names)
			self.commands.append(["define-funs-rec", list(map(list, zip(names, args, ["Bool"]*n))), list(bodies)])
		self.define_funs_rec = None

	def fun_rec_name(self):
		if hasattr(self, "fun_rec_cnt"):
			self.fun_rec_cnt += 1
		else:
			self.fun_rec_cnt = 0
		return "fun-rec-" + str(self.fun_rec_cnt)

	def fun_rec(self, body):
		body_smt = serialize(body)
		if not hasattr(self, "fun_recs"):
			self.fun_recs = {}
		elif body_smt in self.fun_recs:
			return self.fun_recs[body_smt]
		name = self.fun_rec_name()
		self.fun_recs[body_smt] = name
		if self.define_funs_rec is not None:
			self.define_funs_rec.append((name, [["t", "Term"]], body))
		else:
			self.commands.append(["define-fun-rec", name, [["t", "Term"]], "Bool", body]) # TODO define-fun doesn't work
		return name

	def fun_rec_tlist(self, spec):
		spec = self.build_spec(spec, ["th", "l"])
		spec_smt = serialize(spec)
		if not hasattr(self, "fun_rec_tlists"):
			self.fun_rec_tlists = {}
		elif spec_smt in self.fun_rec_tlists:
			return self.fun_rec_tlists[spec_smt]
		name = self.fun_rec_name()
		self.fun_rec_tlists[spec_smt] = name
		args = [["l", "TList"]]
		body = [
			"or",
			["is-tn", "l"],
			["and", ["is-tc", "l"], spec, [name, ["tt", "l"]]],
		]
		if self.define_funs_rec is not None:
			self.define_funs_rec.append((name, args, body))
		else:
			self.commands.append(["define-fun-rec", name, args, "Bool", body])
		return name

	def fun_rec_flist(self, par_spec, ret_spec):
		if par_spec is None:
			arg_spec = "true"
		else:
			arg_spec = ["and"]
			tlist = ["fx", "f"]
			for param_spec in par_spec:
				arg_spec.append(["and", ["is-tc", tlist], self.build_spec(param_spec, ["th", tlist])])
				tlist = ["tt", tlist]
			arg_spec.append(["is-tn", tlist])
		ret_spec = self.build_spec(ret_spec, ["fy", "f"])
		spec_smt = serialize([arg_spec, ret_spec])
		if not hasattr(self, "fun_rec_flists"):
			self.fun_rec_flists = {}
		elif spec_smt in self.fun_rec_flists:
			return self.fun_rec_flists[spec_smt]
		name = self.fun_rec_name()
		self.fun_rec_flists[spec_smt] = name
		args = [["f", "FList"]]
		body = [
			"or",
			["is-fn", "f"],
			["and", ["is-fc", "f"], arg_spec, ret_spec, [name, ["ft", "f"]]],
		]
		if self.define_funs_rec is not None:
			self.define_funs_rec.append((name, args, body))
		else:
			self.commands.append(["define-fun-rec", name, args, "Bool", body])
		return name

	def build_spec(self, spec, var):
		if cc.is_type_any(spec):
			return "true"
		elif cc.is_type_float(spec):
			return ["is-real", var]
		elif cc.is_type_integer(spec):
			return ["is-int", var]
		elif cc.is_type_list(spec):
			inner_spec = cc.get_inner_type_from_list(spec)
			name = self.fun_rec_tlist(inner_spec)
			return [
				"and",
				["is-list", var],
				[name, ["lv", var]],
			]
		elif cc.is_type_nonempty_list(spec):
			inner_spec = cc.get_inner_type_from_nonempty_list(spec)
			name = self.fun_rec_tlist(inner_spec)
			return [
				"and",
				["is-list", var],
				["is-tc", ["lv", var]],
				[name, ["lv", var]],
			]
		elif cc.is_type_tupledet(spec):
			body = ["and", ["is-tuple", var]]
			tlist = ["tv", var]
			for inner_type in cc.get_inner_types_from_tupledet(spec):
				body.append(["is-tc", tlist])
				body.append(self.build_spec(inner_type, ["th", tlist]))
				tlist = ["tt", tlist]
			body.append(["is-tn", tlist])
			return body
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
				ret.append([">=", ["iv", var], build_int(cc.get_lower_bound(limits))])
			if cc.has_upper_bound(limits):
				ret.append(["<=", ["iv", var], build_int(cc.get_upper_bound(limits))])
			return ret
		elif cc.is_type_atom(spec):
			return ["is-atom", var]
		elif cc.is_type_bitstring(spec):
			segment_size = cc.get_segment_size_from_bitstring(spec)
			m = int(segment_size.m)
			n = int(segment_size.n)
			slist = ["sv", var]
			axioms = ["and"]
			axioms.append(["is-str", var])
			while m > 0:
				axioms.append(["is-sc", slist])
				slist = ["st", slist]
				m -= 1
			if n == 0:
				axioms.append(["is-sn", slist])
			elif n > 1:
				axioms.append(SListSpec(slist, build_int(n), self))
			return axioms
		elif cc.is_type_complete_fun(spec):
			# TODO if a function is to be called with wrong arguments, program must crash
			par_spec = cc.get_parameters_from_complete_fun(spec)
			ret_spec = cc.get_rettype_from_fun(spec)
			name = self.fun_rec_flist(par_spec, ret_spec)
			return ["and",
				["is-fun", var],
				["=", ["fa", ["fv", var]], build_int(len(par_spec))],
				[name, ["fm", ["fv", var]]],
				["not", ["=", ["fm", ["fv", var]], "fn"]],
				IsFunction(var),
			]
		elif cc.is_type_generic_fun(spec):
			par_spec = None
			ret_spec = cc.get_rettype_from_fun(spec)
			name = self.fun_rec_flist(par_spec, ret_spec)
			return ["and",
				["is-fun", var],
				[name, ["fm", ["fv", var]]],
				["not", ["=", ["fm", ["fv", var]], "fn"]],
				IsFunction(var),
			]
		elif cc.is_type_atomlit(spec):
			return ["=", var, self.decode(cc.get_literal_from_atomlit(spec))]
		elif cc.is_type_integerlit(spec):
			return ["=", var, self.decode(cc.get_literal_from_integerlit(spec))]
		elif cc.is_type_userdef(spec):
			type_name = cc.get_type_name_of_userdef(spec)
			return ["|{}|".format(type_name), var]
		clg.debug_info("unknown spec: " + str(spec))
		assert False

	def unfold_tuple(self, *terms):
		"""
		Unfold a symbolic tuple.
		"""
		t = self.decode(terms[0])
		conj = [
			"and",
			["is-tuple", t],
		]
		tlist = ["tv", t]
		for x in terms[1:]:
			s = self.decode(x)
			conj.append(["is-tc", tlist])
			conj.append(["=", s, ["th", tlist]])
			tlist = ["tt", tlist]
		conj.append(["is-tn", tlist])
		self.commands.append(["assert", conj])

	def unfold_list(self, *terms):
		"""
		Unfold a symbolic list.
		"""
		# TODO missing testcase
		t = self.decode(terms[0])
		conj = [
			"and",
			["is-list", t],
		]
		tlist = ["lv", t]
		for x in terms[1:]:
			s = self.decode(x)
			conj.append(["is-tc", tlist])
			conj.append(["=", s, ["th", tlist]])
			tlist = ["tt", tlist]
		conj.append(["is-tn", tlist])
		self.commands.append(["assert", conj])

	# TODO when constructing bitstrings, size must have a concrete non-negative integer value

	def int2bv(self, n, b):
		assert isinstance(b, int) and b >= 0, "b must be a non-negative integer"
		assert isinstance(n, int) and n >= 0, "n must be a non-negative integer"
		ret = []
		while b > 0:
			ret.append("true" if n % 2 != 0 else "false")
			n //= 2
			b -= 1
		# assert n == 0, "n overflows b bits as an unsigned integer" # TODO erlang sends b = 0 and n = 42
		ret.reverse()
		return ret


	def var2bv(self, n, b):
		assert isinstance(b, int) and b >= 0, "b must be a non-negative integer"
		conj = [
			"and",
			["is-int", n],
		]
		n = ["iv", n]
		conj.append(["<=", "0", n])
		ret = []
		while b > 0:
			ret.append(["not", ["=", ["mod", n, "2"], "0"]])
			n = ["div", n, "2"]
			b -= 1
		conj.append(["=", n, "0"])
		ret.reverse()
		self.commands.append(["assert", conj])
		return ret

	def make_bitstr(self, symb, encodedValue, size):
		"""
		Make a bitstring by encoding an appropriate term.
		"""
		t = self.decode(symb)
		n = self.decode(encodedValue)
		b = cc.get_int(size)
		conj = [
			"and",
			["is-str", t],
		]
		slist = ["sv", t]
		for bit in self.var2bv(n, b):
			conj.append(["is-sc", slist])
			conj.append(["=", ["sh", slist], bit])
			slist = ["st", slist]
		conj.append(["is-sn", slist])
		self.commands.append(["assert", conj])

	def concat_segs(self, *terms):
		"""
		Concatenate many bitstrings into a large binary.
		"""
		t = self.decode(terms[0])
		r = self.decode(terms[1])
		v = ["sv", r]
		conj = [
			"and",
			["is-str", t],
			["is-str", r],
		]
		for term in reversed(terms[2:]):
			b = self.decode(term)
			conj.append(IsBool(b))
			v = ["sc", AtomToBool(b), v]
		conj.append(["=", ["sv", t], v])
		self.commands.append(["assert", conj])

	def fresh_closure(self, tFun, tArity):
		"""
		Assert that tFun is a closure with arity tArity.
		"""
		f = self.decode(tFun)
		a = self.decode(tArity)
		self.commands.append(["assert", [
			"and",
			["is-fun", f],
			["is-int", a],
			["=", ["fa", ["fv", f]], ["iv", a]],
		]])

	def evaluated_closure(self, *args):
		"""
		Assert that the evaluation of a closure returns some specific terms.
		"""
		self.erl_lambda(*args)

	# -------------------------------------------------------------------------
	# Constraints.
	# -------------------------------------------------------------------------

	def erl_lambda(self, *args):
		"""
		Assert that a lambda application has succeeded.
		"""
		ret = self.decode(args[0])
		fun = self.decode(args[1])
		tlist = "tn"
		tlist_length = 0
		for arg in reversed(args[2:]):
			tlist = ["tc", self.decode(arg), tlist]
			tlist_length += 1
		if hasattr(self, "flist_depth"):
			self.flist_depth += 1
		else:
			self.flist_depth = 0
		self.commands.append(["assert", [
			"and",
			["is-fun", fun],
			["=", ["fa", ["fv", fun]], build_int(tlist_length)],
			FListEquals(["fm", ["fv", fun]], tlist, ret, build_int(self.flist_depth), self),
		]])

	def erl_lambda_reversed(self, *args): # TODO not exactly reversed
		"""
		Assert that a lambda application has failed.
		"""
		t_fun = self.decode(args[1])
		self.commands.append(["assert", ["not", ["is-fun", t_fun]]])

	def guard_true(self, term):
		"""
		Assert the predicate: term == true
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["=", t, true]])

	def guard_true_reversed(self, term): # TODO not exactly reversed
		"""
		Assert the predicate: Not (term == true)
		"""
		self.guard_false(term)

	def guard_false(self, term):
		"""
		Assert the predicate: term == false
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["=", t, false]])

	def guard_false_reversed(self, term): # TODO not exactly reversed
		"""
		Assert the predicate: Not (term == false)
		"""
		self.guard_true(term)

	def match_equal(self, term1, term2):
		"""
		Assert the predicate: term1 == term2
		"""
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", ["=", t1, t2]])

	def match_equal_reversed(self, term1, term2):
		"""
		Assert the predicate: Not (term1 == term2)
		"""
		self.match_not_equal(term1, term2)

	def match_not_equal(self, term1, term2):
		"""
		Assert the predicate: term1 != term2
		"""
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", ["not", ["=", t1, t2]]])

	def match_not_equal_reversed(self, term1, term2):
		"""
		Assert the predicate: Not (term1 != term2)
		"""
		self.match_equal(term1, term2)

	def list_nonempty(self, term):
		"""
		Assert that: term is a nonempty list.
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["and", ["is-list", t], ["is-tc", ["lv", t]]]])

	def list_nonempty_reversed(self, term):
		"""
		Assert that: Not(term is a nonempty list).
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["not", ["and", ["is-list", t], ["is-tc", ["lv", t]]]]])

	def list_empty(self, term):
		"""
		Assert that: term is an empty list.
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["and", ["is-list", t], ["is-tn", ["lv", t]]]])

	def list_empty_reversed(self, term): # TODO not exactly reversed
		"""
		Assert that: Not(term is an empty list).
		"""
		self.list_nonempty(term)

	def list_not_lst(self, term):
		"""
		Assert that: term is not list.
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["not", ["is-list", t]]])

	def list_not_lst_reversed(self, term): # TODO not exactly reversed
		"""
		Assert that: Not (term is not list).
		"""
		t = self.decode(term)
		self.list_nonempty(term)

	def tuple_sz(self, term, num):
		"""
		Assert that: term is a tuple of size num.
		"""
		t = self.decode(term)
		n = cc.get_int(num)
		l = ["and", ["is-tuple", t]]
		c = ["tv", t]
		while n > 0:
			l.append(["is-tc", c])
			c = ["tt", c]
			n -= 1
		l.append(["is-tn", c])
		self.commands.append(["assert", l])

	def tuple_sz_reversed(self, term, num):
		"""
		Assert that: term is not a tuple of size num.
		"""
		self.tuple_not_sz(term, num)

	def tuple_not_sz(self, term, num):
		"""
		Assert that: term is not a tuple of size num.
		"""
		t = self.decode(term)
		n = cc.get_int(num)
		is_t = ["is-tuple", t]
		l = ["and"]
		c = ["tv", t]
		while n > 0:
			l.append(["is-tc", c])
			c = ["tt", c]
			n -= 1
		l.append(["is-tn", c])
		self.commands.append(["assert", ["and", is_t, ["not", l]]])

	def tuple_not_sz_reversed(self, term, num):
		"""
		Assert that: Not (term is not a tuple of size num).
		"""
		self.tuple_sz(term, num)

	def tuple_not_tpl(self, term, num):
		"""
		Assert that: term is not a tuple.
		"""
		t = self.decode(term)
		self.commands.append(["assert", ["not", ["is-tuple", t]]])

	def tuple_not_tpl_reversed(self, term, num): # TODO not exactly reversed
		"""
		Assert that: Not (term is not a tuple).
		"""
		self.tuple_sz(term, num)

	def empty_bitstr(self, term):
		"""
		Assert that: term is an empty bitstring.
		"""
		t = self.decode(term)
		self.commands.append(["assert", [
			"and",
			["is-str", t],
			["is-sn", ["sv", t]],
		]])

	def empty_bitstr_reversed(self, term): # TODO not exactly reversed
		"""
		Assert that: Not (term is an empty bitstring).
		"""
		t = self.decode(term)
		self.commands.append(["assert", [
			"and",
			["is-str", t],
			["is-sc", ["sv", t]],
		]])

	def nonempty_bitstr(self, term1, term2, term):
		"""
		Assert that: term is a nonempty bitstring.
		"""
		t = self.decode(term)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-str", t],
			["is-sc", ["sv", t]],
			IsBool(t1),
			["=", AtomToBool(t1), ["sh", ["sv", t]]],
			["is-str", t2],
			["=", ["sv", t2], ["st", ["sv", t]]],
		]])

	def nonempty_bitstr_reversed(self, term1, term2, term): # TODO not exactly reversed
		"""
		Assert that: Not (term is a nonempty bitstring).
		"""
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.empty_bitstr(term)

	def bitmatch_const_true(self, termRest, cnstValue, size, termBitstr):
		"""
		Assert that: termBitstr == <<cnstValue/size, termRest>>.
		"""
		r = self.decode(termRest)
		n = cc.get_int(cnstValue)
		b = cc.get_int(size)
		t = self.decode(termBitstr)
		conj = [
			"and",
			["is-str", t],
			["is-str", r],
		]
		slist = ["sv", t]
		for bit in self.int2bv(n, b):
			conj.append(["is-sc", slist])
			conj.append(["=", ["sh", slist], bit])
			slist = ["st", slist]
		conj.append(["=", slist, ["sv", r]])
		self.commands.append(["assert", conj])

	def bitmatch_const_true_reversed(self, termRest, cnstValue, size, termBitstr): # TODO not exactly reversed
		"""
		Assert that: Not (termBitstr == <<cnstValue/size, termRest>>).
		"""
		r = self.decode(termRest)
		self.bitmatch_const_false(cnstValue, size, termBitstr)

	def bitmatch_const_false(self, cnstValue, size, termBitstr):
		"""
		Assert that: termBitstr =/= <<cnstValue/size, termRest>>.
		"""
		n = cc.get_int(cnstValue)
		b = cc.get_int(size)
		t = self.decode(termBitstr)
		conj = [
			"and",
			["is-str", t],
		]
		slist = ["sv", t]
		for bit in self.int2bv(n, b):
			conj.append(["is-sc", slist])
			conj.append(["=", ["sh", slist], bit])
			slist = ["st", slist]
		self.commands.append(["assert", ["not", conj]])

	def bitmatch_const_false_reversed(self, cnstValue, size, termBitstr):
		"""
		Assert that: Not (termBitstr =/= <<cnstValue/size, termRest>>).
		"""
		n = cc.get_int(cnstValue)
		b = cc.get_int(size)
		t = self.decode(termBitstr)
		conj = [
			"and",
			["is-str", t],
		]
		slist = ["sv", t]
		for bit in self.int2bv(n, b):
			conj.append(["is-sc", slist])
			conj.append(["=", ["sh", slist], bit])
			slist = ["st", slist]
		self.commands.append(["assert", conj])

	def bitmatch_var_true(self, term1, term2, size, termBitstr):
		"""
		Assert that: termBitstr == <<term1/size, term2>>.
		"""
		r = self.decode(term2)
		n = self.decode(term1)
		b = cc.get_int(size)
		t = self.decode(termBitstr)
		conj = [
			"and",
			["is-str", r],
			["is-str", t],
		]
		slist = ["sv", t]
		for bit in self.var2bv(n, b):
			conj.append(["is-sc", slist])
			conj.append(["=", ["sh", slist], bit])
			slist = ["st", slist]
		conj.append(["=", slist, ["sv", r]])
		self.commands.append(["assert", conj])

	def bitmatch_var_true_reversed(self, term1, term2, size, termBitstr): # TODO not exactly reversed
		"""
		Assert that: Not (termBitstr == <<term1/size, term2>>).
		"""
		r = self.decode(term2)
		n = self.decode(term1)
		self.bitmatch_var_false(size, termBitstr)

	def bitmatch_var_false(self, size, termBitstr):
		"""
		Assert that: termBitstr =/= <<term1/size, term2>>.
		"""
		b = cc.get_int(size)
		t = self.decode(termBitstr)
		assert b >= 0, "b must be a non-negative integer"
		conj = [
			"and",
			["is-str", t],
		]
		slist = ["sv", t]
		while b > 0:
			conj.append(["is-sc", slist])
			slist = ["st", slist]
			b -= 1
		self.commands.append(["assert", ["not", conj]])

	def bitmatch_var_false_reversed(self, size, termBitstr):
		"""
		Assert that: Not (termBitstr =/= <<term1/size, term2>>).
		"""
		b = cc.get_int(size)
		t = self.decode(termBitstr)
		assert b >= 0, "b must be a non-negative integer"
		conj = [
			"and",
			["is-str", t],
		]
		slist = ["sv", t]
		while b > 0:
			conj.append(["is-sc", slist])
			slist = ["st", slist]
			b -= 1
		self.commands.append(["assert", conj])

	def not_lambda_with_arity_reversed(self, tFun, tArity): # TODO function appears only in reversed form
		"""
		Assert that: Not (tFun is not a function with arity tArity).
		"""
		f = self.decode(tFun)
		a = self.decode(tArity)
		self.commands.append(["assert", [
			"and",
			["is-fun", f],
			["is-int", a],
			["=", ["fa", ["fv", f]], ["iv", a]],
		]])

	# -------------------------------------------------------------------------
	# Erlang BIFs or MFAs treated as BIFs.
	# -------------------------------------------------------------------------

	def head(self, term0, term1):
		"""
		Assert that: term0 == hd(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["is-list", t1],
			["is-tc", ["lv", t1]],
			["=", t0, ["th", ["lv", t1]]],
		]])

	def tail(self, term0, term1):
		"""
		Assert that: term0 == tl(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["is-list", t1],
			["is-tc", ["lv", t1]],
			["=", t0, ["list", ["tt", ["lv", t1]]]],
		]])

	def cons(self, term0, term1, term2):
		"""
		Assert that: term0 = [term1 | term2].
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-list", t2],
			["=", t0, ["list", ["tc", t1, ["lv", t2]]]],
		]])

	### Operations on atoms.

	def atom_nil(self, term0, term1):
		"""
		Assert that: term0 = (term1 == '').
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["=", t1, ["atom", "in"]])]])

	def atom_head(self, term0, term1):
		"""
		Assert that: term0 is the first character of term1.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["is-atom", t1],
			["is-ic", ["av", t1]],
			["=", t0, ["int", ["ih", ["av", t1]]]],
		]])

	def atom_tail(self, term0, term1):
		"""
		Assert that: term0 is term1 without its first character.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["is-atom", t1],
			["is-ic", ["av", t1]],
			["=", t0, ["atom", ["it", ["av", t1]]]],
		]])

	### Operations on tuples.

	def tcons(self, *terms):
		"""
		Assert that: a term is tuple of many terms.
		"""
		t0 = self.decode(terms[0])
		tlist = "tn"
		for term in reversed(terms[1:]):
			t = self.decode(term)
			tlist = ["tc", t, tlist]
		self.commands.append(["assert", ["=", t0, ["tuple", tlist]]])

	### Query types.

	def is_boolean(self, term0, term1):
		"""
		Assert that: term0 == is_boolean(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(IsBool(t1))]])

	def is_integer(self, term0, term1):
		"""
		Assert that: term0 == is_integer(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-int", t1])]])

	def is_float(self, term0, term1):
		"""
		Assert that: term1 == is_float(term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-real", t1])]])

	def is_list(self, term0, term1):
		"""
		Assert that: term0 == is_list(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-list", t1])]])

	def is_tuple(self, term0, term1):
		"""
		Assert that: term0 == is_tuple(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-tuple", t1])]])

	def is_atom(self, term0, term1):
		"""
		Assert that: term0 == is_atom(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-atom", t1])]])

	def is_bitstring(self, term0, term1):
		"""
		Assert that: term0 == is_bitstring(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-str", t1])]])

	def is_fun(self, term0, term1):
		"""
		Assert that: term0 == is_function(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["is-fun", t1])]])

	def is_fun_with_arity(self, r, t, a):
		"""
		Assert that: r == is_function(t, a).
		"""
		r = self.decode(r)
		t = self.decode(t)
		a = self.decode(a)
		self.commands.append(["assert", ["=", r, BoolToAtom([
			"and",
			["is-fun", t],
			["is-int", a],
			["=", ["fa", ["fv", t]], ["iv", a]],
		])]])

	def is_number(self, term0, term1):
		"""
		Assert that: term0 == is_number(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["or", ["is-int", t1], ["is-real", t1]])]])

	### Arithmetic Operations.

	def plus(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 + term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", NumBinOp("+", t0, t1, t2)])

	def minus(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 - term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", NumBinOp("-", t0, t1, t2)])

	def times(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 * term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", NumBinOp("*", t0, t1, t2)])

	def rdiv(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 / term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["or", ["is-int", t1], ["is-real", t1]],
			[
				"or",
				["and", ["is-int", t2], ["not", ["=", ["iv", t2], "0"]]],
				["and", ["is-real", t2], ["not", ["=", ["rv", t2], "0"]]],
			],
			["=", t0, ["real", [
				"/",
				["ite", ["is-int", t1], ["to_real", ["iv", t1]], ["rv", t1]],
				["ite", ["is-int", t2], ["to_real", ["iv", t2]], ["rv", t2]]
			]]],
		]])
		# solver returns unknown when there are no other constraints; nonlinear integer arithmetic is undecidable

	def idiv_nat(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 // term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-int", t1],
			["is-int", t2],
			[">=", ["iv", t1], "0"],
			[">", ["iv", t2], "0"],
			["=", t0, ["int", ["div", ["iv", t1], ["iv", t2]]]],
		]])

	def rem_nat(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 % term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-int", t1],
			["is-int", t2],
			[">=", ["iv", t1], "0"],
			[">", ["iv", t2], "0"],
			["=", t0, ["int", ["mod", ["iv", t1], ["iv", t2]]]],
		]])

	def unary(self, term0, term1):
		"""
		Assert that: term0 = - term1.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["or", ["is-int", t1], ["is-real", t1]],
			[
				"ite",
				["is-int", t1],
				["=", t0, ["int", ["-", ["iv", t1]]]],
				["=", t0, ["real", ["-", ["rv", t1]]]]
			],
		]])

	# TODO currently term0 must be a real and term2 an integer
	def pow(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 ** term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-real", t0],
			["or", ["is-int", t1], ["is-real", t1]],
			["is-int", t2],
			RealPow(["rv", t0], ["ite", ["is-int", t1], ["to_real", ["iv", t1]], ["rv", t1]], ["iv", t2], self),
		]])

	def trunc(self, term0, term1):
		"""
		Assert that: term0 is term1 truncated.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["or", ["is-int", t1], ["is-real", t1]],
			[
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
							[">=", ["rv", t1], "0.0"],
							["to_int", ["rv", t1]],
							["-", ["to_int", ["-", ["rv", t1]]]]
						]
					]
				]
			],
		]])

	### Comparisons.

	def equal(self, term0, term1, term2):
		"""
		Assert that: term0 = (term1 == term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", ["=", t0, BoolToAtom(["=", t1, t2])]])

	def lt_integers(self, term0, term1, term2):
		"""
		Assert that: term0 = (term1 < term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-int", t1],
			["is-int", t2],
			["=", t0, BoolToAtom(["<", ["iv", t1], ["iv", t2]])],
		]])

	def lt_floats(self, term0, term1, term2):
		"""
		Assert that: term0 = (term1 < term2).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", [
			"and",
			["is-real", t1],
			["is-real", t2],
			["=", t0, BoolToAtom(["<", ["rv", t1], ["rv", t2]])],
		]])

	### Type conversions.

	def to_float(self, term0, term1):
		"""
		Assert that: term0 = float(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["or", ["is-int", t1], ["is-real", t1]],
			["=", t0, ["real", ["ite", ["is-int", t1], ["to_real", ["iv", t1]], ["rv", t1]]]],
		]])

	def list_to_tuple(self, term0, term1):
		"""
		Assert that: term0 = list_to_tuple(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["is-list", t1],
			["=", t0, ["tuple", ["lv", t1]]],
		]])

	def tuple_to_list(self, term0, term1):
		"""
		Assert that: term0 = tuple_to_list(term1).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", [
			"and",
			["is-tuple", t1],
			["=", t0, ["list", ["tv", t1]]],
		]])

	### Bogus operations (used for their side-effects in Erlang).

	def bogus(self, term0, term1):
		"""
		Assert that: term0 == term1 (Identity function).
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		self.commands.append(["assert", ["=", t0, t1]])

	### Bitwise Operations.
	# no need to check again whether terms are integers

	def band(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 & term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", IntAnd(["iv", t0], ["iv", t1], ["iv", t2], self)])

	def bxor(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 ^ term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", IntXor(["iv", t0], ["iv", t1], ["iv", t2], self)])

	def bor(self, term0, term1, term2):
		"""
		Assert that: term0 = term1 | term2.
		"""
		t0 = self.decode(term0)
		t1 = self.decode(term1)
		t2 = self.decode(term2)
		self.commands.append(["assert", IntOr(["iv", t0], ["iv", t1], ["iv", t2], self)])
